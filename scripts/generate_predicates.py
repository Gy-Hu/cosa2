#!/usr/bin/env python3

import openai
import os
import sys
from pathlib import Path
import argparse

# Try importing z3, but make it optional
try:
    from z3 import parse_smt2_string
    HAVE_Z3 = True
except ImportError:
    HAVE_Z3 = False

# Configure OpenAI
openai.api_base = "https://api.xty.app/v1"
openai.api_key = os.getenv("OPENAI_API_KEY")

def validate_smt2(content):
    """Validate SMT2 content using z3"""
    try:
        parse_smt2_string(content)
        return True
    except Exception as e:
        print(f"Z3 parsing error: {str(e)}", file=sys.stderr)
        print(f"Generated smt2 content: {content}", file=sys.stderr)
        return False

def extract_predicates(content):
    """Extract define-fun declarations with their associated comments"""
    lines = content.split('\n')
    predicates = []
    in_define = False
    pending_comments = []
    
    for line in lines:
        line = line.strip()
        if not line:  # Skip empty lines
            continue
            
        if line.startswith(';'):  # Collect comments
            pending_comments.append(line)
        elif line.startswith('(define-fun'):
            # Add collected comments before the define-fun
            predicates.extend(pending_comments)
            predicates.append(line)
            pending_comments = []  # Clear pending comments
            in_define = True
        elif in_define:
            predicates.append(line)
            if line.endswith(')'):
                in_define = False
                predicates.append('')  # Add blank line between predicates
                
    return '\n'.join(predicates).strip()

def generate_predicates(btor_file, validate=False, verbose=False, max_retries=2, temperature=0.1, max_tokens=1000, top_p=0.1):
    # Read BTOR2 file
    with open(btor_file, 'r') as f:
        btor_content = f.read()
    
    attempt = 0
    last_error = None
    last_predicates = None
    
    
    while attempt < max_retries:
        try:
            # Construct base prompt
            prompt = f"""Given this BTOR2 file, output ONLY define-fun declarations and comments near define-fun declarations in SMT2 format:
            
            {btor_content}
            
            STRICT OUTPUT FORMAT:
            - ONLY output define-fun declarations and its comments
            - NO other text or commands allowed
            - NO markdown formatting, such as code blocks, because the later file will be parsed by a SMT2 parser
            - NO set-logic, check-sat, or exit commands
            - EXACTLY follow this format:

            ; <comment describing the predicate>
            (define-fun |predicate.N| ((x (_ BitVec N)) (y (_ BitVec M))) Bool
            <predicate_body>)
            
            You should get the N and M from the BTOR2 file, every variable should have their bit vector width specified

            Example of valid output:
            ; x <= 61
            (define-fun |predicate.0| ((x (_ BitVec 6)) (y (_ BitVec 6))) Bool
            (bvule x (_ bv61 6)))
            ; y <= 63
            (define-fun |predicate.1| ((x (_ BitVec 6)) (y (_ BitVec 6))) Bool
            (bvule y (_ bv63 6)))
            ; y = x + 2
            (define-fun |predicate.2| ((x (_ BitVec 6)) (y (_ BitVec 6))) Bool
            (= y (bvadd x (_ bv2 6))))

            REQUIREMENTS:
            - Generate predicates for key assertions, bounds, and variable relationships, which will facilitate the model checking process convergent faster
            - Generate top-5 predicates for each file if you can generate more than 5, do not generate too many if you think those are not necessary
            - Variable name should strictly follow the name in the BTOR2 file, do not make up new names
            - Use correct bit vector widths, according to the BTOR2 file
            - DO NOT MAKEUP THE FAKE VARIABLES, such as "unused", "dummy", etc. THE NAME SHOULD BE EXACTLY THE SAME AS THE VARIABLES IN THE BTOR2 FILE
            - Start predicate numbering from 0
            - Include only brief comments describing each predicate
            - Be careful of the brackets, you are easily confused by them, they should be properly paired

            ANY OUTPUT NOT MATCHING THIS EXACT FORMAT WILL BE REJECTED.
            """
            
            # Add error feedback if this is a retry
            if last_error:
                prompt += f"\nPREVIOUS ATTEMPT FAILED Z3 VALIDATION: {last_error}\nPlease fix the error and ensure valid SMT2 syntax."

            response = openai.ChatCompletion.create(
                model="gpt-4o",
                messages=[
                    {"role": "system", "content": "You are a formal verification expert, and ruthless SMT-LIB2 predicate generator. Follow the example format exactly, any other output format or additional text will result in immediate rejection. "},
                    {"role": "user", "content": prompt}
                ]
            )
            
            predicates = response.choices[0].message.content
            last_predicates = predicates
            
            # Validate response is not empty
            if not predicates.strip():
                raise ValueError("Empty response from LLM")
            
            # Format complete SMT2 file for validation
            smt2_content = f"""(set-logic QF_BV)
{predicates}
(check-sat)
(exit)"""

            # Validate if requested
            if validate:
                if not HAVE_Z3:
                    print("Warning: Z3 is not installed, skipping validation", file=sys.stderr)
                else:
                    try:
                        if not validate_smt2(smt2_content):
                            last_error = "Z3 validation failed"
                            attempt += 1
                            continue
                    except Exception as e:
                        last_error = str(e)
                        attempt += 1
                        # print(f"Generated smt2 content: {smt2_content}", file=sys.stderr)
                        continue

            # Extract just predicates and save
            predicates = extract_predicates(predicates)
            output_file = str(Path(btor_file).with_suffix('.helper.smt2'))
            with open(output_file, 'w') as f:
                f.write(predicates)
                
            if verbose:
                print(f"Generated predicates saved to {output_file}")
                
            return True
                
        except Exception as e:
            print(f"Error on attempt {attempt + 1}: {str(e)}", file=sys.stderr)
            last_error = str(e)
            attempt += 1
            continue
    
    # Save predicates after all attempts if we have any
    if last_predicates:
        print("Warning: Saving predicates despite validation failure", file=sys.stderr)
        output_file = str(Path(btor_file).with_suffix('.helper.smt2'))
        with open(output_file, 'w') as f:
            f.write("; WARNING: These predicates failed validation\n")
            f.write(extract_predicates(last_predicates))
        if verbose:
            print(f"Generated predicates saved to {output_file} despite validation errors")
    
    print(f"Failed after {max_retries} attempts", file=sys.stderr)
    return False

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("btor_file", help="Input BTOR2 file")
    parser.add_argument("--validate", action="store_true", help="Validate SMT2 with z3")
    parser.add_argument("--verbose", action="store_true", help="Print detailed output")
    parser.add_argument("--temperature", type=float, default=0.1, help="Temperature for generation (0-1)")
    parser.add_argument("--max-tokens", type=int, default=2000, help="Maximum tokens in response")
    parser.add_argument("--top-p", type=float, default=0.1, help="Top-p sampling parameter (0-1)")
    args = parser.parse_args()
    
    success = generate_predicates(
        args.btor_file, 
        args.validate, 
        args.verbose,
        temperature=args.temperature,
        max_tokens=args.max_tokens,
        top_p=args.top_p
    )
    sys.exit(0 if success else 1)