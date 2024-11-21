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
    if not HAVE_Z3:
        print("Z3 is not installed, skipping validation", file=sys.stderr)
        return True
    try:
        parse_smt2_string(content)
        return True
    except Exception as e:
        print(f"Z3 parsing error: {str(e)}", file=sys.stderr)
        print(f"Generated smt2 content: {content}", file=sys.stderr)
        return False

def extract_predicates(content):
    """Extract only the define-fun declarations"""
    lines = content.split('\n')
    predicates = []
    in_define = False
    
    for line in lines:
        if line.startswith('(define-fun'):
            predicates.append(line)
            in_define = True
        elif in_define:
            predicates.append(line)
            if line.strip().endswith(')'):
                in_define = False
                
    return '\n'.join(predicates)

def generate_predicates(btor_file, validate=False, verbose=False, max_retries=3):
    # Read BTOR2 file
    with open(btor_file, 'r') as f:
        btor_content = f.read()
    
    attempt = 0
    last_error = None
    
    while attempt < max_retries:
        try:
            # Construct base prompt
            prompt = f"""Given this BTOR2 file, output ONLY define-fun declarations in SMT2 format:
            
            {btor_content}
            
            STRICT OUTPUT FORMAT:
            - ONLY output define-fun declarations
            - NO other text or commands allowed
            - NO markdown formatting, such as code blocks
            - NO set-logic, check-sat, or exit commands
            - EXACTLY follow this format:

            ; <comment describing the predicate>
            (define-fun |predicate.N| ((x (_ BitVec 6)) (y (_ BitVec 6))) Bool
            <predicate_body>)

            Example of valid output:
            (define-fun |predicate.0| ((x (_ BitVec 6)) (y (_ BitVec 6))) Bool
            (bvule x (_ bv61 6)))
            (define-fun |predicate.1| ((x (_ BitVec 6)) (y (_ BitVec 6))) Bool
            (bvule y (_ bv63 6)))
            (define-fun |predicate.2| ((x (_ BitVec 6)) (y (_ BitVec 6))) Bool
            (= y (bvadd x (_ bv2 6))))

            REQUIREMENTS:
            - Generate predicates for key assertions, bounds, and variable relationships
            - Use consistent bit vector widths
            - Start predicate numbering from 0
            - Include only brief comments describing each predicate

            ANY OUTPUT NOT MATCHING THIS EXACT FORMAT WILL BE REJECTED.
            """
            
            # Add error feedback if this is a retry
            if last_error:
                prompt += f"\nPREVIOUS ATTEMPT FAILED Z3 VALIDATION: {last_error}\nPlease fix the error and ensure valid SMT2 syntax."

            response = openai.ChatCompletion.create(
                model="gpt-4o",
                messages=[
                    {"role": "system", "content": "You are a formal verification expert, and ruthless SMT-LIB2 predicate generator that ONLY outputs define-fun declarations. Any other output format or additional text will result in immediate rejection. Follow the example format exactly."},
                    {"role": "user", "content": prompt}
                ]
            )
            
            predicates = response.choices[0].message.content
            
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
            output_file = str(Path(btor_file).with_suffix('.helper2.smt2'))
            with open(output_file, 'w') as f:
                f.write(predicates)
                
            if verbose:
                print(f"Generated predicates saved to {output_file}")
                
            return True
                
        except Exception as e:
            print(f"Error on attempt {attempt + 1}: {str(e)}", file=sys.stderr)
            last_error = str(e)
            attempt += 1
    
    print(f"Failed after {max_retries} attempts", file=sys.stderr)
    return False

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("btor_file", help="Input BTOR2 file")
    parser.add_argument("--validate", action="store_true", help="Validate SMT2 with z3")
    parser.add_argument("--verbose", action="store_true", help="Print detailed output")
    args = parser.parse_args()
    
    success = generate_predicates(args.btor_file, args.validate, args.verbose)
    sys.exit(0 if success else 1)