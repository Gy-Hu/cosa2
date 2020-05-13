/*********************                                                        */
/*! \file 
 ** \verbatim
 ** Top contributors (to current version):
 **   Hongce Zhang
 ** This file is part of the cosa2 project.
 ** Copyright (c) 2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file LICENSE in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief SyGuS Query Generator
 **
 ** 
 **/

#include "str_util.h"
#include "container_shortcut.h"
#include "gen_sygus_query.h"

#include <fmt/format.h>
#include <fstream>
#include <queue>

namespace cosa {

namespace sygus {


SyGuSTransBuffer::SyGuSTransBuffer (const TransitionSystem & ts):
ts_(ts), states_(ts.states()), next_states_(ts.next_states()), inputs_(ts.inputs()) {
  std::vector<std::string> arg_lists_init_;
  std::vector<std::string> arg_lists_trans_;
  std::vector<std::string> arg_lists_call_init_;
  std::vector<std::string> arg_lists_call_trans_;
  // compute vars
  for (const auto &s : states_) {
    auto name = name_sanitize(s->to_string());
    auto sort = s->get_sort()->to_string();
    primal_var_def_ += "(declare-var " + name + " () " + sort + ")\n";
    arg_lists_init_.push_back("("+name + " " + sort+")");
    arg_lists_trans_.push_back("("+name + " " + sort+")");
    arg_lists_call_init_.push_back(name);
    arg_lists_call_trans_.push_back(name);
  }
  for (const auto &s : next_states_) {
    auto name = name_sanitize(s->to_string());
    auto sort = s->get_sort()->to_string();
    prime_var_def_ += "(declare-var " + name + " () " + sort + ")\n";
    arg_lists_trans_.push_back("("+name + " " + sort+")");
    arg_lists_call_trans_.push_back(name);
  }
  for (const auto &s : inputs_) {
    auto name = name_sanitize(s->to_string());
    auto sort = s->get_sort()->to_string();
    prime_var_def_ += "(declare-var " + name + " () " + sort + ")\n";
    arg_lists_trans_.push_back("("+name + " " + sort+")");
    arg_lists_call_trans_.push_back(name);
  }

  trans_def_ = "(define-fun Trans (" + Join(arg_lists_trans_, " ") +") Bool ("
    + ts_.trans()->to_string() + "))";
  trans_use_ = "(Trans " + Join(arg_lists_call_trans_, " ") + ")";

  // (define-fun Fprev (state_arg_def_) Bool (...))
  // (Fprev )
  state_arg_def_ = Join(arg_lists_init_, " ");
  state_arg_use_ = Join(arg_lists_call_init_, " ");

  init_def_ = "(define-fun Init (" + state_arg_def_ +") Bool ("
    + ts_.init()->to_string() + "))";
  init_use_ = "(Init " + state_arg_use_ + ")";

}

std::string SyGuSTransBuffer::GetFprevDef(const smt::Term & Fprev) const {
  return ("(define-fun Fprev (" +state_arg_def_+") Bool ("
    + Fprev->to_string() + "))");
}
std::string SyGuSTransBuffer::GetFprevUse() const {
  return ("(Fprev " + state_arg_use_ + ")");
}

// ------------ END of buffer functions ------------ //

std::vector<std::string_view> operator_symbols = 
{
  "And",
  "Or",
  "Xor",
  "Not",
  "=>", // Implies
  "=", // Iff
  "----", // Ite
  "=", // Equal
  "=", // Distinct: Not equal should work
  "----", // Apply

  /* Arithmetic Theories */
  "----", // Plus,
  "----", // Minus,
  "----", // Negate,
  "----", // Mult,
  "----", // Div,
  "----", // Lt,
  "----", // Le,
  "----", // Gt,
  "----", // Ge,
  // Integers only
  "----", //Mod,
  "----", //Abs,
  "----", //Pow,
  "----", //IntDiv,
  // Int/Real Conversion and Queries
  "----", //To_Real,
  "----", //To_Int,
  "----", //Is_Int,
  /* Fixed Size BitVector Theory */
  "----", // Concat,
  "----", // Extract,
  "bvnot", // BVNot,
  "bvneg", // BVNeg,
  "bvand", // BVAnd,
  "bvor", // BVOr,
  "bvxor", // BVXor,
  "bvnand", // BVNand,
  "bvnor", // BVNor,
  "bvxnor", // BVXnor,
  "=", // BVComp,
  "bvadd", // BVAdd,
  "bvsub", // BVSub,
  "bvmul", // BVMul,
  "bvudiv", // BVUdiv,
  "bvsdiv", // BVSdiv,
  "bvurem", // BVUrem,
  "bvsrem", // BVSrem,
  "bvsmod", // BVSmod,
  "bvshl", // BVShl,
  "bvashr", // BVAshr,
  "bvlshr", // BVLshr,
  "bvult", // BVUlt,
  "bvule", // BVUle,
  "bvugt", // BVUgt,
  "bvuge", // BVUge,
  "bvslt", // BVSlt,
  "bvsle", // BVSle,
  "bvsgt", // BVSgt,
  "bvsge", // BVSge,
  "zero_extend", // Zero_Extend,
  "sign_extend", // Sign_Extend,
  "----", // Repeat,
  "rotate_left", // Rotate_Left,
  "rotate_right", // Rotate_Right,
  // BitVector Conversion
  "----", // BV_To_Nat,
  "----", // Int_To_BV,
  /* Array Theory */
  "----", // Select,
  "----", // Store,
  /**
     Serves as both the number of ops and a null element for builtin operators.
   */
  "----", // NUM_OPS_AND_NULL
};

static std::string width_to_type(uint64_t w) {
  if (w == 0)
    return "Bool";
  return "(_ BitVec " + std::to_string(w) +")";
}


// ------------ END of Constants------------ //

static std::string syntax_constraints_template = R"**(
(synth-fun INV 
   %args% Bool
( (Conj Bool) (Disj Bool) (Literal Bool) (Atom Bool)
  %nonterminals%
)
(
    (Conj Bool (Disj 
                (and Disj Conj)))
    (Disj Bool (Literal 
                (or Literal Disj)))
    (Literal Bool (Atom
                (not Atom)))
    (Atom Bool (
      %comps%
      ))
      %evcs%
   ))

)**";

SyGusQueryGen::SyGusQueryGen(
  const SyntaxStructureT & syntax,
  const std::unordered_set<std::string> & keep_vars_name,
  const std::unordered_set<std::string> & remove_vars_name) :
  syntax_(syntax)
{ 
	// compute the all variable list
  // gen necessary strings
  std::vector<std::string> inv_def_vars;
  // std::vector<std::string> inv_use_vars;

  for (auto && w_cnstr : syntax_) {
    auto width = w_cnstr.first;
    const auto & cnstr = w_cnstr.second;
    for (const auto & name : cnstr.symbol_names) {
      if (!keep_vars_name.empty() && !IN(name ,keep_vars_name ))
        continue;
      if (IN(name, remove_vars_name))
        continue;
      new_variable_set_[width].insert(name);
      inv_def_vars.push_back("("+ name + " " + width_to_type(width) + ")" );
      ordered_vars.push_back(name);
      vars_kept.insert(name);
    }
  } // here we compute the vars to keep
  inv_def_var_list = Join(inv_def_vars, " ");
  inv_use_var_list = Join(ordered_vars, " ");
  inv_use = "(INV " + inv_use_var_list + ")";

  generate_syntax_cnstr_string();  // -> syntax_constraints

} // SyGusQueryGen::SyGusQueryGen

// _to_sygus_tree
void SyGusQueryGen::generate_syntax_cnstr_string() {
  typedef std::vector<std::string> stvec;
  // 1. refilter again the vars
  remove_unused_width(); // -> reachable_width
  stvec comps_list;
  stvec nonterminal_list;
  std::string evcs;

  for (auto width : reachable_width) {
    if (!IN(width, syntax_))
      continue;
    const auto & syn = syntax_.at(width);
    const auto & var = new_variable_set_.at(width);

    comps_list.push_back( fmt::format("(= E{0} E{0})", width) );
    for (auto primop : syn.op_comp ) {
      unsigned opnum = (unsigned)primop;
      assert(opnum < operator_symbols.size());
      std::string_view opstr = operator_symbols.at(opnum);
      assert(opstr != "----");
      if (opstr == "=")
        continue; // already has it
      if (primop != smt::BVComp && primop != smt::Equal )
        comps_list.push_back( fmt::format("({1} E{0} E{0})", width, opstr) );
    }

    auto tp = width_to_type(width);
    evcs += "(E"+std::to_string(width) + "  " + tp + " (";
    nonterminal_list.push_back("(E"+std::to_string(width) + "  " + tp + ")");

    if (!var.empty()) {
      evcs += "V"+std::to_string(width)+" ";
      nonterminal_list.push_back("(V"+std::to_string(width) + "  " + tp + ")");
    }
    if (!syn.constants.empty()) {
      evcs += "C"+std::to_string(width)+" ";
      nonterminal_list.push_back("(C"+std::to_string(width) + "  " + tp + ")");
    }
    if (!syn.op_binary.empty() || !syn.op_unary.empty()) {
      evcs += "Arithm"+std::to_string(width)+" ";
      nonterminal_list.push_back("(Arithm"+std::to_string(width) + "  " + tp + ")");
    }
    if (!syn.op_concat.empty()) {
      evcs += "Concat"+std::to_string(width)+" ";
      nonterminal_list.push_back("(Concat"+std::to_string(width) + "  " + tp + ")");
    }
    if (!syn.op_extract.empty()) {
      evcs += "Extract"+std::to_string(width)+" ";
      nonterminal_list.push_back("(Extract"+std::to_string(width) + "  " + tp + ")");
    }
    if (!syn.op_rotate.empty()) {
      evcs += "Rotate"+std::to_string(width)+" ";
      nonterminal_list.push_back("(Rotate"+std::to_string(width) + "  " + tp + ")");
    }
    if (!syn.op_extend.empty()) {
      evcs += "Ext"+std::to_string(width)+" ";
      nonterminal_list.push_back("(Ext"+std::to_string(width) + "  " + tp + ")");
    }

    evcs += "))\n";

    if (!var.empty()) {
      evcs += "(V"+std::to_string(width)+" " + tp +" (";
      for (auto pos = var.begin() ; pos != var.end(); ++ pos) {
        if (pos == var.begin())
          evcs += *pos; // already sanitized
        else
          evcs += " "  +  *pos;
      }
      evcs += "))\n";
    }
    if (!syn.constants.empty()) {
      evcs += "(C"+std::to_string(width)+" " + tp +" (";
      for (auto pos = syn.constants.begin() ; pos != syn.constants.end(); ++ pos) {
        if (pos == syn.constants.begin())
          evcs += name_sanitize( (*pos) );
        else
          evcs += " "  + name_sanitize( (*pos) );
      }
      evcs += "))\n";
    }
    if (!syn.op_binary.empty() || !syn.op_unary.empty()) {
      evcs += "(Arithm"+std::to_string(width)+" " + tp + " (";
      stvec arithm;
      for (auto op : syn.op_unary) {
        unsigned opnum = (unsigned)op;
        assert(opnum < operator_symbols.size());
        std::string_view opstr = operator_symbols.at(opnum);
        assert(opstr != "----");
        arithm.push_back(fmt::format("({1} E{0})", width, opstr));
      }
      for (auto op : syn.op_binary) {
        unsigned opnum = (unsigned)op;
        assert(opnum < operator_symbols.size());
        std::string_view opstr = operator_symbols.at(opnum);
        assert(opstr != "----");
        arithm.push_back(fmt::format("({1} E{0} E{0})", width, opstr));
      }
      evcs += Join(arithm, " ");
      evcs += "))\n";
    }
    if (!syn.op_concat.empty()) {
      evcs += "(Concat"+std::to_string(width)+" " + tp + " (";
      stvec concats;
      for (auto && concat : syn.op_concat)
        concats.push_back( fmt::format("(concat E{0} E{1})", concat.width1, concat.width2 ) );
      evcs += Join(concats, " ");
      evcs += "))\n";
    }
    if (!syn.op_extract.empty()) {
      evcs += "(Extract"+std::to_string(width)+" " + tp + " (";
      stvec extracts;
      for (auto && extract : syn.op_extract)
       extracts.push_back( fmt::format("((_ extract {0} {1}) E{2})", extract.h, extract.l, extract.input_width) );
      evcs += Join(extracts, " ");
      evcs += "))\n";
    }
    if (!syn.op_rotate.empty()) {
      evcs += "(Rotate"+std::to_string(width)+" " + tp + " (";
      stvec rotates;
      for (auto && rotate : syn.op_rotate) {
        unsigned opnum = (unsigned)rotate.op;
        assert(opnum < operator_symbols.size());
        std::string_view opstr = operator_symbols.at(opnum);
        assert(opstr != "----");
        rotates.push_back( fmt::format("((_ {} {}) E{})", opstr, rotate.param, width) );
      }
      evcs += Join(rotates, " ");
      evcs += "))\n";
    }
    if (!syn.op_extend.empty()) {
      evcs += "(Ext"+std::to_string(width)+" " + tp + " (";
      stvec exts;
      for (auto && ext : syn.op_extend) {
        unsigned opnum = (unsigned)ext.op;
        assert(opnum < operator_symbols.size());
        std::string_view opstr = operator_symbols.at(opnum);
        assert(opstr != "----");
        exts.push_back( fmt::format("((_ {} {}) E{})", opstr, ext.extw, ext.input_width) );
      }
      evcs += Join(exts, " ");
      evcs += "))\n";
    }
  } // for all reachable width

  syntax_constraints = 
    ReplaceAll( ReplaceAll( ReplaceAll( ReplaceAll(syntax_constraints_template,
      "%args%", "(" + inv_def_var_list + ")"),
      "%nonterminals%", Join(nonterminal_list, " ") ),
      "%comps%", Join(comps_list, " ")),
      "%evcs%", evcs);
} // SyGusQueryGen::generate_syntax_cnstr_string()


void SyGusQueryGen::remove_unused_width() {
  //std::unordered_set<width_t> start_set;
  std::unordered_map<width_t, std::unordered_set<width_t>> use_map;
  std::queue<width_t> q;

  for (auto && width_cnstr : syntax_) {
    auto width = width_cnstr.first;
    const auto & cnstr = width_cnstr.second;
    
    if ( (IN(width, new_variable_set_) && !new_variable_set_.at(width).empty()) ||
        !cnstr.constants.empty()) {
      q.push(width);
      use_map[width].insert(width);
    }

    if (!cnstr.op_unary.empty() || !cnstr.op_binary.empty() || !cnstr.op_concat.empty())
      use_map[width].insert(width);
    for (const auto & exd: cnstr.op_extend)
      use_map[width].insert(exd.input_width);
    for (const auto & extract: cnstr.op_extract)
      use_map[width].insert(extract.input_width);
    for (const auto & concats: cnstr.op_concat) {
      use_map[width].insert(concats.width1);      
      use_map[width].insert(concats.width2);      
    }   
  } // for each width

  // now do the graph reach algorithm
  while(!q.empty()) {
    width_t cur = q.front();
    q.pop();

    for (auto dstw : use_map[cur]) {
      if(!IN(dstw,reachable_width )) {
        reachable_width.insert(dstw);
        q.push(dstw);
      }
    }
  } // while queue is not empty

} // RemoveUnusedWidth

bool SyGusQueryGen::contains_extra_var(Model * m) const {
  for ( auto && v_val : m->cube ) {
    if (!IN(name_sanitize( v_val.first->to_string() ), vars_kept))
      return true;
  }
  return false;
} // SyGusQueryGen::contains_extra_var

// return true if there are cex left
bool SyGusQueryGen::dump_cex_block(
  const cexs_t  & cex_to_block, 
  const SyGuSTransBuffer & sygus_ts_buf,
  std::ostream & os) {

  // use_var_name to find the states and do an index into it
  const auto & symbols = sygus_ts_buf.ts_.symbols();
  for (auto model_ptr : cex_to_block) {
    if (contains_extra_var(model_ptr))
      continue;
    os<<"(constraint (not (INV";
    for (auto && vname : ordered_vars) {
      auto desanitized_name = name_desanitize(vname);
      auto pos = symbols.find(desanitized_name);
      assert(pos != symbols.end());
      auto val_pos = model_ptr->cube.find(pos->second);
      if (val_pos == model_ptr->cube.end()) {
        // not found
        os << " " << vname; // keep the value symbolic
      } else { // gen the value string
        os << " " << val_pos->second->to_string();
      }
    } // for each v in INV
    os << ")))\n";
  }
} // SyGusQueryGen::dump_cex_block

// return true if there are fact left
bool SyGusQueryGen::dump_fact_allow(
  const facts_t  & facts_all, 
  const SyGuSTransBuffer & sygus_ts_buf,
  std::ostream & os) {
  for (auto model_ptr : facts_all) {
    std::string constraint = "(constraint (INV";
    bool skip_this_fact = false;
    const auto & symbols = sygus_ts_buf.ts_.symbols();
    for (auto && vname : ordered_vars) {
      auto desanitized_name = name_desanitize(vname);
      auto pos = symbols.find(desanitized_name);
      assert(pos != symbols.end());
      auto val_pos = model_ptr->cube.find(pos->second);
      if (val_pos == model_ptr->cube.end()) {
        // not found
        skip_this_fact = true;
        break;
      } else { // gen the value string
        os << " " << val_pos->second->to_string();
      }
    } // for each v in INV
    if (skip_this_fact)
      continue;
    constraint += "))\n";
    os << constraint;
  } // for each fact
} // SyGusQueryGen::dump_fact_allow


// (constraint (=> (INV ...) ()))
void SyGusQueryGen::dump_inv_imply_prop(
  const smt::Term & prop, 
  const SyGuSTransBuffer & sygus_ts_buf,
  std::ostream & os) {
  if (prop == nullptr)
    return;
  os << "(constraint (=> " << inv_use << " ("
     << prop->to_string() <<")))\n";
}


void SyGusQueryGen::GenToFile(
    const smt::Term & prevF,
    const facts_t & facts_all, // internal filters
    const cexs_t  & cex_to_block,
    const smt::Term & prop_to_imply,
    const SyGuSTransBuffer & sygus_ts_buf,
    const std::string & fname) {

  std::ofstream fout(fname);

  if (!fout.is_open())
    throw CosaException("SyGuS query file : " + fname + " cannot be created");

  fout << "(set-logic BV)\n";
  fout << syntax_constraints << std::endl;
  fout << sygus_ts_buf.GetInitDef() << std::endl;
  fout << sygus_ts_buf.GetTransDef() << std::endl;
  fout << sygus_ts_buf.GetFprevDef(prevF) << std::endl;
  fout << sygus_ts_buf.GetPrimalVarDef() << std::endl;
  fout << sygus_ts_buf.GetPrimeVarDef() << std::endl;
  fout << sygus_ts_buf.GetInputVarDef() << std::endl;
  
  // facts  -- filter needed with more vars
  dump_cex_block(cex_to_block, sygus_ts_buf, fout);
  dump_fact_allow(facts_all, sygus_ts_buf, fout);
  dump_inv_imply_prop(prop_to_imply, sygus_ts_buf, fout);

  // imply  // '(constraint (=> (and (Fminus2 {argV}) (Tr {argV} {argP})) (INV {argInvP})))'
  fout << "(constraint (=> (and " << sygus_ts_buf.GetFprevUse() << " " << sygus_ts_buf.GetTransUse()  << ") " << inv_use << "))" << std::endl;
  // init_imply // '(constraint (=> (Init {argV}) (INV {argInvV})))'
  fout << "(constraint (=> " << sygus_ts_buf.GetInitUse() << " " << inv_use + "))";

  fout.close();
} // SyGusQueryGen::GenToFile



} // namespace sygus

} // namespace cosa