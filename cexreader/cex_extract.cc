/// \file CounterExample Extractor
// ---Hongce Zhang

#include <cexreader/cex_extract.h>

#include <cexreader/VCDFileParser.hpp>
#include <utils/str_util.h>
#include <utils/logger.h>
#include <utils/container_shortcut.h>
#include <fstream>
#include <sstream>
#include <string.h>
namespace pono {

static std::string val2str(const VCDValue& v) {
  std::stringstream ret;

  switch (v.get_type()) {
  case (VCD_SCALAR):
    ret << "1'b" << VCDValue::VCDBit2Char(v.get_value_bit());
    break;
  case (VCD_VECTOR): {
    const VCDBitVector* vecval = v.get_value_vector();
    ret << std::to_string(vecval->size()) << "'b";
    for (auto it = vecval->begin(); it != vecval->end(); ++it)
      ret << VCDValue::VCDBit2Char(*it);
  } break;
  case (VCD_REAL):
    ret << v.get_value_real();
    break;
  default:
    throw PonoException("Unknown value type!");
  }
  return ret.str();
}


static std::string val2SMTstr(const VCDValue& v) {
  std::stringstream ret;

  switch (v.get_type()) {
  case (VCD_SCALAR):
    ret << VCDValue::VCDBit2Char(v.get_value_bit());
    break;
  case (VCD_VECTOR): {
    const VCDBitVector* vecval = v.get_value_vector();
    // ret << std::to_string(vecval->size()) ;
    // ret << "#b";
    for (auto it = vecval->begin(); it != vecval->end(); ++it)
      ret << VCDValue::VCDBit2Char(*it);
  } break;
  case (VCD_REAL):
    throw PonoException("Unable to handle real numbers in counterexamples.");
    ret << v.get_value_real();
    break;
  default:
    throw PonoException("Unknown value type!");
  }
  return ret.str();
}

std::string prepend(const std::string& prefix, const std::string& sig_name) {
  if (prefix.empty())
    return sig_name;
  return prefix + "." + sig_name;
}

/*
bool in_scope(VCDScope * sc, const std::string & sc_name) {
  VCDScope * sc_traverse = sc;
  while(sc_traverse) {
    if (sc_traverse->name == sc_name)
      return true;
    sc_traverse = sc_traverse->parent;
  }
  return false;
}
*/

std::string collect_scope(VCDScope* sc) {
  std::string ret;
  while (sc) {
    ret = sc->name + "." + ret;
    sc = sc->parent;
  }
  return ret;
}

void CexExtractor::parse_from(const std::string& vcd_file_name,
                              const std::string& scope, is_reg_t is_reg,
                              bool reg_only) {

  cex.clear();

  VCDFileParser parser;
  VCDFile* trace = parser.parse_file(vcd_file_name);

  if (!trace) {
    throw PonoException("Error while reading waveform from: ");
    std::cout<< vcd_file_name;
    return;
  }

  VCDScope* top = trace->get_scope("$root");
  // ILA_NOT_NULL(top);

  // determine the start signal time
  std::string start_sig_hash;
  for (VCDSignal* root_sig : top->signals) {
    // find the hash of it
    if (root_sig->reference == "__START__" ||
        root_sig->reference == "__START__[0:0]")
      start_sig_hash = root_sig->hash;
  }
  if (start_sig_hash.empty()) {
    std::vector<VCDSignal*>* sigs = trace->get_signals();
    for (VCDSignal* sig : *sigs) {
      if(sig->reference=="__START__")
        start_sig_hash = sig->hash;
    }
  }
  VCDTime start_time = -1;
  if (start_sig_hash.empty()) {
    start_time = 0;
  }
  else{
    VCDSignalValues* start_sig_vals = trace->get_signal_value(start_sig_hash);
    
    for (VCDTimedValue* tv : *start_sig_vals) {
      if (val2str(*(tv->value)) == "1'b1") {
        start_time = tv->time;
        break;
      }
    }

    if (start_time == -1) {
      throw PonoException("Start time not found from waveform!");
      return;
    }
}

  std::vector<VCDSignal*>* sigs = trace->get_signals();

  for (VCDSignal* sig : *sigs) {

    // ensure it is only register
    if (sig->type != VCDVarType::VCD_VAR_REG)
      continue;

    // check scope
    // if (! in_scope(sig->scope, scope))
    //  continue;

    auto scopes = collect_scope(sig->scope);

    // check scope -- only the top level
    if (!(syntax_analysis::StrStartsWith(scopes, "$root." + scope + ".") ||
          syntax_analysis::StrStartsWith(scopes, scope + ".")))
      continue;

    auto vlg_name = syntax_analysis::ReplaceAll(scopes + sig->reference, "$root.", "");

    std::string check_name = vlg_name;
    {
      auto pos = check_name.rfind('[');
      if (pos != std::string::npos) {
        auto rpos = check_name.find(']',pos);//If we cannot find, the find function will return the std::string::npos
        // ILA_ERROR_IF(rpos == std::string::npos) 
        //   << "Cex variable name:" << check_name << " has unmatched [] pair";
        if (rpos == std::string::npos)
          throw PonoException("has unmatched [] pair");
        auto colon_pos = check_name.find(':', pos);
        if (colon_pos != std::string::npos && colon_pos < rpos)
          check_name = check_name.substr(0, pos); 
      }
      // auto pos_wrap_l =check_name.rfind('RTL.');
      // pos_wrap_l = pos_wrap_l + 1;
      // auto pos_wrap_r =check_name.rfind("DOT");
      // // pos_wrap_r = pos_wrap_r;
      // check_name.erase(check_name.begin(),check_name.begin()+pos_wrap_r+3);

    }
    if (check_name.find("RTL.") == 0) 
      check_name.erase(check_name.begin(), check_name.begin() +4);
    else continue;
    bool is_this_var_reg = is_reg(check_name);

    if (reg_only && !is_this_var_reg)
      continue;

    auto vlg_val_ptr = trace->get_signal_value_at(sig->hash, start_time);

    if (vlg_val_ptr == nullptr) {
      throw PonoException(" gets Xs. Ignored.");
      continue;
    }

    std::string val = val2SMTstr(*vlg_val_ptr);

    cex.insert(std::make_pair(check_name, val));
    cex_is_reg.insert(std::make_pair(check_name, is_this_var_reg));

  } // for sig

  if (cex.empty())
  {
    throw PonoException("No counterexample is extracted!");
  }
} // parse_from


CexExtractor::CexExtractor(const std::string& vcd_file_name,
                           const std::string& scope, is_reg_t is_reg,
                           bool reg_only) {
  parse_from(vcd_file_name, scope, is_reg, reg_only);
}

/// create from an existing file
CexExtractor::CexExtractor(const std::string& fn) {
  std::ifstream fin(fn);
  if (!fin.is_open()) {
    throw PonoException("Failed to read : ");
    return;
  }
  unsigned pairs;
  fin >> pairs;

  std::string name, val;
  for (unsigned idx = 0; idx < pairs; ++idx) {
    fin >> name;
    fin >> val;
    if (name.empty() || val.empty()) {
      throw PonoException("Failed to read cex from file!");
      break;
    }
    cex.insert(std::make_pair(name, val));
    cex_is_reg.insert(std::make_pair(name, true));
  }
}
// -------------------- MEMBERS ------------------ //
/// return a string to be added to the design
std::string
CexExtractor::GenInvAssert(const std::string& prefix,
                           const std::set<std::string>& focus_name) const {
  std::string ret;
  for (auto&& nv : cex) {
    if (!cex_is_reg.at(nv.first)) // skipping those that are not registers
      continue;
    auto fullname = prepend(prefix, syntax_analysis::ReplaceAll(nv.first, "[0:0]", ""));
    auto check_name = fullname; // remove further of [][:]
    auto pos = check_name.rfind('[');
    if (pos != std::string::npos)
      check_name = check_name.substr(0, pos);
    if (!focus_name.empty() && !IN(check_name, focus_name))
      continue;
    if (ret.empty())
      ret = "(" + fullname + " == " + nv.second + ")";
    else
      ret += "\n&& (" + fullname + " == " + nv.second + ")";
  }
  return ret;
}

const CexExtractor::cex_t& CexExtractor::GetCex() const { return cex; }

// save to file
void CexExtractor::StoreCexToFile(const std::string& fn, const cex_t& c) {
  std::ofstream fout(fn);

  if (!fout.is_open()) {
    throw PonoException("Failed to read : "+ fn);
    return;
  }

  fout << c.size() << "\n";
  for (auto&& nv : c) {
    if(S_IN(' ', nv.first) || S_IN('\r', nv.first) ||
                 S_IN('\t', nv.first) || S_IN('\n', nv.first))
       throw PonoException(nv.first +  " contains space!");
    fout << nv.first << " " << nv.second << std::endl;
  }
}
// save to file (invoke within)
void CexExtractor::StoreCexToFile(const std::string& fn) const {
  StoreCexToFile(fn, cex);
}

// generalize cex
void CexExtractor::DropStates(const std::vector<std::string>& vnames) {
  for (auto&& n : vnames) {
    if (IN(n, cex)) {
      cex.erase(n);
      cex_is_reg.erase(n);
    }
  }
}

//--------------------------------------------------------------------------


void SelectiveExtractor::parse_from(const std::string& vcd_file_name,
                              const std::string& scope, is_reg_t is_reg,
                              bool reg_only) {

  cex.clear();

  VCDFileParser parser;
  VCDFile* trace = parser.parse_file(vcd_file_name);

  if (!trace) {
    throw PonoException("Error while reading waveform from: ");
    std::cout<< vcd_file_name;
    return;
  }

  VCDScope* top = trace->get_scope("$root");
  assert(top);
  std::string start_sig_hash;
  for (VCDSignal* root_sig : top->signals) {
    // find the hash of it
    if (root_sig->reference == "__START__" ||
        root_sig->reference == "__START__[0:0]"||root_sig->reference == "RTL.__START__")
      start_sig_hash = root_sig->hash;
  }
  if (start_sig_hash.empty()) {
    std::vector<VCDSignal*>* sigs = trace->get_signals();
    for (VCDSignal* sig : *sigs) {
      if(sig->reference=="__START__")
        start_sig_hash = sig->hash;
    }
  }
  VCDTime start_time = -1;
  if (start_sig_hash.empty()) {
    start_time = 0;
  }
  else{
    VCDSignalValues* start_sig_vals = trace->get_signal_value(start_sig_hash);
    
    for (VCDTimedValue* tv : *start_sig_vals) {
      if (val2str(*(tv->value)) == "1'b1") {
        start_time = tv->time;
        break;
      }
    }

    if (start_time == -1) {
      throw PonoException("Start time not found from waveform!");
      return;
    }
}


  std::vector<VCDSignal*>* sigs = trace->get_signals();

  logger.log(0,"START @ {}", start_time);
  for (VCDSignal* sig : *sigs) {

    // ensure it is only register
    if (sig->type != VCDVarType::VCD_VAR_REG)
      continue;

    // check scope
    // if (! in_scope(sig->scope, scope))
    //  continue;

    auto scopes = collect_scope(sig->scope);

    // check scope -- only the top level
    if (!(syntax_analysis::StrStartsWith(scopes, "$root." + scope) ||
          syntax_analysis::StrStartsWith(scopes, scope)))
      continue;

    auto vlg_name = syntax_analysis::ReplaceAll(scopes + sig->reference, "$root.", "");
    if ( vlg_name.find(name_removal_) == 0 ) {
      vlg_name = vlg_name.substr(name_removal_.length());
    }

    std::string check_name = vlg_name;
    {
      auto pos = check_name.rfind('[');
      if (pos != std::string::npos) {
        auto rpos = check_name.find(']',pos);//If we cannot find, the find function will return the std::string::npos
        // ILA_ERROR_IF(rpos == std::string::npos) 
        //   << "Cex variable name:" << check_name << " has unmatched [] pair";
        if (rpos == std::string::npos)
          throw PonoException("has unmatched [] pair");
        auto colon_pos = check_name.find(':', pos);
        if (colon_pos != std::string::npos && colon_pos < rpos)
          check_name = check_name.substr(0, pos); 
      }
    }

    bool is_this_var_reg = is_reg(check_name);

    if (reg_only && !is_this_var_reg)
      continue;

    auto vlg_val_ptr = trace->get_signal_value_at(sig->hash, start_time);

    if (vlg_val_ptr == nullptr) {
      throw PonoException(" gets Xs. Ignored.");
      continue;
    }

    std::string val = val2SMTstr(*vlg_val_ptr);

    cex.insert(std::make_pair(check_name, val));
    cex_is_reg.insert(std::make_pair(check_name, is_this_var_reg));

  } // for sig

  if (cex.empty())
  {
    throw PonoException("No counterexample is extracted!");
  }
} // parse_from

}; // namespace ilang
