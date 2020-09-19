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
 ** \brief To BTOR to CHC
 **
 **
 **/

#pragma once

#include "chc_printer_base.h"
#include "prop.h"
#include "smt-switch/smt.h"
#include "ts.h"

#include <string>
#include <unordered_map>

namespace cosa {

class ChcPrinter : public ChcPrinterBase{

protected:
  const TransitionSystem & ts_;
  const Property & property_;

  const smt::UnorderedTermSet & states_;
  const smt::UnorderedTermSet & next_states_;
  const smt::UnorderedTermSet & inputs_;
  const smt::UnorderedTermSet & next_inputs_;


  std::string var_type_; // (type1 type2 type3 ...)

  std::string var_use_; // n1 n2 n3 ...
  std::string var_prime_use_; // n1' n2' n3'

  std::string primal_declare_;       // ((name type) (name type))
  std::string primal_prime_declare_; // ((name type) (name type) and prime variables)



public:
  ChcPrinter (const Property & p);

  virtual void Export(std::ostream & os) const override;

}; // class ChcPrinter

} // namespace cosa
