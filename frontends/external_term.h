/*********************                                                        */
/*! \file external_term.h
** \verbatim
** Top contributors (to current version):
**   Hongce Zhang
** This file is part of the pono project.
** Copyright (c) 2024 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Frontend for properties in 
**       (define-fun predicate.0 ...) or
**       (define-fun assertion.0 ...) or (define-fun assumption.0 ...)
**
**
**/

#pragma once

#include <iostream>

#include "assert.h"
#include "core/ts.h"
#include "smt-switch/smt.h"
#include "smt-switch/smtlib_reader.h"
#include "utils/exceptions.h"

namespace pono {
class ExternalTermInterface : public smt::SmtLibReader
{
 public:
  ExternalTermInterface(const std::string & filename, TransitionSystem & ts);

  typedef SmtLibReader super;

  smt::Term AddAssertions(const smt::Term &in) const;

  void AddAssumptionsToTS();
  const smt::TermVec & GetExternalPredicates() const { return predicates_; }
  const smt::TermList & GetExternalClauses() const { return clauses_; }

 protected:
  // overloaded function, used when arg list of function is parsed
  // NOTE: | |  pipe quotes are removed.
  smt::Term register_arg(const std::string & name, const smt::Sort & sort) override;
  
  // Override process_define_fun to handle clause.X terms
  void process_define_fun(const std::string & name, 
                         const smt::TermVec & params,
                         const smt::Sort & sort,
                         const smt::Term & term);

  std::string filename_;
  TransitionSystem & ts_;

  smt::TermVec predicates_;
  smt::TermVec assertions_;
  smt::TermVec assumptions_;
  smt::TermList clauses_;    // Store clauses in a list
};

}  // namespace pono
