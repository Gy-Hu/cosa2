#include "engines/ic3ng.h"

#include <fstream>

#include "smt-switch/smtlib_reader.h"

namespace pono {

  void IC3ng::set_helper_term_predicates(const smt::TermVec & preds) const {
    loaded_predicates_ = preds;
  }

} // namespace pono

