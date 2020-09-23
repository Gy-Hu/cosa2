/*********************                                                        */
/*! \file 
 ** \verbatim
 ** Top contributors (to current version):
 **   Makai Mann
 ** This file is part of the cosa2 project.
 ** Copyright (c) 2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file LICENSE in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief 
 **
 ** 
 **/


#pragma once

#include <string>
#include <unordered_map>

namespace cosa {

// Engine options
enum Engine
{
  BMC = 0,
  BMC_SP,
  KIND,
  INTERP,
  APDR,
  TOCHC,
  TOCHCREL
};

static const std::unordered_map<std::string, Engine> str2engine(
    { { "bmc", BMC },
      { "bmc-sp", BMC_SP },
      { "ind", KIND },
      { "interp", INTERP },
      { "apdr", APDR },
      { "chc", TOCHC },
      { "chcrel", TOCHCREL }
    });

const Engine to_engine(std::string s)
{
  if (str2engine.find(s) != str2engine.end()) {
    return str2engine.at(s);
  } else {
    throw CosaException("Unrecognized engine: " + s);
  }
}

/************************************ Default Values
 * *********************************/
static const Engine default_engine = APDR;
static const unsigned int default_prop_idx = 0;
static const unsigned int default_bound = 1000;
static const unsigned int default_verbosity = 3;
/********************************* End Default Values
 * ********************************/
}  // namespace cosa
