/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andres Noetzli, Tianyi Liang
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A simple demonstration of reasoning about sequences via the C++ API.
 */

#include <cvc5/cvc5.h>

#include <iostream>

using namespace cvc5;

int main()
{
  TermManager tm;
  Solver slv(tm);

  // Set the logic
  slv.setLogic("QF_SLIA");
  // Produce models
  slv.setOption("produce-models", "true");
  // The option strings-exp is needed
  slv.setOption("strings-exp", "true");

  // Sequence sort
  Sort intSeq = tm.mkSequenceSort(tm.getIntegerSort());

  // Sequence variables
  Term x = tm.mkConst(intSeq, "x");
  Term y = tm.mkConst(intSeq, "y");

  // Empty sequence
  Term empty = tm.mkEmptySequence(tm.getIntegerSort());
  // Sequence concatenation: x.y.empty
  Term concat = tm.mkTerm(Kind::SEQ_CONCAT, {x, y, empty});
  // Sequence length: |x.y.empty|
  Term concat_len = tm.mkTerm(Kind::SEQ_LENGTH, {concat});
  // |x.y.empty| > 1
  Term formula1 = tm.mkTerm(Kind::GT, {concat_len, tm.mkInteger(1)});
  // Sequence unit: seq(1)
  Term unit = tm.mkTerm(Kind::SEQ_UNIT, {tm.mkInteger(1)});
  // x = seq(1)
  Term formula2 = tm.mkTerm(Kind::EQUAL, {x, unit});

  // Make a query
  Term q = tm.mkTerm(Kind::AND, {formula1, formula2});

  // check sat
  Result result = slv.checkSatAssuming(q);
  std::cout << "cvc5 reports: " << q << " is " << result << "." << std::endl;

  if (result.isSat())
  {
    std::cout << "  x = " << slv.getValue(x) << std::endl;
    std::cout << "  y = " << slv.getValue(y) << std::endl;
  }
}
