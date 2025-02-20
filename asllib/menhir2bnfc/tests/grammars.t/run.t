Ensure that a bnfc-style grammar can be generated from a simple menhir grammar
  $ menhir --cmly calc.mly
  $ menhir2bnfc calc.cmly calc.cf
  $ diff calc.cf calc.cf.expected

Test the bnf output
  $ menhir --cmly calc.mly
  $ menhir2bnfc --no-ast calc.cmly calc.bnf
  $ diff calc.bnf calc.bnf.expected

Test the sorting logic
  $ menhir --cmly calc.mly
  $ menhir2bnfc --order calc_order.txt calc.cmly calc_ordered.cf
  $ diff calc_ordered.cf calc_ordered.cf.expected
