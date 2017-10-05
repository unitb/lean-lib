# lean-lib

Build: [![Build Status](https://travis-ci.org/unitb/lean-lib.svg?branch=master)](https://travis-ci.org/unitb/lean-lib)

## Features

 * `traversable` type class (`util.data.traversable`)
 * cardinality type classes for types with a finite number of values
   and countably many values (`util.data.finite`,
   `util.data.countable`)
 * `category` type class (`util.category`)
 * tactics for proving efficiently inequalities between large literal
   numbers (`util.data.norm_num`)
 * machinery for defining coinductive data types
   (`util.data.coinductive`)
 * monad for expressing non-terminating computations
   (`util.control.monad.non_terminating`, now redundant
   with `mathlib`)
 * Various lemmas complementary to the basic libraries
