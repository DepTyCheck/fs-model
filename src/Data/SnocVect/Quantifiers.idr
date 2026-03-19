module Data.SnocVect.Quantifiers

import Data.SnocVect

%default total
%prefix_record_projections off

namespace All
  ||| A proof that all elements of a snoc-vector satisfy a property. It is a list of
  ||| proofs, corresponding element-wise to the `SnocVect`.
  public export
  data All : (0 p : a -> Type) -> SnocVect n a -> Type where
    Lin  : All p Lin
    (:<) : {0 xs : SnocVect n a} -> All p sx -> p x -> All p (sx :< x)
