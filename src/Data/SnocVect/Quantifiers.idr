module Data.SnocVect.Quantifiers

import Data.SnocVect
import Data.DPair

%default total
%prefix_record_projections off

namespace All
  public export
  data All : (0 p : a -> Type) -> SnocVect n a -> Type where
    Lin  : All p Lin
    (:<) : {0 sx : SnocVect n a} -> All p sx -> p x -> All p (sx :< x)

  public export
  pushIn : (sx : SnocVect n a) -> (0 _ : All p sx) -> SnocVect n $ Subset a p
  pushIn [<]       [<]       = [<]
  pushIn (sx :< x) (sp :< p) = pushIn sx sp :< Element x p

  public export
  length : All p xs -> Nat
  length [<] = 0
  length (xs :< x) = S (length xs)

  export
  lengthCorrect : (pxs : All p {n} xs) -> length pxs === n
  lengthCorrect [<] = Refl
  lengthCorrect (pxs :< x) = cong S $ lengthCorrect pxs
  
  export
  lengthUnfold : (pxs : All p xs) -> length pxs === length xs
  lengthUnfold [<] = Refl
  lengthUnfold (pxs :< _) = cong S (lengthUnfold pxs)
