module Lukasiewicz (axioms) where

import Formula
import Axiom

axioms = zipWith Axiom [
  (\x ->
   (If 
    (Variable x)
    (If
     (Variable $ x + 1)
     (Variable x)
    )
   )
  ),
  (\x ->
   (If
    (If 
     (Variable x)
     (If 
      (Variable $ x + 1)
      (Variable $ x + 2)
     )
    )
    (If
     (If 
      (Variable x)
      (Variable $ x + 1)
     )
     (If 
      (Variable x)
      (Variable $ x + 2)
     )
    )
   )
  ),
  (\x ->
   (If
    (If
     (Neg
      (Variable x)
     )
     (Neg
      (Variable $ x + 1)
     )
    )
    (If
     (Variable $ x + 1)
     (Variable x)
    )
   )
  )
 ] [2,3,2]
