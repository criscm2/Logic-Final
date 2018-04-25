module Meredith (axioms) where

import Formula

axioms = zip [
  (\x ->
   (If
    (If
     (If
      (If
       (If
        (Variable $ x)
        (Variable $ x + 1)
       )
       (If
        (Neg
         (Variable $ x + 2)
        )
        (Neg
         (Variable $ x + 3)
        )
       )
      )
      (Variable $ x + 2)
     )
     (Variable $ x + 4)
    )
    (If
     (If
      (Variable $ x + 4)
      (Variable $ x)
     )
     (If
      (Variable $ x + 3)
      (Variable $ x)
     )
    )
   )
  )
 ] [1]
