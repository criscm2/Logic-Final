module Axiom (Axiom(..), buildAxiom) where

import Formula
import Assignment

data Axiom = Axiom {
 constructor :: (Int -> Formula),
 airity :: Int
}

instance Show Axiom where
 show (Axiom construct _) = show $ construct 0

combineLists :: (Ord a) => [a] -> [a] -> [a]
combineLists [] x = x
combineLists x [] = x
combineLists (a:ax) (b:bx)
 | a < b     = a : combineLists ax (b:bx) 
 | a == b    = a : combineLists ax bx 
 | otherwise = b : combineLists (a:ax) bx 

vSet :: Formula -> [Int]
vSet (Atom _)         = []
vSet (Neg form)       = vSet form
vSet (Variable n)     = [n]
vSet (If form1 form2) = combineLists (vSet form1) (vSet form2)

buildAxiom :: Formula -> Axiom
buildAxiom form = Axiom (\x -> apply [ SubAssignment var (Variable $ x + index) | (index, var) <- zip [0..] variables ] form) (length variables)
 where variables = vSet form 

