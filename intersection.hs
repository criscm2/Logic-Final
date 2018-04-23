module Intersection (intersection) where

import Formula
import Assignment

intersection :: Formula -> Formula -> Maybe Assignment

intersection (If a b) (If c d)
 | (Just equivList) <- intersection a c = fmap (equivList ++) $ intersection (apply equivList b) (apply equivList d)
 | otherwise = Nothing

intersection (Neg a) (Neg b) = intersection a b

intersection (Atom a) (Atom b)
 | a == b    = Just []
 | otherwise = Nothing

intersection (Variable a) (Variable b) | a == b = Just []

intersection (Variable a) st
 | contains st (Variable a) = Nothing
 | otherwise = Just [SubAssignment a st]

intersection st (Variable a)
 | contains st (Variable a) = Nothing
 | otherwise = Just [SubAssignment a st]

intersection _ _ = Nothing

main = print $ intersection (Variable 1) (Variable 2)
