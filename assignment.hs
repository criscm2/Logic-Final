module Assignment (Assignment, apply, SubAssignment(..)) where

import Formula

data SubAssignment = SubAssignment Integer Formula

instance Show SubAssignment where
 show (SubAssignment num st) = '{' : show num ++ "} => "++show st

type Assignment = [SubAssignment]

apply' :: SubAssignment -> Formula -> Formula
apply' (SubAssignment varname st) (Variable a)
 | a == varname = st
 | otherwise    = Variable a
apply' equiv (If a b) = If (apply' equiv a) (apply' equiv b)
apply' equiv (Neg a)  = Neg $ apply' equiv a
apply' _   a@(Atom _) = a

apply :: Assignment -> Formula -> Formula
apply assignment form = foldr apply' form assignment
