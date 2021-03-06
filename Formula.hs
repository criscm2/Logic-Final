module Formula (Formula(..), contains, vMax) where

greek :: String
greek = "αβγδεζηθικλµνξοπρσςτυφψω"

data Formula = If Formula Formula | Neg Formula | Atom Char | Variable Int deriving Eq

instance Show Formula where
 show (If a b)     = "(" ++ show a ++ " -> " ++ show b ++ ")"
 show (Neg a)      = "-" ++ show a
 show (Atom a)     = a:""
 show (Variable a) = '{' : show a ++ "}"
-- show (Variable a) = greek !! (fromInteger (toInteger a)) : ""

contains :: Formula -> Formula -> Bool
contains a b | a == b = True
contains (If a1 a2) b   = contains a1 b || contains a2 b
contains (Neg a) b      = contains a b
contains (Atom _) b     = False
contains (Variable _) b = False

vMax :: Formula -> Int
vMax (Variable a) = a
vMax (If a b) = max (vMax a) (vMax b)
vMax (Neg a) = vMax a
vMax (Atom _) = 0
