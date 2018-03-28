data Statement = If Statement Statement | Neg Statement | Atom Char | Variable Char deriving Eq

instance Show Statement where
 show (If a b)     = "(" ++ show a ++ " -> " ++ show b ++ ")"
 show (Neg a)      = "-" ++ show a
 show (Atom a)     = a:""
 show (Variable a) = '{':a:"}"

data Equivalence = Equivalence Char Statement

instance Show Equivalence where
 show (Equivalence chr st) = '{':chr:"} => "++show st

contains :: Statement -> Statement -> Bool
contains a b
 | a == b = True
contains (If a1 a2) b   = contains a1 b || contains a2 b
contains (Neg a) b      = contains a b
contains (Atom _) b     = False
contains (Variable _) b = False

replace :: Statement -> Equivalence -> Statement
replace (Variable a) (Equivalence varname st) 
 | a == varname = st
 | otherwise    = Variable a
replace (If a b) equiv = If (replace a equiv) (replace b equiv) 
replace (Neg a) equiv  = Neg $ replace a equiv
replace a@(Atom _) _   = a

equivalence :: Statement -> Statement -> Maybe [Equivalence]
equivalence (Neg a) (Neg b) = equivalence a b
equivalence (Atom a) (Atom b)
 | a == b    = Just []
 | otherwise = Nothing
equivalence (Variable a) st
 | contains st (Variable a) = Nothing
 | otherwise = Just [Equivalence a st]
equivalence st (Variable a)
 | contains st (Variable a) = Nothing
 | otherwise = Just [Equivalence a st]
equivalence (If a b) (If c d)
 | (Just equivList) <- equivalence a c = fmap (equivList ++) $ equivalence (foldl replace b equivList) (foldl replace d equivList)
 | otherwise = Nothing
equivalence _ _ = Nothing

main=print$equivalence (If (Atom 'A') (Variable 'Ω')) (If (Variable '∆') (Atom 'B'))