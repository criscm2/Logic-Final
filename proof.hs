import Intersection
import Formula
import Assignment
import Lukasiewicz
import Control.Arrow
import Axiom
import Data.List

data Justification = Ax Int | MP | None

instance Show Justification where
 show (Ax x) = "(Axiom " ++ show x ++ ")" 
 show MP = "(Modus Ponens)"
 show None = "????"

data Statement = Statement {
 formula       :: Formula,
 justification :: Justification,
 liabilities   :: [Int]
}

{- TODO label modus ponens -}

instance Show Statement where
 show (Statement form just liabilities ) = show just ++ ' ' : show form

updateForm :: (Formula -> Formula) -> Statement -> Statement
updateForm f state = state {formula = f $ formula state}

combineLists :: (Ord a) => [a] -> [a] -> [a]
combineLists [] x = x
combineLists x [] = x
combineLists (a:ax) (b:bx)
 | a > b     = a : combineLists ax (b:bx) 
 | a == b    = a : combineLists ax bx 
 | otherwise = b : combineLists (a:ax) bx 

addLiabilities :: [Int] -> Statement -> Statement
addLiabilities newLiabilities state = state { liabilities = combineLists newLiabilities $ liabilities state }

justify :: Justification -> Statement -> Statement
justify just state = state {justification = just}

data ProblemState = ProblemState {
  justifiedFormulae   :: [Statement],
  unjustifiedFormulae :: [Statement],
  unusedName :: Int
 }

instance Show ProblemState where
 show (ProblemState jForms uForms _) = (reverse uForms ++ jForms) >>= (('\n' :) . show)

instance Eq ProblemState where
 a == b = proofSize a == proofSize b

instance Ord ProblemState where
 compare a b
  | proofSize a < proofSize b = LT
  | proofSize a > proofSize b = GT
  | otherwise = EQ

proofSize :: ProblemState -> Int
proofSize = ((+) . length . justifiedFormulae) <*> (length . unjustifiedFormulae)

addStep :: ProblemState -> Statement -> ProblemState
addStep (ProblemState jForms uForms uName) statement = ProblemState jForms (statement : uForms) uName

universalApply :: Assignment -> ProblemState -> ProblemState
universalApply assignment (ProblemState jForms uForms uName) = ProblemState ((map $ updateForm $ apply assignment) jForms) ((map $ updateForm $ apply assignment) uForms) uName

justifyHead :: ProblemState -> Justification -> ProblemState
justifyHead (ProblemState jForms (headForm:tailForms) uName) justification = ProblemState (justify justification headForm : jForms) tailForms (uName + 1)

modusPonens :: ProblemState -> [ProblemState]
modusPonens pState@(ProblemState _ [] _) = [pState]
modusPonens pState@(ProblemState jForms (headForm:tailForms) uName) = (unification newPState >>= unification) ++ unification newPState ++ unification newPState' ++ [newPState]
 where
  newLiabilities = length jForms : liabilities headForm -- Zero indexed
  antecedent     = Statement (Variable uName) None newLiabilities
  implication    = Statement (If (Variable uName) (formula headForm)) None newLiabilities
  newPState      = ProblemState (justify MP headForm : jForms) (implication : antecedent : tailForms) (uName + 1)
  newPState'     = ProblemState (justify MP headForm : jForms) (antecedent : implication : tailForms) (uName + 1) -- Used for unifying just the antecedent
 
linkLiabilities :: Int -> [Int] -> ProblemState -> ProblemState
linkLiabilities oldLiab links pState =
 pState {
  unjustifiedFormulae =
   [
    if (elem oldLiab $ liabilities uForm) then
     (addLiabilities links uForm)
    else
     uForm
   |
     uForm <- unjustifiedFormulae pState
   ]
 } 

unification :: ProblemState -> [ProblemState]
unification (ProblemState jForms (newForm : uForms) uName) =
 [
  linkLiabilities index (liabilities mergeForm) $ universalApply assignment $ ProblemState jForms uForms uName
 |
  (index, mergeForm) <- removeLiabilities (length jForms - 1) (liabilities newForm) $ zip [0 ..] $ jForms,
  Just assignment <- [ intersection (formula mergeForm) (formula newForm) ]
 ] ++
 [
  universalApply assignment $ ProblemState jForms (take index uForms ++ addLiabilities (liabilities newForm) (uForms !! index) : drop (index + 1) uForms) uName
 |
  (index, mergeForm) <- zip [0 ..] uForms,
  Just assignment <- [ intersection (formula mergeForm) (formula newForm) ]
 ]

removeLiabilities :: Int -> [Int] -> [a] -> [a]
removeLiabilities _ [] states = states
removeLiabilities _ liabilities [] = []
removeLiabilities count (headLiability:tailLiabilities) (headState:tailStates)
 | headLiability == count = removeLiabilities (count - 1) tailLiabilities tailStates
 | headLiability > count  = removeLiabilities (count - 1) tailLiabilities (headState:tailStates) 
 | headLiability < count  = headState : removeLiabilities (count - 1) (headLiability : tailLiabilities) tailStates

axiomInstantiations :: ProblemState -> [ProblemState]
axiomInstantiations (ProblemState _ [] _ ) = []
axiomInstantiations (ProblemState jForms (headForm:tailForms) uName) = [ universalApply assignment $ ProblemState (justify (Ax n) headForm:jForms) tailForms (uName + size) | (n, Just assignment, size) <- zip3 [1..] (map ((`intersection` formula headForm) . ($ uName).constructor) axioms) (map airity $ axioms) ]

type ProofQueue = [ProblemState]
 
merge :: (Ord a) => [a] -> [a] -> [a]
merge [] [] = []
merge [] right = right
merge left [] = left
merge (headA : tailA) (headB : tailB)
 | headA < headB = headA : merge tailA (headB : tailB)
 | headA > headB = headB : merge (headA : tailA) tailB
 | otherwise = headA : merge tailA (headB : tailB)

takeStep :: ProofQueue -> ProofQueue
takeStep [] = []
takeStep (headState : tailState) = axiomInstantiations headState ++ merge (modusPonens headState) tailState 

findProof :: ProofQueue -> Maybe ProblemState
findProof [] = Nothing
findProof (p@(ProblemState _ [] _):_) = Just p
findProof pQueue = findProof $ takeStep pQueue

format :: [Formula] -> ProofQueue
format forms = [ProblemState [] [Statement form None [] | form <- forms] $ 1 + maximum (map vMax forms) ]
