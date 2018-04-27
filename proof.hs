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
 show (Statement form just _) = show just ++ ' ' : show form

updateForm :: (Formula -> Formula) -> Statement -> Statement
updateForm f state@(Statement form _ _) = state {formula = f form}

justify :: Justification -> Statement -> Statement
justify just state = state {justification = just}

data ProblemState = ProblemState {
  justifiedFormulae   :: [Statement],
  unjustifiedFormulae :: [Statement],
  unusedName :: Int
 }

instance Show ProblemState where
 show (ProblemState jForms uForms _) = (reverse uForms ++ jForms) >>= (('\n' :) . show)

proofSize :: ProblemState -> Int
proofSize = ((+) . length . justifiedFormulae) <*> (length . unjustifiedFormulae)

universalApply :: Assignment -> ProblemState -> ProblemState
universalApply assignment (ProblemState jForms uForms uName) = ProblemState ((map $ updateForm $ apply assignment) jForms) ((map $ updateForm $ apply assignment) uForms) uName

modusPonens :: ProblemState -> ProofQueue
modusPonens pState@(ProblemState _ [] _) = [pState]
modusPonens (ProblemState jForms (headForm:tailForms) uName) = [ProblemState ((justify MP headForm):jForms) (tailForms ++ [implication, antecedent]) (uName + 1)]
 where
  newLiabilities = liabilities headForm ++ [length jForms]
  antecedent     = Statement (Variable uName) None newLiabilities
  implication    = Statement (If (Variable uName) (formula headForm)) None newLiabilities
  
unification :: Statement -> ProblemState -> ProofQueue
unification (Statement form _ liabilities) (ProblemState jForms uForms uName ) = []

axiomInstantiations :: ProblemState -> [ProblemState]
axiomInstantiations (ProblemState jForms [] _ ) = []
axiomInstantiations (ProblemState jForms (headForm:tailForms) uName) = [ universalApply assignment $ ProblemState (justify (Ax n) headForm:jForms) tailForms (uName + size) | (n, Just assignment, size) <- zip3 [1..] (map ((`intersection` formula headForm) . ($ uName).constructor) axioms) (map airity $ axioms) ]

type ProofQueue = [ProblemState]
 
merge :: ProofQueue -> ProofQueue -> ProofQueue
merge [] [] = []
merge [] proofQueue = proofQueue
merge proofQueue [] = proofQueue
merge (headStateA : tailStatesA) (headStateB : tailStatesB)
 | proofSize (headStateA) < proofSize (headStateB) = headStateA : merge tailStatesA (headStateB : tailStatesB)
 | proofSize (headStateA) > proofSize (headStateB) = headStateB : merge (headStateA : tailStatesA) tailStatesB
 | otherwise = headStateA : merge tailStatesA (headStateB : tailStatesB)

takeStep :: ProofQueue -> ProofQueue
takeStep [] = []
takeStep (headState : tailState) = axiomInstantiations headState ++ merge (modusPonens headState) tailState 

findProof :: ProofQueue -> Maybe ProblemState
findProof [] = Nothing
findProof (p@(ProblemState _ [] _):_) = Just p
findProof pQueue = findProof $ takeStep pQueue

format :: [Formula] -> ProofQueue
format forms = [ProblemState [] [Statement form None []|form <- forms] $ 1 + maximum (map vMax forms) ]
main = print(findProof (format [If (Atom 'A') (Atom 'A')]))
