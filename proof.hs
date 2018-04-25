import Intersection
import Formula
import Assignment
import Lukasiewicz
import Control.Arrow

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
  unusedName :: Integer
 }

instance Show ProblemState where
 show (ProblemState jForms uForms _) = (reverse uForms ++ jForms) >>= (('\n' :) . show)

proofSize :: ProblemState -> Int
proofSize = ((+) . length . justifiedFormulae) <*> (length . unjustifiedFormulae)

universalApply :: Assignment -> ProblemState -> ProblemState
universalApply assignment (ProblemState jForms uForms uName) = ProblemState ((map $ updateForm $ apply assignment) jForms) ((map $ updateForm $ apply assignment) uForms) uName

modusPonens :: ProblemState -> ProblemState
modusPonens pState@(ProblemState _ [] _) = pState
modusPonens (ProblemState jForms (headForm:tailForms) uName) = ProblemState ((justify MP headForm):jForms) (tailForms ++ [implication, antecedent]) (uName + 1)
 where
  newLiabilities = liabilities headForm ++ [length jForms]
  antecedent     = Statement (Variable uName) None newLiabilities
  implication    = Statement (If (Variable uName) (formula headForm)) None newLiabilities

axiomInstantiations :: ProblemState -> [ProblemState]
axiomInstantiations (ProblemState jForms [] _ ) = []
axiomInstantiations (ProblemState jForms (headForm:tailForms) uName) = [ universalApply assignment $ ProblemState (justify (Ax n) headForm:jForms) tailForms (uName + size) | (n, (Just assignment, size)) <- zip [1..] $ map (first $ (`intersection` formula headForm) . ($ uName)) axioms ]

justifyFormula :: ProblemState -> [ProblemState]
justifyFormula (ProblemState jForms [] _) = [] 
justifyFormula pState = modusPonens pState :  axiomInstantiations pState

type ProofQueue = [ProblemState]

insert :: ProblemState -> ProofQueue -> ProofQueue
insert pState [] = [pState]
insert pState proofQueue
 | proofSize (proofQueue !! halfway) > proofSize pState  = insert pState (take halfway proofQueue) ++ drop halfway proofQueue
 | proofSize (proofQueue !! halfway) == proofSize pState = take halfway proofQueue ++ (pState : drop halfway proofQueue)
 | otherwise                                             = take (halfway + 1) proofQueue ++ insert pState (drop (halfway + 1) proofQueue)
 where halfway = (length proofQueue) `div` 2

takeStep :: ProofQueue -> ProofQueue
takeStep [] = []
takeStep (headState : tailState) = axiomInstantiations headState ++ insert (modusPonens headState) tailState 

findProof :: ProofQueue -> Maybe ProblemState
findProof [] = Nothing
findProof (p@(ProblemState _ [] _):_) = Just p
findProof pQueue = findProof $ takeStep pQueue

format :: [Formula] -> ProofQueue
format forms = [ProblemState [] [Statement form None []|form <- forms] $ 1 + maximum (map vMax forms) ]
