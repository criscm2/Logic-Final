import Intersection
import Formula
import Assignment
import Control.Arrow

axioms = [
		(If 
			(Variable (-1))
			(If
				(Variable (-2))
				(Variable (-1))
			)
		),
		(If
			(If 
				(Variable (-1))
				(If 
					(Variable (-2))
					(Variable (-3))
				)
			)
			(If
				(If 
					(Variable (-1))
					(Variable (-2))
				)
				(If 
					(Variable (-1))
					(Variable (-3))
				)
			)
		),
		(If
			(If
				(Neg
					(Variable (-1))
				)
				(Neg
					(Variable (-2))
				)
			)
			(If
				(Variable (-2))
				(Variable (-1))
			)
		)
	]

data Justification = Axiom Int | MP

instance Show Justification where
 show (Axiom x) = "(Axiom " ++ show x ++ ")" 
 show MP = "(Modus Ponens)" 

{- TODO label modus ponens -}

data ProblemState = ProblemState {
		justifiedFormulae   :: [(Formula, Justification)],
		unjustifiedFormulae :: [Formula],
		unusedName :: Integer
	}

proofLineJ :: (Formula, Justification) -> String
proofLineJ (form, just) = '\n': show just ++ ' ' : show form

instance Show ProblemState where
 show (ProblemState jForms uForms _) = ((reverse uForms) >>= (('\n':).show)) ++ (jForms >>= proofLineJ)

proofSize :: ProblemState -> Int
proofSize = ((+) . length . justifiedFormulae) <*> (length . unjustifiedFormulae)

universalApply :: Assignment -> ProblemState -> ProblemState
universalApply assignment (ProblemState jForms uForms uName) = ProblemState (map (first (apply assignment)) jForms) (map (apply assignment) uForms) uName

modusPonens :: ProblemState -> ProblemState
modusPonens pState@(ProblemState _ [] _) = pState
modusPonens (ProblemState jForms (headForm:tailForms) uName) = (ProblemState ((headForm, MP):jForms) (tailForms ++ [If (Variable uName) (headForm),Variable uName]) (uName + 1))

axiomInstantiations :: ProblemState -> [ProblemState]
axiomInstantiations (ProblemState jForms [] _ ) = []
axiomInstantiations pState@(ProblemState jForms (headForm:tailForms) uName) = [ universalApply assignment $ ProblemState ((headForm, Axiom n):jForms) tailForms uName | (n, Just assignment) <- zip [1..] $ map (`intersection` headForm) axioms ]

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

insert' x [] = [x]
insert' x queue
 | queue !! halfway > x  = insert' x (take halfway queue) ++ drop halfway queue
 | queue !! halfway == x = take halfway queue ++ (x : drop halfway queue)
 | otherwise             = take (halfway + 1) queue ++ insert' x (drop (halfway + 1) queue)
 where halfway = (length queue) `div` 2

takeStep :: ProofQueue -> ProofQueue
takeStep [] = []
takeStep (headState : tailState) = foldr insert tailState $ justifyFormula headState

findProof :: ProofQueue -> Maybe ProblemState
findProof [] = Nothing
findProof (p@(ProblemState _ [] _):_) = Just p
findProof pQueue = findProof $ takeStep pQueue
