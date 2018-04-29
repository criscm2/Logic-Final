import Prover
import Formula
import Meredith

main = print $ findProof axioms $ format [If (Atom 'A') (Atom 'A')]
