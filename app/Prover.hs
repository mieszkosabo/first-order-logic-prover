module Prover where

import Formula
import Functions
import Data.List (nub)
import Control.Monad
import Utils

type Arity = Int
type Signature = [(FunName, Arity)]

sigT :: Term -> Signature
sigT (Var _) = []
sigT (Fun f ts) = nub $ (f, length ts) : concatMap sigT ts

sig :: Formula -> Signature
sig T = []
sig F = []
sig (Rel r ts) = concatMap sigT ts
sig (Not phi) = sig phi
sig (And phi psi) = nub $ sig phi ++ sig psi
sig (Or phi psi) = nub $ sig phi ++ sig psi
sig (Implies phi psi) = nub $ sig phi ++ sig psi
sig (Iff phi psi) = nub $ sig phi ++ sig psi
sig (Exists _ phi) = sig phi
sig (Forall _ phi) = sig phi

constants :: Signature -> [Term]
constants s = [Fun c [] | (c, 0) <- s]

signatureWithoutConstants :: Signature -> Signature
signatureWithoutConstants = filter (\(_, n) -> n > 0)

choose :: Int -> [a] -> [[a]]
choose = replicateM

createFunctionFromPairs pairs = foldr (\(x, y) fun -> update fun x y) (\x -> Var x) pairs

groundInstances :: Formula -> [Term] -> [Formula]
groundInstances phi ts = let
  freeVars = fv phi
  possTermsAssignments = choose (length freeVars) ts
  pairs = map (zip freeVars) possTermsAssignments
  subFuns = map createFunctionFromPairs pairs
  in map (`subst` phi) subFuns
  
atomicFormulas :: Formula -> [Formula]
atomicFormulas T = []
atomicFormulas F = []
atomicFormulas phi@(Rel _ ts) = [phi]
atomicFormulas (Not phi) = atomicFormulas phi
atomicFormulas (And phi psi) = nub $ atomicFormulas phi ++ atomicFormulas psi
atomicFormulas (Or phi psi) = nub $ atomicFormulas phi ++ atomicFormulas psi
atomicFormulas (Implies phi psi) = nub $ atomicFormulas phi ++ atomicFormulas psi
atomicFormulas (Iff phi psi) = nub $ atomicFormulas phi ++ atomicFormulas psi
atomicFormulas (Exists x phi) = atomicFormulas phi
atomicFormulas (Forall x phi) = atomicFormulas phi

sat :: Formula -> Bool
sat phi = or [ev int phi | int <- functions atoms [True, False]]
  where atoms = atomicFormulas phi
        
        ev :: (Formula -> Bool) -> Formula -> Bool
        ev int T = True
        ev int F = False
        ev int atom@(Rel _ _) = int atom
        ev int (Not φ) = not (ev int φ)
        ev int (Or φ ψ) = ev int φ || ev int ψ
        ev int (And φ ψ) = ev int φ && ev int ψ
        ev _ φ = error $ "unexpected formula: " ++ show φ

isHerbrandUniverseFinite :: Signature -> Bool
isHerbrandUniverseFinite sig = null $ signatureWithoutConstants sig

generateElementsOfHerbrandUniverse :: Formula -> Signature -> [Term]
generateElementsOfHerbrandUniverse phi sig = if isHerbrandUniverseFinite sig
  then herbrandConstants
  else generateAllElements herbrandConstants (signatureWithoutConstants sig)
    where herbrandConstants = if null (constants sig) then [Fun (freshVariant "c" phi) []] else constants sig

-- recursively generate all herbrand elements eg. c, f(c), f(f(c)), etc.
generateAllElements :: [Term] -> Signature -> [Term]
generateAllElements set sig = set ++ generateAllElements (concatMap (step set) sig) sig 
  where 
    step :: [Term] -> (FunName, Arity) -> [Term]
    step elements (fName, arity) = map (Fun fName) (choose arity elements)

removePrefixOfUniversalQuantifiers :: Formula -> Formula
removePrefixOfUniversalQuantifiers (Forall _ a) = removePrefixOfUniversalQuantifiers a
removePrefixOfUniversalQuantifiers b = b

prover :: Formula -> Bool
prover phi = let
  closed = generalise phi
  negated = Not closed
  skolemised = skolemise negated
  withoutPrefix = removePrefixOfUniversalQuantifiers skolemised
  isFinite = isHerbrandUniverseFinite $ sig withoutPrefix
  groundTerms  = generateElementsOfHerbrandUniverse withoutPrefix (sig withoutPrefix)
  in if isFinite then
    -- (C.2)
    not $ sat $ foldr And T (groundInstances withoutPrefix groundTerms)
    else if null $ fv withoutPrefix then
      -- (C.1)
      not $ sat withoutPrefix
  else 
    -- (A or B)
    startChecking 1 withoutPrefix groundTerms

startChecking :: Int -> Formula -> [Term] -> Bool
startChecking howManyElementsToTake phi groundTerms = 
  isTauto || startChecking (howManyElementsToTake + 1) phi groundTerms
  where
    isTauto = not $ sat $ foldr And T gi
    gi = groundInstances phi termsToCheck
    termsToCheck = take howManyElementsToTake groundTerms