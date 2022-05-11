module Prover where

import Formula
import Functions
import Data.List (nub)
import Utils

prover :: Formula -> Bool
prover = aedecide



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

choose :: Int -> [a] -> [[a]]
choose n list = sequence $ replicate n list
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

removePrefixOfUniversalQuantifiers :: Formula -> Formula
removePrefixOfUniversalQuantifiers (Forall _ a) = removePrefixOfUniversalQuantifiers a
removePrefixOfUniversalQuantifiers b = b

aedecide :: Formula -> Bool
aedecide phi = let
  closed = generalise phi -- 1
  negated = Not closed -- 2
  skolemised = skolemise negated -- 3
  withoutPrefix = removePrefixOfUniversalQuantifiers skolemised -- 4
  -- if herbrand universe is empty then we add an additional constant, else we dont have to
  consts = if null (constants $ sig withoutPrefix) then [Fun (freshVariant "c" withoutPrefix) []] else constants $ sig withoutPrefix
  gi = groundInstances withoutPrefix consts -- 5
  in not $ sat $ foldr And T gi