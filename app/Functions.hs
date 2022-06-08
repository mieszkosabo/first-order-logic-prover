module Functions where

import Formula
import Control.Monad.State

import Utils

renameT :: VarName -> VarName -> Term -> Term
renameT x y (Var z)
  | z == x = Var y
  | otherwise = Var z
renameT x y (Fun f ts) = Fun f (map (renameT x y) ts)

rename :: VarName -> VarName -> Formula -> Formula
rename x y T = T
rename x y F = F
rename x y (Rel r ts) = Rel r (map (renameT x y) ts)
rename x y (Not phi) = Not (rename x y phi)
rename x y (And phi psi) = And (rename x y phi) (rename x y psi)
rename x y (Or phi psi) = Or (rename x y phi) (rename x y psi)
rename x y (Implies phi psi) = Implies (rename x y phi) (rename x y psi)
rename x y (Iff phi psi) = Iff (rename x y phi) (rename x y psi)
rename x y (Forall z phi)
  | z == x = Forall z phi
  | otherwise = Forall z (rename x y phi)
rename x y (Exists z phi)
  | z == x = Exists z phi
  | otherwise = Exists z (rename x y phi)

nnf :: Formula -> Formula
nnf (Implies a b) = Or (nnf $ Not a) (nnf b)
nnf (Iff a b) = Or (And (nnf a) (nnf b)) (And (nnf $ Not a) (nnf $ Not b))
nnf (Not a) = case a' of
  (And p q) -> Or (nnf $ Not p) (nnf $ Not q)
  (Or p q) -> And (nnf $ Not p) (nnf $ Not q)
  (Not b) -> b
  F -> T
  T -> F
  r@(Rel _ _) -> Not r
  (Exists x phi) -> Forall x (nnf $ Not phi)
  (Forall x phi) -> Exists x (nnf $ Not phi)
  where a' = nnf a
nnf (Or a b) = Or (nnf a) (nnf b)
nnf (And a b) = And (nnf a) (nnf b)
nnf (Exists x a) = Exists x (nnf a)
nnf (Forall x a) = Forall x (nnf a)
nnf a = a

-- prenex normal form (all quantifiers in front)
pnf :: Formula -> Formula
pnf = pnf' . nnf

-- operates on formulas in nnf form
pnf' T = T
pnf' F = F
pnf' (Not a) = Not $ pnf' a
pnf' r@(Rel _ _) = r
pnf' (Forall x phi) = Forall x (pnf' phi)
pnf' (Exists x phi) = Exists x (pnf' phi)
pnf' (And a b) = pnf'BinAnd (pnf' a) (pnf' b)
pnf' (Or a b) = pnf'BinOr (pnf' a) (pnf' b)

pnf'QQ q1 x a q2 y b op = let
    x' = freshVariant2 x a b
    a' = rename x x' a
    y' = freshVariant2 y a' b
    b' = rename y y' b
    in q1 x' (q2 y' (pnf' (op a' b')))

pnf'Q q x a b op = let
    x' = freshVariant2 x a b
    a' = rename x x' a
    in q x' (pnf' (op a' b))

pnf'BinAnd (Forall x a) (Forall y b) = let
    x' = if x == y then x else freshVariant2 x a b
    a' = if x == y then a else rename x x' a
    b' = if x == y then b else rename y x' b
    in Forall x' (pnf' (And a' b'))
pnf'BinAnd a b = pnf'Bin a b And

pnf'BinOr (Exists x a) (Exists y b) = let
    x' = if x == y then x else freshVariant2 x a b
    a' = if x == y then a else rename x x' a
    b' = if x == y then b else rename y x' b
    in Exists x' (pnf' (Or a' b'))
pnf'BinOr a b = pnf'Bin a b Or

pnf'Bin (Forall x a) (Forall y b) op = pnf'QQ Forall x a Forall y b op
pnf'Bin (Forall x a) (Exists y b) op = pnf'QQ Forall x a Exists y b op
pnf'Bin (Exists x a) (Exists y b) op = pnf'QQ Exists x a Exists y b op
pnf'Bin (Exists x a) (Forall y b) op = pnf'QQ Exists x a Forall y b op

pnf'Bin (Exists x a) b op = pnf'Q Exists x a b op
pnf'Bin b (Exists x a) op = pnf'Q Exists x a b op
pnf'Bin (Forall x a) b op = pnf'Q Forall x a b op
pnf'Bin b (Forall x a) op = pnf'Q Forall x a b op

pnf'Bin a b op = op a b

generalise :: Formula -> Formula
generalise phi = go $ fv phi
  where go [] = phi
        go (x:xs) = Forall x $ go xs

-- quantify existentially all the free variables
existentialise :: Formula -> Formula
existentialise phi = go $ fv phi
  where go [] = phi
        go (x:xs) = Exists x $ go xs

fresh :: Formula -> Formula
fresh phi = evalState (go phi) []
  where go :: Formula -> State [VarName] Formula
        go T = return T
        go F = return F
        go phi@(Rel _ _) = return phi
        go (Not phi) = liftM Not (go phi)
        go (And phi psi) = liftM2 And (go phi) (go psi)
        go (Or phi psi) = liftM2 Or (go phi) (go psi)
        go (Implies phi psi) = liftM2 Implies (go phi) (go psi)
        go (Iff phi psi) = liftM2 Iff (go phi) (go psi)
        go (Forall x phi) = go2 Forall x phi
        go (Exists x phi) = go2 Exists x phi
        
        go2 quantifier x phi =
          do xs <- get
             let y = head [y | y <- variants x, not $ y `elem` xs]
             let psi = rename x y phi
             put $ y : xs
             liftM (quantifier y) $ go psi


-- TODO: add miniscoping for perf improvements
skolemise :: Formula -> Formula
skolemise =
  pnf . replaceWithSkolemFunctions . fresh . nnf . existentialise
  
replaceWithSkolemFunctions :: Formula -> Formula
replaceWithSkolemFunctions phi = evalState (replaceWithSkolemFunctions' phi) initialState

type Substitution = VarName -> Term

substT :: Substitution -> Term -> Term
substT σ (Var x) = σ x
substT σ (Fun f ts) = Fun f (map (substT σ) ts)

subst :: Substitution -> Formula -> Formula
subst _ T = T
subst _ F = F
subst σ (Rel r ts) = Rel r $ map (substT σ) ts
subst σ (Not phi) = Not $ subst σ phi
subst σ (And phi psi) = And (subst σ phi) (subst σ psi)
subst σ (Or phi psi) = Or (subst σ phi) (subst σ psi)
subst σ (Implies phi psi) = Implies (subst σ phi) (subst σ psi)
subst σ (Iff phi psi) = Iff (subst σ phi) (subst σ psi)
subst σ (Exists x phi) = Exists x (subst (update σ x (Var x)) phi)
subst σ (Forall x phi) = Forall x (subst (update σ x (Var x)) phi)

data SkolemState = SkolemState {
  scope :: [VarName],
  substitutions :: Substitution
  }

initialState :: SkolemState
initialState = SkolemState {
  scope = [],
  -- this is like a id Subtitution function, it will be extended during the algorithm
  substitutions = Var
  }

replaceWithSkolemFunctions' :: Formula -> State SkolemState Formula
replaceWithSkolemFunctions' T = return T
replaceWithSkolemFunctions' F = return F
replaceWithSkolemFunctions' (Not r@(Rel _ _)) = do
  r' <- replaceWithSkolemFunctions' r
  return $ Not r'
-- following 3 cases are undefined bc we are in nnf
replaceWithSkolemFunctions' (Implies _ _) = undefined
replaceWithSkolemFunctions' (Iff _ _) = undefined
replaceWithSkolemFunctions' (Not a) = undefined
replaceWithSkolemFunctions' (And a b) = do
  currState <- get
  a' <- replaceWithSkolemFunctions' a
  put currState
  b' <- replaceWithSkolemFunctions' b
  return $ And a' b'
replaceWithSkolemFunctions' (Or a b) = do
  currState <- get
  a' <- replaceWithSkolemFunctions' a
  put currState
  b' <- replaceWithSkolemFunctions' b
  return $ Or a' b'
replaceWithSkolemFunctions' (Exists x phi) = do
  sc <- gets scope
  modify $ \s -> s { substitutions = update (substitutions s) x (Fun x (map Var sc))}
  phi' <- replaceWithSkolemFunctions' phi
  return phi'
replaceWithSkolemFunctions' (Forall x phi) = do
  modify $ \s -> s { scope = x:scope s }
  phi' <- replaceWithSkolemFunctions' phi
  return $ Forall x phi'
replaceWithSkolemFunctions' (Rel relName terms) = do
  subFun <- gets substitutions
  return $ Rel relName (map (substT subFun) terms)
