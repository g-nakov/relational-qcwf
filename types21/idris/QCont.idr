module QCont

import Linear.Types
import Linear.Equality
import FunExt

parameters (a : Type, b : a -> Type)

  F : Type -> Type
  F x = Sigma1 a (\ z => b z -<> x)
  
  Fmap : (f : x -<> y) -> (F x -<> F y)
  Fmap f (a # h) = a # (\ z => f (h z))

  data W : Type where
    Con : F W -<> W

  fold : (F x -<> x) -> W -<> x -- uses alg twice
  fold alg (Con (a # h)) = alg (a # \z => fold alg (h z))

  uniqueness : (alg : F x -<> x) -> (h : W -<> x) -> ((y : F W) -> h (Con y) = alg (Fmap h y)) -> (x : W) -> h x = fold alg x
  uniqueness alg h commutes (Con (x # g)) =
    trans (commutes (x # g))
          (cong (\ z => alg (x # z)) (funext _ _ pointwise))
    where
      pointwise : (y : b x) -> h (g y) = fold alg (g y)
      pointwise y = uniqueness alg h commutes (g y)

{-
  induction' : (p : W -> Type) ->
               (step : (1 z : a) -> (0 h : b z -<> W) -> (1 ih : (1 y : b z) -> p (h y)) -> p (Con (Sig1 z h))) ->
               (1 x : W) -> p x -- uses step twice
  induction' p step (Con (Sig1 z h)) = step z h (\ y => induction' p step (h y))
-}


  indAlg : (0 p : W -> Type) -> let W' = Sigma0 W p in
           (1 step : (1 z : a) -> (0 h : b z -<> W) -> (1 ih : (1 y : b z) -> p (h y)) -> p (Con (z # h))) ->
           F W' -<> W'
  indAlg p step (z # h) = (Con ( z # \ y => fst (h y))) # (step z _ (\ y => snd (h y)))

  induction : (0 p : W -> Type) ->
              (step : (1 z : a) -> (0 h : b z -<> W) -> (1 ih : (1 y : b z) -> p (h y)) -> p (Con (z # h))) ->
              (1 x : W) -> p x
  induction p step x = replace0 p (sym (eq x)) (foldIt x) where
    foldIt : (1 x : W) -> p (fst (fold (indAlg p step) x)) -- uses step twice
    foldIt x = snd (fold (indAlg p step) x)
    0 eq : (0 x : W) -> x = fst (fold (indAlg p step) x)
    eq (Con (x #  h)) = cong (\ z => Con (x # z)) (funext h _ ih)
      where
        0 ih : (y : b x) -> h y = fst (fold (indAlg p step) (h y))
        ih y = eq (h y)

  initiality : (induction :(0 p : W -> Type) -> (step : (1 z : a) -> (0 h : b z -<> W) -> 
                           (1 ih : (1 y : b z) -> p (h y)) -> p (Con (z # h))) ->
                           (1 x : W) -> p x) ->
                (alg : F x -<> x) -> W -<> x
  initiality induction alg w = induction (\_ => x) (\z, ih, pz => alg (z # pz)) w  
