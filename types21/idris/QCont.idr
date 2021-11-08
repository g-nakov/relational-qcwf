module QCont

import Linear.Types
import Linear.Equality
import FunExt

import Syntax.PreorderReasoning
import Data.Nat
import Data.Vect

parameters (S : Type, P : S -> Type)

  0 F : Type -> Type
  F x = Sigma1 S (\ s => P s -<> x)
  
  infix 10 <$#>
  
  (<$#>) : (f : x -<> y) -> (F x -<> F y)
  f <$#> (a # h) = a # (\ z => f (h z))

  data W : Type where
    Con : F W -<> W

  fold : (F x -<> x) -> W -<> x -- uses alg twice
  fold alg (Con w) = alg (fold alg <$#> w)   
  
  -- morphisms are equal if pointwise equal
  uniqueness : (alg : F x -<> x) -> 
               (g : W -<> x) -> 
               ((y : F W) -> g (Con y) = alg (g <$#> y)) ->
               (w : W) -> g w = fold alg w
  uniqueness alg g commutes (Con (s # h)) =
    trans (commutes (s # h))
          (cong (\ h => alg (s # h)) (funext _ _ pointwise))
    where
      pointwise : (p : P s) -> g (h p) = fold alg (h p)
      pointwise p = uniqueness alg g commutes (h p)


  indAlg : (0 Q : W -> Type) -> 
           let W' = Sigma0 W Q in
           (1 m : (1 s : S) -> (0 h : P s -<> W) -> 
                  ((1 p : P s) -> Q (h p)) -<> Q (Con (s # h))) ->
           F W' -<> W'
  indAlg q m (s # h') = Con (fst <$#> (s # h')) # m s _ (\p => snd (h' p))
  
  0
  eqFstFold : (0 Q : W -> Type) ->
              (1 m : (1 s : S) -> (0 h : P s -<> W) -> 
                     ((1 p : P s) -> Q (h p)) -<> Q (Con (s # h))) ->
              (0 w : W) -> w = fst (fold (indAlg Q m) w)
  eqFstFold q m (Con (s # h)) = cong (\z => Con (s # z)) (funext h _ ih)
    where
      0 ih : (p : P s) -> h p = fst (fold (indAlg q m) (h p))
      ih p = eqFstFold q m (h p)
  
  induction : (0 Q : W -> Type) ->
              (m : (1 s : S) -> (0 h : P s -<> W) -> 
                   ((1 p : P s) -> Q (h p)) -<> Q (Con (s # h))) ->
              (1 w : W) -> Q w
  induction q m w = replace0 q (sym (eqFstFold q m w)) (foldIt w) 
    where
      foldIt : (1 w : W) -> q (fst (fold (indAlg q m) w)) -- uses step twice
      foldIt w = snd (fold (indAlg q m) w)
    
  initiality : (induction :(0 Q : W -> Type) -> 
                           (m : (1 s : S) -> 
                                (0 h : P s -<> W) -> 
                                ((1 p : P s) -> Q (h p)) -<> 
                                Q (Con (s # h))) ->
                           (1 w : W) -> Q w) ->
                (alg : F x -<> x) ->
                W -<> x
  initiality induction alg = induction (\_ => x) (\s, _, ih => alg (s # ih)) 

  0
  indComp : (0 Q : W -> Type) ->
            (m : (1 s : S) -> 
                 (0 h : P s -<> W) -> 
                 ((1 p : P s) -> Q (h p)) -<> 
                 Q (Con (s # h))) ->
            (1 s : S) -> 
            (1 h : P s -<> W) ->
            induction Q m (Con (s # h)) = m s h (\p => induction Q m (h p)) 
  indComp q m s h = ?a
  {- Calc $
    |~ induction q m (Con (s # h))
    ~~ replace0 q (sym (eqFstFold q m (Con (s # h)))) (snd (fold (indAlg q m) (Con (s # h)))) ...(Refl)
    ~~ m s h (\p => induction q m (h p))  ...(?last_step) -}


