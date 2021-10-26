module QCont

import Linear.Types
import Linear.Equality
import FunExt

import Syntax.PreorderReasoning


parameters (S : Type, P : S -> Type)

  F : Type -> Type
  F x = Sigma1 S (\ s => P s -<> x)
  
  Fmap : (f : x -<> y) -> (F x -<> F y)
  Fmap f (a # h) = a # (\ z => f (h z))

  data W : Type where
    Con : F W -<> W

  fold : (F x -<> x) -> W -<> x -- uses alg twice
  fold alg (Con w) = alg (Fmap (fold alg) w)   
  
  uniqueness : (alg : F x -<> x) -> 
               (g : W -<> x) -> 
               ((y : F W) -> g (Con y) = alg (Fmap g y)) ->
               (w : W) -> g w = fold alg w
  uniqueness alg g commutes (Con (s # h)) =
    trans (commutes (s # h))
          (cong (\ h => alg (s # h)) (funext _ _ pointwise))
    where
      pointwise : (p : P s) -> g (h p) = fold alg (h p)
      pointwise p = uniqueness alg g commutes (h p)


  indAlg : (0 Q : W -> Type) -> 
           let W' = Sigma0 W Q in
           (1 m : (1 s : S) -> 
                     (0 h : P s -<> W) -> 
                     ((1 p : P s) -> Q (h p)) -<> 
                     Q (Con (s # h))) ->
           F W' -<> W'
  indAlg q m (s # h') = Con (Fmap fst (s # h')) # m s _ (\p => snd (h' p))
  
  
  induction : (0 Q : W -> Type) ->
              (m : (1 s : S) -> 
                   (0 h : P s -<> W) -> 
                   ((1 p : P s) -> Q (h p)) -<> 
                   Q (Con (s # h))) ->
              (1 w : W) -> Q w
  induction q m w = replace0 q (sym (eq w)) (foldIt w) 
    where
      foldIt : (1 w : W) -> q (fst (fold (indAlg q m) w)) -- uses step twice
      foldIt w = snd (fold (indAlg q m) w)
    
      0 eq : (0 w : W) -> w = fst (fold (indAlg q m) w)
      eq (Con (s # h)) = cong (\ z => Con (s # z)) (funext h _ ih)
        where
          0 ih : (p : P s) -> h p = fst (fold (indAlg q m) (h p))
          ih p = eq (h p)
   
  initiality : (induction :(0 Q : W -> Type) -> 
                           (m : (1 s : S) -> 
                                (0 h : P s -<> W) -> 
                                ((1 p : P s) -> Q (h p)) -<> 
                                Q (Con (s # h))) ->
                           (1 w : W) -> Q w) ->
                (alg : F x -<> x) ->
                W -<> x
  initiality induction alg = induction (\_ => x) (\s, _, ih => alg (s # ih)) 

  
  indComp : (0 Q : W -> Type) ->
            (m : (1 s : S) -> 
                 (0 h : P s -<> W) -> 
                 ((1 p : P s) -> Q (h p)) -<> 
                 Q (Con (s # h))) ->
            (1 s : S) -> 
            (1 h : P s -<> W) ->
            induction Q m (Con (s # h)) = m s h (\p => induction Q m (h p)) 
  indComp q m s h = Calc $
    |~ induction q m (Con (s # h))
    ~~ q (fst (fold (indAlg q m) (Con (s # h)))) ...(?la)
    ~~ m s h (\p => induction q m (h p))  ...(?last_step)
