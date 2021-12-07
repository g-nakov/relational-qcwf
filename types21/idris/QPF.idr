module QPF

import Linear.Types
import Linear.Equality
import FunExt

data Desc : Type where
  Id' : Desc
  Const' : Type -> Desc
  Prod' : Desc -> Desc -> Desc
  Sum' : Desc -> Desc -> Desc
  With' : Desc -> Desc -> Desc
  
0 qpf : Desc -> Type -> Type
qpf Id' x = x
qpf (Const' x) _  =  x
qpf (Prod' f g) x = Pair1 (qpf f x) (qpf g x)
qpf (Sum' f g) x = Sum (qpf f x) (qpf g x)
qpf (With' f g) x = With (qpf f x) (qpf g x)

0 lift : (d : Desc) -> (p : x -> Type) -> qpf d x -> Type
lift Id' p f = p f
lift (Const' x) p f = x
lift (Prod' c d) p (f #  g) = LPair (lift c p f) (lift d p g)
lift (Sum' c d) p (Inl f) = lift c p f
lift (Sum' c d) p (Inr g) = lift d p g
lift (With' c d) p f = With (lift c p (f True)) (lift d p (f False))


dist : {0 x : Type} -> {0 y : x -> Type} -> 
       (d : Desc) -> qpf d (Sigma0 x y) -<> Sigma0 (qpf d x) (lift d y)
dist Id' (x # y)  = x # y
dist (Const' _) x = x # x
dist (Prod' c d) (x # y) = 
  let (f # lf) = dist c x
      (g # lg) = dist d y
  in  (f # g) # (lf # lg)
dist (Sum' c d) (Inl f) = 
  let (f # lf) = dist c f
  in  (Inl f) # lf
dist (Sum' c d) (Inr g) =
  let (g # lg) = dist d g
  in  (Inr g) # lg
dist (With' c d) w = 
   (h w) # (j w) where
    0 h : With (qpf c (Sigma0 x y)) (qpf d (Sigma0 x y)) -> With (qpf c x) (qpf d x) 
    h u True  = fst (dist c (u True))
    h u False = fst (dist d (u False))
    
    j : (1 u : With (qpf c (Sigma0 x y)) (qpf d (Sigma0 x y))) -> 
        With (lift c y (h u True)) (lift d y (h u False))
    j u True  = snd (dist c (u True))
    j u False = snd (dist d (u False))


distW : {0 x : Type} -> {0 y : x -> Type} -> 
        (d : Desc) -> qpf d (DWith x y) -<> DWith (qpf d x) (lift d y) 
distW Id' (z #  w) = z # (\x => if x then (w True) else (w False)) 
distW (Const' z) w = w # (\x => if x then (w # Refl) else w)
distW (Prod' c d) (f # g) =
  let (f # lf) = distW c f
      (g # lg) = distW d g
  in (f # g) # (\x => if x then (let (u # Refl) = lf True
                                     (v # Refl) = lg True
                                 in  (u # v) # Refl)
                           else  lf False # lg False) 
distW (Sum' c d) (Inl f) =
  let (x # lf) = distW c f
  in (Inl x) # (\b => if b then (let (u # Refl) = lf True in (Inl u) # Refl)
                           else (let u = lf False in u))
distW (Sum' c d) (Inr g) =
  let (x # lg) = distW d g
  in (Inr x) # (\b => if b then (let (u # Refl) = lg True in (Inr u) # Refl)
                           else (let u = lg False in u))
                                                    
distW (With' c d) w = (h w) # (j w)
where
  0 h : With (qpf c (DWith x y)) (qpf d (DWith x y)) -<> With (qpf c x) (qpf d x)
  h w True = fst (distW c (w True))
  h w False = fst (distW d (w False))

  h1 : With (qpf c (DWith x y)) (qpf d (DWith x y)) -<> With (qpf c x) (qpf d x)
  h1 w True  = extractSingleton (snd (distW c (w True))  True)
  h1 w False = extractSingleton (snd (distW d (w False)) True)

  0 eq : (w : With (qpf c (DWith x y)) (qpf d (DWith x y))) -> h1 w = h w
  eq w = funext (h1 w) (h w)
                (\ b => if b then extractSingletonExtractsSingleton (snd (distW c (w True)) True)
                             else extractSingletonExtractsSingleton (snd (distW d (w False)) True))

  j : (1 w : With (qpf c (DWith x y)) (qpf d (DWith x y))) ->
      With (Sigma1 (With (qpf c x) (qpf d x)) (\z => z = h w)) (lift (With' c d) y (h w))
  j w True = (h1 w) # (promoteEq (eq w))
  j w False = \ b => if b then snd (distW c (w True)) False else snd (distW d (w False)) False

data W : (0 u : Desc) -> Type where
  Con : qpf u (W u)  -<> W u

fmap : (d : Desc) -> (f : a -<> b) -> qpf d a -<> qpf d b
fmap Id' f x = f x 
fmap (Const' _) _ x = x
fmap (Prod' c d) f x = bimap (fmap c f) (fmap d f) x 
fmap (Sum' c d) f x = bimap (fmap c f) (fmap d f) x
fmap (With' c d) f x = bimap (fmap c f) (fmap d f) x

0 fmap_id : {c : Desc} -> {d : Desc} -> 
            (1 x : qpf d (W c)) -> x = fmap {b = W c} d (\1 x => x) x
fmap_id {d = Id'} x = Refl
fmap_id {d = (Const' _)} _ = Refl
fmap_id {d = (Prod' c d)} (x # y) = lcong2 (#) (fmap_id x) (fmap_id y)
fmap_id {d = (Sum' c d)} (Inl x) = lcong Inl (fmap_id x)
fmap_id {d = (Sum' c d)} (Inr y) = lcong Inr (fmap_id y)
fmap_id {d = (With' c d)} x = funext _ _ (\b => if b then fmap_id (x True) else fmap_id (x False))

mutual
  fold_h : {c : Desc} -> (d : Desc) -> (qpf c x -<> x) -> qpf d (W c) -<> qpf d x
  fold_h Id' alg (Con w) = alg (fold_h c alg w)
  fold_h (Const' y) alg w = w
  fold_h (Prod' c d) alg w = bimap (fold_h c alg) (fold_h d alg) w
  fold_h (Sum' c d) alg w = bimap (fold_h c alg) (fold_h d alg) w
  fold_h (With' c d) alg w = with With.bimap (bimap (fold_h c alg) (fold_h d alg) w)
  
  fold : (d : Desc) -> (qpf d x -<> x) -> W d -<> x
  fold d alg (Con w) = alg (fold_h d alg w)

mutual
  0 uniq_h : {c : Desc} -> (d : Desc) -> 
             (h : W c -<> x) -> 
             (alg : qpf c x -<> x) ->
             ((1 y : qpf c (W c)) -> h (Con y) = alg (fmap c h y)) ->
             (w : qpf d (W c)) -> fmap d h w = fold_h {c = c} d alg w
  uniq_h Id' h alg commutes (Con y) = trans (commutes y) (lcong alg (uniq_h c h alg commutes y))
  uniq_h (Const' y) h calg commutes z = Refl
  uniq_h (Prod' c' d') h calg commutes (f' # g') =
    let uc' = uniq_h c' h calg commutes f' 
        ud' = uniq_h d' h calg commutes g' 
    in lcong2 (#) uc' ud'
  uniq_h (Sum' c' d') h calg commutes (Inl f') = lcong Inl (uniq_h c' h calg commutes f')  
  uniq_h (Sum' c' d') h calg commutes (Inr g') = lcong Inr (uniq_h d' h calg commutes g') 
  uniq_h (With' c' d') h calg commutes z = 
    funext _ _ (\x => if x then uniq_h c' h calg commutes (z True)
                           else uniq_h d' h calg commutes (z False))
  0 uniq : {d : Desc} -> 
           (alg : qpf d x -<> x) -> 
           (h : W d -<> x) -> 
           ((1 y : qpf d (W d)) -> h (Con y) = alg (fmap d h y)) -> 
           (w : W d) -> h w = fold d alg w
  uniq alg h commutes (Con y) = 
    trans (commutes y) (lcong alg (uniq_h d h alg commutes y))
    
0 foldCon_id : (1 w : W d) -> w = fold d Con w
foldCon_id w = uniq Con (\x => x) (\y => lcong Con (fmap_id y)) w
       
0 foldCommutes : (d : Desc) -> 
      (alg : qpf d x -<> x) -> 
      (1 w : qpf d (W d)) ->  
      let h = fold d alg 
      in h (Con w) = alg (fmap d h w)
foldCommutes Id' alg (Con x) = Refl
foldCommutes (Const' _) alg x = Refl
foldCommutes (Prod' c d) alg (x # y) = 
  let commutesC = uniq_h c (fold (Prod' c d) alg) alg (foldCommutes (Prod' c d) alg) x
      commutesD = uniq_h d (fold (Prod' c d) alg) alg (foldCommutes (Prod' c d) alg) y
  in lcong alg (lcong2 (#) (sym commutesC) (sym commutesD))

foldCommutes (Sum' c d) alg (Inl x) =
  let commutesC = uniq_h c (fold (Sum' c d) alg) alg (foldCommutes (Sum' c d) alg) x
  in lcong alg (lcong Inl (sym commutesC))
  
foldCommutes (Sum' c d) alg (Inr y) =
  let commutesD = uniq_h d (fold (Sum' c d) alg) alg (foldCommutes (Sum' c d) alg) y
  in lcong alg (lcong Inr (sym commutesD))
  
foldCommutes (With' c d) alg x = 
  lcong alg (funext _ _ 
    (\b => if b then sym (uniq_h c (fold (With' c d) alg) alg (foldCommutes (With' c d) alg) (x True)) 
                else sym (uniq_h d (fold (With' c d) alg) alg (foldCommutes (With' c d) alg) (x False))
     ))
  
namespace TensorInduction
            
  pAlg : {d : Desc} -> {0 p : W d -> Type} ->
         (step : (1 w : Sigma0 (qpf d (W d)) (lift d p)) -> p (Con (fst w))) ->  
         qpf d (Sigma0 (W d) p) -<> Sigma0 (W d) p
  pAlg step x = 
    let z = dist {x = W d} d x 
    in Con (fst z) # step z
    
 
  0 pAlgCommutes : {d : Desc} -> {0 p : W d -> Type} ->
                 {step : (1 w : Sigma0 (qpf d (W d)) (lift d p)) -> p (Con (fst w))} ->
                 (1 w : qpf d (Sigma0 (W d) p)) -> 
                 fst (pAlg {p = p} step w) = Con (fmap {a = Sigma0 (W d) p} {b = W d} d (\x => fst x) w)
  pAlgCommutes {d = Id'}  (x # y) = Refl
  pAlgCommutes {d = (Const' x)}  w = Refl
  pAlgCommutes {d = (Prod' c d)} (x # y) with (dist {x = W (Prod' c d)} c x)
    pAlgCommutes  {d = (Prod' c d)} (x # y) | (f # lf) with (dist {x = W (Prod' c d)} d y) 
       pAlgCommutes  {d = (Prod' c d)} (x # y) | (f # lf) | (g # fg) = 
         ?pAlg_Prod --need inspect and lemma for dist (fst (dist c x) ~ x)
  pAlgCommutes {d = (Sum' x y)} {step = step} w = ?pAlg_Sum
  pAlgCommutes {d = (With' x y)} {step = step} w = ?pAlg_With
  
  
  induction : {d : Desc} -> {0 p : W d -> Type} ->
              (step : (1 w : Sigma0 (qpf d (W d)) (lift d p)) -> p (Con (fst w))) ->
              (1 w : W d) -> p w
  induction step w = ?ind_hole
{-  
    let pw = snd (h w)
    in replace0 {x = fst (h w)} p (eq w) pw where
    
    h : (1 _ : W d) -> Sigma0 (W d) p
    h = fold d (pAlg step)
                      
    0 eq : (w : W d) -> fst (h w) = w
    eq w = let z = uniq Con (\w => fst (fold d (pAlg step) w)) ?a4 w 
           in ?b
-}           
    
  indComp : {d : Desc} -> {0 p : W d -> Type} ->
            (step : (1 w : Sigma0 (qpf d (W d)) (lift d p)) -> p (Con (fst w))) ->
            (1 w : qpf d (W d)) ->
            induction {p = p} step (Con w) = step (w # induction {p = p} step ?A)
    
namespace WithInduction
  
  withAlg : (p : x -> Type) -> 
            (d : Desc) -> 
            (alg : qpf d x -<> x) -> 
            (step : (0 y : qpf d x) -> lift d p y -<> p (alg y)) ->  
            qpf d (DWith x p) -<> DWith x p
  withAlg p d alg step fp = 
    let (x0 #  w) = distW d fp
    in (alg x0) # (\x => if x 
                       then (let (u # ueq) = w True in (alg u) # (lcong (\x => alg x) ueq))                              
                       else step x0 (w False))


  pAlg : {d : Desc} -> {0 p : W d -> Type} ->
         (step : (1 w : DWith (qpf d (W d)) (lift d p)) -> p (Con (fstW {b = lift d p} w))) ->  -- okay, I can just do p (fst x), but that would be cheating wrt. internal representation
         qpf d (DWith (W d) p) -<> DWith (W d) p
  pAlg step x = 
      Con (fstW (distW d x)) # (\b => if b then (Con (fstW (distW d x))) # Refl
                                           else step (distW d x))
