module QCont

data Sigma1 : (a : Type) -> (b : a -> Type) -> Type where
  Sig1 : (1 x : a) -> (1 y : b x) -> Sigma1 a b

data Sigma0 : (a : Type) -> (b : a -> Type) -> Type where
  Sig0 : (0 x : a) -> (1 y : b x) -> Sigma0 a b

0 proj0 : Sigma0 a b -> a
proj0 (Sig0 x y) = x 

proj2 : (1 x : Sigma0 a b) -> b (proj0 x)
proj2 (Sig0 x y) = y

(-<>) : Type -> Type -> Type
(-<>) a b = (1 x : a) -> b

infixr 0 -<>

extractSingleton : {0 a : Type} -> {0 x : a} -> Sigma1 a (\ z => z = x) -<> a
extractSingleton (Sig1 x Refl) = x

0 extractSingletonExtractsSingleton : {0 a : Type} -> {0 x : a} -> (0 y : Sigma1 a (\ z => z = x)) ->
                                    extractSingleton y = x
extractSingletonExtractsSingleton (Sig1 x Refl) = Refl


data Sum : (a : Type) -> (b : Type) -> Type where
  Inl : (1 x : a) -> Sum a b
  Inr : (1 y : b) -> Sum a b
  
fmapSum :  (a -<> a') -> (b -<> b') -> Sum a b -<> Sum a' b'
fmapSum f g (Inl x) = Inl $ f x
fmapSum f g (Inr y) = Inr $ g y

0 With : Type -> Type -> Type
With a b = (1 x : Bool) -> if x then a else b

fmapWith : (a -<> a') -> (b -<> b') -> With a b -<> With a' b'
fmapWith f g x True  = f (x True)
fmapWith f g x False = g (x False)

replace0 : (p : a -> Type) -> (0 _ : x = y) -> p x -<> p y
replace0 p Refl r = r

promoteEq : (0 _ : x = y) -> x = y
promoteEq Refl = Refl

cong2d : {t : Type} -> {s : t -> Type} ->
         (f : (x : t) -> s x -> u) -> {a : t} -> {b : t} -> {a' : s a} -> {b' : s b} ->
          a = b -> a' = b' -> f a a' = f b b'
cong2d f Refl Refl = Refl

congl : (f : (1 x : t) -> u) ->
          (1 p : a = b) -> f a = f b 
congl f Refl = Refl

cong2l : (f : (1 x : t) -> (1 y : s) -> u) ->
          a = b -> a' = b' -> f a a' = f b b'
cong2l f Refl Refl = Refl

{- parameters (a : Type, b : a -> Type, funext : {a : Type} -> {b : a -> Type} -> (f, g : (1 x : a) -> b x) -> (0 _ : (x : a) -> f x = g x) -> f = g)

  F : Type -> Type
  F x = Sigma1 a (\ z => b z -<> x)
  
  Fmap : (f : x -<> y) -> (F x -<> F y)
  Fmap f (Sig1 a h) = Sig1 a (\ z => f (h z))

  data W : Type where
    Con : F W -<> W

  fold : (F x -<> x) -> W -<> x -- uses alg twice
  fold alg (Con (Sig1 a h)) = alg (Sig1 a \z => fold alg (h z))

  uniqueness : (alg : F x -<> x) -> (h : W -<> x) -> ((y : F W) -> h (Con y) = alg (Fmap h y)) -> (x : W) -> h x = fold alg x
  uniqueness alg h commutes (Con (Sig1 x g)) =
    trans (commutes (Sig1 x g))
          (cong (\ z => alg (Sig1 x z)) (funext _ _ pointwise))
    where
      pointwise : (y : b x) -> h (g y) = fold alg (g y)
      pointwise y = uniqueness alg h commutes (g y)

{-
  induction' : (p : W -> Type) ->
               (step : (1 z : a) -> (0 h : b z -<> W) -> (1 ih : (1 y : b z) -> p (h y)) -> p (Con (Sig1 z h))) ->
               (1 x : W) -> p x -- uses step twice
  induction' p step (Con (Sig1 z h)) = step z h (\ y => induction' p step (h y))
-}


  indAlg : (p : W -> Type) -> let W' = Sigma0 W p in
           (1 step : (1 z : a) -> (0 h : b z -<> W) -> (1 ih : (1 y : b z) -> p (h y)) -> p (Con (Sig1 z h))) ->
           F W' -<> W'
  indAlg p step (Sig1 z h) = Sig0 (Con (Sig1 z (\ y => proj0 (h y)))) (step z _ (\ y => proj2 (h y)))

  induction : (p : W -> Type) ->
               (step : (1 z : a) -> (0 h : b z -<> W) -> (1 ih : (1 y : b z) -> p (h y)) -> p (Con (Sig1 z h))) ->
               (1 x : W) -> p x
  induction p step x = replace0 p (sym (eq x)) (foldIt x) where
    foldIt : (1 x : W) -> p (proj0 (fold (indAlg p step) x)) -- uses step twice
    foldIt x = proj2 (fold (indAlg p step) x)
    0 eq : (0 x : W) -> x = proj0 (fold (indAlg p step) x)
    eq (Con (Sig1 x h)) = cong (\ z => Con (Sig1 x z)) (funext h _ ih)
      where
        0 ih : (y : b x) -> h y = proj0 (fold (indAlg p step) (h y))
        ih y = eq (h y)
-}

data Desc : Type where
  Id' : Desc
  Const' : Type -> Desc
  Prod' : Desc -> Desc -> Desc
  Sum' : Desc -> Desc -> Desc
  With' : Desc -> Desc -> Desc

0 qpf : Desc -> Type -> Type
qpf Id' x = x
qpf (Const' x) _  =  x
qpf (Prod' f g) x = Sigma1 (qpf f x) (\_ => qpf g x)
qpf (Sum' f g) x = Sum (qpf f x) (qpf g x)
qpf (With' f g) x = With (qpf f x) (qpf g x)

0 lift : (d : Desc) -> (p : x -> Type) -> qpf d x -> Type
lift Id' p f = p f
lift (Const' x) p f = x
lift (Prod' c d) p (Sig1 f g) = Sigma1 (lift c p f) (\_ => lift d p g)
lift (Sum' c d) p (Inl f) = lift c p f
lift (Sum' c d) p (Inr g) = lift d p g
lift (With' c d) p f = With (lift c p (f True)) (lift d p (f False))



0 DepWith : (a : Type) -> (b : a -> Type) -> Type
DepWith a b = Sigma0 a (\x => With (Sigma1 a (\z => z = x)) (b x)) -- (1 y : Bool) -> if y then (Sigma1 a (\z => z = x)) else b x)

{-
fmapDepWith : {a, a' : Type} -> {b : a -> Type} -> {b' : a' -> Type} ->
              (f : a -> a') -> (g : (0 x : a) -> b x -> b' (f x)) -> DepWith a b -> DepWith a' b'
fmapDepWith f g (Sig0 x w) = Sig0 (f x) (\1 b => case b of
                                          True => let (Sig1 y Refl) = w True in Sig1 (f y) Refl
                                          False => let y = w False in g x y)
-}

parameters(funext : (a : Type) -> (b : a -> Type) -> (f, g : (1 x : a) -> b x) -> (0 _ : (x : a) -> f x = g x) -> f = g)

  dist : {0 x : Type} -> {0 y : x -> Type} -> 
         (d : Desc) -> qpf d (Sigma0 x y) -<> Sigma0 (qpf d x) (lift d y)
  dist Id' (Sig0 x y) = Sig0 x y
  dist (Const' x) f = Sig0 f f
  dist (Prod' c d) (Sig1 f g) = 
    let (Sig0 f lf) = dist c f
        (Sig0 g lg) = dist d g
    in Sig0 (Sig1 f g) (Sig1 lf lg)
  dist (Sum' c d) (Inl f) = 
    let (Sig0 f lf) = dist c f
    in  Sig0 (Inl f) lf
  dist (Sum' c d) (Inr g) =
    let (Sig0 g lg) = dist d g
    in Sig0 (Inr g) lg
  dist (With' c d) w = 
     Sig0 (h w) (j w) where
      0 h : With (qpf c (Sigma0 x y)) (qpf d (Sigma0 x y)) -> With (qpf c x) (qpf d x) 
      h u True  = proj0 (dist c (u True))
      h u False = proj0 (dist d (u False))
      
      j : (1 u : With (qpf c (Sigma0 x y)) (qpf d (Sigma0 x y))) -> 
          With (lift c y (h u True)) (lift d y (h u False))
      j u True  = proj2 (dist c (u True))
      j u False = proj2 (dist d (u False))

  
  distW : {0 x : Type} -> {0 y : x -> Type} -> 
          (d : Desc) -> qpf d (DepWith x y) -<> DepWith (qpf d x) (lift d y) 
  distW Id' (Sig0 z w) = Sig0 z (\x => if x then (w True) else (w False)) 
  distW (Const' z) w = Sig0 w (\x => if x then Sig1 w Refl else w)
  distW (Prod' c d) (Sig1 f g) =
    let (Sig0 f lf) = distW c f
        (Sig0 g lg) = distW d g
    in Sig0 (Sig1 f g) (\x => case x of
                              True => let (Sig1 u Refl) = lf True
                                          (Sig1 v Refl) = lg True
                                      in Sig1 (Sig1 u v) Refl
                              False => let u = lf False
                                           v = lg False
                                       in Sig1 u v)

  distW (Sum' c d) (Inl f) =
    let (Sig0 x lf) = distW c f
    in Sig0 (Inl x) (\b => case b of
                           True => let (Sig1 u Refl) = lf True in Sig1 (Inl u) Refl
                           False => let u = lf False in u)
  distW (Sum' c d) (Inr g) =
    let (Sig0 x lg) = distW d g
    in Sig0 (Inr x) (\b => case b of
                           True => let (Sig1 u Refl) = lg True in Sig1 (Inr u) Refl
                           False => let u = lg False in u)
                           
  distW (With' c d) w = Sig0 (h w) (j w)
  where
    0 h : With (qpf c (DepWith x y)) (qpf d (DepWith x y)) -<> With (qpf c x) (qpf d x)
    h w True = proj0 (distW c (w True))
    h w False = proj0 (distW d (w False))

    h1 : With (qpf c (DepWith x y)) (qpf d (DepWith x y)) -<> With (qpf c x) (qpf d x)
    h1 w True  = extractSingleton (proj2 (distW c (w True))  True)
    h1 w False = extractSingleton (proj2 (distW d (w False)) True)

    0 eq : (w : With (qpf c (DepWith x y)) (qpf d (DepWith x y))) -> h1 w = h w
    eq w = funext _ _ (h1 w) (h w)
                  (\ b => if b then extractSingletonExtractsSingleton (proj2 (distW c (w True)) True)
                               else extractSingletonExtractsSingleton (proj2 (distW d (w False)) True))

    j : (1 w : With (qpf c (DepWith x y)) (qpf d (DepWith x y))) ->
        With (Sigma1 (With (qpf c x) (qpf d x)) (\z => z = h w)) (lift (With' c d) y (h w))
    j w True = Sig1 (h1 w) (promoteEq (eq w))
    j w False = \ b => if b then proj2 (distW c (w True)) False else proj2 (distW d (w False)) False

  data W : (0 u : Desc) -> Type where
    Con : qpf u (W u)  -<> W u

  fmap : (d : Desc) -> (f : a -<> b) -> qpf d a -<> qpf d b
  fmap Id' f = f
  fmap (Const' x) f = \x => x
  fmap (Prod' c d) f = \(Sig1 u v) => Sig1 (fmap c f u) (fmap d f v)
  fmap (Sum' c d) f = fmapSum (fmap c f) (fmap d f)
  fmap (With' c d) f = fmapWith (fmap c f) (fmap d f)
  
  mutual
    fold_h : {c : Desc} -> (d : Desc) -> (qpf c x -<> x) -> qpf d (W c) -<> qpf d x
    fold_h Id' alg w = fold c alg w
    fold_h (Const' y) alg w = w
    fold_h (Prod' c d) alg (Sig1 f g) = Sig1 (fold_h c alg f) (fold_h d alg g)
    fold_h (Sum' c d) alg w = fmapSum (fold_h c alg) (fold_h d alg) w
    fold_h (With' c d) alg w = fmapWith (fold_h c alg) (fold_h d alg) w
  
    fold : (d : Desc) -> (qpf d x -<> x) -> W d -<> x
    fold d alg (Con w) = alg (fold_h d alg w)
    
    
  mutual
    0 uniq_h : {c : Desc} -> 
           (d : Desc) -> 
           (h : W c -<> x) -> (calg : qpf c x -<> x) ->
           ((y : qpf c (W c)) -> h (Con y) = calg (fmap c h y)) ->
           (z : qpf d (W c)) -> fmap d h z = fold_h {c = c} d calg z
    uniq_h Id' h calg commutes y = uniq calg h commutes y
    uniq_h (Const' y) h calg commutes z = Refl
    uniq_h (Prod' c' d') h calg commutes (Sig1 f' g') =
      let uc' = uniq_h c' h calg commutes f' 
          ud' = uniq_h d' h calg commutes g' 
      in cong2l Sig1 uc' ud'
    uniq_h (Sum' c' d') h calg commutes (Inl f') = cong (\x => Inl x) (uniq_h c' h calg commutes f')  
    uniq_h (Sum' c' d') h calg commutes (Inr g') = cong (\x => Inr x) (uniq_h d' h calg commutes g') 
    uniq_h (With' c'  d') h calg commutes z = 
      funext _ _ _ _  (\x => if x then
                           uniq_h c' h calg commutes (z True)
                         else uniq_h d' h calg commutes (z False))
  
    0 uniq : {d : Desc} -> 
             (alg : qpf d x -<> x) -> 
             (h : W d -<> x) -> 
             ((y : qpf d (W d)) -> h (Con y) = alg (fmap d h y)) -> 
             (w : W d) -> h w = fold d alg w
    uniq alg h commutes (Con y) = 
      trans (commutes y) (cong (\x => alg x) (uniq_h d h alg commutes y))
              
  palg : (p : x -> Type) -> 
         (d : Desc) -> 
         (alg : qpf d x -<> x) -> 
         (step : (0 y : qpf d x) -> lift d p y -<> p (alg y)) ->  
         qpf d (Sigma0 x p) -<> Sigma0 x p
  palg p d alg step fp = 
    let (Sig0 z zp) = dist d fp
    in Sig0 (alg z) (step z zp)
    
  with_alg : (p : x -> Type) -> 
         (d : Desc) -> 
         (alg : qpf d x -<> x) -> 
         (step : (0 y : qpf d x) -> lift d p y -<> p (alg y)) ->  
         qpf d (DepWith x p) -<> DepWith x p
  with_alg p d alg step fp = 
    let (Sig0 x0 w) = distW d fp
    in Sig0 (alg x0) (\x => if x then 
                              (let (Sig1 u ueq) = w True in Sig1 (alg u) (congl (\x => alg x) ueq))                           else let u = w False in (step x0 u))
  
  pinduction : (p : x -> Type) -> 
               (d : Desc) -> 
               (alg : qpf d x-<> x) ->
               (step : (0 x' : qpf d x) -> lift d p x' -<> p (alg x')) ->
               (w : W d) -> p (fold d alg w)
  pinduction p d alg step w = 
    let h = \1 z => fold d (palg p d alg step) z
    -- you would expect that should work...wrong :|
    -- in replace0 p (uniq alg (\y => proj0 (h y)) (v p d alg step) w) (proj2 (h w)) where  
    in replace0 p (uniq alg (\y => proj0 (fold d (palg p d alg step) y)) (v p d alg step) w) (proj2 (fold d (palg p d alg step) w)) where

  conv_pinduction : (p : x -> Type)

     v :  (p : x -> Type) -> 
          (d : Desc) -> 
          (alg : qpf d x-<> x) ->
          (step : (0 x' : qpf d x) -> lift d p x' -<> p (alg x')) ->
          (y : qpf d (W d)) -> 
          let h = fold d (palg p d alg step) in
            proj0 (h (Con y)) = alg (fmap d (\1 y => proj0 (h y)) y)
     v p Id' alg step y = 
       let (Sig0 z zp) = (dist Id' (fold Id' (palg p Id' alg step) y)) in ?b where
       
        v' :  (z : x) -> (zp : p z) ->
             proj0 (the (Sigma0 x p) (Sig0 (alg z) (step z zp))) = alg (proj0 (fold Id' (palg p Id' alg step) y))
        v' k = ?c
       
     -- what about (hint : Can't solve constraint between: x and qpf d x)
     -- v p Id' alg step y with (dist Id' (fold Id' (palg p Id' alg step) y)) 
     --  v p Id' alg step y | zz = ?a
     
     v p d alg step y = ?az
     
{-
fmap (Prod' c d) (\1 y => proj0 (fold (palg p (Prod' c d) alg step) y)) (Sig1 wc wd))
Sig1 (fmap c wc) (fmap d wd)


-}

(fold Id' (pAlg step) w)
