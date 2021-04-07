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

congd2 : {t : Type} -> {s : t -> Type} ->
         (f : (x : t) -> s x -> u) -> {a : t} -> {b : t} -> {a' : s a} -> {b' : s b} ->
          a = b -> a' = b' -> f a a' = f b b'
congd2 f Refl Refl = Refl

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

        
0 DepWith : (0 a : Type) -> (0 _ : a -> Type) -> Type
DepWith a b = Sigma0 a (\x => (1 y : Bool) -> if y then (Sigma1 a (\z => z = x)) else b x)

fmapDepWith : {a, a' : Type} -> {b : a -> Type} -> {b' : a' -> Type} ->
              (f : a -> a') -> (g : (0 x : a) -> b x -> b' (f x)) -> DepWith a b -> DepWith a' b'
fmapDepWith f g (Sig0 x w) = Sig0 (f x) (\1 b => case b of
                                          True => let (Sig1 y Refl) = w True in Sig1 (f y) Refl
                                          False => let y = w False in g x y)
                                          
parameters(funext : {a : Type} -> {b : a -> Type} -> (f, g : (1 x : a) -> b x) -> (0 _ : (x : a) -> f x = g x) -> f = g)

  distW : {0 x : Type} -> {0 y : x -> Type} -> 
          (d : Desc) -> qpf d (DepWith x y) -<> DepWith (qpf d x) (lift d y) 
  distW Id' (Sig0 z w) = Sig0 z (\x => case x of
                                   True => (w True)
                                   False => (w False)) 
  distW (Const' z) w = Sig0 w (\x => case x of 
                                   True => Sig1 w Refl
                                   False => w )
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
  distW (With' c d) w = 
      (k w)  where
      
      0 h : (w : With (qpf c (DepWith x y)) (qpf d (DepWith x y))) -> With (qpf c x) (qpf d x)
      h w True with (distW c (w True))
        h w True | (Sig0 z _)  = z
      h w False with (distW d (w False))
        h w False | (Sig0 z _) = z
      
      0 i : {a , b : Type} -> (0 u : With a b) -> 
            (the (With a b) (\1 b => if b then u True else u False)) = u
      i u = funext _ _ (\x => case x of 
                           True => Refl
                           False => Refl)
      
      j : (1 w : With (qpf c (DepWith x y)) (qpf d (DepWith x y))) ->
          (1 b : Bool) -> 
          if b then Sigma1 (With (qpf c x) (qpf d x)) (\z => z = (h w)) 
               else With (lift c y ((h w) True)) (lift d y ((h w) False))
      j w True = ?a -- Sig1 (h ?a) Refl
      j w False = ?c
      
      k : (1 w : With (qpf c (DepWith x y)) (qpf d (DepWith x y))) ->
           DepWith (With (qpf c x) (qpf d x)) 
                 (\u => With (lift c y (u True)) (lift d y (u False)))
      k w = Sig0 {a = With (qpf c x) (qpf d x)} 
                 {b = (\u => With (lift c y (u True)) (lift d y (u False)))} 
                 (h w) ?second
    
{- namespace A
  parameters(funext : {a : Type} -> {b : a -> Type} -> (f, g : (1 x : a) -> b x) -> (0 _ : (x : a) -> f x = g x) -> f = g)
    data W : (0 d : Desc) -> Type where
      Con : qpf d (W d)  -<> W d

    fmap : (d : Desc) -> (f : a -<> b) -> qpf d a -<> qpf d b
    fmap Id' f = f
    fmap (Const' x) f = \x => x
    fmap (Prod' c d) f = \(Sig1 u v) => Sig1 (fmap c f u) (fmap d f v)
    fmap (Sum' c d) f = fmapSum (fmap c f) (fmap d f)
    fmap (With' c d) f = fmapWith (fmap c f) (fmap d f)
  
   
    fold_h : {c : Desc} -> (d : Desc) -> (qpf c x -<> x) -> qpf d (W c) -<> qpf d x
    fold_h Id' alg (Con w) = alg (fold_h c alg w)
    fold_h (Const' y) alg w = w
    fold_h (Prod' c d) alg (Sig1 f g) = Sig1 (fold_h c alg f) (fold_h d alg g)
    fold_h (Sum' c d) alg w = fmapSum (fold_h c alg) (fold_h d alg) w
    fold_h (With' c d) alg w = fmapWith (fold_h c alg) (fold_h d alg) w
    
    fold : (d : Desc) -> (qpf d x -<> x) -> W d -<> x
    fold d alg (Con w) = alg (fold_h d alg w)

    0 uniq_h : {c : Desc} -> 
             (d : Desc) -> 
             (h : W c -<> x) -> (calg : qpf c x -<> x) ->
             ((y : qpf c (W c)) -> h (Con y) = calg (fmap c h y)) ->
             (z : qpf d (W c)) -> fmap d h z = fold_h {c = c} d calg z
    uniq_h Id' h calg commutes (Con y) = 
      let it = uniq_h c h calg commutes y 
      in trans (commutes y) (cong (\x => calg x) it)
    uniq_h (Const' y) h calg commutes z = Refl
    uniq_h (Prod' c' d') h calg commutes (Sig1 f' g') =
      let uc' = uniq_h c' h calg commutes f' 
          ud' = uniq_h d' h calg commutes g' 
      in cong2l Sig1 uc' ud'
    uniq_h (Sum' c' d') h calg commutes (Inl f') = cong (\x => Inl x) (uniq_h c' h calg commutes f')  
    uniq_h (Sum' c' d') h calg commutes (Inr g') = cong (\x => Inr x) (uniq_h d' h calg commutes g') 
    uniq_h (With' c'  d') h calg commutes z = 
      funext _ _  (\x => case x of
                    True  => uniq_h c' h calg commutes (z True)
                    False => uniq_h d' h calg commutes (z False))
  
    0 uniq : (d : Desc) -> 
             (alg : qpf d x -<> x) -> 
             (h : W d -<> x) -> 
             ((y : qpf d (W d)) -> h (Con y) = alg (fmap d h y)) -> 
             (w : W d) -> h w = fold d alg w
    uniq d alg h commutes (Con y) = 
      trans (commutes y) (cong (\x => alg x) (uniq_h d h alg commutes y))
              
    palg : (p : x -> Type) -> 
           (d : Desc) -> 
           (alg : qpf d x -<> x) -> 
           (step : (0 y : qpf d x) -> lift d p y -<> p (alg y)) ->  
           qpf d (Sigma0 x p) -<> Sigma0 x p
    palg _ d alg step fp = 
      let (Sig0 z zp) = dist d fp 
      in Sig0 (alg z) (step z zp)
  
    pinduction : (p : x -> Type) -> 
                 (d : Desc) -> 
                 (alg : qpf d x-<> x) ->
                 (step : (0 x' : qpf d x) -> lift d p x' -<> p (alg x')) ->
                 (w : W d) -> p (fold d alg w)
    pinduction p d alg step w = 
      let u = proj2 (fold d (palg p d alg step) w)
      in replace0 p (commutes d alg step w) u where 

      v : (d : Desc) -> 
          (alg : qpf d x -<> x) ->
          (step : (0 x' : qpf d x) -> lift d p x' -<> p (alg x')) ->
          (w : qpf d (W d)) -> 
          let the_alg = palg p d alg step in 
           proj0 (fold d the_alg (Con w)) = alg (fmap d (\1 w => proj0 (fold d the_alg w)) w)
      v Id' alg step w = ?a
      v d alg step w = ?b
                  
      0 commutes : (d : Desc) -> 
            (alg : qpf d x -<> x) -> 
            (step : (0 x' : qpf d x) -> lift d p x' -<> p (alg x')) -> 
            (w : W d) -> proj0 (fold d (palg p d alg step) w) = fold d alg w
      commutes d alg step w = uniq d alg (\w => proj0 (fold d (palg p d alg step) w)) (v d alg step) w
    
-}
