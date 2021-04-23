module FunExt

public export
funext : {a : Type} -> {b : a -> Type} -> (f, g : (1 x : a) -> b x) -> (0 _ : (x : a) -> f x = g x) -> f = g
funext _ _ _ = believe_me ()

