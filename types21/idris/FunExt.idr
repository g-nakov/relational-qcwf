module FunExt

public export
funext : {a : Type} -> {b : a -> Type} -> 
         {f, g : (1 x : a) -> b x} -> (0 _ : (1 x : a) -> f x = g x) -> f = g
funext _  = believe_me ()

public export
funextW : {a : Type} -> {b : a -> Type} -> 
          {f, g : (x : a) -> b x} -> (0 _ : (x : a) -> f x = g x) -> f = g
funextW _  = believe_me ()
