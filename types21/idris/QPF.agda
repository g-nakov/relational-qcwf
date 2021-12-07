module QPF where

open import Data.Bool
open import Data.Product
open import Data.Sum

With : Set → Set →  Set
With A B = (b : Bool) → if b then A else B 

data Code : Set where
  Id : Code
  Const : Code
  _⊗_ : Code → Code → Code
  _⊕_ : Code → Code → Code
  _&_ : Code → Code → Code

⟦_⟧F : Code → Set → Set
⟦ Id ⟧F X = X
⟦ Const ⟧F A = A
⟦ f ⊗ g ⟧F X = ⟦ f ⟧F X × ⟦ g ⟧F X
⟦ f ⊕ g ⟧F X = ⟦ f ⟧F X ⊎ ⟦ g ⟧F X
⟦ f & g ⟧F X = With (⟦ f ⟧F X) (⟦ g ⟧F X)


alg : Code → Set → Set
alg c X = ⟦ c ⟧F X → X 

_↑_ : ∀{X} (c : Code) → (Q : X → Set) →  ⟦ c ⟧F X → Set
(Id ↑ Q) F = Q F
_↑_ {X} Const Q F = X
((f ⊗ g) ↑ Q) (F , G) = (f ↑ Q) F × (g ↑ Q) G
((f ⊕ g) ↑ Q) (inj₁ F) = (f ↑ Q) F
((f ⊕ g) ↑ Q) (inj₂ G) = (g ↑ Q) G
((f & g) ↑ Q) F = With ((f ↑ Q) (F true)) ((g ↑ Q) (F false))


dist : ∀{X}{Q : X → Set} → (c : Code) → ⟦ c ⟧F (Σ X Q) → Σ (⟦ c ⟧F X) ( c ↑ Q)
dist Id F = F
dist Const (x , _) = x , x
dist (f ⊗ g) (F , G) with (F' , qF') ← (dist f F) | (G' , qG') ← (dist g G) =
  (F' , G') , (qF' , qG')
dist (f ⊕ g) (inj₁ F) with (F' , qF') ← dist f F = inj₁ F' , qF'
dist (f ⊕ g) (inj₂ G) with (G' , qG') ← dist g G = inj₂ G' , qG'
dist (f & g) F with  (F' , qF') ← dist f (F true) | (G' , qG') ← dist g (F false) =
  (λ{ false → G' ; true → F' }) , λ{ false → qG' ; true → qF'}


data W (c : Code): Set where
  Con : ⟦ c ⟧F (W c) → W c



fold : ∀{X}{c : Code} → alg c X → W c → X
fold {c = Id} α (Con w) = {!!}
fold {c = Const} α (Con w) = {!!}
fold {c = c ⊗ c₁} α (Con x) = {!!}
fold {c = c ⊕ c₁} α (Con x) = {!!}
fold {c = c & c₁} α (Con x) = {!!}
