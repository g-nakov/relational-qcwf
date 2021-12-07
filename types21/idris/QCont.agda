module QCont where

open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality
open import Axiom.UniquenessOfIdentityProofs.WithK


postulate
  funext : ∀{X : Set} {Y : X → Set} {f g : (s : X) → Y s} → (∀ x → f x ≡ g x) → f ≡ g

module _ (S : Set) (P : S → Set)  where

  ⟦F_⟧ : Set → Set
  ⟦F X ⟧ =  Σ S λ s → P s → X

  _<$>_ : ∀{X Y} → (f : X → Y) → ⟦F X ⟧ → ⟦F Y ⟧
  f <$> (s , h)  = s , λ x → f (h x)

  infix 5 _<$>_
  
  alg : Set → Set
  
  alg X = ⟦F X ⟧ → X
  
  data W : Set where
    Con : ⟦F W ⟧ → W

  record F-homomorphism {X Y : Set} (α : alg X) (β : alg Y) : Set where
    eta-equality
    constructor _,_
    field
      fun : X → Y
      commutes : (x : ⟦F X ⟧) → fun (α x) ≡ β (fun <$> x)

  syntax F-homomorphism a b = a -F⟶ b

  open F-homomorphism

  _≡ₚₜ_ : ∀{X Y} {α : alg X}{β : alg Y} → (h g : α -F⟶ β) → Set
  _≡ₚₜ_ {X} h g = (x : X) → fun h x ≡ fun g x 
    

  [_]=f : ∀{X Y} {α : alg X}{β : alg Y}{h g : α -F⟶ β} →
           (p : h ≡ g) → (fun h ≡ fun g)
  [ p ]=f = cong fun p


  _∘F_ : ∀{X Y Z}{α : alg X}{β : alg Y}{γ : alg Z} →
         (β -F⟶ γ) → (α -F⟶ β) → (α -F⟶ γ)
  fun (h ∘F g) = fun h ∘ fun g
  commutes (h ∘F g) x rewrite commutes g x = commutes h _
 
  idₕ :  ∀{X} (α : alg X) → α -F⟶ α
  idₕ α =  id , λ c → refl
   
  foldₕ : ∀{X} (α : alg X) → Con -F⟶ α
  fun (foldₕ α) (Con (s , h)) = α (s , fun (foldₕ α) ∘ h)
  commutes (foldₕ α) w = refl

  uniq-f : ∀{X}{α : alg X} → (g : Con -F⟶ α) → g ≡ₚₜ foldₕ α
  uniq-f {α = α} (g , commutes) (Con (s , h)) =
    trans (commutes (s , h)) (cong (λ h → α (s , h)) (funext (pointwise h)))
   where
     pointwise : ∀{s : S} (h : P s → W) → (x : P s) → g (h x) ≡ fun (foldₕ α) (h x)
     pointwise h p = uniq-f (g , commutes) (h p)  

  uniqueness : ∀{X}{α : alg X} → (g : Con -F⟶ α) → g ≡ foldₕ α
  uniqueness {α = α} (g , commutes) with funext (uniq-f {α = α} (g , commutes))
  ...| refl =  cong (λ x → fun (foldₕ α) , x) (funext λ x → uip _ _ )


  idₕW=foldₕW : idₕ Con ≡ foldₕ Con
  idₕW=foldₕW = uniqueness (idₕ Con)

  
  module _ (Q : W → Set) where

    motive : Set
    motive = (s : S) → (h : P s → W) → ((p : P s) → Q (h p)) → Q (Con (s , h))

    ind-alg : motive → alg (Σ W Q)
    ind-alg m (s , h) = (Con (proj₁ <$> (s , h))) , m s _ (λ p → proj₂ (h p))

    proj₁-ind-algₕ : motive → Con -F⟶ Con
    fun (proj₁-ind-algₕ m) = proj₁ ∘ fun (foldₕ (ind-alg m))
    commutes (proj₁-ind-algₕ m) x = refl

    id=ₕproj₁-ind-alg : (m : motive) → idₕ Con ≡ proj₁-ind-algₕ m
    id=ₕproj₁-ind-alg m = trans idₕW=foldₕW (sym (uniqueness (proj₁-ind-algₕ m)))

    id=ₚₜproj₁-ind-alg : (m : motive) → (idₕ Con) ≡ₚₜ (proj₁-ind-algₕ m)
    id=ₚₜproj₁-ind-alg m w = cong-app [ id=ₕproj₁-ind-alg m ]=f w

    induction : motive → (w : W) → Q w
    induction m w =
      subst Q (sym (id=ₚₜproj₁-ind-alg m w)) (proj₂ (fun (foldₕ (ind-alg m)) w))

  open ≡-Reasoning
    
  ind-comp : (Q : W → Set) → (m : motive Q) →
             (s : S) → (h : P s → W) →
             induction Q m (Con (s , h)) ≡ m s h (λ p → induction Q m (h p))
  ind-comp Q m s h =
    let snd-fold = proj₂ ∘ fun (foldₕ (ind-alg Q m))
        fst-fold = proj₁ ∘ fun (foldₕ (ind-alg Q m))
        eq =  [ id=ₕproj₁-ind-alg Q m ]=f
        w = Con (s , h)
    in begin
        induction Q m (Con (s , h))
          ≡⟨ (cong (λ x → subst Q (sym x) (snd-fold w)) ({!uip (funext _) _!} {- uip _ _ -}) ) ⟩
        subst Q (sym (cong (λ g → Con (s , (λ z → g (h z)))) eq)) 
          (m s (λ z → fst-fold (h z)) (λ p → snd-fold (h p)))
          ≡⟨ fixQ eq snd-fold ⟩
        m s h (λ p → induction Q m (h p))
       ∎
    where
      fixQ : {g : W → W} → (eq : (λ x → x) ≡ g) → (exp : (w : W) → Q (g w)) →
             subst Q (sym (cong (λ g → Con (s , λ z → g (h z))) eq))
                     (m s (λ z → g (h z)) (λ p → exp (h p)))
             ≡ m s h λ p → subst Q (sym (cong-app eq (h p))) (exp (h p))
      fixQ refl v = refl

        
  initiality : ∀{X} → (α : alg X) → (Con -F⟶ α)
  fun (initiality {X} α) = induction (λ _ → X) λ s _ ih → α (s , ih)
  commutes (initiality {X} α) (s , h) = ind-comp _ (λ s _ ih → α (s , ih)) s h
    
  uniq-morphism-f : ∀{X} →  (α : alg X) → (f : Con -F⟶ α) →
                    fun f ≡ fun (initiality α) 
  uniq-morphism-f α (f , commutes) = funext (induction (λ z → f z ≡ fun (initiality α) z) m)
   where
    m :  (s : S) (h : P s → W) → ((p : P s) → f (h p) ≡ fun (initiality α) (h p))
         → f (Con (s , h)) ≡ fun (initiality α) (Con (s , h))
    m s h ih = begin
        f (Con (s , h))
          ≡⟨ commutes (s , h) ⟩ 
        α (s , f ∘ h )
          ≡⟨ cong (λ u → α (s , u)) (funext ih)  ⟩
        α (s , (λ p → fun (initiality α) (h p)))
          ≡⟨ sym (ind-comp _ (λ s _ h → α (s , h)) s h) ⟩
        fun (initiality α) (Con (s , h)) ∎

  uniq-morphismₕ : ∀{X} →  (α : alg X) → (f : Con -F⟶ α) →  f ≡ initiality α 
  uniq-morphismₕ α f with uniq-morphism-f α f
  ...| refl = cong (λ commutes → fun f , commutes) (funext λ _ → uip _ _ )
