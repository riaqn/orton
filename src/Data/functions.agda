----------------------------------------------------------------------
-- This Agda code is designed to accompany the paper
--
-- Ian Orton and Andrew M. Pitts,
-- "Axioms for Modelling Cubical Type Theory in a Topos"
-- (Journal of Logical Methods in Computer Science, Special Issue for CSL 2016) 
--
-- The idea for getting an impredicative universe of propositions Ω
-- comes from Martin Escardo, more details can be found at:
--
--          http://www.cs.bham.ac.uk/~mhe/impredicativity/          
----------------------------------------------------------------------

module Data.functions where

open import prelude
open import impredicative
open import interval
open import cof
open import fibrations
open import Data.products
open import Data.paths

----------------------------------------------------------------------
-- Dependent functions
----------------------------------------------------------------------
Π' : {Γ : Set}(A : Γ → Set)(B : (Σ x ∈ Γ , A x) → Set) → Γ → Set
Π' A B x = (a : A x) → B (x , a)

module FibΠidInternal {A : Int → Set}
                      {B : (Σ x ∈ Int , A x) → Set}
                      (α : isFib A)
                      (β : isFib B)
                      (p : Int → Int) where
 module Construct (φ : Cof) (f : [ φ ] → Π ((Π' A B) ∘ p)) (e₀ e₁ : Int)
                  (h₀ : ⟦ g₀ ∈ (Π' A B) (p e₀) ∣ (φ , f) ∙ e₀ ↗ g₀ ⟧) where
  g₀ = fst h₀
  f↗g₀ = snd h₀

  module _ (a : A (p e₁)) where
   Σpa = fill {A = A} α p cofFalse ∅-elim e₁ (a , (λ u → ∅-elim u))

   pa : Π (A ∘ p)
   pa = fst Σpa
 
   pa≡a : pa e₁ ≡ a
   pa≡a = snd (snd Σpa)

   q : Int → Σ Int A
   q i = (p i , pa i)

   f' : [ φ ] → Π (B ∘ q)
   f' u i = f u i (pa i)

   b₀ : B (q e₀)
   b₀ = g₀ (pa e₀)

   f'↗b₀ : prf ((φ , f') ∙ e₀ ↗ b₀)
   f'↗b₀ u = cong (λ f → f (pa e₀)) (f↗g₀ u)

   Σb₀ : ⟦ b₀ ∈ B (q e₀) ∣ (φ , f') ∙ e₀ ↗ b₀ ⟧
   Σb₀ = (b₀ , f'↗b₀)

   g₁ : B ( p e₁ , a)
   g₁ = let b = fst (fst (β q) φ f' e₀ e₁ Σb₀) in subst (λ a → B (p e₁ , a)) pa≡a b 

  extends : prf ((φ , f) ∙ e₁ ↗ g₁)
  extends u = funext (λ a → substLemma (pa≡a a) (trans (f'I≡g₁ a) (fI≡f'I a))) where
   substLemma : {a a' : A (p e₁)}(eq : a' ≡ a){b : B (p e₁ , a)}{b' : B (p e₁ , a')}
     → subst (λ a → B (p e₁ , a)) (symm eq) b ≡ b' → b ≡ subst (λ a → B (p e₁ , a)) eq b'
   substLemma refl refl = refl
   f'I≡g₁ : (a : A (p e₁)) → f' a u e₁ ≡ fst (fst (β (q a)) φ (f' a) e₀ e₁ (Σb₀ a))
   f'I≡g₁ a = snd (fst (β (q a)) φ (f' a) e₀ e₁ (Σb₀ a)) u
   fI≡f'I : (a : A (p e₁)) → subst (λ a₁ → B (p e₁ , a₁)) (symm (pa≡a a)) (snd ((φ , f) ∙ e₁) u a) ≡ f' a u e₁
   fI≡f'I a = congdep (λ a' → f u e₁ a') (symm (pa≡a a))

  h₁ : ⟦ g₁ ∈ (Π' A B) (p e₁) ∣ (φ , f) ∙ e₁ ↗ g₁ ⟧ 
  h₁ = (g₁ , extends)
 module Reduce (φ : Cof) (f : [ φ ] → Π ((Π' A B) ∘ p)) (e : Int)
               (h₀ : ⟦ g ∈ (Π' A B) (p e) ∣ (φ , f ) ∙ e ↗ g ⟧) where
  module c = Construct φ f e e h₀

  g₀ = fst h₀
  f↗g₀ = snd h₀

  g₁≡g₀ : c.g₁ ≡ c.g₀
  g₁≡g₀ = funext (λ a → let pa₁ = c.pa a e
                            g₀_pa = g₀ pa₁
                            g₀_pa' = subst (λ a → B (p e , a)) (c.pa≡a a) g₀_pa
                            g₀_pa'≡g₀_a = congdep g₀ (c.pa≡a a)
                            g₁'≡g₀ = cong fst (snd (β (c.q a)) φ (c.f' a) e (c.Σb₀ a))
                            g₁≡g₀_pa' = cong (subst (λ a → B (p e , a)) (c.pa≡a a)) g₁'≡g₀
                         in trans g₀_pa'≡g₀_a g₁≡g₀_pa')
                        --subst ((λ b → subst (λ a → B (p e , a)) (c.pa≡a a) b ≡ g₀ a )) {!symm (g₁'≡g₀)!} g₀_pa'≡g₀_a)

  h₁≡h₀ : c.h₁ ≡ h₀
  h₁≡h₀ = Σext g₁≡g₀ (funext (λ x → uipImp))

FibΠid :
 {A : Int → Set}
 {B : (Σ x ∈ Int , A x) → Set}
 (α : isFib A)
 (β : isFib B)
 → isFib (Π' A B)
FibΠid {A} {B} α β p = (fibΠidInternal.Construct.h₁ , fibΠidInternal.Reduce.h₁≡h₀) where
                module fibΠidInternal = FibΠidInternal {A} {B} α β p

FibΠ :
  {Γ : Set}
  {A : Γ → Set}
  {B : (Σ x ∈ Γ , A x) → Set}
  (α : isFib A)
  (β : isFib B)
  → -----------
  isFib (Π' A B)
(FibΠ {Γ} {A} {B} α β p) = (FibΠid (reindex A α p) (reindex B β (p ×id)) id)

Πext : {Γ : Set}{A : Γ → Set}{B : (Σ x ∈ Γ , A x) → Set}{x : Γ}{f g : Π' A B x} → ((a : A x) → f a ~ g a) → f ~ g
fst (Πext pointwise) i a = fst (pointwise a) i
fst (snd (Πext pointwise)) = funext (λ a → fst (snd (pointwise a)))
snd (snd (Πext pointwise)) = funext (λ a → snd (snd (pointwise a)))
  
----------------------------------------------------------------------
-- Forming Π-types is stable under reindexing
----------------------------------------------------------------------
reindexΠ :
  {Δ Γ : Set}
  (A : Γ → Set)
  (B : Σ Γ A → Set)
  (α : isFib A)
  (β : isFib B)
  (ρ : Δ → Γ)
  → ----------------------
  reindex (Π' A B) (FibΠ {B = B} α β) ρ ≡ FibΠ {B = B ∘ (ρ ×id)} (reindex A α ρ) (reindex B β (ρ ×id))
reindexΠ A B α β ρ = refl
