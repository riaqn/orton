
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

{-# OPTIONS --rewriting #-}
module Data.products where 

open import prelude
open import impredicative
open import interval
open import cof
open import fibrations
  
----------------------------------------------------------------------
-- Dependent products
----------------------------------------------------------------------
Σ' : ∀{a}{Γ : Set a}(A : Γ → Set)(B : (Σ x ∈ Γ , A x) → Set) → Γ → Set
Σ' A B x = Σ a ∈ A x , B (x , a)

abstract
 module FibΣidInternal {A : Int → Set} 
                       {B : (Σ x ∈ Int , A x) → Set} 
                       (α : isFib A)
                       (β : isFib B)
                       (p : Int → Int) where
  transLift :
   {i : Int}
   {Bi : A (p i) → Set}
   {x y z : A (p i)}
   (p : x ≡ y)
   (q : x ≡ z)
   (r : y ≡ z)
   {bx : Bi x}
   {by : Bi y}
   (s : subst Bi p bx ≡ by)
   → ---------
   subst Bi q bx ≡ subst Bi r by
  transLift refl refl refl refl = refl


  module Construct (φ : Cof)
                   (f : [ φ ] → Π ((Σ' A B) ∘ p))
                   (e₀ e₁ : Int)
                   (h₀ : ⟦ x₀ ∈ (Σ' A B) (p e₀) ∣ (φ , f) ∙ e₀ ↗ x₀ ⟧) where
    a₀ = fst (fst h₀)
    b₀ = snd (fst h₀)
    f↗ab₀ = snd h₀

    fa : [ φ ] → Π (A ∘ p)
    fa u i = fst (f u i)

    fa↗a₀ : prf ((φ , fa) ∙ e₀ ↗ a₀)
    fa↗a₀ u = cong fst (f↗ab₀ u)

    Σa₁ = fst (α p) φ fa e₀ e₁ (a₀ , fa↗a₀)

    a₁ : (A ∘ p) e₁
    a₁ = fst Σa₁

    fa↗a₁ : prf ((φ , fa) ∙ e₁ ↗ a₁)
    fa↗a₁ = snd Σa₁

    Σfa' = fill {A = A} α p φ fa e₀ (a₀ , fa↗a₀)

    fa' : Π (A ∘ p)
    fa' = fst Σfa'

    fa↗fa' : prf( (φ , fa) ↗ fa')
    fa↗fa' = fst (snd Σfa')

    fa'≈a₀ : prf (fa' e₀ ≈ a₀)
    fa'≈a₀ = snd (snd Σfa')

    q : Int → (Σ x ∈ Int , A x)
    q i = (p i , fa' i)

    fb' : [ φ ] → Π (B ∘ q)
    fb' u i = subst (λ a → B (p i , a)) (appCongDep (fa↗fa' u)) (snd (f u i))

    b₀' : B (p e₀ , fa' e₀)
    b₀' = subst (λ a → B (p e₀ , a)) (symm fa'≈a₀) b₀


    fb'↗b₀' : prf ((φ , fb') ∙ e₀ ↗ b₀')
    fb'↗b₀' u = transLift fa₀≡a₀ fa₀≡fa'₀ a₀≡fa'₀ s where
                 fa₀≡a₀ : (fa u e₀) ≡ a₀
                 fa₀≡a₀ = Σeq₁ (snd h₀ u)

                 a₀≡fa'₀ : a₀ ≡ (fa' e₀)
                 a₀≡fa'₀ = symm fa'≈a₀

                 fa₀≡fa'₀ : (fa u e₀) ≡ fa' e₀
                 fa₀≡fa'₀ = appCongDep (fa↗fa' u)

                 s : subst (λ a → B ( p e₀ , a)) fa₀≡a₀ (snd (f u e₀) ) ≡ b₀
                 s = Σeq₂ (snd h₀ u)

    fa'₁ = fa' e₁

    Σb₁' = fst (β q) φ fb' e₀ e₁ (b₀' , fb'↗b₀')

    b₁' : B (p e₁ , fa'₁)
    b₁' = fst Σb₁'

    fb'↗b₁' : prf ((φ , fb') ∙ e₁ ↗ b₁')
    fb'↗b₁' = snd Σb₁'

    b₁ : B (p e₁ , a₁)
    b₁ = subst (λ a → B (p e₁ , a)) (fillAtAny α p φ fa e₀ a₀ fa↗a₀ e₁) b₁'

    f↗ab₁ : prf ((φ , f ) ∙ e₁ ↗ (a₁ , b₁))
    f↗ab₁ u = Σext (fa↗a₁ u) (transLift fa₁≡fa'₁ fa₁≡a₁ fa'₁≡a₁ fb'₁≡b₁') where
                fa₁ = fst (f u e₁)
                fb'₁ = fb' u e₁

                fa₁≡fa'₁ : fa₁ ≡ fa'₁
                fa₁≡fa'₁ = appCongDep (fa↗fa' u)

                fa₁≡a₁ : fa₁ ≡ a₁
                fa₁≡a₁ = fa↗a₁ u

                fa'₁≡a₁ : fa'₁ ≡ a₁
                fa'₁≡a₁ = fillAtAny α p φ fa e₀ a₀ fa↗a₀ e₁

                fb'₁≡b₁' : fb'₁ ≡ b₁'
                fb'₁≡b₁' = fb'↗b₁' u

    h₁ : ⟦ x₁ ∈ (Σ' A B) (p e₁) ∣ (φ , f) ∙ e₁ ↗ x₁ ⟧ 
    h₁ = (a₁ , b₁) , f↗ab₁

  module Reduce (φ : Cof) (f : [ φ ] → Π ((Σ' A B) ∘ p))
                (e : Int) (h : ⟦ x₀ ∈ (Σ' A B) (p e) ∣ (φ , f) ∙ e ↗ x₀ ⟧) where
   module c = Construct φ f e e h

   Σa₁≡Σa₀ : (c.a₁ , c.fa↗a₁) ≡ (c.a₀ , c.fa↗a₀)
   Σa₁≡Σa₀ = snd (α p) φ c.fa  e ((c.a₀ , c.fa↗a₀))

   Σb₁'≡Σb₀' : (c.b₁' , c.fb'↗b₁') ≡ (c.b₀' , c.fb'↗b₀')
   Σb₁'≡Σb₀' = snd (β c.q) φ c.fb' e (c.b₀' , c.fb'↗b₀')

   ab₁≡ab₀ : (c.a₁ , c.b₁) ≡ (c.a₀ , c.b₀)
   ab₁≡ab₀ = symm (Σext (symm (cong fst Σa₁≡Σa₀)) (transLift (symm c.fa'≈a₀) (symm (cong fst Σa₁≡Σa₀)) (fillAtAny α p φ c.fa e c.a₀ c.fa↗a₀ e) (symm (cong fst Σb₁'≡Σb₀'))))

   h₁≡h₀ : c.h₁ ≡ h
   h₁≡h₀ = Σext ab₁≡ab₀ (funext (λ x → uip (subst (λ x₁ → prf ((φ , f) ∙ e ↗ x₁)) ab₁≡ab₀ c.f↗ab₁ x) (snd h x)))

 FibΣid :
  {A : Int → Set}
  {B : (Σ x ∈ Int , A x) → Set}
  (α : isFib A)
  (β : isFib B)
  → -----------
  isFib (Σ' A B)
 FibΣid {A} {B} α β p = (construct , reduce) where
  module fibΣidInternal = FibΣidInternal {A} {B} α β p
  construct : Comp ((Σ' A B ) ∘ p)
  construct φ f e₀ e₁ h₀ = c.h₁ where
   module c = fibΣidInternal.Construct φ f e₀ e₁ h₀
  reduce : Reduce construct
  reduce φ f e h = r.h₁≡h₀ where
   module r = fibΣidInternal.Reduce φ f e h


 fstFibΣid :
  {A : Int → Set}
  {B : (Σ x ∈ Int , A x) → Set}
  (α : isFib A)
  (β : isFib B)
  (e₀ e₁ : Int)(p : Int → Int)
  (φ : Cof)(f : [ φ ] → Π ((Σ' A B) ∘ p))
  (ab₀ : ⟦ ab ∈ Σ' A B (p e₀) ∣ (φ , f) ∙ e₀ ↗ ab ⟧)
  → -----------
  fst (fst (fst (FibΣid {A} {B} α β p)  φ f e₀ e₁ ab₀)) ≡ fst (fst (α p) φ (λ u i → fst (f u i)) e₀ e₁  ((fst (fst ab₀)) , (λ u → cong fst (snd ab₀ u))))
 fstFibΣid α β e p φ f ab₀ = λ ab₁ → refl

_×id : {A A' : Set}{B : A' → Set}(f : A → A') → Σ A (B ∘ f) → Σ A' B
(f ×id) (a , b) = (f a , b)

FibΣ :
  {Γ : Set}
  {A : Γ → Set}
  {B : (Σ x ∈ Γ , A x) → Set}
  (α : isFib A)
  (β : isFib B)
  → -----------
  isFib (Σ' A B)
fst (FibΣ {Γ} {A} {B} α β p) = fst (FibΣid (reindex A α p) (reindex B β (p ×id)) id)
snd (FibΣ {Γ} {A} {B} α β p) = snd (FibΣid (reindex A α p) (reindex B β (p ×id)) id)

----------------------------------------------------------------------
-- Forming Σ-types is stable under reindexing
----------------------------------------------------------------------
reindexΣ :
  {Δ Γ : Set}
  (A : Γ → Set)
  (B : Σ Γ A → Set)
  (α : isFib A)
  (β : isFib B)
  (ρ : Δ → Γ)
  → ----------------------
  reindex (Σ' A B) (FibΣ {B = B} α β) ρ ≡ FibΣ {B = B ∘ (ρ ×id)} (reindex A α ρ) (reindex B β (ρ ×id))
reindexΣ A B α β ρ = refl
