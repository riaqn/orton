
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
module fibrations where 

open import prelude
open import impredicative
open import interval
open import cof
open import Agda.Builtin.TrustMe

----------------------------------------------------------------------
-- Path composition structure
----------------------------------------------------------------------
Comp : (Int → Set) → Set
Comp A = (φ : Cof) (f : [ φ ] → Π A) → (e₀ e₁ : Int)
         (h₀ : ⟦ x₀ ∈ (A e₀) ∣ (φ , f) ∙ e₀ ↗ x₀ ⟧)
         →     ⟦ x₁ ∈ (A e₁) ∣ (φ , f) ∙ e₁ ↗ x₁ ⟧

Reduce : {A : Int → Set} → (c : Comp A) → Set
Reduce {A = A} c = (φ : Cof) (f : [ φ ] → Π A) (e : Int) → (h : ⟦ a ∈ A e ∣ (φ , f) ∙ e ↗ a ⟧) → (c φ f e e h) ≡ h

----------------------------------------------------------------------
-- Fibrations
----------------------------------------------------------------------

isFib : ∀{a} {Γ : Set a} (A : Γ → Set) → Set a
isFib {a = a} {Γ = Γ} A = (p : Int → Γ) → Σ c ∈ Comp (A ∘ p) , Reduce c

Fib : ∀{a}(Γ : Set a) → Set (lsuc lzero ⊔ a)
Fib {a} Γ = Σ (Γ → Set) isFib

----------------------------------------------------------------------
-- Fibrations can be reindexed
----------------------------------------------------------------------
reindex : ∀{a a'}{Δ : Set a}{Γ : Set a'}(A : Γ → Set)(α : isFib A)(ρ : Δ → Γ) → isFib (A ∘ ρ)
reindex A α ρ p = α (ρ ∘ p)

reindex' : ∀{a a'}{Δ : Set a}{Γ : Set a'}(Aα : Fib Γ)(ρ : Δ → Γ) → Fib Δ
reindex' (A , α) ρ = (A ∘ ρ , reindex A α ρ)

{-
----------------------------------------------------------------------
-- Reindexing is functorial
----------------------------------------------------------------------
reindexAlongId : {Γ : Set}{A : Γ → Set}{α : isFib A} → α ≡ reindex A α id 
reindexAlongId = refl

reindexComp :
  {Γ₁ Γ₂ Γ₃ : Set}{A : Γ₃ → Set}{α : isFib A}
  (f : Γ₁ → Γ₂)(g : Γ₂ → Γ₃)
  → ----------------------
  reindex A α (g ∘ f) ≡ reindex (A ∘ g) (reindex A α g) f
reindexComp g f = refl

reindexAlongId' : {Γ : Set}{A : Fib Γ} → reindex' A id ≡ A
reindexAlongId' = refl

abstract
 reindexComp' :
  {Γ₁ Γ₂ Γ₃ : Set}{A : Fib Γ₃}
  (f : Γ₁ → Γ₂)(g : Γ₂ → Γ₃)
  → ----------------------
  reindex' A (g ∘ f) ≡ reindex' (reindex' A g) f
 reindexComp' g f = refl


----------------------------------------------------------------------
-- Using the fibration structure to interpret
-- Γ ⊢ comp^i A [φ ↦ u] a₀
----------------------------------------------------------------------
comp^i :
  -- Context Γ
  {Γ : Set}
  -- Fibrant type Γ, i:𝕀 ⊢ A
  (A : (Γ × Int) → Set)
  (α : isFib A)
  -- Face formula Γ ⊢ φ : 𝔽
  (φ : Γ → Cof)
  -- Partial element Γ, φ, i:𝕀 ⊢ u : A
  (u : (x : Γ)(_ : [ φ x ])(i : Int) → A (x , i))
  -- Term Γ ⊢ a₀ : A(i0)[φ ↦ u(i0)]
  (a₀ : ⟦ a₀ ∈ ((x : Γ) → A (x , O)) ∣ All x ∈ Γ , ((φ x , u x) ∙ O ↗ a₀ x) ⟧)
  → -------------
  -- Resulting term:  Γ ⊢ comp^i A [φ ↦ u] a₀
  ⟦ a₁ ∈ ((x : Γ) → A (x , I)) ∣ All x ∈ Γ , ((φ x , u x) ∙ I ↗ a₁ x) ⟧
comp^i A α φ u (a₀ , ext) =
  ( (λ x → fst (fst ({!!})))
  , (λ x → snd (fst ({!!}))))

-- This has the required uniformity property
comp^iReindex :
  {Δ Γ : Set}
  (A : (Γ × Int) → Set)
  (α : isFib A)
  (φ : Γ → Cof)
  (u : (x : Γ)(_ : [ φ x ])(i : Int) → A (x , i))
  (a₀ : ⟦ a₀ ∈ ((x : Γ) → A (x , O)) ∣ All x ∈ Γ , ((φ x , u x) ∙ O ↗ a₀ x) ⟧)
  (f : Δ → Γ)
  → -------------
  (λ x → fst (comp^i A α φ u a₀) (f x))
      ≡ fst (comp^i (A ∘ (f ×' id)) (reindex A α (f ×' id)) (φ ∘ f)
          (λ x φfx → u (f x) φfx) ((λ x → fst a₀ (f x)) , (λ x → snd a₀ (f x))))
comp^iReindex A α φ u a₀ f = refl

----------------------------------------------------------------------
-- Trvial compositions might not reduce (we don't have regularity)
----------------------------------------------------------------------

trivComp : {Γ : Set}(A : Fib Γ)(e : Int)(x : Γ)(a : fst A x) → fst A x
trivComp (A , α) e x a = fst (α e e (λ _ → x) cofFalse ∅-elim (a , (λ ())))

----------------------------------------------------------------------
-- An extentionality principle for fibration structures
----------------------------------------------------------------------
fibExt : {Γ : Set}{A : Γ → Set}{α α' : isFib A}
  → ((e e' : Int)(p : Int → Γ)
     (φ : Cof)(f : [ φ ] → Π (A ∘ p))
     (a₀ : ⟦ x₁ ∈ (A (p e)) ∣ (φ , f) ∙ e ↗ x₁ ⟧) → fst (α e e' p φ f a₀) ≡ fst (α' e e' p φ f a₀))
  → α ≡ α'
fibExt {α = α} {α'} ext =
  funext (λ e → funext (λ e' → funext (λ p → funext (λ φ → funext (λ f →
    funext (λ a₀ → incMono (λ x → (φ , f) ∙ e' ↗ x) (α e e' p φ f a₀) (α' e e' p φ f a₀) (ext e e' p φ f a₀)))))))

----------------------------------------------------------------------
-- Terminal object is fibrant
----------------------------------------------------------------------
FibUnit : {Γ : Set} → isFib(λ(_ : Γ) → Unit)
fst (FibUnit _ _ _ _ _ (unit , _))   = unit
snd (FibUnit _ _ _ _ _ (unit , _)) _ = refl

----------------------------------------------------------------------
-- Initial object is fibrant
----------------------------------------------------------------------
Fib∅ : {Γ : Set} → isFib(λ(_ : Γ) → ∅)
Fib∅ _ _ _ _ _ (() , _)

----------------------------------------------------------------------
-- Fibrations are closed under isomorphism
----------------------------------------------------------------------
_≅_ : {Γ : Set}(A B : Γ → Set) → Set
_≅_ {Γ} A B = (x : Γ) → Σ f ∈ (A x → B x) , Σ g ∈ (B x → A x) , (g ∘ f ≡ id) × (f ∘ g ≡ id)

FibIso : {Γ : Set}(A B : Γ → Set) → (A ≅ B) → isFib A → isFib B
FibIso A B iso α e e' p φ q b = b' where
  f : (i : Int) → A (p i) → B (p i)
  f i = fst (iso (p i))
  g : (i : Int) → B (p i) → A (p i)
  g i = fst (snd (iso (p i)))
  q' : [ φ ] → Π (A ∘ p)
  q' u i = g i (q u i)
  a : ⟦ a ∈ ((A ∘ p) e ) ∣ ((φ , q') ∙ e) ↗ a ⟧
  fst a = g e (fst b)
  snd a u = cong (g e) (snd b u)
  a' : ⟦ a ∈ ((A ∘ p) e') ∣ ((φ , q') ∙ e') ↗ a ⟧
  a' = α e e' p φ q' a
  b' : ⟦ b ∈ ((B ∘ p) e') ∣ ((φ , q) ∙ e') ↗ b ⟧
  fst b' = f e' (fst a')
  snd b' u = z where
    x : q' u e' ≡ fst a'
    x = snd a' u
    y : f e' (q' u e') ≡ f e' (fst a')
    y = cong (f e') x
    z : q u e' ≡ f e' (fst a')
    z = trans y (cong (λ f → f (q u e')) (symm (snd (snd (snd (iso (p e')))))))

-- trans fgq≡b' (symm (fgq≡q)) where
--     fgq≡b' : f !e (g !e (q u !e)) ≡ fst b'
--     fgq≡b' = cong (f !e) (snd a' u)
--     fgq≡q : f !e (g !e (q u !e)) ≡ q u !e
--     fgq≡q = cong (λ f → f (q u !e)) (snd (snd (snd (iso (p !e)))))

trivialFibIso : {Γ : Set}(A B : Γ → Set)(iso : A ≅ B)(α : isFib A)
  (p : Int → Γ)(b : B (p O))
  → fst (FibIso A B iso α O I p cofFalse ∅-elim (b , λ ()))
    ≡ fst (iso (p I)) (fst (α O I p cofFalse ∅-elim (fst (snd (iso (p O))) b , λ ())))
trivialFibIso A B iso α p b =
  cong (λ hh' → fst (iso (p I)) (fst (α O I p cofFalse (fst hh') (fst (snd (iso (p O))) b , snd hh'))))
    (Σext (funext (λ ())) (funext (λ ())))
-}
----------------------------------------------------------------------
-- Path filling structure
----------------------------------------------------------------------
Fill : (Int → Set) → Set
Fill A =
  (φ : Cof)
  (f : [ φ ] → Π A)
  (e : Int)
  (h : ⟦ a ∈ A e ∣ ((φ , f) ∙ e ↗ a )⟧)
  → --------------------------------------
  ⟦ p ∈ Π A ∣ ((φ , f ) ↗ p) & p e ≈ fst h ⟧ 

----------------------------------------------------------------------
-- Compatible partial functions
----------------------------------------------------------------------
_⌣_ : {A : Set} → □ A → □ A → Ω
(φ , f) ⌣ (ψ , g) = All u ∈ [ φ ] , All v ∈ [ ψ ] , f u ≈ g v

_∪_ :
  {A : Set}
  {φ ψ : Cof}
  (f : [ φ ] → A)
  (g : [ ψ ] → A)
  {p : prf((φ , f) ⌣ (ψ , g))}
  → ---------------------------
  [ φ ∨ ψ ] → A
_∪_ {A} {φ} {ψ} f g {p} w = ∥∥-elim h q w where

  h : [ φ ] ⊎ [ ψ ] → A
  h (inl u) = f u
  h (inr v) = g v

  q : (z z' : [ φ ] ⊎ [ ψ ]) → h z ≡ h z'
  q (inl _) (inl _) = cong f (eq (fst φ))
  q (inl u) (inr v) = p u v
  q (inr v) (inl u) = symm (p u v)
  q (inr _) (inr _) = cong g (eq (fst ψ))

----------------------------------------------------------------------
-- Path filling from path composition
----------------------------------------------------------------------
private
 fillInternal :
  {Γ : Set}
  {A : Γ → Set}
  (α : isFib A)
  (p : Int → Γ)
  (φ : Cof)
  (f : [ φ ] → Π(A ∘ p))
  (e₀ : Int)
  (a : A (p e₀))
  (u : prf ((φ , f) ∙ e₀ ↗ a))
  → -----------
  Σ fill ∈ ⟦ fi ∈ Π (A ∘ p) ∣ ((φ , f ) ↗ fi) & (fi e₀ ≈ a) ⟧ ,
  ((e₁ : Int) → fst fill e₁ ≡ fst (fst (α p) φ f e₀ e₁ (a , u)))
 fillInternal {Γ} {A} α p φ f e a u = (fill , eqFib) where
  fill : ⟦ fi ∈ Π (A ∘ p) ∣ (( φ , f ) ↗ fi) & (fi e ≈ a) ⟧
  fst fill = λ i → fst (fst (α p) φ f e i (a , u))
  fst (snd fill) = λ x → funext (λ i → (snd (fst (α p) φ f e i (a , u)) x))
  snd (snd fill) = cong fst (snd (α p) φ f e (a , u))

  eqFib : (e' : Int) → fst fill e' ≡ fst (fst (α p) φ f e e' (a , u ))
  eqFib = λ e' → refl

abstract
 fill :
  {Γ : Set}
  {A : Γ → Set}
  (α : isFib A)
  (p : Int → Γ)
  → -----------
  Fill (A ∘ p)
 fill {Γ} {A} α p φ f e (a , u) = fst (fillInternal {A = A ∘ p} (reindex A α p) id φ f e a u)

 fillAtAny :
  {Γ : Set}
  {A : Γ → Set}
  (α : isFib A)
  (p : Int → Γ)
  (φ : Cof)
  (f : [ φ ] → Π (A ∘ p))
  (e : Int)
  (a : A (p e))
  (u : prf ((φ , f) ∙ e ↗ a))
  → -----------
  (e' : Int) → fst (fill {A = A} α p φ f e (a , u)) e' ≡ fst (fst (α p) φ f e e' (a , u))
 fillAtAny {Γ} {A} α p φ f e a u e' = snd (fillInternal {A = A ∘ p} (reindex A α p) id φ f e a u) e'


