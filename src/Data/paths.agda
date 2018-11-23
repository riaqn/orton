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
module Data.paths where

open import prelude
open import impredicative
open import interval
open import cof
open import fibrations
open import Data.products

----------------------------------------------------------------------
-- Path types
----------------------------------------------------------------------
_~~_ : {A : Int → Set}(a : A O)(a' : A I) → Set
_~~_ {A} a a' = ⟦ p ∈ (Π A) ∣ (p O ≈ a) & (p I ≈ a') ⟧

_~_ : {A : Set}(a a' : A) → Set
_~_ {A} a a' = _~~_ {A = λ _ → A} a a'

transDep : {A : Int → Set}{α : isFib A}{a a' : A O}{b : A I} → (a ~~ b) → (a' ~~ b) → (a ~ a')
transDep {A} {α} {a} {a'} {b} (p , pO , pI) (q , qO , qI) = ((λ i → fst (r i)) , rO≡a , rI≡a') where
  f : (i : Int) → [ i ≈O ∨ i ≈I ] → Π A
  f i u j = OI-elim cases u where
    cases : (i ≡ O) ⊎ (i ≡ I) → A j
    cases (inl _) = p j
    cases (inr _) = q j
    
  r : (i : Int) → ⟦ a ∈ (A O) ∣ ((i ≈O ∨ i ≈I) , f i) ∙ O ↗ a ⟧
  r i = fst (α id) (i ≈O ∨ i ≈I) (f i) I O (b , or-elim-eq (λ u → f i u I) b pI qI)

  rO≡a : fst (r O) ≡ a
  rO≡a = trans pO (symm (snd (r O) ∣ inl refl ∣))

  rI≡a' : fst (r I) ≡ a'
  rI≡a' = trans qO (symm (snd (r I) ∣ inr refl ∣))

transDep' : {A : Int → Set}{α : isFib A}{a : A O}{b b' : A I} → (a ~~ b) → (a ~~ b') → (b ~ b')
transDep' {A} {α} {a} {b} {b'} (p , pO , pI) (q , qO , qI) = ((λ i → fst (r i)) , rO≡a , rI≡a') where
  f : (i : Int) → [ i ≈O ∨ i ≈I ] → Π A
  f i u j = OI-elim cases u where
    cases : (i ≡ O) ⊎ (i ≡ I) → A j
    cases (inl _) = p j
    cases (inr _) = q j
    
  r : (i : Int) → ⟦ b ∈ (A I) ∣ ((i ≈O ∨ i ≈I) , f i) ∙ I ↗ b ⟧
  r i = fst (α id) (i ≈O ∨ i ≈I) (f i) O I (a , or-elim-eq (λ u → f i u O) a pO qO)

  rO≡a : fst (r O) ≡ b
  rO≡a = trans pI (symm (snd (r O) ∣ inl refl ∣))

  rI≡a' : fst (r I) ≡ b'
  rI≡a' = trans qI (symm (snd (r I) ∣ inr refl ∣))

transPath : {A : Set}(α : isFib {Γ = Unit} (λ _ → A)){x y z : A} → x ~ y → y ~ z → x ~ z
transPath {A} α {x} {y} {z} p q = ((λ i → fst (r i)) , rO≡x , rI≡z) where
  f : (i : Int) → [ i ≈O ∨ i ≈I ] → Π (λ _ → A)
  f i u j = OI-elim cases u where
    cases : (i ≡ O) ⊎ (i ≡ I) → A
    cases (inl _) = x 
    cases (inr _) = fst q j
  
  qO=pI : (i : Int)(eq : i ≡ I) → fst q O ≡ fst p i
  qO=pI .I refl = trans (symm (snd (snd p))) (fst (snd q))

  pO=pi : (i : Int)(l : i ≡ O) → fst p O ≡ fst p i
  pO=pi .O refl = refl
  
  r : (i : Int) → ⟦ a ∈ A ∣ ((i ≈O ∨ i ≈I) , f i) ∙ I ↗ a ⟧
  r i = fst (α (λ _ → tt)) (i ≈O ∨ i ≈I) (f i) O I 
    ((fst p i , or-elim-eq (λ u → f i u O) (fst p i) (λ {l} → trans (pO=pi i l) (symm (fst (snd p)))) (λ {r} → qO=pI i r)))

  rO≡x : fst (r O) ≡ x
  rO≡x = symm (snd (r O) ∣ inl refl ∣)

  rI≡z : fst (r I) ≡ z
  rI≡z = trans (snd (snd q)) (symm (snd (r I) ∣ inr refl ∣))

congPath :
  {A : Set}
  {B : Set}
  (f : A → B)
  {x y : A}
  (p : x ~ y)
  → -----------
  f x ~ f y
congPath f p = ((f ∘ (fst p)) , (cong f (fst (snd p))) , cong f (snd (snd p)))

fillPath : {P : Int → Set}(ρ : isFib P)(x : P O) → _~~_ {P} x (fst (fst (ρ id) cofFalse ∅-elim O I (x , λ ())))
fillPath ρ x =
  let filler = fill ρ id cofFalse ∅-elim O (x , (λ ())) in
  fst filler , snd (snd filler) , fillAtAny ρ id cofFalse ∅-elim O x (λ ()) I

fillPath' : {P : Int → Set}(ρ : isFib P)(x : P I) → _~~_ {P} (fst (fst (ρ id) cofFalse ∅-elim I O (x , λ ()))) x
fillPath' ρ x =
  let filler = fill ρ id cofFalse ∅-elim I (x , (λ ())) in
  fst filler , fillAtAny ρ id cofFalse ∅-elim I x (λ ()) O , snd (snd filler)


Path : {Γ : Set}(A : Γ → Set) → Σ x ∈ Γ , A x × A x → Set
Path A (x , (a , a')) = a ~ a'

reflPath : {Γ : Set}{A : Γ → Set}{x : Γ}(a : A x) → Path A (x , (a , a))
reflPath a = ((λ _ → a) , refl , refl)

reflPath' : {A : Set}{a a' : A} → (a ≡ a') → a ~ a'
reflPath' {A} {a} .{a} refl = ((λ _ → a) , (refl , refl))

reflPathEval : {A : Set}{a a' : A}(p : a ≡ a')(i : Int) → fst (reflPath' p) i ≡ a'
reflPathEval refl i = refl

PathExt : {A : Set}{a a' : A}{p q : a ~ a'} → fst p ≡ fst q → p ≡ q
PathExt refl = Σext refl (Σext uipImp uipImp)

module FibPathIdInternal {A : Int → Set} 
                         (α : isFib A)
                         (p : Int → Σ γ ∈ Int , A γ × A γ) where
 module Construct (φ : Cof)
                  (f : [ φ ] → Π ((Path A) ∘ p))
                  (e₀ e₁ : Int)
                  (h₀ : ⟦ p₀ ∈ (Path A) (p e₀)∣ (φ , f) ∙ e₀ ↗ p₀ ⟧) where
  p₀ = fst h₀
  f↗p₀ = snd h₀

  f' : Int → [ φ ] → Π (A ∘ fst ∘ p)
  f' i u j = fst (f u j) i
  
  f₀ : (i : Int) → ⟦ g ∈ ([ i ≈O ] → Π (A ∘ fst ∘ p)) ∣ (φ , f' i) ⌣ (i ≈O , g) ⟧
  fst (f₀ i) _ j = fst (snd (p j))
  snd (f₀ .O) u refl = funext (λ j → fst (snd (f u j)))
  
  f₀' : (i : Int) → [ φ ∨ i ≈O ] → Π (A ∘ fst ∘ p)
  f₀' i = _∪_ {φ = φ} {ψ = i ≈O} (f' i) (fst (f₀ i)) {p = snd (f₀ i)}
  
  f₁ : (i : Int) → ⟦ g ∈ ([ i ≈I ] → Π (A ∘ fst ∘ p)) ∣ ((φ ∨ i ≈O) , f₀' i)  ⌣ (i ≈I , g) ⟧
  fst (f₁ i) _ j = snd (snd (p j))
  snd (f₁ .I) u refl = funext (λ j →
    or-elim-eq (λ v → f₀' I v j) (snd (snd (p j))) (λ {u'} → snd (snd (f u' j))) (λ {I≡O} → ∅-elim (O≠I (symm I≡O))) u)
    
  f₁' : (i : Int) → [ (φ ∨ i ≈O) ∨ i ≈I ] → Π (A ∘ fst ∘ p)
  f₁' i = _∪_ {φ = φ ∨ i ≈O} {ψ = i ≈I} (f₀' i) (fst (f₁ i)) {p = snd (f₁ i)}
  
  extends : (i : Int) → prf ((((φ ∨ i ≈O) ∨ i ≈I) , f₁' i) ∙ e₀ ↗ fst p₀ i)
  extends i u = or-elim-eq (λ v → f₁' i v e₀) (fst p₀ i) (λ {l} → leftCase l) (λ {r} → rightCase i r) u where
    rightCase : (i : Int)(r : i ≡ I) → f₁' i ∣ inr r ∣ e₀ ≡ fst p₀ i
    rightCase .I refl = symm (snd (snd p₀))
    leftCase : (l : prf (fst (φ ∨ i ≈O))) → f₁' i ∣ inl l ∣ e₀ ≡ fst p₀ i
    leftCase l = or-elim-eq (λ v → f₁' i ∣ inl v ∣ e₀) (fst p₀ i) (λ {l} → llCase l) (λ {r} → rlCase i r) l where
      rlCase : (i : Int)(r : i ≡ O) → f₁' i ∣ inl ∣ inr r ∣ ∣ e₀ ≡ fst p₀ i
      rlCase .O refl = symm (fst (snd p₀))
      llCase : (l : [ φ ]) → f₁' i ∣ inl ∣ inl l ∣ ∣ e₀ ≡ fst p₀ i
      llCase u = cong (λ p → fst p i) (f↗p₀ u)
      
  comp : (i : Int) → ⟦ a ∈ ((A ∘ fst ∘ p) e₁) ∣ (((φ ∨ i ≈O) ∨ i ≈I) , f₁' i) ∙ e₁ ↗ a ⟧
  comp i = fst (α (fst ∘ p)) ((φ ∨ i ≈O) ∨ i ≈I) (f₁' i) e₀ e₁ (fst p₀ i , extends i)
  
  p₁ : (Path A ∘ p) e₁
  fst p₁ i = fst (comp i)
  fst (snd p₁) = symm eqAtO where
    eqAtO : fst (snd (p e₁)) ≡ fst (comp O)
    eqAtO = snd (comp O) ∣ inl ∣ inr refl ∣ ∣
  snd (snd p₁) = symm eqAtI where
    eqAtI : snd (snd (p e₁)) ≡ fst (comp I)
    eqAtI = snd (comp I) ∣ inr refl ∣

  f↗p₁ : prf ((φ , f) ∙ e₁ ↗ p₁)
  f↗p₁ u = PathExt (funext (λ i → snd (comp i) ∣ inl ∣ inl u ∣ ∣))

  h₁ : ⟦ p₁ ∈ (Path A) (p e₁)∣ (φ , f) ∙ e₁ ↗ p₁ ⟧
  h₁ = (p₁ , f↗p₁)

 module Reduce (φ : Cof)
               (f : [ φ ] → Π ((Path A) ∘ p))
               (e : Int)
               (h₀ : ⟦ p₀ ∈ (Path A) (p e) ∣ (φ , f) ∙ e ↗ p₀ ⟧) where
  module c = Construct φ f e e h₀

  fstp₁≡fstp₀ : fst (c.p₁) ≡ fst (c.p₀)
  fstp₁≡fstp₀ = funext λ i → cong fst (snd (α (fst ∘ p)) ((φ ∨ i ≈O) ∨ i ≈I) (c.f₁' i) e (fst c.p₀ i , c.extends i ))

  p₁≡p₀ : c.p₁ ≡ c.p₀
  p₁≡p₀ = Σext fstp₁≡fstp₀ (Σext uipImp uipImp)

  h₁≡h₀ : c.h₁ ≡ h₀
  h₁≡h₀ = Σext p₁≡p₀ (funext (λ x → uipImp))

abstract
 FibPathId :
  {A : Int → Set}
  (α : isFib A)
  → -----------
  isFib (Path A)
 FibPathId {A} α p = (fibPathId.Construct.h₁ , fibPathId.Reduce.h₁≡h₀) where
  module fibPathId = FibPathIdInternal α p

FibPath :
  {Γ : Set}
  {A : Γ → Set}
  (α : isFib A)
  → -----------
  isFib (Path A)
FibPath {Γ} {A} α p =(FibPathId (reindex A α (fst ∘ p)) (id× p)) where
  id×_ : (p : Int → Σ Γ (λ x → A x × A x)) → Int → Σ Int (λ i → A (fst (p i)) × A (fst (p i)))
  (id× p) i = (i , snd (p i))

funextPath : {A : Set}{B : A → Set}{f g : (x : A) → B x} → ((a : A) → f a ~ g a) → f ~ g
fst (funextPath pointwise) i a = fst (pointwise a) i
fst (snd (funextPath pointwise)) = funext (λ a → fst (snd (pointwise a)))
snd (snd (funextPath pointwise)) = funext (λ a → snd (snd (pointwise a)))

----------------------------------------------------------------------
-- Forming Path types is stable under reindexing
----------------------------------------------------------------------
reindexPath :
  {Δ Γ : Set}
  (A : Γ → Set)
  (α : isFib A)
  (ρ : Δ → Γ)
  → ----------------------
  reindex (Path A) (FibPath α) (ρ ×id) ≡ FibPath (reindex A α ρ)
reindexPath A α ρ = refl
