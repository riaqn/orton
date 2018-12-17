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
module Data.id where

open import prelude
open import impredicative
open import interval
open import cof
open import fibrations
open import Data.paths
open import Data.products

----------------------------------------------------------------------
-- Id types
----------------------------------------------------------------------
Id : {Γ : Set}(A : Γ → Set) → Σ x ∈ Γ , A x × A x → Set
Id {Γ} A = Σ' (Path A) Prf where
  Prf : Σ (Σ Γ (λ x → A x × A x)) (Path A) → Set
  Prf ((x , (a , a')) , p) = ⟦ φ ∈ Cof ∣ fst φ ⊃ (All i ∈ Int , fst p i ≈ a) ⟧

pathToId : {Γ : Set}{A : Γ → Set}{x : Γ}{a a' : A x} → Path A (x , a' , a') → Id A (x , a' , a')
pathToId p = (p , cofFalse , (λ ()))

IdExt :
  {Γ : Set}
  {A : Γ → Set}
  {x : Γ}
  {a a' : A x}
  {id id' : Id A (x , (a , a'))}
  → ------------
  (fst (fst id) ≡ fst (fst id')) → (fst (fst (snd id))) ≡ fst (fst (snd id')) → id ≡ id'
IdExt {Γ} {A} {x} {a} {a'} {(p , u)} refl refl =
  let pathEq = (PathExt refl) in Σext pathEq (PrfExt pathEq refl) where
    Prf : Σ (Σ Γ (λ x → A x × A x)) (Path A) → Set
    Prf ((x , (a , a')) , p) = ⟦ φ ∈ Cof ∣ fst φ ⊃ (All i ∈ Int , fst p i ≈ a) ⟧
    PrfExt : {p p' : a ~ a'}(eq : p ≡ p'){u : Prf ((x , (a , a')) , p)}{v : Prf ((x , (a , a')) , p')}
      → fst (fst u) ≡ fst (fst v) → subst ((λ p → Prf ((x , a , a') , p))) eq u ≡ v
    PrfExt {p} {_} refl {((φ , _) , _)} refl =
      Σext (Σext refl (eq (cof φ))) (eq (φ ⊃ all Int (λ i → fst p i ≈ a)))

existsCof : (φ : Cof)(f : [ φ ]  → Ω) → ((u : [ φ ]) → prf (cof (f u))) → prf (cof (exists [ φ ] f))
existsCof φ f fCof = subst (prf ∘ cof) eqProps' cofφ&exists where
  imp : prf (fst φ ⊃ cof (exists [ φ ] f))
  imp u = subst (prf ∘ cof) eqProps (fCof u) where
    eqProps : f u ≡ exists [ φ ] f
    eqProps = propext (λ v → ∣ (u , v) ∣) (λ v → ∥∥-elim body (λ _ _ → eq (f u)) v) where
      body : Σ (prf (fst φ)) (λ v₁ → prf (f v₁)) → prf (f u)
      body (u' , fu') = subst (prf ∘ f) (eq (fst φ)) fu'
      
  eqProps' : (fst φ & exists [ φ ] f) ≡ exists [ φ ] f
  eqProps' = propext snd (λ u → (∥∥-rec (fst φ) fst u , u))
  
  cofφ&exists : prf (cof (fst φ & exists [ φ ] f))
  cofφ&exists = cof& (fst φ) (exists [ φ ] f) (snd φ) imp
  
Ωext : {prf₀ prf₁ : Set}
       {equ₀ : (u v : prf₀) → u ≡ v}
       {equ₁ : (u v : prf₁) → u ≡ v}
       (p : prf₀ ≡ prf₁)
       (q : subst (λ prf → (u v : prf) → u ≡ v) p equ₀ ≡ equ₁)
       →
       prop prf₀ equ₀ ≡ prop prf₁ equ₁
Ωext refl refl = refl

FibId' : {A : Int → Set} → isFib A → isFib (Id A)
FibId' {A} α = FibΣ {B = Prf} (FibPath {A = A} α) β where
  Γ' : Set
  Γ' = Σ (Σ Int (λ x → A x × A x)) (Path A)
  
  Prf : Γ' → Set
  Prf ((x , (a , a')) , p) = ⟦ φ ∈ Cof ∣ fst φ ⊃ (All i ∈ Int , fst p i ≈ a) ⟧
  
  prfExt : {x : Int}{a a' : A x}{p : a ~ a'}{pr pr' : Prf ((x , (a , a')) , p)} → fst (fst pr) ≡ fst (fst pr') → pr ≡ pr'
  prfExt {x} {a} {a'} {p} {((φ , _) , _)} {_} refl = Σext (Σext refl (eq (cof φ))) (eq (φ ⊃ (All i ∈ Int , fst p i ≈ a)))

  module FibPrfInternal (p : Int → Γ') where
   module Construct (φ : Cof) (f : [ φ ] → Π (Prf ∘ p))
                    (e₀ e₁ : Int) (h₀ : ⟦ x₀ ∈ Prf (p e₀) ∣ (φ , f ) ∙ e₀ ↗ x₀ ⟧)  where
    h₁ : ⟦ h₁ ∈ (Prf (p e₁)) ∣ (φ , f) ∙ e₁ ↗ h₁ ⟧
    fst (fst h₁) = (exists [ φ ] fI , existsCof φ fI (λ u → snd (fst (f u e₁)))) where
      fI : [ φ ] → Ω
      fI u = fst (fst (f u e₁))
    snd (fst h₁) ex i = ex goal proof where
      goal : Ω
      goal = fst (snd (p e₁)) i ≈ fst (snd (fst (p e₁)))
      proof : Σ [ φ ] (λ u → prf (fst (fst (f u e₁)))) → prf (goal)
      proof (u , v) = snd (f u e₁) v i
    snd h₁ u = prfExt {p = snd (p e₁)} (propext (λ v → ∣ u , v ∣) backwards) where
      backwards : prf (fst (fst (fst h₁))) → prf (fst (fst (f u e₁)))
      backwards v = ∥∥-rec (fst (fst (f u e₁))) (λ pair → subst (λ v → [ fst (f v e₁) ]) (eq (fst φ )) (snd pair)) v
   module Reduce (φ : Cof) (f : [ φ ] → Π (Prf ∘ p))
                 (e : Int) (h : ⟦ x₀ ∈ Prf (p e) ∣ (φ , f) ∙ e ↗ x₀ ⟧) where
    module c = Construct φ f e e h

    h₁≡h₀ : c.h₁ ≡ h
    h₁≡h₀ = Σext (prfExt (propext (∥∥-elim (λ x → subst (λ k → prf (fst (fst k))) (snd h (fst x)) (snd x) ) λ x x' → {!cong !}) λ x P x₁ → x₁ {!!})) (funext (λ x → uipImp))

  β : isFib Prf
  β p = (construct , reduce) where
   module fibPrfInternal = FibPrfInternal p
   construct : Comp (Prf ∘ p)
   construct φ f e₀ e₁ h₀ = c.h₁ where
    module c = fibPrfInternal.Construct φ f e₀ e₁ h₀
   reduce : Reduce construct
   reduce φ f e h = r.h₁≡h₀ where
    module r = fibPrfInternal.Reduce φ f e h
FibId : {Γ : Set}{A : Γ → Set} → isFib A → isFib (Id A)
FibId {Γ} {A} α p = FibId' (reindex A α (fst ∘ p)) (id× p) where
  id×_ : (p : Int → Σ Γ (λ x → A x × A x)) → Int → Σ Int (λ i → A (fst (p i)) × A (fst (p i)))
  (id× p) i = (i , snd (p i))

----------------------------------------------------------------------
-- Forming Id types is stable under reindexing
----------------------------------------------------------------------
reindexId :
  {Δ Γ : Set}
  (A : Γ → Set)
  (α : isFib A)
  (ρ : Δ → Γ)
  → ----------------------
  reindex (Id A) (FibId α) (ρ ×id) ≡ FibId (reindex A α ρ)
reindexId A α ρ = refl


----------------------------------------------------------------------
-- Refl and J-eliminator
----------------------------------------------------------------------
reflId : {Γ : Set}(A : Γ → Set){x : Γ}(a : A x) → Id A (x , (a , a))
reflId {Γ} A {x} a = (reflPath {A = A} a , (cofTrue , (λ tt i → refl)))


private
 triple :
  {Γ : Set}
  (A : Γ → Set)
  {x : Γ}
  {a : A x}
  (B : Σ a' ∈ (A x) , Id A (x , (a , a')) → Set)
  (a' : A x)
  (e : Id A (x , (a , a')))
  (b : B (a' , e))
  → Σ a' ∈ (A x) , Σ e ∈ (Id A (x , (a , a'))) , B (a' , e)
 triple _ _ a' e b = (a' , e , b)

private
 tripleExt :
  {Γ : Set}
  (A : Γ → Set)
  {x : Γ}
  {a₀ : A x}
  (B : Σ a' ∈ (A x) , Id A (x , (a₀ , a')) → Set)
  {a a' : A x}
  {e  : Id A (x , (a₀ , a))}
  {e' : Id A (x , (a₀ , a'))}
  {b  : B (a , e)}
  {b' : B (a' , e')}
  (_ : a ≡ a')
  (_ : fst (fst e) ≡ fst (fst e'))
  (_ : fst (fst (snd e)) ≡  fst (fst (snd e')))
  (eqB : (p : (a , e) ≡ (a' , e')) → subst B p b ≡ b')
  -----------------
  → triple A B a e b ≡ triple A B a' e' b'
 tripleExt A {x} {a₀} B {a} .{a} {e} {e'} {b} {b'} refl p q eqB =
   Σext refl (Σext (IdExt {A = A} p q) (trans step₂ step₁)) where
     substLemma : (e' : Id A (x , (a₀ , a)))(p : e ≡ e')
       → subst (λ e → B (a , e)) p b ≡ subst B (Σext refl p) b
     substLemma _ refl = refl
     step₁ : subst (λ e₁ → B (a , e₁)) (IdExt {A = A} p q) b ≡ subst B (Σext refl (IdExt {A = A} p q)) b
     step₁ = substLemma e' (IdExt {A = A} p q)
     step₂ : subst B (Σext refl (IdExt {A = A} p q)) b ≡ b'
     step₂ = eqB ((Σext refl (IdExt {A = A} p q)))

private
 Jinternal :
  {Γ : Set}
  {A : Γ → Set}
  {x : Γ}
  {a : A x}
  (B : Σ a' ∈ (A x) , Id A (x , (a , a')) → Set)
  (β : isFib B)
  (a' : A x)
  (e : Id A (x , (a , a')))
  → -------------
  (b : B (a , reflId A a)) → ⟦ b' ∈ B(a' , e) ∣ fst (fst (snd e)) ⊃ (triple A B a' e b') ≈ (triple A B a (reflId A a) b) ⟧
 Jinternal {Γ} {A} {x} {a} B β a' (p , φ , pRefl) b = {!!}

J :
  {Γ : Set}
  {A : Γ → Set}
  {x : Γ}
  {a : A x}
  (B : Σ a' ∈ (A x) , Id A (x , (a , a')) → Set)
  (β : isFib B)
  (a' : A x)
  (e : Id A (x , (a , a')))
  → -------------
  B (a , reflId A a) → B(a' , e)
J {Γ} {A} {x} {a} B β a' e b = fst (Jinternal {A = A} B β a' e b)


Jrefl :
  {Γ : Set}
  {A : Γ → Set}
  {x : Γ}
  {a : A x}
  (B : Σ a' ∈ (A x) , Id A (x , (a , a')) → Set)
  (β : isFib B)
  (b : B (a , reflId A a))
  → -------------
  J {A = A} B β a (reflId A a) b ≡ b
Jrefl {Γ} {A} {x} {a} B β b = extractEq (snd (Jinternal {A = A} B β a (reflId A a) b) tt) where
  extractEq :
    {b b' : B (a , reflId A a)}
    → -------------
    triple A B a (reflId A a) b ≡ triple A B a (reflId A a) b' → b ≡ b' 
  extractEq {b} .{b} refl = refl
