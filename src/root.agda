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

module root where

----------------------------------------------------------------------
-- Introducing basics (e.g. equality, products etc)
----------------------------------------------------------------------
open import prelude

----------------------------------------------------------------------
-- Impredicative universe of propositions and logic
----------------------------------------------------------------------
open import impredicative 

----------------------------------------------------------------------
-- The interval I
----------------------------------------------------------------------
open import interval

----------------------------------------------------------------------
-- Cofibrant propositions
----------------------------------------------------------------------
open import cof

----------------------------------------------------------------------
-- Fibrations
----------------------------------------------------------------------
open import fibrations

----------------------------------------------------------------------
-- Type formers: products, functions, path and identity types
----------------------------------------------------------------------
open import Data.products
open import Data.functions
open import Data.paths
open import Data.id

----------------------------------------------------------------------
-- Equivalences, quasi-inverss, contractiability, extendability etc
----------------------------------------------------------------------
open import equivs

----------------------------------------------------------------------
-- The glueing construction
----------------------------------------------------------------------
open import glueing

----------------------------------------------------------------------
-- Univalence 
----------------------------------------------------------------------
open import univalence
