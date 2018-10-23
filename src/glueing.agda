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
module glueing where 

open import glueing.core
open import glueing.strict
open import glueing.fix
