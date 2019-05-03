------------------------------------------------------------------------
-- The "terminates" relation
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

open import Atom

module Termination (atoms : χ-atoms) where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude

open import H-level equality-with-J

open import Chi           atoms
open import Deterministic atoms
open import Propositional atoms

-- Terminates e means that e terminates with a value.

Terminates : Exp → Set
Terminates p = ∃ λ v → p ⇓ v

-- This relation is propositional.

Terminates-propositional :
  ∀ {e} →
  Is-proposition (Terminates e)
Terminates-propositional =
  _⇔_.from propositional⇔irrelevant
    λ { (_ , e₁) (_ , e₂) →
        Σ-≡,≡→≡ (⇓-deterministic e₁ e₂)
                (_⇔_.to propositional⇔irrelevant ⇓-propositional _ _) }
