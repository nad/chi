------------------------------------------------------------------------
-- The "terminates" relation
------------------------------------------------------------------------

open import Atom

module Termination (atoms : χ-atoms) where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Nat equality-with-J using (_≤_)

open import Chi             atoms
open import Derivation-size atoms
open import Deterministic   atoms
open import Propositional   atoms

-- Terminates e means that e terminates with a value.

Terminates : Exp → Type
Terminates p = ∃ λ v → p ⇓ v

-- This relation is propositional.

Terminates-propositional :
  ∀ {e} →
  Is-proposition (Terminates e)
Terminates-propositional (_ , e₁) (_ , e₂) =
  Σ-≡,≡→≡ (⇓-deterministic e₁ e₂)
          (⇓-propositional _ _)

-- Termination in at most a given number of steps.

infix 4 _⇓≤_ _⇓⋆≤_

_⇓≤_ : Exp → ℕ → Type
e ⇓≤ n = ∃ λ v → ∃ λ (p : e ⇓ v) → size p ≤ n

_⇓⋆≤_ : List Exp → ℕ → Type
es ⇓⋆≤ n = ∃ λ vs → ∃ λ (ps : es ⇓⋆ vs) → size⋆ ps ≤ n
