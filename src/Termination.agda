------------------------------------------------------------------------
-- The "terminates" relation
------------------------------------------------------------------------

open import Atom

module Termination (atoms : χ-atoms) where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Double-negation equality-with-J
open import Monad equality-with-J
open import Nat equality-with-J as Nat using (_≤_)

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

-- If e terminates then e terminates in n steps for some n.

⇓→⇓≤ : ∀ {e} → Terminates e → ∃ (e ⇓≤_)
⇓→⇓≤ (v , p) = (size p , v , p , Nat.≤-refl)

-- If e does not terminate in any number of steps then e does not
-- terminate.

¬⇓≤→¬⇓ : ∀ {e} → (∀ n → ¬ e ⇓≤ n) → ¬ Terminates e
¬⇓≤→¬⇓ {e = e} ¬⇓ =
  Terminates e  →⟨ ⇓→⇓≤ ⟩
  ∃ (e ⇓≤_)     →⟨ uncurry ¬⇓ ⟩□
  ⊥             □

-- If it is not the case that, for every n, e does not terminate in at
-- most n steps, then it is not the case that e does not terminate.

¬¬⇓≤→¬¬⇓ : ∀ {e} → ¬ (∀ n → ¬ e ⇓≤ n) → ¬ ¬ Terminates e
¬¬⇓≤→¬¬⇓ {e = e} =
  ¬ (∀ n → ¬ e ⇓≤ n)    →⟨ (λ hyp₁ hyp₂ → hyp₁ (curry hyp₂)) ⟩
  ¬ ¬ (∃ λ n → e ⇓≤ n)  →⟨ wrap ⟩
  ¬¬ (∃ λ n → e ⇓≤ n)   →⟨ (λ (_ , v , e⇓v , _) → v , e⇓v) ⟨$⟩_ ⟩
  ¬¬ Terminates e       →⟨ (λ hyp → hyp .run) ⟩□
  ¬ ¬ Terminates e      □
