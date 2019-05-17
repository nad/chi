------------------------------------------------------------------------
-- The semantics is deterministic
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

open import Atom

module Deterministic (atoms : χ-atoms) where

open import Equality.Propositional
open import Prelude hiding (const)
open import Tactic.By.Propositional

open import Chi atoms

open χ-atoms atoms

Lookup-deterministic :
  ∀ {c₁ c₂ bs xs₁ xs₂ e₁ e₂} →
  Lookup c₁ bs xs₁ e₁ → Lookup c₂ bs xs₂ e₂ →
  c₁ ≡ c₂ → xs₁ ≡ xs₂ × e₁ ≡ e₂
Lookup-deterministic here          here          _    = refl , refl
Lookup-deterministic here          (there q _)   refl = ⊥-elim (q refl)
Lookup-deterministic (there p _)   here          refl = ⊥-elim (p refl)
Lookup-deterministic (there p₁ p₂) (there q₁ q₂) refl =
  Lookup-deterministic p₂ q₂ refl

↦-deterministic :
  ∀ {e xs es e₁ e₂} →
  e [ xs ← es ]↦ e₁ → e [ xs ← es ]↦ e₂ → e₁ ≡ e₂
↦-deterministic []    []    = refl
↦-deterministic (∷ p) (∷ q) = by (↦-deterministic p q)

mutual

  ⇓-deterministic : ∀ {e v₁ v₂} → e ⇓ v₁ → e ⇓ v₂ → v₁ ≡ v₂
  ⇓-deterministic (apply p₁ p₂ p₃) (apply q₁ q₂ q₃)
    with ⇓-deterministic p₁ q₁ | ⇓-deterministic p₂ q₂
  ... | refl | refl = ⇓-deterministic p₃ q₃

  ⇓-deterministic (case p₁ p₂ p₃ p₄) (case q₁ q₂ q₃ q₄)
    with ⇓-deterministic p₁ q₁
  ... | refl with Lookup-deterministic p₂ q₂ refl
  ...   | refl , refl rewrite ↦-deterministic p₃ q₃ =
    ⇓-deterministic p₄ q₄

  ⇓-deterministic (rec p)    (rec q)    = ⇓-deterministic p q
  ⇓-deterministic lambda     lambda     = refl
  ⇓-deterministic (const ps) (const qs) = by (⇓⋆-deterministic ps qs)

  ⇓⋆-deterministic : ∀ {es vs₁ vs₂} → es ⇓⋆ vs₁ → es ⇓⋆ vs₂ → vs₁ ≡ vs₂
  ⇓⋆-deterministic []       []       = refl
  ⇓⋆-deterministic (p ∷ ps) (q ∷ qs) =
    cong₂ _∷_ (⇓-deterministic p q) (⇓⋆-deterministic ps qs)
