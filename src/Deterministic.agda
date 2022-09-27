------------------------------------------------------------------------
-- The semantics is deterministic
------------------------------------------------------------------------

open import Atom

module Deterministic (atoms : χ-atoms) where

open import Equality.Propositional
open import Prelude hiding (const)
open import Tactic.By.Propositional

open import Chi          atoms
open import Cancellation atoms

open χ-atoms atoms

-- The Lookup relation is deterministic (in a certain sense).

Lookup-deterministic :
  ∀ {c₁ c₂ bs xs₁ xs₂ e₁ e₂} →
  Lookup c₁ bs xs₁ e₁ → Lookup c₂ bs xs₂ e₂ →
  c₁ ≡ c₂ → xs₁ ≡ xs₂ × e₁ ≡ e₂
Lookup-deterministic here          here          _    = refl , refl
Lookup-deterministic here          (there q _)   refl = ⊥-elim (q refl)
Lookup-deterministic (there p _)   here          refl = ⊥-elim (p refl)
Lookup-deterministic (there p₁ p₂) (there q₁ q₂) refl =
  Lookup-deterministic p₂ q₂ refl

-- The relation _[_←_]↦_ is deterministic (in a certain sense).

↦-deterministic :
  ∀ {e xs es e₁ e₂} →
  e [ xs ← es ]↦ e₁ → e [ xs ← es ]↦ e₂ → e₁ ≡ e₂
↦-deterministic []    []    = refl
↦-deterministic (∷ p) (∷ q) = by (↦-deterministic p q)

mutual

  -- The semantics is deterministic.

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

-- Some corollaries.

apply-deterministic :
  ∀ {e₁ e₂ x₁ x₂ e′₁ e′₂ v₂₁ v₂₂} →
  e₁ ⇓ lambda x₁ e′₁ → e₂ ⇓ v₂₁ →
  e₁ ⇓ lambda x₂ e′₂ → e₂ ⇓ v₂₂ →
  (x₁ ≡ x₂ × e′₁ ≡ e′₂ × v₂₁ ≡ v₂₂) ×
  e′₁ [ x₁ ← v₂₁ ] ≡ e′₂ [ x₂ ← v₂₂ ]
apply-deterministic
  {x₁ = x₁} {x₂ = x₂} {e′₁ = e′₁} {e′₂ = e′₂} {v₂₁ = v₂₁} {v₂₂ = v₂₂}
  p₁ q₁ p₂ q₂ =
  case cancel-lambda $ ⇓-deterministic p₁ p₂ of λ
    (x₁≡x₂ , e′₁≡e′₂) →
      case ⇓-deterministic q₁ q₂ of λ
        v₂₁≡v₂₂ →
            (x₁≡x₂ , e′₁≡e′₂ , v₂₁≡v₂₂)
          , (e′₁ [ x₁ ← v₂₁ ]  ≡⟨ cong (e′₁ [ x₁ ←_]) v₂₁≡v₂₂ ⟩
             e′₁ [ x₁ ← v₂₂ ]  ≡⟨ cong₂ (_[_← v₂₂ ]) e′₁≡e′₂ x₁≡x₂ ⟩∎
             e′₂ [ x₂ ← v₂₂ ]  ∎)

case-deterministic₁ :
  ∀ {e bs c₁ c₂ vs₁ vs₂ xs₁ xs₂ e′₁ e′₂} →
  e ⇓ const c₁ vs₁ → Lookup c₁ bs xs₁ e′₁ →
  e ⇓ const c₂ vs₂ → Lookup c₂ bs xs₂ e′₂ →
  (c₁ ≡ c₂ × vs₁ ≡ vs₂ × xs₁ ≡ xs₂ × e′₁ ≡ e′₂) ×
  (∀ {e″} → e′₂ [ xs₂ ← vs₂ ]↦ e″ → e′₁ [ xs₁ ← vs₁ ]↦ e″)
case-deterministic₁
  {vs₁ = vs₁} {vs₂ = vs₂} {xs₁ = xs₁} {xs₂ = xs₂}
  {e′₁ = e′₁} {e′₂ = e′₂} p₁ q₁ p₂ q₂ =
  case cancel-const $ ⇓-deterministic p₁ p₂ of λ
    (c₁≡c₂ , vs₁≡vs₂) →
      case Lookup-deterministic q₁ q₂ c₁≡c₂ of λ
        (xs₁≡xs₂ , e′₁≡e′₂) →
            (c₁≡c₂ , vs₁≡vs₂ , xs₁≡xs₂ , e′₁≡e′₂)
          , (λ {e″ = e″} →
               e′₂ [ xs₂ ← vs₂ ]↦ e″  →⟨ subst id $ sym $ cong₂ (_[_← vs₂ ]↦ e″) e′₁≡e′₂ xs₁≡xs₂ ⟩
               e′₁ [ xs₁ ← vs₂ ]↦ e″  →⟨ subst (e′₁ [ xs₁ ←_]↦ e″) $ sym vs₁≡vs₂ ⟩□
               e′₁ [ xs₁ ← vs₁ ]↦ e″  □)

case-deterministic₂ :
  ∀ {e bs c₁ c₂ vs₁ vs₂ xs₁ xs₂ e′₁ e′₂ e″₁ e″₂} →
  e ⇓ const c₁ vs₁ → Lookup c₁ bs xs₁ e′₁ → e′₁ [ xs₁ ← vs₁ ]↦ e″₁ →
  e ⇓ const c₂ vs₂ → Lookup c₂ bs xs₂ e′₂ → e′₂ [ xs₂ ← vs₂ ]↦ e″₂ →
  (c₁ ≡ c₂ × vs₁ ≡ vs₂ × xs₁ ≡ xs₂ × e′₁ ≡ e′₂) × e″₁ ≡ e″₂
case-deterministic₂ p₁ q₁ r₁ p₂ q₂ r₂ =
  Σ-map id (λ e′₂↦→e′₁↦ → ↦-deterministic r₁ (e′₂↦→e′₁↦ r₂)) $
  case-deterministic₁ p₁ q₁ p₂ q₂
