------------------------------------------------------------------------
-- "Reasoning" combinators
------------------------------------------------------------------------

open import Atom

module Reasoning (atoms : χ-atoms) where

open import Equality.Propositional

open import Chi    atoms
open import Values atoms

infix  -1 finally-⇓ _■⟨_⟩ _■⟨_⟩⋆
infixr -2 step-≡⇓ step-⇓ _≡⟨⟩⟶_ modus-ponens-⇓

step-≡⇓ : ∀ e₁ {e₂ e₃} → e₂ ⇓ e₃ → e₁ ≡ e₂ → e₁ ⇓ e₃
step-≡⇓ _ e₂⇓e₃ refl = e₂⇓e₃

syntax step-≡⇓ e₁ e₂⇓e₃ e₁≡e₂ = e₁ ≡⟨ e₁≡e₂ ⟩⟶ e₂⇓e₃

_≡⟨⟩⟶_ : ∀ e₁ {e₂} → e₁ ⇓ e₂ → e₁ ⇓ e₂
_ ≡⟨⟩⟶ e₁⇓e₂ = e₁⇓e₂

mutual

  _■⟨_⟩ : ∀ e → Value e → e ⇓ e
  _ ■⟨ lambda x e ⟩ = lambda
  _ ■⟨ const c vs ⟩ = const (_ ■⟨ vs ⟩⋆)

  _■⟨_⟩⋆ : ∀ es → Values es → es ⇓⋆ es
  _ ■⟨ []     ⟩⋆ = []
  _ ■⟨ v ∷ vs ⟩⋆ = (_ ■⟨ v ⟩) ∷ (_ ■⟨ vs ⟩⋆)

finally-⇓ : (e₁ e₂ : Exp) → e₁ ⇓ e₂ → e₁ ⇓ e₂
finally-⇓ _ _ e₁⇓e₂ = e₁⇓e₂

syntax finally-⇓ e₁ e₂ e₁⇓e₂ = e₁ ⇓⟨ e₁⇓e₂ ⟩■ e₂

modus-ponens-⇓ : ∀ e {e′ v} → e′ ⇓ v → (e′ ⇓ v → e ⇓ v) → e ⇓ v
modus-ponens-⇓ _ x f = f x

syntax modus-ponens-⇓ e x f = e ⟶⟨ f ⟩ x

mutual

  trans-⇓ : ∀ {e₁ e₂ e₃} → e₁ ⇓ e₂ → e₂ ⇓ e₃ → e₁ ⇓ e₃
  trans-⇓ (apply p q r)  s          = apply p q (trans-⇓ r s)
  trans-⇓ (case p q r s) t          = case p q r (trans-⇓ s t)
  trans-⇓ (rec p)        q          = rec (trans-⇓ p q)
  trans-⇓ lambda         lambda     = lambda
  trans-⇓ (const ps)     (const qs) = const (trans-⇓⋆ ps qs)

  trans-⇓⋆ : ∀ {es₁ es₂ es₃} → es₁ ⇓⋆ es₂ → es₂ ⇓⋆ es₃ → es₁ ⇓⋆ es₃
  trans-⇓⋆ []       []       = []
  trans-⇓⋆ (p ∷ ps) (q ∷ qs) = trans-⇓ p q ∷ trans-⇓⋆ ps qs

step-⇓ : ∀ e₁ {e₂ e₃} → e₂ ⇓ e₃ → e₁ ⇓ e₂ → e₁ ⇓ e₃
step-⇓ _ e₂⇓e₃ e₁⇓e₂ = trans-⇓ e₁⇓e₂ e₂⇓e₃

syntax step-⇓ e₁ e₂⇓e₃ e₁⇓e₂ = e₁ ⇓⟨ e₁⇓e₂ ⟩ e₂⇓e₃
