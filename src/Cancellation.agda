------------------------------------------------------------------------
-- Some cancellation lemmas
------------------------------------------------------------------------

open import Atom

module Cancellation (atoms : χ-atoms) where

open import Equality.Propositional
open import Prelude hiding (const)

open import Chi atoms

cancel-const :
  ∀ {c₁ c₂ es₁ es₂} →
  Exp.const c₁ es₁ ≡ const c₂ es₂ →
  c₁ ≡ c₂ × es₁ ≡ es₂
cancel-const refl = refl , refl

cancel-lambda :
  ∀ {x₁ x₂ e₁ e₂} →
  Exp.lambda x₁ e₁ ≡ lambda x₂ e₂ →
  x₁ ≡ x₂ × e₁ ≡ e₂
cancel-lambda refl = refl , refl

cancel-rec :
  ∀ {x₁ x₂ e₁ e₂} →
  Exp.rec x₁ e₁ ≡ rec x₂ e₂ →
  x₁ ≡ x₂ × e₁ ≡ e₂
cancel-rec refl = refl , refl

cancel-apply :
  ∀ {e₁₁ e₁₂ e₂₁ e₂₂} →
  Exp.apply e₁₁ e₂₁ ≡ apply e₁₂ e₂₂ →
  e₁₁ ≡ e₁₂ × e₂₁ ≡ e₂₂
cancel-apply refl = refl , refl

cancel-case :
  ∀ {e₁ e₂ bs₁ bs₂} →
  Exp.case e₁ bs₁ ≡ case e₂ bs₂ →
  e₁ ≡ e₂ × bs₁ ≡ bs₂
cancel-case refl = refl , refl

cancel-var :
  ∀ {x₁ x₂} →
  Exp.var x₁ ≡ var x₂ → x₁ ≡ x₂
cancel-var refl = refl

cancel-branch :
  ∀ {c₁ c₂ xs₁ xs₂ e₁ e₂} →
  Br.branch c₁ xs₁ e₁ ≡ branch c₂ xs₂ e₂ →
  c₁ ≡ c₂ × xs₁ ≡ xs₂ × e₁ ≡ e₂
cancel-branch refl = refl , refl , refl
