------------------------------------------------------------------------
-- A self-interpreter (without correctness proof)
------------------------------------------------------------------------

module Self-interpreter where

open import Prelude hiding (const)

-- To simplify the development, let's work with actual natural numbers
-- as variables and constants (see
-- Atom.one-can-restrict-attention-to-χ-ℕ-atoms).

open import Atom

open import Chi            χ-ℕ-atoms
open import Constants      χ-ℕ-atoms
open import Free-variables χ-ℕ-atoms

open import Combinators
open import Internal-lookup
open import Internal-substitution

-- A map function. The application of map to the function is done at
-- the meta-level in order to simplify proofs.

map : Exp → Exp
map f = rec v-map (lambda v-xs (case (var v-xs) branches))
  module Map where
  branches =
    branch c-nil [] (const c-nil []) ∷
    branch c-cons (v-x ∷ v-xs ∷ []) (
      const c-cons (apply f (var v-x) ∷
                    apply (var v-map) (var v-xs) ∷
                    [])) ∷
    []

-- The self-interpreter.

eval : Exp
eval =
  rec v-eval (lambda v-p (case (var v-p) branches))
  module Eval where
  apply-branch =
    branch c-lambda (v-x ∷ v-e ∷ []) (
      apply (var v-eval) (
        apply (apply (apply internal-subst (var v-x))
                 (apply (var v-eval) (var v-e₂)))
          (var v-e))) ∷
    []

  case-body₂ =
    case (apply (apply internal-lookup (var v-c)) (var v-bs)) (
      branch c-branch (v-underscore ∷ v-xs ∷ v-e ∷ []) (
        apply (var v-eval) (
          apply (apply (apply internal-substs (var v-xs))
            (var v-es)) (var v-e))) ∷
      [])

  case-body₁ =
    case (apply (var v-eval) (var v-e)) (
      branch c-const (v-c ∷ v-es ∷ []) case-body₂ ∷
      [])

  branches =
    branch c-apply (v-e₁ ∷ v-e₂ ∷ []) (
      case (apply (var v-eval) (var v-e₁)) apply-branch) ∷
    branch c-case (v-e ∷ v-bs ∷ []) case-body₁ ∷
    branch c-rec (v-x ∷ v-e ∷ []) (
      apply (var v-eval) (
        apply (apply (apply internal-subst (var v-x))
                 (const c-rec (var v-x ∷ var v-e ∷ [])))
          (var v-e))) ∷
    branch c-lambda (v-x ∷ v-e ∷ []) (
      const c-lambda (var v-x ∷ var v-e ∷ [])) ∷
    branch c-const (v-c ∷ v-es ∷ []) (
      const c-const (var v-c ∷
                     apply (map (var v-eval)) (var v-es) ∷
                     [])) ∷
    []

eval-closed : Closed eval
eval-closed = from-⊎ (closed? eval)
