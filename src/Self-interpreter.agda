------------------------------------------------------------------------
-- A self-interpreter (without correctness proof)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Self-interpreter where

open import Prelude hiding (const)

-- To simplify the development, let's work with actual natural numbers
-- as variables and constants (see
-- Atom.one-can-restrict-attention-to-χ-ℕ-atoms).

open import Atom

open import Chi            χ-ℕ-atoms
open import Constants      χ-ℕ-atoms
open import Free-variables χ-ℕ-atoms

open χ-atoms χ-ℕ-atoms

open import Combinators

-- Substitution.

internal-subst : Exp
internal-subst = lambda v-x (lambda v-new body)
  module Internal-subst where
  private
    rec-or-lambda = λ c →
      branch c (v-y ∷ v-e ∷ []) (
        case (equal-ℕ (var v-x) (var v-y)) (
          branch c-true [] (const c (var v-y ∷ var v-e ∷ [])) ∷
          branch c-false [] (
            const c (var v-y ∷ apply (var v-subst) (var v-e) ∷ [])) ∷
          []))

  branches =
    branch c-apply (v-e₁ ∷ v-e₂ ∷ []) (
      const c-apply (apply (var v-subst) (var v-e₁) ∷
                     apply (var v-subst) (var v-e₂) ∷ [])) ∷
    branch c-case (v-e ∷ v-bs ∷ []) (
      const c-case (
        apply (var v-subst) (var v-e) ∷
        apply (var v-subst) (var v-bs) ∷ [])) ∷
    rec-or-lambda c-rec ∷
    rec-or-lambda c-lambda ∷
    branch c-const (v-c ∷ v-es ∷ []) (
      const c-const (var v-c ∷ apply (var v-subst) (var v-es) ∷ [])) ∷
    branch c-var (v-y ∷ []) (
      case (equal-ℕ (var v-x) (var v-y)) (
        branch c-true [] (var v-new) ∷
        branch c-false [] (const c-var (var v-y ∷ [])) ∷ [])) ∷
    branch c-branch (v-c ∷ v-ys ∷ v-e ∷ []) (
      const c-branch (
        var v-c ∷
        var v-ys ∷
        case (member (var v-x) (var v-ys)) (
          branch c-true [] (var v-e) ∷
          branch c-false [] (apply (var v-subst) (var v-e)) ∷
          []) ∷ [])) ∷
    branch c-nil [] (const c-nil []) ∷
    branch c-cons (v-e ∷ v-es ∷ []) (
      const c-cons (apply (var v-subst) (var v-e) ∷
                    apply (var v-subst) (var v-es) ∷ [])) ∷
    []

  body = rec v-subst (lambda v-e (case (var v-e) branches))

-- Searches for a branch matching a given natural number.

internal-lookup : Exp
internal-lookup =
  lambda v-c (rec v-lookup (lambda v-bs (case (var v-bs) (
    branch c-cons (v-b ∷ v-bs ∷ []) (case (var v-b) (
      branch c-branch (v-c′ ∷ v-underscore ∷ v-underscore ∷ []) (
        case (equal-ℕ (var v-c) (var v-c′)) (
          branch c-false [] (apply (var v-lookup) (var v-bs)) ∷
          branch c-true [] (var v-b) ∷ [])) ∷ [])) ∷ []))))

-- Tries to apply multiple substitutions.

internal-substs : Exp
internal-substs =
  rec v-substs (lambda v-xs (lambda v-es (lambda v-e′ (
    case (var v-xs) (
      branch c-nil [] (case (var v-es) (
        branch c-nil [] (var v-e′) ∷ [])) ∷
      branch c-cons (v-x ∷ v-xs ∷ []) (case (var v-es) (
        branch c-cons (v-e ∷ v-es ∷ []) (
          apply (apply (apply internal-subst (var v-x)) (var v-e))
            (apply (apply (apply (var v-substs) (var v-xs))
               (var v-es)) (var v-e′))) ∷ [])) ∷ [])))))

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
