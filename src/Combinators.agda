------------------------------------------------------------------------
-- Some simple χ program combinators
------------------------------------------------------------------------

module Combinators where

open import Equality.Propositional
open import Prelude hiding (if_then_else_; not; const)

-- To simplify the development, let's work with actual natural numbers
-- as variables and constants (see
-- Atom.one-can-restrict-attention-to-χ-ℕ-atoms).

open import Atom

open import Chi            χ-ℕ-atoms
open import Coding         χ-ℕ-atoms
open import Constants      χ-ℕ-atoms
open import Free-variables χ-ℕ-atoms
open import Termination    χ-ℕ-atoms

open χ-atoms χ-ℕ-atoms

-- If-then-else.

infix 5 if_then_else_

if_then_else_ : Exp → Exp → Exp → Exp
if c then t else f =
  case c (branch c-true  [] t ∷
          branch c-false [] f ∷
          [])

if-then-else-closed :
  ∀ {xs c t f} →
  Closed′ xs c → Closed′ xs t → Closed′ xs f →
  Closed′ xs (if c then t else f)
if-then-else-closed c-cl t-cl f-cl =
  Closed′-closed-under-case
    c-cl
    λ where
      (inj₁ refl)        → t-cl
      (inj₂ (inj₁ refl)) → f-cl
      (inj₂ (inj₂ ()))

-- Negation of booleans.

not : Exp → Exp
not e = case e branches
  module Not where
  branches =
    branch c-true  [] (const c-false []) ∷
    branch c-false [] (const c-true  []) ∷
    []

not-closed : ∀ {xs e} → Closed′ xs e → Closed′ xs (not e)
not-closed {xs} {e} cl-e =
  Closed′-closed-under-case
    cl-e
    (from-⊎ (closed′?-B⋆ (Not.branches e) xs))

not⟶ : ∀ b → not (code b) ⟶ code (Prelude.not b)
not⟶ true  = case (const []) here [] (const [])
not⟶ false = case (const []) (there (λ ()) here) [] (const [])

-- A non-terminating expression.

loop : Exp
loop = rec v-x (var v-x)

loop-closed : Closed loop
loop-closed =
  Closed′-closed-under-rec $
  Closed′-closed-under-var (inj₁ refl)

¬loop⟶ : ¬ Terminates loop
¬loop⟶ (_ , p) = lemma p
  where
  lemma : ∀ {w} → ¬ loop ⟶ w
  lemma (rec p) with v-x V.≟ v-x
  ... | no  x≢x = x≢x refl
  ... | yes _   = lemma p
