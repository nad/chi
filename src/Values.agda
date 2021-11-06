------------------------------------------------------------------------
-- Values
------------------------------------------------------------------------

open import Atom

module Values (atoms : χ-atoms) where

open import Equality.Propositional
open import Prelude hiding (const)

open import Chi atoms
open import Deterministic atoms

open χ-atoms atoms

-- Values.

mutual

  infixr 5 _∷_

  data Value : Exp → Type where
    lambda : ∀ x e → Value (lambda x e)
    const  : ∀ c {es} → Values es → Value (const c es)

  data Values : List Exp → Type where
    []  : Values []
    _∷_ : ∀ {e es} → Value e → Values es → Values (e ∷ es)

-- Constructor applications.

data Consts : Type where
  const : Const → List Consts → Consts

mutual

  data Constructor-application : Exp → Type where
    const : ∀ c {es} →
            Constructor-applications es →
            Constructor-application (const c es)

  data Constructor-applications : List Exp → Type where
    []  : Constructor-applications []
    _∷_ : ∀ {e es} →
          Constructor-application e → Constructor-applications es →
          Constructor-applications (e ∷ es)

-- Constructor applications are values.

mutual

  const→value : ∀ {e} → Constructor-application e → Value e
  const→value (const c cs) = const c (consts→values cs)

  consts→values : ∀ {es} → Constructor-applications es → Values es
  consts→values []       = []
  consts→values (c ∷ cs) = const→value c ∷ consts→values cs

-- The second argument of _⇓_ is always a Value.

mutual

  ⇓-Value : ∀ {e v} → e ⇓ v → Value v
  ⇓-Value (apply _ _ p)  = ⇓-Value p
  ⇓-Value (case _ _ _ p) = ⇓-Value p
  ⇓-Value (rec p)        = ⇓-Value p
  ⇓-Value lambda         = lambda _ _
  ⇓-Value (const ps)     = const _ (⇓⋆-Values ps)

  ⇓⋆-Values : ∀ {es vs} → es ⇓⋆ vs → Values vs
  ⇓⋆-Values []       = []
  ⇓⋆-Values (p ∷ ps) = ⇓-Value p ∷ ⇓⋆-Values ps

mutual

  values-compute-to-themselves : ∀ {v} → Value v → v ⇓ v
  values-compute-to-themselves (lambda _ _) = lambda
  values-compute-to-themselves (const _ ps) =
    const (values-compute-to-themselves⋆ ps)

  values-compute-to-themselves⋆ : ∀ {vs} → Values vs → vs ⇓⋆ vs
  values-compute-to-themselves⋆ []       = []
  values-compute-to-themselves⋆ (p ∷ ps) =
    values-compute-to-themselves p ∷ values-compute-to-themselves⋆ ps

values-only-compute-to-themselves :
  ∀ {v₁ v₂} → Value v₁ → v₁ ⇓ v₂ → v₁ ≡ v₂
values-only-compute-to-themselves p q =
  ⇓-deterministic (values-compute-to-themselves p) q

values-only-compute-to-themselves⋆ :
  ∀ {vs₁ vs₂} → Values vs₁ → vs₁ ⇓⋆ vs₂ → vs₁ ≡ vs₂
values-only-compute-to-themselves⋆ ps qs =
  ⇓⋆-deterministic (values-compute-to-themselves⋆ ps) qs
