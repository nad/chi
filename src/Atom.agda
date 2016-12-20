------------------------------------------------------------------------
-- Atoms
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Atom where

open import Bag-equivalence
open import Equality.Propositional
open import Interval using (ext)
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J as Bijection using (_↔_)
open import Equality.Decidable-UIP equality-with-J
open import Equivalence equality-with-J as Eq using (_≃_)
open import Function-universe equality-with-J
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import Injection equality-with-J using (Injective)
import Nat equality-with-J as Nat
open import Univalence-axiom equality-with-J

-- Atoms.

record Atoms : Set₁ where
  field
    -- The type of atoms.

    Name : Set

    -- The type must be countably infinite.

    countably-infinite : Name ↔ ℕ

  -- Atoms have decidable equality.

  _≟_ : Decidable-equality Name
  _≟_ = Bijection.decidable-equality-respects
          (inverse countably-infinite) Nat._≟_

  -- Membership test.

  member : (x : Name) (xs : List Name) → Dec (x ∈ xs)
  member x []       = no (λ ())
  member x (y ∷ xs) with x ≟ y
  ... | yes x≡y = yes (inj₁ x≡y)
  ... | no  x≢y with member x xs
  ...   | yes x∈xs = yes (inj₂ x∈xs)
  ...   | no  x∉xs = no [ x≢y , x∉xs ]

  -- Conversions.

  name : ℕ → Name
  name = _↔_.from countably-infinite

  code : Name → ℕ
  code = _↔_.to countably-infinite

  -- The name function is injective.

  name-injective : Injective name
  name-injective = _↔_.injective (inverse countably-infinite)

  -- Distinct natural numbers are mapped to distinct names.

  distinct-codes→distinct-names : ∀ {m n} → m ≢ n → name m ≢ name n
  distinct-codes→distinct-names {m} {n} m≢n =
    name m ≡ name n  ↝⟨ name-injective ⟩
    m ≡ n            ↝⟨ m≢n ⟩□
    ⊥                □

  -- Name is a set.

  Name-set : Is-set Name
  Name-set = decidable⇒set _≟_

-- One implementation of atoms, using natural numbers.

ℕ-atoms : Atoms
Atoms.Name               ℕ-atoms = ℕ
Atoms.countably-infinite ℕ-atoms = Bijection.id

-- Two sets of atoms, one for constants and one for variables.

record χ-atoms : Set₁ where
  field
    const-atoms var-atoms : Atoms

  module C = Atoms const-atoms renaming (Name to Const)
  module V = Atoms var-atoms   renaming (Name to Var)

  open C public using (Const)
  open V public using (Var)

-- One implementation of χ-atoms, using natural numbers.

χ-ℕ-atoms : χ-atoms
χ-atoms.const-atoms χ-ℕ-atoms = ℕ-atoms
χ-atoms.var-atoms   χ-ℕ-atoms = ℕ-atoms

-- The type of atoms is isomorphic to the unit type (assuming
-- univalence).

Atoms↔⊤ :
  Univalence (# 0) →
  Atoms ↔ ⊤
Atoms↔⊤ univ =
  Atoms                          ↝⟨ eq ⟩
  (∃ λ (Name : Set) → Name ↔ ℕ)  ↝⟨ ∃-cong (λ _ → Eq.↔↔≃′ ext ℕ-set) ⟩
  (∃ λ (Name : Set) → Name ≃ ℕ)  ↝⟨ singleton-with-≃-↔-⊤ ext univ ⟩□
  ⊤                              □
  where
  open Atoms

  eq : Atoms ↔ ∃ λ (Name : Set) → Name ↔ ℕ
  eq = record
    { surjection = record
      { logical-equivalence = record
        { to   = λ a → Name a , countably-infinite a
        ; from = uncurry λ N c →
                   record { Name = N; countably-infinite = c }
        }
      ; right-inverse-of = λ _ → refl
      }
    ; left-inverse-of = λ _ → refl
    }

-- The χ-atoms type is isomorphic to the unit type (assuming
-- univalence).

χ-atoms↔⊤ :
  Univalence (# 0) →
  χ-atoms ↔ ⊤
χ-atoms↔⊤ univ =
  χ-atoms        ↝⟨ eq ⟩
  Atoms × Atoms  ↝⟨ Atoms↔⊤ univ ×-cong Atoms↔⊤ univ ⟩
  ⊤ × ⊤          ↝⟨ ×-right-identity ⟩□
  ⊤              □
  where
  open χ-atoms

  eq : χ-atoms ↔ Atoms × Atoms
  eq = record
    { surjection = record
      { logical-equivalence = record
        { to   = λ a → const-atoms a , var-atoms a
        ; from = uncurry λ c v →
                   record { const-atoms = c; var-atoms = v }
        }
      ; right-inverse-of = λ _ → refl
      }
    ; left-inverse-of = λ _ → refl
    }

-- If a property holds for one choice of atoms, then it holds for any
-- other choice of atoms (assuming univalence).

invariant :
  ∀ {p} →
  Univalence (# 0) →
  (P : χ-atoms → Set p) →
  ∀ a₁ a₂ → P a₁ → P a₂
invariant univ P a₁ a₂ =
  subst P (_⇔_.to propositional⇔irrelevant
             (mono₁ 0 $ _⇔_.from contractible⇔⊤↔ $ inverse $
                χ-atoms↔⊤ univ)
             a₁ a₂)

-- If a property holds for χ-ℕ-atoms, then it holds for any choice of
-- atoms (assuming univalence).

one-can-restrict-attention-to-χ-ℕ-atoms :
  ∀ {p} →
  Univalence (# 0) →
  (P : χ-atoms → Set p) →
  P χ-ℕ-atoms → ∀ a → P a
one-can-restrict-attention-to-χ-ℕ-atoms univ P p a =
  invariant univ P χ-ℕ-atoms a p
