------------------------------------------------------------------------
-- Atoms
------------------------------------------------------------------------

module Atom where

open import Equality.Propositional.Cubical
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bag-equivalence equality-with-J
open import Bijection equality-with-J as Bijection using (_↔_)
open import Equality.Decidable-UIP equality-with-J
open import Equality.Path.Isomorphisms.Univalence equality-with-paths
open import Equivalence equality-with-J as Eq using (_≃_)
open import Finite-subset.Listed equality-with-paths as S
  using (Finite-subset-of; _∉_)
open import Function-universe equality-with-J hiding (id)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional equality-with-paths
  using (∥_∥; ∣_∣)
open import Injection equality-with-J using (Injective)
import Nat equality-with-J as Nat
open import Univalence-axiom equality-with-J

-- Atoms.

record Atoms : Type₁ where
  field
    -- The type of atoms.

    Name : Type

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

  -- One can always find a name that is distinct from the names in a
  -- given finite set of names.

  fresh :
    (ns : Finite-subset-of Name) →
    ∃ λ (n : Name) → n ∉ ns
  fresh ns =
    Σ-map name
      (λ {m} →
         →-cong-→
           (name m S.∈ ns                        ↝⟨ (λ ∈ns → ∣ name m , ∈ns
                                                             , _↔_.right-inverse-of countably-infinite _
                                                             ∣) ⟩
            ∥ (∃ λ n → n S.∈ ns × code n ≡ m) ∥  ↔⟨ inverse S.∈map≃ ⟩□
            m S.∈ S.map code ns                  □)
           id)
      (S.fresh (S.map code ns))

  -- Name is a set.

  Name-set : Is-set Name
  Name-set = decidable⇒set _≟_

-- One implementation of atoms, using natural numbers.

ℕ-atoms : Atoms
Atoms.Name               ℕ-atoms = ℕ
Atoms.countably-infinite ℕ-atoms = Bijection.id

-- Two sets of atoms, one for constants and one for variables.

record χ-atoms : Type₁ where
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

-- The type of atoms is isomorphic to the unit type.

Atoms↔⊤ : Atoms ↔ ⊤
Atoms↔⊤ =
  Atoms                           ↝⟨ eq ⟩
  (∃ λ (Name : Type) → Name ↔ ℕ)  ↝⟨ ∃-cong (λ _ → Eq.↔↔≃′ ext ℕ-set) ⟩
  (∃ λ (Name : Type) → Name ≃ ℕ)  ↝⟨ singleton-with-≃-↔-⊤ ext univ ⟩□
  ⊤                               □
  where
  open Atoms

  eq : Atoms ↔ ∃ λ (Name : Type) → Name ↔ ℕ
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

-- The χ-atoms type is isomorphic to the unit type.

χ-atoms↔⊤ : χ-atoms ↔ ⊤
χ-atoms↔⊤ =
  χ-atoms        ↝⟨ eq ⟩
  Atoms × Atoms  ↝⟨ Atoms↔⊤ ×-cong Atoms↔⊤ ⟩
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
-- other choice of atoms.

invariant :
  ∀ {p} (P : χ-atoms → Type p) →
  ∀ a₁ a₂ → P a₁ → P a₂
invariant P a₁ a₂ =
  subst P (mono₁ 0 (_⇔_.from contractible⇔↔⊤ χ-atoms↔⊤) a₁ a₂)

-- If a property holds for χ-ℕ-atoms, then it holds for any choice of
-- atoms.

one-can-restrict-attention-to-χ-ℕ-atoms :
  ∀ {p} (P : χ-atoms → Type p) →
  P χ-ℕ-atoms → ∀ a → P a
one-can-restrict-attention-to-χ-ℕ-atoms P p a =
  invariant P χ-ℕ-atoms a p
