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
import Erased.Cubical equality-with-paths as E
open import Finite-subset.Listed equality-with-paths as S
  using (Finite-subset-of)
open import Finite-subset.Listed.Membership.Erased equality-with-paths
  as SM using (_∉_)
open import Function-universe equality-with-J hiding (id; _∘_)
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

    countably-infinite : Name ≃ ℕ

  -- Atoms have decidable equality.

  _≟_ : Decidable-equality Name
  _≟_ = Bijection.decidable-equality-respects
          (from-equivalence $ inverse countably-infinite)
          Nat._≟_

  -- Membership test.

  member : (x : Name) (xs : List Name) → Dec (x ∈ xs)
  member x []       = no (λ ())
  member x (y ∷ xs) =
    case x ≟ y of λ where
      (yes x≡y) → yes (inj₁ x≡y)
      (no  x≢y) → case member x xs of ⊎-map
        (λ x∈xs → inj₂ x∈xs)
        (λ x∉xs → [ x≢y , x∉xs ])

  -- Conversions.

  name : ℕ → Name
  name = _≃_.from countably-infinite

  code : Name → ℕ
  code = _≃_.to countably-infinite

  -- The name function is injective.

  name-injective : Injective name
  name-injective = _≃_.injective (inverse countably-infinite)

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
      (λ {m} → E.Stable-Π (λ _ → E.Stable-¬)
         E.[ →-cong-→
               (name m SM.∈ ns                        ↝⟨ (λ ∈ns → ∣ name m , ∈ns
                                                                  , _≃_.right-inverse-of countably-infinite _
                                                                  ∣) ⟩
                ∥ (∃ λ n → n SM.∈ ns × code n ≡ m) ∥  ↔⟨ inverse SM.∈map≃ ⟩□
                m SM.∈ S.map code ns                  □)
               id
           ])
      (SM.fresh (S.map code ns))

  -- Name is a set.

  Name-set : Is-set Name
  Name-set = decidable⇒set _≟_

-- One implementation of atoms, using natural numbers.

ℕ-atoms : Atoms
Atoms.Name               ℕ-atoms = ℕ
Atoms.countably-infinite ℕ-atoms = Eq.id

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

-- The type of atoms is equivalent to the unit type (assuming
-- univalence).

Atoms≃⊤ : Univalence lzero → Atoms ≃ ⊤
Atoms≃⊤ univ =
  Atoms                           ↔⟨ eq ⟩
  (∃ λ (Name : Type) → Name ≃ ℕ)  ↔⟨ singleton-with-≃-↔-⊤ ext univ ⟩□
  ⊤                               □
  where
  open Atoms

  eq : Atoms ↔ ∃ λ (Name : Type) → Name ≃ ℕ
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

-- The χ-atoms type is equivalent to the unit type (assuming
-- univalence).

χ-atoms≃⊤ : Univalence lzero → χ-atoms ≃ ⊤
χ-atoms≃⊤ univ =
  χ-atoms        ↔⟨ eq ⟩
  Atoms × Atoms  ↝⟨ Atoms≃⊤ univ ×-cong Atoms≃⊤ univ ⟩
  ⊤ × ⊤          ↔⟨ ×-right-identity ⟩□
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
  Univalence lzero →
  ∀ {p} (P : χ-atoms → Type p) →
  ∀ a₁ a₂ → P a₁ → P a₂
invariant univ P a₁ a₂ = subst P (prop a₁ a₂)
  where
  prop : Is-proposition χ-atoms
  prop =
    mono₁ 0 $ _⇔_.from contractible⇔↔⊤ $ from-equivalence $
    χ-atoms≃⊤ univ

-- If a predicate holds for χ-ℕ-atoms, then it holds for any choice of
-- atoms (assuming univalence).

one-can-restrict-attention-to-χ-ℕ-atoms :
  Univalence lzero →
  ∀ {p} (P : χ-atoms → Type p) →
  P χ-ℕ-atoms → ∀ a → P a
one-can-restrict-attention-to-χ-ℕ-atoms univ P p a =
  invariant univ P χ-ℕ-atoms a p

-- If ¬ P χ-ℕ-atoms holds, then ¬ P a holds for any choice of atoms a.

one-can-restrict-attention-to-χ-ℕ-atoms-for-¬ :
  ∀ {p} (P : χ-atoms → Type p) →
  ¬ P χ-ℕ-atoms → ∀ a → ¬ P a
one-can-restrict-attention-to-χ-ℕ-atoms-for-¬ P p a =
  E.Stable-¬
    E.[ one-can-restrict-attention-to-χ-ℕ-atoms univ (¬_ ∘ P) p a ]
