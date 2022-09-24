------------------------------------------------------------------------
-- A definition of the size of an operational semantics derivation,
-- along with some properties
------------------------------------------------------------------------

open import Atom

module Derivation-size (atoms : χ-atoms) where

open import Equality.Propositional
open import Prelude hiding (const)
open import Tactic.By.Propositional

open import Nat equality-with-J as Nat
  using (_≤_; _∎≤; step-≡≤; step-≤; finally-≤)

open import Chi           atoms
open import Compatibility atoms
open import Deterministic atoms
open import Propositional atoms
open import Reasoning     atoms
open import Values        atoms

private variable
  e v v₁ v₂ : Exp
  es vs     : List Exp
  q         : e ⇓ v
  qs        : es ⇓⋆ vs

------------------------------------------------------------------------
-- The size of an operational semantics derivation

mutual

  -- The size of a derivation.

  size : e ⇓ v → ℕ
  size (apply p q r)  = 1 + size p + size q + size r
  size (case p _ _ q) = 1 + size p + size q
  size (rec p)        = 1 + size p
  size lambda         = 0
  size (const ps)     = 1 + size⋆ ps

  size⋆ : es ⇓⋆ vs → ℕ
  size⋆ []       = 0
  size⋆ (p ∷ ps) = size p + size⋆ ps

------------------------------------------------------------------------
-- A uniqueness lemma

-- Two derivations for a given starting expression always have the
-- same size.

size-unique : (p : e ⇓ v₁) (q : e ⇓ v₂) → size p ≡ size q
size-unique {e = e} p q = subst
  (λ v → (q : e ⇓ v) → size p ≡ size q)
  (⇓-deterministic p q)
  (λ q → cong size (⇓-propositional p q))
  q

------------------------------------------------------------------------
-- Lemmas related to the Value predicate

mutual

  -- If p has type Value v, then the proof
  -- values-compute-to-themselves p has minimal size among all proofs
  -- of type e ⇓ v, for any expression e.

  size-values-compute-to-themselves :
    (p : Value v) (q : e ⇓ v) →
    size (values-compute-to-themselves p) ≤ size q
  size-values-compute-to-themselves (lambda x e) q =
    0       ≤⟨ Nat.zero≤ _ ⟩∎
    size q  ∎≤
  size-values-compute-to-themselves p (apply q₁ q₂ q₃) =
    size (values-compute-to-themselves p)  ≤⟨ size-values-compute-to-themselves p q₃ ⟩
    size q₃                                ≤⟨ Nat.m≤n+m _ _ ⟩∎
    1 + size q₁ + size q₂ + size q₃        ∎≤
  size-values-compute-to-themselves p (case q₁ _ _ q₂) =
    size (values-compute-to-themselves p)  ≤⟨ size-values-compute-to-themselves p q₂ ⟩
    size q₂                                ≤⟨ Nat.m≤n+m _ _ ⟩∎
    1 + size q₁ + size q₂                  ∎≤
  size-values-compute-to-themselves p (rec q) =
    size (values-compute-to-themselves p)  ≤⟨ size-values-compute-to-themselves p q ⟩
    size q                                 ≤⟨ Nat.m≤n+m _ _ ⟩∎
    1 + size q                             ∎≤
  size-values-compute-to-themselves (const c vs) (const qs) =
    1 + size⋆ (values-compute-to-themselves⋆ vs)  ≤⟨ Nat.suc≤suc $ size⋆-values-compute-to-themselves⋆ vs qs ⟩∎
    1 + size⋆ qs                                  ∎≤

  -- If ps has type Values vs, then the proof
  -- values-compute-to-themselves⋆ ps has minimal size among all
  -- proofs of type es ⇓⋆ vs, for any list of expressions es.

  size⋆-values-compute-to-themselves⋆ :
    (ps : Values vs) (qs : es ⇓⋆ vs) →
    size⋆ (values-compute-to-themselves⋆ ps) ≤ size⋆ qs
  size⋆-values-compute-to-themselves⋆ [] [] =
    0  ∎≤
  size⋆-values-compute-to-themselves⋆ (p ∷ ps) (q ∷ qs) =
    size (values-compute-to-themselves p) +
    size⋆ (values-compute-to-themselves⋆ ps)  ≤⟨ size-values-compute-to-themselves p q
                                                   Nat.+-mono
                                                 size⋆-values-compute-to-themselves⋆ ps qs ⟩∎
    size q + size⋆ qs                         ∎≤

-- A corollary of size-values-compute-to-themselves.

size-values-compute-to-themselves-⇓-Value :
  (p : e ⇓ v) →
  size (values-compute-to-themselves (⇓-Value p)) ≤ size p
size-values-compute-to-themselves-⇓-Value p =
  size-values-compute-to-themselves (⇓-Value p) p

-- If p has type v₁ ⇓ v₂, where v₁ is a value, then the size of p is
-- equal to the size of values-compute-to-themselves (⇓-Value p).

size-values-compute-to-themselves-⇓-Value-Value :
  Value v₁ →
  (p : v₁ ⇓ v₂) →
  size (values-compute-to-themselves (⇓-Value p)) ≡ size p
size-values-compute-to-themselves-⇓-Value-Value {v₁ = v₁} v p = subst
  (λ v₂ → (p : v₁ ⇓ v₂) →
          size (values-compute-to-themselves (⇓-Value p)) ≡ size p)
  (values-only-compute-to-themselves v p)
  (λ p →
     size (values-compute-to-themselves (⇓-Value p))  ≡⟨ cong size $
                                                         ⇓-propositional (values-compute-to-themselves (⇓-Value p)) p ⟩∎
     size p                                           ∎)
  p

------------------------------------------------------------------------
-- Lemmas related to some reasoning and compatibility combinators

-- The size of e ≡⟨ p ⟩⟶ q is the size of q.

size-≡⟨⟩⟶ : ∀ p → size (e ≡⟨ p ⟩⟶ q) ≡ size q
size-≡⟨⟩⟶ refl = refl

mutual

  -- The size of trans-⇓ p q is the size of p.

  size-trans-⇓ : (p : e ⇓ v) → size (trans-⇓ p q) ≡ size p
  size-trans-⇓ {q = s} (apply p q r) =
    1 + size p + size q + ⟨ size (trans-⇓ r s) ⟩  ≡⟨ ⟨by⟩ (size-trans-⇓ r) ⟩∎
    1 + size p + size q + size r                  ∎
  size-trans-⇓ {q = r} (case p _ _ q) =
    1 + size p + ⟨ size (trans-⇓ q r) ⟩  ≡⟨ ⟨by⟩ (size-trans-⇓ q) ⟩∎
    1 + size p + size q                  ∎
  size-trans-⇓ {q = q} (rec p) =
    1 + ⟨ size (trans-⇓ p q) ⟩  ≡⟨ ⟨by⟩ (size-trans-⇓ p) ⟩∎
    1 + size p                  ∎
  size-trans-⇓ {q = lambda} lambda =
    0  ∎
  size-trans-⇓ {q = const qs} (const ps) =
    1 + ⟨ size⋆ (trans-⇓⋆ ps qs) ⟩  ≡⟨ ⟨by⟩ (size⋆-trans-⇓⋆ ps) ⟩∎
    1 + size⋆ ps                    ∎

  -- The size of trans-⇓⋆ ps qs is the size of ps.

  size⋆-trans-⇓⋆ : (ps : es ⇓⋆ vs) → size⋆ (trans-⇓⋆ ps qs) ≡ size⋆ ps
  size⋆-trans-⇓⋆ {qs = []} [] =
    0  ∎
  size⋆-trans-⇓⋆ {qs = q ∷ qs} (p ∷ ps) =
    size (trans-⇓ p q) + size⋆ (trans-⇓⋆ ps qs)  ≡⟨ cong₂ _+_ (size-trans-⇓ p) (size⋆-trans-⇓⋆ ps) ⟩∎
    size p + size⋆ ps                            ∎

mutual

  -- The size of []⇓⁻¹ c p q is at most size q.

  size-[]⇓⁻¹ :
    (c : Context) {p : e ⇓ v₁} {q : c [ e ] ⇓ v₂} →
    size ([]⇓⁻¹ c p q) ≤ size q
  size-[]⇓⁻¹ {v₁ = v₁} {v₂ = v₂} ∙ {p = p} {q = q} =
    size (v₁  ≡⟨ ⇓-deterministic p q ⟩⟶
          v₂  ■⟨ ⇓-Value q ⟩)            ≡⟨ size-≡⟨⟩⟶ (⇓-deterministic p q) ⟩≤

    size (v₂  ■⟨ ⇓-Value q ⟩)            ≤⟨ size-values-compute-to-themselves-⇓-Value q ⟩∎

    size q                               ∎≤
  size-[]⇓⁻¹ (apply← c) {p = p} {q = apply q r s} =
    1 + size ([]⇓⁻¹ c p q) + size r + size s  ≤⟨ Nat.suc≤suc $ size-[]⇓⁻¹ c Nat.+-mono Nat.≤-refl Nat.+-mono Nat.≤-refl ⟩∎
    1 + size q + size r + size s              ∎≤
  size-[]⇓⁻¹ (apply→ c) {p = p} {q = apply q r s} =
    1 + size q + size ([]⇓⁻¹ c p r) + size s  ≤⟨ Nat.suc≤suc $ Nat.≤-refl {n = size q} Nat.+-mono size-[]⇓⁻¹ c Nat.+-mono Nat.≤-refl ⟩∎
    1 + size q + size r + size s              ∎≤
  size-[]⇓⁻¹ (const c) {p = p} {q = const qs} =
    1 + size⋆ ([]⇓⋆⁻¹ c p qs)  ≤⟨ Nat.suc≤suc $ size-[]⇓⋆⁻¹ c ⟩∎
    1 + size⋆ qs               ∎≤
  size-[]⇓⁻¹ (case c) {p = p} {q = case q r s t} =
    1 + size ([]⇓⁻¹ c p q) + size t  ≤⟨ Nat.suc≤suc $ size-[]⇓⁻¹ c Nat.+-mono Nat.≤-refl ⟩∎
    1 + size q + size t              ∎≤

  size-[]⇓⋆⁻¹ :
    (c : Context⋆) {p : e ⇓ v} {q : c [ e ]⋆ ⇓⋆ vs} →
    size⋆ ([]⇓⋆⁻¹ c p q) ≤ size⋆ q
  size-[]⇓⋆⁻¹ (here c) {p = p} {q = q ∷ qs} =
    size ([]⇓⁻¹ c p q) + size⋆ qs  ≤⟨ size-[]⇓⁻¹ c Nat.+-mono Nat.≤-refl ⟩∎
    size q + size⋆ qs              ∎≤
  size-[]⇓⋆⁻¹ (there c) {p = p} {q = q ∷ qs} =
    size q + size⋆ ([]⇓⋆⁻¹ c p qs)  ≤⟨ Nat.≤-refl Nat.+-mono size-[]⇓⋆⁻¹ c ⟩∎
    size q + size⋆ qs               ∎≤

mutual

  -- If p has type e ⇓ v₁ and e is a value, then the size of
  -- []⇓⁻¹ c p q is the size of q.

  size-[]⇓⁻¹-Value :
    Value e → (c : Context) {p : e ⇓ v₁} {q : c [ e ] ⇓ v₂} →
    size ([]⇓⁻¹ c p q) ≡ size q
  size-[]⇓⁻¹-Value {v₁ = v₁} {v₂ = v₂} e-value ∙ {p = p} {q = q} =
    size (v₁  ≡⟨ ⇓-deterministic p q ⟩⟶
          v₂  ■⟨ ⇓-Value q ⟩)            ≡⟨ size-≡⟨⟩⟶ (⇓-deterministic p q) ⟩

    size (v₂  ■⟨ ⇓-Value q ⟩)            ≡⟨ size-values-compute-to-themselves-⇓-Value-Value e-value q ⟩∎

    size q                               ∎
  size-[]⇓⁻¹-Value e-value (apply← c) {p = p} {q = apply q r s} =
    1 + ⟨ size ([]⇓⁻¹ c p q) ⟩ + size r + size s  ≡⟨ ⟨by⟩ (size-[]⇓⁻¹-Value e-value c) ⟩∎
    1 + size q + size r + size s                  ∎
  size-[]⇓⁻¹-Value e-value (apply→ c) {p = p} {q = apply q r s} =
    1 + size q + ⟨ size ([]⇓⁻¹ c p r) ⟩ + size s  ≡⟨ ⟨by⟩ (size-[]⇓⁻¹-Value e-value c) ⟩∎
    1 + size q + size r + size s                  ∎
  size-[]⇓⁻¹-Value e-value (const c) {p = p} {q = const qs} =
    1 + ⟨ size⋆ ([]⇓⋆⁻¹ c p qs) ⟩  ≡⟨ ⟨by⟩ (size-[]⇓⋆⁻¹-Value e-value c) ⟩∎
    1 + size⋆ qs                   ∎
  size-[]⇓⁻¹-Value e-value (case c) {p = p} {q = case q r s t} =
    1 + ⟨ size ([]⇓⁻¹ c p q) ⟩ + size t  ≡⟨ ⟨by⟩ (size-[]⇓⁻¹-Value e-value c) ⟩∎
    1 + size q + size t                  ∎

  size-[]⇓⋆⁻¹-Value :
    Value e → (c : Context⋆) {p : e ⇓ v} {q : c [ e ]⋆ ⇓⋆ vs} →
    size⋆ ([]⇓⋆⁻¹ c p q) ≡ size⋆ q
  size-[]⇓⋆⁻¹-Value e-value (here c) {p = p} {q = q ∷ qs} =
    ⟨ size ([]⇓⁻¹ c p q) ⟩ + size⋆ qs  ≡⟨ ⟨by⟩ (size-[]⇓⁻¹-Value e-value c) ⟩∎
    size q + size⋆ qs                  ∎
  size-[]⇓⋆⁻¹-Value e-value (there c) {p = p} {q = q ∷ qs} =
    size q + ⟨ size⋆ ([]⇓⋆⁻¹ c p qs) ⟩  ≡⟨ ⟨by⟩ (size-[]⇓⋆⁻¹-Value e-value c) ⟩∎
    size q + size⋆ qs                   ∎
