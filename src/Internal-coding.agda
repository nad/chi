------------------------------------------------------------------------
-- Internal coding
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

module Internal-coding where

open import Equality.Propositional
open import Prelude hiding (const)
open import Tactic.By.Propositional

-- To simplify the development, let's work with actual natural numbers
-- as variables and constants (see
-- Atom.one-can-restrict-attention-to-χ-ℕ-atoms).

open import Atom

open import Chi            χ-ℕ-atoms
open import Coding         χ-ℕ-atoms
open import Constants      χ-ℕ-atoms
open import Free-variables χ-ℕ-atoms
open import Reasoning      χ-ℕ-atoms

open χ-atoms χ-ℕ-atoms

import Coding.Instances.Nat

abstract

  -- Some auxiliary definitions.

  private

    cd : Var → Exp
    cd x = apply (var v-internal-code) (var x)

    nullary-branch : Const → Br
    nullary-branch c =
      branch c [] (
        const c-const (⌜ c ⌝ ∷
          ⌜ [] ⦂ List Exp ⌝ ∷ []))

    unary-branch : Const → Br
    unary-branch c =
      branch c (v-x ∷ []) (
        const c-const (⌜ c ⌝ ∷
          const c-cons (cd v-x ∷
            ⌜ [] ⦂ List Exp ⌝ ∷ []) ∷ []))

    binary-branch : Const → Br
    binary-branch c =
      branch c (v-x ∷ v-y ∷ []) (
        const c-const (⌜ c ⌝ ∷
          const c-cons (cd v-x ∷
            const c-cons (cd v-y ∷
              ⌜ [] ⦂ List Exp ⌝ ∷ []) ∷ []) ∷ []))

    trinary-branch : Const → Br
    trinary-branch c =
      branch c (v-x ∷ v-y ∷ v-z ∷ []) (
        const c-const (⌜ c ⌝ ∷
          const c-cons (cd v-x ∷
            const c-cons (cd v-y ∷
              const c-cons (cd v-z ∷
                ⌜ [] ⦂ List Exp ⌝ ∷ []) ∷ []) ∷ []) ∷ []))

    branches : List Br
    branches =
      nullary-branch c-zero ∷
      unary-branch c-suc ∷
      nullary-branch c-nil ∷
      binary-branch c-cons ∷
      binary-branch c-apply ∷
      binary-branch c-lambda ∷
      binary-branch c-case ∷
      binary-branch c-rec ∷
      unary-branch c-var ∷
      binary-branch c-const ∷
      trinary-branch c-branch ∷
      []

  -- Internal coding.

  internal-code : Exp
  internal-code =
    rec v-internal-code (lambda v-p (case (var v-p) branches))

  internal-code-closed : Closed internal-code
  internal-code-closed = from-⊎ (closed? internal-code)

  -- The internal coder encodes natural numbers correctly.

  internal-code-correct-ℕ :
    (n : ℕ) → apply internal-code ⌜ n ⌝ ⇓ ⌜ ⌜ n ⌝ ⦂ Exp ⌝
  internal-code-correct-ℕ n =
    apply internal-code ⌜ n ⌝  ⟶⟨ apply (rec lambda) (rep⇓rep n) ⟩
    case ⌜ n ⌝ branches′       ⇓⟨ lemma n ⟩■
    ⌜ ⌜ n ⌝ ⦂ Exp ⌝
    where
    branches′ : List Br
    branches′ = branches [ v-internal-code ← internal-code ]B⋆

    lemma : (n : ℕ) → case ⌜ n ⌝ branches′ ⇓ ⌜ ⌜ n ⌝ ⦂ Exp ⌝
    lemma zero =
      case ⌜ zero ⌝ branches′  ⇓⟨ case (rep⇓rep zero) here [] (rep⇓rep (⌜ zero ⌝ ⦂ Exp)) ⟩■
      ⌜ ⌜ zero ⌝ ⦂ Exp ⌝

    lemma (suc n) =
      case ⌜ suc n ⌝ branches′                        ⟶⟨ case (rep⇓rep (suc n)) (there (λ ()) here) (∷ []) ⟩

      const c-const (⌜ c-suc ⌝ ∷
        const c-cons (apply internal-code ⌜ n ⌝ ∷
          ⌜ [] ⦂ List Exp ⌝ ∷ []) ∷ [])               ⇓⟨ const (rep⇓rep c-suc ∷
                                                           const (internal-code-correct-ℕ n ∷ rep⇓rep ([] ⦂ List Exp) ∷ []) ∷ []) ⟩■
      ⌜ ⌜ suc n ⌝ ⦂ Exp ⌝

  -- The internal coder encodes lists of variables correctly.

  internal-code-correct-Var⋆ :
    (xs : List Var) →
    apply internal-code ⌜ xs ⌝ ⇓ ⌜ ⌜ xs ⌝ ⦂ Exp ⌝
  internal-code-correct-Var⋆ xs =
    apply internal-code ⌜ xs ⌝  ⟶⟨ apply (rec lambda) (rep⇓rep xs) ⟩
    case ⌜ xs ⌝ branches′       ⇓⟨ lemma xs ⟩■
    ⌜ ⌜ xs ⌝ ⦂ Exp ⌝
    where
    branches′ : List Br
    branches′ = branches [ v-internal-code ← internal-code ]B⋆

    lemma : (xs : List Var) →
            case ⌜ xs ⌝ branches′ ⇓ ⌜ ⌜ xs ⌝ ⦂ Exp ⌝
    lemma [] =
      case ⌜ [] ⦂ List Var ⌝ branches′  ⇓⟨ case (rep⇓rep ([] ⦂ List Var)) (there (λ ()) (there (λ ()) here)) []
                                                (rep⇓rep (⌜ [] ⦂ List Var ⌝ ⦂ Exp)) ⟩■
      ⌜ ⌜ [] ⦂ List Var ⌝ ⦂ Exp ⌝

    lemma (x ∷ xs) =
      case ⌜ x List.∷ xs ⌝ branches′                                      ⟶⟨ case (rep⇓rep (x List.∷ xs))
                                                                                (there (λ ()) (there (λ ()) (there (λ ()) here))) (∷ ∷ []) ⟩
      const c-const (⌜ c-cons ⌝ ∷
        const c-cons (apply internal-code ⌜ x ⌝ ∷
          const c-cons (apply internal-code ⟨ ⌜ xs ⌝ [ v-x ← ⌜ x ⌝ ] ⟩ ∷
            ⌜ [] ⦂ List Exp ⌝ ∷ []) ∷ []) ∷ [])                           ≡⟨ ⟨by⟩ (subst-rep xs) ⟩⟶

      const c-const (⌜ c-cons ⌝ ∷
        const c-cons (apply internal-code ⌜ x ⌝ ∷
          const c-cons (apply internal-code ⌜ xs ⌝ ∷
            ⌜ [] ⦂ List Exp ⌝ ∷ []) ∷ []) ∷ [])                           ⇓⟨ const (rep⇓rep c-cons ∷
                                                                               const (internal-code-correct-ℕ x ∷
                                                                                 const (internal-code-correct-Var⋆ xs ∷
                                                                                   rep⇓rep ([] ⦂ List Exp) ∷ []) ∷ []) ∷ []) ⟩■
      ⌜ ⌜ x List.∷ xs ⌝ ⦂ Exp ⌝

  mutual

    -- The internal coder encodes expressions correctly.

    internal-code-correct :
      (p : Exp) → apply internal-code ⌜ p ⌝ ⇓ ⌜ ⌜ p ⌝ ⦂ Exp ⌝
    internal-code-correct p =
      apply internal-code ⌜ p ⌝  ⟶⟨ apply (rec lambda) (rep⇓rep p) ⟩
      case ⌜ p ⌝ branches′       ⇓⟨ lemma p ⟩■
      ⌜ ⌜ p ⌝ ⦂ Exp ⌝
      where
      branches′ : List Br
      branches′ = branches [ v-internal-code ← internal-code ]B⋆

      lemma : (p : Exp) → case ⌜ p ⌝ branches′ ⇓ ⌜ ⌜ p ⌝ ⦂ Exp ⌝
      lemma (apply p₁ p₂) =
        case ⌜ Exp.apply p₁ p₂ ⌝ branches′                                   ⟶⟨ case (rep⇓rep (Exp.apply p₁ p₂))
                                                                                     (there (λ ()) (there (λ ()) (there (λ ())
                                                                                        (there (λ ()) here))))
                                                                                     (∷ ∷ []) ⟩
        const c-const (⌜ c-apply ⌝ ∷
          const c-cons (apply internal-code ⌜ p₁ ⌝ ∷
            const c-cons (apply internal-code ⟨ ⌜ p₂ ⌝ [ v-x ← ⌜ p₁ ⌝ ] ⟩ ∷
              ⌜ [] ⦂ List Exp ⌝ ∷ []) ∷ []) ∷ [])                            ≡⟨ ⟨by⟩ (subst-rep p₂) ⟩⟶

        const c-const (⌜ c-apply ⌝ ∷
          const c-cons (apply internal-code ⌜ p₁ ⌝ ∷
            const c-cons (apply internal-code ⌜ p₂ ⌝ ∷
              ⌜ [] ⦂ List Exp ⌝ ∷ []) ∷ []) ∷ [])                            ⇓⟨ const (rep⇓rep c-apply ∷
                                                                                  const (internal-code-correct p₁ ∷
                                                                                    const (internal-code-correct p₂ ∷
                                                                                      rep⇓rep ([] ⦂ List Exp) ∷ []) ∷ []) ∷ []) ⟩■
        ⌜ ⌜ Exp.apply p₁ p₂ ⌝ ⦂ Exp ⌝

      lemma (lambda x p) =
        case ⌜ Exp.lambda x p ⌝ branches′                                  ⟶⟨ case (rep⇓rep (Exp.lambda x p))
                                                                                   (there (λ ()) (there (λ ()) (there (λ ())
                                                                                      (there (λ ()) (there (λ ()) here)))))
                                                                                   (∷ ∷ []) ⟩
        const c-const (⌜ c-lambda ⌝ ∷
          const c-cons (apply internal-code ⌜ x ⌝ ∷
            const c-cons (apply internal-code ⟨ ⌜ p ⌝ [ v-x ← ⌜ x ⌝ ] ⟩ ∷
              ⌜ [] ⦂ List Exp ⌝ ∷ []) ∷ []) ∷ [])                          ≡⟨ ⟨by⟩ (subst-rep p) ⟩⟶

        const c-const (⌜ c-lambda ⌝ ∷
          const c-cons (apply internal-code ⌜ x ⌝ ∷
            const c-cons (apply internal-code ⌜ p ⌝ ∷
              ⌜ [] ⦂ List Exp ⌝ ∷ []) ∷ []) ∷ [])                          ⇓⟨ const (rep⇓rep c-lambda ∷
                                                                                const (internal-code-correct-ℕ x ∷
                                                                                  const (internal-code-correct p ∷
                                                                                    rep⇓rep ([] ⦂ List Exp) ∷ []) ∷ []) ∷ []) ⟩■
        ⌜ ⌜ Exp.lambda x p ⌝ ⦂ Exp ⌝

      lemma (case p bs) =
        case ⌜ Exp.case p bs ⌝ branches′                                    ⟶⟨ case (rep⇓rep (Exp.case p bs))
                                                                                    (there (λ ()) (there (λ ()) (there (λ ())
                                                                                       (there (λ ()) (there (λ ()) (there (λ ()) here))))))
                                                                                    (∷ ∷ []) ⟩
        const c-const (⌜ c-case ⌝ ∷
          const c-cons (apply internal-code ⌜ p ⌝ ∷
            const c-cons (apply internal-code ⟨ ⌜ bs ⌝ [ v-x ← ⌜ p ⌝ ] ⟩ ∷
              ⌜ [] ⦂ List Exp ⌝ ∷ []) ∷ []) ∷ [])                           ≡⟨ ⟨by⟩ (subst-rep bs) ⟩⟶

        const c-const (⌜ c-case ⌝ ∷
          const c-cons (apply internal-code ⌜ p ⌝ ∷
            const c-cons (apply internal-code ⌜ bs ⌝ ∷
              ⌜ [] ⦂ List Exp ⌝ ∷ []) ∷ []) ∷ [])                           ⇓⟨ const (rep⇓rep c-case ∷
                                                                                 const (internal-code-correct p ∷
                                                                                   const (internal-code-correct-B⋆ bs ∷
                                                                                     rep⇓rep ([] ⦂ List Exp) ∷ []) ∷ []) ∷ []) ⟩■
        ⌜ ⌜ Exp.case p bs ⌝ ⦂ Exp ⌝

      lemma (rec x p) =
        case ⌜ Exp.rec x p ⌝ branches′                                     ⟶⟨ case (rep⇓rep (Exp.rec x p))
                                                                                   (there (λ ()) (there (λ ()) (there (λ ()) (there (λ ())
                                                                                      (there (λ ()) (there (λ ()) (there (λ ()) here)))))))
                                                                                   (∷ ∷ []) ⟩
        const c-const (⌜ c-rec ⌝ ∷
          const c-cons (apply internal-code ⌜ x ⌝ ∷
            const c-cons (apply internal-code ⟨ ⌜ p ⌝ [ v-x ← ⌜ x ⌝ ] ⟩ ∷
              ⌜ [] ⦂ List Exp ⌝ ∷ []) ∷ []) ∷ [])                          ≡⟨ ⟨by⟩ (subst-rep p) ⟩⟶
        const c-const (⌜ c-rec ⌝ ∷
          const c-cons (apply internal-code ⌜ x ⌝ ∷
            const c-cons (apply internal-code ⌜ p ⌝ ∷
              ⌜ [] ⦂ List Exp ⌝ ∷ []) ∷ []) ∷ [])                          ⇓⟨ const (rep⇓rep c-rec ∷
                                                                                const (internal-code-correct-ℕ x ∷
                                                                                  const (internal-code-correct p ∷
                                                                                    rep⇓rep ([] ⦂ List Exp) ∷ []) ∷ []) ∷ []) ⟩■
        ⌜ ⌜ Exp.rec x p ⌝ ⦂ Exp ⌝

      lemma (var x) =
        case ⌜ Exp.var x ⌝ branches′                 ⟶⟨ case (rep⇓rep (Exp.var x))
                                                             (there (λ ()) (there (λ ()) (there (λ ()) (there (λ ()) (there (λ ())
                                                                (there (λ ()) (there (λ ()) (there (λ ()) here))))))))
                                                             (∷ []) ⟩
        const c-const (⌜ c-var ⌝ ∷
          const c-cons (apply internal-code ⌜ x ⌝ ∷
            ⌜ [] ⦂ List Exp ⌝ ∷ []) ∷ [])            ⇓⟨ const (rep⇓rep c-var ∷
                                                          const (internal-code-correct-ℕ x ∷ rep⇓rep ([] ⦂ List Exp) ∷ []) ∷ []) ⟩■
        ⌜ ⌜ Exp.var x ⌝ ⦂ Exp ⌝

      lemma (const c ps) =
        case ⌜ Exp.const c ps ⌝ branches′                                   ⟶⟨ case (rep⇓rep (Exp.const c ps))
                                                                                    (there (λ ()) (there (λ ()) (there (λ ()) (there (λ ())
                                                                                       (there (λ ()) (there (λ ()) (there (λ ()) (there (λ ())
                                                                                          (there (λ ()) here)))))))))
                                                                                    (∷ ∷ []) ⟩
        const c-const (⌜ c-const ⌝ ∷
          const c-cons (apply internal-code ⌜ c ⌝ ∷
            const c-cons (apply internal-code ⟨ ⌜ ps ⌝ [ v-x ← ⌜ c ⌝ ] ⟩ ∷
              ⌜ [] ⦂ List Exp ⌝ ∷ []) ∷ []) ∷ [])                           ≡⟨ ⟨by⟩ (subst-rep ps) ⟩⟶

        const c-const (⌜ c-const ⌝ ∷
          const c-cons (apply internal-code ⌜ c ⌝ ∷
            const c-cons (apply internal-code ⌜ ps ⌝ ∷
              ⌜ [] ⦂ List Exp ⌝ ∷ []) ∷ []) ∷ [])                           ⇓⟨ const (rep⇓rep c-const ∷
                                                                                 const (internal-code-correct-ℕ c ∷
                                                                                   const (internal-code-correct-⋆ ps ∷
                                                                                     rep⇓rep ([] ⦂ List Exp) ∷ []) ∷ []) ∷ []) ⟩■
        ⌜ ⌜ Exp.const c ps ⌝ ⦂ Exp ⌝

    -- The internal coder encodes branches correctly.

    internal-code-correct-B :
      (b : Br) → apply internal-code ⌜ b ⌝ ⇓ ⌜ ⌜ b ⌝ ⦂ Exp ⌝
    internal-code-correct-B (branch c xs e) =
      apply internal-code ⌜ branch c xs e ⌝                                ⟶⟨ apply (rec lambda) (rep⇓rep (branch c xs e)) ⟩

      case ⌜ branch c xs e ⌝ branches′                                     ⟶⟨ case (rep⇓rep (branch c xs e))
                                                                                   (there (λ ()) (there (λ ()) (there (λ ()) (there (λ ())
                                                                                      (there (λ ()) (there (λ ()) (there (λ ()) (there (λ ())
                                                                                         (there (λ ()) (there (λ ()) here))))))))))
                                                                                   (∷ ∷ ∷ []) ⟩
      const c-const (⌜ c-branch ⌝ ∷
        const c-cons (apply internal-code ⌜ c ⌝ ∷
          const c-cons (apply internal-code ⌜ xs ⌝ [ v-x ← ⌜ c ⌝ ] ∷
            const c-cons (apply internal-code ⟨ ⌜ e ⌝ [ v-y ← ⌜ xs ⌝ ]
                                                      [ v-x ← ⌜ c ⌝ ] ⟩ ∷
              ⌜ [] ⦂ List Exp ⌝ ∷ []) ∷ []) ∷ []) ∷ [])                    ≡⟨ ⟨by⟩ (substs-rep e ((v-x , ⌜ c ⌝) ∷ (v-y , ⌜ xs ⌝) ∷ [])) ⟩⟶

      const c-const (⌜ c-branch ⌝ ∷
        const c-cons (apply internal-code ⌜ c ⌝ ∷
          const c-cons (apply internal-code ⟨ ⌜ xs ⌝ [ v-x ← ⌜ c ⌝ ] ⟩ ∷
            const c-cons (apply internal-code ⌜ e ⌝ ∷
              ⌜ [] ⦂ List Exp ⌝ ∷ []) ∷ []) ∷ []) ∷ [])                    ≡⟨ ⟨by⟩ (subst-rep xs) ⟩⟶

      const c-const (⌜ c-branch ⌝ ∷
        const c-cons (apply internal-code ⌜ c ⌝ ∷
          const c-cons (apply internal-code ⌜ xs ⌝ ∷
            const c-cons (apply internal-code ⌜ e ⌝ ∷
              ⌜ [] ⦂ List Exp ⌝ ∷ []) ∷ []) ∷ []) ∷ [])                    ⇓⟨ const (rep⇓rep c-branch ∷
                                                                                const (internal-code-correct-ℕ c ∷
                                                                                  const (internal-code-correct-Var⋆ xs ∷
                                                                                    const (internal-code-correct e ∷
                                                                                      rep⇓rep ([] ⦂ List Exp) ∷ []) ∷ []) ∷ []) ∷ []) ⟩■
      ⌜ ⌜ branch c xs e ⌝ ⦂ Exp ⌝
      where
      branches′ : List Br
      branches′ = branches [ v-internal-code ← internal-code ]B⋆

    -- The internal coder encodes lists of expressions correctly.

    internal-code-correct-⋆ :
      (ps : List Exp) →
      apply internal-code ⌜ ps ⌝ ⇓ ⌜ ⌜ ps ⌝ ⦂ Exp ⌝
    internal-code-correct-⋆ ps =
      apply internal-code ⌜ ps ⌝  ⟶⟨ apply (rec lambda) (rep⇓rep ps) ⟩
      case ⌜ ps ⌝ branches′       ⇓⟨ lemma ps ⟩■
      ⌜ ⌜ ps ⌝ ⦂ Exp ⌝
      where
      branches′ : List Br
      branches′ = branches [ v-internal-code ← internal-code ]B⋆

      lemma : (ps : List Exp) →
              case ⌜ ps ⌝ branches′ ⇓ ⌜ ⌜ ps ⌝ ⦂ Exp ⌝
      lemma [] =
        case ⌜ [] ⦂ List Exp ⌝ branches′  ⇓⟨ case (rep⇓rep ([] ⦂ List Exp)) (there (λ ()) (there (λ ()) here)) []
                                                  (rep⇓rep (⌜ [] ⦂ List Exp ⌝ ⦂ Exp)) ⟩■
        ⌜ ⌜ [] ⦂ List Exp ⌝ ⦂ Exp ⌝

      lemma (p ∷ ps) =
        case ⌜ p List.∷ ps ⌝ branches′                                      ⟶⟨ case (rep⇓rep (p List.∷ ps))
                                                                                    (there (λ ()) (there (λ ()) (there (λ ()) here))) (∷ ∷ []) ⟩
        const c-const (⌜ c-cons ⌝ ∷
          const c-cons (apply internal-code ⌜ p ⌝ ∷
            const c-cons (apply internal-code ⟨ ⌜ ps ⌝ [ v-x ← ⌜ p ⌝ ] ⟩ ∷
              ⌜ [] ⦂ List Exp ⌝ ∷ []) ∷ []) ∷ [])                           ≡⟨ ⟨by⟩ (subst-rep ps) ⟩⟶
        const c-const (⌜ c-cons ⌝ ∷
          const c-cons (apply internal-code ⌜ p ⌝ ∷
            const c-cons (apply internal-code ⌜ ps ⌝ ∷
              ⌜ [] ⦂ List Exp ⌝ ∷ []) ∷ []) ∷ [])                           ⇓⟨ const (rep⇓rep c-cons ∷
                                                                                 const (internal-code-correct p ∷
                                                                                   const (internal-code-correct-⋆ ps ∷
                                                                                     rep⇓rep ([] ⦂ List Exp) ∷ []) ∷ []) ∷ []) ⟩■
        ⌜ ⌜ p List.∷ ps ⌝ ⦂ Exp ⌝

    -- The internal coder encodes lists of branches correctly.

    internal-code-correct-B⋆ :
      (bs : List Br) →
      apply internal-code ⌜ bs ⌝ ⇓ ⌜ ⌜ bs ⌝ ⦂ Exp ⌝
    internal-code-correct-B⋆ bs =
      apply internal-code ⌜ bs ⌝  ⟶⟨ apply (rec lambda) (rep⇓rep bs) ⟩
      case ⌜ bs ⌝ branches′       ⇓⟨ lemma bs ⟩■
      ⌜ ⌜ bs ⌝ ⦂ Exp ⌝
      where
      branches′ : List Br
      branches′ = branches [ v-internal-code ← internal-code ]B⋆

      lemma : (bs : List Br) →
              case ⌜ bs ⌝ branches′ ⇓ ⌜ ⌜ bs ⌝ ⦂ Exp ⌝
      lemma [] =
        case ⌜ [] ⦂ List Br ⌝ branches′  ⇓⟨ case (rep⇓rep ([] ⦂ List Br)) (there (λ ()) (there (λ ()) here)) []
                                                 (rep⇓rep (⌜ [] ⦂ List Br ⌝ ⦂ Exp)) ⟩■
        ⌜ ⌜ [] ⦂ List Br ⌝ ⦂ Exp ⌝

      lemma (b ∷ bs) =
        case ⌜ b List.∷ bs ⌝ branches′                                      ⟶⟨ case (rep⇓rep (b List.∷ bs))
                                                                                    (there (λ ()) (there (λ ()) (there (λ ()) here))) (∷ ∷ []) ⟩
        const c-const (⌜ c-cons ⌝ ∷
          const c-cons (apply internal-code ⌜ b ⌝ ∷
            const c-cons (apply internal-code ⟨ ⌜ bs ⌝ [ v-x ← ⌜ b ⌝ ] ⟩ ∷
              ⌜ [] ⦂ List Exp ⌝ ∷ []) ∷ []) ∷ [])                           ≡⟨ ⟨by⟩ (subst-rep bs) ⟩⟶
        const c-const (⌜ c-cons ⌝ ∷
          const c-cons (apply internal-code ⌜ b ⌝ ∷
            const c-cons (apply internal-code ⌜ bs ⌝ ∷
              ⌜ [] ⦂ List Exp ⌝ ∷ []) ∷ []) ∷ [])                           ⇓⟨ const (rep⇓rep c-cons ∷
                                                                                 const (internal-code-correct-B b ∷
                                                                                   const (internal-code-correct-B⋆ bs ∷
                                                                                     rep⇓rep ([] ⦂ List Exp) ∷ []) ∷ []) ∷ []) ⟩■
        ⌜ ⌜ b List.∷ bs ⌝ ⦂ Exp ⌝
