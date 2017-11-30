------------------------------------------------------------------------
-- Internal coding
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Internal-coding where

open import Equality.Propositional
open import Prelude hiding (const)
open import Tactic.By

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
        const c-const (code c ∷
          code ([] ⦂ List Exp) ∷ []))

    unary-branch : Const → Br
    unary-branch c =
      branch c (v-x ∷ []) (
        const c-const (code c ∷
          const c-cons (cd v-x ∷
            code ([] ⦂ List Exp) ∷ []) ∷ []))

    binary-branch : Const → Br
    binary-branch c =
      branch c (v-x ∷ v-y ∷ []) (
        const c-const (code c ∷
          const c-cons (cd v-x ∷
            const c-cons (cd v-y ∷
              code ([] ⦂ List Exp) ∷ []) ∷ []) ∷ []))

    trinary-branch : Const → Br
    trinary-branch c =
      branch c (v-x ∷ v-y ∷ v-z ∷ []) (
        const c-const (code c ∷
          const c-cons (cd v-x ∷
            const c-cons (cd v-y ∷
              const c-cons (cd v-z ∷
                code ([] ⦂ List Exp) ∷ []) ∷ []) ∷ []) ∷ []))

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
    (n : ℕ) → apply internal-code (code n) ⇓ code (code n ⦂ Exp)
  internal-code-correct-ℕ n =
    apply internal-code (code n)  ⟶⟨ apply (rec lambda) (code⇓code n) ⟩
    case (code n) branches′       ⇓⟨ lemma n ⟩■
    code (code n ⦂ Exp)
    where
    branches′ : List Br
    branches′ = branches [ v-internal-code ← internal-code ]B⋆

    lemma : (n : ℕ) → case (code n) branches′ ⇓ code (code n ⦂ Exp)
    lemma zero =
      case (code zero) branches′  ⇓⟨ case (code⇓code zero) here [] (code⇓code (code zero ⦂ Exp)) ⟩■
      code (code zero ⦂ Exp)

    lemma (suc n) =
      case (code (suc n)) branches′                   ⟶⟨ case (code⇓code (suc n)) (there (λ ()) here) (∷ []) ⟩

      const c-const (code c-suc ∷
        const c-cons (apply internal-code (code n) ∷
          code ([] ⦂ List Exp) ∷ []) ∷ [])            ⇓⟨ const (code⇓code c-suc ∷
                                                           const (internal-code-correct-ℕ n ∷ code⇓code ([] ⦂ List Exp) ∷ []) ∷ []) ⟩■
      code (code (suc n) ⦂ Exp)

  -- The internal coder encodes lists of variables correctly.

  internal-code-correct-Var⋆ :
    (xs : List Var) →
    apply internal-code (code xs) ⇓ code (code xs ⦂ Exp)
  internal-code-correct-Var⋆ xs =
    apply internal-code (code xs)  ⟶⟨ apply (rec lambda) (code⇓code xs) ⟩
    case (code xs) branches′       ⇓⟨ lemma xs ⟩■
    code (code xs ⦂ Exp)
    where
    branches′ : List Br
    branches′ = branches [ v-internal-code ← internal-code ]B⋆

    lemma : (xs : List Var) →
            case (code xs) branches′ ⇓ code (code xs ⦂ Exp)
    lemma [] =
      case (code ([] ⦂ List Var)) branches′  ⇓⟨ case (code⇓code ([] ⦂ List Var)) (there (λ ()) (there (λ ()) here)) []
                                                     (code⇓code (code ([] ⦂ List Var) ⦂ Exp)) ⟩■
      code (code ([] ⦂ List Var) ⦂ Exp)

    lemma (x ∷ xs) =
      case (code (x List.∷ xs)) branches′                                 ⟶⟨ case (code⇓code (x List.∷ xs))
                                                                                  (there (λ ()) (there (λ ()) (there (λ ()) here))) (∷ ∷ []) ⟩
      const c-const (code c-cons ∷
        const c-cons (apply internal-code (code x) ∷
          const c-cons (apply internal-code (code xs [ v-x ← code x ]) ∷
            code ([] ⦂ List Exp) ∷ []) ∷ []) ∷ [])                        ≡⟨ cong (λ e → const _ (_ ∷ const _ (_ ∷ const _ (apply _ e ∷ _) ∷ _) ∷ _))
                                                                                  (subst-code xs) ⟩⟶
      const c-const (code c-cons ∷
        const c-cons (apply internal-code (code x) ∷
          const c-cons (apply internal-code (code xs) ∷
            code ([] ⦂ List Exp) ∷ []) ∷ []) ∷ [])                        ⇓⟨ const (code⇓code c-cons ∷
                                                                               const (internal-code-correct-ℕ x ∷
                                                                                 const (internal-code-correct-Var⋆ xs ∷
                                                                                   code⇓code ([] ⦂ List Exp) ∷ []) ∷ []) ∷ []) ⟩■
      code (code (x List.∷ xs) ⦂ Exp)

  mutual

    -- The internal coder encodes expressions correctly.

    internal-code-correct :
      (p : Exp) → apply internal-code (code p) ⇓ code (code p ⦂ Exp)
    internal-code-correct p =
      apply internal-code (code p)  ⟶⟨ apply (rec lambda) (code⇓code p) ⟩
      case (code p) branches′       ⇓⟨ lemma p ⟩■
      code (code p ⦂ Exp)
      where
      branches′ : List Br
      branches′ = branches [ v-internal-code ← internal-code ]B⋆

      lemma : (p : Exp) → case (code p) branches′ ⇓ code (code p ⦂ Exp)
      lemma (apply p₁ p₂) =
        case (code (Exp.apply p₁ p₂)) branches′                              ⟶⟨ case (code⇓code (Exp.apply p₁ p₂))
                                                                                     (there (λ ()) (there (λ ()) (there (λ ()) (there (λ ()) here))))
                                                                                     (∷ ∷ []) ⟩
        const c-const (code c-apply ∷
          const c-cons (apply internal-code (code p₁) ∷
            const c-cons (apply internal-code (code p₂ [ v-x ← code p₁ ]) ∷
              code ([] ⦂ List Exp) ∷ []) ∷ []) ∷ [])                         ≡⟨ cong (λ e → const _ (_ ∷ const _ (_ ∷
                                                                                              const _ (apply _ e ∷ _) ∷ _) ∷ _))
                                                                                     (subst-code p₂) ⟩⟶
        const c-const (code c-apply ∷
          const c-cons (apply internal-code (code p₁) ∷
            const c-cons (apply internal-code (code p₂) ∷
              code ([] ⦂ List Exp) ∷ []) ∷ []) ∷ [])                         ⇓⟨ const (code⇓code c-apply ∷
                                                                                  const (internal-code-correct p₁ ∷
                                                                                    const (internal-code-correct p₂ ∷
                                                                                      code⇓code ([] ⦂ List Exp) ∷ []) ∷ []) ∷ []) ⟩■
        code (code (Exp.apply p₁ p₂) ⦂ Exp)

      lemma (lambda x p) =
        case (code (Exp.lambda x p)) branches′                              ⟶⟨ case (code⇓code (Exp.lambda x p))
                                                                                    (there (λ ()) (there (λ ()) (there (λ ())
                                                                                       (there (λ ()) (there (λ ()) here)))))
                                                                                    (∷ ∷ []) ⟩
        const c-const (code c-lambda ∷
          const c-cons (apply internal-code (code x) ∷
            const c-cons (apply internal-code (code p [ v-x ← code x ]) ∷
              code ([] ⦂ List Exp) ∷ []) ∷ []) ∷ [])                       ≡⟨ cong (λ e → const _ (_ ∷ const _ (_ ∷ const _ (apply _ e ∷ _) ∷ _) ∷ _))
                                                                                   (subst-code p) ⟩⟶
        const c-const (code c-lambda ∷
          const c-cons (apply internal-code (code x) ∷
            const c-cons (apply internal-code (code p) ∷
              code ([] ⦂ List Exp) ∷ []) ∷ []) ∷ [])                       ⇓⟨ const (code⇓code c-lambda ∷
                                                                                const (internal-code-correct-ℕ x ∷
                                                                                  const (internal-code-correct p ∷
                                                                                    code⇓code ([] ⦂ List Exp) ∷ []) ∷ []) ∷ []) ⟩■
        code (code (Exp.lambda x p) ⦂ Exp)

      lemma (case p bs) =
        case (code (Exp.case p bs)) branches′                              ⟶⟨ case (code⇓code (Exp.case p bs))
                                                                                   (there (λ ()) (there (λ ()) (there (λ ())
                                                                                      (there (λ ()) (there (λ ()) (there (λ ()) here))))))
                                                                                   (∷ ∷ []) ⟩
        const c-const (code c-case ∷
          const c-cons (apply internal-code (code p) ∷
            const c-cons (apply internal-code (code bs [ v-x ← code p ]) ∷
              code ([] ⦂ List Exp) ∷ []) ∷ []) ∷ [])                        ≡⟨ cong (λ e → const _ (_ ∷ const _ (_ ∷
                                                                                             const _ (apply _ e ∷ _) ∷ _) ∷ _))
                                                                                    (subst-code bs) ⟩⟶
        const c-const (code c-case ∷
          const c-cons (apply internal-code (code p) ∷
            const c-cons (apply internal-code (code bs) ∷
              code ([] ⦂ List Exp) ∷ []) ∷ []) ∷ [])                        ⇓⟨ const (code⇓code c-case ∷
                                                                                 const (internal-code-correct p ∷
                                                                                   const (internal-code-correct-B⋆ bs ∷
                                                                                     code⇓code ([] ⦂ List Exp) ∷ []) ∷ []) ∷ []) ⟩■
        code (code (Exp.case p bs) ⦂ Exp)

      lemma (rec x p) =
        case (code (Exp.rec x p)) branches′                                ⟶⟨ case (code⇓code (Exp.rec x p))
                                                                                   (there (λ ()) (there (λ ()) (there (λ ()) (there (λ ())
                                                                                      (there (λ ()) (there (λ ()) (there (λ ()) here)))))))
                                                                                   (∷ ∷ []) ⟩
        const c-const (code c-rec ∷
          const c-cons (apply internal-code (code x) ∷
            const c-cons (apply internal-code (code p [ v-x ← code x ]) ∷
              code ([] ⦂ List Exp) ∷ []) ∷ []) ∷ [])                       ≡⟨ cong (λ e → const _ (_ ∷ const _ (_ ∷ const _ (apply _ e ∷ _) ∷ _) ∷ _))
                                                                                   (subst-code p) ⟩⟶
        const c-const (code c-rec ∷
          const c-cons (apply internal-code (code x) ∷
            const c-cons (apply internal-code (code p) ∷
              code ([] ⦂ List Exp) ∷ []) ∷ []) ∷ [])                       ⇓⟨ const (code⇓code c-rec ∷
                                                                                const (internal-code-correct-ℕ x ∷
                                                                                  const (internal-code-correct p ∷
                                                                                    code⇓code ([] ⦂ List Exp) ∷ []) ∷ []) ∷ []) ⟩■
        code (code (Exp.rec x p) ⦂ Exp)

      lemma (var x) =
        case (code (Exp.var x)) branches′               ⟶⟨ case (code⇓code (Exp.var x))
                                                                (there (λ ()) (there (λ ()) (there (λ ()) (there (λ ()) (there (λ ())
                                                                   (there (λ ()) (there (λ ()) (there (λ ()) here))))))))
                                                                (∷ []) ⟩
        const c-const (code c-var ∷
          const c-cons (apply internal-code (code x) ∷
            code ([] ⦂ List Exp) ∷ []) ∷ [])            ⇓⟨ const (code⇓code c-var ∷
                                                             const (internal-code-correct-ℕ x ∷ code⇓code ([] ⦂ List Exp) ∷ []) ∷ []) ⟩■
        code (code (Exp.var x) ⦂ Exp)

      lemma (const c ps) =
        case (code (Exp.const c ps)) branches′                              ⟶⟨ case (code⇓code (Exp.const c ps))
                                                                                    (there (λ ()) (there (λ ()) (there (λ ()) (there (λ ())
                                                                                       (there (λ ()) (there (λ ()) (there (λ ()) (there (λ ())
                                                                                          (there (λ ()) here)))))))))
                                                                                    (∷ ∷ []) ⟩
        const c-const (code c-const ∷
          const c-cons (apply internal-code (code c) ∷
            const c-cons (apply internal-code (code ps [ v-x ← code c ]) ∷
              code ([] ⦂ List Exp) ∷ []) ∷ []) ∷ [])                        ≡⟨ cong (λ e → const _ (_ ∷ const _ (_ ∷
                                                                                             const _ (apply _ e ∷ _) ∷ _) ∷ _))
                                                                                    (subst-code ps) ⟩⟶
        const c-const (code c-const ∷
          const c-cons (apply internal-code (code c) ∷
            const c-cons (apply internal-code (code ps) ∷
              code ([] ⦂ List Exp) ∷ []) ∷ []) ∷ [])                        ⇓⟨ const (code⇓code c-const ∷
                                                                                 const (internal-code-correct-ℕ c ∷
                                                                                   const (internal-code-correct-⋆ ps ∷
                                                                                     code⇓code ([] ⦂ List Exp) ∷ []) ∷ []) ∷ []) ⟩■
        code (code (Exp.const c ps) ⦂ Exp)

    -- The internal coder encodes branches correctly.

    internal-code-correct-B :
      (b : Br) → apply internal-code (code b) ⇓ code (code b ⦂ Exp)
    internal-code-correct-B (branch c xs e) =
      apply internal-code (code (branch c xs e))                           ⟶⟨ apply (rec lambda) (code⇓code (branch c xs e)) ⟩

      case (code (branch c xs e)) branches′                                ⟶⟨ case (code⇓code (branch c xs e))
                                                                                   (there (λ ()) (there (λ ()) (there (λ ()) (there (λ ())
                                                                                      (there (λ ()) (there (λ ()) (there (λ ()) (there (λ ())
                                                                                         (there (λ ()) (there (λ ()) here))))))))))
                                                                                   (∷ ∷ ∷ []) ⟩
      const c-const (code c-branch ∷
        const c-cons (apply internal-code (code c) ∷
          const c-cons (apply internal-code (code xs [ v-x ← code c ]) ∷
            const c-cons (apply internal-code (code e [ v-y ← code xs ]
                                                      [ v-x ← code c ]) ∷
              code ([] ⦂ List Exp) ∷ []) ∷ []) ∷ []) ∷ [])                 ≡⟨ cong (λ e → const _ (_ ∷ const _ (_ ∷ const _ (_ ∷
                                                                                            const _ (apply _ e ∷ _) ∷ _) ∷ _) ∷ _))
                                                                                   (substs-code e ((v-x , code c) ∷ (v-y , code xs) ∷ [])) ⟩⟶
      const c-const (code c-branch ∷
        const c-cons (apply internal-code (code c) ∷
          const c-cons (apply internal-code (code xs [ v-x ← code c ]) ∷
            const c-cons (apply internal-code (code e) ∷
              code ([] ⦂ List Exp) ∷ []) ∷ []) ∷ []) ∷ [])                 ≡⟨ cong (λ e → const _ (_ ∷ const _ (_ ∷
                                                                                            const _ (apply _ e ∷ _ ∷ _) ∷ _) ∷ _))
                                                                                   (subst-code xs) ⟩⟶
      const c-const (code c-branch ∷
        const c-cons (apply internal-code (code c) ∷
          const c-cons (apply internal-code (code xs) ∷
            const c-cons (apply internal-code (code e) ∷
              code ([] ⦂ List Exp) ∷ []) ∷ []) ∷ []) ∷ [])                 ⇓⟨ const (code⇓code c-branch ∷
                                                                                const (internal-code-correct-ℕ c ∷
                                                                                  const (internal-code-correct-Var⋆ xs ∷
                                                                                    const (internal-code-correct e ∷
                                                                                      code⇓code ([] ⦂ List Exp) ∷ []) ∷ []) ∷ []) ∷ []) ⟩■
      code (code (branch c xs e) ⦂ Exp)
      where
      branches′ : List Br
      branches′ = branches [ v-internal-code ← internal-code ]B⋆

    -- The internal coder encodes lists of expressions correctly.

    internal-code-correct-⋆ :
      (ps : List Exp) →
      apply internal-code (code ps) ⇓ code (code ps ⦂ Exp)
    internal-code-correct-⋆ ps =
      apply internal-code (code ps)  ⟶⟨ apply (rec lambda) (code⇓code ps) ⟩
      case (code ps) branches′       ⇓⟨ lemma ps ⟩■
      code (code ps ⦂ Exp)
      where
      branches′ : List Br
      branches′ = branches [ v-internal-code ← internal-code ]B⋆

      lemma : (ps : List Exp) →
              case (code ps) branches′ ⇓ code (code ps ⦂ Exp)
      lemma [] =
        case (code ([] ⦂ List Exp)) branches′  ⇓⟨ case (code⇓code ([] ⦂ List Exp)) (there (λ ()) (there (λ ()) here)) []
                                                       (code⇓code (code ([] ⦂ List Exp) ⦂ Exp)) ⟩■
        code (code ([] ⦂ List Exp) ⦂ Exp)

      lemma (p ∷ ps) =
        case (code (p List.∷ ps)) branches′                                 ⟶⟨ case (code⇓code (p List.∷ ps))
                                                                                    (there (λ ()) (there (λ ()) (there (λ ()) here))) (∷ ∷ []) ⟩
        const c-const (code c-cons ∷
          const c-cons (apply internal-code (code p) ∷
            const c-cons (apply internal-code (code ps [ v-x ← code p ]) ∷
              code ([] ⦂ List Exp) ∷ []) ∷ []) ∷ [])                        ≡⟨ cong (λ e → const _ (_ ∷ const _ (_ ∷
                                                                                             const _ (apply _ e ∷ _) ∷ _) ∷ _))
                                                                                    (subst-code ps) ⟩⟶
        const c-const (code c-cons ∷
          const c-cons (apply internal-code (code p) ∷
            const c-cons (apply internal-code (code ps) ∷
              code ([] ⦂ List Exp) ∷ []) ∷ []) ∷ [])                        ⇓⟨ const (code⇓code c-cons ∷
                                                                                 const (internal-code-correct p ∷
                                                                                   const (internal-code-correct-⋆ ps ∷
                                                                                     code⇓code ([] ⦂ List Exp) ∷ []) ∷ []) ∷ []) ⟩■
        code (code (p List.∷ ps) ⦂ Exp)

    -- The internal coder encodes lists of branches correctly.

    internal-code-correct-B⋆ :
      (bs : List Br) →
      apply internal-code (code bs) ⇓ code (code bs ⦂ Exp)
    internal-code-correct-B⋆ bs =
      apply internal-code (code bs)  ⟶⟨ apply (rec lambda) (code⇓code bs) ⟩
      case (code bs) branches′       ⇓⟨ lemma bs ⟩■
      code (code bs ⦂ Exp)
      where
      branches′ : List Br
      branches′ = branches [ v-internal-code ← internal-code ]B⋆

      lemma : (bs : List Br) →
              case (code bs) branches′ ⇓ code (code bs ⦂ Exp)
      lemma [] =
        case (code ([] ⦂ List Br)) branches′  ⇓⟨ case (code⇓code ([] ⦂ List Br)) (there (λ ()) (there (λ ()) here)) []
                                                      (code⇓code (code ([] ⦂ List Br) ⦂ Exp)) ⟩■
        code (code ([] ⦂ List Br) ⦂ Exp)

      lemma (b ∷ bs) =
        case (code (b List.∷ bs)) branches′                                 ⟶⟨ case (code⇓code (b List.∷ bs))
                                                                                    (there (λ ()) (there (λ ()) (there (λ ()) here))) (∷ ∷ []) ⟩
        const c-const (code c-cons ∷
          const c-cons (apply internal-code (code b) ∷
            const c-cons (apply internal-code (code bs [ v-x ← code b ]) ∷
              code ([] ⦂ List Exp) ∷ []) ∷ []) ∷ [])                        ≡⟨ cong (λ e → const _ (_ ∷ const _ (_ ∷
                                                                                             const _ (apply _ e ∷ _) ∷ _) ∷ _))
                                                                                    (subst-code bs) ⟩⟶
        const c-const (code c-cons ∷
          const c-cons (apply internal-code (code b) ∷
            const c-cons (apply internal-code (code bs) ∷
              code ([] ⦂ List Exp) ∷ []) ∷ []) ∷ [])                        ⇓⟨ const (code⇓code c-cons ∷
                                                                                 const (internal-code-correct-B b ∷
                                                                                   const (internal-code-correct-B⋆ bs ∷
                                                                                     code⇓code ([] ⦂ List Exp) ∷ []) ∷ []) ∷ []) ⟩■
        code (code (b List.∷ bs) ⦂ Exp)
