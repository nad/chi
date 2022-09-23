------------------------------------------------------------------------
-- Internal substitution
------------------------------------------------------------------------

module Internal-substitution where

open import Equality.Propositional
open import Prelude hiding (const)

open import Bag-equivalence equality-with-J using (_∈_)

-- To simplify the development, let's work with actual natural numbers
-- as variables and constants (see
-- Atom.one-can-restrict-attention-to-χ-ℕ-atoms).

open import Atom

open import Chi            χ-ℕ-atoms
open import Coding         χ-ℕ-atoms
open import Compatibility  χ-ℕ-atoms
open import Constants      χ-ℕ-atoms
open import Deterministic  χ-ℕ-atoms
open import Free-variables χ-ℕ-atoms
open import Reasoning      χ-ℕ-atoms
open import Values         χ-ℕ-atoms

open import Coding.Instances.Nat
open import Combinators
open import Free-variables.Remove-substs

open χ-atoms χ-ℕ-atoms using (Var; module V)

private

  -- Auxiliary definitions used in the implementation of
  -- internal-subst.

  branches : List Br
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
    where
    rec-or-lambda : ℕ → Br
    rec-or-lambda c =
      branch c (v-y ∷ v-e ∷ []) (
        case (equal-ℕ (var v-x) (var v-y)) (
          branch c-true [] (const c (var v-y ∷ var v-e ∷ [])) ∷
          branch c-false [] (
            const c (var v-y ∷ apply (var v-subst) (var v-e) ∷ [])) ∷
          []))

  body : Exp
  body = rec v-subst (lambda v-e (case (var v-e) branches))

-- Internal substitution.

internal-subst : Exp
internal-subst = lambda v-x (lambda v-new body)

-- Internal substitution is correct (part one).

internal-subst-correct₁ :
  ∀ {e x e′} →
  apply (apply (apply internal-subst ⌜ x ⌝) ⌜ e′ ⌝) ⌜ e ⌝
    ⇓
  ⌜ e [ x ← e′ ] ⌝
internal-subst-correct₁ {e = e} {x = x} {e′ = e′} =
  apply (apply (apply internal-subst ⌜ x ⌝) ⌜ e′ ⌝) ⌜ e ⌝  ⟶⟨ apply (apply (apply lambda (rep⇓rep x) lambda)
                                                                       (rep⇓rep e′) (rec lambda))
                                                                (rep⇓rep e) ⟩
  case ⌜ e ⌝
    (branches [ v-x ← ⌜ x ⌝ ]B⋆ [ v-new ← ⌜ e′ ⌝ ]B⋆
       [ v-subst ← sub ]B⋆ [ v-e ← ⌜ e ⌝ ]B⋆)              ⇓⟨ case-Exp e ⟩■

  ⌜ e [ x ← e′ ] ⌝
  where
  sub : Exp
  sub = body [ v-x ← ⌜ x ⌝ ] [ v-new ← ⌜ e′ ⌝ ]

  sub-closed : Closed sub
  sub-closed = Closed′-closed-under-subst
    (Closed′-closed-under-subst
       (from-⊎ (closed′? body (v-x ∷ v-new ∷ [])) )
       (Closed→Closed′ $ rep-closed x))
    (rep-closed e′)

  mutual

    sub-Exp : ∀ e → apply sub ⌜ e ⌝ ⇓ ⌜ e [ x ← e′ ] ⌝
    sub-Exp e =
      apply sub ⌜ e ⌝                                     ⟶⟨ apply (rec lambda) (rep⇓rep e) ⟩

      case ⌜ e ⌝
        (branches [ v-x ← ⌜ x ⌝ ]B⋆ [ v-new ← ⌜ e′ ⌝ ]B⋆
           [ v-subst ← sub ]B⋆ [ v-e ← ⌜ e ⌝ ]B⋆)         ⇓⟨ case-Exp e ⟩■

      ⌜ e [ x ← e′ ] ⌝

    sub-Exps : ∀ es → apply sub ⌜ es ⌝ ⇓ ⌜ es [ x ← e′ ]⋆ ⌝
    sub-Exps es =
      apply sub ⌜ es ⌝                                     ⟶⟨ apply (rec lambda) (rep⇓rep es) ⟩

      case ⌜ es ⌝
        (branches [ v-x ← ⌜ x ⌝ ]B⋆ [ v-new ← ⌜ e′ ⌝ ]B⋆
           [ v-subst ← sub ]B⋆ [ v-e ← ⌜ es ⌝ ]B⋆)         ⇓⟨ case-Exps es ⟩■

      ⌜ es [ x ← e′ ]⋆ ⌝

    sub-Br : ∀ b → apply sub ⌜ b ⌝ ⇓ ⌜ b [ x ← e′ ]B ⌝
    sub-Br b =
      apply sub ⌜ b ⌝                                     ⟶⟨ apply (rec lambda) (rep⇓rep b) ⟩

      case ⌜ b ⌝
        (branches [ v-x ← ⌜ x ⌝ ]B⋆ [ v-new ← ⌜ e′ ⌝ ]B⋆
           [ v-subst ← sub ]B⋆ [ v-e ← ⌜ b ⌝ ]B⋆)         ⇓⟨ case-Br b ⟩■

      ⌜ b [ x ← e′ ]B ⌝

    sub-Brs : ∀ bs → apply sub ⌜ bs ⌝ ⇓ ⌜ bs [ x ← e′ ]B⋆ ⌝
    sub-Brs bs =
      apply sub ⌜ bs ⌝                                    ⟶⟨ apply (rec lambda) (rep⇓rep bs) ⟩

      case ⌜ bs ⌝
        (branches [ v-x ← ⌜ x ⌝ ]B⋆ [ v-new ← ⌜ e′ ⌝ ]B⋆
           [ v-subst ← sub ]B⋆ [ v-e ← ⌜ bs ⌝ ]B⋆)        ⇓⟨ case-Brs bs ⟩■

      ⌜ bs [ x ← e′ ]B⋆ ⌝

    case-Exp :
      ∀ e →
      case ⌜ e ⌝
        (branches [ v-x ← ⌜ x ⌝ ]B⋆ [ v-new ← ⌜ e′ ⌝ ]B⋆
           [ v-subst ← sub ]B⋆ [ v-e ← ⌜ e ⌝ ]B⋆)
        ⇓
      ⌜ e [ x ← e′ ] ⌝
    case-Exp (apply e₁ e₂) =
      case ⌜ Exp.apply e₁ e₂ ⌝
        (branches [ v-x ← ⌜ x ⌝ ]B⋆ [ v-new ← ⌜ e′ ⌝ ]B⋆
           [ v-subst ← sub ]B⋆ [ v-e ← ⌜ Exp.apply e₁ e₂ ⌝ ]B⋆)   ⟶⟨ case (rep⇓rep (Exp.apply e₁ e₂)) here (∷ ∷ []) ⟩

      const c-apply (
        apply (sub [ v-e₂ ← ⌜ e₂ ⌝ ] [ v-e₁ ← ⌜ e₁ ⌝ ]) ⌜ e₁ ⌝ ∷
        apply (sub [ v-e₂ ← ⌜ e₂ ⌝ ] [ v-e₁ ← ⌜ e₁ ⌝ ])
              (⌜ e₂ ⌝ [ v-e₁ ← ⌜ e₁ ⌝ ]) ∷
        [])                                                       ≡⟨ remove-substs ((sub , sub-closed) ∷ []) ⟩⟶

      const c-apply (apply sub ⌜ e₁ ⌝ ∷ apply sub ⌜ e₂ ⌝ ∷ [])    ⇓⟨ const (sub-Exp e₁ ∷ sub-Exp e₂ ∷ []) ⟩■

      ⌜ Exp.apply (e₁ [ x ← e′ ]) (e₂ [ x ← e′ ]) ⌝

    case-Exp (lambda y e) =
      case ⌜ Exp.lambda y e ⌝
        (branches [ v-x ← ⌜ x ⌝ ]B⋆ [ v-new ← ⌜ e′ ⌝ ]B⋆
           [ v-subst ← sub ]B⋆ [ v-e ← ⌜ Exp.lambda y e ⌝ ]B⋆)    ⟶⟨ case (rep⇓rep (Exp.lambda y e))
                                                                       (there (λ ()) (there (λ ()) (there (λ ()) here)))
                                                                       (∷ ∷ []) ⟩
      case (equal-ℕ (⌜ x ⌝ [ v-new ← ⌜ e′ ⌝ ]
                           [ v-subst ← sub ]
                           [ v-e ← ⌜ e ⌝ ]
                           [ v-y ← ⌜ y ⌝ ])
                    ⌜ y ⌝) (
        branch c-true [] (
          const c-lambda (⌜ y ⌝ ∷ ⌜ e ⌝ [ v-y ← ⌜ y ⌝ ] ∷ [])) ∷
        branch c-false [] (
          const c-lambda (
            ⌜ y ⌝ ∷
            apply (sub [ v-e ← ⌜ e ⌝ ] [ v-y ← ⌜ y ⌝ ])
              (⌜ e ⌝ [ v-y ← ⌜ y ⌝ ]) ∷
            [])) ∷
        [])                                                       ≡⟨ remove-substs ((sub , sub-closed) ∷ []) ⟩⟶

      case (equal-ℕ ⌜ x ⌝ ⌜ y ⌝) (
        branch c-true [] (
          const c-lambda (⌜ y ⌝ ∷ ⌜ e ⌝ ∷ [])) ∷
        branch c-false [] (
          const c-lambda (⌜ y ⌝ ∷ apply sub ⌜ e ⌝ ∷ [])) ∷
        [])                                                       ⇓⟨ lambda-lemma _ (x V.≟ y) (equal-ℕ-correct-ℕ-atoms x y) ⟩■

      ⌜ Exp.lambda y e [ x ← e′ ] ⌝
      where
      lambda-lemma :
        (e″ : Exp) (b : Dec (x ≡ y)) →
        e″ ⇓ ⌜ Prelude.if b then true else false ⌝ →
        case e″ (
          branch c-true [] (
            const c-lambda (⌜ y ⌝ ∷ ⌜ e ⌝ ∷ [])) ∷
          branch c-false [] (
            const c-lambda (⌜ y ⌝ ∷ apply sub ⌜ e ⌝ ∷ [])) ∷
          []) ⇓
        ⌜ Exp.lambda y (Prelude.if b then e else e [ x ← e′ ]) ⌝
      lambda-lemma e″ (yes _) e″⇓ =
        case e″ (
          branch c-true [] (
            const c-lambda (⌜ y ⌝ ∷ ⌜ e ⌝ ∷ [])) ∷
          branch c-false [] (
            const c-lambda (⌜ y ⌝ ∷ apply sub ⌜ e ⌝ ∷ [])) ∷
          [])                                                 ⟶⟨ case e″⇓ here [] ⟩

        ⌜ Exp.lambda y e ⌝                                    ■⟨ rep-value (lambda y e) ⟩

      lambda-lemma e″ (no _) e″⇓ =
        case e″ (
          branch c-true [] (
            const c-lambda (⌜ y ⌝ ∷ ⌜ e ⌝ ∷ [])) ∷
          branch c-false [] (
            const c-lambda (⌜ y ⌝ ∷ apply sub ⌜ e ⌝ ∷ [])) ∷
          [])                                                 ⟶⟨ case e″⇓ (there (λ ()) here) [] ⟩

        const c-lambda (⌜ y ⌝ ∷ apply sub ⌜ e ⌝ ∷ [])         ⇓⟨ const (rep⇓rep y ∷ sub-Exp e ∷ []) ⟩■

        ⌜ Exp.lambda y (e [ x ← e′ ]) ⌝

    case-Exp (case e bs) =
      case ⌜ Exp.case e bs ⌝
        (branches [ v-x ← ⌜ x ⌝ ]B⋆ [ v-new ← ⌜ e′ ⌝ ]B⋆
           [ v-subst ← sub ]B⋆ [ v-e ← ⌜ Exp.case e bs ⌝ ]B⋆)  ⟶⟨ case (rep⇓rep (Exp.case e bs))
                                                                    (there (λ ()) here)
                                                                    (∷ ∷ []) ⟩

      const c-case (
        apply (sub [ v-bs ← ⌜ bs ⌝ ] [ v-e ← ⌜ e ⌝ ]) ⌜ e ⌝ ∷
        apply (sub [ v-bs ← ⌜ bs ⌝ ] [ v-e ← ⌜ e ⌝ ])
          (⌜ bs ⌝ [ v-e ← ⌜ e ⌝ ]) ∷
        [])                                                    ≡⟨ remove-substs ((sub , sub-closed) ∷ []) ⟩⟶

      const c-case (apply sub ⌜ e ⌝ ∷ apply sub ⌜ bs ⌝ ∷ [])   ⇓⟨ const (sub-Exp e ∷ sub-Brs bs ∷ []) ⟩■

      ⌜ Exp.case e bs [ x ← e′ ] ⌝

    case-Exp (rec y e) =
      case ⌜ Exp.rec y e ⌝
        (branches [ v-x ← ⌜ x ⌝ ]B⋆ [ v-new ← ⌜ e′ ⌝ ]B⋆
           [ v-subst ← sub ]B⋆ [ v-e ← ⌜ Exp.rec y e ⌝ ]B⋆)     ⟶⟨ case (rep⇓rep (Exp.rec y e))
                                                                     (there (λ ()) (there (λ ()) here))
                                                                     (∷ ∷ []) ⟩
      case (equal-ℕ (⌜ x ⌝ [ v-new ← ⌜ e′ ⌝ ]
                           [ v-subst ← sub ]
                           [ v-e ← ⌜ e ⌝ ]
                           [ v-y ← ⌜ y ⌝ ])
                    ⌜ y ⌝) (
        branch c-true [] (
          const c-rec (⌜ y ⌝ ∷ ⌜ e ⌝ [ v-y ← ⌜ y ⌝ ] ∷ [])) ∷
        branch c-false [] (
          const c-rec (
            ⌜ y ⌝ ∷
            apply (sub [ v-e ← ⌜ e ⌝ ] [ v-y ← ⌜ y ⌝ ])
              (⌜ e ⌝ [ v-y ← ⌜ y ⌝ ]) ∷
            [])) ∷
        [])                                                     ≡⟨ remove-substs ((sub , sub-closed) ∷ []) ⟩⟶

      case (equal-ℕ ⌜ x ⌝ ⌜ y ⌝) (
        branch c-true [] (
          const c-rec (⌜ y ⌝ ∷ ⌜ e ⌝ ∷ [])) ∷
        branch c-false [] (
          const c-rec (⌜ y ⌝ ∷ apply sub ⌜ e ⌝ ∷ [])) ∷
        [])                                                     ⇓⟨ rec-lemma _ (x V.≟ y) (equal-ℕ-correct-ℕ-atoms x y) ⟩■

      ⌜ Exp.rec y e [ x ← e′ ] ⌝
      where
      rec-lemma :
        (e″ : Exp) (b : Dec (x ≡ y)) →
        e″ ⇓ ⌜ Prelude.if b then true else false ⌝ →
        case e″ (
          branch c-true [] (
            const c-rec (⌜ y ⌝ ∷ ⌜ e ⌝ ∷ [])) ∷
          branch c-false [] (
            const c-rec (⌜ y ⌝ ∷ apply sub ⌜ e ⌝ ∷ [])) ∷
          []) ⇓
        ⌜ Exp.rec y (Prelude.if b then e else e [ x ← e′ ]) ⌝
      rec-lemma e″ (yes _) e″⇓ =
        case e″ (
          branch c-true [] (
            const c-rec (⌜ y ⌝ ∷ ⌜ e ⌝ ∷ [])) ∷
          branch c-false [] (
            const c-rec (⌜ y ⌝ ∷ apply sub ⌜ e ⌝ ∷ [])) ∷
          [])                                              ⟶⟨ case e″⇓ here [] ⟩

        ⌜ Exp.rec y e ⌝                                    ■⟨ rep-value (rec y e) ⟩

      rec-lemma e″ (no _) e″⇓ =
        case e″ (
          branch c-true [] (
            const c-rec (⌜ y ⌝ ∷ ⌜ e ⌝ ∷ [])) ∷
          branch c-false [] (
            const c-rec (⌜ y ⌝ ∷ apply sub ⌜ e ⌝ ∷ [])) ∷
          [])                                              ⟶⟨ case e″⇓ (there (λ ()) here) [] ⟩

        const c-rec (⌜ y ⌝ ∷ apply sub ⌜ e ⌝ ∷ [])         ⇓⟨ const (rep⇓rep y ∷ sub-Exp e ∷ []) ⟩■

        ⌜ Exp.rec y (e [ x ← e′ ]) ⌝

    case-Exp (var y) =
      case ⌜ Exp.var y ⌝
        (branches [ v-x ← ⌜ x ⌝ ]B⋆ [ v-new ← ⌜ e′ ⌝ ]B⋆
           [ v-subst ← sub ]B⋆ [ v-e ← ⌜ Exp.var y ⌝ ]B⋆)   ⟶⟨ case (rep⇓rep (Exp.var y))
                                                                 (there (λ ()) (there (λ ()) (there (λ ())
                                                                    (there (λ ()) (there (λ ()) here)))))
                                                                 (∷ []) ⟩
      case (equal-ℕ
              (⌜ x ⌝ [ v-new ← ⌜ e′ ⌝ ] [ v-subst ← sub ]
                     [ v-e ← ⌜ Exp.var y ⌝ ]
                     [ v-y ← ⌜ y ⌝ ])
              ⌜ y ⌝) (
        branch c-true [] (⌜ e′ ⌝ [ v-subst ← sub ]
                                 [ v-e ← ⌜ Exp.var y ⌝ ]
                                 [ v-y ← ⌜ y ⌝ ]) ∷
        branch c-false [] (const c-var (⌜ y ⌝ ∷ [])) ∷ [])  ≡⟨ remove-substs [] ⟩⟶

      case (equal-ℕ ⌜ x ⌝ ⌜ y ⌝) (
        branch c-true [] ⌜ e′ ⌝ ∷
        branch c-false [] (const c-var (⌜ y ⌝ ∷ [])) ∷ [])  ⇓⟨ var-lemma _ (x V.≟ y) (equal-ℕ-correct-ℕ-atoms x y) ⟩■

      ⌜ Exp.var y [ x ← e′ ] ⌝
      where
      var-lemma :
        (e : Exp) (b : Dec (x ≡ y)) →
        e ⇓ ⌜ Prelude.if b then true else false ⌝ →
        case e (
          branch c-true [] ⌜ e′ ⌝ ∷
          branch c-false [] (const c-var (⌜ y ⌝ ∷ [])) ∷ []) ⇓
        ⌜ Prelude.if b then e′ else var y ⌝
      var-lemma e (yes _) e⇓ =
        case e (
          branch c-true [] ⌜ e′ ⌝ ∷
          branch c-false [] (const c-var (⌜ y ⌝ ∷ [])) ∷ [])  ⟶⟨ case e⇓ here [] ⟩

        ⌜ e′ ⌝                                                ■⟨ rep-value e′ ⟩

      var-lemma e (no _) e⇓ =
        case e (
          branch c-true [] ⌜ e′ ⌝ ∷
          branch c-false [] (const c-var (⌜ y ⌝ ∷ [])) ∷ [])  ⟶⟨ case e⇓ (there (λ ()) here) [] ⟩

        ⌜ Exp.var y ⌝                                         ■⟨ rep-value (var y) ⟩

    case-Exp (const c es) =
      case ⌜ Exp.const c es ⌝
        (branches [ v-x ← ⌜ x ⌝ ]B⋆ [ v-new ← ⌜ e′ ⌝ ]B⋆
           [ v-subst ← sub ]B⋆ [ v-e ← ⌜ Exp.const c es ⌝ ]B⋆)  ⟶⟨ case (rep⇓rep (Exp.const c es))
                                                                     (there (λ ()) (there (λ ()) (there (λ ()) (there (λ ()) here))))
                                                                     (∷ ∷ []) ⟩
      const c-const (
        ⌜ c ⌝ ∷
        apply (sub [ v-e ← ⌜ Exp.const c es ⌝ ]
                   [ v-es ← ⌜ es ⌝ ]
                   [ v-c ← ⌜ c ⌝ ])
          (⌜ es ⌝ [ v-c ← ⌜ c ⌝ ]) ∷ [])                        ≡⟨ remove-substs ((sub , sub-closed) ∷ []) ⟩⟶

      const c-const (⌜ c ⌝ ∷ apply sub ⌜ es ⌝ ∷ [])             ⇓⟨ const (rep⇓rep c ∷ sub-Exps es ∷ []) ⟩■

      ⌜ Exp.const c es [ x ← e′ ] ⌝

    case-Exps :
      ∀ es →
      case ⌜ es ⌝
        (branches [ v-x ← ⌜ x ⌝ ]B⋆ [ v-new ← ⌜ e′ ⌝ ]B⋆
           [ v-subst ← sub ]B⋆ [ v-e ← ⌜ es ⌝ ]B⋆)
        ⇓
      ⌜ es [ x ← e′ ]⋆ ⌝
    case-Exps [] =
      case ⌜ [] ⦂ List Exp ⌝
        (branches [ v-x ← ⌜ x ⌝ ]B⋆ [ v-new ← ⌜ e′ ⌝ ]B⋆
           [ v-subst ← sub ]B⋆ [ v-e ← ⌜ [] ⦂ List Exp ⌝ ]B⋆)  ⟶⟨ case (rep⇓rep ([] ⦂ List Exp))
                                                                    (there (λ ()) (there (λ ()) (there (λ ()) (there (λ ()) (
                                                                     there (λ ()) (there (λ ()) (there (λ ()) here)))))))
                                                                    [] ⟩

      ⌜ [] [ x ← e′ ]⋆ ⌝                                       ■⟨ rep-value ([] ⦂ List Exp) ⟩

    case-Exps (e ∷ es) =
      case ⌜ e ∷ es ⌝
        (branches [ v-x ← ⌜ x ⌝ ]B⋆ [ v-new ← ⌜ e′ ⌝ ]B⋆
           [ v-subst ← sub ]B⋆ [ v-e ← ⌜ e ∷ es ⌝ ]B⋆)         ⟶⟨ case (rep⇓rep (e ∷ es))
                                                                    (there (λ ()) (there (λ ()) (there (λ ()) (there (λ ()) (
                                                                     there (λ ()) (there (λ ()) (there (λ ()) (there (λ ()) here))))))))
                                                                    (∷ ∷ []) ⟩

      const c-cons (
        apply (sub [ v-es ← ⌜ es ⌝ ] [ v-e ← ⌜ e ⌝ ]) ⌜ e ⌝ ∷
        apply (sub [ v-es ← ⌜ es ⌝ ] [ v-e ← ⌜ e ⌝ ])
          (⌜ es ⌝ [ v-e ← ⌜ e ⌝ ]) ∷
        [])                                                    ≡⟨ remove-substs ((sub , sub-closed) ∷ []) ⟩⟶

      const c-cons (apply sub ⌜ e ⌝ ∷ apply sub ⌜ es ⌝ ∷ [])   ⇓⟨ const (sub-Exp e ∷ sub-Exps es ∷ []) ⟩■

      ⌜ (e ∷ es) [ x ← e′ ]⋆ ⌝

    case-Br :
      ∀ b →
      case ⌜ b ⌝
        (branches [ v-x ← ⌜ x ⌝ ]B⋆ [ v-new ← ⌜ e′ ⌝ ]B⋆
           [ v-subst ← sub ]B⋆ [ v-e ← ⌜ b ⌝ ]B⋆)
        ⇓
      ⌜ b [ x ← e′ ]B ⌝
    case-Br (branch c ys e) =
      case ⌜ Br.branch c ys e ⌝
        (branches [ v-x ← ⌜ x ⌝ ]B⋆ [ v-new ← ⌜ e′ ⌝ ]B⋆
           [ v-subst ← sub ]B⋆ [ v-e ← ⌜ Br.branch c ys e ⌝ ]B⋆)        ⟶⟨ case (rep⇓rep (Br.branch c ys e))
                                                                             (there (λ ()) (there (λ ()) (there (λ ()) (there (λ ()) (
                                                                              there (λ ()) (there (λ ()) here))))))
                                                                             (∷ ∷ ∷ []) ⟩
      const c-branch (
        ⌜ c ⌝ ∷
        ⌜ ys ⌝ [ v-c ← ⌜ c ⌝ ] ∷
        case (member
                (⌜ x ⌝ [ v-new ← ⌜ e′ ⌝ ] [ v-subst ← sub ]
                   [ v-e ← ⌜ e ⌝ ] [ v-ys ← ⌜ ys ⌝ ] [ v-c ← ⌜ c ⌝ ])
                (⌜ ys ⌝ [ v-c ← ⌜ c ⌝ ])) (
          branch c-true [] (⌜ e ⌝ [ v-ys ← ⌜ ys ⌝ ] [ v-c ← ⌜ c ⌝ ]) ∷
          branch c-false [] (
            apply (sub [ v-e ← ⌜ e ⌝ ] [ v-ys ← ⌜ ys ⌝ ]
                     [ v-c ← ⌜ c ⌝ ])
              (⌜ e ⌝ [ v-ys ← ⌜ ys ⌝ ] [ v-c ← ⌜ c ⌝ ])) ∷
          []) ∷
        [])                                                             ≡⟨ remove-substs ((sub , sub-closed) ∷ []) ⟩⟶

      const c-branch (
        ⌜ c ⌝ ∷
        ⌜ ys ⌝ ∷
        case (member ⌜ x ⌝ ⌜ ys ⌝) (
          branch c-true [] ⌜ e ⌝ ∷
          branch c-false [] (apply sub ⌜ e ⌝) ∷
          []) ∷
        [])                                                             ⇓⟨ branch-lemma _ (V.member x ys) (member-correct x ys) ⟩■

      ⌜ Br.branch c ys e [ x ← e′ ]B ⌝
      where
      branch-lemma :
        (e″ : Exp) (b : Dec (x ∈ ys)) →
        e″ ⇓ ⌜ Prelude.if b then true else false ⌝ →
        const c-branch (
          ⌜ c ⌝ ∷
          ⌜ ys ⌝ ∷
          case e″ (
            branch c-true [] ⌜ e ⌝ ∷
            branch c-false [] (apply sub ⌜ e ⌝) ∷
            []) ∷
          []) ⇓
        ⌜ Prelude.if b
          then branch c ys e
          else branch c ys (e [ x ← e′ ]) ⌝
      branch-lemma e″ (yes _) e″⇓ =
        const c-branch (
          ⌜ c ⌝ ∷
          ⌜ ys ⌝ ∷
          case e″ (
            branch c-true [] ⌜ e ⌝ ∷
            branch c-false [] (apply sub ⌜ e ⌝) ∷
            []) ∷
          [])                                      ⇓⟨ const (rep⇓rep c ∷ rep⇓rep ys ∷
                                                             case e″⇓ here [] (rep⇓rep e) ∷ []) ⟩■
        ⌜ branch c ys e ⌝

      branch-lemma e″ (no _) e″⇓ =
        const c-branch (
          ⌜ c ⌝ ∷
          ⌜ ys ⌝ ∷
          case e″ (
            branch c-true [] ⌜ e ⌝ ∷
            branch c-false [] (apply sub ⌜ e ⌝) ∷
            []) ∷
          [])                                      ⇓⟨ const (rep⇓rep c ∷ rep⇓rep ys ∷
                                                             case e″⇓ (there (λ ()) here) [] (sub-Exp e) ∷ []) ⟩■
        ⌜ branch c ys (e [ x ← e′ ]) ⌝

    case-Brs :
      ∀ bs →
      case ⌜ bs ⌝
        (branches [ v-x ← ⌜ x ⌝ ]B⋆ [ v-new ← ⌜ e′ ⌝ ]B⋆
           [ v-subst ← sub ]B⋆ [ v-e ← ⌜ bs ⌝ ]B⋆)
        ⇓
      ⌜ bs [ x ← e′ ]B⋆ ⌝
    case-Brs [] =
      case ⌜ [] ⦂ List Br ⌝
        (branches [ v-x ← ⌜ x ⌝ ]B⋆ [ v-new ← ⌜ e′ ⌝ ]B⋆
           [ v-subst ← sub ]B⋆ [ v-e ← ⌜ [] ⦂ List Br ⌝ ]B⋆)  ⟶⟨ case (rep⇓rep ([] ⦂ List Br))
                                                                   (there (λ ()) (there (λ ()) (there (λ ()) (there (λ ()) (
                                                                    there (λ ()) (there (λ ()) (there (λ ()) here)))))))
                                                                   [] ⟩

      ⌜ [] [ x ← e′ ]B⋆ ⌝                                     ■⟨ rep-value ([] ⦂ List Br) ⟩

    case-Brs (b ∷ bs) =
      case ⌜ b ∷ bs ⌝
        (branches [ v-x ← ⌜ x ⌝ ]B⋆ [ v-new ← ⌜ e′ ⌝ ]B⋆
           [ v-subst ← sub ]B⋆ [ v-e ← ⌜ b ∷ bs ⌝ ]B⋆)         ⟶⟨ case (rep⇓rep (b ∷ bs))
                                                                    (there (λ ()) (there (λ ()) (there (λ ()) (there (λ ()) (
                                                                     there (λ ()) (there (λ ()) (there (λ ()) (there (λ ()) here))))))))
                                                                    (∷ ∷ []) ⟩

      const c-cons (
        apply (sub [ v-es ← ⌜ bs ⌝ ] [ v-e ← ⌜ b ⌝ ]) ⌜ b ⌝ ∷
        apply (sub [ v-es ← ⌜ bs ⌝ ] [ v-e ← ⌜ b ⌝ ])
          (⌜ bs ⌝ [ v-e ← ⌜ b ⌝ ]) ∷
        [])                                                    ≡⟨ remove-substs ((sub , sub-closed) ∷ []) ⟩⟶

      const c-cons (apply sub ⌜ b ⌝ ∷ apply sub ⌜ bs ⌝ ∷ [])   ⇓⟨ const (sub-Br b ∷ sub-Brs bs ∷ []) ⟩■

      ⌜ (b ∷ bs) [ x ← e′ ]B⋆ ⌝

-- Internal substitution is correct (part two).

internal-subst-correct₂ :
  ∀ {e x e′ v} →
  apply (apply (apply internal-subst ⌜ x ⌝) ⌜ e′ ⌝) ⌜ e ⌝ ⇓ v →
  v ≡ ⌜ e [ x ← e′ ] ⌝
internal-subst-correct₂ p =
  ⇓-deterministic p internal-subst-correct₁

private

  -- An auxiliary definition used in the implementation of
  -- internal-substs.

  body′ : Exp
  body′ =
    case (var v-xs) (
      branch c-nil [] (case (var v-es) (
        branch c-nil [] (var v-e′) ∷ [])) ∷
      branch c-cons (v-x ∷ v-xs ∷ []) (case (var v-es) (
        branch c-cons (v-e ∷ v-es ∷ []) (
          apply (apply (apply internal-subst (var v-x)) (var v-e))
            (apply (apply (apply (var v-substs) (var v-xs))
                      (var v-es))
               (var v-e′))) ∷
        [])) ∷
      [])

-- A program that tries to apply multiple substitutions.

internal-substs : Exp
internal-substs =
  rec v-substs (lambda v-xs (lambda v-es (lambda v-e′ body′)))

-- The program internal-substs is correctly implemented (part one).

internal-substs-correct₁ :
  ∀ {e xs es e′} →
  e [ xs ← es ]↦ e′ →
  apply (apply (apply internal-substs ⌜ xs ⌝) ⌜ es ⌝) ⌜ e ⌝ ⇓ ⌜ e′ ⌝
internal-substs-correct₁ {e = e} {xs = xs} {es = es} {e′ = e′} p =
  apply (apply (apply internal-substs ⌜ xs ⌝) ⌜ es ⌝) ⌜ e ⌝             ⟶⟨ apply (apply (apply (rec lambda) (rep⇓rep xs) lambda)
                                                                             (rep⇓rep es) lambda) (rep⇓rep e) ⟩
  case (⌜ xs ⌝ [ v-es ← ⌜ es ⌝ ] [ v-e′ ← ⌜ e ⌝ ]) (
    branch c-nil [] (case (⌜ es ⌝ [ v-e′ ← ⌜ e ⌝ ]) (
      branch c-nil [] ⌜ e ⌝ ∷ [])) ∷
    branch c-cons (v-x ∷ v-xs ∷ []) (case (⌜ es ⌝ [ v-e′ ← ⌜ e ⌝ ]) (
      branch c-cons (v-e ∷ v-es ∷ []) (
        apply (apply (apply internal-subst (var v-x)) (var v-e))
          (apply (apply (apply internal-substs (var v-xs)) (var v-es))
             ⌜ e ⌝)) ∷
      [])) ∷
    [])                                                                 ≡⟨ remove-substs [] ⟩⟶

  case ⌜ xs ⌝ (
    branch c-nil [] (case ⌜ es ⌝ (
      branch c-nil [] ⌜ e ⌝ ∷ [])) ∷
    branch c-cons (v-x ∷ v-xs ∷ []) (case ⌜ es ⌝ (
      branch c-cons (v-e ∷ v-es ∷ []) (
        apply (apply (apply internal-subst (var v-x)) (var v-e))
          (apply (apply (apply internal-substs (var v-xs)) (var v-es))
             ⌜ e ⌝)) ∷
      [])) ∷
    [])                                                                 ⇓⟨ lemma e xs es e′ p ⟩■

  ⌜ e′ ⌝
  where
  lemma :
    ∀ e xs es e′ →
    e [ xs ← es ]↦ e′ →
    case ⌜ xs ⌝ (
      branch c-nil [] (case ⌜ es ⌝ (
        branch c-nil [] ⌜ e ⌝ ∷ [])) ∷
      branch c-cons (v-x ∷ v-xs ∷ []) (case ⌜ es ⌝ (
        branch c-cons (v-e ∷ v-es ∷ []) (
          apply (apply (apply internal-subst (var v-x)) (var v-e))
            (apply (apply (apply internal-substs (var v-xs)) (var v-es))
               ⌜ e ⌝)) ∷
        [])) ∷
      []) ⇓
    ⌜ e′ ⌝
  lemma e [] [] .e [] =
    case ⌜ [] ⦂ List Var ⌝ (
      branch c-nil [] (case ⌜ [] ⦂ List Exp ⌝ (
        branch c-nil [] ⌜ e ⌝ ∷ [])) ∷
      branch c-cons (v-x ∷ v-xs ∷ []) (case ⌜ [] ⦂ List Exp ⌝ (
        branch c-cons (v-e ∷ v-es ∷ []) (
          apply (apply (apply internal-subst (var v-x)) (var v-e))
            (apply (apply (apply internal-substs (var v-xs)) (var v-es))
               ⌜ e ⌝)) ∷
        [])) ∷
      [])                                                                 ⟶⟨ case (rep⇓rep ([] ⦂ List Var)) here [] ⟩

    case ⌜ [] ⦂ List Exp ⌝ (
      branch c-nil [] ⌜ e ⌝ ∷ [])                                         ⇓⟨ case (rep⇓rep ([] ⦂ List Exp)) here [] (rep⇓rep e) ⟩■

    ⌜ e ⌝

  lemma e (x ∷ xs) (e′ ∷ es′) .(e″ [ x ← e′ ]) (∷_ {e″ = e″} p) =
    case ⌜ x ∷ xs ⌝ (
      branch c-nil [] (case ⌜ e′ ∷ es′ ⌝ (
        branch c-nil [] ⌜ e ⌝ ∷ [])) ∷
      branch c-cons (v-x ∷ v-xs ∷ []) (case ⌜ e′ ∷ es′ ⌝ (
        branch c-cons (v-e ∷ v-es ∷ []) (
          apply (apply (apply internal-subst (var v-x)) (var v-e))
            (apply (apply (apply internal-substs (var v-xs)) (var v-es))
               ⌜ e ⌝)) ∷
        [])) ∷
      [])                                                                 ⟶⟨ case (rep⇓rep (x ∷ xs)) (there (λ ()) here) (∷ ∷ []) ⟩

    case (⌜ e′ ∷ es′ ⌝ [ v-xs ← ⌜ xs ⌝ ] [ v-x ← ⌜ x ⌝ ]) (
      branch c-cons (v-e ∷ v-es ∷ []) (
        apply (apply (apply internal-subst ⌜ x ⌝) (var v-e))
          (apply (apply (apply internal-substs (⌜ xs ⌝ [ v-x ← ⌜ x ⌝ ]))
                    (var v-es))
             (⌜ e ⌝ [ v-xs ← ⌜ xs ⌝ ] [ v-x ← ⌜ x ⌝ ]))) ∷
      [])                                                                 ≡⟨ remove-substs [] ⟩⟶

    case ⌜ e′ ∷ es′ ⌝ (
      branch c-cons (v-e ∷ v-es ∷ []) (
        apply (apply (apply internal-subst ⌜ x ⌝) (var v-e))
          (apply (apply (apply internal-substs ⌜ xs ⌝) (var v-es))
             ⌜ e ⌝)) ∷
      [])                                                                 ⟶⟨ case (rep⇓rep (e′ ∷ es′)) here (∷ ∷ []) ⟩

    apply (apply (apply internal-subst
                    (⌜ x ⌝ [ v-es ← ⌜ es′ ⌝ ] [ v-e ← ⌜ e′ ⌝ ]))
             ⌜ e′ ⌝)
      (apply (apply (apply internal-substs
                       (⌜ xs ⌝ [ v-es ← ⌜ es′ ⌝ ] [ v-e ← ⌜ e′ ⌝ ]))
                (⌜ es′ ⌝ [ v-e ← ⌜ e′ ⌝ ]))
         (⌜ e ⌝ [ v-es ← ⌜ es′ ⌝ ] [ v-e ← ⌜ e′ ⌝ ]))                     ≡⟨ remove-substs [] ⟩⟶

    apply (apply (apply internal-subst ⌜ x ⌝) ⌜ e′ ⌝)
      (apply (apply (apply internal-substs ⌜ xs ⌝) ⌜ es′ ⌝) ⌜ e ⌝)        ⟶⟨ []⇓ (apply→ ∙) (internal-substs-correct₁ p) ⟩

    apply (apply (apply internal-subst ⌜ x ⌝) ⌜ e′ ⌝) ⌜ e″ ⌝              ⇓⟨ internal-subst-correct₁ ⟩■

    ⌜ e″ [ x ← e′ ] ⌝

-- The program internal-substs is correctly implemented (part two).

internal-substs-correct₂ :
  ∀ {e xs es v} →
  apply (apply (apply internal-substs ⌜ xs ⌝) ⌜ es ⌝) ⌜ e ⌝ ⇓ v →
  ∃ λ e′ → e [ xs ← es ]↦ e′ × v ≡ ⌜ e′ ⌝
internal-substs-correct₂ {e = e} {xs = xs} {es = es} {v = v}
  (apply {v₂ = v₃}
     (apply {v₂ = v₂}
        (apply {v₂ = v₁} (rec lambda) ⌜xs⌝⇓v₁ lambda)
        ⌜es⌝⇓v₂
        lambda)
     ⌜e⌝⇓v₃ p) =
  lemma e xs es v (
    case ⌜ xs ⌝ (
      branch c-nil [] (case ⌜ es ⌝ (
        branch c-nil [] ⌜ e ⌝ ∷ [])) ∷
      branch c-cons (v-x ∷ v-xs ∷ []) (case ⌜ es ⌝ (
        branch c-cons (v-e ∷ v-es ∷ []) (
          apply (apply (apply internal-subst (var v-x)) (var v-e))
            (apply (apply (apply internal-substs (var v-xs)) (var v-es))
               ⌜ e ⌝)) ∷
        [])) ∷
      [])                                                                 ≡⟨ sym $ remove-substs [] ⟩⟶

    case (⌜ xs ⌝ [ v-es ← ⌜ es ⌝ ] [ v-e′ ← ⌜ e ⌝ ]) (
      branch c-nil [] (case (⌜ es ⌝ [ v-e′ ← ⌜ e ⌝ ]) (
        branch c-nil [] ⌜ e ⌝ ∷ [])) ∷
      branch c-cons (v-x ∷ v-xs ∷ []) (case (⌜ es ⌝ [ v-e′ ← ⌜ e ⌝ ]) (
        branch c-cons (v-e ∷ v-es ∷ []) (
          apply (apply (apply internal-subst (var v-x)) (var v-e))
            (apply (apply (apply internal-substs (var v-xs)) (var v-es))
               ⌜ e ⌝)) ∷
        [])) ∷
      [])                                                                 ≡⟨⟩⟶

    body′ [ v-substs ← internal-substs ] [ v-xs ← ⌜ xs ⌝ ]
      [ v-es ← ⌜ es ⌝ ] [ v-e′ ← ⌜ e ⌝ ]                                  ≡⟨ trans
                                                                               (cong (λ xs → body′ [ v-substs ← internal-substs ]
                                                                                        [ v-xs ← xs ] [ v-es ← ⌜ es ⌝ ] [ v-e′ ← ⌜ e ⌝ ]) $
                                                                                rep⇓≡rep xs ⌜xs⌝⇓v₁)
                                                                               (cong₂ (λ es e → body′ [ v-substs ← internal-substs ]
                                                                                         [ v-xs ← v₁ ] [ v-es ← es ] [ v-e′ ← e ])
                                                                                  (rep⇓≡rep es ⌜es⌝⇓v₂)
                                                                                  (rep⇓≡rep e ⌜e⌝⇓v₃))  ⟩⟶
    body′ [ v-substs ← internal-substs ] [ v-xs ← v₁ ] [ v-es ← v₂ ]
      [ v-e′ ← v₃ ]                                                       ⇓⟨ p ⟩■

    v)
  where
  lemma :
    ∀ e xs es v →
    case ⌜ xs ⌝ (
      branch c-nil [] (case ⌜ es ⌝ (
        branch c-nil [] ⌜ e ⌝ ∷ [])) ∷
      branch c-cons (v-x ∷ v-xs ∷ []) (case ⌜ es ⌝ (
        branch c-cons (v-e ∷ v-es ∷ []) (
          apply (apply (apply internal-subst (var v-x)) (var v-e))
            (apply (apply (apply internal-substs (var v-xs)) (var v-es))
               ⌜ e ⌝)) ∷
        [])) ∷
      []) ⇓
    v →
    ∃ λ e′ → e [ xs ← es ]↦ e′ × v ≡ ⌜ e′ ⌝
  lemma _ [] (_ ∷ _) _ (case _ here [] (case _ (there _ ()) _ _))
  lemma _ [] _ _ (case (const []) (there _ (there _ ())) _ _)
  lemma _ _ [] _
    (case _ (there _ here) (∷ ∷ []) (case _ (there _ ()) _ _))

  lemma e [] [] v
    (case (const []) here [] (case (const []) here [] ⌜e⌝⇓v)) =
    e , [] , sym (rep⇓≡rep e ⌜e⌝⇓v)

  lemma e (x ∷ xs) (e′ ∷ es′) v
    (case (const (_∷_ {v = x′} ⌜x⌝⇓x′ (_∷_ {v = xs′} ⌜xs⌝⇓xs′ [])))
       (there _ here) (∷ ∷ [])
       (case (const (_∷_ {v = e″} ⌜e′⌝[xs←xs′][x←x′]⇓e″
                       (_∷_ {v = es″} ⌜es′⌝[xs←xs′][x←x′]⇓es″ [])))
          here (∷ ∷ []) p)) =
    lemma′ (
      apply (apply (apply internal-subst ⌜ x ⌝) ⌜ e′ ⌝)
        (apply (apply (apply internal-substs ⌜ xs ⌝) ⌜ es′ ⌝) ⌜ e ⌝)      ≡⟨ sym $ remove-substs [] ⟩⟶

      apply (apply (apply internal-subst
                      (⌜ x ⌝ [ v-es ← es″ ] [ v-e ← e″ ]))
               ⌜ e′ ⌝)
        (apply (apply (apply internal-substs
                         (⌜ xs ⌝ [ v-x ← x′ ] [ v-es ← es″ ]
                            [ v-e ← e″ ]))
                  (⌜ es′ ⌝ [ v-e ← e″ ]))
           (⌜ e ⌝ [ v-xs ← xs′ ] [ v-x ← x′ ]
              [ v-es ← es″ ] [ v-e ← e″ ]))                               ≡⟨ cong₂ apply
                                                                               (cong₂ (λ x e′ → apply
                                                                                         (apply internal-subst (x [ v-es ← es″ ] [ v-e ← e″ ])) e′)
                                                                                  (rep⇓≡rep x ⌜x⌝⇓x′)
                                                                                  (rep⇓≡rep e′ ⌜e′⌝⇓e″))
                                                                               (cong (flip Exp.apply _) $
                                                                                cong₂ (λ xs es′ → apply
                                                                                         (apply internal-substs
                                                                                            (xs [ v-x ← x′ ] [ v-es ← es″ ] [ v-e ← e″ ]))
                                                                                         (es′ [ v-e ← e″ ]))
                                                                                  (rep⇓≡rep xs ⌜xs⌝⇓xs′)
                                                                                  (rep⇓≡rep es′ ⌜es′⌝⇓es″)) ⟩⟶
      apply (apply (apply internal-subst
                      (x′ [ v-es ← es″ ] [ v-e ← e″ ]))
               e″)
        (apply (apply (apply internal-substs
                         (xs′ [ v-x ← x′ ] [ v-es ← es″ ] [ v-e ← e″ ]))
                  (es″ [ v-e ← e″ ]))
           (⌜ e ⌝ [ v-xs ← xs′ ] [ v-x ← x′ ]
              [ v-es ← es″ ] [ v-e ← e″ ]))                               ⇓⟨ p ⟩■

      v)
    where
    ⌜e′⌝⇓e″ : ⌜ e′ ⌝ ⇓ e″
    ⌜e′⌝⇓e″ =
      ⌜ e′ ⌝                              ≡⟨ sym $ remove-substs [] ⟩⟶
      ⌜ e′ ⌝ [ v-xs ← xs′ ] [ v-x ← x′ ]  ⇓⟨ ⌜e′⌝[xs←xs′][x←x′]⇓e″ ⟩■
      e″

    ⌜es′⌝⇓es″ : ⌜ es′ ⌝ ⇓ es″
    ⌜es′⌝⇓es″ =
      ⌜ es′ ⌝                              ≡⟨ sym $ remove-substs [] ⟩⟶
      ⌜ es′ ⌝ [ v-xs ← xs′ ] [ v-x ← x′ ]  ⇓⟨ ⌜es′⌝[xs←xs′][x←x′]⇓es″ ⟩■
      es″

    lemma′ :
      apply (apply (apply internal-subst ⌜ x ⌝) ⌜ e′ ⌝)
        (apply (apply (apply internal-substs ⌜ xs ⌝) ⌜ es′ ⌝) ⌜ e ⌝) ⇓
      v →
      ∃ λ e″ → e [ x ∷ xs ← e′ ∷ es′ ]↦ e″ × v ≡ ⌜ e″ ⌝
    lemma′ (apply {v₂ = v″} p₁ p₂ p₃) =
      case internal-substs-correct₂ p₂ of λ where
        (e″ , e[xs←es′]↦e″ , v″≡⌜e″⌝) →
          let p = apply (apply (apply internal-subst ⌜ x ⌝) ⌜ e′ ⌝)
                    ⌜ e″ ⌝                                              ≡⟨ cong (apply _) $ sym v″≡⌜e″⌝ ⟩⟶

                  apply (apply (apply internal-subst ⌜ x ⌝) ⌜ e′ ⌝) v″  ⇓⟨ apply p₁ (values-compute-to-themselves $ ⇓-Value p₂) p₃ ⟩■

                  v
          in
            e″ [ x ← e′ ]
          , ∷ e[xs←es′]↦e″
          , (v                  ≡⟨ internal-subst-correct₂ p ⟩∎
             ⌜ e″ [ x ← e′ ] ⌝  ∎)
