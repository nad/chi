------------------------------------------------------------------------
-- Rice's theorem
------------------------------------------------------------------------

open import Equality.Propositional
open import Prelude hiding (const; Decidable)

-- To simplify the development, let's work with actual natural numbers
-- as variables and constants (see
-- Atom.one-can-restrict-attention-to-χ-ℕ-atoms).

open import Atom

open import Chi            χ-ℕ-atoms
open import Coding         χ-ℕ-atoms
open import Free-variables χ-ℕ-atoms

import Coding.Instances.Nat

-- The theorem is stated and proved under the assumption that a
-- correct self-interpreter can be implemented.

module Rices-theorem
  (eval : Exp)
  (cl-eval : Closed eval)
  (eval₁ : ∀ p v → Closed p → p ⇓ v → apply eval ⌜ p ⌝ ⇓ ⌜ v ⌝)
  (eval₂ : ∀ p v → Closed p → apply eval ⌜ p ⌝ ⇓ v →
           ∃ λ v′ → p ⇓ v′ × v ≡ ⌜ v′ ⌝)
  where

open import H-level.Truncation.Propositional as Trunc hiding (rec)
open import Logical-equivalence using (_⇔_)
open import Tactic.By.Propositional

open import Double-negation equality-with-J
open import Equality.Decision-procedures equality-with-J
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import Monad equality-with-J

open import Cancellation  χ-ℕ-atoms
open import Compatibility χ-ℕ-atoms
open import Computability χ-ℕ-atoms hiding (_∘_)
open import Constants     χ-ℕ-atoms
open import Deterministic χ-ℕ-atoms
open import Propositional χ-ℕ-atoms
open import Reasoning     χ-ℕ-atoms
open import Termination   χ-ℕ-atoms
open import Values        χ-ℕ-atoms

open χ-atoms χ-ℕ-atoms

open import Combinators as χ hiding (id; if_then_else_)
open import Free-variables.Remove-substs
open import Halting-problem
open import Internal-coding

------------------------------------------------------------------------
-- The theorem

-- Definition of "pointwise semantically equivalent".

Pointwise-semantically-equivalent : Closed-exp → Closed-exp → Type
Pointwise-semantically-equivalent e₁ e₂ =
  ∀ e v → semantics [ apply-cl e₁ e ]= v ⇔
          semantics [ apply-cl e₂ e ]= v

-- This relation is symmetric.

symmetric :
  ∀ e₁ e₂ →
  Pointwise-semantically-equivalent e₁ e₂ →
  Pointwise-semantically-equivalent e₂ e₁
symmetric _ _ eq = λ e v → inverse (eq e v)

-- Rice's theorem.

module _
  (P : Closed-exp →Bool)
  (let P′ = proj₁ P)
  (e∈ : Closed-exp)
  (Pe∈ : P′ [ e∈ ]= true)
  (e∉ : Closed-exp)
  (¬Pe∉ : P′ [ e∉ ]= false)
  (resp : ∀ e₁ e₂ {b} →
          Pointwise-semantically-equivalent e₁ e₂ →
          P′ [ e₁ ]= b → P′ [ e₂ ]= b)
  where

  private

    module Helper
      (p : Exp) (cl-p : Closed p)
      (hyp : ∀ e b → P′ [ e ]= b → apply p ⌜ e ⌝ ⇓ ⌜ b ⌝)
      where

      arg : Closed-exp → Closed-exp → Closed-exp
      arg e p =
          lambda v-x
            (apply (lambda v-underscore (apply (proj₁ e) (var v-x)))
                   (apply eval (proj₁ p)))
        , (Closed′-closed-under-lambda $
           Closed′-closed-under-apply
             (Closed′-closed-under-lambda $
              Closed′-closed-under-apply
                (Closed→Closed′ $ proj₂ e)
                (Closed′-closed-under-var (inj₂ (inj₁ refl))))
             (Closed′-closed-under-apply
                (Closed→Closed′ cl-eval)
                (Closed→Closed′ (proj₂ p))))

      coded-arg : Closed-exp → Exp
      coded-arg e =
        const c-lambda (⌜ v-x ⌝ ∷
          const c-apply (
            ⌜ Exp.lambda v-underscore (apply (proj₁ e) (var v-x)) ⌝ ∷
            const c-apply (
              ⌜ eval ⌝ ∷
              apply internal-code (var v-p) ∷
              []) ∷ []) ∷ [])

      branches : List Br
      branches =
        branch c-false [] (apply p (coded-arg e∈)) ∷
        branch c-true  [] (χ.not (apply p (coded-arg e∉))) ∷
        []

      const-loop : Closed-exp
      const-loop =
          lambda v-underscore loop
        , (Closed′-closed-under-lambda $
           Closed→Closed′ loop-closed)

      ⌜const-loop⌝ : Closed-exp
      ⌜const-loop⌝ = ⌜ proj₁ const-loop ⌝

      halts : Exp
      halts =
        lambda v-p (case (apply p (proj₁ ⌜const-loop⌝)) branches)

      cl-coded-arg : ∀ e → Closed′ (v-p ∷ []) (coded-arg e)
      cl-coded-arg e =
        Closed′-closed-under-const λ where
          _ (inj₂ (inj₂ ()))
          _ (inj₁ refl) →
            Closed→Closed′ (rep-closed v-x)
          _ (inj₂ (inj₁ refl)) →
            Closed′-closed-under-const λ where
              _ (inj₂ (inj₂ ()))
              _ (inj₁ refl) →
                Closed→Closed′ $
                rep-closed (Exp.lambda v-underscore (apply (proj₁ e) (var v-x)))
              _ (inj₂ (inj₁ refl)) →
                Closed′-closed-under-const λ where
                  _ (inj₂ (inj₂ ()))
                  _ (inj₁ refl) →
                    Closed→Closed′ $
                    rep-closed eval
                  _ (inj₂ (inj₁ refl)) →
                    Closed′-closed-under-apply
                      (Closed→Closed′ internal-code-closed)
                      (Closed′-closed-under-var (inj₁ refl))

      cl-halts : Closed halts
      cl-halts =
        Closed′-closed-under-lambda $
        Closed′-closed-under-case
          (Closed′-closed-under-apply
             (Closed→Closed′ cl-p)
             (Closed→Closed′ $ proj₂ ⌜const-loop⌝))
          (λ where
             (inj₁ refl)        →
               Closed′-closed-under-apply
                 (Closed→Closed′ cl-p)
                 (cl-coded-arg e∈)
             (inj₂ (inj₁ refl)) →
               not-closed $
               Closed′-closed-under-apply
                 (Closed→Closed′ cl-p)
                 (cl-coded-arg e∉)
             (inj₂ (inj₂ ())))

      coded-arg⇓⌜arg⌝ :
        (e p : Closed-exp) →
        coded-arg e [ v-p ← ⌜ p ⌝ ] ⇓ ⌜ arg e ⌜ p ⌝ ⌝
      coded-arg⇓⌜arg⌝ e p =
        coded-arg e [ v-p ← ⌜ p ⌝ ]                                    ≡⟨⟩⟶

        const c-lambda (⌜ v-x ⌝ ∷
          const c-apply (
            ⌜ Exp.lambda v-underscore (apply (proj₁ e) (var v-x)) ⌝
              [ v-p ← ⌜ p ⌝ ] ∷
            const c-apply (
              ⌜ eval ⌝ [ v-p ← ⌜ p ⌝ ] ∷
              apply (internal-code [ v-p ← ⌜ p ⌝ ]) ⌜ p ⌝ ∷
                []) ∷ []) ∷ [])                                        ≡⟨ remove-substs ((internal-code , internal-code-closed) ∷ []) ⟩⟶

        const c-lambda (⌜ v-x ⌝ ∷
          const c-apply (
            ⌜ Exp.lambda v-underscore (apply (proj₁ e) (var v-x)) ⌝ ∷
            const c-apply (
              ⌜ eval ⌝ ∷
              apply internal-code ⌜ p ⌝ ∷
                []) ∷ []) ∷ [])                                        ⟶⟨ []⇓ (const (there (here (const (there (here
                                                                                 (const (there (here ∙)))))))))
                                                                              (internal-code-correct (proj₁ p)) ⟩
        const c-lambda (⌜ v-x ⌝ ∷
          const c-apply (
            ⌜ Exp.lambda v-underscore (apply (proj₁ e) (var v-x)) ⌝ ∷
            const c-apply (
              ⌜ eval ⌝ ∷
              ⌜ ⌜ p ⌝ ⦂ Exp ⌝ ∷
                []) ∷ []) ∷ [])                                        ≡⟨⟩⟶

        ⌜ arg e ⌜ p ⌝ ⌝                                                ■⟨ rep-value (arg e ⌜ p ⌝) ⟩

      arg-lemma-⇓ :
        (e p : Closed-exp) →
        Terminates (proj₁ p) →
        Pointwise-semantically-equivalent (arg e ⌜ p ⌝) e
      arg-lemma-⇓ (e , cl-e) (p , cl-p) (vp , p⇓vp)
                  (e′ , cl-e′) (v , _) = record
        { to = λ where
            (apply {v₂ = ve′} lambda q₁
               (apply {v₂ = vp} lambda _
                  (apply {x = x} {e = e-body} {v₂ = ve″} q₂ q₃ q₄))) →

              apply e e′                                        ≡⟨ sym $ remove-substs ((e , cl-e) ∷ []) ⟩⟶

              apply (e [ v-x ← ve′ ] [ v-underscore ← vp ]) e′  ⟶⟨ apply q₂ q₁ ⟩

              e-body [ x ← ⟨ ve′ ⟩ ]                            ≡⟨ ⟨by⟩ (values-only-compute-to-themselves (⇓-Value q₁) (

                  ve′                                                    ≡⟨ sym $ remove-substs ((ve′ , closed⇓closed q₁ cl-e′) ∷ []) ⟩⟶
                  ve′ [ v-underscore ← vp ]                              ⇓⟨ q₃ ⟩■
                  ve″                                                    )) ⟩⟶

              e-body [ x ← ve″ ]                                ⇓⟨ q₄ ⟩■

              v
        ; from = λ where
            (apply {v₂ = ve′} q₁ q₂ q₃) →

              proj₁ (apply-cl (arg (e , cl-e) ⌜ p ⌝) (e′ , cl-e′))       ⟶⟨ apply lambda q₂ ⟩

              apply (lambda v-underscore (apply (e [ v-x ← ve′ ]) ve′))
                    (apply (eval [ v-x ← ve′ ]) (⌜ p ⌝ [ v-x ← ve′ ]))   ≡⟨ remove-substs ((e , cl-e) ∷ (eval , cl-eval) ∷ []) ⟩⟶

              apply (lambda v-underscore (apply e ve′))
                    (apply eval ⌜ p ⌝)                                   ⟶⟨ apply lambda (eval₁ p _ cl-p p⇓vp) ⟩

              apply (e [ v-underscore ← ⌜ vp ⌝ ])
                (ve′ [ v-underscore ← ⌜ vp ⌝ ])                          ≡⟨ remove-substs ((e , cl-e) ∷ (ve′ , closed⇓closed q₂ cl-e′) ∷ []) ⟩⟶

              apply e ve′                                                ⇓⟨ apply q₁ (values-compute-to-themselves (⇓-Value q₂)) q₃ ⟩■

              v
        }

      arg-lemma-⇓-true :
        (e : Closed-exp) →
        Terminates (proj₁ e) →
        P′ [ arg e∈ ⌜ e ⌝ ]= true
      arg-lemma-⇓-true e e⇓ =      $⟨ Pe∈ ⟩
        P′ [ e∈ ]= true            ↝⟨ resp _ _ (symmetric (arg e∈ ⌜ e ⌝) e∈ (arg-lemma-⇓ e∈ e e⇓)) ⟩□
        P′ [ arg e∈ ⌜ e ⌝ ]= true  □

      arg-lemma-⇓-false :
        (e : Closed-exp) →
        Terminates (proj₁ e) →
        P′ [ arg e∉ ⌜ e ⌝ ]= false
      arg-lemma-⇓-false e e⇓ =      $⟨ ¬Pe∉ ⟩
        P′ [ e∉ ]= false            ↝⟨ resp _ _ (symmetric (arg e∉ ⌜ e ⌝) e∉ (arg-lemma-⇓ e∉ e e⇓)) ⟩□
        P′ [ arg e∉ ⌜ e ⌝ ]= false  □

      arg-lemma-¬⇓′ :
        (e p : Closed-exp) →
        ¬ Terminates (proj₁ p) →
        Pointwise-semantically-equivalent (arg e ⌜ p ⌝) const-loop
      arg-lemma-¬⇓′ (e , cl-e) (p , cl-p) ¬p⇓
                    (e′ , cl-e′) (v , _) = record
        { to = λ where
            (apply {v₂ = ve′} lambda _ (apply {v₂ = vp} _ q _)) →
              ⊥-elim $ ¬p⇓ $ Σ-map id proj₁ $
                eval₂ p vp cl-p (
                  apply eval ⌜ p ⌝                                  ≡⟨ sym $ remove-substs ((eval , cl-eval) ∷ []) ⟩⟶
                  apply (eval [ v-x ← ve′ ]) (⌜ p ⌝ [ v-x ← ve′ ])  ⇓⟨ q ⟩■
                  vp)
        ; from = λ where
            (apply lambda _ loop⇓) → ⊥-elim $ ¬loop⇓ (_ , loop⇓)
        }

      arg-lemma-¬⇓ :
        ∀ {b} (e₀ e : Closed-exp) →
        ¬ Terminates (proj₁ e) →
        P′ [ const-loop ]= b →
        P′ [ arg e₀ ⌜ e ⌝ ]= b
      arg-lemma-¬⇓ {b} e₀ e ¬e⇓ =
        P′ [ const-loop ]= b    ↝⟨ resp _ _ (symmetric (arg e₀ ⌜ e ⌝) const-loop (arg-lemma-¬⇓′ e₀ e ¬e⇓)) ⟩□
        P′ [ arg e₀ ⌜ e ⌝ ]= b  □

      ∃Bool : Type
      ∃Bool = ∃ λ (b : Bool) →
                apply p (proj₁ ⌜const-loop⌝) ⇓ ⌜ b ⌝
                  ×
                P′ [ const-loop ]= b

      ¬¬∃ : ¬¬ ∃Bool
      ¬¬∃ =
        excluded-middle {A = P′ [ const-loop ]= true} >>= λ where
          (inj₁ P-const-loop) → return ( true
                                       , hyp const-loop true
                                           P-const-loop
                                       , P-const-loop
                                       )
          (inj₂ ¬P-const-loop) →
            proj₂ P const-loop >>= λ where
              (true  , P-const-loop)  → ⊥-elim (¬P-const-loop
                                                  P-const-loop)
              (false , ¬P-const-loop) →
                return ( false
                       , hyp const-loop false ¬P-const-loop
                       , ¬P-const-loop
                       )

      halts⇓-lemma :
        ∀ {v} →
        ∃Bool →
        (e : Closed-exp) →
        (P′ [ const-loop ]= false →
         apply p (⌜ arg e∈ ⌜ e ⌝ ⌝) ⇓ v) →
        (P′ [ const-loop ]= true →
         χ.not (apply p (⌜ arg e∉ ⌜ e ⌝ ⌝)) ⇓ v) →
        apply halts ⌜ e ⌝ ⇓ v
      halts⇓-lemma {v} ∃bool e e∈⇓v e∉⇓v =
        apply halts ⌜ e ⌝                                                 ⟶⟨ apply lambda (rep⇓rep e) ⟩

        case (apply (p [ v-p ← ⌜ e ⌝ ]) (proj₁ ⌜const-loop⌝))
          (branches [ v-p ← ⌜ e ⌝ ]B⋆)                                    ≡⟨ remove-substs ((p , cl-p) ∷ []) ⟩⟶

        case (apply p (proj₁ ⌜const-loop⌝)) (branches [ v-p ← ⌜ e ⌝ ]B⋆)  ⇓⟨ lemma ∃bool ⟩■

        v
        where
        lemma : ∃Bool → _
        lemma (true , p⌜const-loop⌝⇓true , P-const-loop) =
          case (apply p (proj₁ ⌜const-loop⌝)) (branches [ v-p ← ⌜ e ⌝ ]B⋆)  ⟶⟨ case p⌜const-loop⌝⇓true (there (λ ()) here) [] ⟩
          χ.not (apply (p [ v-p ← ⌜ e ⌝ ]) (coded-arg e∉ [ v-p ← ⌜ e ⌝ ]))  ≡⟨ remove-substs ((p , cl-p) ∷ []) ⟩⟶
          χ.not (apply p (coded-arg e∉ [ v-p ← ⌜ e ⌝ ]))                    ⟶⟨ []⇓ (case (apply→ ∙)) (coded-arg⇓⌜arg⌝ e∉ e) ⟩
          χ.not (apply p (⌜ arg e∉ ⌜ e ⌝ ⌝))                                ⇓⟨ e∉⇓v P-const-loop ⟩■
          v

        lemma (false , p⌜const-loop⌝⇓false , ¬P-const-loop) =
          case (apply p (proj₁ ⌜const-loop⌝)) (branches [ v-p ← ⌜ e ⌝ ]B⋆)  ⟶⟨ case p⌜const-loop⌝⇓false here [] ⟩
          apply (p [ v-p ← ⌜ e ⌝ ]) (coded-arg e∈ [ v-p ← ⌜ e ⌝ ])          ≡⟨ remove-substs ((p , cl-p) ∷ []) ⟩⟶
          apply p (coded-arg e∈ [ v-p ← ⌜ e ⌝ ])                            ⟶⟨ []⇓ (apply→ ∙) (coded-arg⇓⌜arg⌝ e∈ e) ⟩
          apply p (⌜ arg e∈ ⌜ e ⌝ ⌝)                                        ⇓⟨ e∈⇓v ¬P-const-loop ⟩■
          v

      ⇓-lemma :
        ∃Bool →
        (e : Closed-exp) →
        Terminates (proj₁ e) →
        apply halts ⌜ e ⌝ ⇓ ⌜ true ⦂ Bool ⌝
      ⇓-lemma ∃bool e e⇓ = halts⇓-lemma ∃bool e

          (λ _ →
             apply p (⌜ arg e∈ ⌜ e ⌝ ⌝)  ⇓⟨ hyp (arg e∈ ⌜ e ⌝) true (arg-lemma-⇓-true e e⇓) ⟩■
             ⌜ true ⦂ Bool ⌝)

          (λ _ →
             χ.not (apply p (⌜ arg e∉ ⌜ e ⌝ ⌝))  ⟶⟨ []⇓ (case ∙) (hyp (arg e∉ ⌜ e ⌝) false (arg-lemma-⇓-false e e⇓)) ⟩
             χ.not ⌜ false ⦂ Bool ⌝              ⇓⟨ not-correct false (rep⇓rep (false ⦂ Bool)) ⟩■
             ⌜ true ⦂ Bool ⌝)

      ¬⇓-lemma :
        ∃Bool →
        (e : Closed-exp) →
        ¬ Terminates (proj₁ e) →
        apply halts ⌜ e ⌝ ⇓ ⌜ false ⦂ Bool ⌝
      ¬⇓-lemma ∃bool e ¬e⇓ = halts⇓-lemma ∃bool e

          (λ ¬P-const-loop →
             apply p (⌜ arg e∈ ⌜ e ⌝ ⌝)  ⇓⟨ hyp (arg e∈ ⌜ e ⌝) false (arg-lemma-¬⇓ e∈ e ¬e⇓ ¬P-const-loop) ⟩■
             ⌜ false ⦂ Bool ⌝)

          (λ P-const-loop →
             χ.not (apply p (⌜ arg e∉ ⌜ e ⌝ ⌝))  ⟶⟨ []⇓ (case ∙) (hyp (arg e∉ ⌜ e ⌝) true (arg-lemma-¬⇓ e∉ e ¬e⇓ P-const-loop)) ⟩
             χ.not ⌜ true ⦂ Bool ⌝               ⇓⟨ not-correct true (rep⇓rep (true ⦂ Bool)) ⟩■
             ⌜ false ⦂ Bool ⌝)

  rice's-theorem : ¬ Decidable P
  rice's-theorem (p , cl-p , hyp , _) = ¬¬¬⊥ $
    ¬¬∃ >>= λ ∃bool →
    return (intensional-halting-problem₀
              ( halts
              , cl-halts
              , λ e cl-e → ⇓-lemma  ∃bool (e , cl-e)
                         , ¬⇓-lemma ∃bool (e , cl-e)
              ))
    where
    open Helper p cl-p hyp

-- A variant of the theorem.

rice's-theorem′ :
  (P : Closed-exp → Type)
  (e∈ : Closed-exp) →
  P e∈ →
  (e∉ : Closed-exp) →
  ¬ P e∉ →
  (∀ e₁ e₂ →
   Pointwise-semantically-equivalent e₁ e₂ →
   P e₁ → P e₂) →
  ¬ Decidable (as-function-to-Bool₁ P)
rice's-theorem′ P e∈ Pe∈ e∉ ¬Pe∉ resp =
  rice's-theorem
    (as-function-to-Bool₁ P)
    e∈
    ((λ _ → refl) , ⊥-elim ∘ (_$ Pe∈))
    e∉
    (⊥-elim ∘ ¬Pe∉ , (λ _ → refl))
    (λ e₁ e₂ eq →
       Σ-map (_∘ resp e₂ e₁ (symmetric e₁ e₂ eq))
             (_∘ (_∘ resp e₁ e₂ eq)))

------------------------------------------------------------------------
-- Examples

-- The problem of deciding whether an expression implements the
-- successor function is undecidable.

Equal-to-suc : Closed-exp →Bool
Equal-to-suc =
  as-function-to-Bool₁ λ e →
    (n : ℕ) → apply (proj₁ e) ⌜ n ⌝ ⇓ ⌜ suc n ⌝

equal-to-suc-not-decidable : ¬ Decidable Equal-to-suc
equal-to-suc-not-decidable =
  rice's-theorem′
    _
    (s , from-⊎ (closed? s))
    (λ n → apply lambda (rep⇓rep n) (rep⇓rep (suc n)))
    (z , from-⊎ (closed? z))
    (λ z⌜n⌝⇓ → case z⌜n⌝⇓ 0 of λ { (apply () _ _) })
    (λ e₁ e₂ e₁∼e₂ Pe₁ n →
       apply (proj₁ e₂) ⌜ n ⌝  ⇓⟨ _⇔_.to (e₁∼e₂ ⌜ n ⌝ ⌜ suc n ⌝) (Pe₁ n) ⟩■
       ⌜ suc n ⌝)
  where
  z = const c-zero []
  s = lambda v-n (const c-suc (var v-n ∷ []))

-- The problem of deciding whether an expression always terminates
-- with the same value when applied to an arbitrary argument is
-- undecidable.

Is-constant : Closed-exp →Bool
Is-constant = as-function-to-Bool₁ λ e →
  ∃ λ v → (n : ℕ) → apply (proj₁ e) ⌜ n ⌝ ⇓ v

is-constant-not-decidable : ¬ Decidable Is-constant
is-constant-not-decidable =
  rice's-theorem′
    _
    (c , from-⊎ (closed? c))
    ((⌜ 0 ⌝ ⦂ Exp) , λ n →
       apply c ⌜ n ⌝  ⇓⟨ apply lambda (rep⇓rep n) (const []) ⟩■
       ⌜ 0 ⌝)
    (f , from-⊎ (closed? f))
    not-constant
    (λ e₁ e₂ e₁∼e₂ → Σ-map id λ {v} ⇓v n →
       let v-closed : Closed v
           v-closed = closed⇓closed (⇓v n) $
                        Closed′-closed-under-apply
                          (proj₂ e₁)
                          (rep-closed n)
       in
       apply (proj₁ e₂) ⌜ n ⌝  ⇓⟨ _⇔_.to (e₁∼e₂ ⌜ n ⌝ (v , v-closed)) (⇓v n) ⟩■
       v)
  where
  c = lambda v-underscore ⌜ 0 ⌝
  f = lambda v-n (var v-n)

  not-constant : ¬ ∃ λ v → (n : ℕ) → apply f ⌜ n ⌝ ⇓ v
  not-constant (v  , constant) = impossible
    where
    v≡0 : v ≡ ⌜ 0 ⌝
    v≡0 with constant 0
    ... | apply lambda (const []) (const []) = refl

    v≡1 : v ≡ ⌜ 1 ⌝
    v≡1 with constant 1
    ... | apply lambda (const (const [] ∷ [])) (const (const [] ∷ [])) =
      refl

    0≡1 =
      ⌜ 0 ⌝  ≡⟨ sym v≡0 ⟩
      v      ≡⟨ v≡1 ⟩∎
      ⌜ 1 ⌝  ∎

    impossible : ⊥
    impossible with 0≡1
    ... | ()
