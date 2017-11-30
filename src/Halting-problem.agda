------------------------------------------------------------------------
-- The halting problem
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Halting-problem where

open import Equality.Propositional
open import H-level.Truncation.Propositional as Trunc hiding (rec)
open import Logical-equivalence using (_⇔_)
open import Prelude hiding (const; Decidable)
open import Tactic.By
open import Univalence-axiom

open import Equality.Decision-procedures equality-with-J
open import Function-universe equality-with-J hiding (id; _∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J

-- To simplify the development, let's work with actual natural numbers
-- as variables and constants (see
-- Atom.one-can-restrict-attention-to-χ-ℕ-atoms).

open import Atom

open import Cancellation   χ-ℕ-atoms
open import Chi            χ-ℕ-atoms
open import Coding         χ-ℕ-atoms hiding (id)
open import Compatibility  χ-ℕ-atoms
open import Computability  χ-ℕ-atoms hiding (_∘_)
open import Constants      χ-ℕ-atoms
open import Deterministic  χ-ℕ-atoms
open import Free-variables χ-ℕ-atoms
open import Propositional  χ-ℕ-atoms
open import Reasoning      χ-ℕ-atoms
open import Termination    χ-ℕ-atoms
open import Values         χ-ℕ-atoms

open χ-atoms χ-ℕ-atoms

import Coding.Instances.Nat
open import Combinators as χ hiding (if_then_else_)
open import Internal-coding

-- The extensional halting problem is undecidable.

extensional-halting-problem :
  ¬ ∃ λ halts →
      Closed halts
        ×
      ∀ p → Closed p →
        (Terminates p →
         apply halts (lambda v-underscore p) ⇓ code (true  ⦂ Bool))
          ×
        (¬ Terminates p →
         apply halts (lambda v-underscore p) ⇓ code (false ⦂ Bool))
extensional-halting-problem (halts , cl , hyp) = contradiction
  where
  terminv : Exp → Exp
  terminv p = χ.if apply halts (lambda v-underscore p)
              then loop
              else code zero

  terminv-lemma : ∀ {p} → Closed p →
                  Terminates (terminv p) ⇔ ¬ Terminates p
  terminv-lemma {p} cl-p = record { to = to; from = from }
    where
    to : Terminates (terminv p) → ¬ Terminates p
    to (_ , case _           (there _ (there _ ())) _  _) p⇓
    to (_ , case halts⇓false (there _ here)         [] _) p⇓ =
      C.distinct-codes→distinct-names (λ ()) $
        proj₁ $ cancel-const $
          ⇓-deterministic (proj₁ (hyp p cl-p) p⇓) halts⇓false
    to (_ , case _ here [] loop⇓) p⇓ = ¬loop⇓ (_ , loop⇓)

    from : ¬ Terminates p → Terminates (terminv p)
    from ¬p⇓ =
      _ , case (proj₂ (hyp p cl-p) ¬p⇓) (there lemma here) [] (const [])
      where
      lemma = C.distinct-codes→distinct-names (λ ())

  strange : Exp
  strange = rec v-p (terminv (var v-p))

  strange-closed : Closed strange
  strange-closed =
    Closed′-closed-under-rec $
    if-then-else-closed
      (Closed′-closed-under-apply
         (Closed→Closed′ cl)
         (Closed′-closed-under-lambda
            (Closed′-closed-under-var (inj₂ (inj₁ refl)))))
      (Closed→Closed′ loop-closed)
      (Closed→Closed′ $ code-closed zero)

  subst-lemma : terminv (var v-p) [ v-p ← strange ] ≡ terminv strange
  subst-lemma =
    terminv (var v-p) [ v-p ← strange ]                ≡⟨⟩

    χ.if apply (halts [ v-p ← strange ])
               (lambda v-underscore strange)
    then loop else code zero                           ≡⟨ by (subst-closed _ _ cl) ⟩

    χ.if apply halts (lambda v-underscore strange)
    then loop else code zero                           ≡⟨⟩

    terminv strange                                    ∎

  strange-lemma : Terminates strange ⇔ ¬ Terminates strange
  strange-lemma =
    Terminates strange                                ↝⟨ record { to   = λ { (_ , rec p) → _ , p }
                                                                ; from = Σ-map _ rec
                                                                } ⟩
    Terminates (terminv (var v-p) [ v-p ← strange ])  ↔⟨ ≡⇒↝ bijection (by subst-lemma) ⟩
    Terminates (terminv strange)                      ↝⟨ terminv-lemma strange-closed ⟩
    ¬ Terminates strange                              □

  contradiction : ⊥
  contradiction = ¬[⇔¬] strange-lemma

-- A variant of the statement above.

extensional-halting-problem′ :
  ¬ ∃ λ halts →
      Closed halts
        ×
      ∀ p → Closed p →
        ∃ λ (b : Bool) →
          apply halts (lambda v-underscore p) ⇓ code b
            ×
          if b then Terminates p else (¬ Terminates p)
extensional-halting-problem′ (halts , cl , hyp) =
  extensional-halting-problem
    ( halts
    , cl
    , λ _ cl-p → ⇓→⇓true   cl-p
               , ¬⇓→⇓false cl-p
    )
  where
  ⇓→⇓true : ∀ {p} → Closed p → Terminates p →
            apply halts (lambda v-underscore p) ⇓ code (true ⦂ Bool)
  ⇓→⇓true {p} cl p⇓ with hyp p cl
  ... | true ,  halts⇓true , _   = halts⇓true
  ... | false , _          , ¬p⇓ = ⊥-elim (¬p⇓ p⇓)

  ¬⇓→⇓false :
    ∀ {p} → Closed p → ¬ Terminates p →
    apply halts (lambda v-underscore p) ⇓ code (false ⦂ Bool)
  ¬⇓→⇓false {p} cl ¬p⇓ with hyp p cl
  ... | false ,  halts⇓false , _  = halts⇓false
  ... | true  , _            , p⇓ = ⊥-elim (¬p⇓ p⇓)

-- And another variant.

extensional-halting-problem″ :
  ¬ ∃ λ halts →
      Closed halts
        ×
      ∀ p → Closed p →
        ∥ (∃ λ (b : Bool) →
             apply halts (lambda v-underscore p) ⇓ code b
               ×
             if b then Terminates p else (¬ Terminates p)) ∥
extensional-halting-problem″ (halts , cl , hyp) =
  extensional-halting-problem
    ( halts
    , cl
    , λ _ cl-p → ⇓→⇓true cl-p , ¬⇓→⇓false cl-p
    )
  where
  ⇓→⇓true : ∀ {p} → Closed p → Terminates p →
            apply halts (lambda v-underscore p) ⇓ code (true ⦂ Bool)
  ⇓→⇓true cl p⇓ =
    flip (Trunc.rec ⇓-propositional) (hyp _ cl) λ where
      (false , _          , ¬p⇓) → ⊥-elim (¬p⇓ p⇓)
      (true  , halts⇓true , _)   → halts⇓true

  ¬⇓→⇓false :
    ∀ {p} → Closed p → ¬ Terminates p →
    apply halts (lambda v-underscore p) ⇓ code (false ⦂ Bool)
  ¬⇓→⇓false cl ¬p⇓ =
    flip (Trunc.rec ⇓-propositional) (hyp _ cl) λ where
      (true  , _           , p⇓) → ⊥-elim (¬p⇓ p⇓)
      (false , halts⇓false , _)  → halts⇓false

-- The intensional halting problem of self-application. (This
-- definition is not used below.)

Intensional-halting-problem-of-self-application : Closed-exp →Bool
Intensional-halting-problem-of-self-application =
  as-function-to-Bool₁ (λ { (e , _) → Terminates (apply e (code e)) })

-- The intensional halting problem of self-application is not
-- decidable.

intensional-halting-problem-of-self-application :
  ¬ ∃ λ halts →
      Closed halts
        ×
      ∀ p → Closed p →
        (Terminates (apply p (code p)) →
           apply halts (code p) ⇓ code (true ⦂ Bool))
          ×
        (¬ Terminates (apply p (code p)) →
           apply halts (code p) ⇓ code (false ⦂ Bool))
intensional-halting-problem-of-self-application (halts , cl , hyp) =
  contradiction
  where
  self-apply : Exp → Exp
  self-apply p = apply p (code p)

  terminv : Exp
  terminv = lambda v-x
              (χ.if apply halts (var v-x)
               then loop
               else code zero)

  terminv-lemma : ∀ {p} → Closed p →
                  Terminates (apply terminv (code p))
                    ⇔
                  ¬ Terminates (self-apply p)
  terminv-lemma {p} cl-p = record { to = to; from = from }
    where
    to : Terminates (apply terminv (code p)) →
         ¬ Terminates (self-apply p)
    to (_ , apply lambda _ (case _ here [] loop⇓)) p⇓ =
      ¬loop⇓ (_ , loop⇓)

    to (_ , apply lambda _ (case _ (there _ (there _ ())) _  _)) p⇓

    to (_ , apply lambda code-p⇓
              (case halts⇓false′ (there _ here) [] _)) p⇓ =
      C.distinct-codes→distinct-names (λ ()) $
        proj₁ $ cancel-const $
          ⇓-deterministic (proj₁ (hyp p cl-p) p⇓) halts⇓false
      where
      halts⇓false : apply halts (code p) ⇓ code (false ⦂ Bool)
      halts⇓false rewrite code⇓≡code p code-p⇓ =
        subst (λ e → apply e _ ⇓ _)
              (subst-closed _ _ cl)
              halts⇓false′

    from : ¬ Terminates (self-apply p) →
           Terminates (apply terminv (code p))
    from ¬p⇓ =
      _ , apply lambda (code⇓code p)
            (case halts⇓false
                  (there (C.distinct-codes→distinct-names (λ ())) here)
                  []
                  (const []))
      where
      halts⇓false : apply (halts [ v-x ← code p ]) (code p) ⇓
                    code (false ⦂ Bool)
      halts⇓false =
        subst (λ e → apply e _ ⇓ _)
              (sym $ subst-closed _ _ cl)
              (proj₂ (hyp p cl-p) ¬p⇓)

  strange : Exp
  strange = self-apply terminv

  terminv-closed : Closed terminv
  terminv-closed =
    Closed′-closed-under-lambda $
    if-then-else-closed
      (Closed′-closed-under-apply
         (Closed→Closed′ cl)
         (Closed′-closed-under-var (inj₁ refl)))
      (Closed→Closed′ loop-closed)
      (Closed→Closed′ $ code-closed zero)

  strange-lemma : Terminates strange ⇔ ¬ Terminates strange
  strange-lemma = terminv-lemma terminv-closed

  contradiction : ⊥
  contradiction = ¬[⇔¬] strange-lemma

-- The intensional halting problem with one argument is not decidable.

intensional-halting-problem₁ :
  ¬ ∃ λ halts →
      Closed halts
        ×
      ∀ p x → Closed p → Closed x →
        (Terminates (apply p (code x)) →
           apply halts (code (p , x)) ⇓ code (true ⦂ Bool))
          ×
        (¬ Terminates (apply p (code x)) →
           apply halts (code (p , x)) ⇓ code (false ⦂ Bool))
intensional-halting-problem₁ (halts , cl , hyp) =
  intensional-halting-problem-of-self-application
    ( halts′
    , cl′
    , λ p cl-p → Σ-map (lemma p true ∘_) (lemma p false ∘_)
                       (hyp p p cl-p cl-p)
    )
  where
  arg    = const c-pair (var v-p ∷ var v-p ∷ [])
  halts′ = lambda v-p (apply halts arg)

  cl′ : Closed halts′
  cl′ =
    Closed′-closed-under-lambda $
    Closed′-closed-under-apply
      (Closed→Closed′ cl)
      (from-⊎ (closed′? arg (v-p ∷ [])))

  lemma : (p : Exp) (b : Bool) →
          apply halts (code (p , p)) ⇓ code b →
          apply halts′ (code p) ⇓ code b
  lemma p b halts⇓ =
    apply halts′ (code p)                          ⟶⟨ apply lambda (code⇓code p) ⟩
    apply (halts [ v-p ← code p ]) (code (p , p))  ≡⟨ by (subst-closed _ _ cl) ⟩⟶
    apply halts (code (p , p))                     ⇓⟨ halts⇓ ⟩■
    code b

-- The intensional halting problem with zero arguments is not
-- decidable.

intensional-halting-problem₀ :
  ¬ ∃ λ halts →
      Closed halts
        ×
      ∀ p → Closed p →
        (Terminates p → apply halts (code p) ⇓ code (true ⦂ Bool))
          ×
        (¬ Terminates p → apply halts (code p) ⇓ code (false ⦂ Bool))
intensional-halting-problem₀ (halts , cl , hyp) =
  intensional-halting-problem-of-self-application
    ( halts′
    , cl′
    , λ p cl-p → Σ-map (lemma p true ∘_) (lemma p false ∘_)
                       (hyp (apply p (code p))
                            (Closed′-closed-under-apply
                               (Closed→Closed′ cl-p)
                               (Closed→Closed′ (code-closed p))))
    )
  where
  halts′ =
    lambda v-p (apply halts (
       const c-apply (var v-p ∷ apply internal-code (var v-p) ∷ [])))

  cl′ : Closed halts′
  cl′ =
    Closed′-closed-under-lambda $
    Closed′-closed-under-apply
      (Closed→Closed′ cl)
      (Closed′-closed-under-const
         (λ { _ (inj₁ refl) →
                Closed′-closed-under-var (inj₁ refl)

            ; _ (inj₂ (inj₁ refl)) →
                Closed′-closed-under-apply
                  (Closed→Closed′ internal-code-closed)
                  (Closed′-closed-under-var (inj₁ refl))

            ; _ (inj₂ (inj₂ ()))
            }))

  abstract

    lemma : (p : Exp) (b : Bool) →
            apply halts (code (Exp.apply p (code p))) ⇓ code b →
            apply halts′ (code p) ⇓ code b
    lemma p b halts⇓ =
      apply halts′ (code p)                                              ⟶⟨ apply lambda (code⇓code p) ⟩

      apply (halts [ v-p ← code p ]) (const c-apply (
        code p ∷ apply (internal-code [ v-p ← code p ]) (code p) ∷ []))  ≡⟨ by (subst-closed _ _ cl) ⟩⟶

      apply halts (const c-apply (
        code p ∷ apply (internal-code [ v-p ← code p ]) (code p) ∷ []))  ≡⟨ by (subst-closed v-p (code p) internal-code-closed) ⟩⟶

      apply halts (const c-apply (
        code p ∷ apply internal-code (code p) ∷ []))                     ⟶⟨ []⇓ (apply→ ∙) (const (code⇓code p ∷ internal-code-correct p ∷ [])) ⟩

      apply halts (const c-apply (code p ∷ code (code p ⦂ Exp) ∷ []))    ⟶⟨⟩

      apply halts (code (Exp.apply p (code p)))                          ⇓⟨ halts⇓ ⟩■

      code b

-- Two statements of the intensional halting problem with zero
-- arguments.

Intensional-halting-problem₀₁ : Closed-exp →Bool
Intensional-halting-problem₀₁ =
  as-function-to-Bool₁ (Terminates ∘ proj₁)

Intensional-halting-problem₀₂ : Closed-exp →Bool
Intensional-halting-problem₀₂ =
  as-function-to-Bool₂ (Terminates ∘ proj₁) Terminates-propositional

-- The first variant is not decidable.

intensional-halting-problem₀₁ :
  ¬ Decidable Intensional-halting-problem₀₁
intensional-halting-problem₀₁ (halts , cl , hyp , _) =
  intensional-halting-problem₀
    ( halts
    , cl
    , λ p cl-p →
        (λ p⇓ →
           apply halts (code p)  ⇓⟨ hyp (p , cl-p) true ((λ _ → refl) , λ ¬p⇓ → ⊥-elim (¬p⇓ p⇓)) ⟩■
           code (true ⦂ Bool)) ,
        λ ¬p⇓ →
          apply halts (code p)  ⇓⟨ hyp (p , cl-p) false ((λ p⇓ → ⊥-elim (¬p⇓ p⇓)) , λ _ → refl) ⟩■
          code (false ⦂ Bool)
    )

-- The second variant is not decidable.

intensional-halting-problem₀₂ :
  ¬ Decidable Intensional-halting-problem₀₂
intensional-halting-problem₀₂ (halts , cl , hyp , _) =
  intensional-halting-problem₀
    ( halts
    , cl
    , λ p cl-p →
          (λ p⇓  →
             apply halts (code p)  ⇓⟨ hyp (p , cl-p) true (inj₁ (p⇓  , refl)) ⟩■
             code (true ⦂ Bool))
        , (λ ¬p⇓ →
             apply halts (code p)  ⇓⟨ hyp (p , cl-p) false (inj₂ (¬p⇓ , refl)) ⟩■
             code (false ⦂ Bool))
    )

-- Under the assumption of excluded middle one can prove that
-- Intensional-halting-problem₀₁ and Intensional-halting-problem₀₂ are
-- pointwise equal.

Intensional-halting-problem₀₂→Intensional-halting-problem₀₁ :
  ∀ {e b} →
  proj₁ Intensional-halting-problem₀₂ [ e ]= b →
  proj₁ Intensional-halting-problem₀₁ [ e ]= b
Intensional-halting-problem₀₂→Intensional-halting-problem₀₁
  (inj₁ (e⇓ , refl)) = (λ _ → refl) , (⊥-elim ∘ (_$ e⇓))
Intensional-halting-problem₀₂→Intensional-halting-problem₀₁
  (inj₂ (¬e⇓ , refl)) = (⊥-elim ∘ ¬e⇓) , λ _ → refl

Intensional-halting-problem₀₁→Intensional-halting-problem₀₂ :
  (excluded-middle : (P : Set) → Is-proposition P → Dec P) →
  ∀ {e} b →
  proj₁ Intensional-halting-problem₀₁ [ e ]= b →
  proj₁ Intensional-halting-problem₀₂ [ e ]= b
Intensional-halting-problem₀₁→Intensional-halting-problem₀₂ em =
  λ where
    true (_ , ¬¬e⇓) →
      inj₁ ( double-negation-elimination
               Terminates-propositional
               (Bool.true≢false ∘ ¬¬e⇓)
           , refl
           )
    false (¬e⇓ , _) →
      inj₂ ( Bool.true≢false ∘ sym ∘ ¬e⇓
           , refl
           )
  where
  double-negation-elimination :
    {P : Set} → Is-proposition P → ¬ ¬ P → P
  double-negation-elimination P-prop ¬¬p =
    case em _ P-prop of λ where
      (inj₁ p)  → p
      (inj₂ ¬p) → ⊥-elim (¬¬p ¬p)

-- If a (correct) self-interpreter can be implemented, then "half of
-- the halting problem" is computable.

half-of-the-halting-problem :
  (eval : Exp) →
  Closed eval →
  (∀ p v → Closed p → p ⇓ v → apply eval (code p) ⇓ code v) →
  (∀ p → Closed p → ¬ Terminates p →
     ¬ Terminates (apply eval (code p))) →
  ∃ λ halts →
      Closed halts
        ×
      ∀ p → Closed p →
        (Terminates p → apply halts (code p) ⇓ code (true ⦂ Bool))
          ×
        (¬ Terminates p → ¬ Terminates (apply halts (code p)))
half-of-the-halting-problem eval cl eval⇓ eval¬⇓ =
  halts , cl′ , λ p cl-p → lemma₁ p cl-p , lemma₂ p cl-p
  module Half-of-the-halting-problem where
  halts = lambda v-p (apply (lambda v-underscore (code (true ⦂ Bool)))
                            (apply eval (var v-p)))

  cl′ : Closed halts
  cl′ =
    Closed′-closed-under-lambda $
    Closed′-closed-under-apply
      (from-⊎ (closed′? (lambda v-underscore (code (true ⦂ Bool))) _))
      (Closed′-closed-under-apply
        (Closed→Closed′ cl)
        (Closed′-closed-under-var (inj₁ refl)))

  lemma₁ : ∀ p → Closed p → Terminates p →
           apply halts (code p) ⇓ code (true ⦂ Bool)
  lemma₁ p cl-p (v , p⇓v) =
    apply halts (code p)                             ⟶⟨ apply lambda (code⇓code p) ⟩

    apply (lambda v-underscore (code (true ⦂ Bool)))
          (apply (eval [ v-p ← code p ]) (code p))   ≡⟨ by (subst-closed _ _ cl) ⟩⟶

    apply (lambda v-underscore (code (true ⦂ Bool)))
          (apply eval (code p))                      ⇓⟨ apply lambda (eval⇓ p v cl-p p⇓v) (code⇓code (true ⦂ Bool)) ⟩■

    code (true ⦂ Bool)

  halts-eval-inversion :
    ∀ e →
    Terminates (apply halts e) →
    Terminates (apply eval e)
  halts-eval-inversion e (_ , apply {v₂ = v} lambda e⇓
                           (apply {v₂ = v₂} _ eval⇓ _)) =
    _ , (apply eval e                ⟶⟨ []⇓ (apply→ ∙) e⇓ ⟩
         apply eval v                ≡⟨ by (subst-closed _ _ cl) ⟩⟶
         apply (eval [ v-p ← v ]) v  ⇓⟨ eval⇓ ⟩■
         v₂)

  lemma₂ : ∀ p → Closed p →
           ¬ Terminates p →
           ¬ Terminates (apply halts (code p))
  lemma₂ p cl-p ¬p⇓ =
    Terminates (apply halts (code p))  ↝⟨ halts-eval-inversion (code p) ⟩
    Terminates (apply eval (code p))   ↝⟨ eval¬⇓ p cl-p ¬p⇓ ⟩□
    ⊥                                  □

-- Two statements of "half of the halting problem".

Half-of-the-halting-problem₁ : Closed-exp ⇀ Bool
Half-of-the-halting-problem₁ =
  as-partial-function-to-Bool₁ (Terminates ∘ proj₁)

Half-of-the-halting-problem₂ : Closed-exp ⇀ Bool
Half-of-the-halting-problem₂ =
  as-partial-function-to-Bool₂
    (Terminates ∘ proj₁)
    Terminates-propositional

-- If a (correct) self-interpreter can be implemented, then
-- Half-of-the-halting-problem₂ is computable.

half-of-the-halting-problem₂ :
  (eval : Exp) →
  Closed eval →
  (∀ p v → Closed p → p ⇓ v → apply eval (code p) ⇓ code v) →
  (∀ p v → Closed p → apply eval (code p) ⇓ v →
     ∃ λ v′ → p ⇓ v′ × v ≡ code v′) →
  Computable Half-of-the-halting-problem₂
half-of-the-halting-problem₂ eval cl eval₁ eval₂ =
  H.halts , H.cl′ ,
  (λ { (p , cl-p) .true (p⇓ , refl) → H.lemma₁ p cl-p p⇓ }) ,
  (λ { (p , cl-p) v halts⌜p⌝⇓v → true ,
       Σ-map (_, refl) id (lemma₂ p v cl-p halts⌜p⌝⇓v) })
  where
  eval-inversion :
    ∀ p → Closed p →
    Terminates (apply eval (code p)) →
    Terminates p
  eval-inversion p cl-p = Σ-map id proj₁ ∘ eval₂ p _ cl-p ∘ proj₂

  module H = Half-of-the-halting-problem eval cl eval₁
               (λ { p cl-p ¬p⇓ →
                    Terminates (apply eval (code p))  ↝⟨ eval-inversion p cl-p ⟩
                    Terminates p                      ↝⟨ ¬p⇓ ⟩□
                    ⊥                                 □ })

  lemma₂ : ∀ p v → Closed p → apply H.halts (code p) ⇓ v →
           Terminates p × v ≡ code (true ⦂ Bool)
  lemma₂ p v cl-p q@(apply lambda _ (apply lambda _ (const []))) =
      (                                     $⟨ _ , q ⟩
       Terminates (apply H.halts (code p))  ↝⟨ H.halts-eval-inversion (code p) ⟩
       Terminates (apply eval (code p))     ↝⟨ eval-inversion p cl-p ⟩□
       Terminates p                         □)
    , refl

-- If the expression terminates with code zero as the result, then
-- this (total partial) function returns true. If the expression does
-- not terminate with code zero as the result, then the function
-- returns false.

Halts-with-zero : Closed-exp →Bool
Halts-with-zero =
  as-function-to-Bool₁ (λ { (e , _) → e ⇓ code zero })

-- Halts-with-zero is not decidable.

halts-with-zero : ¬ Decidable Halts-with-zero
halts-with-zero =
  Reduction→¬Computable→¬Computable
    (proj₁ Intensional-halting-problem₀₁) (proj₁ Halts-with-zero) red
    intensional-halting-problem₀₁
  where
  red : Reduction (proj₁ Intensional-halting-problem₀₁)
                  (proj₁ Halts-with-zero)
  red (halts-with-zero , cl , hyp₁ , hyp₂) =
    halts , cl-halts , hyp₁′ , hyp₂′
    where
    argument : Closed-exp → Closed-exp
    argument (p , cl-p) =
        apply (lambda v-x (const c-zero [])) p
      , (Closed′-closed-under-apply
           (from-⊎ (closed′? (lambda v-x (const c-zero [])) []))
           (Closed→Closed′ cl-p))

    coded-argument : Exp → Exp
    coded-argument p = const c-apply (
      code (Exp.lambda v-x (const c-zero [])) ∷
      p ∷
      [])

    halts : Exp
    halts =
      lambda v-p (apply halts-with-zero (coded-argument (var v-p)))

    cl-halts : Closed halts
    cl-halts =
      Closed′-closed-under-lambda $
      Closed′-closed-under-apply
        (Closed→Closed′ cl)
        (Closed′-closed-under-const λ where
           _ (inj₁ refl)        → Closed→Closed′ $
                                    code-closed (Exp.lambda v-x (const c-zero []))
           _ (inj₂ (inj₁ refl)) → Closed′-closed-under-var (inj₁ refl)
           _ (inj₂ (inj₂ ())))

    lemma₁ :
      ∀ p b →
      proj₁ Intensional-halting-problem₀₁ [ p ]= b →
      proj₁ Halts-with-zero [ argument p ]= b
    lemma₁ p true (_ , ¬¬p⇓) =
        (λ _ → refl)
      , λ ¬arg-p⇓zero → ¬¬p⇓ λ p⇓ → ¬arg-p⇓zero
                          (proj₁ (argument p)  ⇓⟨ apply lambda (proj₂ p⇓) (const []) ⟩■
                           const c-zero [])

    lemma₁ p false (¬p⇓ , _) =
        (λ { (apply _ p⇓ _) → ¬p⇓ (_ , p⇓) })
      , λ _ → refl

    hyp₁′ : ∀ p b → proj₁ Intensional-halting-problem₀₁ [ p ]= b →
            apply halts (code p) ⇓ code b
    hyp₁′ p b halts[p]=b =
      apply halts (code p)                                                ⟶⟨ apply lambda (code⇓code p) ⟩
      apply (halts-with-zero [ v-p ← code p ]) (coded-argument (code p))  ≡⟨ by (subst-closed _ _ cl) ⟩⟶
      apply halts-with-zero (coded-argument (code p))                     ⟶⟨⟩
      apply halts-with-zero (code (argument p))                           ⇓⟨ hyp₁ (argument p) b (lemma₁ p _ halts[p]=b) ⟩■
      code b

    pattern coded-argument-⇓ p =
      const (const (const (const (const (const [] ∷ []) ∷ []) ∷ []) ∷
                    const (const [] ∷ const [] ∷ []) ∷
                    []) ∷
             p ∷
             [])

    lemma₂ :
      ∀ p v →
      apply halts (code p) ⇓ v →
      apply halts-with-zero (code (argument p)) ⇓ v
    lemma₂ p v (apply {v₂ = v₂} lambda q r) =
      apply halts-with-zero (code (argument p))                       ≡⟨ by (subst-closed _ _ cl) ⟩⟶
      apply (halts-with-zero [ v-p ← v₂ ]) (coded-argument (code p))  ⟶⟨ []⇓ (apply→ ∙) (coded-argument-⇓ q) ⟩
      apply (halts-with-zero [ v-p ← v₂ ]) (coded-argument v₂)        ⇓⟨ r ⟩■
      v

    hyp₂′ : ∀ p v → apply halts (code p) ⇓ v →
            ∃ λ v′ →
              proj₁ Intensional-halting-problem₀₁ [ p ]= v′
                ×
              v ≡ code v′
    hyp₂′ p v q =
      Σ-map id
        (Σ-map
           (Σ-map
              (_∘ λ p⇓ → apply lambda (proj₂ p⇓) (const []))
              (_∘ λ ¬p⇓ → λ { (apply lambda p⇓ (const [])) →
                              ¬p⇓ (_ , p⇓) }))
           id) $
        hyp₂ (argument p) v (lemma₂ p v q)
