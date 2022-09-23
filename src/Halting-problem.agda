------------------------------------------------------------------------
-- The halting problem
------------------------------------------------------------------------

module Halting-problem where

open import Equality.Propositional.Cubical
open import Logical-equivalence using (_⇔_)
open import Prelude hiding (const; Decidable)
open import Tactic.By.Propositional
open import Univalence-axiom

open import Equality.Decision-procedures equality-with-J
open import Function-universe equality-with-J hiding (id; _∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional equality-with-paths
  as Trunc hiding (rec)

-- To simplify the development, let's work with actual natural numbers
-- as variables and constants (see
-- Atom.one-can-restrict-attention-to-χ-ℕ-atoms).

open import Atom

open import Cancellation   χ-ℕ-atoms
open import Chi            χ-ℕ-atoms
open import Coding         χ-ℕ-atoms
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
open import Combinators as χ hiding (id; if_then_else_)
open import Free-variables.Remove-substs
open import Internal-coding

------------------------------------------------------------------------
-- The extensional halting problem

-- The extensional halting problem is undecidable.

extensional-halting-problem :
  ¬ ∃ λ halts →
      Closed halts
        ×
      ∀ p → Closed p →
        (Terminates p →
         apply halts (lambda v-underscore p) ⇓ ⌜ true  ⦂ Bool ⌝)
          ×
        (¬ Terminates p →
         apply halts (lambda v-underscore p) ⇓ ⌜ false ⦂ Bool ⌝)
extensional-halting-problem (halts , cl , hyp) = contradiction
  where
  terminv : Exp → Exp
  terminv p = χ.if apply halts (lambda v-underscore p)
              then loop
              else ⌜ zero ⌝

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
      (Closed→Closed′ $ rep-closed zero)

  subst-lemma : terminv (var v-p) [ v-p ← strange ] ≡ terminv strange
  subst-lemma =
    terminv (var v-p) [ v-p ← strange ]             ≡⟨⟩

    χ.if apply (halts [ v-p ← strange ])
               (lambda v-underscore strange)
    then loop else ⌜ zero ⌝                         ≡⟨ remove-substs ((halts , cl) ∷ []) ⟩

    χ.if apply halts (lambda v-underscore strange)
    then loop else ⌜ zero ⌝                         ≡⟨⟩

    terminv strange                                 ∎

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
          apply halts (lambda v-underscore p) ⇓ ⌜ b ⌝
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
            apply halts (lambda v-underscore p) ⇓ ⌜ true ⦂ Bool ⌝
  ⇓→⇓true {p} cl p⇓ with hyp p cl
  ... | true ,  halts⇓true , _   = halts⇓true
  ... | false , _          , ¬p⇓ = ⊥-elim (¬p⇓ p⇓)

  ¬⇓→⇓false :
    ∀ {p} → Closed p → ¬ Terminates p →
    apply halts (lambda v-underscore p) ⇓ ⌜ false ⦂ Bool ⌝
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
             apply halts (lambda v-underscore p) ⇓ ⌜ b ⌝
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
            apply halts (lambda v-underscore p) ⇓ ⌜ true ⦂ Bool ⌝
  ⇓→⇓true cl p⇓ =
    flip (Trunc.rec ⇓-propositional) (hyp _ cl) λ where
      (false , _          , ¬p⇓) → ⊥-elim (¬p⇓ p⇓)
      (true  , halts⇓true , _)   → halts⇓true

  ¬⇓→⇓false :
    ∀ {p} → Closed p → ¬ Terminates p →
    apply halts (lambda v-underscore p) ⇓ ⌜ false ⦂ Bool ⌝
  ¬⇓→⇓false cl ¬p⇓ =
    flip (Trunc.rec ⇓-propositional) (hyp _ cl) λ where
      (true  , _           , p⇓) → ⊥-elim (¬p⇓ p⇓)
      (false , halts⇓false , _)  → halts⇓false

------------------------------------------------------------------------
-- The intensional halting problem with arbitrary or non-standard
-- coding relations

-- A "termination inversion" function, parametrised by a solution to
-- the (generalised) intensional halting problem of self application.

terminv : Exp → Exp
terminv halts =
  lambda v-x
    (χ.if apply halts (var v-x)
     then loop
     else ⌜ zero ⌝)

-- A generalised variant of the intensional halting problem of
-- self-application is not decidable. This variant replaces the coding
-- function for expressions with an arbitrary relation, restricted so
-- that codes have to be values. Furthermore the statement is changed
-- to include the assumption that there is a code for a certain
-- "strange" program.

generalised-intensional-halting-problem-of-self-application :
  (Code : Exp → ∃ Value → Type) →
  ¬ ∃ λ halts →
      Closed halts
        ×
      ∃ (Code (terminv halts))
        ×
      ∀ p c → Closed p → Code p c →
        let c′ = proj₁ c in
        (Terminates (apply p c′) →
           apply halts c′ ⇓ ⌜ true ⦂ Bool ⌝)
          ×
        (¬ Terminates (apply p c′) →
           apply halts c′ ⇓ ⌜ false ⦂ Bool ⌝)
generalised-intensional-halting-problem-of-self-application
  Code (halts , cl , (code-strange , cd) , hyp) =
  contradiction
  where
  terminv-lemma : ∀ p c → Closed p → Code p c →
                  Terminates (apply (terminv halts) (proj₁ c))
                    ⇔
                  ¬ Terminates (apply p (proj₁ c))
  terminv-lemma p (c , c-vl) cl-p cd-p =
    record { to = to; from = from }
    where
    to : Terminates (apply (terminv halts) c) →
         ¬ Terminates (apply p c)
    to (_ , apply lambda _ (case _ here [] loop⇓)) p⇓ =
      ¬loop⇓ (_ , loop⇓)

    to (_ , apply lambda _ (case _ (there _ (there _ ())) _  _)) p⇓

    to (_ , apply lambda rep-p⇓
              (case halts⇓false′ (there _ here) [] _)) p⇓ =
      C.distinct-codes→distinct-names (λ ()) $
        proj₁ $ cancel-const $
          ⇓-deterministic
            (proj₁ (hyp p (c , c-vl) cl-p cd-p) p⇓)
            halts⇓false
      where
      halts⇓false : apply halts c ⇓ ⌜ false ⦂ Bool ⌝
      halts⇓false
        rewrite sym $ values-only-compute-to-themselves c-vl rep-p⇓ =
        subst (λ e → apply e _ ⇓ _)
              (subst-closed _ _ cl)
              halts⇓false′

    from : ¬ Terminates (apply p c) →
           Terminates (apply (terminv halts) c)
    from ¬p⇓ =
      _ , apply lambda (values-compute-to-themselves c-vl)
            (case halts⇓false
                  (there (C.distinct-codes→distinct-names (λ ())) here)
                  []
                  (const []))
      where
      halts⇓false : apply (halts [ v-x ← c ]) c ⇓
                    ⌜ false ⦂ Bool ⌝
      halts⇓false =
        subst (λ e → apply e _ ⇓ _)
              (sym $ subst-closed _ _ cl)
              (proj₂ (hyp p (c , c-vl) cl-p cd-p) ¬p⇓)

  strange : Exp
  strange = apply (terminv halts) (proj₁ code-strange)

  terminv-closed : Closed (terminv halts)
  terminv-closed =
    Closed′-closed-under-lambda $
    if-then-else-closed
      (Closed′-closed-under-apply
         (Closed→Closed′ cl)
         (Closed′-closed-under-var (inj₁ refl)))
      (Closed→Closed′ loop-closed)
      (Closed→Closed′ $ rep-closed zero)

  strange-lemma : Terminates strange ⇔ ¬ Terminates strange
  strange-lemma =
    terminv-lemma
      (terminv halts) code-strange
      terminv-closed cd

  contradiction : ⊥
  contradiction = ¬[⇔¬] strange-lemma

-- A coding relation: An expression e that terminates is encoded by
-- the representation of true, and an expression e that does not
-- terminate is encoded by the representation of false.

⇓-coding : Exp → ∃ Value → Type
⇓-coding e (c , _) =
  Terminates e × c ≡ ⌜ true ⦂ Bool ⌝
    ⊎
  ¬ Terminates e × c ≡ ⌜ false ⦂ Bool ⌝

-- When this coding relation is used the intensional halting problem
-- with zero arguments is decidable.

intensional-halting-problem₀-with-⇓-coding :
  ∃ λ halts →
    Closed halts
      ×
    ∀ p (c@(c′ , _) : ∃ Value) → Closed p → ⇓-coding p c →
      (Terminates p → apply halts c′ ⇓ ⌜ true ⦂ Bool ⌝)
        ×
      (¬ Terminates p → apply halts c′ ⇓ ⌜ false ⦂ Bool ⌝)
intensional-halting-problem₀-with-⇓-coding =
    halts
  , halts-closed
  , halts-correct
  where
  halts : Exp
  halts =
    lambda v-p
      (case (var v-p)
         (branch c-true  [] ⌜ true  ⦂ Bool ⌝ ∷
          branch c-false [] ⌜ false ⦂ Bool ⌝ ∷
          []))

  halts-closed : Closed halts
  halts-closed = from-⊎ (closed? halts)

  halts-correct :
    ∀ p (c@(c′ , _) : ∃ Value) → Closed p → ⇓-coding p c →
    (Terminates p → apply halts c′ ⇓ ⌜ true ⦂ Bool ⌝)
      ×
    (¬ Terminates p → apply halts c′ ⇓ ⌜ false ⦂ Bool ⌝)
  halts-correct _ (.(⌜ true ⌝) , _) _ (inj₁ (p⇓ , refl)) =
      (λ _   → apply lambda (rep⇓rep (true ⦂ Bool))
                 (case (rep⇓rep (true ⦂ Bool)) here []
                    (rep⇓rep (true ⦂ Bool))))
    , (λ ¬p⇓ → ⊥-elim (¬p⇓ p⇓))

  halts-correct _ (.(⌜ false ⌝) , _) _ (inj₂ (¬p⇓ , refl)) =
      (λ p⇓ → ⊥-elim (¬p⇓ p⇓))
    , (λ _   → apply lambda (rep⇓rep (false ⦂ Bool))
                 (case (rep⇓rep (false ⦂ Bool)) (there (λ ()) here) []
                    (rep⇓rep (false ⦂ Bool))))

------------------------------------------------------------------------
-- The intensional halting problem

-- The intensional halting problem of self-application. (This
-- definition is not used below.)

Intensional-halting-problem-of-self-application : Closed-exp →Bool
Intensional-halting-problem-of-self-application =
  as-function-to-Bool₁ (λ { (e , _) → Terminates (apply e ⌜ e ⌝) })

-- The intensional halting problem of self-application is not
-- decidable.

intensional-halting-problem-of-self-application :
  ¬ ∃ λ halts →
      Closed halts
        ×
      ∀ p → Closed p →
        (Terminates (apply p ⌜ p ⌝) →
           apply halts ⌜ p ⌝ ⇓ ⌜ true ⦂ Bool ⌝)
          ×
        (¬ Terminates (apply p ⌜ p ⌝) →
           apply halts ⌜ p ⌝ ⇓ ⌜ false ⦂ Bool ⌝)
intensional-halting-problem-of-self-application
  (halts , cl , hyp) =
  generalised-intensional-halting-problem-of-self-application
     ⌜⌝-Code
     ( halts
     , cl
     , ( ( ⌜ terminv halts ⌝
         , const→value (rep-const (terminv halts))
         )
       , refl
       )
     , λ { p _ cl-p refl → hyp p cl-p }
     )
  where
  ⌜⌝-Code : Exp → ∃ Value → Type
  ⌜⌝-Code e (c , _) = ⌜ e ⌝ ≡ c

-- The intensional halting problem with one argument is not decidable.

intensional-halting-problem₁ :
  ¬ ∃ λ halts →
      Closed halts
        ×
      ∀ p x → Closed p → Closed x →
        (Terminates (apply p ⌜ x ⌝) →
           apply halts ⌜ p , x ⌝ ⇓ ⌜ true ⦂ Bool ⌝)
          ×
        (¬ Terminates (apply p ⌜ x ⌝) →
           apply halts ⌜ p , x ⌝ ⇓ ⌜ false ⦂ Bool ⌝)
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
          apply halts ⌜ p , p ⌝ ⇓ ⌜ b ⌝ →
          apply halts′ ⌜ p ⌝ ⇓ ⌜ b ⌝
  lemma p b halts⇓ =
    apply halts′ ⌜ p ⌝                       ⟶⟨ apply lambda (rep⇓rep p) ⟩
    apply (halts [ v-p ← ⌜ p ⌝ ]) ⌜ p , p ⌝  ≡⟨ remove-substs ((halts , cl) ∷ []) ⟩⟶
    apply halts ⌜ p , p ⌝                    ⇓⟨ halts⇓ ⟩■
    ⌜ b ⌝

-- The intensional halting problem with zero arguments is not
-- decidable.

intensional-halting-problem₀ :
  ¬ ∃ λ halts →
      Closed halts
        ×
      ∀ p → Closed p →
        (Terminates p → apply halts ⌜ p ⌝ ⇓ ⌜ true ⦂ Bool ⌝)
          ×
        (¬ Terminates p → apply halts ⌜ p ⌝ ⇓ ⌜ false ⦂ Bool ⌝)
intensional-halting-problem₀ (halts , cl , hyp) =
  intensional-halting-problem-of-self-application
    ( halts′
    , cl′
    , λ p cl-p → Σ-map (lemma p true ∘_) (lemma p false ∘_)
                       (hyp (apply p ⌜ p ⌝)
                            (Closed′-closed-under-apply
                               (Closed→Closed′ cl-p)
                               (Closed→Closed′ (rep-closed p))))
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
            apply halts ⌜ Exp.apply p ⌜ p ⌝ ⌝ ⇓ ⌜ b ⌝ →
            apply halts′ ⌜ p ⌝ ⇓ ⌜ b ⌝
    lemma p b halts⇓ =
      apply halts′ ⌜ p ⌝                                              ⟶⟨ apply lambda (rep⇓rep p) ⟩

      apply (halts [ v-p ← ⌜ p ⌝ ]) (const c-apply (
        ⌜ p ⌝ ∷ apply (internal-code [ v-p ← ⌜ p ⌝ ]) ⌜ p ⌝ ∷ []))    ≡⟨ remove-substs
                                                                           ((halts , cl) ∷ (internal-code , internal-code-closed) ∷ []) ⟩⟶
      apply halts (const c-apply (
        ⌜ p ⌝ ∷ apply internal-code ⌜ p ⌝ ∷ []))                      ⟶⟨ []⇓ (apply→ ∙) (const (rep⇓rep p ∷ internal-code-correct p ∷ [])) ⟩

      apply halts (const c-apply (⌜ p ⌝ ∷ ⌜ ⌜ p ⌝ ⦂ Exp ⌝ ∷ []))      ≡⟨⟩⟶

      apply halts ⌜ Exp.apply p ⌜ p ⌝ ⌝                               ⇓⟨ halts⇓ ⟩■

      ⌜ b ⌝

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
           apply halts ⌜ p ⌝  ⇓⟨ hyp (p , cl-p) true ((λ _ → refl) , λ ¬p⇓ → ⊥-elim (¬p⇓ p⇓)) ⟩■
           ⌜ true ⦂ Bool ⌝) ,
        λ ¬p⇓ →
          apply halts ⌜ p ⌝  ⇓⟨ hyp (p , cl-p) false ((λ p⇓ → ⊥-elim (¬p⇓ p⇓)) , λ _ → refl) ⟩■
          ⌜ false ⦂ Bool ⌝
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
             apply halts ⌜ p ⌝  ⇓⟨ hyp (p , cl-p) true (inj₁ (p⇓  , refl)) ⟩■
             ⌜ true ⦂ Bool ⌝)
        , (λ ¬p⇓ →
             apply halts ⌜ p ⌝  ⇓⟨ hyp (p , cl-p) false (inj₂ (¬p⇓ , refl)) ⟩■
             ⌜ false ⦂ Bool ⌝)
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
  (excluded-middle : (P : Type) → Is-proposition P → Dec P) →
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
    {P : Type} → Is-proposition P → ¬ ¬ P → P
  double-negation-elimination P-prop ¬¬p =
    case em _ P-prop of λ where
      (inj₁ p)  → p
      (inj₂ ¬p) → ⊥-elim (¬¬p ¬p)

------------------------------------------------------------------------
-- "Half of the halting problem"

-- If a (correct) self-interpreter can be implemented, then "half of
-- the halting problem" is computable.

half-of-the-halting-problem :
  (eval : Exp) →
  Closed eval →
  (∀ p v → Closed p → p ⇓ v → apply eval ⌜ p ⌝ ⇓ ⌜ v ⌝) →
  (∀ p → Closed p → ¬ Terminates p →
     ¬ Terminates (apply eval ⌜ p ⌝)) →
  ∃ λ halts →
      Closed halts
        ×
      ∀ p → Closed p →
        (Terminates p → apply halts ⌜ p ⌝ ⇓ ⌜ true ⦂ Bool ⌝)
          ×
        (¬ Terminates p → ¬ Terminates (apply halts ⌜ p ⌝))
half-of-the-halting-problem eval cl eval⇓ eval¬⇓ =
  halts , cl′ , λ p cl-p → lemma₁ p cl-p , lemma₂ p cl-p
  module Half-of-the-halting-problem where
  halts = lambda v-p (apply (lambda v-underscore ⌜ true ⦂ Bool ⌝)
                            (apply eval (var v-p)))

  cl′ : Closed halts
  cl′ =
    Closed′-closed-under-lambda $
    Closed′-closed-under-apply
      (from-⊎ (closed′? (lambda v-underscore ⌜ true ⦂ Bool ⌝) _))
      (Closed′-closed-under-apply
        (Closed→Closed′ cl)
        (Closed′-closed-under-var (inj₁ refl)))

  lemma₁ : ∀ p → Closed p → Terminates p →
           apply halts ⌜ p ⌝ ⇓ ⌜ true ⦂ Bool ⌝
  lemma₁ p cl-p (v , p⇓v) =
    apply halts ⌜ p ⌝                            ⟶⟨ apply lambda (rep⇓rep p) ⟩

    apply (lambda v-underscore ⌜ true ⦂ Bool ⌝)
          (apply (eval [ v-p ← ⌜ p ⌝ ]) ⌜ p ⌝)   ≡⟨ remove-substs ((eval , cl) ∷ []) ⟩⟶

    apply (lambda v-underscore ⌜ true ⦂ Bool ⌝)
          (apply eval ⌜ p ⌝)                     ⇓⟨ apply lambda (eval⇓ p v cl-p p⇓v) (rep⇓rep (true ⦂ Bool)) ⟩■

    ⌜ true ⦂ Bool ⌝

  halts-eval-inversion :
    ∀ e →
    Terminates (apply halts e) →
    Terminates (apply eval e)
  halts-eval-inversion e (_ , apply {v₂ = v} lambda e⇓
                           (apply {v₂ = v₂} _ eval⇓ _)) =
    _ , (apply eval e                ⟶⟨ []⇓ (apply→ ∙) e⇓ ⟩
         apply eval v                ≡⟨ sym $ remove-substs ((eval , cl) ∷ []) ⟩⟶
         apply (eval [ v-p ← v ]) v  ⇓⟨ eval⇓ ⟩■
         v₂)

  lemma₂ : ∀ p → Closed p →
           ¬ Terminates p →
           ¬ Terminates (apply halts ⌜ p ⌝)
  lemma₂ p cl-p ¬p⇓ =
    Terminates (apply halts ⌜ p ⌝)  ↝⟨ halts-eval-inversion ⌜ p ⌝ ⟩
    Terminates (apply eval ⌜ p ⌝)   ↝⟨ eval¬⇓ p cl-p ¬p⇓ ⟩□
    ⊥                               □

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
  (∀ p v → Closed p → p ⇓ v → apply eval ⌜ p ⌝ ⇓ ⌜ v ⌝) →
  (∀ p v → Closed p → apply eval ⌜ p ⌝ ⇓ v →
     ∃ λ v′ → p ⇓ v′ × v ≡ ⌜ v′ ⌝) →
  Computable Half-of-the-halting-problem₂
half-of-the-halting-problem₂ eval cl eval₁ eval₂ =
  H.halts , H.cl′ ,
  (λ { (p , cl-p) .true (p⇓ , refl) → H.lemma₁ p cl-p p⇓ }) ,
  (λ { (p , cl-p) v halts⌜p⌝⇓v → true ,
       Σ-map (_, refl) id (lemma₂ p v cl-p halts⌜p⌝⇓v) })
  where
  eval-inversion :
    ∀ p → Closed p →
    Terminates (apply eval ⌜ p ⌝) →
    Terminates p
  eval-inversion p cl-p = Σ-map id proj₁ ∘ eval₂ p _ cl-p ∘ proj₂

  module H = Half-of-the-halting-problem eval cl eval₁
               (λ { p cl-p ¬p⇓ →
                    Terminates (apply eval ⌜ p ⌝)  ↝⟨ eval-inversion p cl-p ⟩
                    Terminates p                   ↝⟨ ¬p⇓ ⟩□
                    ⊥                              □ })

  lemma₂ : ∀ p v → Closed p → apply H.halts ⌜ p ⌝ ⇓ v →
           Terminates p × v ≡ ⌜ true ⦂ Bool ⌝
  lemma₂ p v cl-p q@(apply lambda _ (apply lambda _ (const []))) =
      (                                  $⟨ _ , q ⟩
       Terminates (apply H.halts ⌜ p ⌝)  ↝⟨ H.halts-eval-inversion ⌜ p ⌝ ⟩
       Terminates (apply eval ⌜ p ⌝)     ↝⟨ eval-inversion p cl-p ⟩□
       Terminates p                      □)
    , refl

------------------------------------------------------------------------
-- Halting with zero

-- If the expression terminates with ⌜ zero ⌝ as the result, then this
-- (total partial) function returns true. If the expression does not
-- terminate with ⌜ zero ⌝ as the result, then the function returns
-- false.

Halts-with-zero : Closed-exp →Bool
Halts-with-zero =
  as-function-to-Bool₁ (λ { (e , _) → e ⇓ ⌜ zero ⌝ })

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
      ⌜ Exp.lambda v-x (const c-zero []) ⌝ ∷
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
                                    rep-closed (Exp.lambda v-x (const c-zero []))
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
            apply halts ⌜ p ⌝ ⇓ ⌜ b ⌝
    hyp₁′ p b halts[p]=b =
      apply halts ⌜ p ⌝                                               ⟶⟨ apply lambda (rep⇓rep p) ⟩
      apply (halts-with-zero [ v-p ← ⌜ p ⌝ ]) (coded-argument ⌜ p ⌝)  ≡⟨ remove-substs ((halts-with-zero , cl) ∷ []) ⟩⟶
      apply halts-with-zero (coded-argument ⌜ p ⌝)                    ≡⟨⟩⟶
      apply halts-with-zero ⌜ argument p ⌝                            ⇓⟨ hyp₁ (argument p) b (lemma₁ p _ halts[p]=b) ⟩■
      ⌜ b ⌝

    pattern coded-argument-⇓ p =
      const (const (const (const (const (const [] ∷ []) ∷ []) ∷ []) ∷
                    const (const [] ∷ const [] ∷ []) ∷
                    []) ∷
             p ∷
             [])

    lemma₂ :
      ∀ p v →
      apply halts ⌜ p ⌝ ⇓ v →
      apply halts-with-zero ⌜ argument p ⌝ ⇓ v
    lemma₂ p v (apply {v₂ = v₂} lambda q r) =
      apply halts-with-zero ⌜ argument p ⌝                         ≡⟨ sym $ remove-substs ((halts-with-zero , cl) ∷ []) ⟩⟶
      apply (halts-with-zero [ v-p ← v₂ ]) (coded-argument ⌜ p ⌝)  ⟶⟨ []⇓ (apply→ ∙) (coded-argument-⇓ q) ⟩
      apply (halts-with-zero [ v-p ← v₂ ]) (coded-argument v₂)     ⇓⟨ r ⟩■
      v

    hyp₂′ : ∀ p v → apply halts ⌜ p ⌝ ⇓ v →
            ∃ λ v′ →
              proj₁ Intensional-halting-problem₀₁ [ p ]= v′
                ×
              v ≡ ⌜ v′ ⌝
    hyp₂′ p v q =
      Σ-map id
        (Σ-map
           (Σ-map
              (_∘ λ p⇓ → apply lambda (proj₂ p⇓) (const []))
              (_∘ λ ¬p⇓ → λ { (apply lambda p⇓ (const [])) →
                              ¬p⇓ (_ , p⇓) }))
           id) $
        hyp₂ (argument p) v (lemma₂ p v q)
