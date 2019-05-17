------------------------------------------------------------------------
-- A theorem related to pointwise equality
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

-- To simplify the development, let's work with actual natural numbers
-- as variables and constants (see
-- Atom.one-can-restrict-attention-to-χ-ℕ-atoms).

open import Atom

open import Chi            χ-ℕ-atoms
open import Coding         χ-ℕ-atoms
open import Free-variables χ-ℕ-atoms

import Coding.Instances.Nat

-- The results are stated and proved under the assumption that a
-- correct self-interpreter can be implemented.

module Pointwise-equality
  (eval : Exp)
  (cl-eval : Closed eval)
  (eval-correct₁ : ∀ p v → Closed p → p ⇓ v → apply eval ⌜ p ⌝ ⇓ ⌜ v ⌝)
  where

open import Equality.Propositional
open import Prelude hiding (const; Decidable)

open import Bag-equivalence equality-with-J
open import Equality.Decision-procedures equality-with-J
open import H-level.Closure equality-with-J

open import Computability χ-ℕ-atoms
open import Constants     χ-ℕ-atoms
open import Reasoning     χ-ℕ-atoms
open import Values        χ-ℕ-atoms

open Computable-function
open χ-atoms χ-ℕ-atoms

open import Combinators hiding (if_then_else_)

-- Pointwise equality of computable functions to Bool.

Pointwise-equal :
  ∀ {a} (A : Set a) ⦃ rA : Rep A Consts ⦄ →
  let F = Computable-function A Bool Bool-set in
  (F × F) →Bool
Pointwise-equal _ =
  as-function-to-Bool₁
    (λ { (f , g) → ∀ x → function f x ≡ function g x })

-- Pointwise equality of computable functions from Bool to Bool is
-- decidable.

pointwise-equal-Bool : Decidable (Pointwise-equal Bool)
pointwise-equal-Bool =
  total→almost-computable→computable
    id
    id
    (proj₁ (Pointwise-equal Bool))
    total
    ( pointwise-equal
    , closed
    , correct
    )
  where
  F = Computable-function Bool Bool Bool-set

  pointwise-equal′ : F × F → Bool
  pointwise-equal′ (f , g) =
    (if function f true  Bool.≟ function g true  then true else false)
      ∧
    (if function f false Bool.≟ function g false then true else false)

  total : Total id (proj₁ (Pointwise-equal Bool))
  total p@(f , g) = result , true-lemma , false-lemma
    where
    result = pointwise-equal′ p

    true-lemma : (∀ b → function f b ≡ function g b) → result ≡ true
    true-lemma hyp
      with function f true Bool.≟ function g true | hyp true
    ... | no  f≢g | f≡g = ⊥-elim (f≢g f≡g)
    ... | yes _   | _
      with function f false Bool.≟ function g false | hyp false
    ... | no  f≢g | f≡g = ⊥-elim (f≢g f≡g)
    ... | yes _   | _   = refl

    false-lemma : ¬ (∀ b → function f b ≡ function g b) → result ≡ false
    false-lemma hyp
      with function f true  Bool.≟ function g true
         | function f false Bool.≟ function g false
    ... | yes ft≡gt | yes ff≡gf = ⊥-elim $ hyp Prelude.[ (λ _ → ft≡gt)
                                                       , (λ _ → ff≡gf)
                                                       ]
    ... | yes _     | no  _     = refl
    ... | no  _     | yes _     = refl
    ... | no  _     | no  _     = refl

  infix 10 _at_

  _at_ : Exp → Bool → Exp
  f at b =
    decode-Bool
      (apply eval (const c-apply (f ∷ ⌜ ⌜ b ⌝ ⦂ Exp ⌝ ∷ [])))

  test : Bool → Exp
  test b = equal-Bool (var v-f at b) (var v-g at b)

  pointwise-equal : Exp
  pointwise-equal =
    lambda v-p (case (var v-p) (
      branch c-pair (v-f ∷ v-g ∷ [])
        (and (test true) (test false)) ∷ []))

  -- This proof could have been simplified if eval had been a concrete
  -- implementation, rather than a variable.

  closed : Closed pointwise-equal
  closed =
    Closed′-closed-under-lambda $
    Closed′-closed-under-case
      (Closed′-closed-under-var (inj₁ refl))
      (λ where
        (inj₁ refl) → and-closed (test-closed true) (test-closed false)
        (inj₂ ()))
    where
    variables = v-f ∷ v-g ∷ v-p ∷ []

    at-closed : ∀ f b → f ∈ variables → Closed′ variables (var f at b)
    at-closed f b f∈ =
      decode-Bool-closed $
      Closed′-closed-under-apply
        (Closed→Closed′ cl-eval)
        (Closed′-closed-under-const λ where
           _ (inj₁ refl)        → Closed′-closed-under-var f∈
           _ (inj₂ (inj₁ refl)) → Closed→Closed′ $
                                  rep-closed (⌜ b ⌝ ⦂ Exp)
           _ (inj₂ (inj₂ ())))

    test-closed : ∀ b → Closed′ variables (test b)
    test-closed b =
      equal-Bool-closed
        (at-closed v-f b (from-⊎ (V.member v-f variables)))
        (at-closed v-g b (from-⊎ (V.member v-g variables)))

  at-correct :
    ∀ (f : F) b → ⌜ f ⌝ at b ⇓ ⌜ function f b ⌝
  at-correct f b = decode-Bool-correct (function f b) (
    apply eval ⌜ apply (proj₁ (computable f)) ⌜ b ⌝ ⦂ Exp ⌝  ⇓⟨ eval-correct₁
                                                                  (apply (proj₁ $ computable f) ⌜ b ⌝)
                                                                  ⌜ function f b ⌝
                                                                  (Closed′-closed-under-apply
                                                                     (proj₁ $ proj₂ $ computable f)
                                                                     (rep-closed b))
                                                                  (proj₁ (proj₂ $ proj₂ $ computable f)
                                                                     b
                                                                     (function f b)
                                                                     (lift refl)) ⟩■
    ⌜ ⌜ function f b ⌝ ⦂ Exp ⌝)

  test-correct :
    ∀ b (f g : F) →
    test b [ v-g ← ⌜ g ⌝ ] [ v-f ← ⌜ f ⌝ ] ⇓
    ⌜ if function f b Bool.≟ function g b then true else false ⌝
  test-correct b f g =
    equal-Bool-correct (function f b) (function g b)

      (var v-f at b [ v-g ← ⌜ g ⌝ ] [ v-f ← ⌜ f ⌝ ]  ≡⟨ lemma ⌜ f ⌝ ⟩⟶
       ⌜ f ⌝ at b                                    ⇓⟨ at-correct f b ⟩■
       ⌜ function f b ⌝)

      (var v-g at b [ v-g ← ⌜ g ⌝ ] [ v-f ← ⌜ f ⌝ ]  ≡⟨ lemma (⌜ g ⌝ [ v-f ← ⌜ f ⌝ ]) ⟩⟶
       (⌜ g ⌝ [ v-f ← ⌜ f ⌝ ]) at b                  ≡⟨ cong (_at b) (subst-rep g) ⟩⟶
       ⌜ g ⌝ at b                                    ⇓⟨ at-correct g b ⟩■
       ⌜ function g b ⌝)
    where
    ss = (v-f , ⌜ f ⌝) ∷ (v-g , ⌜ g ⌝) ∷ []

    lemma : ∀ _ → _
    lemma = λ e →
      cong₂ (λ e₁ e₂ → decode-Bool (apply e₁ (const _ (e ∷ e₂ ∷ []))))
        (substs-closed eval cl-eval ss)
        (substs-rep (⌜ b ⌝ ⦂ Exp) ss)

  correct :
    ∀ p b →
    proj₁ (Pointwise-equal Bool) [ p ]= b →
    apply pointwise-equal ⌜ p ⌝ ⇓ ⌜ b ⌝
  correct p@(f , g) b [p]=b =
    apply pointwise-equal ⌜ p ⌝                               ⟶⟨ apply lambda (rep⇓rep p) ⟩

    case ⌜ p ⌝ (
      branch c-pair (v-f ∷ v-g ∷ [])
        (and (test true) (test false) [ v-p ← ⌜ p ⌝ ]) ∷ [])  ≡⟨ cong₂ (λ e₁ e₂ → case ⌜ p ⌝ (branch c-pair (v-f ∷ v-g ∷ []) (and e₁ e₂) ∷ []))
                                                                   (test-lemma true)
                                                                   (test-lemma false) ⟩⟶
    case ⌜ p ⌝ (
      branch c-pair (v-f ∷ v-g ∷ [])
        (and (test true) (test false)) ∷ [])                  ⟶⟨ case (rep⇓rep p) here (∷ ∷ []) ⟩

    and (test true  [ v-g ← ⌜ g ⌝ ] [ v-f ← ⌜ f ⌝ ])
        (test false [ v-g ← ⌜ g ⌝ ] [ v-f ← ⌜ f ⌝ ])          ⇓⟨ and-correct (if function f true  Bool.≟ function g true  then true else false)
                                                                             (if function f false Bool.≟ function g false then true else false)
                                                                             (test-correct true f g) (test-correct false f g) ⟩

    ⌜ pointwise-equal′ p ⌝                                    ≡⟨ cong ⌜_⌝ (_⇀_.deterministic (proj₁ (Pointwise-equal Bool)) {a = p}
                                                                                             (proj₂ (total p)) [p]=b) ⟩⟶
    ⌜ b ⌝                                                     ■⟨ rep-value b ⟩

    where

    at-lemma :
      ∀ b f → v-p ≢ f → var f at b [ v-p ← ⌜ p ⌝ ] ≡ var f at b
    at-lemma b f p≢f =
      var f at b [ v-p ← ⌜ p ⌝ ]                                          ≡⟨⟩

      decode-Bool (apply (eval [ v-p ← ⌜ p ⌝ ]) (const c-apply
        (var f [ v-p ← ⌜ p ⌝ ] ∷ ⌜ ⌜ b ⌝ ⦂ Exp ⌝ [ v-p ← ⌜ p ⌝ ] ∷ [])))  ≡⟨ cong (λ e → decode-Bool (apply e (const _
                                                                                          (var f [ v-p ← ⌜ p ⌝ ] ∷
                                                                                           ⌜ ⌜ b ⌝ ⦂ Exp ⌝ [ v-p ← ⌜ p ⌝ ] ∷ []))))
                                                                               (subst-closed v-p ⌜ p ⌝ cl-eval) ⟩
      decode-Bool (apply eval (const c-apply
        (var f [ v-p ← ⌜ p ⌝ ] ∷ ⌜ ⌜ b ⌝ ⦂ Exp ⌝ [ v-p ← ⌜ p ⌝ ] ∷ [])))  ≡⟨ cong (λ e → decode-Bool (apply _ (const _ (e ∷ _))))
                                                                               (subst-∉ v-p (var f) λ { (var p≡f) → p≢f p≡f }) ⟩
      decode-Bool (apply eval (const c-apply
        (var f ∷ ⌜ ⌜ b ⌝ ⦂ Exp ⌝ [ v-p ← ⌜ p ⌝ ] ∷ [])))                  ≡⟨ cong (λ e → decode-Bool (apply _ (const _ (_ ∷ e ∷ _))))
                                                                               (subst-rep (⌜ b ⌝ ⦂ Exp)) ⟩
      decode-Bool (apply eval (const c-apply
        (var f ∷ ⌜ ⌜ b ⌝ ⦂ Exp ⌝ ∷ [])))                                  ≡⟨⟩

      var f at b                                                          ∎

    test-lemma : ∀ b → test b [ v-p ← ⌜ p ⌝ ] ≡ test b
    test-lemma b =
      cong₂ equal-Bool (at-lemma b v-f (λ ())) (at-lemma b v-g (λ ()))
