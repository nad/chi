------------------------------------------------------------------------
-- Some results related to pointwise equality
------------------------------------------------------------------------

module Pointwise-equality where

open import Equality.Propositional
open import Prelude as P hiding (const; not; Decidable)
open import Tactic.By.Propositional

open import Bag-equivalence equality-with-J
import Bool equality-with-J as Bool
open import Equality.Decision-procedures equality-with-J
open import Function-universe equality-with-J hiding (id; _∘_)
open import H-level.Closure equality-with-J

-- To simplify the development, let's work with actual natural numbers
-- as variables and constants (see
-- Atom.one-can-restrict-attention-to-χ-ℕ-atoms).

open import Atom

open import Chi                 χ-ℕ-atoms
open import Coding              χ-ℕ-atoms
open import Compatibility       χ-ℕ-atoms
open import Computability       χ-ℕ-atoms hiding (_∘_)
open import Computable-function χ-ℕ-atoms
open import Constants           χ-ℕ-atoms
open import Free-variables      χ-ℕ-atoms
open import Not-the-code-of     χ-ℕ-atoms
open import Reasoning           χ-ℕ-atoms
open import Termination         χ-ℕ-atoms
open import Values              χ-ℕ-atoms

open Computable-function
open χ-atoms χ-ℕ-atoms

import Coding.Instances.Nat
open import Combinators hiding (id; if_then_else_)
open import Decidable
open import Free-variables.Remove-substs
open import Halting-problem
open import Internal-coding
open import Self-interpreter

-- Pointwise equality of computable (Agda) functions to Bool.

Pointwise-equal :
  ∀ {a} (A : Type a) ⦃ rA : Rep A Consts ⦄ →
  let F = Computable-function A Bool Bool-set in
  (F × F) →Bool
Pointwise-equal _ =
  as-function-to-Bool₁
    (λ { (f , g) → ∀ x → function f x ≡ function g x })

-- Pointwise equality of computable Agda functions from Bool to Bool
-- is decidable.

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
    ... | yes ft≡gt | yes ff≡gf = ⊥-elim $ hyp P.[ (λ _ → ft≡gt)
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
        (Closed→Closed′ eval-closed)
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
        (substs-closed eval eval-closed ss)
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
        (var f [ v-p ← ⌜ p ⌝ ] ∷ ⌜ ⌜ b ⌝ ⦂ Exp ⌝ [ v-p ← ⌜ p ⌝ ] ∷ [])))  ≡⟨ remove-substs ((eval , eval-closed) ∷ []) ⟩

      decode-Bool (apply eval (const c-apply
        (var f [ v-p ← ⌜ p ⌝ ] ∷ ⌜ ⌜ b ⌝ ⦂ Exp ⌝ ∷ [])))                  ≡⟨ cong (λ e → decode-Bool (apply _ (const _ (e ∷ _))))
                                                                               (subst-∉ v-p (var f) λ { (var p≡f) → p≢f p≡f }) ⟩
      decode-Bool (apply eval (const c-apply
        (var f ∷ ⌜ ⌜ b ⌝ ⦂ Exp ⌝ ∷ [])))                                  ≡⟨⟩

      var f at b                                                          ∎

    test-lemma : ∀ b → test b [ v-p ← ⌜ p ⌝ ] ≡ test b
    test-lemma b =
      cong₂ equal-Bool (at-lemma b v-f (λ ())) (at-lemma b v-g (λ ()))

-- Pointwise equality of computable functions from ℕ to Bool is
-- not decidable, assuming that terminates-in-Bool is computable.

not-pointwise-equal-ℕ :
  Computable (as-partial Bool-set terminates-in-Bool) →
  ¬ Decidable (Pointwise-equal ℕ)
not-pointwise-equal-ℕ
  (term-in , term-in-closed , term-in-ok , _)
  (pointwise-equal , pointwise-equal-closed , peq-ok , _) =
  intensional-halting-problem₀
    ( halts
    , halts-closed
    , λ p _ → true-lemma p , false-lemma p
    )
  where
  halts = Exp.lambda v-p (not (
    apply pointwise-equal (const c-pair (
      ⌜ lambda v-n (apply ⌜ term-in ⌝ (const c-pair (
          ⌞ apply internal-code (var v-p) ⌟ ∷
          var v-n ∷
          []))) ⌝E ∷
      ⌜ lambda v-underscore ⌜ false ⌝ ⌝ ∷
      []))))

  halts-closed : Closed halts
  halts-closed =
    Closed′-closed-under-lambda $
    not-closed $
    Closed′-closed-under-apply
      (Closed→Closed′ pointwise-equal-closed) $
      Closed′-closed-under-const λ where
        _ (inj₂ (inj₁ refl)) →
          Closed→Closed′ $ rep-closed (lambda v-underscore ⌜ false ⌝)
        _ (inj₁ refl) → Closed′-closed-under-const λ where
          _ (inj₁ refl)        → Closed→Closed′ $ rep-closed v-n
          _ (inj₂ (inj₁ refl)) → Closed′-closed-under-const λ where
            _ (inj₁ refl) →                        $⟨ rep-closed term-in ⟩
              Closed ⌜ term-in ⌝                   →⟨ subst Closed $ sym $ ⌜⌜⌝⌝E≡⌜⌝ _ ⟩
              Closed ⌜ ⌜ term-in ⌝ ⌝E              →⟨ Closed→Closed′ ⟩□
              Closed′ (v-p ∷ []) ⌜ ⌜ term-in ⌝ ⌝E  □
            _ (inj₂ (inj₁ refl)) → Closed′-closed-under-const λ where
              _ (inj₁ refl) → Closed→Closed′ $ rep-closed c-pair
              _ (inj₂ (inj₁ refl)) → Closed′-closed-under-const λ where
                _ (inj₁ refl) → Closed′-closed-under-apply
                  (Closed→Closed′ internal-code-closed)
                  (Closed′-closed-under-var (inj₁ refl))
                _ (inj₂ (inj₁ refl)) →
                  Closed′-closed-under-const λ where
                    _ (inj₁ refl) → Closed′-closed-under-const λ where
                      _ (inj₁ refl) → Closed→Closed′ $ rep-closed v-n
                    _ (inj₂ (inj₁ refl)) →
                      Closed′-closed-under-const λ _ ()

  f : Exp → Computable-function ℕ Bool Bool-set
  f p = computable-function
    (λ n → terminates-in-Bool (p , n))
    f′
    (Closed′-closed-under-lambda $
     Closed′-closed-under-apply
       (Closed→Closed′ term-in-closed)
       (Closed′-closed-under-const λ where
          _ (inj₁ refl)        → Closed→Closed′ $ rep-closed p
          _ (inj₂ (inj₁ refl)) → Closed′-closed-under-var (inj₁ refl)))
    (λ n →
       apply
         (lambda v-n (
            apply term-in (const c-pair (⌜ p ⌝ ∷ var v-n ∷ []))))
         ⌜ n ⌝                                                     ⟶⟨ apply lambda (rep⇓rep n) ⟩

       apply (term-in [ v-n ← ⌜ n ⌝ ])
         (const c-pair (⌜ p ⌝ [ v-n ← ⌜ n ⌝ ] ∷ ⌜ n ⌝ ∷ []))       ≡⟨ remove-substs ((term-in , term-in-closed) ∷ []) ⟩⟶

       apply term-in ⌜ p , n ⌝                                     ⇓⟨ term-in-ok (p , n) (terminates-in-Bool (p , n)) (lift refl) ⟩■

       ⌜ terminates-in-Bool (p , n) ⌝)
    where
    f′ =
      lambda v-n (apply term-in (const c-pair (⌜ p ⌝ ∷ var v-n ∷ [])))

  g : Computable-function ℕ Bool Bool-set
  g = computable-function
    (λ _ → false)
    g′
    (from-⊎ $ closed? g′)
    (λ n →
       apply g′ ⌜ n ⌝  ⇓⟨ apply lambda (rep⇓rep n) (const []) ⟩■
       ⌜ false ⌝)
    where
    g′ = lambda v-underscore ⌜ false ⌝

  lemma :
    ∀ b p →
    ((∀ n → terminates-in-Bool (p , n) ≡ false) → P.not b ≡ true) →
    (¬ (∀ n → terminates-in-Bool (p , n) ≡ false) → P.not b ≡ false) →
    apply halts ⌜ p ⌝ ⇓ ⌜ b ⌝
  lemma b p hyp₁ hyp₂ =
    apply halts ⌜ p ⌝                                                ⟶⟨ apply lambda (rep⇓rep p) ⟩

    not (apply (pointwise-equal [ v-p ← ⌜ p ⌝ ]) (const c-pair (
      ⌜ lambda v-n (apply ⌜ term-in ⌝ (const c-pair (
          ⌞ apply internal-code (var v-p) ⌟ ∷
          var v-n ∷
          []))) ⌝E [ v-p ← ⌜ p ⌝ ] ∷
      ⌜ lambda v-underscore ⌜ false ⌝ ⌝ ∷
      [])))                                                          ≡⟨⟩⟶

    not (apply (pointwise-equal [ v-p ← ⌜ p ⌝ ]) (const c-pair (
      (const c-lambda (
         ⌜ v-n ⌝ ∷
         const c-apply (
           ⟨ ⌜ ⌜ term-in ⌝ ⌝E ⟩ [ v-p ← ⌜ p ⌝ ] ∷
           ⌜ const c-pair (
               ⌞ apply (internal-code [ v-p ← ⌜ p ⌝ ]) ⌜ p ⌝ ⌟ ∷
               var v-n ∷
               []) ⌝E ∷
           []) ∷
         [])) ∷
      ⌜ lambda v-underscore ⌜ false ⌝ ⌝ ∷
      [])))                                                          ≡⟨ ⟨by⟩ (⌜⌜⌝⌝E≡⌜⌝ term-in) ⟩⟶

    not (apply (pointwise-equal [ v-p ← ⌜ p ⌝ ]) (const c-pair (
      (const c-lambda (
         ⌜ v-n ⌝ ∷
         const c-apply (
           ⌜ term-in ⌝ [ v-p ← ⌜ p ⌝ ] ∷
           ⌜ const c-pair (
               ⌞ apply (internal-code [ v-p ← ⌜ p ⌝ ]) ⌜ p ⌝ ⌟ ∷
               var v-n ∷
               []) ⌝E ∷
           []) ∷
         [])) ∷
      ⌜ lambda v-underscore ⌜ false ⌝ ⌝ ∷
      [])))                                                          ≡⟨⟩⟶

    not (apply (pointwise-equal [ v-p ← ⌜ p ⌝ ]) (const c-pair (
      (const c-lambda (
         ⌜ v-n ⌝ ∷
         const c-apply (
           ⌜ term-in ⌝ [ v-p ← ⌜ p ⌝ ] ∷
           const c-const (
             ⌜ c-pair ⌝ ∷
             const c-cons (
               apply (internal-code [ v-p ← ⌜ p ⌝ ]) ⌜ p ⌝ ∷
               ⌜ var v-n ∷ [] ⌝ ∷
               []) ∷
             []) ∷
           []) ∷
         [])) ∷
      ⌜ lambda v-underscore ⌜ false ⌝ ⌝ ∷
      [])))                                                          ≡⟨ remove-substs
                                                                          ((pointwise-equal , pointwise-equal-closed) ∷
                                                                           (internal-code , internal-code-closed) ∷
                                                                           []) ⟩⟶
    not (apply pointwise-equal (const c-pair (
      (const c-lambda (
         ⌜ v-n ⌝ ∷
         const c-apply (
           ⌜ term-in ⌝ ∷
           const c-const (
             ⌜ c-pair ⌝ ∷
             const c-cons (
               apply internal-code ⌜ p ⌝ ∷
               ⌜ var v-n ∷ [] ⌝ ∷
               []) ∷
             []) ∷
           []) ∷
         [])) ∷
      ⌜ lambda v-underscore ⌜ false ⌝ ⌝ ∷
      [])))                                                          ⟶⟨ []⇓
                                                                          (case (apply→ const (here (const (there (here (const (there (here
                                                                             (const (there (here (const (here ∙))))))))))))))
                                                                          (internal-code-correct p) ⟩
    not (apply pointwise-equal (const c-pair (
      (const c-lambda (
         ⌜ v-n ⌝ ∷
         const c-apply (
           ⌜ term-in ⌝ ∷
           const c-const (
             ⌜ c-pair ⌝ ∷
             const c-cons (
               ⌜ ⌜ p ⌝ ⦂ Exp ⌝ ∷
               ⌜ var v-n ∷ [] ⌝ ∷
               []) ∷
             []) ∷
           []) ∷
         [])) ∷
      ⌜ lambda v-underscore ⌜ false ⌝ ⌝ ∷
      [])))                                                          ≡⟨⟩⟶

    not (apply pointwise-equal
      ⌜ lambda v-n (
          apply term-in (
            const c-pair (⌜ p ⌝ ∷ var v-n ∷ [])))
      , lambda v-underscore ⌜ false ⌝
      ⌝)                                                             ≡⟨⟩⟶

    not (apply pointwise-equal ⌜ f p , g ⌝)                          ⟶⟨ []⇓ (case ∙) (peq-ok (f p , g) (P.not b) (hyp₁ , hyp₂)) ⟩

    not ⌜ P.not b ⌝                                                  ⇓⟨ not-correct _ (rep⇓rep (P.not b)) ⟩

    ⌜ ⟨ P.not (P.not b) ⟩ ⌝                                          ≡⟨ ⟨by⟩ (Bool.not-involutive b) ⟩⟶

    ⌜ b ⌝                                                            ■⟨ rep-value b ⟩

  true-lemma :
    ∀ p → Terminates p → apply halts ⌜ p ⌝ ⇓ ⌜ true ⌝
  true-lemma p p⇓ = lemma true p
    ((∀ n → terminates-in-Bool (p , n) ≡ false)  →⟨ (∀-cong _ λ _ → terminates-in-Bool-false) ⟩
     (∀ n → ¬ p ⇓≤ n)                            →⟨ ¬⇓≤→¬⇓ ⟩
     ¬ Terminates p                              →⟨ _$ p⇓ ⟩
     ⊥                                           →⟨ ⊥-elim ⟩□
     false ≡ true                                □)
    (λ _ → refl)

  false-lemma :
    ∀ p → ¬ Terminates p → apply halts ⌜ p ⌝ ⇓ ⌜ false ⌝
  false-lemma p p⇑ = lemma false p
    (λ _ → refl)
    (¬ (∀ n → terminates-in-Bool (p , n) ≡ false)   →⟨ →-cong-→ (∀-cong _ λ n → sym ∘ Bool.≢⇒not≡ _ _ ∘ (_∘ sym)) id ⟩
     ¬ (∀ n → ¬ terminates-in-Bool (p , n) ≡ true)  →⟨ →-cong-→ (∀-cong _ λ _ → →-cong-→ terminates-in-Bool-true id) id ⟩
     ¬ (∀ n → ¬ p ⇓≤ n)                             →⟨ ¬¬⇓≤→¬¬⇓ ⟩
     ¬ ¬ Terminates p                               →⟨ _$ p⇑ ⟩
     ⊥                                              →⟨ ⊥-elim ⟩□
     true ≡ false                                   □)
