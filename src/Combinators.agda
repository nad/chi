------------------------------------------------------------------------
-- Some χ program combinators
------------------------------------------------------------------------

module Combinators where

open import Equality.Propositional
open import Prelude hiding (if_then_else_; not; const)
open import Tactic.By

open import Equality.Decision-procedures equality-with-J
import Nat equality-with-J as Nat

-- To simplify the development, let's work with actual natural numbers
-- as variables and constants (see
-- Atom.one-can-restrict-attention-to-χ-ℕ-atoms).

open import Atom

open import Chi            χ-ℕ-atoms
open import Coding         χ-ℕ-atoms
open import Constants      χ-ℕ-atoms
open import Deterministic  χ-ℕ-atoms
open import Free-variables χ-ℕ-atoms
open import Reasoning      χ-ℕ-atoms
open import Termination    χ-ℕ-atoms
open import Values         χ-ℕ-atoms

open χ-atoms χ-ℕ-atoms

import Coding.Instances.Nat

------------------------------------------------------------------------
-- A non-terminating expression

loop : Exp
loop = rec v-x (var v-x)

loop-closed : Closed loop
loop-closed =
  Closed′-closed-under-rec $
  Closed′-closed-under-var (inj₁ refl)

¬loop⇓ : ¬ Terminates loop
¬loop⇓ (_ , p) = lemma p
  where
  lemma : ∀ {w} → ¬ loop ⇓ w
  lemma (rec p) with v-x V.≟ v-x
  ... | no  x≢x = x≢x refl
  ... | yes _   = lemma p

------------------------------------------------------------------------
-- Natural numbers

-- Equality of natural numbers.

private

  equal-ℕ′ : Exp
  equal-ℕ′ =
    rec v-equal (lambda v-m (lambda v-n (case (var v-m) branches)))
    module Equal-ℕ where
    zero-branches =
      branch c-zero [] (const c-true []) ∷
      branch c-suc (v-n ∷ []) (const c-false []) ∷
      []

    suc-branches =
      branch c-zero [] (const c-false []) ∷
      branch c-suc (v-n ∷ []) (
        apply (apply (var v-equal) (var v-m)) (var v-n)) ∷
      []

    branches =
      branch c-zero [] (case (var v-n) zero-branches) ∷
      branch c-suc (v-m ∷ []) (case (var v-n) suc-branches) ∷
      []

equal-ℕ : Exp → Exp → Exp
equal-ℕ e₁ e₂ = apply (apply equal-ℕ′ e₁) e₂

equal-ℕ-closed :
  ∀ {xs e₁ e₂} →
  Closed′ xs e₁ → Closed′ xs e₂ → Closed′ xs (equal-ℕ e₁ e₂)
equal-ℕ-closed {xs} cl-e₁ cl-e₂ =
  Closed′-closed-under-apply
    (Closed′-closed-under-apply
       (from-⊎ (closed′? equal-ℕ′ xs))
       cl-e₁)
    cl-e₂

equal-ℕ-correct :
  ∀ m n →
  equal-ℕ ⌜ m ⌝ ⌜ n ⌝ ⇓
  ⌜ Prelude.if m Nat.≟ n then true else false ⌝
equal-ℕ-correct m n =
  equal-ℕ ⌜ m ⌝ ⌜ n ⌝                               ⟶⟨⟩

  apply (apply equal-ℕ′ ⌜ m ⌝) ⌜ n ⌝                ⟶⟨ apply (apply (rec lambda) (rep⇓rep m) lambda) (rep⇓rep n) ⟩

  case (⌜ m ⌝ [ v-n ← ⌜ n ⌝ ])
    (branches [ v-equal ← equal-ℕ′ ]B⋆
              [ v-m ← ⌜ m ⌝ ]B⋆ [ v-n ← ⌜ n ⌝ ]B⋆)  ≡⟨ by (subst-rep m) ⟩⟶

  case ⌜ m ⌝
    (branches [ v-equal ← equal-ℕ′ ]B⋆
              [ v-m ← ⌜ m ⌝ ]B⋆ [ v-n ← ⌜ n ⌝ ]B⋆)  ⇓⟨ lemma m n ⟩■

  ⌜ Prelude.if m Nat.≟ n then true else false ⌝
  where
  open Equal-ℕ

  lemma :
    ∀ m n →
    case ⌜ m ⌝
      (branches [ v-equal ← equal-ℕ′ ]B⋆
                [ v-m ← ⌜ m ⌝ ]B⋆ [ v-n ← ⌜ n ⌝ ]B⋆)
      ⇓
    ⌜ Prelude.if m Nat.≟ n then true else false ⌝
  lemma zero zero =
    case ⌜ zero ⌝
      (branches [ v-equal ← equal-ℕ′ ]B⋆
                [ v-m ← ⌜ zero ⌝ ]B⋆ [ v-n ← ⌜ zero ⌝ ]B⋆)  ⟶⟨ _⇓_.case (rep⇓rep zero) here [] ⟩

    case ⌜ zero ⌝ zero-branches                             ⇓⟨ case (rep⇓rep zero) here [] (rep⇓rep (true ⦂ Bool)) ⟩■

    ⌜ true ⦂ Bool ⌝

  lemma zero (suc n) =
    case ⌜ zero ⌝
      (branches [ v-equal ← equal-ℕ′ ]B⋆
                [ v-m ← ⌜ zero ⌝ ]B⋆ [ v-n ← ⌜ suc n ⌝ ]B⋆)  ⟶⟨ case (rep⇓rep zero) here [] ⟩

    case ⌜ suc n ⌝ zero-branches                             ⇓⟨ case (rep⇓rep (suc n)) (there (λ ()) here) (∷ [])
                                                                     (rep⇓rep (false ⦂ Bool)) ⟩■
    ⌜ false ⦂ Bool ⌝

  lemma (suc m) zero =
    case ⌜ suc m ⌝
      (branches [ v-equal ← equal-ℕ′ ]B⋆
                [ v-m ← ⌜ suc m ⌝ ]B⋆ [ v-n ← ⌜ zero ⌝ ]B⋆)     ⟶⟨ case (rep⇓rep (suc m)) (there (λ ()) here) (∷ []) ⟩

    case ⌜ zero ⌝
      (suc-branches [ v-equal ← equal-ℕ′ ]B⋆ [ v-m ← ⌜ m ⌝ ]B⋆
                    [ v-n ← ⌜ zero ⌝ ]B⋆)                       ⇓⟨ case (rep⇓rep zero) here [] (rep⇓rep (false ⦂ Bool)) ⟩■

    ⌜ false ⦂ Bool ⌝

  lemma (suc m) (suc n) =
    case ⌜ suc m ⌝
      (branches [ v-equal ← equal-ℕ′ ]B⋆
                [ v-m ← ⌜ suc m ⌝ ]B⋆ [ v-n ← ⌜ suc n ⌝ ]B⋆)    ⟶⟨ case (rep⇓rep (suc m)) (there (λ ()) here) (∷ []) ⟩

    case (⌜ suc n ⌝ [ v-m ← ⌜ m ⌝ ])
      (suc-branches [ v-equal ← equal-ℕ′ ]B⋆ [ v-m ← ⌜ m ⌝ ]B⋆
                    [ v-n ← ⌜ suc n ⌝ ]B⋆)                      ≡⟨ by (subst-rep (suc n)) ⟩⟶

    case ⌜ suc n ⌝
      (suc-branches [ v-equal ← equal-ℕ′ ]B⋆ [ v-m ← ⌜ m ⌝ ]B⋆
                    [ v-n ← ⌜ suc n ⌝ ]B⋆)                      ⟶⟨ case (rep⇓rep (suc n)) (there (λ ()) here) (∷ []) ⟩

    apply (apply equal-ℕ′ (⌜ m ⌝ [ v-n ← ⌜ n ⌝ ])) ⌜ n ⌝        ≡⟨ by (subst-rep m) ⟩⟶

    apply (apply equal-ℕ′ ⌜ m ⌝) ⌜ n ⌝                          ⟶⟨⟩

    equal-ℕ ⌜ m ⌝ ⌜ n ⌝                                         ⇓⟨ equal-ℕ-correct m n ⟩

    ⌜ Prelude.if m Nat.≟ n then true else false ⌝               ≡⟨ by lem ⟩⟶

    ⌜ Prelude.if suc m Nat.≟ suc n then true else false ⌝       ■⟨ rep-value (Prelude.if suc m Nat.≟ suc n then true else false) ⟩
    where
    lem : Prelude.if m Nat.≟ n then true else false ≡
          Prelude.if suc m Nat.≟ suc n then true else false
    lem with m Nat.≟ n
    ... | yes _ = refl
    ... | no  _ = refl

private

  equal-ℕ-correct′ :
    ∀ m n {v} →
    equal-ℕ ⌜ m ⌝ ⌜ n ⌝ ⇓ v →
    v ≡ ⌜ Prelude.if m Nat.≟ n then true else false ⌝
  equal-ℕ-correct′ m n p =
    ⇓-deterministic p (equal-ℕ-correct m n)

-- Membership of a list of natural numbers.

private

  member′ : Exp
  member′ =
    lambda v-x body
    module Member where
    cons-branches =
      branch c-true [] (const c-true []) ∷
      branch c-false [] (apply (var v-member) (var v-xs)) ∷
      []

    branches =
      branch c-nil [] (const c-false []) ∷
      branch c-cons (v-y ∷ v-xs ∷ []) (
        case (equal-ℕ (var v-x) (var v-y))
          cons-branches) ∷
      []

    body = rec v-member (lambda v-xs (case (var v-xs) branches))

    body-closed : ∀ {xs} → Closed′ (v-x ∷ xs) body
    body-closed {xs} = from-⊎ (closed′? body (v-x ∷ xs))

member : Exp → Exp → Exp
member m ns = apply (apply member′ m) ns

member-closed :
  ∀ {xs m ns} →
  Closed′ xs m → Closed′ xs ns → Closed′ xs (member m ns)
member-closed cl-m cl-ns =
  Closed′-closed-under-apply
    (Closed′-closed-under-apply
       (Closed′-closed-under-lambda Member.body-closed)
       cl-m)
    cl-ns

member-correct :
  ∀ m ns →
  member ⌜ m ⌝ ⌜ ns ⌝ ⇓
  ⌜ Prelude.if V.member m ns then true else false ⌝
member-correct m ns =
  member ⌜ m ⌝ ⌜ ns ⌝                                                   ⟶⟨⟩

  apply (apply member′ ⌜ m ⌝) ⌜ ns ⌝                                    ⟶⟨ apply (apply lambda (rep⇓rep m) (rec lambda)) (rep⇓rep ns) ⟩

  case ⌜ ns ⌝
    (branches [ v-x ← ⌜ m ⌝ ]B⋆ [ v-member ← body [ v-x ← ⌜ m ⌝ ] ]B⋆)  ⇓⟨ lemma ns ⟩■

  ⌜ Prelude.if V.member m ns then true else false ⌝
  where
  open Member

  lemma :
    ∀ ns →
    case ⌜ ns ⌝ (branches [ v-x ← ⌜ m ⌝ ]B⋆
                             [ v-member ← body [ v-x ← ⌜ m ⌝ ] ]B⋆)
      ⇓
    ⌜ Prelude.if V.member m ns then true else false ⌝
  lemma [] =
    case ⌜ [] ⦂ List ℕ ⌝
      (branches [ v-x ← ⌜ m ⌝ ]B⋆
                [ v-member ← body [ v-x ← ⌜ m ⌝ ] ]B⋆)           ⇓⟨ case (rep⇓rep ([] ⦂ List ℕ)) here [] (const []) ⟩■

    ⌜ false ⦂ Bool ⌝

  lemma (n ∷ ns) =
    case ⌜ n List.∷ ns ⌝
      (branches [ v-x ← ⌜ m ⌝ ]B⋆
                [ v-member ← body [ v-x ← ⌜ m ⌝ ] ]B⋆)         ⟶⟨ case (rep⇓rep (n List.∷ ns)) (there (λ ()) here) (∷ ∷ []) ⟩

    case (equal-ℕ ⟨ ⌜ m ⌝ [ v-member ← body [ v-x ← ⌜ m ⌝ ] ]
                          [ v-xs ← ⌜ ns ⌝ ] [ v-y ← ⌜ n ⌝ ] ⟩
                  ⌜ n ⌝)
      (cons-branches [ v-x ← ⌜ m ⌝ ]B⋆
                     [ v-member ← body [ v-x ← ⌜ m ⌝ ] ]B⋆
                     [ v-xs ← ⌜ ns ⌝ ]B⋆ [ v-y ← ⌜ n ⌝ ]B⋆)    ≡⟨ ⟨by⟩ (substs-rep m ((v-y , ⌜ n ⌝) ∷ (v-xs , ⌜ ns ⌝) ∷
                                                                                      (v-member , body [ v-x ← ⌜ m ⌝ ]) ∷ [])) ⟩⟶
    case (equal-ℕ ⌜ m ⌝ ⌜ n ⌝)
      (⟨ cons-branches [ v-x ← ⌜ m ⌝ ]B⋆ ⟩
                       [ v-member ← body [ v-x ← ⌜ m ⌝ ] ]B⋆
                       [ v-xs ← ⌜ ns ⌝ ]B⋆ [ v-y ← ⌜ n ⌝ ]B⋆)  ≡⟨ ⟨by⟩ (subst-∉-B⋆ _ _ ⌜ m ⌝ (from-⊎ (v-x ∈?-B⋆ cons-branches))) ⟩⟶

    case (equal-ℕ ⌜ m ⌝ ⌜ n ⌝)
      ⟨ cons-branches [ v-member ← body [ v-x ← ⌜ m ⌝ ] ]B⋆
                      [ v-xs ← ⌜ ns ⌝ ]B⋆ [ v-y ← ⌜ n ⌝ ]B⋆ ⟩  ≡⟨ ⟨by⟩ (subst-∉-B⋆ _ _ _
                                                                          λ { (._ , ._ , ._ , inj₁ refl        , const _ ()        , _)
                                                                            ; (._ , ._ , ._ , inj₂ (inj₁ refl) , y∈FV[body[x←m]ns] , _) →
                                                                              Closed′-closed-under-apply
                                                                                (Closed′-closed-under-subst body-closed (rep-closed m))
                                                                                (rep-closed ns)
                                                                                v-y (λ ()) y∈FV[body[x←m]ns]
                                                                            ; (_ , _ , _ , (inj₂ (inj₂ ())) , _) }) ⟩⟶
    case (equal-ℕ ⌜ m ⌝ ⌜ n ⌝)
      (cons-branches [ v-member ← body [ v-x ← ⌜ m ⌝ ] ]B⋆
                     [ v-xs ← ⌜ ns ⌝ ]B⋆)                      ⇓⟨ lemma′ (m Nat.≟ n) (equal-ℕ-correct m n) ⟩■

    ⌜ Prelude.if V.member m (n ∷ ns) then true else false ⌝
    where
    lemma′ :
      (m≟n : Dec (m ≡ n)) →
      equal-ℕ ⌜ m ⌝ ⌜ n ⌝
        ⇓
      ⌜ Prelude.if m≟n then true else false ⌝ →
      case (equal-ℕ ⌜ m ⌝ ⌜ n ⌝)
        (cons-branches [ v-member ← body [ v-x ← ⌜ m ⌝ ] ]B⋆
                       [ v-xs ← ⌜ ns ⌝ ]B⋆)
        ⇓
      ⌜ Prelude.if V.member m (n ∷ ns) then true else false ⌝
    lemma′ (yes m≡n) hyp =
      case (equal-ℕ ⌜ m ⌝ ⌜ n ⌝)
        (cons-branches [ v-member ← body [ v-x ← ⌜ m ⌝ ] ]B⋆
                       [ v-xs ← ⌜ ns ⌝ ]B⋆)                    ⟶⟨ case hyp here [] ⟩

      ⌜ true ⦂ Bool ⌝                                          ≡⟨ cong ⌜_⌝ lem ⟩⟶

      ⌜ Prelude.if V.member m (n ∷ ns) then true else false ⌝  ■⟨ rep-value (Prelude.if V.member m (n ∷ ns) then true else false) ⟩
      where
      lem : true ≡ Prelude.if V.member m (n ∷ ns) then true else false
      lem with m Nat.≟ n
      ... | yes _   = refl
      ... | no  m≢n = ⊥-elim (m≢n m≡n)

    lemma′ (no m≢n) hyp =
      case (equal-ℕ ⌜ m ⌝ ⌜ n ⌝)
        (cons-branches [ v-member ← body [ v-x ← ⌜ m ⌝ ] ]B⋆
                       [ v-xs ← ⌜ ns ⌝ ]B⋆)                    ⟶⟨ case hyp (there (λ ()) here) [] ⟩

      apply (body [ v-x ← ⌜ m ⌝ ] [ v-xs ← ⌜ ns ⌝ ]) ⌜ ns ⌝    ≡⟨ by (subst-closed v-x ⌜ ns ⌝
                                                                        (Closed′-closed-under-subst body-closed (rep-closed m))) ⟩⟶

      apply (body [ v-x ← ⌜ m ⌝ ]) ⌜ ns ⌝                      ⟶⟨ apply (rec lambda) (rep⇓rep ns) ⟩

      case ⌜ ns ⌝
        (branches [ v-x ← ⌜ m ⌝ ]B⋆
                  [ v-member ← body [ v-x ← ⌜ m ⌝ ] ]B⋆)       ⇓⟨ lemma ns ⟩

      ⌜ Prelude.if V.member m      ns  then true else false ⌝  ≡⟨ cong ⌜_⌝ lem ⟩⟶

      ⌜ Prelude.if V.member m (n ∷ ns) then true else false ⌝  ■⟨ rep-value (Prelude.if V.member m (n ∷ ns) then true else false) ⟩
      where
      lem : Prelude.if V.member m      ns  then true else false ≡
            Prelude.if V.member m (n ∷ ns) then true else false
      lem with m Nat.≟ n
      ... | yes m≡n = ⊥-elim (m≢n m≡n)
      ... | no  _   with V.member m ns
      ...   | yes _ = refl
      ...   | no  _ = refl

------------------------------------------------------------------------
-- Booleans

-- If-then-else.

infix 5 if_then_else_

if_then_else_ : Exp → Exp → Exp → Exp
if c then t else f =
  case c (branch c-true  [] t ∷
          branch c-false [] f ∷
          [])

if-then-else-closed :
  ∀ {xs c t f} →
  Closed′ xs c → Closed′ xs t → Closed′ xs f →
  Closed′ xs (if c then t else f)
if-then-else-closed c-cl t-cl f-cl =
  Closed′-closed-under-case
    c-cl
    λ where
      (inj₁ refl)        → t-cl
      (inj₂ (inj₁ refl)) → f-cl
      (inj₂ (inj₂ ()))

if-then-else-correct :
  ∀ {A : Set} ⦃ cA : Rep A Consts ⦄ {e₁ e₂ e₃}
  (b₁ : Bool) (v₂ v₃ : A) →
  e₁ ⇓ ⌜ b₁ ⌝ → e₂ ⇓ ⌜ v₂ ⌝ → e₃ ⇓ ⌜ v₃ ⌝ →
  if e₁ then e₂ else e₃ ⇓ ⌜ Prelude.if b₁ then v₂ else v₃ ⌝
if-then-else-correct true  _ _ e₁⇓ e₂⇓ e₃⇓ = case e₁⇓ here [] e₂⇓
if-then-else-correct false _ _ e₁⇓ e₂⇓ e₃⇓ =
  case e₁⇓ (there (λ ()) here) [] e₃⇓

-- Negation of booleans.

not : Exp → Exp
not e = if e then ⌜ false ⦂ Bool ⌝ else ⌜ true ⦂ Bool ⌝

not-closed : ∀ {xs e} → Closed′ xs e → Closed′ xs (not e)
not-closed cl-e =
  if-then-else-closed
    cl-e
    (Closed→Closed′ (from-⊎ (closed? ⌜ false ⦂ Bool ⌝)))
    (Closed→Closed′ (from-⊎ (closed? ⌜ true  ⦂ Bool ⌝)))

not-correct : ∀ {e} b → e ⇓ ⌜ b ⌝ → not e ⇓ ⌜ Prelude.not b ⌝
not-correct b e⇓ =
  if-then-else-correct b false true
    e⇓ (rep⇓rep (false ⦂ Bool)) (rep⇓rep (true ⦂ Bool))

-- Conjunction.

and : Exp → Exp → Exp
and e₁ e₂ = if e₁ then e₂ else ⌜ false ⦂ Bool ⌝

and-closed :
  ∀ {xs e₁ e₂} → Closed′ xs e₁ → Closed′ xs e₂ → Closed′ xs (and e₁ e₂)
and-closed cl-e₁ cl-e₂ =
  if-then-else-closed
    cl-e₁
    cl-e₂
    (Closed→Closed′ (from-⊎ (closed? ⌜ false ⦂ Bool ⌝)))

and-correct :
  ∀ {e₁ e₂} b₁ b₂ →
  e₁ ⇓ ⌜ b₁ ⌝ → e₂ ⇓ ⌜ b₂ ⌝ →
  and e₁ e₂ ⇓ ⌜ b₁ ∧ b₂ ⌝
and-correct b₁ b₂ e₁⇓ e₂⇓ =
  if-then-else-correct b₁ b₂ false e₁⇓ e₂⇓ (rep⇓rep (false ⦂ Bool))

-- Disjunction.

or : Exp → Exp → Exp
or e₁ e₂ = if e₁ then ⌜ true ⦂ Bool ⌝ else e₂

or-closed :
  ∀ {xs e₁ e₂} → Closed′ xs e₁ → Closed′ xs e₂ → Closed′ xs (or e₁ e₂)
or-closed cl-e₁ cl-e₂ =
  if-then-else-closed
    cl-e₁
    (Closed→Closed′ (from-⊎ (closed? ⌜ true ⦂ Bool ⌝)))
    cl-e₂

or-correct :
  ∀ {e₁ e₂} b₁ b₂ →
  e₁ ⇓ ⌜ b₁ ⌝ → e₂ ⇓ ⌜ b₂ ⌝ →
  or e₁ e₂ ⇓ ⌜ b₁ ∨ b₂ ⌝
or-correct b₁ b₂ e₁⇓ e₂⇓ =
  if-then-else-correct b₁ true b₂ e₁⇓ (rep⇓rep (true ⦂ Bool)) e₂⇓

-- Equality of booleans.

equal-Bool : Exp → Exp → Exp
equal-Bool e₁ e₂ =
  if e₁ then e₂ else not e₂

equal-Bool-closed :
  ∀ {xs e₁ e₂} →
  Closed′ xs e₁ → Closed′ xs e₂ → Closed′ xs (equal-Bool e₁ e₂)
equal-Bool-closed cl-e₁ cl-e₂ =
  if-then-else-closed cl-e₁ cl-e₂ (not-closed cl-e₂)

equal-Bool-correct :
  ∀ {e₁ e₂} b₁ b₂ →
  e₁ ⇓ ⌜ b₁ ⌝ → e₂ ⇓ ⌜ b₂ ⌝ →
  equal-Bool e₁ e₂ ⇓ ⌜ Prelude.if b₁ Bool.≟ b₂ then true else false ⌝
equal-Bool-correct {e₁} {e₂} b₁ b₂ e₁⇓ e₂⇓ =
  equal-Bool e₁ e₂                                  ⇓⟨ if-then-else-correct b₁ b₂ (Prelude.not b₂) e₁⇓ e₂⇓ (not-correct b₂ e₂⇓) ⟩
  ⌜ Prelude.if b₁ then b₂ else Prelude.not b₂ ⌝     ≡⟨ cong ⌜_⌝ (lemma b₁ b₂) ⟩⟶
  ⌜ Prelude.if b₁ Bool.≟ b₂ then true else false ⌝  ■⟨ rep-value (Prelude.if b₁ Bool.≟ b₂ then true else false) ⟩
  where
  lemma :
    ∀ b₁ b₂ →
    Prelude.if b₁ then b₂ else Prelude.not b₂ ≡
    Prelude.if b₁ Bool.≟ b₂ then true else false
  lemma true  true  = refl
  lemma true  false = refl
  lemma false true  = refl
  lemma false false = refl

-- An internal decoding function for booleans.

decode-Bool : Exp → Exp
decode-Bool e =
  case e
    (branch c-const (v-c ∷ v-es ∷ [])
       (equal-ℕ (var v-c) ⌜ c-true ⌝) ∷ [])

decode-Bool-closed :
  ∀ {xs e} → Closed′ xs e → Closed′ xs (decode-Bool e)
decode-Bool-closed cl-e =
  Closed′-closed-under-case
    cl-e
    λ where
      (inj₁ refl) → equal-ℕ-closed
                      (Closed′-closed-under-var
                         (from-⊎ (V.member v-c (v-c ∷ v-es ∷ _))))
                      (Closed→Closed′ (rep-closed c-true))
      (inj₂ ())

decode-Bool-correct :
  ∀ {e} (b : Bool) →
  e ⇓ ⌜ ⌜ b ⌝ ⦂ Exp ⌝ → decode-Bool e ⇓ ⌜ b ⌝
decode-Bool-correct true e⇓ =
  case e⇓ here (∷ ∷ []) (equal-ℕ-correct c-true c-true)
decode-Bool-correct false e⇓ =
  case e⇓ here (∷ ∷ []) (equal-ℕ-correct c-false c-true)
