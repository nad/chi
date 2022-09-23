------------------------------------------------------------------------
-- The rec construction can be encoded using λ-terms
------------------------------------------------------------------------

module Recursion-without-rec where

open import Equality.Propositional.Cubical
open import Prelude hiding (id; swap)

import Finite-subset.Listed equality-with-paths as S
import Finite-subset.Listed.Membership.Erased equality-with-paths as SM

-- To simplify the development, let's work with actual natural numbers
-- as variables and constants (see
-- Atom.one-can-restrict-attention-to-χ-ℕ-atoms).

open import Atom

open import Alpha-equivalence χ-ℕ-atoms
open import Chi               χ-ℕ-atoms
open import Compatibility     χ-ℕ-atoms
open import Constants         χ-ℕ-atoms
open import Free-variables    χ-ℕ-atoms
open import Reasoning         χ-ℕ-atoms
open import Substitution      χ-ℕ-atoms
open import Values            χ-ℕ-atoms

open χ-atoms χ-ℕ-atoms

open import Combinators using (id; id-closed)

private
  variable
    A           : Type
    R           : A → A → Type
    x y z z₁ z₂ : Var
    e e′ v      : Exp

------------------------------------------------------------------------
-- "Plain" lambda terms

-- A predicate that holds for plain lambda terms, i.e. terms that are
-- built up using only var, lambda and apply.

Plain : Exp → Type
Plain (var _)       = ⊤
Plain (lambda _ e)  = Plain e
Plain (apply e₁ e₂) = Plain e₁ × Plain e₂
Plain (case _ _)    = ⊥
Plain (rec _ _)     = ⊥
Plain (const _ _)   = ⊥

-- Plain is preserved by substitutions.

plain-subst : ∀ e → Plain e → Plain e′ → Plain (e [ x ← e′ ])
plain-subst (apply e₁ e₂) (e₁-ok , e₂-ok) e′-ok =
  plain-subst e₁ e₁-ok e′-ok , plain-subst e₂ e₂-ok e′-ok
plain-subst {x = x} (lambda y e) e-ok e′-ok with x V.≟ y
… | yes _ = e-ok
… | no _  = plain-subst e e-ok e′-ok
plain-subst {x = x} (var y) _ e′-ok with x V.≟ y
… | yes _ = e′-ok
… | no _  = _

------------------------------------------------------------------------
-- A variant of a fixpoint combinator

-- A variant of the call-by-value fixpoint combinator Θᵥ that (at the
-- time of writing) is presented on the Wikipedia page about
-- fixed-point combinators
-- (https://en.wikipedia.org/wiki/Fixed-point_combinator). There Θᵥ is
-- defined to be the application of λxy.y(λz.xxyz) to itself. I have
-- dropped the final z, and made the choice of variable name for z
-- customisable.

mutual

  F : Var → Exp
  F z = apply (f z) (f z)

  f : Var → Exp
  f z =
    lambda v-x (lambda v-y (
      apply (var v-y) (
        lambda z (
          apply (apply (var v-x) (var v-x)) (var v-y)))))

-- The expressions f z, F z and id are closed.

f-closed : Closed (f z)
f-closed =
  Closed′-closed-under-lambda $
  Closed′-closed-under-lambda $
  Closed′-closed-under-apply
    (from-⊎ (closed′? (var v-y) (v-y ∷ v-x ∷ [])))
    (Closed′-closed-under-lambda $
     Closed′-closed-under-apply
       (Closed′-closed-under-apply
          (Closed′-closed-under-var (inj₂ (inj₂ (inj₁ refl))))
          (Closed′-closed-under-var (inj₂ (inj₂ (inj₁ refl)))))
       (Closed′-closed-under-var (inj₂ (inj₁ refl))))

F-closed : Closed (F z)
F-closed = Closed′-closed-under-apply f-closed f-closed

-- F z₁ and f z₁ are α-equivalent to F z₂ and f z₂, respectively,
-- assuming that z₁ and z₂ are distinct from v-x and v-y.

f≈αf :
  z₁ ≢ v-x → z₁ ≢ v-y → z₂ ≢ v-x → z₂ ≢ v-y →
  Alpha R (f z₁) (f z₂)
f≈αf {z₁ = z₁} {z₂ = z₂} {R = R} z₁≢x z₁≢y z₂≢x z₂≢y =
  lambda (
  lambda (
  apply (var y∼y₁) (
  lambda (
  apply (
  apply (var x∼x) (var x∼x)) (
  var y∼y₂)))))
  where
  x∼x : (R [ v-x ∼ v-x ] [ v-y ∼ v-y ] [ z₁ ∼ z₂ ]) v-x v-x
  x∼x = inj₂ (z₁≢x , z₂≢x , inj₂ ((λ ()) , (λ ()) , inj₁ (refl , refl)))

  y∼y₁ : (R [ v-x ∼ v-x ] [ v-y ∼ v-y ]) v-y v-y
  y∼y₁ = inj₁ (refl , refl)

  y∼y₂ : (R [ v-x ∼ v-x ] [ v-y ∼ v-y ] [ z₁ ∼ z₂ ]) v-y v-y
  y∼y₂ = inj₂ (z₁≢y , z₂≢y , y∼y₁)

F≈αF :
  z₁ ≢ v-x → z₁ ≢ v-y → z₂ ≢ v-x → z₂ ≢ v-y →
  Alpha R (F z₁) (F z₂)
F≈αF z₁≢x z₁≢y z₂≢x z₂≢y =
  apply (f≈αf z₁≢x z₁≢y z₂≢x z₂≢y) (f≈αf z₁≢x z₁≢y z₂≢x z₂≢y)

------------------------------------------------------------------------
-- A plain alternative to rec

-- An expression former that has the same semantics as rec, but that
-- takes plain expressions to plain expressions.
--
-- Note that substitution does not necessarily behave in the same way
-- for plain-rec as for rec (see below).

plain-rec : Var → Exp → Exp
plain-rec x e =
  let z , _ = fresh′ (S.from-List (v-x ∷ v-y ∷ [])) e in
  apply (lambda z (apply (F z) (lambda x (e [ x ← apply (var x) id ]))))
    id

-- If e is a plain lambda term, then plain-rec x e is a plain
-- lambda term.

plain-rec-plain : ∀ e → Plain e → Plain (plain-rec x e)
plain-rec-plain e ok = (_ , plain-subst e ok _) , _

-- The semantic rule given for rec is admissible for plain-rec.

plain-rec-⇓ :
  ∀ e → e [ x ← plain-rec x e ] ⇓ v → plain-rec x e ⇓ v
plain-rec-⇓ {x = x} {v = v} e ⇓v =
  plain-rec x e                                                         ≡⟨⟩⟶

  apply (lambda z′
           (apply (F z′) (lambda x (e [ x ← apply (var x) id ]))))
    id                                                                  ⟶⟨ apply lambda lambda ⟩

  apply (F z′) (lambda x (e [ x ← apply (var x) id ])) [ z′ ← id ]      ≡⟨ subst-∉ z′ _ z∉apply ⟩⟶

  apply (F z′) (lambda x (e [ x ← apply (var x) id ]))                  ⟶⟨ []⇓ (apply← ∙) F⇓ ⟩

  apply (lambda v-y
           (apply (var v-y) (lambda z′ (apply (F z′) (var v-y)))))
    (lambda x (e [ x ← apply (var x) id ]))                             ⟶⟨ apply lambda lambda ⟩

  apply (var v-y) (lambda z′ (apply (F z′) (var v-y)))
    [ v-y ← lambda x (e [ x ← apply (var x) id ]) ]                     ≡⟨ cong (apply _) (lambda-step-≢ y≢z) ⟩⟶

  apply (lambda x (e [ x ← apply (var x) id ]))
    (lambda z′ (apply (F z′) (lambda x (e [ x ← apply (var x) id ]))))  ⟶⟨ apply lambda lambda ⟩

  e [ x ← apply (var x) id ]
    [ x ← lambda z′
            (apply (F z′) (lambda x (e [ x ← apply (var x) id ]))) ]    ≡⟨ fusion e ⟩⟶

  e [ x ← apply (var x) id
            [ x ← lambda z′
                    (apply (F z′)
                       (lambda x (e [ x ← apply (var x) id ]))) ] ]     ≡⟨ cong₂ (λ e₁ e₂ → e [ x ← apply e₁ e₂ ])
                                                                             (var-step-≡ (refl {x = x}))
                                                                             (subst-closed x _ id-closed) ⟩⟶

  e [ x ← plain-rec x e ]                                               ⇓⟨ ⇓v ⟩■

  v
  where
  z,f = fresh′ (S.from-List (v-x ∷ v-y ∷ [])) e

  z′ : Var
  z′ = proj₁ z,f

  z∉e : ¬ z′ ∈FV e
  z∉e = proj₁ (proj₂ z,f)

  x≢z : v-x ≢ z′
  x≢z x≡z = proj₂ (proj₂ z,f) (SM.≡→∈∷ (sym x≡z))

  y≢z : v-y ≢ z′
  y≢z y≡z = proj₂ (proj₂ z,f) (SM.∈→∈∷ (SM.≡→∈∷ (sym y≡z)))

  F⇓ :
    F z′ ⇓
    lambda v-y (apply (var v-y) (lambda z′ (apply (F z′) (var v-y))))
  F⇓ =
    apply lambda lambda
      (lambda v-y
         (apply (var v-y)
            (lambda z′ (apply (apply (var v-x) (var v-x)) (var v-y))))
         [ v-x ← f z′ ]                                                   ≡⟨⟩⟶

       lambda v-y
         (apply (var v-y)
            (lambda z′ (apply (apply (var v-x) (var v-x)) (var v-y))
               [ v-x ← f z′ ]))                                           ≡⟨ cong (lambda _) $ cong (apply _) $
                                                                             lambda-step-≢ x≢z ⟩⟶

       lambda v-y (apply (var v-y) (lambda z′ (apply (F z′) (var v-y))))  ■⟨ lambda _ _ ⟩)

  z∉apply :
    ¬ z′ ∈FV apply (F z′) (lambda x (e [ x ← apply (var x) id ]))
  z∉apply (apply-left z∈Fz) =
    F-closed z′ (λ ()) z∈Fz
  z∉apply (apply-right (lambda z≢x z∈)) with subst-∈FV x e z∈
  … | inj₁ (z∈e , _)              = z∉e z∈e
  … | inj₂ (apply-left (var z≡x)) = z≢x z≡x
  … | inj₂ (apply-right z∈id)     = id-closed z′ (λ ()) z∈id

-- Substitution of closed expressions is not in general defined in the
-- same way for plain-rec as for rec.

¬-plain-rec-subst :
  ¬ (∀ y e x e′ →
     Closed e′ →
     plain-rec y e [ x ← e′ ] ≡
     plain-rec y (if x V.≟ y then e else e [ x ← e′ ]))
¬-plain-rec-subst plain-rec-subst =
  not-equal (plain-rec-subst y′ e₁ x′ e₂ id-closed)
  where
  y′ = v-y
  x′ = v-z
  e₂ = id
  e₁ = var x′

  not-equal :
    plain-rec y′ e₁ [ x′ ← e₂ ] ≢
    plain-rec y′ (if x′ V.≟ y′ then e₁ else e₁ [ x′ ← e₂ ])
  not-equal ()

-- However, it is defined in the same way /up to α-equivalence/.

plain-rec-subst :
  ∀ x →
  Closed e′ →
  plain-rec y e [ x ← e′ ] ≈α
  plain-rec y (if x V.≟ y then e else e [ x ← e′ ])
plain-rec-subst {e′ = e′} {y = y} {e = e} x cl-e′ =
  apply (lambda z¹
           (apply (F z¹) (lambda y (e [ y ← apply (var y) id ]))))
    id [ x ← e′ ]                                                   ≡⟨ cong (apply _) $
                                                                       subst-closed x _ id-closed ⟩α
  apply (lambda z¹
           (apply (F z¹) (lambda y (e [ y ← apply (var y) id ])))
           [ x ← e′ ])
    id                                                              ≡⟨ cong (λ e → apply (lambda z¹ e) id) $
                                                                       lemma₁ (x V.≟ z¹) (x V.≟ y) ⟩α
  apply (lambda z¹
           (apply (F z¹)
              (lambda y ((if x V.≟ y then e else e [ x ← e′ ])
                           [ y ← apply (var y) id ]))))
    id                                                              ≈⟨ apply (lambda (apply (F≈αF z¹≢x z¹≢y z²≢x z²≢y)
                                                                                        (refl-Alpha _ lemma₂)))
                                                                         refl-α ⟩α∎
  apply (lambda z²
           (apply (F z²)
              (lambda y ((if x V.≟ y then e else e [ x ← e′ ])
                           [ y ← apply (var y) id ]))))
    id                                                              ∎
  where
  z¹,f₁ = fresh′ (S.from-List (v-x ∷ v-y ∷ [])) e

  z¹ : Var
  z¹ = proj₁ z¹,f₁

  z¹∉e : ¬ z¹ ∈FV e
  z¹∉e = proj₁ (proj₂ z¹,f₁)

  z¹≢x : z¹ ≢ v-x
  z¹≢x z¹≡x = proj₂ (proj₂ z¹,f₁) (SM.≡→∈∷ z¹≡x)

  z¹≢y : z¹ ≢ v-y
  z¹≢y z¹≡y = proj₂ (proj₂ z¹,f₁) (SM.∈→∈∷ (SM.≡→∈∷ z¹≡y))

  z²,f₂ =
    fresh′ (S.from-List (v-x ∷ v-y ∷ []))
      (if x V.≟ y then e else e [ x ← e′ ])

  z² : Var
  z² = proj₁ z²,f₂

  z²∉ : ¬ z² ∈FV if x V.≟ y then e else e [ x ← e′ ]
  z²∉ = proj₁ (proj₂ z²,f₂)

  z²≢x : z² ≢ v-x
  z²≢x z²≡x = proj₂ (proj₂ z²,f₂) (SM.≡→∈∷ z²≡x)

  z²≢y : z² ≢ v-y
  z²≢y z²≡y = proj₂ (proj₂ z²,f₂) (SM.∈→∈∷ (SM.≡→∈∷ z²≡y))

  x∉y-id : x ≢ y → ¬ x ∈FV apply (var y) id
  x∉y-id x≢y (apply-left (var x≡y)) = x≢y x≡y
  x∉y-id _   (apply-right x∈id)     = id-closed x (λ ()) x∈id

  lemma₁ :
    (x≟z¹ : Dec (x ≡ z¹)) (x≟y : Dec (x ≡ y)) →
    if x≟z¹
    then apply (F z¹) (lambda y (e [ y ← apply (var y) id ]))
    else apply (F z¹) (lambda y (e [ y ← apply (var y) id ]))
           [ x ← e′ ] ≡
    apply (F z¹)
      (lambda y ((if x≟y then e else e [ x ← e′ ])
                   [ y ← apply (var y) id ]))
  lemma₁ (yes _) (yes _) = refl

  lemma₁ (yes x≡z¹) (no _) =
    apply (F z¹) (lambda y (e [ y ← apply (var y) id ]))             ≡⟨ cong (apply _) $ cong (lambda _) $ cong (_[ _ ← _ ]) $ sym $
                                                                        subst-∉ x e (z¹∉e ∘ subst (_∈FV _) x≡z¹) ⟩∎
    apply (F z¹) (lambda y (e [ x ← e′ ] [ y ← apply (var y) id ]))  ∎

  lemma₁ (no _) (yes x≡y) =
    apply (F z¹ [ x ← e′ ])
      (lambda y (e [ y ← apply (var y) id ]) [ x ← e′ ])             ≡⟨ cong (λ e″ → apply e″ (lambda y (e [ y ← apply (var y) id ])
                                                                                                 [ x ← e′ ])) $
                                                                        subst-closed x e′ F-closed ⟩

    apply (F z¹) (lambda y (e [ y ← apply (var y) id ]) [ x ← e′ ])  ≡⟨ cong (apply (F z¹)) $
                                                                        lambda-step-≡ x≡y ⟩∎
    apply (F z¹) (lambda y (e [ y ← apply (var y) id ]))             ∎

  lemma₁ (no _) (no x≢y) =
    apply (F z¹ [ x ← e′ ])
      (lambda y (e [ y ← apply (var y) id ]) [ x ← e′ ])             ≡⟨ cong (λ e″ → apply e″ (lambda y (e [ y ← apply (var y) id ])
                                                                                                 [ x ← e′ ])) $
                                                                        subst-closed x e′ F-closed ⟩

    apply (F z¹) (lambda y (e [ y ← apply (var y) id ]) [ x ← e′ ])  ≡⟨ cong (apply (F z¹)) $
                                                                        lambda-step-≢ x≢y ⟩

    apply (F z¹) (lambda y (e [ y ← apply (var y) id ] [ x ← e′ ]))  ≡⟨ cong (apply _) $ cong (lambda _) $ sym $
                                                                        swap x≢y (x∉y-id x≢y) (cl-e′ _ (λ ())) e ⟩∎
    apply (F z¹) (lambda y (e [ x ← e′ ] [ y ← apply (var y) id ]))  ∎

  lemma₂ :
    ∀ z →
    z ∈FV lambda y ((if x V.≟ y then e else e [ x ← e′ ])
                      [ y ← apply (var y) id ]) →
    (_≡_ [ z¹ ∼ z² ]) z z
  lemma₂ z (lambda z≢y z∈) =
    case subst-∈FV y _ z∈ of λ where
      (inj₁ (z∈ , _)) →
        inj₂ ( z¹≢ (x V.≟ y) z∈
             , z²∉ ∘ flip (subst (_∈FV _)) z∈ ∘ sym
             , refl
             )

      (inj₂ (apply-left (var z≡y))) →
        ⊥-elim $ z≢y z≡y

      (inj₂ (apply-right ∈id)) →
        ⊥-elim $ id-closed _ (λ ()) ∈id
    where
    z¹≢ :
      ∀ x≟y →
      z ∈FV if x≟y then e else e [ x ← e′ ] →
      z¹ ≢ z
    z¹≢ (yes _) z∈ = z¹∉e ∘ flip (subst (_∈FV _)) z∈ ∘ sym
    z¹≢ (no _)  z∈ = case subst-∈FV x e z∈ of λ where
      (inj₁ (z∈ , _)) →
        z¹∉e ∘ flip (subst (_∈FV _)) z∈ ∘ sym
      (inj₂ z∈e′) →
        ⊥-elim $ cl-e′ _ (λ ()) z∈e′
