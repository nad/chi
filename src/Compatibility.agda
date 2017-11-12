------------------------------------------------------------------------
-- Compatibility lemmas
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Atom

module Compatibility (atoms : χ-atoms) where

open import Bag-equivalence hiding (trans)
open import Equality.Propositional
open import Prelude hiding (const)
open import Tactic.By

open import List equality-with-J using (map)

open import Chi       atoms
open import Constants atoms
open import Reasoning atoms
open import Values    atoms

open χ-atoms atoms

-- A compatibility lemma that does not hold.

¬-⇓-[←]-right :
  ¬ (∀ {e′ v′} e x {v} →
     e′ ⇓ v′ → e [ x ← v′ ] ⇓ v → e [ x ← e′ ] ⇓ v)
¬-⇓-[←]-right hyp = ¬e[x←e′]⇓v (hyp e x e′⇓v′ e[x←v′]⇓v)
  where
  x : Var
  x = v-x

  e′ v′ e v : Exp
  e′ = apply (lambda v-x (var v-x)) (const c-true [])
  v′ = const c-true []
  e  = lambda v-y (var v-x)
  v  = lambda v-y (const c-true [])

  e′⇓v′ : e′ ⇓ v′
  e′⇓v′ = apply lambda (const [])
            (case v-x V.≟ v-x
             return (λ b → if b then const c-true []
                                else var v-x ⇓ v′) of (λ where
               (yes _)   → const []
               (no  x≢x) → ⊥-elim (x≢x refl)))

  lemma : ∀ v → e [ x ← v ] ≡ lambda v-y v
  lemma _ with v-x V.≟ v-y
  ... | yes x≡y = ⊥-elim (V.distinct-codes→distinct-names (λ ()) x≡y)
  ... | no  _   with v-x V.≟ v-x
  ...   | yes _   = refl
  ...   | no  x≢x = ⊥-elim (x≢x refl)

  e[x←v′]⇓v : e [ x ← v′ ] ⇓ v
  e[x←v′]⇓v =
    e [ x ← v′ ]   ≡⟨ lemma _ ⟩⟶
    lambda v-y v′  ⇓⟨ lambda ⟩■
    v

  ¬e[x←e′]⇓v : ¬ e [ x ← e′ ] ⇓ v
  ¬e[x←e′]⇓v p with e [ x ← e′ ] | lemma e′
  ¬e[x←e′]⇓v () | ._ | refl

mutual

  -- Contexts.

  data Context : Set where
    ∙       : Context
    apply←_ : Context → {e : Exp} → Context
    apply→_ : {e : Exp} → Context → Context
    const   : {c : Const} → Context⋆ → Context
    case    : Context → {bs : List Br} → Context

  data Context⋆ : Set where
    here  : Context → {es : List Exp} → Context⋆
    there : {e : Exp} → Context⋆ → Context⋆

mutual

  -- Filling a context's hole (∙) with an expression.

  infix 6 _[_] _[_]⋆

  _[_] : Context → Exp → Exp
  ∙                  [ e ] = e
  apply←_ c {e = e′} [ e ] = apply (c [ e ]) e′
  apply→_ {e = e′} c [ e ] = apply e′ (c [ e ])
  const {c = c′} c   [ e ] = const c′ (c [ e ]⋆)
  case c {bs = bs}   [ e ] = case (c [ e ]) bs

  _[_]⋆ : Context⋆ → Exp → List Exp
  here c {es = es} [ e ]⋆ = (c [ e ]) ∷ es
  there {e = e′} c [ e ]⋆ = e′ ∷ (c [ e ]⋆)

mutual

  -- If e₁ terminates with v₁ and c [ v₁ ] terminates with v₂, then
  -- c [ e₁ ] also terminates with v₂.

  []⇓ :
    ∀ c {e₁ v₁ v₂} →
    e₁ ⇓ v₁ → c [ v₁ ] ⇓ v₂ → c [ e₁ ] ⇓ v₂
  []⇓ ∙ {e₁} {v₁} {v₂} p q =
    e₁  ⇓⟨ p ⟩
    v₁  ⇓⟨ q ⟩■
    v₂

  []⇓ (apply← c) p (apply q r s)  = apply ([]⇓ c p q) r s
  []⇓ (apply→ c) p (apply q r s)  = apply q ([]⇓ c p r) s
  []⇓ (const c)  p (const ps)     = const ([]⇓⋆ c p ps)
  []⇓ (case c)   p (case q r s t) = case ([]⇓ c p q) r s t

  []⇓⋆ :
    ∀ c {e v vs} →
    e ⇓ v → c [ v ]⋆ ⇓⋆ vs → c [ e ]⋆ ⇓⋆ vs
  []⇓⋆ (here  c) p (q ∷ qs) = []⇓ c p q ∷ qs
  []⇓⋆ (there c) p (q ∷ qs) = q ∷ []⇓⋆ c p qs
