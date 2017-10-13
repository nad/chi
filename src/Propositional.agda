------------------------------------------------------------------------
-- The abstract syntax is a set, and the semantics is propositional
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Atom

module Propositional (atoms : χ-atoms) where

open import Equality.Propositional
open import Interval using (ext)
open import Logical-equivalence using (_⇔_)
open import Prelude hiding (const)

open import Bijection equality-with-J using (_↔_)
open import Equality.Decidable-UIP equality-with-J
open import Equality.Decision-procedures equality-with-J
open import Function-universe equality-with-J hiding (_∘_)
open import H-level equality-with-J as H-level
open import H-level.Closure equality-with-J

open import Cancellation  atoms
open import Chi           atoms
open import Deterministic atoms

open χ-atoms atoms

-- Exp has decidable equality.

mutual

  _≟_ : Decidable-equality Exp
  apply e₁₁ e₂₁ ≟ apply e₁₂ e₂₂ with e₁₁ ≟ e₁₂
  ... | no  e₁₁≢e₁₂ = no (e₁₁≢e₁₂ ∘ proj₁ ∘ cancel-apply)
  ... | yes e₁₁≡e₁₂ = ⊎-map (cong₂ apply e₁₁≡e₁₂)
                            (_∘ proj₂ ∘ cancel-apply)
                            (e₂₁ ≟ e₂₂)


  lambda x₁ e₁ ≟ lambda x₂ e₂ with x₁ V.≟ x₂
  ... | no  x₁≢x₂ = no (x₁≢x₂ ∘ proj₁ ∘ cancel-lambda)
  ... | yes x₁≡x₂ = ⊎-map (cong₂ lambda x₁≡x₂)
                          (_∘ proj₂ ∘ cancel-lambda)
                          (e₁ ≟ e₂)

  case e₁ bs₁ ≟ case e₂ bs₂ with e₁ ≟ e₂
  ... | no  e₁≢e₂ = no (e₁≢e₂ ∘ proj₁ ∘ cancel-case)
  ... | yes e₁≡e₂ = ⊎-map (cong₂ case e₁≡e₂)
                          (_∘ proj₂ ∘ cancel-case)
                          (bs₁ ≟-B⋆ bs₂)

  rec x₁ e₁ ≟ rec x₂ e₂ with x₁ V.≟ x₂
  ... | no  x₁≢x₂ = no (x₁≢x₂ ∘ proj₁ ∘ cancel-rec)
  ... | yes x₁≡x₂ = ⊎-map (cong₂ rec x₁≡x₂)
                          (_∘ proj₂ ∘ cancel-rec)
                          (e₁ ≟ e₂)

  var x₁ ≟ var x₂ = ⊎-map (cong var) (_∘ cancel-var) (x₁ V.≟ x₂)

  const c₁ es₁ ≟ const c₂ es₂ with c₁ C.≟ c₂
  ... | no  c₁≢c₂ = no (c₁≢c₂ ∘ proj₁ ∘ cancel-const)
  ... | yes c₁≡c₂ = ⊎-map (cong₂ const c₁≡c₂)
                          (_∘ proj₂ ∘ cancel-const)
                          (es₁ ≟-⋆ es₂)

  apply _ _  ≟ lambda _ _ = no (λ ())
  apply _ _  ≟ case _ _   = no (λ ())
  apply _ _  ≟ rec _ _    = no (λ ())
  apply _ _  ≟ var _      = no (λ ())
  apply _ _  ≟ const _ _  = no (λ ())
  lambda _ _ ≟ apply _ _  = no (λ ())
  lambda _ _ ≟ case _ _   = no (λ ())
  lambda _ _ ≟ rec _ _    = no (λ ())
  lambda _ _ ≟ var _      = no (λ ())
  lambda _ _ ≟ const _ _  = no (λ ())
  case _ _   ≟ apply _ _  = no (λ ())
  case _ _   ≟ lambda _ _ = no (λ ())
  case _ _   ≟ rec _ _    = no (λ ())
  case _ _   ≟ var _      = no (λ ())
  case _ _   ≟ const _ _  = no (λ ())
  rec _ _    ≟ apply _ _  = no (λ ())
  rec _ _    ≟ lambda _ _ = no (λ ())
  rec _ _    ≟ case _ _   = no (λ ())
  rec _ _    ≟ var _      = no (λ ())
  rec _ _    ≟ const _ _  = no (λ ())
  var _      ≟ apply _ _  = no (λ ())
  var _      ≟ lambda _ _ = no (λ ())
  var _      ≟ case _ _   = no (λ ())
  var _      ≟ rec _ _    = no (λ ())
  var _      ≟ const _ _  = no (λ ())
  const _ _  ≟ apply _ _  = no (λ ())
  const _ _  ≟ lambda _ _ = no (λ ())
  const _ _  ≟ case _ _   = no (λ ())
  const _ _  ≟ rec _ _    = no (λ ())
  const _ _  ≟ var _      = no (λ ())

  _≟-B_ : Decidable-equality Br
  branch c₁ xs₁ e₁ ≟-B branch c₂ xs₂ e₂ with c₁ C.≟ c₂
  ... | no  c₁≢c₂ = no (c₁≢c₂ ∘ proj₁ ∘ cancel-branch)
  ... | yes c₁≡c₂ with List.Dec._≟_ V._≟_ xs₁ xs₂
  ...   | no  xs₁≢xs₂ = no (xs₁≢xs₂ ∘ proj₁ ∘ proj₂ ∘ cancel-branch)
  ...   | yes xs₁≡xs₂ = ⊎-map (cong₂ (uncurry branch)
                                     (cong₂ _,_ c₁≡c₂ xs₁≡xs₂))
                              (_∘ proj₂ ∘ proj₂ ∘ cancel-branch)
                              (e₁ ≟ e₂)

  _≟-⋆_ : Decidable-equality (List Exp)
  []         ≟-⋆ []         = yes refl
  (e₁ ∷ es₁) ≟-⋆ (e₂ ∷ es₂) with e₁ ≟ e₂
  ... | no  e₁≢e₂ = no (e₁≢e₂ ∘ List.cancel-∷-head)
  ... | yes e₁≡e₂ = ⊎-map (cong₂ _∷_ e₁≡e₂)
                          (_∘ List.cancel-∷-tail)
                          (es₁ ≟-⋆ es₂)

  []      ≟-⋆ (_ ∷ _) = no (λ ())
  (_ ∷ _) ≟-⋆ []      = no (λ ())

  _≟-B⋆_ : Decidable-equality (List Br)
  []         ≟-B⋆ []         = yes refl
  (b₁ ∷ bs₁) ≟-B⋆ (b₂ ∷ bs₂) with b₁ ≟-B b₂
  ... | no  b₁≢b₂ = no (b₁≢b₂ ∘ List.cancel-∷-head)
  ... | yes b₁≡b₂ = ⊎-map (cong₂ _∷_ b₁≡b₂)
                          (_∘ List.cancel-∷-tail)
                          (bs₁ ≟-B⋆ bs₂)

  []      ≟-B⋆ (_ ∷ _) = no (λ ())
  (_ ∷ _) ≟-B⋆ []      = no (λ ())

-- Exp is a set.

Exp-set : Is-set Exp
Exp-set = decidable⇒set _≟_

-- An alternative definition of the semantics.

data Lookup′ (c : Const) : List Br → List Var → Exp → Set where
  here  : ∀ {c′ xs xs′ e e′ bs} →
          c ≡ c′ → xs ≡ xs′ → e ≡ e′ →
          Lookup′ c (branch c′ xs′ e′ ∷ bs) xs e
  there : ∀ {c′ xs′ e′ bs xs e} →
          c ≢ c′ → Lookup′ c bs xs e →
          Lookup′ c (branch c′ xs′ e′ ∷ bs) xs e

infixr 5 _∷_
infix  4 _[_←_]↦′_

data _[_←_]↦′_ (e : Exp) : List Var → List Exp → Exp → Set where
  []  : ∀ {e′} → e ≡ e′ → e [ [] ← [] ]↦′ e′
  _∷_ : ∀ {x xs e′ es′ e″ e‴} →
        e‴ ≡ e″ [ x ← e′ ] → e [ xs ← es′ ]↦′ e″ →
        e [ x ∷ xs ← e′ ∷ es′ ]↦′ e‴

infix 4 _⟶′_ _⟶⋆′_

mutual

  data _⟶′_ : Exp → Exp → Set where
    apply  : ∀ {e₁ e₂ x e v₂ v} →
             e₁ ⟶′ lambda x e → e₂ ⟶′ v₂ → e [ x ← v₂ ] ⟶′ v →
             apply e₁ e₂ ⟶′ v
    case   : ∀ {e bs c es xs e′ e″ v} →
             e ⟶′ const c es → Lookup′ c bs xs e′ →
             e′ [ xs ← es ]↦′ e″ → e″ ⟶′ v →
             case e bs ⟶′ v
    rec    : ∀ {x e v} → e [ x ← rec x e ] ⟶′ v → rec x e ⟶′ v
    lambda : ∀ {x x′ e e′} →
             x ≡ x′ → e ≡ e′ → lambda x e ⟶′ lambda x′ e′
    const  : ∀ {c c′ es vs} →
             c ≡ c′ → es ⟶⋆′ vs → const c es ⟶′ const c′ vs

  data _⟶⋆′_ : List Exp → List Exp → Set where
    []  : [] ⟶⋆′ []
    _∷_ : ∀ {e es v vs} → e ⟶′ v → es ⟶⋆′ vs → e ∷ es ⟶⋆′ v ∷ vs

-- The alternative definition is isomorphic to the other one.

Lookup↔Lookup′ : ∀ {c bs xs e} → Lookup c bs xs e ↔ Lookup′ c bs xs e
Lookup↔Lookup′ = record
  { surjection = record
    { logical-equivalence = record
      { to   = to
      ; from = from
      }
    ; right-inverse-of = to∘from
    }
  ; left-inverse-of = from∘to
  }
  where
  to : ∀ {c bs xs e} → Lookup c bs xs e → Lookup′ c bs xs e
  to here          = here refl refl refl
  to (there p₁ p₂) = there p₁ (to p₂)

  from : ∀ {c bs xs e} → Lookup′ c bs xs e → Lookup c bs xs e
  from (here refl refl refl) = here
  from (there p₁ p₂)         = there p₁ (from p₂)

  from∘to : ∀ {c bs xs e} (p : Lookup c bs xs e) → from (to p) ≡ p
  from∘to here          = refl
  from∘to (there p₁ p₂) rewrite from∘to p₂ = refl

  to∘from : ∀ {c bs xs e} (p : Lookup′ c bs xs e) → to (from p) ≡ p
  to∘from (here refl refl refl) = refl
  to∘from (there p₁ p₂)         rewrite to∘from p₂ = refl

↦↔↦′ : ∀ {e xs es e′} → e [ xs ← es ]↦ e′ ↔ e [ xs ← es ]↦′ e′
↦↔↦′ = record
  { surjection = record
    { logical-equivalence = record
      { to   = to
      ; from = from
      }
    ; right-inverse-of = to∘from
    }
  ; left-inverse-of = from∘to
  }
  where
  to : ∀ {e xs es e′} → e [ xs ← es ]↦ e′ → e [ xs ← es ]↦′ e′
  to []    = [] refl
  to (∷ p) = refl ∷ to p

  from : ∀ {e xs es e′} → e [ xs ← es ]↦′ e′ → e [ xs ← es ]↦ e′
  from ([] refl)  = []
  from (refl ∷ p) = ∷ from p

  from∘to : ∀ {e xs es e′} (p : e [ xs ← es ]↦ e′) → from (to p) ≡ p
  from∘to []    = refl
  from∘to (∷ p) rewrite from∘to p = refl

  to∘from : ∀ {e xs es e′} (p : e [ xs ← es ]↦′ e′) → to (from p) ≡ p
  to∘from ([] refl)  = refl
  to∘from (refl ∷ p) rewrite to∘from p = refl

⟶↔⟶′ : ∀ {e v} → e ⟶ v ↔ e ⟶′ v
⟶↔⟶′ = record
  { surjection = record
    { logical-equivalence = record
      { to   = to
      ; from = from
      }
    ; right-inverse-of = to∘from
    }
  ; left-inverse-of = from∘to
  }
  where
  mutual

    to : ∀ {e v} → e ⟶ v → e ⟶′ v
    to (apply p q r)  = apply (to p) (to q) (to r)
    to (case p q r s) = case (to p) (_↔_.to Lookup↔Lookup′ q)
                             (_↔_.to ↦↔↦′ r) (to s)
    to (rec p)        = rec (to p)
    to lambda         = lambda refl refl
    to (const ps)     = const refl (to⋆ ps)

    to⋆ : ∀ {e v} → e ⟶⋆ v → e ⟶⋆′ v
    to⋆ []       = []
    to⋆ (p ∷ ps) = to p ∷ to⋆ ps

  mutual

    from : ∀ {e v} → e ⟶′ v → e ⟶ v
    from (apply p q r)      = apply (from p) (from q) (from r)
    from (case p q r s)     = case (from p) (_↔_.from Lookup↔Lookup′ q)
                                   (_↔_.from ↦↔↦′ r) (from s)
    from (rec p)            = rec (from p)
    from (lambda refl refl) = lambda
    from (const refl ps)    = const (from⋆ ps)

    from⋆ : ∀ {e v} → e ⟶⋆′ v → e ⟶⋆ v
    from⋆ []       = []
    from⋆ (p ∷ ps) = from p ∷ from⋆ ps

  mutual

    from∘to : ∀ {e v} (p : e ⟶ v) → from (to p) ≡ p
    from∘to (apply p q r)  rewrite from∘to p | from∘to q | from∘to r
                           = refl
    from∘to (case p q r s) rewrite from∘to p
                                 | _↔_.left-inverse-of Lookup↔Lookup′ q
                                 | _↔_.left-inverse-of ↦↔↦′ r
                                 | from∘to s = refl
    from∘to (rec p)        rewrite from∘to p = refl
    from∘to lambda         = refl
    from∘to (const ps)     rewrite from⋆∘to⋆ ps = refl

    from⋆∘to⋆ : ∀ {e v} (ps : e ⟶⋆ v) → from⋆ (to⋆ ps) ≡ ps
    from⋆∘to⋆ []       = refl
    from⋆∘to⋆ (p ∷ ps) rewrite from∘to p | from⋆∘to⋆ ps = refl

  mutual

    to∘from : ∀ {e v} (p : e ⟶′ v) → to (from p) ≡ p
    to∘from (apply p q r)      rewrite to∘from p | to∘from q | to∘from r
                               = refl
    to∘from (case p q r s)     rewrite to∘from p
                                     | _↔_.right-inverse-of
                                         Lookup↔Lookup′ q
                                     | _↔_.right-inverse-of ↦↔↦′ r
                                     | to∘from s = refl
    to∘from (rec p)            rewrite to∘from p = refl
    to∘from (lambda refl refl) = refl
    to∘from (const refl ps)    rewrite to⋆∘from⋆ ps = refl

    to⋆∘from⋆ : ∀ {e v} (ps : e ⟶⋆′ v) → to⋆ (from⋆ ps) ≡ ps
    to⋆∘from⋆ []       = refl
    to⋆∘from⋆ (p ∷ ps) rewrite to∘from p | to⋆∘from⋆ ps = refl

-- The alternative semantics is deterministic.

Lookup′-deterministic :
  ∀ {c bs xs₁ xs₂ e₁ e₂} →
  Lookup′ c bs xs₁ e₁ → Lookup′ c bs xs₂ e₂ →
  xs₁ ≡ xs₂ × e₁ ≡ e₂
Lookup′-deterministic p q =
  Lookup-deterministic
    (_↔_.from Lookup↔Lookup′ p) (_↔_.from Lookup↔Lookup′ q) refl

↦′-deterministic :
  ∀ {e xs es e₁ e₂} →
  e [ xs ← es ]↦′ e₁ → e [ xs ← es ]↦′ e₂ → e₁ ≡ e₂
↦′-deterministic p q =
  ↦-deterministic (_↔_.from ↦↔↦′ p) (_↔_.from ↦↔↦′ q)

⟶′-deterministic : ∀ {e v₁ v₂} → e ⟶′ v₁ → e ⟶′ v₂ → v₁ ≡ v₂
⟶′-deterministic p q =
  ⟶-deterministic (_↔_.from ⟶↔⟶′ p) (_↔_.from ⟶↔⟶′ q)

-- The alternative semantics is proof-irrelevant.

Lookup′-proof-irrelevant :
  ∀ {c bs xs e} → Proof-irrelevant (Lookup′ c bs xs e)
Lookup′-proof-irrelevant (here p₁ p₂ p₃) (here q₁ q₂ q₃)
    rewrite _⇔_.to set⇔UIP C.Name-set p₁ q₁
          | _⇔_.to set⇔UIP (decidable⇒set (List.Dec._≟_ V._≟_)) p₂ q₂
          | _⇔_.to set⇔UIP Exp-set p₃ q₃
    = refl
Lookup′-proof-irrelevant (there p₁ p₂) (there q₁ q₂)
  rewrite _⇔_.to propositional⇔irrelevant
            (¬-propositional ext) p₁ q₁
        | Lookup′-proof-irrelevant p₂ q₂
  = refl

Lookup′-proof-irrelevant (here c≡c′ _ _) (there c≢c′ _) =
  ⊥-elim (c≢c′ c≡c′)
Lookup′-proof-irrelevant (there c≢c′ _) (here c≡c′ _ _) =
  ⊥-elim (c≢c′ c≡c′)

↦′-proof-irrelevant :
  ∀ {e xs es e′} → Proof-irrelevant (e [ xs ← es ]↦′ e′)
↦′-proof-irrelevant ([] p) ([] q)
  rewrite _⇔_.to set⇔UIP Exp-set p q
  = refl
↦′-proof-irrelevant (p₁ ∷ p₂) (q₁ ∷ q₂)
  with ↦′-deterministic p₂ q₂
... | refl rewrite _⇔_.to set⇔UIP Exp-set p₁ q₁
                 | ↦′-proof-irrelevant p₂ q₂
  = refl

mutual

  ⟶′-proof-irrelevant : ∀ {e v} → Proof-irrelevant (e ⟶′ v)
  ⟶′-proof-irrelevant (apply p₁ p₂ p₃) (apply q₁ q₂ q₃)
    with ⟶′-deterministic p₁ q₁
  ... | refl rewrite ⟶′-proof-irrelevant p₁ q₁
                with ⟶′-deterministic p₂ q₂
  ... | refl rewrite ⟶′-proof-irrelevant p₂ q₂
                   | ⟶′-proof-irrelevant p₃ q₃
             = refl
  ⟶′-proof-irrelevant (case p₁ p₂ p₃ p₄) (case q₁ q₂ q₃ q₄)
    with ⟶′-deterministic p₁ q₁
  ... | refl rewrite ⟶′-proof-irrelevant p₁ q₁
                with Lookup′-deterministic p₂ q₂
  ... | refl , refl rewrite Lookup′-proof-irrelevant p₂ q₂
                       with ↦′-deterministic p₃ q₃
  ... | refl rewrite ↦′-proof-irrelevant p₃ q₃
                   | ⟶′-proof-irrelevant p₄ q₄
    = refl
  ⟶′-proof-irrelevant (rec p) (rec q)
    rewrite ⟶′-proof-irrelevant p q
    = refl
  ⟶′-proof-irrelevant (lambda p₁ p₂) (lambda q₁ q₂)
    rewrite _⇔_.to set⇔UIP V.Name-set p₁ q₁
          | _⇔_.to set⇔UIP Exp-set p₂ q₂
          = refl
  ⟶′-proof-irrelevant (const p ps) (const q qs)
    rewrite _⇔_.to set⇔UIP C.Name-set p q
          | ⟶⋆′-proof-irrelevant ps qs
    = refl

  ⟶⋆′-proof-irrelevant : ∀ {es vs} → Proof-irrelevant (es ⟶⋆′ vs)
  ⟶⋆′-proof-irrelevant []       []       = refl
  ⟶⋆′-proof-irrelevant (p ∷ ps) (q ∷ qs)
    rewrite ⟶′-proof-irrelevant p q
          | ⟶⋆′-proof-irrelevant ps qs
    = refl

-- The semantics is propositional.

⟶-propositional : ∀ {e v} → Is-proposition (e ⟶ v)
⟶-propositional {e} {v} =    $⟨ ⟶′-proof-irrelevant ⟩
  Proof-irrelevant (e ⟶′ v)  ↝⟨ _⇔_.from propositional⇔irrelevant ⟩
  Is-proposition (e ⟶′ v)    ↝⟨ H-level.respects-surjection (_↔_.surjection $ inverse ⟶↔⟶′) 1 ⟩□
  Is-proposition (e ⟶ v)     □
