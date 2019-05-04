------------------------------------------------------------------------
-- Definitions of "free in" and "closed", along with some properties
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

open import Atom

module Free-variables (atoms : χ-atoms) where

open import Bag-equivalence hiding (trans)
open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude hiding (const)

open import Bijection equality-with-J using (_↔_)
open import Equality.Path.Isomorphisms equality-with-J using (ext)
open import Function-universe equality-with-J hiding (id; _∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import List equality-with-J using (_++_; foldr)

open import Chi           atoms
open import Propositional atoms
open import Values        atoms

open χ-atoms atoms

------------------------------------------------------------------------
-- Definitions

-- Free variables.

infix 4 _∈FV_

data _∈FV_ (x : Var) : Exp → Set where
  apply-left  : ∀ {e₁ e₂} → x ∈FV e₁ → x ∈FV apply e₁ e₂
  apply-right : ∀ {e₁ e₂} → x ∈FV e₂ → x ∈FV apply e₁ e₂
  lambda      : ∀ {y e} → x ≢ y → x ∈FV e → x ∈FV lambda y e
  case-head   : ∀ {e bs} → x ∈FV e → x ∈FV case e bs
  case-body   : ∀ {e bs c xs e′} →
                x ∈FV e′ → branch c xs e′ ∈ bs → ¬ x ∈ xs →
                x ∈FV case e bs
  rec         : ∀ {y e} → x ≢ y → x ∈FV e → x ∈FV rec y e
  var         : ∀ {y} → x ≡ y → x ∈FV var y
  const       : ∀ {c es e} → x ∈FV e → e ∈ es → x ∈FV const c es

-- Closed, expect that the given variables may occur.

Closed′ : List Var → Exp → Set
Closed′ xs e = ∀ x → ¬ x ∈ xs → ¬ x ∈FV e

-- The property of being closed.

Closed : Exp → Set
Closed = Closed′ []

-- Closed expressions.

Closed-exp : Set
Closed-exp = ∃ Closed

------------------------------------------------------------------------
-- Some properties

-- Closed is propositional.

Closed-propositional : ∀ {e} → Is-proposition (Closed e)
Closed-propositional =
  Π-closure ext 1 λ _ →
  Π-closure ext 1 λ _ →
  ¬-propositional ext

-- Closed-exp is a set.

Closed-exp-set : Is-set Closed-exp
Closed-exp-set =
  Σ-closure 2 Exp-set (λ _ → mono₁ 1 Closed-propositional)

-- Two closed expressions are equal if the underlying expressions are
-- equal.

closed-equal-if-expressions-equal :
  {e₁ e₂ : Closed-exp} → proj₁ e₁ ≡ proj₁ e₂ → e₁ ≡ e₂
closed-equal-if-expressions-equal eq =
  Σ-≡,≡→≡ eq (Closed-propositional _ _)

-- Constructor applications are closed.

mutual

  const→closed : ∀ {e} → Constructor-application e → Closed e
  const→closed (const c cs) x x∉[] (const x∈e e∈es) =
    consts→closed cs e∈es x x∉[] x∈e

  consts→closed : ∀ {e es} →
                  Constructor-applications es → e ∈ es → Closed e
  consts→closed []       ()
  consts→closed (c ∷ cs) (inj₁ refl) = const→closed c
  consts→closed (c ∷ cs) (inj₂ e∈es) = consts→closed cs e∈es

-- Closed e implies Closed′ xs e, for any xs.

Closed→Closed′ : ∀ {xs e} → Closed e → Closed′ xs e
Closed→Closed′ cl x _ = cl x (λ ())

-- If a variable is free in e [ x ← e′ ], then it is either free in e,
-- or it is distinct from x and free in e′.

mutual

  subst-∈FV : ∀ x e {x′ e′} →
              x′ ∈FV e [ x ← e′ ] → x′ ∈FV e × x′ ≢ x ⊎ x′ ∈FV e′
  subst-∈FV x (apply e₁ e₂) (apply-left  p)        = ⊎-map (Σ-map apply-left  id) id (subst-∈FV x e₁ p)
  subst-∈FV x (apply e₁ e₂) (apply-right p)        = ⊎-map (Σ-map apply-right id) id (subst-∈FV x e₂ p)
  subst-∈FV x (lambda y e)  (lambda x′≢y p)        with x V.≟ y
  subst-∈FV x (lambda y e)  (lambda x′≢y p)        | yes x≡y = inj₁ (lambda x′≢y p , x′≢y ∘ flip trans x≡y)
  subst-∈FV x (lambda y e)  (lambda x′≢y p)        | no  _   = ⊎-map (Σ-map (lambda x′≢y) id) id (subst-∈FV x e p)
  subst-∈FV x (case e bs)   (case-head p)          = ⊎-map (Σ-map case-head id) id (subst-∈FV x e p)
  subst-∈FV x (case e bs)   (case-body p ps x′∉xs) = ⊎-map (Σ-map (λ (p : ∃ λ _ → ∃ λ _ → ∃ λ _ → _ × _ × _) →
                                                                     let _ , _ , _ , ps , p , ∉ = p in
                                                                     case-body p ps ∉)
                                                                  id)
                                                           id
                                                           (subst-∈FV-B⋆ bs p ps x′∉xs)
  subst-∈FV x (rec y e)     p                      with x V.≟ y
  subst-∈FV x (rec y e)     (rec x′≢y p)           | yes x≡y = inj₁ (rec x′≢y p , x′≢y ∘ flip trans x≡y)
  subst-∈FV x (rec y e)     (rec x′≢y p)           | no  x≢y = ⊎-map (Σ-map (rec x′≢y) id) id (subst-∈FV x e p)
  subst-∈FV x (var y)       p                      with x V.≟ y
  subst-∈FV x (var y)       p                      | yes x≡y = inj₂ p
  subst-∈FV x (var y)       (var x′≡y)             | no  x≢y = inj₁ (var x′≡y , x≢y ∘ flip trans x′≡y ∘ sym)
  subst-∈FV x (const c es)  (const p ps)           = ⊎-map (Σ-map (λ { (_ , ps , p) → const p ps }) id) id
                                                           (subst-∈FV-⋆ es p ps)

  subst-∈FV-⋆ : ∀ {x x′ e e′} es →
                x′ ∈FV e → e ∈ es [ x ← e′ ]⋆ →
                (∃ λ e → e ∈ es × x′ ∈FV e) × x′ ≢ x ⊎ x′ ∈FV e′
  subst-∈FV-⋆ []       p ()
  subst-∈FV-⋆ (e ∷ es) p (inj₁ refl) = ⊎-map (Σ-map (λ p → _ , inj₁ refl , p) id) id (subst-∈FV _ e p)
  subst-∈FV-⋆ (e ∷ es) p (inj₂ q)    = ⊎-map (Σ-map (Σ-map id (Σ-map inj₂ id)) id) id (subst-∈FV-⋆ es p q)

  subst-∈FV-B⋆ : ∀ {x x′ e e′ c xs} bs →
                 x′ ∈FV e → branch c xs e ∈ bs [ x ← e′ ]B⋆ → ¬ x′ ∈ xs →
                 (∃ λ c → ∃ λ xs → ∃ λ e →
                    branch c xs e ∈ bs × x′ ∈FV e × ¬ x′ ∈ xs) × x′ ≢ x
                   ⊎
                 x′ ∈FV e′
  subst-∈FV-B⋆     []                   p ()
  subst-∈FV-B⋆ {x} (branch c xs e ∷ bs) p (inj₁ eq)   q with V.member x xs
  subst-∈FV-B⋆ {x} (branch c xs e ∷ bs) p (inj₁ refl) q | yes x∈xs = inj₁ ((c , xs , e , inj₁ refl , p , q) , λ x′≡x →
                                                                       q (subst (λ x → Any (x ≡_) xs) (sym x′≡x) x∈xs))
  subst-∈FV-B⋆ {x} (branch c xs e ∷ bs) p (inj₁ refl) q | no  x∉xs = ⊎-map (Σ-map (λ p → _ , _ , _ , inj₁ refl , p , q) id)
                                                                           id
                                                                           (subst-∈FV _ e p)
  subst-∈FV-B⋆     (b             ∷ bs) p (inj₂ ps)   q =
    ⊎-map (Σ-map (Σ-map _ (Σ-map _ (Σ-map _ (Σ-map inj₂ id)))) id) id
      (subst-∈FV-B⋆ bs p ps q)

------------------------------------------------------------------------
-- Various closure properties (or similar properties) for Closed′

Closed′-closed-under-apply :
  ∀ {xs e₁ e₂} →
  Closed′ xs e₁ → Closed′ xs e₂ → Closed′ xs (apply e₁ e₂)
Closed′-closed-under-apply cl-e₁ cl-e₂ x x∉xs = λ where
  (apply-left  x∈e₁) → cl-e₁ x x∉xs x∈e₁
  (apply-right x∈e₂) → cl-e₂ x x∉xs x∈e₂

Closed′-closed-under-lambda :
  ∀ {x xs e} →
  Closed′ (x ∷ xs) e → Closed′ xs (lambda x e)
Closed′-closed-under-lambda cl y y∉xs (lambda y≢x y∈e) =
  cl y [ y≢x , y∉xs ] y∈e

Closed′-closed-under-rec :
  ∀ {x xs e} →
  Closed′ (x ∷ xs) e → Closed′ xs (rec x e)
Closed′-closed-under-rec cl y y∉xs (rec y≢x y∈e) =
  cl y [ y≢x , y∉xs ] y∈e

Closed′-closed-under-case :
  ∀ {xs e bs} →
  Closed′ xs e →
  (∀ {c ys e} → branch c ys e ∈ bs → Closed′ (ys ++ xs) e) →
  Closed′ xs (case e bs)
Closed′-closed-under-case cl-e cl-bs y y∉xs = λ where
  (case-head y∈e)           → cl-e y y∉xs y∈e
  (case-body y∈e b∈bs y∉ys) →
    cl-bs b∈bs y ([ y∉ys , y∉xs ] ∘ _↔_.to (Any-++ _ _ _)) y∈e

Closed′-closed-under-const :
  ∀ {xs c es} →
  (∀ e → e ∈ es → Closed′ xs e) →
  Closed′ xs (const c es)
Closed′-closed-under-const cl y y∉xs (const y∈e e∈es) =
  cl _ e∈es y y∉xs y∈e

Closed′-closed-under-var : ∀ {x xs} → x ∈ xs → Closed′ xs (var x)
Closed′-closed-under-var x∈xs ._ x∉xs (var refl) = x∉xs x∈xs

Closed′-closed-under-subst :
  ∀ {x xs e e′} →
  Closed′ (x ∷ xs) e →
  Closed′ xs e′ →
  Closed′ xs (e [ x ← e′ ])
Closed′-closed-under-subst cl-e cl-e′ y y∉xs =
  [ uncurry (λ y∈e y≢x → cl-e y [ y≢x , y∉xs ] y∈e)
  , cl-e′ y y∉xs
  ] ∘ subst-∈FV _ _

------------------------------------------------------------------------
-- Decision procedures

-- The free variable relation, _∈FV_, is decidable.

mutual

  _∈?_ : ∀ x e → Dec (x ∈FV e)
  x ∈? apply e₁ e₂ with x ∈? e₁
  x ∈? apply e₁ e₂ | yes x∈e₁ = yes (apply-left x∈e₁)
  x ∈? apply e₁ e₂ | no x∉e₁  = ⊎-map apply-right
                                      (λ x∉e₂ → λ { (apply-left  x∈e₁) → x∉e₁ x∈e₁
                                                  ; (apply-right x∈e₂) → x∉e₂ x∈e₂
                                                  })
                                      (x ∈? e₂)
  x ∈? lambda y e  with x V.≟ y
  x ∈? lambda y e  | yes x≡y = no (λ { (lambda x≢y _) → x≢y x≡y })
  x ∈? lambda y e  | no  x≢y = ⊎-map (lambda x≢y)
                                     (λ x∉e → λ { (lambda _ x∈e) → x∉e x∈e })
                                     (x ∈? e)
  x ∈? rec y e     with x V.≟ y
  x ∈? rec y e     | yes x≡y = no (λ { (rec x≢y _) → x≢y x≡y })
  x ∈? rec y e     | no  x≢y = ⊎-map (rec x≢y)
                                     (λ x∉e → λ { (rec _ x∈e) → x∉e x∈e })
                                     (x ∈? e)
  x ∈? var y       with x V.≟ y
  x ∈? var y       | yes x≡y = yes (var x≡y)
  x ∈? var y       | no  x≢y = no (λ { (var x≡y) → x≢y x≡y })
  x ∈? const c es  = ⊎-map (λ { (_ , e∈es , x∈e) → const x∈e e∈es })
                           (λ x∉es → λ { (const x∈e e∈es) →
                                         x∉es (_ , e∈es , x∈e) })
                           (x ∈?-⋆ es)
  x ∈? case e bs   with x ∈? e
  x ∈? case e bs   | yes x∈e = yes (case-head x∈e)
  x ∈? case e bs   | no  x∉e = ⊎-map (λ { (_ , _ , _ , xs→e∈bs , x∈e , x∉xs) →
                                            case-body x∈e xs→e∈bs x∉xs })
                                     (λ x∉bs → λ { (case-head x∈e)              → x∉e x∈e
                                                 ; (case-body x∈e xs→e∈bs x∉xs) →
                                                     x∉bs (_ , _ , _ , xs→e∈bs , x∈e , x∉xs)
                                                 })
                                     (x ∈?-B⋆ bs)

  _∈?-⋆_ : ∀ x es → Dec (∃ λ e → e ∈ es × x ∈FV e)
  x ∈?-⋆ []       = no (λ { (_ , () , _) })
  x ∈?-⋆ (e ∷ es) with x ∈? e
  x ∈?-⋆ (e ∷ es) | yes x∈e = yes (_ , inj₁ refl , x∈e)
  x ∈?-⋆ (e ∷ es) | no  x∉e =
    ⊎-map (Σ-map id (Σ-map inj₂ id))
          (λ x∉es → λ { (_ , inj₁ refl , x∈e) → x∉e x∈e
                      ; (_ , inj₂ e∈es , x∈e) → x∉es (_ , e∈es , x∈e)
                      })
          (x ∈?-⋆ es)

  _∈?-B⋆_ :
    ∀ x bs →
    Dec (∃ λ c → ∃ λ xs → ∃ λ e →
           branch c xs e ∈ bs × x ∈FV e × ¬ x ∈ xs)
  x ∈?-B⋆ []                   = no λ { (_ , _ , _ , () , _) }

  x ∈?-B⋆ (branch c xs e ∷ bs) with x ∈?-B⋆ bs
  x ∈?-B⋆ (branch c xs e ∷ bs) | yes x∈bs =
    yes (Σ-map id (Σ-map id (Σ-map id (Σ-map inj₂ id))) x∈bs)

  x ∈?-B⋆ (branch c xs e ∷ bs) | no  x∉bs with V.member x xs
  x ∈?-B⋆ (branch c xs e ∷ bs) | no  x∉bs | yes x∈xs =
    no (λ { (_ , _ , _ , inj₁ refl , _   , x∉xs) → x∉xs x∈xs
          ; (_ , _ , _ , inj₂ e∈es , x∈e , x∉xs) →
              x∉bs (_ , _ , _ , e∈es , x∈e , x∉xs)
          })

  x ∈?-B⋆ (branch c xs e ∷ bs) | no  x∉bs | no  x∉xs =
    ⊎-map (λ x∈e → _ , _ , _ , inj₁ refl , x∈e , x∉xs)
          (λ x∉e → λ { (_ , _ , _ , inj₁ refl , x∈e , _)    → x∉e x∈e
                     ; (_ , _ , _ , inj₂ e∈es , x∈e , x∉xs) →
                         x∉bs (_ , _ , _ , e∈es , x∈e , x∉xs)
                     })
          (x ∈? e)

-- The Closed′ relation is decidable.

mutual

  closed′? : ∀ e xs → Dec (Closed′ xs e)
  closed′? (apply e₁ e₂) xs with closed′? e₁ xs
  closed′? (apply e₁ e₂) xs | no ¬cl₁ = no (¬cl₁ ∘ (λ cl₁ x x∉xs → cl₁ x x∉xs ∘ apply-left))
  closed′? (apply e₁ e₂) xs | yes cl₁ = ⊎-map (Closed′-closed-under-apply cl₁)
                                              (_∘ (λ cl₂ x x∉xs → cl₂ x x∉xs ∘ apply-right))
                                              (closed′? e₂ xs)
  closed′? (lambda x e)  xs = ⊎-map Closed′-closed-under-lambda
                                    (λ ¬cl cl → ¬cl (λ y y∉x∷xs y∈e → cl y (y∉x∷xs ∘ inj₂)
                                                                           (lambda (y∉x∷xs ∘ inj₁) y∈e)))
                                    (closed′? e (x ∷ xs))
  closed′? (rec x e)     xs = ⊎-map Closed′-closed-under-rec
                                    (λ ¬cl cl → ¬cl (λ y y∉x∷xs y∈e → cl y (y∉x∷xs ∘ inj₂)
                                                                           (rec (y∉x∷xs ∘ inj₁) y∈e)))
                                    (closed′? e (x ∷ xs))
  closed′? (var x)       xs = ⊎-map Closed′-closed-under-var
                                    (λ x∉xs cl → cl x x∉xs (var refl))
                                    (V.member x xs)
  closed′? (const c es)  xs = ⊎-map Closed′-closed-under-const
                                    (λ ¬cl cl → ¬cl (λ _ e∈es x x∉xs x∈e →
                                                       cl x x∉xs (const x∈e e∈es)))
                                    (closed′?-⋆ es xs)
  closed′? (case e bs)   xs with closed′? e xs
  closed′? (case e bs)   xs | no  ¬cl-e = no (λ cl → ¬cl-e (λ x x∉xs →
                                                              cl x x∉xs ∘ case-head))
  closed′? (case e bs)   xs | yes cl-e  =
    ⊎-map (Closed′-closed-under-case cl-e)
          (λ ¬cl-bs cl → ¬cl-bs (λ b∈bs x x∉ys++xs x∈e →
             let ¬[x∈ys⊎x∈xs] = x∉ys++xs ∘ _↔_.from (Any-++ _ _ _) in
             cl x (¬[x∈ys⊎x∈xs] ∘ inj₂)
               (case-body x∈e b∈bs (¬[x∈ys⊎x∈xs] ∘ inj₁))))
          (closed′?-B⋆ bs xs)

  closed′?-⋆ : ∀ es xs → Dec (∀ e → e ∈ es → Closed′ xs e)
  closed′?-⋆ []       xs = yes (λ _ ())
  closed′?-⋆ (e ∷ es) xs with closed′? e xs
  closed′?-⋆ (e ∷ es) xs | no  ¬cl-e = no (λ cl →
                                             ¬cl-e (cl _ (inj₁ refl)))
  closed′?-⋆ (e ∷ es) xs | yes cl-e  =
    ⊎-map (λ cl-es e → [ (λ e′≡e x x∉xs → subst (λ e → ¬ x ∈FV e)
                                                (sym e′≡e)
                                                (cl-e x x∉xs))
                       , cl-es e
                       ])
          (λ ¬cl-es cl → ¬cl-es (λ e → cl e ∘ inj₂))
          (closed′?-⋆ es xs)

  closed′?-B⋆ :
    ∀ bs xs →
    Dec (∀ {c ys e} → branch c ys e ∈ bs → Closed′ (ys ++ xs) e)
  closed′?-B⋆ []                   xs = yes (λ ())

  closed′?-B⋆ (branch c ys e ∷ bs) xs with closed′?-B⋆ bs xs
  closed′?-B⋆ (branch c ys e ∷ bs) xs | no  ¬cl-bs =
    no (λ cl → ¬cl-bs (cl ∘ inj₂))

  closed′?-B⋆ (branch c ys e ∷ bs) xs | yes cl-bs  =
    ⊎-map (λ cl-e {c′} {ys′} {e′} →
             [ (λ b′≡b x x∉ys++xs′ x∈e′ →
                  cl-e x (subst (λ ys → ¬ x ∈ ys ++ xs) (ys-lemma b′≡b)
                                x∉ys++xs′)
                         (subst (x ∈FV_) (e-lemma b′≡b) x∈e′))
             , cl-bs
             ])
          (λ ¬cl-e cl → ¬cl-e (cl (inj₁ refl)))
          (closed′? e (ys ++ xs))
    where
    e-lemma :
      ∀ {c ys e c′ ys′ e′} →
      branch c ys e ≡ branch c′ ys′ e′ → e ≡ e′
    e-lemma refl = refl

    ys-lemma :
      ∀ {c ys e c′ ys′ e′} →
      branch c ys e ≡ branch c′ ys′ e′ → ys ≡ ys′
    ys-lemma refl = refl

-- The Closed relation is decidable.

closed? : ∀ e → Dec (Closed e)
closed? e = closed′? e []

------------------------------------------------------------------------
-- Substituting something for a variable that is not free

-- If x is not free in e, then nothing happens when a term is
-- substituted for x in e.

mutual

  subst-∉ : ∀ x e {e′} → ¬ x ∈FV e → e [ x ← e′ ] ≡ e
  subst-∉ x (apply e₁ e₂) x∉ = cong₂ apply (subst-∉ x e₁ (x∉ ∘ apply-left))
                                           (subst-∉ x e₂ (x∉ ∘ apply-right))
  subst-∉ x (lambda y e)  x∉ with x V.≟ y
  subst-∉ x (lambda y e)  x∉ | yes _   = refl
  subst-∉ x (lambda y e)  x∉ | no  x≢y = cong (lambda y) (subst-∉ x e (x∉ ∘ lambda x≢y))
  subst-∉ x (case e bs)   x∉ = cong₂ case (subst-∉ x e (x∉ ∘ case-head))
                                          (subst-∉-B⋆ x bs _ (λ { (_ , _ , _ , ∈bs , x∈ , x∉xs) →
                                                                  x∉ (case-body x∈ ∈bs x∉xs) }))
  subst-∉ x (rec y e)     x∉ with x V.≟ y
  subst-∉ x (rec y e)     x∉ | yes _   = refl
  subst-∉ x (rec y e)     x∉ | no  x≢y = cong (rec y) (subst-∉ x e (x∉ ∘ rec x≢y))
  subst-∉ x (var y)       x∉ with x V.≟ y
  subst-∉ x (var y)       x∉ | yes x≡y = ⊥-elim (x∉ (var x≡y))
  subst-∉ x (var y)       x∉ | no  _   = refl
  subst-∉ x (const c es)  x∉ = cong (const c) (subst-∉-⋆ x es
                                                 (x∉ ∘ (λ { (_ , ps , p) → const p ps })))

  subst-∉-⋆ :
    ∀ x es {e′} →
    ¬ (∃ λ e → e ∈ es × x ∈FV e) →
    es [ x ← e′ ]⋆ ≡ es
  subst-∉-⋆ x []       x∉ = refl
  subst-∉-⋆ x (e ∷ es) x∉ = cong₂ _∷_ (subst-∉ x e (λ x∈ → x∉ (_ , inj₁ refl , x∈)))
                                      (subst-∉-⋆ x es (x∉ ∘ Σ-map id (Σ-map inj₂ id)))

  subst-∉-B⋆ :
    ∀ x bs e′ →
    ¬ (∃ λ c → ∃ λ xs → ∃ λ e →
         branch c xs e ∈ bs × x ∈FV e × ¬ x ∈ xs) →
    bs [ x ← e′ ]B⋆ ≡ bs
  subst-∉-B⋆ x []                   _ x∉ = refl
  subst-∉-B⋆ x (branch c xs e ∷ bs) _ x∉
    with V.member x xs
       | subst-∉-B⋆ x bs _
           (x∉ ∘ Σ-map id (Σ-map id (Σ-map id (Σ-map inj₂ id))))
  ... | yes x∈xs | eq = cong₂ _∷_ refl eq
  ... | no  x∉xs | eq = cong₂ (λ e bs → branch c xs e ∷ bs)
                              (subst-∉ x e λ x∈e →
                                 x∉ (_ , _ , _ , inj₁ refl , x∈e , x∉xs))
                              eq

-- If e is closed, then nothing happens when a term is substituted for
-- x in e.

subst-closed : ∀ x e′ {e} → Closed e → e [ x ← e′ ] ≡ e
subst-closed _ _ c = subst-∉ _ _ (c _ (λ ()))

-- An n-ary variant of the previous lemma.

substs-closed :
  ∀ e → Closed e → ∀ ps →
  foldr (λ ye → _[ proj₁ ye ← proj₂ ye ]) e ps ≡ e
substs-closed e cl []              = refl
substs-closed e cl ((y , e′) ∷ ps) =
  foldr (λ { (y , e) → _[ y ← e ] }) e ps [ y ← e′ ]  ≡⟨ cong _[ y ← e′ ] (substs-closed e cl ps) ⟩
  e [ y ← e′ ]                                        ≡⟨ subst-closed _ _ cl ⟩∎
  e                                                   ∎

------------------------------------------------------------------------
-- Evaluation and free variables

-- If a value contains a free variable, then every term that evaluates
-- to this value also contains the given free variable.

mutual

  ⇓-does-not-introduce-variables :
    ∀ {x v e} → e ⇓ v → x ∈FV v → x ∈FV e
  ⇓-does-not-introduce-variables lambda     q                = q
  ⇓-does-not-introduce-variables (const ps) (const x∈v v∈vs)
    with ⇓⋆-does-not-introduce-variables ps (_ , v∈vs , x∈v)
  ... | _ , e∈es , x∈e = const x∈e e∈es
  ⇓-does-not-introduce-variables (apply {e = e} p₁ p₂ p₃) q
    with subst-∈FV _ e (⇓-does-not-introduce-variables p₃ q)
  ... | inj₂ x∈v₂         = apply-right
                              (⇓-does-not-introduce-variables p₂ x∈v₂)
  ... | inj₁ (x∈e , x≢x′) = apply-left
                              (⇓-does-not-introduce-variables p₁
                                 (lambda x≢x′ x∈e))
  ⇓-does-not-introduce-variables (rec {e = e} p) q
    with subst-∈FV _ e (⇓-does-not-introduce-variables p q)
  ... | inj₂ x∈rec        = x∈rec
  ... | inj₁ (x∈e , x≢x′) = rec x≢x′ x∈e
  ⇓-does-not-introduce-variables {x} {w}
    (case {e = e} {bs = bs} {c = c} {es = es} {xs = xs} {e′ = e′} {e″ = e″} p₁ p₂ p₃ p₄) =

    x ∈FV w                                                   ↝⟨ ⇓-does-not-introduce-variables p₄ ⟩
    x ∈FV e″                                                  ↝⟨ lemma₁ p₃ ⟩
    (x ∈FV e′ × ¬ x ∈ xs) ⊎ ∃ (λ e″₁ → e″₁ ∈ es × x ∈FV e″₁)  ↝⟨ ⊎-map id (λ { (_ , ps , p) → const p ps }) ⟩
    (x ∈FV e′ × ¬ x ∈ xs) ⊎ x ∈FV const c es                  ↝⟨ ⊎-map (λ p → lemma₂ p₂ , p) (⇓-does-not-introduce-variables p₁) ⟩
    (branch c xs e′ ∈ bs × x ∈FV e′ × ¬ x ∈ xs) ⊎ x ∈FV e     ↝⟨ [ (λ { (ps , p , q) → case-body p ps q }) , case-head ] ⟩
    x ∈FV case e bs                                           □

    where
    lemma₁ : ∀ {e e′ x xs es} →
             e [ xs ← es ]↦ e′ → x ∈FV e′ →
             (x ∈FV e × ¬ x ∈ xs) ⊎ ∃ λ e″ → e″ ∈ es × x ∈FV e″
    lemma₁ {e′ = e′} {x} [] =
      x ∈FV e′                 ↝⟨ (λ p → inj₁ (p , (λ ()))) ⟩□
      x ∈FV e′ × ¬ x ∈ [] ⊎ _  □
    lemma₁ {e} {x = x}
           (∷_ {x = y} {xs = ys} {e′ = e′} {es′ = es′} {e″ = e″} p) =

      x ∈FV e″ [ y ← e′ ]                                           ↝⟨ subst-∈FV _ _ ⟩

      x ∈FV e″ × x ≢ y ⊎ x ∈FV e′                                   ↝⟨ ⊎-map (Σ-map (lemma₁ p) id) id ⟩

      (x ∈FV e × ¬ x ∈ ys ⊎ ∃ λ e‴ → e‴ ∈ es′ × x ∈FV e‴) × x ≢ y
        ⊎
      x ∈FV e′                                                      ↝⟨ [ uncurry (λ p x≢y → ⊎-map (Σ-map id (λ x∉ys → [ x≢y , x∉ys ]))
                                                                                                  (Σ-map id (Σ-map inj₂ id))
                                                                                                  p)
                                                                       , (λ p → inj₂ (_ , inj₁ refl , p))
                                                                       ] ⟩□
      x ∈FV e × ¬ x ∈ y ∷ ys ⊎ (∃ λ e″ → e″ ∈ e′ ∷ es′ × x ∈FV e″)  □

    lemma₂ : ∀ {c bs xs e} → Lookup c bs xs e → branch c xs e ∈ bs
    lemma₂ here        = inj₁ refl
    lemma₂ (there _ p) = inj₂ (lemma₂ p)

  ⇓⋆-does-not-introduce-variables :
    ∀ {x es vs} →
    es ⇓⋆ vs →
    (∃ λ v → v ∈ vs × x ∈FV v) →
    (∃ λ e → e ∈ es × x ∈FV e)
  ⇓⋆-does-not-introduce-variables [] = id
  ⇓⋆-does-not-introduce-variables (p ∷ ps) (v , inj₁ refl , q) =
    _ , inj₁ refl , ⇓-does-not-introduce-variables p q
  ⇓⋆-does-not-introduce-variables (p ∷ ps) (v , inj₂ v∈   , q) =
    Σ-map id (Σ-map inj₂ id)
      (⇓⋆-does-not-introduce-variables ps (v , v∈ , q))

-- A closed term's value is closed.

closed⇓closed : ∀ {e v xs} → e ⇓ v → Closed′ xs e → Closed′ xs v
closed⇓closed {e} {v} {xs} p q x x∉xs =
  x ∈FV v  ↝⟨ ⇓-does-not-introduce-variables p ⟩
  x ∈FV e  ↝⟨ q x x∉xs ⟩□
  ⊥        □

------------------------------------------------------------------------
-- More properties

-- A constructor for closed expressions.

apply-cl : Closed-exp → Closed-exp → Closed-exp
apply-cl (e₁ , cl-e₁) (e₂ , cl-e₂) =
    apply e₁ e₂
  , (Closed′-closed-under-apply
       (Closed→Closed′ cl-e₁)
       (Closed→Closed′ cl-e₂))

-- A certain "swapping" lemma does not hold.

no-swapping :
  ¬ (∀ x y e e′ e″ →
     x ≢ y →
     Closed e′ →
     Closed (e″ [ x ← e′ ]) →
     e [ x ← e′ ] [ y ← e″ [ x ← e′ ] ] ≡ e [ y ← e″ ] [ x ← e′ ])
no-swapping hyp = distinct (hyp x y e e′ e″ x≢y cl₁ cl₂)
  where
  x = V.name 0
  y = V.name 1

  e : Exp
  e = lambda x (var y)

  e′ : Exp
  e′ = const (C.name 0) []

  e″ : Exp
  e″ = var x

  x≢y : x ≢ y
  x≢y = V.distinct-codes→distinct-names (λ ())

  cl₁ : Closed e′
  cl₁ = from-⊎ (closed? e′)

  cl₂ : Closed (e″ [ x ← e′ ])
  cl₂ with x V.≟ x
  ... | no  x≢x = ⊥-elim (x≢x refl)
  ... | yes _   = cl₁

  lhs : e [ x ← e′ ] [ y ← e″ [ x ← e′ ] ] ≡ lambda x e′
  lhs with x V.≟ x
  ... | no  x≢x = ⊥-elim (x≢x refl)
  ... | yes _   with y V.≟ x
  ...   | yes y≡x = ⊥-elim (x≢y (sym y≡x))
  ...   | no  _   with y V.≟ y
  ...     | no  y≢y = ⊥-elim (y≢y refl)
  ...     | yes _   = refl

  rhs : e [ y ← e″ ] [ x ← e′ ] ≡ lambda x (var x)
  rhs with y V.≟ x
  ... | yes y≡x = ⊥-elim (x≢y (sym y≡x))
  ... | no  _   with y V.≟ y
  ...   | no  y≢y = ⊥-elim (y≢y refl)
  ...   | yes _   with x V.≟ x
  ...     | no  x≢x = ⊥-elim (x≢x refl)
  ...     | yes _   = refl

  distinct : e [ x ← e′ ] [ y ← e″ [ x ← e′ ] ] ≢
             e [ y ← e″ ] [ x ← e′ ]
  distinct rewrite lhs | rhs = λ ()
