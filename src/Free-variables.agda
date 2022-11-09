------------------------------------------------------------------------
-- Definitions of "free in" and "closed", along with some properties
------------------------------------------------------------------------

open import Atom

module Free-variables (atoms : χ-atoms) where

open import Dec
open import Equality.Propositional.Cubical
open import Logical-equivalence using (_⇔_)
open import Prelude hiding (const; swap)

open import Bag-equivalence equality-with-J as B
  using (_∈_; _∼[_]_; bag; subset)
open import Bijection equality-with-J as Bijection using (_↔_)
open import Erased.Cubical equality-with-paths as E using (Erased)
open import Equivalence equality-with-J as Eq using (_≃_)
open import Finite-subset.Listed equality-with-paths as S
  using (Finite-subset-of)
import Finite-subset.Listed.Membership.Erased equality-with-paths as SM
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional equality-with-paths as T
  using (∥_∥)
open import List equality-with-J using (_++_; foldr)
open import List.All equality-with-J as All using (All)

open import Chi           atoms
open import Propositional atoms
open import Substitution  atoms
open import Values        atoms

open χ-atoms atoms

private
  variable
    A             : Type
    bs            : List Br
    c c′          : Const
    e e₁ e₂ e′ e″ : Exp
    es            : List Exp
    x y           : Var
    xs xs′ ys     : A

private

  -- A variant of V._≟_.

  _≟V_ : (x y : Var) → E.Dec-Erased T.∥ x ≡ y ∥
  x ≟V y = E.Dec→Dec-Erased (T.ΠΠ-Dec→ΠΠ-Dec-∥∥ V._≟_ x y)

------------------------------------------------------------------------
-- Definitions

-- Free variables.

infix 4 _∈FV_

data _∈FV_ (x : Var) : Exp → Type where
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

-- Closed, except that the given variables may occur.

Closed′ : List Var → Exp → Type
Closed′ xs e = ∀ x → ¬ x ∈ xs → ¬ x ∈FV e

-- The property of being closed.

Closed : Exp → Type
Closed = Closed′ []

-- A variant of Closed′ for branches.

Closed′-Br : List Var → Br → Type
Closed′-Br xs (branch c ys e) = Closed′ (ys ++ xs) e

-- A variant of Closed for branches.

Closed-Br : Br → Type
Closed-Br = Closed′-Br []

-- Closed expressions.

Closed-exp : Type
Closed-exp = ∃ Closed

------------------------------------------------------------------------
-- Inversion lemmas for _∈_

∈apply : (x ∈FV apply e₁ e₂) ≃ (x ∈FV e₁ ⊎ x ∈FV e₂)
∈apply = Eq.↔→≃
  (λ { (apply-left  x∈) → inj₁ x∈
     ; (apply-right x∈) → inj₂ x∈
     })
  [ apply-left , apply-right ]
  [ (λ _ → refl) , (λ _ → refl) ]
  (λ { (apply-left  _) → refl
     ; (apply-right _) → refl
     })

∈lambda : (x ∈FV lambda y e) ≃ (x ≢ y × x ∈FV e)
∈lambda = Eq.↔→≃
  (λ { (lambda x≢y x∈e) → x≢y , x∈e })
  (uncurry lambda)
  (λ _ → refl)
  (λ { (lambda _ _) → refl })

∈case :
  (x ∈FV case e bs) ≃
  (x ∈FV e ⊎
   ∃ λ c → ∃ λ xs → ∃ λ e′ → x ∈FV e′ × branch c xs e′ ∈ bs × ¬ x ∈ xs)
∈case = Eq.↔→≃
  (λ { (case-head x∈)       → inj₁ x∈
     ; (case-body x∈ b∈ x∉) → inj₂ (_ , _ , _ , x∈ , b∈ , x∉)
     })
  [ case-head , (λ (_ , _ , _ , x∈ , b∈ , x∉) → case-body x∈ b∈ x∉) ]
  [ (λ _ → refl) , (λ _ → refl) ]
  (λ { (case-head _)     → refl
     ; (case-body _ _ _) → refl
     })

∈rec : (x ∈FV rec y e) ≃ (x ≢ y × x ∈FV e)
∈rec = Eq.↔→≃
  (λ { (rec x≢y x∈e) → x≢y , x∈e })
  (uncurry rec)
  (λ _ → refl)
  (λ { (rec _ _) → refl })

∈var : (x ∈FV var y) ≃ (x ≡ y)
∈var = Eq.↔→≃
  (λ { (var x≡y) → x≡y })
  var
  (λ _ → refl)
  (λ { (var _) → refl })

∈const : (x ∈FV const c es) ≃ (∃ λ e → x ∈FV e × e ∈ es)
∈const = Eq.↔→≃
  (λ { (const ∈e ∈es) → _ , ∈e , ∈es })
  (λ (_ , ∈e , ∈es) → const ∈e ∈es)
  (λ _ → refl)
  (λ { (const _ _) → refl })

------------------------------------------------------------------------
-- Characterisation lemmas for Closed′

Closed′-apply≃ :
  Closed′ xs (apply e₁ e₂) ≃ (Closed′ xs e₁ × Closed′ xs e₂)
Closed′-apply≃ {xs = xs} {e₁ = e₁} {e₂ = e₂} =
  Closed′ xs (apply e₁ e₂)                                       ↔⟨⟩
  (∀ x → ¬ x ∈ xs → ¬ x ∈FV apply e₁ e₂)                         ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → ¬-cong ext ∈apply) ⟩
  (∀ x → ¬ x ∈ xs → ¬ (x ∈FV e₁ ⊎ x ∈FV e₂))                     ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → ¬⊎↔¬×¬ ext) ⟩
  (∀ x → ¬ x ∈ xs → (¬ x ∈FV e₁ × ¬ x ∈FV e₂))                   ↔⟨ (∀-cong ext λ _ → ΠΣ-comm) ⟩
  (∀ x → (¬ x ∈ xs → ¬ x ∈FV e₁) × (¬ x ∈ xs → ¬ x ∈FV e₂))      ↔⟨ ΠΣ-comm ⟩
  (∀ x → ¬ x ∈ xs → ¬ x ∈FV e₁) × (∀ x → ¬ x ∈ xs → ¬ x ∈FV e₂)  ↔⟨⟩
  Closed′ xs e₁ × Closed′ xs e₂                                  □

Closed′-lambda≃ :
  Closed′ xs (lambda x e) ≃ Closed′ (x ∷ xs) e
Closed′-lambda≃ {xs = xs} {x = x} {e = e} =
  Closed′ xs (lambda x e)                 ↔⟨⟩
  (∀ y → ¬ y ∈ xs → ¬ y ∈FV lambda x e)   ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → ¬-cong ext ∈lambda) ⟩
  (∀ y → ¬ y ∈ xs → ¬ (y ≢ x × y ∈FV e))  ↔⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → currying) ⟩
  (∀ y → ¬ y ∈ xs → y ≢ x → ¬ y ∈FV e)    ↔⟨ (∀-cong ext λ _ → Π-comm) ⟩
  (∀ y → y ≢ x → ¬ y ∈ xs → ¬ y ∈FV e)    ↔⟨ (∀-cong ext λ _ → inverse currying) ⟩
  (∀ y → y ≢ x × ¬ y ∈ xs → ¬ y ∈FV e)    ↝⟨ (∀-cong ext λ _ → →-cong₁ {k₁ = equivalence} ext $ inverse $ ¬⊎↔¬×¬ ext) ⟩
  (∀ y → ¬ (y ≡ x ⊎ y ∈ xs) → ¬ y ∈FV e)  ↔⟨⟩
  Closed′ (x ∷ xs) e                      □

Closed′-rec≃ :
  Closed′ xs (rec x e) ≃ Closed′ (x ∷ xs) e
Closed′-rec≃ {xs = xs} {x = x} {e = e} =
  Closed′ xs (rec x e)                    ↔⟨⟩
  (∀ y → ¬ y ∈ xs → ¬ y ∈FV rec x e)      ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → ¬-cong ext ∈rec) ⟩
  (∀ y → ¬ y ∈ xs → ¬ (y ≢ x × y ∈FV e))  ↔⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → currying) ⟩
  (∀ y → ¬ y ∈ xs → y ≢ x → ¬ y ∈FV e)    ↔⟨ (∀-cong ext λ _ → Π-comm) ⟩
  (∀ y → y ≢ x → ¬ y ∈ xs → ¬ y ∈FV e)    ↔⟨ (∀-cong ext λ _ → inverse currying) ⟩
  (∀ y → y ≢ x × ¬ y ∈ xs → ¬ y ∈FV e)    ↝⟨ (∀-cong ext λ _ → →-cong₁ {k₁ = equivalence} ext $ inverse $ ¬⊎↔¬×¬ ext) ⟩
  (∀ y → ¬ (y ≡ x ⊎ y ∈ xs) → ¬ y ∈FV e)  ↔⟨⟩
  Closed′ (x ∷ xs) e                      □

Closed′-case≃ :
  Closed′ xs (case e bs) ≃ (Closed′ xs e × All (Closed′-Br xs) bs)
Closed′-case≃ {xs = xs} {e = e} {bs = bs} =
  Closed′ xs (case e bs)                                           ↔⟨⟩

  (∀ x → ¬ x ∈ xs → ¬ x ∈FV case e bs)                             ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → ¬-cong ext ∈case) ⟩

  (∀ x → ¬ x ∈ xs →
   ¬ (x ∈FV e ⊎
      ∃ λ c → ∃ λ ys → ∃ λ e′ →
        x ∈FV e′ × branch c ys e′ ∈ bs × ¬ x ∈ ys))                ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → ¬⊎↔¬×¬ ext) ⟩

  (∀ x → ¬ x ∈ xs →
   ¬ x ∈FV e ×
   ¬ ∃ λ c → ∃ λ ys → ∃ λ e′ →
       x ∈FV e′ × branch c ys e′ ∈ bs × ¬ x ∈ ys)                  ↔⟨ ΠΣ-comm F.∘
                                                                      (∀-cong ext λ _ → ΠΣ-comm) ⟩
  (∀ x → ¬ x ∈ xs → ¬ x ∈FV e) ×
  (∀ x → ¬ x ∈ xs →
   ¬ ∃ λ c → ∃ λ ys → ∃ λ e′ →
       x ∈FV e′ × branch c ys e′ ∈ bs × ¬ x ∈ ys)                  ↝⟨ ∃-cong lemma ⟩

  (∀ x → ¬ x ∈ xs → ¬ x ∈FV e) × (∀ b → b ∈ bs → Closed′-Br xs b)  ↔⟨⟩

  Closed′ xs e × All (Closed′-Br xs) bs                            □
  where
  Br′ = Const × List Var × Exp

  lemma = λ hyp →
    (∀ x → ¬ x ∈ xs →
     ¬ ∃ λ c → ∃ λ ys → ∃ λ e →
         x ∈FV e × branch c ys e ∈ bs × ¬ x ∈ ys)  ↔⟨ (∀-cong ext λ _ → ∀-cong ext λ _ →
                                                       inverse currying F.∘
                                                       (∀-cong ext λ _ →
                                                        inverse currying F.∘
                                                        (∀-cong ext λ _ →
                                                         (∀-cong ext λ _ →
                                                          currying F.∘
                                                          Π-comm F.∘
                                                          currying) F.∘
                                                         currying) F.∘
                                                        currying) F.∘
                                                       currying) ⟩
    (∀ x → ¬ x ∈ xs → ((c , ys , e) : Br′) →
     branch c ys e ∈ bs → ¬ x ∈ ys → ¬ x ∈FV e)    ↔⟨ (∀-cong ext λ _ →
                                                       (∀-cong ext λ _ →
                                                        (∀-cong ext λ _ →
                                                         inverse currying) F.∘
                                                        currying) F.∘
                                                       Π-comm) F.∘
                                                      Π-comm F.∘
                                                      inverse currying ⟩
    (((c , ys , e) : Br′) → branch c ys e ∈ bs →
     ∀ x → ¬ x ∈ xs × ¬ x ∈ ys → ¬ x ∈FV e)        ↝⟨ (∀-cong ext λ _ →
                                                       ∀-cong ext λ _ → ∀-cong ext λ _ → →-cong₁ ext $
                                                       ¬-cong ext (
                                                         inverse (B.Any-++ _ _ _) F.∘
                                                         ⊎-comm) F.∘
                                                       inverse (¬⊎↔¬×¬ ext)) ⟩
    (((c , ys , e) : Br′) → branch c ys e ∈ bs →
     ∀ x → ¬ x ∈ ys ++ xs → ¬ x ∈FV e)             ↔⟨⟩

    (((c , ys , e) : Br′) → branch c ys e ∈ bs →
     Closed′-Br xs (branch c ys e))                ↝⟨ (Π-cong ext
                                                         (Eq.↔→≃
                                                            (λ (c , ys , e) → branch c ys e)
                                                            (λ { (branch c ys e) → c , ys , e })
                                                            (λ { (branch _ _ _) → refl })
                                                            (λ _ → refl)) λ _ →
                                                         F.id) ⟩□

    (∀ b → b ∈ bs → Closed′-Br xs b)               □

Closed′-const≃ :
  Closed′ xs (const c es) ≃ All (Closed′ xs) es
Closed′-const≃ {xs = xs} {c = c} {es = es} =
  Closed′ xs (const c es)                        ↔⟨⟩
  (∀ x → ¬ x ∈ xs → ¬ x ∈FV const c es)          ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → ¬-cong ext ∈const) ⟩
  (∀ x → ¬ x ∈ xs → ¬ ∃ λ e → x ∈FV e × e ∈ es)  ↔⟨ currying F.∘
                                                    (∀-cong ext λ _ →
                                                     currying) F.∘
                                                    Π-comm F.∘
                                                    (∀-cong ext λ _ →
                                                     inverse currying F.∘
                                                     (∀-cong ext λ _ →
                                                      Π-comm F.∘
                                                      currying) F.∘
                                                     currying) F.∘
                                                    inverse currying ⟩
  (∀ e → e ∈ es → ∀ x → ¬ x ∈ xs → ¬ x ∈FV e)    ↔⟨⟩
  (∀ e → e ∈ es → Closed′ xs e)                  □

Closed′-var≃ : Closed′ xs (var x) ≃ ∥ x ∈ xs ∥
Closed′-var≃ {xs = xs} {x = x} =
  Closed′ xs (var x)                ↔⟨⟩
  (∀ y → ¬ y ∈ xs → ¬ y ∈FV var x)  ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → ¬-cong ext ∈var) ⟩
  (∀ y → ¬ y ∈ xs → ¬ y ≡ x)        ↝⟨ (∀-cong ext λ _ → →-cong₁ ext $ inverse T.¬∥∥↔¬) ⟩
  (∀ y → ¬ ∥ y ∈ xs ∥ → ¬ y ≡ x)    ↝⟨ (∀-cong ext λ _ → inverse $
                                        →≃¬→¬
                                          (λ _ _ → T.truncation-is-proposition)
                                          (λ _ → T.Dec→Dec-∥∥ (B.Decidable-∈ V._≟_ _ _))
                                          ext) ⟩
  (∀ y → y ≡ x → ∥ y ∈ xs ∥)        ↝⟨ (∀-cong ext λ _ → →-cong₁ ext ≡-comm) ⟩
  (∀ y → x ≡ y → ∥ y ∈ xs ∥)        ↝⟨ inverse $ ∀-intro _ ext ⟩□
  ∥ x ∈ xs ∥                        □

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

-- If xs is bag equivalent to ys, then Closed′ xs e and Closed′ ys e
-- are equivalent.

Closed′-≃ : xs ∼[ bag ] ys → Closed′ xs e ≃ Closed′ ys e
Closed′-≃ {xs = xs} {ys = ys} {e = e} xs≈ys =
  (∀ x → ¬ x ∈ xs → ¬ x ∈FV e)  ↝⟨ (∀-cong ext λ _ → →-cong₁ ext $ ¬-cong ext (xs≈ys _)) ⟩□
  (∀ x → ¬ x ∈ ys → ¬ x ∈FV e)  □

-- If xs is a "subset" of ys and Closed′ xs e holds, then Closed′ ys e
-- holds.

Closed′-⊆ : xs ∼[ subset ] ys → Closed′ xs e → Closed′ ys e
Closed′-⊆ {xs = xs} {ys = ys} {e = e} xs⊆ys =
  (∀ x → ¬ x ∈ xs → ¬ x ∈FV e)  →⟨ (∀-cong _ λ _ → →-cong-→ (→-cong-→ (xs⊆ys _) id) id) ⟩□
  (∀ x → ¬ x ∈ ys → ¬ x ∈FV e)  □

-- An instance of Closed′-⊆.

Closed′-++-∷ :
  ∀ {x} xs {ys e} →
  Closed′ (x ∷ xs ++ ys) e → Closed′ (xs ++ x ∷ ys) e
Closed′-++-∷ {x = x} xs {ys = ys} = Closed′-⊆ λ z →
  z ∈ x ∷ xs ++ ys         ↔⟨ F.id ⊎-cong B.Any-++ _ _ _ ⟩
  z ≡ x ⊎ z ∈ xs ⊎ z ∈ ys  ↔⟨ inverse ⊎-assoc F.∘
                              (⊎-comm ⊎-cong F.id) F.∘
                              ⊎-assoc ⟩
  z ∈ xs ⊎ z ≡ x ⊎ z ∈ ys  ↔⟨ inverse (B.Any-++ _ _ _) ⟩□
  z ∈ xs ++ x ∷ ys         □

-- If a variable is free in e [ x ← e′ ], then it is either free in e′,
-- or it is distinct from x and free in e.

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
                                                                       q (subst (_∈ _) (sym x′≡x) x∈xs))
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
Closed′-closed-under-apply = curry $ _≃_.from Closed′-apply≃

Closed′-closed-under-lambda :
  ∀ {x xs e} →
  Closed′ (x ∷ xs) e → Closed′ xs (lambda x e)
Closed′-closed-under-lambda = _≃_.from Closed′-lambda≃

Closed′-closed-under-rec :
  ∀ {x xs e} →
  Closed′ (x ∷ xs) e → Closed′ xs (rec x e)
Closed′-closed-under-rec = _≃_.from Closed′-rec≃

Closed′-closed-under-case :
  ∀ {xs e bs} →
  Closed′ xs e →
  All (Closed′-Br xs) bs →
  Closed′ xs (case e bs)
Closed′-closed-under-case = curry $ _≃_.from Closed′-case≃

Closed′-closed-under-const :
  ∀ {xs c es} →
  All (Closed′ xs) es →
  Closed′ xs (const c es)
Closed′-closed-under-const = _≃_.from Closed′-const≃

Closed′-closed-under-var : ∀ {x xs} → x ∈ xs → Closed′ xs (var x)
Closed′-closed-under-var = _≃_.from Closed′-var≃ ∘ T.∣_∣

Closed′-closed-under-subst :
  ∀ {x xs e e′} →
  Closed′ (x ∷ xs) e →
  Closed′ xs e′ →
  Closed′ xs (e [ x ← e′ ])
Closed′-closed-under-subst cl-e cl-e′ y y∉xs =
  [ uncurry (λ y∈e y≢x → cl-e y [ y≢x , y∉xs ] y∈e)
  , cl-e′ y y∉xs
  ] ∘ subst-∈FV _ _

Closed′-closed-under-[←]↦ :
  ∀ {e xs es e′ ys} →
  e [ xs ← es ]↦ e′ →
  Closed′ (xs ++ ys) e →
  All (Closed′ ys) es →
  Closed′ ys e′
Closed′-closed-under-[←]↦ {e = e} {ys = ys} [] cl =
  All (Closed′ ys) []  →⟨ (λ _ → cl) ⟩□
  Closed′ ys e         □
Closed′-closed-under-[←]↦
  {ys = ys} (∷_ {x = x} {xs = xs} {e′ = e} {es′ = es} {e″ = e′} p) cl =
  All (Closed′ ys) (e ∷ es)                 →⟨ All.All-∷ _ ⟩
  Closed′ ys e × All (Closed′ ys) es        →⟨ Σ-map id (All.map₁ λ _ → Closed′-⊆ λ _ → inj₂) ⟩
  Closed′ ys e × All (Closed′ (x ∷ ys)) es  →⟨ Σ-map id (Closed′-closed-under-[←]↦ p (Closed′-++-∷ xs cl)) ⟩
  Closed′ ys e × Closed′ (x ∷ ys) e′        →⟨ uncurry $ flip Closed′-closed-under-subst ⟩□
  Closed′ ys (e′ [ x ← e ])                 □

------------------------------------------------------------------------
-- Computing free or fresh variables

-- One can construct a finite set containing exactly the free
-- variables in a term.

mutual

  free :
    (e : Exp) →
    ∃ λ (fs : Finite-subset-of Var) → ∀ x → (x SM.∈ fs) ⇔ (x ∈FV e)
  free (apply e₁ e₂) =
    Σ-zip S._∪_
      (λ {fs₁ fs₂} hyp₁ hyp₂ x →
         x SM.∈ fs₁ S.∪ fs₂                    ↔⟨ _≃_.to SM.∈≃≃∈≃Erased E.[ SM.∈∪≃ ] ⟩
         Erased (x SM.∈ fs₁ T.∥⊎∥ x SM.∈ fs₂)  ↝⟨ T.Dec→Erased-∥∥⇔ $
                                                  Dec-⊎ (SM.member? _≟V_ _ _)
                                                        (SM.member? _≟V_ _ _) ⟩
         x SM.∈ fs₁ ⊎ x SM.∈ fs₂               ↝⟨ hyp₁ x ⊎-cong hyp₂ x ⟩
         x ∈FV e₁ ⊎ x ∈FV e₂                   ↔⟨ inverse ∈apply ⟩□
         x ∈FV apply e₁ e₂                     □)
      (free e₁) (free e₂)
  free (lambda x e) =
    Σ-map (SM.delete _≟V_ x)
      (λ {fs} hyp y →
         y SM.∈ SM.delete _≟V_ x fs  ↔⟨ SM.∈delete≃ _≟V_ ⟩
         y ≢ x × y SM.∈ fs           ↝⟨ (∃-cong λ _ → hyp y) ⟩
         y ≢ x × y ∈FV e             ↔⟨ inverse ∈lambda ⟩□
         y ∈FV lambda x e            □)
      (free e)
  free (case e bs) =
    Σ-zip S._∪_
      (λ {fs₁ fs₂} hyp₁ hyp₂ x →
         x SM.∈ fs₁ S.∪ fs₂                             ↔⟨ _≃_.to SM.∈≃≃∈≃Erased E.[ SM.∈∪≃ ] ⟩

         Erased (x SM.∈ fs₁ T.∥⊎∥ x SM.∈ fs₂)           ↝⟨ T.Dec→Erased-∥∥⇔ $
                                                           Dec-⊎ (SM.member? _≟V_ _ _)
                                                                 (SM.member? _≟V_ _ _) ⟩

         x SM.∈ fs₁ ⊎ x SM.∈ fs₂                        ↝⟨ hyp₁ x ⊎-cong hyp₂ x ⟩

         (x ∈FV e ⊎
          ∃ λ c → ∃ λ xs → ∃ λ e′ →
            x ∈FV e′ × branch c xs e′ ∈ bs × ¬ x ∈ xs)  ↔⟨ inverse ∈case ⟩□

         x ∈FV case e bs                                □)
      (free e) (free-B⋆ bs)
  free (rec x e) =
    Σ-map (SM.delete _≟V_ x)
      (λ {fs} hyp y →
         y SM.∈ SM.delete _≟V_ x fs  ↔⟨ SM.∈delete≃ _≟V_ ⟩
         y ≢ x × y SM.∈ fs           ↝⟨ (∃-cong λ _ → hyp y) ⟩
         y ≢ x × y ∈FV e             ↔⟨ inverse ∈rec ⟩□
         y ∈FV rec x e               □)
      (free e)
  free (var x) =
      S.singleton x
    , λ y →
        y SM.∈ S.singleton x  ↔⟨ _≃_.to SM.∈≃≃∈≃Erased E.[ SM.∈singleton≃ ] ⟩
        Erased T.∥ y ≡ x ∥    ↝⟨ T.Dec→Erased-∥∥⇔ (_ V.≟ _) ⟩
        y ≡ x                 ↔⟨ inverse ∈var ⟩□
        y ∈FV var x           □
  free (const c es) =
    Σ-map id
      (λ {fs} hyp x →
         x SM.∈ fs                   ↝⟨ hyp x ⟩
         (∃ λ e → x ∈FV e × e ∈ es)  ↔⟨ inverse ∈const ⟩□
         x ∈FV const c es            □)
      (free-⋆ es)

  free-⋆ :
    (es : List Exp) →
    ∃ λ (fs : Finite-subset-of Var) →
      ∀ x → (x SM.∈ fs) ⇔ (∃ λ e → x ∈FV e × e ∈ es)
  free-⋆ [] =
      S.[]
    , λ x →
        x SM.∈ S.[]                 ↔⟨ SM.∈[]≃ ⟩
        ⊥                           ↔⟨ inverse ×-right-zero ⟩
        Exp × ⊥₀                    ↔⟨ (∃-cong λ _ → inverse ×-right-zero) ⟩
        (∃ λ e → x ∈FV e × ⊥)       ↔⟨⟩
        (∃ λ e → x ∈FV e × e ∈ [])  □
  free-⋆ (e ∷ es) =
    Σ-zip S._∪_
      (λ {fs₁ fs₂} hyp₁ hyp₂ x →
         x SM.∈ fs₁ S.∪ fs₂                                           ↔⟨ _≃_.to SM.∈≃≃∈≃Erased E.[ SM.∈∪≃ ] ⟩
         Erased (x SM.∈ fs₁ T.∥⊎∥ x SM.∈ fs₂)                         ↝⟨ T.Dec→Erased-∥∥⇔ $
                                                                         Dec-⊎ (SM.member? _≟V_ _ _)
                                                                               (SM.member? _≟V_ _ _) ⟩
         x SM.∈ fs₁ ⊎ x SM.∈ fs₂                                      ↝⟨ hyp₁ x ⊎-cong hyp₂ x ⟩
         x ∈FV e ⊎ (∃ λ e′ → x ∈FV e′ × e′ ∈ es)                      ↔⟨ inverse $
                                                                         (drop-⊤-right λ _ → _⇔_.to contractible⇔↔⊤ $
                                                                          singleton-contractible _)
                                                                           ⊎-cong
                                                                         F.id ⟩
         x ∈FV e × (∃ λ e′ → e′ ≡ e) ⊎ (∃ λ e′ → x ∈FV e′ × e′ ∈ es)  ↔⟨ ∃-comm ⊎-cong F.id ⟩
         (∃ λ e′ → x ∈FV e × e′ ≡ e) ⊎ (∃ λ e′ → x ∈FV e′ × e′ ∈ es)  ↔⟨ inverse ∃-⊎-distrib-left ⟩
         (∃ λ e′ → (x ∈FV e × e′ ≡ e) ⊎ (x ∈FV e′ × e′ ∈ es))         ↔⟨ (∃-cong λ _ →
                                                                          (×-cong₁ λ e′≡e → ≡⇒↝ equivalence $ cong (_ ∈FV_) $ sym
                                                                           e′≡e)
                                                                            ⊎-cong
                                                                          F.id) ⟩
         (∃ λ e′ → (x ∈FV e′ × e′ ≡ e) ⊎ (x ∈FV e′ × e′ ∈ es))        ↔⟨ (∃-cong λ _ → inverse ×-⊎-distrib-left) ⟩
         (∃ λ e′ → x ∈FV e′ × (e′ ≡ e ⊎ e′ ∈ es))                     ↔⟨⟩
         (∃ λ e′ → x ∈FV e′ × e′ ∈ e ∷ es)                            □)
      (free e) (free-⋆ es)

  free-B :
    (b : Br) →
    ∃ λ (fs : Finite-subset-of Var) →
      ∀ x →
      (x SM.∈ fs) ⇔
      (∃ λ c → ∃ λ xs → ∃ λ e →
         x ∈FV e × branch c xs e ≡ b × ¬ x ∈ xs)
  free-B (branch c xs e) =
    Σ-map (λ fs → SM.minus _≟V_ fs (S.from-List xs))
      (λ {fs} hyp x →
         x SM.∈ SM.minus _≟V_ fs (S.from-List xs)                      ↔⟨ SM.∈minus≃ ⟩

         x SM.∈ fs × x SM.∉ S.from-List xs                             ↔⟨ (∃-cong λ _ → ¬-cong ext (inverse
                                                                           SM.∥∈∥≃∈-from-List)) ⟩

         x SM.∈ fs × ¬ T.∥ x ∈ xs ∥                                    ↔⟨ (∃-cong λ _ → T.¬∥∥↔¬) ⟩

         x SM.∈ fs × ¬ x ∈ xs                                          ↝⟨ hyp x ×-cong F.id ⟩

         x ∈FV e × ¬ x ∈ xs                                            ↔⟨ (inverse $ drop-⊤-right λ _ →
                                                                           ×-left-identity F.∘ ×-left-identity) ⟩

         (x ∈FV e × ¬ x ∈ xs) × ⊤ × ⊤ × ⊤                              ↔⟨ (∃-cong λ _ → inverse $
                                                                           (_⇔_.to contractible⇔↔⊤ $ singleton-contractible _)
                                                                             ×-cong
                                                                           (_⇔_.to contractible⇔↔⊤ $ singleton-contractible _)
                                                                             ×-cong
                                                                           (_⇔_.to contractible⇔↔⊤ $ singleton-contractible _)) ⟩
         (x ∈FV e × ¬ x ∈ xs) ×
         (∃ λ c′ → c′ ≡ c) × (∃ λ xs′ → xs′ ≡ xs) × (∃ λ e′ → e′ ≡ e)  ↔⟨ (∃-cong λ _ →
                                                                           (∃-cong λ _ →
                                                                            (∃-cong λ _ →
                                                                             ∃-comm F.∘
                                                                             (∃-cong λ _ → ∃-comm)) F.∘
                                                                            ∃-comm F.∘
                                                                            (∃-cong λ _ → inverse Σ-assoc)) F.∘
                                                                           inverse Σ-assoc) ⟩
         (x ∈FV e × ¬ x ∈ xs) ×
         (∃ λ c′ → ∃ λ xs′ → ∃ λ e′ → c′ ≡ c × xs′ ≡ xs × e′ ≡ e)      ↔⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-comm) F.∘
                                                                          (∃-cong λ _ → ∃-comm) F.∘
                                                                          ∃-comm ⟩
         (∃ λ c′ → ∃ λ xs′ → ∃ λ e′ →
            (x ∈FV e × ¬ x ∈ xs) × (c′ ≡ c × xs′ ≡ xs × e′ ≡ e))       ↔⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ →
                                                                           (∃-cong λ _ → ×-comm) F.∘
                                                                           inverse Σ-assoc) ⟩
         (∃ λ c′ → ∃ λ xs′ → ∃ λ e′ →
            x ∈FV e × (c′ ≡ c × xs′ ≡ xs × e′ ≡ e) × ¬ x ∈ xs)         ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ →
                                                                           ∃-cong λ (_ , xs′≡xs , _) → ≡⇒↝ _ $ cong (¬_ ∘ (_ ∈_)) $ sym
                                                                           xs′≡xs) ⟩
         (∃ λ c′ → ∃ λ xs′ → ∃ λ e′ →
            x ∈FV e × (c′ ≡ c × xs′ ≡ xs × e′ ≡ e) × ¬ x ∈ xs′)        ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ →
                                                                           ×-cong₁ λ ((_ , _ , e′≡e) , _) → ≡⇒↝ _ $ cong (_ ∈FV_) $ sym
                                                                           e′≡e) ⟩
         (∃ λ c′ → ∃ λ xs′ → ∃ λ e′ →
            x ∈FV e′ × (c′ ≡ c × xs′ ≡ xs × e′ ≡ e) × ¬ x ∈ xs′)       ↝⟨ (∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ → ∃-cong λ _ → ×-cong₁ λ _ →
                                                                           lemma) ⟩□
         (∃ λ c′ → ∃ λ xs′ → ∃ λ e′ →
            x ∈FV e′ × branch c′ xs′ e′ ≡ branch c xs e × ¬ x ∈ xs′)   □)
      (free e)
    where
    lemma :
      c′ ≡ c × xs′ ≡ xs × e′ ≡ e ⇔ branch c′ xs′ e′ ≡ branch c xs e
    lemma ._⇔_.to (c′≡c , xs′≡xs , e′≡e) =
      cong₂ (uncurry branch) (cong₂ _,_ c′≡c xs′≡xs) e′≡e
    lemma ._⇔_.from eq =
        cong (λ { (branch c _ _)  → c  }) eq
      , cong (λ { (branch _ xs _) → xs }) eq
      , cong (λ { (branch _ _ e)  → e  }) eq

  free-B⋆ :
    (bs : List Br) →
    ∃ λ (fs : Finite-subset-of Var) →
      ∀ x →
      (x SM.∈ fs) ⇔
      (∃ λ c → ∃ λ xs → ∃ λ e →
         x ∈FV e × branch c xs e ∈ bs × ¬ x ∈ xs)
  free-B⋆ [] =
      S.[]
    , λ x →
        x SM.∈ S.[]                                        ↔⟨ SM.∈[]≃ ⟩

        ⊥                                                  ↔⟨ (inverse $
                                                               ×-right-zero {ℓ₁ = lzero} F.∘
                                                               ∃-cong λ _ →
                                                               ×-right-zero {ℓ₁ = lzero} F.∘
                                                               ∃-cong λ _ →
                                                               ×-right-zero {ℓ₁ = lzero} F.∘
                                                               ∃-cong λ _ →
                                                               ×-right-zero {ℓ₁ = lzero} F.∘
                                                               ∃-cong λ _ →
                                                               ×-left-zero) ⟩
        Const × (∃ λ xs → ∃ λ e → x ∈FV e × ⊥ × ¬ x ∈ xs)  ↔⟨⟩

        (∃ λ c → ∃ λ xs → ∃ λ e →
           x ∈FV e × branch c xs e ∈ [] × ¬ x ∈ xs)        □
  free-B⋆ (b ∷ bs) =
    Σ-zip S._∪_
      (λ {fs₁ fs₂} hyp₁ hyp₂ x →
         x SM.∈ fs₁ S.∪ fs₂                               ↔⟨ _≃_.to SM.∈≃≃∈≃Erased E.[ SM.∈∪≃ ] ⟩

         Erased (x SM.∈ fs₁ T.∥⊎∥ x SM.∈ fs₂)             ↝⟨ T.Dec→Erased-∥∥⇔ $
                                                             Dec-⊎ (SM.member? _≟V_ _ _)
                                                                   (SM.member? _≟V_ _ _) ⟩

         x SM.∈ fs₁ ⊎ x SM.∈ fs₂                          ↝⟨ hyp₁ x ⊎-cong hyp₂ x ⟩

         (∃ λ c → ∃ λ xs → ∃ λ e →
            x ∈FV e × branch c xs e ≡ b × ¬ x ∈ xs) ⊎
         (∃ λ c → ∃ λ xs → ∃ λ e →
            x ∈FV e × branch c xs e ∈ bs × ¬ x ∈ xs)      ↔⟨ (inverse $
                                                              ∃-⊎-distrib-left F.∘
                                                              ∃-cong λ _ →
                                                              ∃-⊎-distrib-left F.∘
                                                              ∃-cong λ _ →
                                                              ∃-⊎-distrib-left F.∘
                                                              ∃-cong λ _ →
                                                              ∃-⊎-distrib-left F.∘
                                                              ∃-cong λ _ →
                                                              ∃-⊎-distrib-right) ⟩
         (∃ λ c → ∃ λ xs → ∃ λ e →
            x ∈FV e ×
            (branch c xs e ≡ b ⊎ branch c xs e ∈ bs) ×
            ¬ x ∈ xs)                                     ↔⟨⟩

         (∃ λ c → ∃ λ xs → ∃ λ e →
            x ∈FV e × branch c xs e ∈ b ∷ bs × ¬ x ∈ xs)  □)
      (free-B b) (free-B⋆ bs)

-- It is possible to find a variable that is neither free in a given
-- expression, nor a member of a given finite set.

fresh′ :
  (xs : Finite-subset-of Var) (e : Exp) →
  ∃ λ (x : Var) → ¬ x ∈FV e × x SM.∉ xs
fresh′ xs e =
  Σ-map id
    (λ {x} →
       x SM.∉ proj₁ (free e) S.∪ xs               ↔⟨ ¬-cong ext SM.∈∪≃ ⟩
       ¬ (x SM.∈ proj₁ (free e) T.∥⊎∥ x SM.∈ xs)  ↔⟨ T.¬∥∥↔¬ ⟩
       ¬ (x SM.∈ proj₁ (free e) ⊎ x SM.∈ xs)      ↝⟨ ¬⊎↔¬×¬ _ ⟩
       x SM.∉ proj₁ (free e) × x SM.∉ xs          ↔⟨ ¬-cong-⇔ ext (proj₂ (free e) x) ×-cong F.id ⟩□
       ¬ x ∈FV e × x SM.∉ xs                      □)
    (V.fresh (proj₁ (free e) S.∪ xs))

-- It is possible to find a variable that is not free in a given
-- expression.

fresh : (e : Exp) → ∃ λ (x : Var) → ¬ x ∈FV e
fresh e = Σ-map id proj₁ (fresh′ S.[] e)

-- If two expressions have the same free variables (ignoring any
-- variables in xs), then fresh′ xs returns the same fresh variable
-- for both expressions.

fresh′-unique :
  (∀ x → x SM.∉ xs → x ∈FV e₁ ⇔ x ∈FV e₂) →
  proj₁ (fresh′ xs e₁) ≡ proj₁ (fresh′ xs e₂)
fresh′-unique {xs = xs} {e₁ = e₁} {e₂ = e₂} same =
  E.Very-stable→Stable₀
    (E.Decidable-equality→Very-stable-≡ V._≟_ _ _)
    E.[ proj₁ (V.fresh (proj₁ (free e₁) S.∪ xs))  ≡⟨ (cong (proj₁ ∘ V.fresh) $
                                                      _≃_.from SM.extensionality λ x →
            x SM.∈ proj₁ (free e₁) S.∪ xs               ↝⟨ lemma x e₁ ⟩
            x SM.∉ xs × x ∈FV e₁ T.∥⊎∥ x SM.∈ xs        ↝⟨ ∃-cong (same x) T.∥⊎∥-cong F.id ⟩
            x SM.∉ xs × x ∈FV e₂ T.∥⊎∥ x SM.∈ xs        ↝⟨ inverse $ lemma x e₂ ⟩□
            x SM.∈ proj₁ (free e₂) S.∪ xs               □) ⟩∎

        proj₁ (V.fresh (proj₁ (free e₂) S.∪ xs))  ∎
      ]
  where
  @0 lemma : ∀ _ _ → _ ⇔ _
  lemma x e =
    x SM.∈ proj₁ (free e) S.∪ xs           ↔⟨ SM.∈∪≃ ⟩
    x SM.∈ proj₁ (free e) T.∥⊎∥ x SM.∈ xs  ↝⟨ proj₂ (free e) x T.∥⊎∥-cong F.id ⟩
    x ∈FV e T.∥⊎∥ x SM.∈ xs                ↔⟨ T.∥⊎∥≃¬×∥⊎∥ $ T.Dec→Dec-∥∥ $ SM.member? _≟V_ x xs ⟩□
    x SM.∉ xs × x ∈FV e T.∥⊎∥ x SM.∈ xs    □

-- If two expressions have the same free variables, then fresh returns
-- the same fresh variable for both expressions.

fresh-unique :
  (∀ x → x ∈FV e₁ ⇔ x ∈FV e₂) →
  proj₁ (fresh e₁) ≡ proj₁ (fresh e₂)
fresh-unique same = fresh′-unique (λ x _ → same x)

------------------------------------------------------------------------
-- Decision procedures

-- These decision procedures could presumably be implemented using
-- free.

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
          (_∘ proj₂ ∘ _≃_.to Closed′-case≃)
          (closed′?-B⋆ bs xs)

  closed′?-⋆ : ∀ es xs → Dec (All (Closed′ xs) es)
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

  closed′?-B : ∀ b xs → Dec (Closed′-Br xs b)
  closed′?-B (branch c ys e) xs = closed′? e (ys ++ xs)

  closed′?-B⋆ : ∀ bs xs → Dec (All (Closed′-Br xs) bs)
  closed′?-B⋆ []       xs = yes (λ _ ())

  closed′?-B⋆ (b ∷ bs) xs with closed′?-B⋆ bs xs
  closed′?-B⋆ (b ∷ bs) xs | no ¬cl-bs =
    no (λ cl → ¬cl-bs λ _ → cl _ ∘ inj₂)

  closed′?-B⋆ (b ∷ bs) xs | yes cl-bs =
    ⊎-map (λ cl-b b′ →
             [ (λ b′≡b → subst (Closed′-Br _) (sym b′≡b) cl-b)
             , cl-bs _
             ])
          (_∘ λ cl-bs → cl-bs _ (inj₁ refl))
          (closed′?-B b xs)

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

  subst-∉-B :
    ¬ (x ∈FV e × ¬ x ∈ xs) →
    branch c xs e [ x ← e′ ]B ≡ branch c xs e
  subst-∉-B {x = x} {e = e} {xs = xs} {c = c} {e′ = e′} x∉
    with V.member x xs
  … | yes _ =
    branch c xs e  ∎
  … | no x∉xs =
    branch c xs (e [ x ← e′ ])  ≡⟨ cong (branch _ _) $ subst-∉ x e (→-cong-→ (_, x∉xs) id x∉) ⟩∎
    branch c xs e               ∎

  subst-∉-B⋆ :
    ∀ x bs e′ →
    ¬ (∃ λ c → ∃ λ xs → ∃ λ e →
         branch c xs e ∈ bs × x ∈FV e × ¬ x ∈ xs) →
    bs [ x ← e′ ]B⋆ ≡ bs
  subst-∉-B⋆ x []                  _ x∉ = refl
  subst-∉-B⋆ x (branch c xs e ∷ bs) _ x∉ = cong₂ _∷_
    (subst-∉-B (x∉ ∘ (c ,_) ∘ (xs ,_) ∘ (e ,_) ∘ (inj₁ refl ,_)))
    (subst-∉-B⋆ _ bs _
       (x∉ ∘ Σ-map id (Σ-map id (Σ-map id (Σ-map inj₂ id)))))

-- If it is not the case that x is both free in e and not a member of
-- xs, then ⟨ xs , e ⟩[ x ← e′ ] is equal to e.

⟨,⟩[←]-∉ :
  ∀ xs →
  ¬ (x ∈FV e × ¬ x ∈ xs) →
  ⟨ xs , e ⟩[ x ← e′ ] ≡ e
⟨,⟩[←]-∉ {x = x} {e = e} {e′ = e′} xs hyp =
  ⟨ xs , e ⟩[ x ← e′ ]                       ≡⟨ ⟨,⟩[←]≡ xs ⟩
  if V.member x xs then e else e [ x ← e′ ]  ≡⟨ lemma (V.member x xs) ⟩∎
  e                                          ∎
  where
  lemma :
    (b : Dec (x ∈ xs)) →
    if b then e else e [ x ← e′ ] ≡ e
  lemma (yes _)   = refl
  lemma (no x∉xs) =         $⟨ hyp ⟩
    ¬ (x ∈FV e × ¬ x ∈ xs)  →⟨ →-cong-→ (_, x∉xs) id ⟩
    ¬ x ∈FV e               →⟨ subst-∉ _ _ ⟩□
    e [ x ← e′ ] ≡ e        □

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
no-swapping hyp = distinct (hyp x′ y′ e₁′ e₂′ e₃′ x≢y cl₁ cl₂)
  where
  x′ = V.name 0
  y′ = V.name 1

  e₁′ : Exp
  e₁′ = lambda x′ (var y′)

  e₂′ : Exp
  e₂′ = const (C.name 0) []

  e₃′ : Exp
  e₃′ = var x′

  x≢y : x′ ≢ y′
  x≢y = V.distinct-codes→distinct-names (λ ())

  cl₁ : Closed e₂′
  cl₁ = from-⊎ (closed? e₂′)

  cl₂ : Closed (e₃′ [ x′ ← e₂′ ])
  cl₂ with x′ V.≟ x′
  ... | no  x≢x = ⊥-elim (x≢x refl)
  ... | yes _   = cl₁

  lhs : e₁′ [ x′ ← e₂′ ] [ y′ ← e₃′ [ x′ ← e₂′ ] ] ≡ lambda x′ e₂′
  lhs with x′ V.≟ x′
  ... | no  x≢x = ⊥-elim (x≢x refl)
  ... | yes _   with y′ V.≟ x′
  ...   | yes y≡x = ⊥-elim (x≢y (sym y≡x))
  ...   | no  _   with y′ V.≟ y′
  ...     | no  y≢y = ⊥-elim (y≢y refl)
  ...     | yes _   = refl

  rhs : e₁′ [ y′ ← e₃′ ] [ x′ ← e₂′ ] ≡ lambda x′ (var x′)
  rhs with y′ V.≟ x′
  ... | yes y≡x = ⊥-elim (x≢y (sym y≡x))
  ... | no  _   with y′ V.≟ y′
  ...   | no  y≢y = ⊥-elim (y≢y refl)
  ...   | yes _   with x′ V.≟ x′
  ...     | no  x≢x = ⊥-elim (x≢x refl)
  ...     | yes _   = refl

  distinct : e₁′ [ x′ ← e₂′ ] [ y′ ← e₃′ [ x′ ← e₂′ ] ] ≢
             e₁′ [ y′ ← e₃′ ] [ x′ ← e₂′ ]
  distinct rewrite lhs | rhs = λ ()

-- Another swapping lemma does hold.

module _
  (x≢y  : x ≢ y)
  (x∉e″ : ¬ x ∈FV e″)
  (y∉e′ : ¬ y ∈FV e′)
  where

  mutual

    swap : ∀ e → e [ x ← e′ ] [ y ← e″ ] ≡ e [ y ← e″ ] [ x ← e′ ]
    swap (apply e₁ e₂) = cong₂ apply (swap e₁) (swap e₂)

    swap (lambda z e) with x V.≟ z | y V.≟ z
    … | yes _ | yes _ = refl
    … | yes _ | no  _ = refl
    … | no  _ | yes _ = refl
    … | no  _ | no  _ = cong (lambda z) (swap e)

    swap (case e bs) = cong₂ case (swap e) (swap-B⋆ bs)

    swap (rec z e) with x V.≟ z | y V.≟ z
    … | yes _ | yes _ = refl
    … | yes _ | no  _ = refl
    … | no  _ | yes _ = refl
    … | no  _ | no  _ = cong (rec z) (swap e)

    swap (var z) with x V.≟ z | y V.≟ z
    … | yes x≡z | yes y≡z =
      ⊥-elim $ x≢y (trans x≡z (sym y≡z))

    … | yes x≡z | no _ =
      e′ [ y ← e″ ]     ≡⟨ subst-∉ _ _ y∉e′ ⟩
      e′                ≡⟨ sym $ var-step-≡ x≡z ⟩∎
      var z [ x ← e′ ]  ∎

    … | no _ | yes y≡z =
      var z [ y ← e″ ]  ≡⟨ var-step-≡ y≡z ⟩
      e″                ≡⟨ sym $ subst-∉ _ _ x∉e″ ⟩∎
      e″ [ x ← e′ ]     ∎

    … | no x≢z | no y≢z =
      var z [ y ← e″ ]  ≡⟨ var-step-≢ y≢z ⟩
      var z             ≡⟨ sym $ var-step-≢ x≢z ⟩∎
      var z [ x ← e′ ]  ∎

    swap (const c es) = cong (const c) (swap-⋆ es)

    swap-B :
      ∀ b → b [ x ← e′ ]B [ y ← e″ ]B ≡ b [ y ← e″ ]B [ x ← e′ ]B
    swap-B (branch c zs e) with V.member x zs | V.member y zs
    … | yes x∈zs | yes y∈zs =
      branch c zs e [ y ← e″ ]B  ≡⟨ branch-step-∈ y∈zs ⟩
      branch c zs e              ≡⟨ sym $ branch-step-∈ x∈zs ⟩∎
      branch c zs e [ x ← e′ ]B  ∎

    … | yes x∈zs | no y∉zs =
      branch c zs e [ y ← e″ ]B               ≡⟨ branch-step-∉ y∉zs ⟩
      branch c zs (e [ y ← e″ ])              ≡⟨ sym $ branch-step-∈ x∈zs ⟩∎
      branch c zs (e [ y ← e″ ]) [ x ← e′ ]B  ∎

    … | no x∉zs | yes y∈zs =
      branch c zs (e [ x ← e′ ]) [ y ← e″ ]B  ≡⟨ branch-step-∈ y∈zs ⟩
      branch c zs (e [ x ← e′ ])              ≡⟨ sym $ branch-step-∉ x∉zs ⟩∎
      branch c zs e [ x ← e′ ]B               ∎

    … | no x∉zs | no y∉zs =
      branch c zs (e [ x ← e′ ]) [ y ← e″ ]B  ≡⟨ branch-step-∉ y∉zs ⟩
      branch c zs (e [ x ← e′ ] [ y ← e″ ])   ≡⟨ cong (branch c zs) (swap e) ⟩
      branch c zs (e [ y ← e″ ] [ x ← e′ ])   ≡⟨ sym $ branch-step-∉ x∉zs ⟩∎
      branch c zs (e [ y ← e″ ]) [ x ← e′ ]B  ∎

    swap-⋆ :
      ∀ es → es [ x ← e′ ]⋆ [ y ← e″ ]⋆ ≡ es [ y ← e″ ]⋆ [ x ← e′ ]⋆
    swap-⋆ []       = refl
    swap-⋆ (e ∷ es) = cong₂ _∷_ (swap e) (swap-⋆ es)

    swap-B⋆ :
      ∀ bs → bs [ x ← e′ ]B⋆ [ y ← e″ ]B⋆ ≡ bs [ y ← e″ ]B⋆ [ x ← e′ ]B⋆
    swap-B⋆ []       = refl
    swap-B⋆ (b ∷ bs) = cong₂ _∷_ (swap-B b) (swap-B⋆ bs)
