------------------------------------------------------------------------
-- Partial functions, computability
------------------------------------------------------------------------

open import Atom

module Computability (atoms : χ-atoms) where

open import Equality.Propositional.Cubical
open import Logical-equivalence using (_⇔_)
open import Prelude as P hiding (_∘_; Decidable)
open import Tactic.By.Propositional

open import Bool equality-with-J
open import Bijection equality-with-J using (_↔_)
open import Double-negation equality-with-J
open import Equality.Decision-procedures equality-with-J
open import Equivalence equality-with-J as Eq using (_≃_)
open import Excluded-middle equality-with-J
open import Function-universe equality-with-J hiding (id; _∘_)
open import H-level equality-with-J as H-level
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional equality-with-paths
  as Trunc
open import Monad equality-with-J

open import Chi            atoms
open import Coding         atoms
import Coding.Instances    atoms as Dummy
open import Deterministic  atoms
open import Free-variables atoms
open import Propositional  atoms
open import Reasoning      atoms
open import Values         atoms

------------------------------------------------------------------------
-- Partial functions

-- Partial functions for which the relation defining the partial
-- function must be propositional.

record _⇀_ {a b} (A : Type a) (B : Type b) : Type (lsuc (a ⊔ b)) where
  infix 4 _[_]=_
  field
    -- The relation defining the partial function.
    _[_]=_ : A → B → Type (a ⊔ b)

    -- The relation must be deterministic and propositional.
    deterministic : ∀ {a b₁ b₂} → _[_]=_ a b₁ → _[_]=_ a b₂ → b₁ ≡ b₂
    propositional : ∀ {a b} → Is-proposition (_[_]=_ a b)

  -- The type ∃ (_[_]=_ a) is a proposition.

  ∃[]=-propositional :
    ∀ {a} →
    Is-proposition (∃ (_[_]=_ a))
  ∃[]=-propositional (b₁ , [a]=b₁) (b₂ , [a]=b₂) =
    Σ-≡,≡→≡ (deterministic [a]=b₁ [a]=b₂)
            (propositional _ _)

open _⇀_ public using (_[_]=_)

-- The semantics of χ as a partial function.

semantics : Closed-exp ⇀ Closed-exp
semantics = record
  { _[_]=_        = _⇓_ on proj₁
  ; deterministic = λ e⇓v₁ e⇓v₂ →
      closed-equal-if-expressions-equal (⇓-deterministic e⇓v₁ e⇓v₂)
  ; propositional = ⇓-propositional
  }

-- Composition of partial functions.

infixr 9 _∘_

_∘_ : ∀ {ℓ c} {A B : Type ℓ} {C : Type c} →
      B ⇀ C → A ⇀ B → A ⇀ C
f ∘ g = record
  { _[_]=_        = λ a c → ∃ λ b → g [ a ]= b × f [ b ]= c
  ; deterministic = λ where
      (b₁ , g[a]=b₁ , f[b₁]=c₁) (b₂ , g[a]=b₂ , f[b₂]=c₂) →
        _⇀_.deterministic f
          (subst (f [_]= _) (_⇀_.deterministic g g[a]=b₁ g[a]=b₂) f[b₁]=c₁)
          f[b₂]=c₂
  ; propositional = λ {a c} →                                           $⟨ Σ-closure 1 (_⇀_.∃[]=-propositional g) (λ _ → _⇀_.propositional f) ⟩
      Is-proposition (∃ λ (p : ∃ λ b → g [ a ]= b) → f [ proj₁ p ]= c)  ↝⟨ H-level.respects-surjection (_↔_.surjection $ inverse Σ-assoc) 1 ⟩□
      Is-proposition (∃ λ b → g [ a ]= b × f [ b ]= c)                  □
  }

-- If the codomain of a function is a set, then the function can be
-- turned into a partial function.

as-partial : ∀ {a b} {A : Type a} {B : Type b} →
             Is-set B → (A → B) → A ⇀ B
as-partial {ℓa} B-set f = record
  { _[_]=_        = λ a b → ↑ ℓa (f a ≡ b)
  ; deterministic = λ {a b₁ b₂} fa≡b₁ fa≡b₂ →
                      b₁   ≡⟨ sym (lower fa≡b₁) ⟩
                      f a  ≡⟨ lower fa≡b₂ ⟩∎
                      b₂   ∎
  ; propositional = ↑-closure 1 (+⇒≡ {n = 1} B-set)
  }

-- If f is a partial function, g a function whose domain is a set, and
-- f (g a) = c, then (f ∘ g) a = c.

pre-apply : ∀ {ℓ c} {A B : Type ℓ} {C : Type c}
            (f : B ⇀ C) {g : A → B} {a c}
            (B-set : Is-set B) →
            f [ g a ]= c → f ∘ as-partial B-set g [ a ]= c
pre-apply _ _ f[ga]=b = _ , lift refl , f[ga]=b

-- If f is a function whose domain is a set, g a partial function, and
-- g a = b, then (f ∘ g) a = f b.

post-apply : ∀ {ℓ c} {A B : Type ℓ} {C : Type c}
               {f : B → C} (g : A ⇀ B) {a b}
             (C-set : Is-set C) →
             g [ a ]= b → as-partial C-set f ∘ g [ a ]= f b
post-apply _ _ g[a]=b = _ , g[a]=b , lift refl

------------------------------------------------------------------------
-- Totality

-- Totality. The definition is parametrised by something which could
-- be a modality.

Total : ∀ {a b} {A : Type a} {B : Type b} →
        (Type (a ⊔ b) → Type (a ⊔ b)) →
        A ⇀ B → Type (a ⊔ b)
Total P f = ∀ a → P (∃ λ b → f [ a ]= b)

-- If P maps propositions to propositions then Total P f is a
-- proposition.

Total-propositional :
  ∀ {a b} {A : Type a} {B : Type b}
    ⦃ rA : Rep A Consts ⦄ ⦃ rB : Rep B Consts ⦄ →
    {P : Type (a ⊔ b) → Type (a ⊔ b)}
  (f : A ⇀ B) →
  (∀ {A} → Is-proposition A → Is-proposition (P A)) →
  Is-proposition (Total P f)
Total-propositional f pres =
  Π-closure ext 1 λ _ →
  pres $
  _⇀_.∃[]=-propositional f

-- Totality with ∥_∥ as the modality implies totality with the
-- identity function as the modality.

total-with-∥∥→total :
  ∀ {a b} {A : Type a} {B : Type b} (f : A ⇀ B) →
  Total ∥_∥ f →
  Total id f
total-with-∥∥→total f total a =
  Trunc.rec
    (_⇀_.∃[]=-propositional f)
    id
    (total a)

------------------------------------------------------------------------
-- Computability

-- Implements P p f means that p is an implementation of f. The
-- definition is parametrised by P, which could be a modality.

Implements :
  ∀ {a b} {A : Type a} {B : Type b}
    ⦃ rA : Rep A Consts ⦄ ⦃ rB : Rep B Consts ⦄ →
  (Type (a ⊔ b) → Type (a ⊔ b)) →
  Exp → A ⇀ B → Type (a ⊔ b)
Implements P p f =
  Closed p
    ×
  (∀ x y → f [ x ]= y → apply p ⌜ x ⌝ ⇓ ⌜ y ⌝)
    ×
  (∀ x y → apply p ⌜ x ⌝ ⇓ y →
     P (∃ λ y′ → f [ x ]= y′ × y ≡ ⌜ y′ ⌝))

-- If P maps propositions to propositions, then Implements P p f is a
-- proposition.

Implements-propositional :
  ∀ {a b} {A : Type a} {B : Type b}
    ⦃ rA : Rep A Consts ⦄ ⦃ rB : Rep B Consts ⦄ →
    {P : Type (a ⊔ b) → Type (a ⊔ b)} {p : Exp}
  (f : A ⇀ B) →
  (∀ {A} → Is-proposition A → Is-proposition (P A)) →
  Is-proposition (Implements P p f)
Implements-propositional f pres =
  ×-closure 1 Closed-propositional $
  ×-closure 1 (Π-closure ext 1 λ _ →
               Π-closure ext 1 λ _ →
               Π-closure ext 1 λ _ →
               ⇓-propositional)
              (Π-closure ext 1 λ x →
               Π-closure ext 1 λ y →
               Π-closure ext 1 λ _ →
               pres $
               H-level.respects-surjection
                 (_↔_.surjection $ inverse Σ-assoc) 1
                 (Σ-closure 1 (_⇀_.∃[]=-propositional f) λ _ →
                              Exp-set))

-- Computability. The definition is parametrised by something which
-- could be a modality.

Computable′ :
  ∀ {a b} {A : Type a} {B : Type b}
    ⦃ rA : Rep A Consts ⦄ ⦃ rB : Rep B Consts ⦄ →
  (Type (a ⊔ b) → Type (a ⊔ b)) →
  A ⇀ B → Type (a ⊔ b)
Computable′ P f = ∃ λ p → Implements P p f

-- Computability.

Computable :
  ∀ {a b} {A : Type a} {B : Type b}
    ⦃ rA : Rep A Consts ⦄ ⦃ rB : Rep B Consts ⦄ →
  A ⇀ B → Type (a ⊔ b)
Computable = Computable′ id

-- If the partial function is total, then one part of the proof of
-- computability can be omitted.

total→almost-computable→computable :
  ∀ {a b} {A : Type a} {B : Type b}
    ⦃ rA : Rep A Consts ⦄ ⦃ rB : Rep B Consts ⦄
  (P : Type (a ⊔ b) → Type (a ⊔ b)) →
  (∀ {X Y} → (X → Y) → P X → P Y) →
  (f : A ⇀ B) →
  Total P f →
  (∃ λ p →
     Closed p
       ×
     (∀ x y → f [ x ]= y → apply p ⌜ x ⌝ ⇓ ⌜ y ⌝)) →
  Computable′ P f
total→almost-computable→computable P map f total (p , cl-p , hyp) =
    p
  , cl-p
  , hyp
  , λ x y px⇓y →
      flip map (total x) λ where
        (y′ , f[x]=y′) →
          y′ , f[x]=y′ , ⇓-deterministic px⇓y (hyp x y′ f[x]=y′)

-- Another definition of computability.

Computable″ :
  ∀ {ℓ} {A B : Type ℓ}
    ⦃ rA : Rep A Consts ⦄ ⦃ rB : Rep B Consts ⦄ →
  A ⇀ B → Type ℓ
Computable″ f =
  ∃ λ (p : Closed-exp) → ∀ a →
    ∀ q → semantics [ apply-cl p ⌜ a ⌝ ]= q
            ⇔
          as-partial Closed-exp-set ⌜_⌝ ∘ f [ a ]= q

-- The two definitions of computability are logically equivalent.

Computable⇔Computable″ :
  ∀ {ℓ} {A B : Type ℓ} ⦃ rA : Rep A Consts ⦄ ⦃ rB : Rep B Consts ⦄ →
  (f : A ⇀ B) →
  Computable f ⇔ Computable″ f
Computable⇔Computable″ f = record { to = to; from = from }
  where
  to : Computable f → Computable″ f
  to (p , cl , hyp₁ , hyp₂) =
    (p , cl) , λ { a (q , cl-q) → record
      { to   = Σ-map id (Σ-map id (lift P.∘
                                   closed-equal-if-expressions-equal P.∘
                                   sym))
                 P.∘
               hyp₂ a q
      ; from = λ { (b , f[a]=b , ⌜b⌝≡q) →
                   apply p ⌜ a ⌝  ⇓⟨ hyp₁ a b f[a]=b ⟩
                   ⌜ b ⌝          ≡⟨ cong proj₁ (lower ⌜b⌝≡q) ⟩⟶
                   q              ■⟨ subst Value (cong proj₁ (lower ⌜b⌝≡q)) (rep-value b) ⟩ }
      } }

  from : Computable″ f → Computable f
  from ((p , cl) , hyp) =
    p , cl ,
    (λ a b f[a]=b →
       apply p ⌜ a ⌝  ⇓⟨ _⇔_.from (hyp a ⌜ b ⌝) (post-apply f Closed-exp-set f[a]=b) ⟩■
       ⌜ b ⌝) ,
    λ a q p⌜a⌝⇓q →
      let cl-q : Closed q
          cl-q = closed⇓closed p⌜a⌝⇓q
                   (Closed′-closed-under-apply
                      (Closed→Closed′ cl)
                      (Closed→Closed′ (rep-closed a)))
      in
      Σ-map id (Σ-map id (cong proj₁ P.∘ sym P.∘ lower))
        (_⇔_.to (hyp a (q , cl-q)) p⌜a⌝⇓q)

-- Yet another definition of computability.

Computable‴ :
  ∀ {a b} {A : Type a} {B : Type b}
    ⦃ rA : Rep A Consts ⦄ ⦃ rB : Rep B Consts ⦄ →
  A ⇀ B → Type (a ⊔ b)
Computable‴ f =
  ∃ λ (p : Closed-exp) →
    ∀ a →
      ∃ λ b →
        apply (proj₁ p) ⌜ a ⌝ ⇓ ⌜ b ⌝
          ×
        f [ a ]= b

-- If a partial function is computable by the last definition of
-- computability above, then it is also computable by the first one.

Computable‴→Computable :
  ∀ {a b} {A : Type a} {B : Type b}
    ⦃ rA : Rep A Consts ⦄ ⦃ rB : Rep B Consts ⦄ →
  (f : A ⇀ B) →
  Computable‴ f → Computable f
Computable‴→Computable f ((p , cl-p) , hyp) =
    p
  , cl-p
  , (λ a b f[a]=b → case hyp a of λ where
       (b′ , p⌜a⌝⇓⌜b′⌝ , f[a]=b′) →
         apply p ⌜ a ⌝  ⇓⟨ p⌜a⌝⇓⌜b′⌝ ⟩
         ⌜ b′ ⌝         ≡⟨ by (_⇀_.deterministic f f[a]=b f[a]=b′) ⟩⟶
         ⌜ b ⌝          ■⟨ rep-value b ⟩)
  , (λ a v p⌜a⌝⇓v → case hyp a of λ where
       (b , p⌜a⌝⇓⌜b⌝ , f[a]=b) →
           b
         , f[a]=b
         , ⇓-deterministic p⌜a⌝⇓v p⌜a⌝⇓⌜b⌝)

------------------------------------------------------------------------
-- Reductions

module _  {a b c d} {A : Type a} {B : Type b} {C : Type c} {D : Type d}
          ⦃ rA : Rep A Consts ⦄ ⦃ rB : Rep B Consts ⦄
          ⦃ rC : Rep C Consts ⦄ ⦃ rD : Rep D Consts ⦄ where

  -- Reductions.

  Reduction : A ⇀ B → C ⇀ D → Type (a ⊔ b ⊔ c ⊔ d)
  Reduction f g = Computable g → Computable f

  -- If f can be reduced to g, and f is not computable, then g is not
  -- computable.

  Reduction→¬Computable→¬Computable :
    (f : A ⇀ B) (g : C ⇀ D) →
    Reduction f g → ¬ Computable f → ¬ Computable g
  Reduction→¬Computable→¬Computable _ _ red ¬f g = ¬f (red g)

------------------------------------------------------------------------
-- Turning predicates into partial functions

-- One way to view a predicate as a partial function to the booleans.

as-partial-function-to-Bool₁ :
  ∀ {a} {A : Type a} → (A → Type a) → A ⇀ Bool
as-partial-function-to-Bool₁ P = record
  { _[_]=_        = λ a b →
                      (P a → b ≡ true)
                        ×
                      ¬ ¬ P a
  ; deterministic = λ where
      {b₁ = true}  {b₂ = true}  _ _ → refl
      {b₁ = false} {b₂ = false} _ _ → refl
      {b₁ = true}  {b₂ = false} _ f →
        ⊥-elim $ proj₂ f (Bool.true≢false P.∘ sym P.∘ proj₁ f)
      {b₁ = false} {b₂ = true}  f _ →
        ⊥-elim $ proj₂ f (Bool.true≢false P.∘ sym P.∘ proj₁ f)
  ; propositional = ×-closure 1
                      (Π-closure ext 1 λ _ →
                       Bool-set)
                      (¬-propositional ext)
  }

-- Another way to view a predicate as a partial function to the
-- booleans.
--
-- See also as-function-to-Bool₁ and as-function-to-Bool₂ below.

as-partial-function-to-Bool₂ :
  ∀ {a} {A : Type a} →
  (P : A → Type a) →
  (∀ {a} → Is-proposition (P a)) →
  A ⇀ Bool
as-partial-function-to-Bool₂ P P-prop = record
  { _[_]=_        = λ a b → P a × b ≡ true
  ; deterministic = λ { (_ , refl) (_ , refl) → refl }
  ; propositional = ×-closure 1 P-prop Bool-set
  }

------------------------------------------------------------------------
-- Total partial functions to the booleans

-- Total partial functions to the booleans. Note that totality is
-- defined using the double-negation modality.

_→Bool : ∀ {ℓ} → Type ℓ → Type (lsuc ℓ)
A →Bool = ∃ λ (f : A ⇀ Bool) → Total (λ A → ¬¬ A) f

-- One way to view a predicate as a total partial function to the
-- booleans.

as-function-to-Bool₁ : ∀ {a} {A : Type a} → (A → Type a) → A →Bool
as-function-to-Bool₁ P =
    (record
       { _[_]=_        = λ a b →
                           (P a → b ≡ true)
                             ×
                           (¬ P a → b ≡ false)
       ; deterministic = λ where
           {b₁ = true}  {b₂ = true}  _  _  → refl
           {b₁ = false} {b₂ = false} _  _  → refl
           {b₁ = true}  {b₂ = false} f₁ f₂ →
             proj₂ f₁ (Bool.true≢false P.∘ sym P.∘ proj₁ f₂)
           {b₁ = false} {b₂ = true}  f₁ f₂ →
             sym (proj₂ f₂ (Bool.true≢false P.∘ sym P.∘ proj₁ f₁))
       ; propositional = ×-closure 1
                           (Π-closure ext 1 λ _ →
                            Bool-set)
                           (Π-closure ext 1 λ _ →
                            Bool-set)
       })
  , λ a →
      [ (λ p  → true  , (λ _ → refl)  , ⊥-elim P.∘ (_$ p))
      , (λ ¬p → false , ⊥-elim P.∘ ¬p , (λ _ → refl))
      ] ⟨$⟩ excluded-middle

-- Another way to view a predicate as a total partial function to the
-- booleans.

as-function-to-Bool₂ :
  ∀ {a} {A : Type a} →
  (P : A → Type a) →
  (∀ {a} → Is-proposition (P a)) →
  A →Bool
as-function-to-Bool₂ P P-prop =
    (record
       { _[_]=_        = λ a b →
                           P a × b ≡ true
                             ⊎
                           ¬ P a × b ≡ false
       ; deterministic = λ where
           (inj₁ (_ , refl)) (inj₁ (_ , refl)) → refl
           (inj₁ (p , _))    (inj₂ (¬p , _))   → ⊥-elim (¬p p)
           (inj₂ (¬p , _))   (inj₁ (p , _))    → ⊥-elim (¬p p)
           (inj₂ (_ , refl)) (inj₂ (_ , refl)) → refl
       ; propositional = λ {_ b} →
           ⊎-closure-propositional
             (λ { (_ , b≡true) (_ , b≡false) →
                  Bool.true≢false (
                    true   ≡⟨ sym b≡true ⟩
                    b      ≡⟨ b≡false ⟩∎
                    false  ∎) })
             (×-closure 1 P-prop Bool-set)
             (×-closure 1 (¬-propositional ext) Bool-set)
       })
  , λ a →
      [ (λ p  → true  , inj₁ (p , refl))
      , (λ ¬p → false , inj₂ (¬p , refl))
      ] ⟨$⟩ excluded-middle

-- If a is mapped to b by as-function-to-Bool₂ P P-prop, then a is
-- also mapped to b by as-function-to-Bool₁ P.

to-Bool₂→to-Bool₁ :
  ∀ {a} {A : Type a} ⦃ rA : Rep A Consts ⦄
  (P : A → Type a) (P-prop : ∀ {a} → Is-proposition (P a)) {a b} →
  proj₁ (as-function-to-Bool₂ P P-prop) [ a ]= b →
  proj₁ (as-function-to-Bool₁ P) [ a ]= b
to-Bool₂→to-Bool₁ _ _ = λ where
  (inj₁ (Pa  , refl)) → (λ _ → refl) , ⊥-elim P.∘ (_$ Pa)
  (inj₂ (¬Pa , refl)) → ⊥-elim P.∘ ¬Pa , λ _ → refl

-- If a is mapped to b by as-function-to-Bool₁ P, then a is not not
-- mapped to b by as-function-to-Bool₂ P P-prop.

to-Bool₁→to-Bool₂ :
  ∀ {a} {A : Type a} ⦃ rA : Rep A Consts ⦄
  (P : A → Type a) (P-prop : ∀ {a} → Is-proposition (P a)) {a b} →
  proj₁ (as-function-to-Bool₁ P) [ a ]= b →
  ¬¬ proj₁ (as-function-to-Bool₂ P P-prop) [ a ]= b
to-Bool₁→to-Bool₂ _ _ (Pa→b≡true , ¬Pa→b≡false) =
  ⊎-map (λ Pa → Pa , Pa→b≡true Pa) (λ ¬Pa → ¬Pa , ¬Pa→b≡false ¬Pa) ⟨$⟩
    excluded-middle

-- If as-function-to-Bool₁ P is ¬¬-computable, then
-- as-function-to-Bool₂ P P-prop is also ¬¬-computable.

to-Bool₁-computable→to-Bool₂-computable :
  ∀ {a} {A : Type a} ⦃ rA : Rep A Consts ⦄
  (P : A → Type a) (P-prop : ∀ {a} → Is-proposition (P a)) →
  Computable′ (λ A → ¬¬ A) (proj₁ (as-function-to-Bool₁ P)) →
  Computable′ (λ A → ¬¬ A) (proj₁ (as-function-to-Bool₂ P P-prop))
to-Bool₁-computable→to-Bool₂-computable
  P P-prop (p , cl-p , hyp₁ , hyp₂) =
    p
  , cl-p
  , (λ a b →
       proj₁ (as-function-to-Bool₂ P P-prop) [ a ]= b  ↝⟨ to-Bool₂→to-Bool₁ P P-prop ⟩
       proj₁ (as-function-to-Bool₁ P)        [ a ]= b  ↝⟨ hyp₁ a b ⟩□
       apply p ⌜ a ⌝ ⇓ ⌜ b ⌝                           □)
  , λ a e →
      apply p ⌜ a ⌝ ⇓ e                                             ↝⟨ hyp₂ a e ⟩

      ¬¬ (∃ λ b → proj₁ (as-function-to-Bool₁ P) [ a ]= b ×
                  e ≡ ⌜ b ⌝)                                        ↝⟨ _>>= (λ { (b , =b , ≡⌜b⌝) →
                                                                                 to-Bool₁→to-Bool₂ P P-prop =b >>= λ =b →
                                                                                 return (b , =b , ≡⌜b⌝) }) ⟩□
      ¬¬ (∃ λ b → proj₁ (as-function-to-Bool₂ P P-prop) [ a ]= b ×
                  e ≡ ⌜ b ⌝)                                        □

-- If P is pointwise propositional then
-- P a × b ≡ true ⊎ ¬ P a × b ≡ false is a proposition.

×≡true⊎¬×≡false-propositional :
  ∀ {a} {A : Type a}
  (P : A → Type a) → (∀ {a} → Is-proposition (P a)) →
  ∀ {a b} → Is-proposition (P a × b ≡ true ⊎ ¬ P a × b ≡ false)
×≡true⊎¬×≡false-propositional P P-prop =
  ⊎-closure-propositional
    (λ (Pa , _) (¬Pa , _) → ¬Pa Pa)
    (×-closure 1 P-prop Bool-set)
    (×-closure 1 (¬-propositional ext) Bool-set)

-- The statement P a × b ≡ true ⊎ ¬ P a × b ≡ false is equivalent to
-- stating that P a holds exactly when T b holds (assuming that P is
-- pointwise propositional).

×≡true⊎¬×≡false≃⇔T :
  ∀ {a} {A : Type a} {P : A → Type a} →
  (∀ {a} → Is-proposition (P a)) →
  ∀ {a b} → (P a × b ≡ true ⊎ ¬ P a × b ≡ false) ≃ (P a ⇔ T b)
×≡true⊎¬×≡false≃⇔T {P = P} P-prop {a = a} {b = b} = Eq.⇔→≃
  (×≡true⊎¬×≡false-propositional P P-prop)
  (⇔-closure ext 1 P-prop (T-propositional b))
  (λ where
     (inj₁ (p  , refl)) → record { from = λ _ → p }
     (inj₂ (¬p , refl)) → record { to = ¬p; from = ⊥-elim })
  (helper b)
  where
  helper : ∀ b → P a ⇔ T b → P a × b ≡ true ⊎ ¬ P a × b ≡ false
  helper true  hyp = inj₁ (_⇔_.from hyp _ , refl)
  helper false hyp = inj₂ (_⇔_.to hyp , refl)

-- If as-function-to-Bool₂ P P-prop is computable, then
-- as-function-to-Bool₁ P is computable (assuming excluded middle).

to-Bool₂-computable→to-Bool₁-computable :
  ∀ {a} {A : Type a} ⦃ rA : Rep A Consts ⦄ →
  Excluded-middle a →
  (P : A → Type a) (P-prop : ∀ {a} → Is-proposition (P a)) →
  Computable (proj₁ (as-function-to-Bool₂ P P-prop)) →
  Computable (proj₁ (as-function-to-Bool₁ P))
to-Bool₂-computable→to-Bool₁-computable
  em P P-prop (p , cl-p , hyp₁ , hyp₂) =
    p
  , cl-p
  , (λ a b →
       proj₁ (as-function-to-Bool₁ P) [ a ]= b            →⟨ to-Bool₁→to-Bool₂ P P-prop ⟩
       ¬¬ proj₁ (as-function-to-Bool₂ P P-prop) [ a ]= b  →⟨ Excluded-middle→Double-negation-elimination em $
                                                             ×≡true⊎¬×≡false-propositional P P-prop ⟩
       proj₁ (as-function-to-Bool₂ P P-prop) [ a ]= b     →⟨ hyp₁ a b ⟩□
       apply p ⌜ a ⌝ ⇓ ⌜ b ⌝                              □)
  , (λ a b →
       apply p ⌜ a ⌝ ⇓ b                                       →⟨ hyp₂ a b ⟩

       (∃ λ b′ →
            proj₁ (as-function-to-Bool₂ P P-prop) [ a ]= b′ ×
            b ≡ ⌜ b′ ⌝)                                        →⟨ Σ-map id (Σ-map (to-Bool₂→to-Bool₁ P P-prop) id) ⟩□

       (∃ λ b′ →
            proj₁ (as-function-to-Bool₁ P) [ a ]= b′ ×
            b ≡ ⌜ b′ ⌝)                                        □)

------------------------------------------------------------------------
-- Decidability

-- One definition of what it means for a total partial function to the
-- booleans to be decidable.

Decidable :
  ∀ {a} {A : Type a} ⦃ rA : Rep A Consts ⦄ →
  A →Bool → Type a
Decidable = Computable P.∘ proj₁

-- Another definition of what it means for a total partial function to
-- the booleans to be decidable.

Decidable′ :
  ∀ {a} {A : Type a} ⦃ rA : Rep A Consts ⦄ →
  A →Bool → Type a
Decidable′ = Computable‴ P.∘ proj₁
