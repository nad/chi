------------------------------------------------------------------------
-- Partial functions, computability
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Atom

module Computability (atoms : χ-atoms) where

open import Equality.Propositional
open import H-level.Truncation.Propositional as Trunc
open import Interval using (ext; ⟨ext⟩)
open import Logical-equivalence using (_⇔_)
open import Prelude as P hiding (_∘_; Decidable)
open import Tactic.By

open import Bool equality-with-J
open import Bijection equality-with-J using (_↔_)
open import Double-negation equality-with-J
open import Equality.Decision-procedures equality-with-J
import Equivalence equality-with-J as Eq
open import Function-universe equality-with-J hiding (id; _∘_)
open import H-level equality-with-J as H-level
open import H-level.Closure equality-with-J
open import Injection equality-with-J using (Injective)
open import Monad equality-with-J

open import Chi            atoms
open import Coding         atoms
import Coding.Instances    atoms
open import Deterministic  atoms
open import Free-variables atoms
open import Propositional  atoms
open import Reasoning      atoms
open import Values         atoms

-- Partial functions for which the relation defining the partial
-- function must be propositional.

record _⇀_ {a b} (A : Set a) (B : Set b) : Set (lsuc (a ⊔ b)) where
  infix 4 _[_]=_
  field
    -- The relation defining the partial function.
    _[_]=_ : A → B → Set (a ⊔ b)

    -- The relation must be deterministic and propositional.
    deterministic : ∀ {a b₁ b₂} → _[_]=_ a b₁ → _[_]=_ a b₂ → b₁ ≡ b₂
    propositional : ∀ {a b} → Is-proposition (_[_]=_ a b)

  -- A simple lemma.

  ∃[]=-propositional :
    ∀ {a} →
    Is-proposition (∃ (_[_]=_ a))
  ∃[]=-propositional =
    _⇔_.from propositional⇔irrelevant λ where
      (b₁ , [a]=b₁) (b₂ , [a]=b₂) →
        Σ-≡,≡→≡ (deterministic [a]=b₁ [a]=b₂)
                (_⇔_.to propositional⇔irrelevant propositional _ _)

open _⇀_ public using (_[_]=_)

-- Totality. The definition is parametrised by something which could
-- be a modality.

Total : ∀ {a b} {A : Set a} {B : Set b} →
        (Set (a ⊔ b) → Set (a ⊔ b)) →
        A ⇀ B → Set (a ⊔ b)
Total P f = ∀ a → P (∃ λ b → f [ a ]= b)

-- Totality with ∥_∥ as the modality implies totality with the
-- identity function as the modality.

total-with-∥∥→total :
  ∀ {a b} {A : Set a} {B : Set b} (f : A ⇀ B) →
  Total ∥_∥ f →
  Total id f
total-with-∥∥→total f total a =
  Trunc.rec
    (_⇀_.∃[]=-propositional f)
    id
    (total a)

-- If the codomain of a function is a set, then the function can be
-- turned into a partial function.

as-partial : ∀ {a b} {A : Set a} {B : Set b} →
             Is-set B → (A → B) → A ⇀ B
as-partial {ℓa} B-set f = record
  { _[_]=_        = λ a b → ↑ ℓa (f a ≡ b)
  ; deterministic = λ {a b₁ b₂} fa≡b₁ fa≡b₂ →
                      b₁   ≡⟨ sym (lower fa≡b₁) ⟩
                      f a  ≡⟨ lower fa≡b₂ ⟩∎
                      b₂   ∎
  ; propositional = ↑-closure 1 (B-set _ _)
  }

-- Composition of partial functions.

infixr 9 _∘_

_∘_ : ∀ {ℓ c} {A B : Set ℓ} {C : Set c} →
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

-- If f is a partial function, g a function whose domain is a set, and
-- f (g a) = c, then (f ∘ g) a = c.

pre-apply : ∀ {ℓ c} {A B : Set ℓ} {C : Set c}
            (f : B ⇀ C) {g : A → B} {a c}
            (B-set : Is-set B) →
            f [ g a ]= c → f ∘ as-partial B-set g [ a ]= c
pre-apply _ _ f[ga]=b = _ , lift refl , f[ga]=b

-- If f is a function whose domain is a set, g a partial function, and
-- g a = b, then (f ∘ g) a = f b.

post-apply : ∀ {ℓ c} {A B : Set ℓ} {C : Set c}
               {f : B → C} (g : A ⇀ B) {a b}
             (C-set : Is-set C) →
             g [ a ]= b → as-partial C-set f ∘ g [ a ]= f b
post-apply _ _ g[a]=b = _ , g[a]=b , lift refl

-- Implements P p f means that p is an implementation of f. The
-- definition is parametrised by P, which could be a modality.

Implements :
  ∀ {a b} {A : Set a} {B : Set b}
    ⦃ rA : Rep A Consts ⦄ ⦃ rB : Rep B Consts ⦄ →
  (Set (a ⊔ b) → Set (a ⊔ b)) →
  Exp → A ⇀ B → Set (a ⊔ b)
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
  ∀ {a b} {A : Set a} {B : Set b}
    ⦃ rA : Rep A Consts ⦄ ⦃ rB : Rep B Consts ⦄ →
    {P : Set (a ⊔ b) → Set (a ⊔ b)} {p : Exp}
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
                              Exp-set _ _))

-- Computability. The definition is parametrised by something which
-- could be a modality.

Computable′ :
  ∀ {a b} {A : Set a} {B : Set b}
    ⦃ rA : Rep A Consts ⦄ ⦃ rB : Rep B Consts ⦄ →
  (Set (a ⊔ b) → Set (a ⊔ b)) →
  A ⇀ B → Set (a ⊔ b)
Computable′ P f = ∃ λ p → Implements P p f

-- Computability.

Computable :
  ∀ {a b} {A : Set a} {B : Set b}
    ⦃ rA : Rep A Consts ⦄ ⦃ rB : Rep B Consts ⦄ →
  A ⇀ B → Set (a ⊔ b)
Computable = Computable′ id

-- If the partial function is total, then one part of the proof of
-- computability can be omitted.

total→almost-computable→computable :
  ∀ {a b} {A : Set a} {B : Set b}
    ⦃ rA : Rep A Consts ⦄ ⦃ rB : Rep B Consts ⦄
  (P : Set (a ⊔ b) → Set (a ⊔ b)) →
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

-- The semantics of χ as a partial function.

semantics : Closed-exp ⇀ Closed-exp
semantics = record
  { _[_]=_        = _⇓_ on proj₁
  ; deterministic = λ e⇓v₁ e⇓v₂ →
      closed-equal-if-expressions-equal (⇓-deterministic e⇓v₁ e⇓v₂)
  ; propositional = ⇓-propositional
  }

-- Another definition of computability.

Computable″ :
  ∀ {ℓ} {A B : Set ℓ}
    ⦃ rA : Rep A Consts ⦄ ⦃ rB : Rep B Consts ⦄ →
  A ⇀ B → Set ℓ
Computable″ f =
  ∃ λ (p : Closed-exp) → ∀ a →
    ∀ q → semantics [ apply-cl p ⌜ a ⌝ ]= q
            ⇔
          as-partial Closed-exp-set ⌜_⌝ ∘ f [ a ]= q

-- The two definitions of computability are logically equivalent.

Computable⇔Computable″ :
  ∀ {ℓ} {A B : Set ℓ} ⦃ rA : Rep A Consts ⦄ ⦃ rB : Rep B Consts ⦄ →
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
  ∀ {a b} {A : Set a} {B : Set b}
    ⦃ rA : Rep A Consts ⦄ ⦃ rB : Rep B Consts ⦄ →
  A ⇀ B → Set (a ⊔ b)
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
  ∀ {a b} {A : Set a} {B : Set b}
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

module _  {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
          ⦃ rA : Rep A Consts ⦄ ⦃ rB : Rep B Consts ⦄
          ⦃ rC : Rep C Consts ⦄ ⦃ rD : Rep D Consts ⦄ where

  -- Reductions.

  Reduction : A ⇀ B → C ⇀ D → Set (a ⊔ b ⊔ c ⊔ d)
  Reduction f g = Computable g → Computable f

  -- If f can be reduced to g, and f is not computable, then g is not
  -- computable.

  Reduction→¬Computable→¬Computable :
    (f : A ⇀ B) (g : C ⇀ D) →
    Reduction f g → ¬ Computable f → ¬ Computable g
  Reduction→¬Computable→¬Computable _ _ red ¬f g = ¬f (red g)

-- Total partial functions to the booleans. Note that totality is
-- defined using the double-negation modality.

_→Bool : ∀ {ℓ} → Set ℓ → Set (lsuc ℓ)
A →Bool = ∃ λ (f : A ⇀ Bool) → Total ¬¬_ f

-- One way to view a predicate as a total partial function to the
-- booleans.

as-function-to-Bool₁ : ∀ {a} {A : Set a} → (A → Set a) → A →Bool
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
                            Bool-set _ _)
                           (Π-closure ext 1 λ _ →
                            Bool-set _ _)
       })
  , λ a →
      [ (λ p  → true  , (λ _ → refl)  , ⊥-elim P.∘ (_$ p))
      , (λ ¬p → false , ⊥-elim P.∘ ¬p , (λ _ → refl))
      ] ⟨$⟩ excluded-middle

-- Another way to view a predicate as a total partial function to the
-- booleans.

as-function-to-Bool₂ :
  ∀ {a} {A : Set a} →
  (P : A → Set a) →
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
             (×-closure 1 P-prop (Bool-set _ _))
             (×-closure 1 (¬-propositional ext) (Bool-set _ _))
       })
  , λ a →
      [ (λ p  → true  , inj₁ (p , refl))
      , (λ ¬p → false , inj₂ (¬p , refl))
      ] ⟨$⟩ excluded-middle

-- If a is mapped to b by as-function-to-Bool₂ P P-prop, then a is
-- also mapped to b by as-function-to-Bool₁ P.

to-Bool₂→to-Bool₁ :
  ∀ {a} {A : Set a} ⦃ rA : Rep A Consts ⦄
  (P : A → Set a) (P-prop : ∀ {a} → Is-proposition (P a)) {a b} →
  proj₁ (as-function-to-Bool₂ P P-prop) [ a ]= b →
  proj₁ (as-function-to-Bool₁ P) [ a ]= b
to-Bool₂→to-Bool₁ _ _ = λ where
  (inj₁ (Pa  , refl)) → (λ _ → refl) , ⊥-elim P.∘ (_$ Pa)
  (inj₂ (¬Pa , refl)) → ⊥-elim P.∘ ¬Pa , λ _ → refl

-- If a is mapped to b by as-function-to-Bool₁ P, then a is not not
-- mapped to b by as-function-to-Bool₂ P P-prop.

to-Bool₁→to-Bool₂ :
  ∀ {a} {A : Set a} ⦃ rA : Rep A Consts ⦄
  (P : A → Set a) (P-prop : ∀ {a} → Is-proposition (P a)) {a b} →
  proj₁ (as-function-to-Bool₁ P) [ a ]= b →
  ¬¬ proj₁ (as-function-to-Bool₂ P P-prop) [ a ]= b
to-Bool₁→to-Bool₂ _ _ (Pa→b≡true , ¬Pa→b≡false) =
  ⊎-map (λ Pa → Pa , Pa→b≡true Pa) (λ ¬Pa → ¬Pa , ¬Pa→b≡false ¬Pa) ⟨$⟩
    excluded-middle

-- If as-function-to-Bool₁ P is ¬¬-computable, then
-- as-function-to-Bool₂ P P-prop is also ¬¬-computable.

to-Bool₁-computable→to-Bool₂-computable :
  ∀ {a} {A : Set a} ⦃ rA : Rep A Consts ⦄
  (P : A → Set a) (P-prop : ∀ {a} → Is-proposition (P a)) →
  Computable′ ¬¬_ (proj₁ (as-function-to-Bool₁ P)) →
  Computable′ ¬¬_ (proj₁ (as-function-to-Bool₂ P P-prop))
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

-- A lemma related to as-function-to-Bool₂.

×≡true⊎¬×≡false⇔⇔T :
  ∀ {a} {A : Set a} (P : A → Set a) →
  ∀ {a b} → P a × b ≡ true ⊎ ¬ P a × b ≡ false ⇔ (P a ⇔ T b)
×≡true⊎¬×≡false⇔⇔T P {a} {b} = record
  { to = λ where
      (inj₁ (p  , refl)) → record { from = λ _ → p }
      (inj₂ (¬p , refl)) → record { to = ¬p; from = ⊥-elim }
  ; from = helper b
  }
  where
  helper : ∀ b → P a ⇔ T b → P a × b ≡ true ⊎ ¬ P a × b ≡ false
  helper true  hyp = inj₁ (_⇔_.from hyp _ , refl)
  helper false hyp = inj₂ (_⇔_.to hyp , refl)

-- One way to view a predicate as a partial function to the booleans.

as-partial-function-to-Bool₁ :
  ∀ {a} {A : Set a} → (A → Set a) → A ⇀ Bool
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
                       Bool-set _ _)
                      (¬-propositional ext)
  }

-- Another way to view a predicate as a partial function to the
-- booleans.

as-partial-function-to-Bool₂ :
  ∀ {a} {A : Set a} →
  (P : A → Set a) →
  (∀ {a} → Is-proposition (P a)) →
  A ⇀ Bool
as-partial-function-to-Bool₂ P P-prop = record
  { _[_]=_        = λ a b → P a × b ≡ true
  ; deterministic = λ { (_ , refl) (_ , refl) → refl }
  ; propositional = ×-closure 1 P-prop (Bool-set _ _)
  }

-- One definition of what it means for a total partial function to the
-- booleans to be decidable.

Decidable :
  ∀ {a} {A : Set a} ⦃ rA : Rep A Consts ⦄ →
  A →Bool → Set a
Decidable = Computable P.∘ proj₁

-- Another definition of what it means for a total partial function to
-- the booleans to be decidable.

Decidable′ :
  ∀ {a} {A : Set a} ⦃ rA : Rep A Consts ⦄ →
  A →Bool → Set a
Decidable′ = Computable‴ P.∘ proj₁

-- Computable functions from a type to a set.

record Computable-function
         {a b} (A : Set a) (B : Set b) (B-set : Is-set B)
         ⦃ rA : Rep A Consts ⦄ ⦃ rB : Rep B Consts ⦄ : Set (a ⊔ b) where
  field
    function   : A → B
    computable : Computable (as-partial B-set function)

open Computable-function

-- An unfolding lemma for Computable-function.

Computable-function↔ :
  ∀ {a b} {A : Set a} {B : Set b} {B-set : Is-set B}
    ⦃ rA : Rep A Consts ⦄ ⦃ rB : Rep B Consts ⦄ →
  Computable-function A B B-set ↔
  ∃ λ (f : A → B) → Computable (as-partial B-set f)
Computable-function↔ = record
  { surjection = record
    { logical-equivalence = record
      { to = λ f → function f , computable f
      }
    ; right-inverse-of = λ _ → refl
    }
  ; left-inverse-of = λ _ → refl
  }

-- If two computable functions have equal implementations, then they
-- are equal.

equal-implementations→equal :
  ∀ {a b} {A : Set a} {B : Set b} {B-set : Is-set B}
    ⦃ rA : Rep A Consts ⦄ ⦃ rB : Rep B Consts ⦄
  (f g : Computable-function A B B-set) →
  proj₁ (computable f) ≡ proj₁ (computable g) →
  function f ≡ function g
equal-implementations→equal f g hyp = ⟨ext⟩ λ x →          $⟨ proj₁ (proj₂ (proj₂ (computable f))) x (function f x) (lift refl)
                                                            , proj₁ (proj₂ (proj₂ (computable g))) x (function g x) (lift refl) ⟩
  apply (proj₁ (computable f)) ⌜ x ⌝ ⇓ ⌜ function f x ⌝ ×
  apply (proj₁ (computable g)) ⌜ x ⌝ ⇓ ⌜ function g x ⌝    ↝⟨ Σ-map id (subst (λ e → apply e _ ⇓ _) (sym hyp)) ⟩

  apply (proj₁ (computable f)) ⌜ x ⌝ ⇓ ⌜ function f x ⌝ ×
  apply (proj₁ (computable f)) ⌜ x ⌝ ⇓ ⌜ function g x ⌝    ↝⟨ uncurry ⇓-deterministic ⟩

  ⌜ function f x ⌝ ≡ ⌜ function g x ⌝                      ↝⟨ rep-injective ⟩□

  function f x ≡ function g x                              □

instance

  -- Representation functions for computable functions.

  rep-Computable-function :
    ∀ {a b} {A : Set a} {B : Set b} {B-set : Is-set B}
      ⦃ rA : Rep A Consts ⦄ ⦃ rB : Rep B Consts ⦄ →
    Rep (Computable-function A B B-set) Consts
  rep-Computable-function {B-set = B-set} = record
    { ⌜_⌝           = ⌜_⌝ P.∘ proj₁ P.∘ computable
    ; rep-injective = injective
    }
    where
    abstract
      injective : Injective (⌜_⌝ P.∘ proj₁ P.∘ computable)
      injective {f} {g} =
        ⌜ proj₁ (computable f) ⌝ ≡ ⌜ proj₁ (computable g) ⌝             ↝⟨ rep-injective ⟩

        proj₁ (computable f) ≡ proj₁ (computable g)                     ↝⟨ (λ hyp → cong₂ _,_ (equal-implementations→equal f g hyp) hyp) ⟩

        (function f , proj₁ (computable f)) ≡
        (function g , proj₁ (computable g))                             ↔⟨ ignore-propositional-component $
                                                                           Implements-propositional (as-partial B-set (function g)) id ⟩
        ((function f , proj₁ (computable f)) , proj₂ (computable f)) ≡
        ((function g , proj₁ (computable g)) , proj₂ (computable g))    ↔⟨ Eq.≃-≡ (Eq.↔⇒≃ Σ-assoc) ⟩

        (function f , computable f) ≡ (function g , computable g)       ↔⟨ Eq.≃-≡ (Eq.↔⇒≃ Computable-function↔) ⟩□

        f ≡ g                                                           □
