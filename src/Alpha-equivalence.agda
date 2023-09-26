------------------------------------------------------------------------
-- Alpha-equivalence
------------------------------------------------------------------------

open import Atom

module Alpha-equivalence (atoms : χ-atoms) where

open import Equality.Propositional.Cubical
open import Logical-equivalence using (_⇔_)
open import Prelude hiding (const; module List)

open import Bag-equivalence equality-with-J using (_∈_)
open import Equivalence equality-with-J as Eq using (_≃_)
open import Equivalence-relation equality-with-J
open import Equality.Path.Isomorphisms.Univalence equality-with-paths
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional equality-with-paths as T
  using (∥_∥)
open import List equality-with-J as List using (_++_)
open import List.All equality-with-J as All using (All)
import Nat equality-with-J as Nat
open import Quotient.Erased equality-with-paths as Q using (_/ᴱ_)
open import Sum equality-with-J
open import Univalence-axiom equality-with-J

open import Chi            atoms
open import Deterministic  atoms
open import Free-variables atoms hiding (swap)
open import Propositional  atoms
open import Substitution   atoms

open χ-atoms atoms

private
  variable
    A                                           : Type
    b b₁ b₂ b₃                                  : Br
    bs₁ bs₂ bs₃                                 : List Br
    c c₁ c₂                                     : Const
    e′ e₁ e₁′ e₂′ e₂ e₃ e₁₁ e₁₂ e₂₁ e₂₂ v₁      : Exp
    es₁ es₂ es₃ vs₁                             : List Exp
    R R₁ R₂ R₃                                  : A → A → Type
    e p q v x x₁ x₁′ x₂ x₂′ x₃ y y₁ y₂ y₃ z₁ z₂ : A
    xs xs₁ xs₂ xs₃ ys₁ ys₂                      : List A

------------------------------------------------------------------------
-- The definition of α-equivalence

-- R [ x ∼ y ] relates x to y, and for pairs of variables x′, y′ such
-- that x is distinct from x′ and y is distinct from y′ it behaves
-- like R.

infix 5 _[_∼_]

_[_∼_] : (Var → Var → Type) → Var → Var → (Var → Var → Type)
(R [ x ∼ y ]) x′ y′ =
  x ≡ x′ × y ≡ y′
    ⊎
  x ≢ x′ × y ≢ y′ × R x′ y′

-- Alpha R is α-equivalence up to R: free variables are related if
-- they are related by R.

mutual

  data Alpha (R : Var → Var → Type) : Exp → Exp → Type where
    apply :
      Alpha R e₁₁ e₁₂ → Alpha R e₂₁ e₂₂ →
      Alpha R (apply e₁₁ e₂₁) (apply e₁₂ e₂₂)

    lambda :
      Alpha-binders R (x₁ ∷ []) e₁ (x₂ ∷ []) e₂ →
      Alpha R (lambda x₁ e₁) (lambda x₂ e₂)

    case :
      Alpha R e₁ e₂ →
      Listᴾ (Alpha-Br R) bs₁ bs₂ →
      Alpha R (case e₁ bs₁) (case e₂ bs₂)

    rec :
      Alpha-binders R (x₁ ∷ []) e₁ (x₂ ∷ []) e₂ →
      Alpha R (rec x₁ e₁) (rec x₂ e₂)

    var : R x₁ x₂ → Alpha R (var x₁) (var x₂)

    const :
      c₁ ≡ c₂ →
      Listᴾ (Alpha R) es₁ es₂ →
      Alpha R (const c₁ es₁) (const c₂ es₂)

  data Alpha-Br (R : Var → Var → Type) : Br → Br → Type where
    branch :
      c₁ ≡ c₂ →
      Alpha-binders R xs₁ e₁ xs₂ e₂ →
      Alpha-Br R (branch c₁ xs₁ e₁) (branch c₂ xs₂ e₂)

  data Alpha-binders (R : Var → Var → Type) :
         List Var → Exp → List Var → Exp → Type where
    nil :
      Alpha R e₁ e₂ →
      Alpha-binders R [] e₁ [] e₂
    cons :
      Alpha-binders (R [ x₁ ∼ x₂ ]) xs₁ e₁ xs₂ e₂ →
      Alpha-binders R (x₁ ∷ xs₁) e₁ (x₂ ∷ xs₂) e₂

-- The α-equivalence relation.

infix 4 _≈α_

_≈α_ : Exp → Exp → Type
_≈α_ = Alpha _≡_

------------------------------------------------------------------------
-- The α-equivalence relation is propositional

-- If R is pointwise propositional, then R [ x₁ ∼ x₂ ] is pointwise
-- propositional.

[∼]-propositional :
  (∀ x₁ x₂ → Is-proposition (R x₁ x₂)) →
  Is-proposition ((R [ x₁ ∼ x₂ ]) y₁ y₂)
[∼]-propositional r (inj₁ _) (inj₁ _) =
  cong inj₁ $ ×-closure 1 V.Name-set V.Name-set _ _
[∼]-propositional r (inj₂ _) (inj₂ _) =
  cong inj₂ $
  ×-closure 1
    (¬-propositional ext)
    (×-closure 1 (¬-propositional ext) (r _ _))
    _ _
[∼]-propositional r (inj₁ (x₁≡y₁ , _)) (inj₂ (x₁≢y₁ , _)) =
  ⊥-elim $ x₁≢y₁ x₁≡y₁
[∼]-propositional r (inj₂ (x₁≢y₁ , _)) (inj₁ (x₁≡y₁ , _)) =
  ⊥-elim $ x₁≢y₁ x₁≡y₁

-- The α-equivalence relation is pointwise propositional.

mutual

  ≈α-propositional : Is-proposition (e₁ ≈α e₂)
  ≈α-propositional = Alpha-propositional (λ _ _ → V.Name-set)

  Alpha-propositional :
    (∀ x₁ x₂ → Is-proposition (R x₁ x₂)) →
    Is-proposition (Alpha R e₁ e₂)
  Alpha-propositional r (apply p₁ p₂) (apply q₁ q₂) =
    cong₂ apply
      (Alpha-propositional r p₁ q₁)
      (Alpha-propositional r p₂ q₂)
  Alpha-propositional r (lambda p) (lambda q) =
    cong lambda (Alpha-binders-propositional r p q)
  Alpha-propositional r (case p ps) (case q qs) =
    cong₂ case
      (Alpha-propositional r p q)
      (Listᴾ-Alpha-Br-propositional r ps qs)
  Alpha-propositional r (rec p) (rec q) =
    cong rec (Alpha-binders-propositional r p q)
  Alpha-propositional r (var p) (var q) =
    cong var (r _ _ p q)
  Alpha-propositional r (const p ps) (const q qs) =
    cong₂ const
      (C.Name-set p q)
      (Listᴾ-Alpha-propositional r ps qs)

  Alpha-Br-propositional :
    (∀ x₁ x₂ → Is-proposition (R x₁ x₂)) →
    Is-proposition (Alpha-Br R b₁ b₂)
  Alpha-Br-propositional r (branch p₁ p₂) (branch q₁ q₂) =
    cong₂ branch
      (C.Name-set p₁ q₁)
      (Alpha-binders-propositional r p₂ q₂)

  Alpha-binders-propositional :
    (∀ x₁ x₂ → Is-proposition (R x₁ x₂)) →
    Is-proposition (Alpha-binders R xs₁ e₁ xs₂ e₂)
  Alpha-binders-propositional r (nil p) (nil q) =
    cong nil (Alpha-propositional r p q)
  Alpha-binders-propositional r (cons p) (cons q) =
    cong cons $
    Alpha-binders-propositional
      (λ _ _ → [∼]-propositional r)
      p q

  Listᴾ-Alpha-propositional :
    (∀ x₁ x₂ → Is-proposition (R x₁ x₂)) →
    Is-proposition (Listᴾ (Alpha R) es₁ es₂)
  Listᴾ-Alpha-propositional {es₁ = []} {es₂ = []} _ _ _ =
    refl
  Listᴾ-Alpha-propositional
    {es₁ = _ ∷ _} {es₂ = _ ∷ _} r (p , ps) (q , qs) =
    cong₂ _,_
      (Alpha-propositional r p q)
      (Listᴾ-Alpha-propositional r ps qs)

  Listᴾ-Alpha-Br-propositional :
    (∀ x₁ x₂ → Is-proposition (R x₁ x₂)) →
    Is-proposition (Listᴾ (Alpha-Br R) bs₁ bs₂)
  Listᴾ-Alpha-Br-propositional {bs₁ = []} {bs₂ = []} _ _ _ =
    refl
  Listᴾ-Alpha-Br-propositional
    {bs₁ = _ ∷ _} {bs₂ = _ ∷ _} r (p , ps) (q , qs) =
    cong₂ _,_
      (Alpha-Br-propositional r p q)
      (Listᴾ-Alpha-Br-propositional r ps qs)

------------------------------------------------------------------------
-- The functions _[_]ˡ and _[_]ʳ

-- Two variants of _[_∼_] for lists.

infix 5 _[_]ˡ _[_]ʳ

_[_]ˡ : (Var → Var → Type) → List (Var × Var) → Var → Var → Type
R [ xs ]ˡ = List.foldl (λ R (x , y) → R [ x ∼ y ]) R xs

_[_]ʳ : (Var → Var → Type) → List (Var × Var) → Var → Var → Type
R [ xs ]ʳ = List.foldr (λ (x , y) R → R [ x ∼ y ]) R xs

_ : R [ (x₁ , y₁) ∷ (x₂ , y₂) ∷ [] ]ˡ ≡ R [ x₁ ∼ y₁ ] [ x₂ ∼ y₂ ]
_ = refl

_ : R [ (x₁ , y₁) ∷ (x₂ , y₂) ∷ [] ]ʳ ≡ R [ x₂ ∼ y₂ ] [ x₁ ∼ y₁ ]
_ = refl

-- An alternative characterisation (up to logical equivalence) of
-- Alpha-binders for lists of equal length.

Alpha-binders⇔ :
  ∀ xs →
  Alpha-binders R (List.map proj₁ xs) e₁ (List.map proj₂ xs) e₂ ⇔
  Alpha (R [ xs ]ˡ) e₁ e₂
Alpha-binders⇔ xs = record { to = to xs; from = from xs }
  where
  to :
    ∀ xs →
    Alpha-binders R (List.map proj₁ xs) e₁ (List.map proj₂ xs) e₂ →
    Alpha (R [ xs ]ˡ) e₁ e₂
  to []       (nil p)  = p
  to (_ ∷ xs) (cons p) = to xs p

  from :
    ∀ xs →
    Alpha (R [ xs ]ˡ) e₁ e₂ →
    Alpha-binders R (List.map proj₁ xs) e₁ (List.map proj₂ xs) e₂
  from []       p = nil p
  from (_ ∷ xs) p = cons (from xs p)

------------------------------------------------------------------------
-- Some properties related to reflexivity

-- If R y y holds assuming that y is distinct from x, then
-- (R [ x ∼ x ]) y y holds.

[≢→[∼]]→[∼] :
  ∀ R →
  (y ≢ x → R y y) →
  (R [ x ∼ x ]) y y
[≢→[∼]]→[∼] {y = y} {x = x} _ r = case x V.≟ y of λ where
  (yes x≡y) → inj₁ (x≡y , x≡y)
  (no  x≢y) → inj₂ ( x≢y , x≢y
                   , r (x≢y ∘ sym)
                   )

-- Alpha R is reflexive for expressions for which R x x holds for
-- every free variable x.

mutual

  refl-Alpha :
    ∀ e → (∀ x → x ∈FV e → R x x) → Alpha R e e

  refl-Alpha (apply e₁ e₂) r =
    apply (refl-Alpha e₁ λ x x∈e₁ → r x (apply-left  x∈e₁))
          (refl-Alpha e₂ λ x x∈e₂ → r x (apply-right x∈e₂))

  refl-Alpha (lambda x e) r =
    lambda (refl-Alpha-binders (x ∷ []) e
              (λ y y∉[x] y∈e → r y (lambda (y∉[x] ∘ inj₁) y∈e)))

  refl-Alpha (case e bs) r =
    case
      (refl-Alpha e λ x x∈e →
         r x (case-head x∈e))
      (refl-Alpha-Br-⋆ bs λ x ∈bs x∉xs x∈ →
         r x (case-body x∈ ∈bs x∉xs))

  refl-Alpha (rec x e) r =
    rec (refl-Alpha-binders (x ∷ []) e
           (λ y y∉[x] → r y ∘ rec (y∉[x] ∘ inj₁)))

  refl-Alpha (var x) r =
    var (r x (var refl))

  refl-Alpha (const c es) r =
    const
      refl
      (refl-Alpha-⋆ es λ x e e∈es x∈e →
         r x (const x∈e e∈es))

  refl-Alpha-Br :
    ∀ c xs e →
    (∀ x → ¬ x ∈ xs → x ∈FV e → R x x) →
    Alpha-Br R (branch c xs e) (branch c xs e)
  refl-Alpha-Br _ xs e r =
    branch refl (refl-Alpha-binders xs e r)

  refl-Alpha-binders :
    ∀ xs e →
    (∀ x → ¬ x ∈ xs → x ∈FV e → R x x) →
    Alpha-binders R xs e xs e
  refl-Alpha-binders [] e r =
    nil (refl-Alpha e λ x x∈e →
           r x (λ ()) x∈e)
  refl-Alpha-binders {R = R} (x ∷ xs) e r =
    cons (refl-Alpha-binders xs e λ y y∉xs y∈e → [≢→[∼]]→[∼] R λ y≢x →
            r y [ y≢x , y∉xs ] y∈e)

  refl-Alpha-⋆ :
    ∀ es → (∀ x e → e ∈ es → x ∈FV e → R x x) →
    Listᴾ (Alpha R) es es
  refl-Alpha-⋆ []       _ = _
  refl-Alpha-⋆ (e ∷ es) r =
    refl-Alpha e (λ x x∈e → r x e (inj₁ refl) x∈e) ,
    refl-Alpha-⋆ es (λ x e e∈es x∈e → r x e (inj₂ e∈es) x∈e)

  refl-Alpha-Br-⋆ :
    ∀ bs →
    (∀ x {c xs e} → branch c xs e ∈ bs → ¬ x ∈ xs → x ∈FV e → R x x) →
    Listᴾ (Alpha-Br R) bs bs
  refl-Alpha-Br-⋆ []                   r = _
  refl-Alpha-Br-⋆ (branch c xs e ∷ bs) r =
    refl-Alpha-Br c xs e (λ x x∉xs x∈e → r x (inj₁ refl) x∉xs x∈e) ,
    refl-Alpha-Br-⋆ bs (λ x ∈bs x∉xs x∈ → r x (inj₂ ∈bs) x∉xs x∈)

-- The α-equivalence relation is reflexive.

refl-α : e ≈α e
refl-α = refl-Alpha _ (λ _ _ → refl)

-- The α-equivalence relation for branches is reflexive.

refl-α-Br : Alpha-Br _≡_ b b
refl-α-Br {b = branch _ _ _} =
  refl-Alpha-Br _ _ _ (λ _ _ _ → refl)

-- Equational reasoning combinators.

infix  -1 finally-α _∎α
infixr -2 step-≡-≈α step-≈α-≡ _≡⟨⟩α_

_∎α : ∀ e → e ≈α e
_ ∎α = refl-α

step-≡-≈α : ∀ e₁ → e₂ ≈α e₃ → e₁ ≡ e₂ → e₁ ≈α e₃
step-≡-≈α _ e₂≈e₃ e₁≡e₂ = subst (_≈α _) (sym e₁≡e₂) e₂≈e₃

syntax step-≡-≈α e₁ e₂≈e₃ e₁≡e₂ = e₁ ≡⟨ e₁≡e₂ ⟩α e₂≈e₃

step-≈α-≡ : ∀ e₁ → e₂ ≡ e₃ → e₁ ≈α e₂ → e₁ ≈α e₃
step-≈α-≡ _ e₂≡e₃ e₁≈e₂ = subst (_ ≈α_) e₂≡e₃ e₁≈e₂

syntax step-≈α-≡ e₁ e₂≡e₃ e₁≈e₂ = e₁ ≈⟨ e₁≈e₂ ⟩α e₂≡e₃

_≡⟨⟩α_ : ∀ e₁ → e₁ ≈α e₂ → e₁ ≈α e₂
_ ≡⟨⟩α e₁≈e₂ = e₁≈e₂

finally-α : ∀ e₁ e₂ → e₁ ≈α e₂ → e₁ ≈α e₂
finally-α _ _ e₁≈e₂ = e₁≈e₂

syntax finally-α e₁ e₂ e₁≈e₂ = e₁ ≈⟨ e₁≈e₂ ⟩α∎ e₂ ∎

------------------------------------------------------------------------
-- A map function

-- A kind of map function for _[_∼_].

map-[∼] :
  ∀ R₁ → (∀ {x₁ x₂} → R₁ x₁ x₂ → R₂ x₁ x₂) →
  (R₁ [ x₁ ∼ x₂ ]) x₁′ x₂′ →
  (R₂ [ x₁ ∼ x₂ ]) x₁′ x₂′
map-[∼] _ r = ⊎-map id (Σ-map id (Σ-map id r))

-- A kind of map function for _[_]ˡ.

map-[]ˡ :
  ∀ xs → (∀ {x₁ x₂} → R₁ x₁ x₂ → R₂ x₁ x₂) →
  (R₁ [ xs ]ˡ) x₁ x₂ →
  (R₂ [ xs ]ˡ) x₁ x₂
map-[]ˡ []       r = r
map-[]ˡ {R₁ = R₁} {R₂ = R₂} {x₁ = x₁} {x₂ = x₂} ((y₁ , y₂) ∷ xs) r =
  (R₁ [ y₁ ∼ y₂ ] [ xs ]ˡ) x₁ x₂  →⟨ map-[]ˡ xs (map-[∼] _ (λ {x₁ = x₁} {x₂ = x₂} → r {x₁ = x₁} {x₂ = x₂})) ⟩□
  (R₂ [ y₁ ∼ y₂ ] [ xs ]ˡ) x₁ x₂  □

-- A kind of map function for _[_]ʳ.

map-[]ʳ :
  ∀ xs → (∀ {x₁ x₂} → R₁ x₁ x₂ → R₂ x₁ x₂) →
  (R₁ [ xs ]ʳ) x₁ x₂ →
  (R₂ [ xs ]ʳ) x₁ x₂
map-[]ʳ [] r =
  r
map-[]ʳ {R₁ = R₁} {R₂ = R₂} {x₁ = x₁} {x₂ = x₂} ((y₁ , y₂) ∷ xs) r =
  (R₁ [ xs ]ʳ [ y₁ ∼ y₂ ]) x₁ x₂  →⟨ map-[∼] _ (λ {x₁ = x₁} {x₂ = x₂} → map-[]ʳ {x₁ = x₁} {x₂ = x₂} xs r) ⟩□
  (R₂ [ xs ]ʳ [ y₁ ∼ y₂ ]) x₁ x₂  □

-- A kind of map function for Alpha.

mutual

  map-Alpha :
    (∀ {x₁ x₂} → R₁ x₁ x₂ → R₂ x₁ x₂) →
    Alpha R₁ e₁ e₂ → Alpha R₂ e₁ e₂

  map-Alpha r (var Rx₁x₂) = var (r Rx₁x₂)

  map-Alpha r (lambda e₁≈e₂) =
    lambda (map-Alpha-binders r e₁≈e₂)

  map-Alpha r (rec e₁≈e₂) =
    rec (map-Alpha-binders r e₁≈e₂)

  map-Alpha r (apply e₁₁≈e₁₂ e₂₁≈e₂₂) =
    apply (map-Alpha r e₁₁≈e₁₂) (map-Alpha r e₂₁≈e₂₂)

  map-Alpha r (const c₁≡c₂ es₁≈es₂) =
    const c₁≡c₂ (map-Alpha-⋆ r es₁≈es₂)

  map-Alpha r (case e₁≈e₂ bs₁≈bs₂) =
    case (map-Alpha r e₁≈e₂)
         (map-Alpha-Br-⋆ r bs₁≈bs₂)

  map-Alpha-Br :
    (∀ {x₁ x₂} → R₁ x₁ x₂ → R₂ x₁ x₂) →
    Alpha-Br R₁ b₁ b₂ → Alpha-Br R₂ b₁ b₂
  map-Alpha-Br r (branch c₁≡c₂ bs₁≈bs₂) =
    branch c₁≡c₂ (map-Alpha-binders r bs₁≈bs₂)

  map-Alpha-binders :
    (∀ {x₁ x₂} → R₁ x₁ x₂ → R₂ x₁ x₂) →
    Alpha-binders R₁ xs₁ e₁ xs₂ e₂ → Alpha-binders R₂ xs₁ e₁ xs₂ e₂
  map-Alpha-binders r (nil e₁≈e₂) =
    nil (map-Alpha r e₁≈e₂)
  map-Alpha-binders {R₁ = R₁} r (cons b₁≈b₂) =
    cons (map-Alpha-binders (map-[∼] R₁ r) b₁≈b₂)

  map-Alpha-⋆ :
    (∀ {x₁ x₂} → R₁ x₁ x₂ → R₂ x₁ x₂) →
    Listᴾ (Alpha R₁) es₁ es₂ → Listᴾ (Alpha R₂) es₁ es₂
  map-Alpha-⋆ {es₁ = []} {es₂ = []} _ _ =
    _
  map-Alpha-⋆ {es₁ = _ ∷ _} {es₂ = _ ∷ _} r (e₁≈e₂ , es₁≈es₂) =
    map-Alpha r e₁≈e₂ , map-Alpha-⋆ r es₁≈es₂

  map-Alpha-Br-⋆ :
    (∀ {x₁ x₂} → R₁ x₁ x₂ → R₂ x₁ x₂) →
    Listᴾ (Alpha-Br R₁) bs₁ bs₂ → Listᴾ (Alpha-Br R₂) bs₁ bs₂
  map-Alpha-Br-⋆ {bs₁ = []} {bs₂ = []} _ _ =
    _
  map-Alpha-Br-⋆ {bs₁ = _ ∷ _} {bs₂ = _ ∷ _} r (b₁≈b₂ , bs₁≈bs₂) =
    map-Alpha-Br r b₁≈b₂ , map-Alpha-Br-⋆ r bs₁≈bs₂

------------------------------------------------------------------------
-- Symmetry

-- A kind of symmetry holds for _[_∼_].

sym-[∼] :
  ∀ R →
  (R [ x₁ ∼ x₂ ]) x₁′ x₂′ →
  (flip R [ x₂ ∼ x₁ ]) x₂′ x₁′
sym-[∼] _ =
  ⊎-map swap
        (λ (x₁≢x₁′ , x₂≢x₂′ , R₁x₁′x₂′) →
           x₂≢x₂′ , x₁≢x₁′ , R₁x₁′x₂′)

-- A kind of symmetry holds for _[_]ˡ.

sym-[]ˡ :
  ∀ xs →
  (R [ xs ]ˡ) x₁ x₂ →
  (flip R [ List.map swap xs ]ˡ) x₂ x₁
sym-[]ˡ [] =
  id
sym-[]ˡ {R = R} {x₁ = x₁} {x₂ = x₂} ((y₁ , y₂) ∷ xs) =
  (R [ y₁ ∼ y₂ ] [ xs ]ˡ) x₁ x₂                       →⟨ sym-[]ˡ xs ⟩
  (flip (R [ y₁ ∼ y₂ ]) [ List.map swap xs ]ˡ) x₂ x₁  →⟨ map-[]ˡ (List.map swap xs) (sym-[∼] R) ⟩□
  (flip R [ y₂ ∼ y₁ ] [ List.map swap xs ]ˡ) x₂ x₁    □

-- A kind of symmetry holds for _[_]ʳ.

sym-[]ʳ :
  ∀ xs →
  (R [ xs ]ʳ) x₁ x₂ →
  (flip R [ List.map swap xs ]ʳ) x₂ x₁
sym-[]ʳ [] =
  id
sym-[]ʳ {R = R} {x₁ = x₁} {x₂ = x₂} ((y₁ , y₂) ∷ xs) =
  (R [ xs ]ʳ [ y₁ ∼ y₂ ]) x₁ x₂                     →⟨ sym-[∼] (R [ xs ]ʳ) ⟩
  (flip (R [ xs ]ʳ) [ y₂ ∼ y₁ ]) x₂ x₁              →⟨ map-[∼] (flip (R [ xs ]ʳ)) (sym-[]ʳ xs) ⟩□
  (flip R [ List.map swap xs ]ʳ [ y₂ ∼ y₁ ]) x₂ x₁  □

-- A kind of symmetry holds for Alpha.

mutual

  sym-Alpha : Alpha R e₁ e₂ → Alpha (flip R) e₂ e₁

  sym-Alpha (var Rx₁x₂) = var Rx₁x₂

  sym-Alpha (lambda e₁≈e₂) =
    lambda (sym-Alpha-binders e₁≈e₂)

  sym-Alpha (rec e₁≈e₂) =
    rec (sym-Alpha-binders e₁≈e₂)

  sym-Alpha (apply e₁₁≈e₁₂ e₂₁≈e₂₂) =
    apply (sym-Alpha e₁₁≈e₁₂) (sym-Alpha e₂₁≈e₂₂)

  sym-Alpha (const c₁≡c₂ es₁≈es₂) =
    const (sym c₁≡c₂) (sym-Alpha-⋆ es₁≈es₂)

  sym-Alpha (case e₁≈e₂ bs₁≈bs₂) =
    case (sym-Alpha e₁≈e₂)
         (sym-Alpha-Br-⋆ bs₁≈bs₂)

  sym-Alpha-Br :
    Alpha-Br R b₁ b₂ → Alpha-Br (flip R) b₂ b₁
  sym-Alpha-Br (branch c₁≡c₂ bs₁≈bs₂) =
    branch (sym c₁≡c₂) (sym-Alpha-binders bs₁≈bs₂)

  sym-Alpha-binders :
    Alpha-binders R xs₁ e₁ xs₂ e₂ → Alpha-binders (flip R) xs₂ e₂ xs₁ e₁
  sym-Alpha-binders (nil e₁≈e₂) =
    nil (sym-Alpha e₁≈e₂)
  sym-Alpha-binders {R = R} (cons b₁≈b₂) =
    cons (map-Alpha-binders (sym-[∼] R) (sym-Alpha-binders b₁≈b₂))

  sym-Alpha-⋆ :
    Listᴾ (Alpha R) es₁ es₂ → Listᴾ (Alpha (flip R)) es₂ es₁
  sym-Alpha-⋆ {es₁ = []} {es₂ = []} _ =
    _
  sym-Alpha-⋆ {es₁ = _ ∷ _} {es₂ = _ ∷ _} (e₁≈e₂ , es₁≈es₂) =
    sym-Alpha e₁≈e₂ , sym-Alpha-⋆ es₁≈es₂

  sym-Alpha-Br-⋆ :
    Listᴾ (Alpha-Br R) bs₁ bs₂ → Listᴾ (Alpha-Br (flip R)) bs₂ bs₁
  sym-Alpha-Br-⋆ {bs₁ = []} {bs₂ = []} _ =
    _
  sym-Alpha-Br-⋆ {bs₁ = _ ∷ _} {bs₂ = _ ∷ _} (b₁≈b₂ , bs₁≈bs₂) =
    sym-Alpha-Br b₁≈b₂ , sym-Alpha-Br-⋆ bs₁≈bs₂

-- The α-equivalence relation is symmetric.

sym-α : e₁ ≈α e₂ → e₂ ≈α e₁
sym-α = map-Alpha sym ∘ sym-Alpha

-- The α-equivalence relation for branches is symmetric.

sym-α-Br : Alpha-Br _≡_ b₁ b₂ → Alpha-Br _≡_ b₂ b₁
sym-α-Br = map-Alpha-Br sym ∘ sym-Alpha-Br

------------------------------------------------------------------------
-- Transitivity

-- A kind of transitivity holds for _[_∼_].

trans-[∼] :
  (∀ y₁ y₂ y₃ → R₁ y₁ y₂ → R₂ y₂ y₃ → R₃ y₁ y₃) →
  (R₁ [ x₁ ∼ x₂ ]) y₁ y₂ →
  (R₂ [ x₂ ∼ x₃ ]) y₂ y₃ →
  (R₃ [ x₁ ∼ x₃ ]) y₁ y₃
trans-[∼] _ (inj₁ (x₁≡y₁ , _)) (inj₁ (_ , x₃≡y₃)) =
  inj₁ (x₁≡y₁ , x₃≡y₃)
trans-[∼] r (inj₂ (x₁≢y₁ , _ , y₁R₁y₂)) (inj₂ (_ , x₃≢y₃ , y₂R₂y₃)) =
  inj₂ (x₁≢y₁ , x₃≢y₃ , r _ _ _ y₁R₁y₂ y₂R₂y₃)
trans-[∼] _ (inj₁ (_ , x₂≡y₂)) (inj₂ (x₂≢y₂ , _)) =
  ⊥-elim $ x₂≢y₂ x₂≡y₂
trans-[∼] _ (inj₂ (_ , x₂≢y₂ , _)) (inj₁ (x₂≡y₂ , _)) =
  ⊥-elim $ x₂≢y₂ x₂≡y₂

-- A kind of transitivity holds for _[_]ˡ.

trans-[]ˡ :
  (∀ y₁ y₂ y₃ → R₁ y₁ y₂ → R₂ y₂ y₃ → R₃ y₁ y₃) →
  (xs : List (Var × Var × Var)) →
  (R₁ [ List.map (λ (x₁ , x₂ , x₃) → x₁ , x₂) xs ]ˡ) y₁ y₂ →
  (R₂ [ List.map (λ (x₁ , x₂ , x₃) → x₂ , x₃) xs ]ˡ) y₂ y₃ →
  (R₃ [ List.map (λ (x₁ , x₂ , x₃) → x₁ , x₃) xs ]ˡ) y₁ y₃
trans-[]ˡ r [] =
  r _ _ _
trans-[]ˡ
  {R₁ = R₁} {R₂ = R₂} {R₃ = R₃} {y₁ = y₁} {y₂ = y₂} {y₃ = y₃}
  r ((x₁ , x₂ , x₃) ∷ xs) = curry
  ((R₁ [ x₁ ∼ x₂ ] [ List.map (λ (x₁ , x₂ , x₃) → x₁ , x₂) xs ]ˡ) y₁ y₂
     ×
   (R₂ [ x₂ ∼ x₃ ] [ List.map (λ (x₁ , x₂ , x₃) → x₂ , x₃) xs ]ˡ) y₂ y₃  →⟨ uncurry (trans-[]ˡ (λ _ _ _ → trans-[∼] r) xs) ⟩□

   (R₃ [ x₁ ∼ x₃ ] [ List.map (λ (x₁ , x₂ , x₃) → x₁ , x₃) xs ]ˡ) y₁ y₃  □)

-- A kind of transitivity holds for _[_]ʳ.

trans-[]ʳ :
  (∀ y₁ y₂ y₃ → R₁ y₁ y₂ → R₂ y₂ y₃ → R₃ y₁ y₃) →
  (xs : List (Var × Var × Var)) →
  (R₁ [ List.map (λ (x₁ , x₂ , x₃) → x₁ , x₂) xs ]ʳ) y₁ y₂ →
  (R₂ [ List.map (λ (x₁ , x₂ , x₃) → x₂ , x₃) xs ]ʳ) y₂ y₃ →
  (R₃ [ List.map (λ (x₁ , x₂ , x₃) → x₁ , x₃) xs ]ʳ) y₁ y₃
trans-[]ʳ r [] =
  r _ _ _
trans-[]ʳ
  {R₁ = R₁} {R₂ = R₂} {R₃ = R₃} {y₁ = y₁} {y₂ = y₂} {y₃ = y₃}
  r ((x₁ , x₂ , x₃) ∷ xs) = curry
  ((R₁ [ List.map (λ (x₁ , x₂ , x₃) → x₁ , x₂) xs ]ʳ [ x₁ ∼ x₂ ]) y₁ y₂
     ×
   (R₂ [ List.map (λ (x₁ , x₂ , x₃) → x₂ , x₃) xs ]ʳ [ x₂ ∼ x₃ ]) y₂ y₃  →⟨ (uncurry $ trans-[∼] λ y₁ y₂ y₃ →
                                                                             trans-[]ʳ {y₁ = y₁} {y₂ = y₂} {y₃ = y₃} r xs) ⟩□
   (R₃ [ List.map (λ (x₁ , x₂ , x₃) → x₁ , x₃) xs ]ʳ [ x₁ ∼ x₃ ]) y₁ y₃  □)

-- A kind of transitivity holds for Alpha.

mutual

  trans-Alpha :
    (∀ y₁ y₂ y₃ → R₁ y₁ y₂ → R₂ y₂ y₃ → R₃ y₁ y₃) →
    Alpha R₁ e₁ e₂ → Alpha R₂ e₂ e₃ → Alpha R₃ e₁ e₃

  trans-Alpha r (var p) (var q) = var (r _ _ _ p q)

  trans-Alpha r (lambda p) (lambda q) =
    lambda (trans-Alpha-binders r p q)

  trans-Alpha r (rec p) (rec q) =
    rec (trans-Alpha-binders r p q)

  trans-Alpha r (apply p₁ p₂) (apply q₁ q₂) =
    apply (trans-Alpha r p₁ q₁) (trans-Alpha r p₂ q₂)

  trans-Alpha r (const p ps) (const q qs) =
    const (trans p q) (trans-Alpha-⋆ r ps qs)

  trans-Alpha r (case p ps) (case q qs) =
    case (trans-Alpha r p q)
         (trans-Alpha-Br-⋆ r ps qs)

  trans-Alpha-Br :
    (∀ y₁ y₂ y₃ → R₁ y₁ y₂ → R₂ y₂ y₃ → R₃ y₁ y₃) →
    Alpha-Br R₁ b₁ b₂ → Alpha-Br R₂ b₂ b₃ → Alpha-Br R₃ b₁ b₃
  trans-Alpha-Br r (branch p₁ p₂) (branch q₁ q₂) =
    branch (trans p₁ q₁) (trans-Alpha-binders r p₂ q₂)

  trans-Alpha-binders :
    (∀ y₁ y₂ y₃ → R₁ y₁ y₂ → R₂ y₂ y₃ → R₃ y₁ y₃) →
    Alpha-binders R₁ xs₁ e₁ xs₂ e₂ →
    Alpha-binders R₂ xs₂ e₂ xs₃ e₃ →
    Alpha-binders R₃ xs₁ e₁ xs₃ e₃
  trans-Alpha-binders r (nil p) (nil q) =
    nil (trans-Alpha r p q)
  trans-Alpha-binders r (cons p) (cons q) =
    cons (trans-Alpha-binders (λ _ _ _ → trans-[∼] r) p q)

  trans-Alpha-⋆ :
    (∀ y₁ y₂ y₃ → R₁ y₁ y₂ → R₂ y₂ y₃ → R₃ y₁ y₃) →
    Listᴾ (Alpha R₁) es₁ es₂ →
    Listᴾ (Alpha R₂) es₂ es₃ →
    Listᴾ (Alpha R₃) es₁ es₃
  trans-Alpha-⋆ {es₁ = []} {es₂ = []} {es₃ = []} _ _ _ =
    _
  trans-Alpha-⋆
    {es₁ = _ ∷ _} {es₂ = _ ∷ _} {es₃ = _ ∷ _} r (p , ps) (q , qs) =
    trans-Alpha r p q , trans-Alpha-⋆ r ps qs

  trans-Alpha-Br-⋆ :
    (∀ y₁ y₂ y₃ → R₁ y₁ y₂ → R₂ y₂ y₃ → R₃ y₁ y₃) →
    Listᴾ (Alpha-Br R₁) bs₁ bs₂ →
    Listᴾ (Alpha-Br R₂) bs₂ bs₃ →
    Listᴾ (Alpha-Br R₃) bs₁ bs₃
  trans-Alpha-Br-⋆ {bs₁ = []} {bs₂ = []} {bs₃ = []} _ _ _ =
    _
  trans-Alpha-Br-⋆
    {bs₁ = _ ∷ _} {bs₂ = _ ∷ _} {bs₃ = _ ∷ _} r (p , ps) (q , qs) =
    trans-Alpha-Br r p q , trans-Alpha-Br-⋆ r ps qs

-- The α-equivalence relation is transitive.

trans-α : e₁ ≈α e₂ → e₂ ≈α e₃ → e₁ ≈α e₃
trans-α = trans-Alpha (λ _ _ _ → trans)

-- The α-equivalence relation for branches is transitive.

trans-α-Br :
  Alpha-Br _≡_ b₁ b₂ → Alpha-Br _≡_ b₂ b₃ → Alpha-Br _≡_ b₁ b₃
trans-α-Br = trans-Alpha-Br (λ _ _ _ → trans)

------------------------------------------------------------------------
-- Some lemmas related to _[_∼_]

-- If x₁ is not equal to y₁ and x₂ is equal to y₂, then
-- R [ x₁ ∼ x₂ ] [ y₁ ∼ y₂ ] does not hold for x₁ and any value.

≢≡→¬[∼][∼] :
  ∀ R → x₁ ≢ y₁ → x₂ ≡ y₂ →
  ¬ (R [ x₁ ∼ x₂ ] [ y₁ ∼ y₂ ]) x₁ z₂
≢≡→¬[∼][∼]
  {x₁ = x₁} {y₁ = y₁} {x₂ = x₂} {y₂ = y₂} {z₂ = z₂} R x₁≢y₁ x₂≡y₂ =

  (R [ x₁ ∼ x₂ ] [ y₁ ∼ y₂ ]) x₁ z₂  →⟨ [ ⊥-elim ∘ x₁≢y₁ ∘ sym ∘ proj₁
                                        , proj₂
                                        ] ⟩
  y₂ ≢ z₂ × (R [ x₁ ∼ x₂ ]) x₁ z₂    →⟨ (∃-cong λ _ →
                                         [ proj₂
                                         , ⊥-elim ∘ (_$ refl) ∘ proj₁
                                         ]) ⟩
  y₂ ≢ z₂ × x₂ ≡ z₂                  →⟨ proj₁ ∘ (×-cong₁ λ x₂≡z₂ → _∘ flip trans x₂≡z₂) ⟩
  y₂ ≢ x₂                            →⟨ _$ sym x₂≡y₂ ⟩□
  ⊥                                  □

-- If x₁ is equal to y₁ and x₂ is not equal to y₂, then
-- R [ x₁ ∼ x₂ ] [ y₁ ∼ y₂ ] does not hold for any value and x₂.

≡≢→¬[∼][∼] :
  ∀ R → x₁ ≡ y₁ → x₂ ≢ y₂ →
  ¬ (R [ x₁ ∼ x₂ ] [ y₁ ∼ y₂ ]) z₁ x₂
≡≢→¬[∼][∼]
  {x₁ = x₁} {y₁ = y₁} {x₂ = x₂} {y₂ = y₂} {z₁ = z₁} R x₁≡y₁ x₂≢y₂ =

  (R [ x₁ ∼ x₂ ] [ y₁ ∼ y₂ ]) z₁ x₂         →⟨ sym-[∼] (R [ x₁ ∼ x₂ ]) ⟩
  (flip (R [ x₁ ∼ x₂ ]) [ y₂ ∼ y₁ ]) x₂ z₁  →⟨ map-[∼] (flip (R [ x₁ ∼ x₂ ])) (sym-[∼] R) ⟩
  (flip R [ x₂ ∼ x₁ ] [ y₂ ∼ y₁ ]) x₂ z₁    →⟨ ≢≡→¬[∼][∼] (flip R) x₂≢y₂ x₁≡y₁ ⟩□
  ⊥                                         □

-- If x₁ is not equal to y₁ and x₂ is not equal to y₂, then
-- (R [ x₁ ∼ x₂ ] [ y₁ ∼ y₂ ]) z₁ z₂ implies
-- (R [ y₁ ∼ y₂ ] [ x₁ ∼ x₂ ]) z₁ z₂.

swap-[∼] :
  ∀ R → x₁ ≢ y₁ → x₂ ≢ y₂ →
  (R [ x₁ ∼ x₂ ] [ y₁ ∼ y₂ ]) z₁ z₂ →
  (R [ y₁ ∼ y₂ ] [ x₁ ∼ x₂ ]) z₁ z₂
swap-[∼]
  {x₁ = x₁} {y₁ = y₁} {x₂ = x₂} {y₂ = y₂} {z₁ = z₁} {z₂ = z₂}
  R x₁≢y₁ x₂≢y₂ =
  y₁ ≡ z₁ × y₂ ≡ z₂ ⊎
  y₁ ≢ z₁ × y₂ ≢ z₂ ×
  (x₁ ≡ z₁ × x₂ ≡ z₂ ⊎
   x₁ ≢ z₁ × x₂ ≢ z₂ × R z₁ z₂)  →⟨ [ (λ (y₁≡z₁ , y₂≡z₂) →
                                         inj₂ ( x₁≢y₁ ∘ flip trans (sym y₁≡z₁)
                                              , x₂≢y₂ ∘ flip trans (sym y₂≡z₂)
                                              , inj₁ (y₁≡z₁ , y₂≡z₂)
                                              ))
                                    , (uncurry λ y₁≢z₁ → uncurry λ y₂≢z₂ →
                                       ⊎-map id λ (x₁≢z₁ , x₂≢z₂ , z₁Rz₂) →
                                       x₁≢z₁ , x₂≢z₂ , inj₂ (y₁≢z₁ , y₂≢z₂ , z₁Rz₂))
                                    ] ⟩□
  x₁ ≡ z₁ × x₂ ≡ z₂ ⊎
  x₁ ≢ z₁ × x₂ ≢ z₂ ×
  (y₁ ≡ z₁ × y₂ ≡ z₂ ⊎
   y₁ ≢ z₁ × y₂ ≢ z₂ × R z₁ z₂)  □

-- If x₁ is equal to y₁ or x₂ is equal to y₂, then
-- (R [ x₁ ∼ x₂ ] [ y₁ ∼ y₂ ]) z₁ z₂ implies (R [ y₁ ∼ y₂ ]) z₁ z₂.

drop-[∼] :
  ∀ R → x₁ ≡ y₁ ⊎ x₂ ≡ y₂ →
  (R [ x₁ ∼ x₂ ] [ y₁ ∼ y₂ ]) z₁ z₂ →
  (R [ y₁ ∼ y₂ ]) z₁ z₂
drop-[∼]
  {x₁ = x₁} {y₁ = y₁} {x₂ = x₂} {y₂ = y₂} {z₁ = z₁} {z₂ = z₂}
  R x₁≡y₁⊎x₂≡y₂ =
  y₁ ≡ z₁ × y₂ ≡ z₂ ⊎
  y₁ ≢ z₁ × y₂ ≢ z₂ ×
  (x₁ ≡ z₁ × x₂ ≡ z₂ ⊎
   x₁ ≢ z₁ × x₂ ≢ z₂ × R z₁ z₂)  →⟨ (⊎-map id $ uncurry λ y₁≢z₁ → uncurry λ y₂≢z₂ →
                                     [ (λ (x₁≡z₁ , x₂≡z₂) → ⊥-elim $
                                          [ (λ x₁≡y₁ → y₁≢z₁ $ trans (sym x₁≡y₁) x₁≡z₁)
                                          , (λ x₂≡y₂ → y₂≢z₂ $ trans (sym x₂≡y₂) x₂≡z₂)
                                          ] x₁≡y₁⊎x₂≡y₂)
                                     , (λ (_ , _ , z₁Rz₂) →
                                          y₁≢z₁ , y₂≢z₂ , z₁Rz₂)
                                     ]) ⟩□
  y₁ ≡ z₁ × y₂ ≡ z₂ ⊎
  y₁ ≢ z₁ × y₂ ≢ z₂ × R z₁ z₂    □

------------------------------------------------------------------------
-- A kind of weakening property

-- If (_≡_ [ xs ]ʳ) x₁ x₂ holds, and it is "merely true" that x₁ is
-- equal to the first projection of an element in xs, then
-- (R [ xs ]ʳ) x₁ x₂ holds for any R.

≡-[]ʳ→[]ʳ :
  ∀ xs →
  ∥ x₁ ∈ List.map proj₁ xs ∥ →
  (_≡_ [ xs ]ʳ) x₁ x₂ →
  (R [ xs ]ʳ) x₁ x₂
≡-[]ʳ→[]ʳ {x₁ = x₁} {x₂ = x₂} {R = R} [] cl _ =
               $⟨ cl ⟩
  ∥ x₁ ∈ [] ∥  ↔⟨⟩
  ∥ ⊥ ∥        ↔⟨ T.∥∥↔ ⊥-propositional ⟩
  ⊥            →⟨ ⊥-elim ⟩□
  R x₁ x₂      □
≡-[]ʳ→[]ʳ {x₁ = x₁} {x₂ = x₂} {R = R} ((y₁ , y₂) ∷ xs) cl =
  (_≡_ [ xs ]ʳ [ y₁ ∼ y₂ ]) x₁ x₂                              ↔⟨⟩
  y₁ ≡ x₁ × y₂ ≡ x₂ ⊎ y₁ ≢ x₁ × y₂ ≢ x₂ × (_≡_ [ xs ]ʳ) x₁ x₂  →⟨ (⊎-map id $ ∃-cong λ y₁≢x₁ → ∃-cong λ _ →
                                                                   ≡-[]ʳ→[]ʳ xs (cl′ y₁≢x₁)) ⟩
  y₁ ≡ x₁ × y₂ ≡ x₂ ⊎ y₁ ≢ x₁ × y₂ ≢ x₂ × (R [ xs ]ʳ) x₁ x₂    ↔⟨⟩
  (R   [ xs ]ʳ [ y₁ ∼ y₂ ]) x₁ x₂                              □
  where
  cl′ : y₁ ≢ x₁ → ∥ x₁ ∈ List.map proj₁ xs ∥
  cl′ y₁≢x₁ =                             $⟨ cl ⟩
    ∥ x₁ ∈ y₁ ∷ List.map proj₁ xs ∥       ↔⟨⟩
    ∥ x₁ ≡ y₁ ⊎ x₁ ∈ List.map proj₁ xs ∥  →⟨ T.∥∥-map [ ⊥-elim ∘ y₁≢x₁ ∘ sym , id ] ⟩□
    ∥ x₁ ∈ List.map proj₁ xs ∥            □

-- The previous lemma was stated using ∥ x₁ ∈ List.map proj₁ xs ∥. As
-- the following lemma shows this choice was a bit arbitrary.

≡-[]ʳ→∈₁⇔∈₂ :
  ∀ xs →
  (_≡_ [ xs ]ʳ) x₁ x₂ →
  x₁ ∈ List.map proj₁ xs ⇔ x₂ ∈ List.map proj₂ xs
≡-[]ʳ→∈₁⇔∈₂ {x₁ = x₁} {x₂ = x₂} xs p =
  record { to = curry (to xs) p; from = from }
  where
  to :
    ∀ {x₁ x₂} xs →
    (_≡_ [ xs ]ʳ) x₁ x₂ × x₁ ∈ List.map proj₁ xs →
    x₂ ∈ List.map proj₂ xs
  to {x₁ = x₁} {x₂ = x₂} ((y₁ , y₂) ∷ xs) =
    (y₁ ≡ x₁ × y₂ ≡ x₂ ⊎ y₁ ≢ x₁ × y₂ ≢ x₂ × (_≡_ [ xs ]ʳ) x₁ x₂) ×
    (x₁ ≡ y₁ ⊎ x₁ ∈ List.map proj₁ xs)                                    ↔⟨ (F.id ⊎-cong ∃-⊎-distrib-left) F.∘
                                                                             ∃-⊎-distrib-right ⟩
    (y₁ ≡ x₁ × y₂ ≡ x₂) × (x₁ ≡ y₁ ⊎ x₁ ∈ List.map proj₁ xs) ⊎
    ((y₁ ≢ x₁ × y₂ ≢ x₂ × (_≡_ [ xs ]ʳ) x₁ x₂) × x₁ ≡ y₁ ⊎
     (y₁ ≢ x₁ × y₂ ≢ x₂ × (_≡_ [ xs ]ʳ) x₁ x₂) × x₁ ∈ List.map proj₁ xs)  →⟨ ⊎-map (sym ∘ proj₂ ∘ proj₁)
                                                                               [ (λ ((y₁≢x₁ , _) , x₁≡y₁) → ⊥-elim $ y₁≢x₁ (sym x₁≡y₁))
                                                                               , Σ-map (proj₂ ∘ proj₂) id
                                                                               ] ⟩

    x₂ ≡ y₂ ⊎ (_≡_ [ xs ]ʳ) x₁ x₂ × x₁ ∈ List.map proj₁ xs                →⟨ ⊎-map id (to xs) ⟩□

    x₂ ≡ y₂ ⊎ x₂ ∈ List.map proj₂ xs                                      □

  from :
    x₂ ∈ List.map proj₂ xs →
    x₁ ∈ List.map proj₁ xs
  from =
    x₂ ∈ List.map proj₂ xs                          →⟨ subst (_ ∈_) $ sym $ List.map∘map xs ⟩
    x₂ ∈ List.map proj₁ (List.map Prelude.swap xs)  →⟨ curry (to (List.map Prelude.swap xs)) lemma ⟩
    x₁ ∈ List.map proj₂ (List.map Prelude.swap xs)  →⟨ subst (_ ∈_) $ List.map∘map xs ⟩□
    x₁ ∈ List.map proj₁ xs                          □
    where
    lemma =                                   $⟨ p ⟩
      (_≡_ [ xs ]ʳ) x₁ x₂                     →⟨ sym-[]ʳ xs ⟩
      (flip _≡_ [ List.map swap xs ]ʳ) x₂ x₁  →⟨ map-[]ʳ (List.map swap xs) sym ⟩□
      (_≡_ [ List.map swap xs ]ʳ) x₂ x₁       □

mutual

  -- If e₁ and e₂ are α-equivalent and e₁ is closed, then
  -- Alpha R e₁ e₂ holds.

  ≈α→Alpha : Closed e₁ → e₁ ≈α e₂ → Alpha R e₁ e₂
  ≈α→Alpha cl p = Alpha-≡→Alpha [] cl p

  Alpha-≡→Alpha :
    ∀ xs →
    Closed′ (List.map proj₁ xs) e₁ →
    Alpha (_≡_ [ xs ]ʳ) e₁ e₂ →
    Alpha (R   [ xs ]ʳ) e₁ e₂
  Alpha-≡→Alpha xs cl (apply p q) = apply
    (Alpha-≡→Alpha xs (_≃_.to Closed′-apply≃ cl .proj₁) p)
    (Alpha-≡→Alpha xs (_≃_.to Closed′-apply≃ cl .proj₂) q)
  Alpha-≡→Alpha xs cl (lambda p) = lambda
    (Alpha-binders-≡→Alpha-binders xs (_≃_.to Closed′-lambda≃ cl) p)
  Alpha-≡→Alpha xs cl (case p q) = case
    (Alpha-≡→Alpha xs (_≃_.to Closed′-case≃ cl .proj₁) p)
    (Alpha-Br-⋆-≡→Alpha-Br-⋆ xs (_≃_.to Closed′-case≃ cl .proj₂) q)
  Alpha-≡→Alpha xs cl (rec p) = rec
    (Alpha-binders-≡→Alpha-binders xs (_≃_.to Closed′-rec≃ cl) p)
  Alpha-≡→Alpha xs cl (var {x₁ = x₁} {x₂ = x₂} p) = var
    (≡-[]ʳ→[]ʳ xs (_≃_.to Closed′-var≃ cl) p)
  Alpha-≡→Alpha xs cl (const c₁≡c₂ p) = const c₁≡c₂
    (Alpha-⋆-≡→Alpha-⋆ xs (_≃_.to Closed′-const≃ cl) p)

  Alpha-Br-≡→Alpha-Br :
    ∀ xs →
    Closed′-Br (List.map proj₁ xs) b₁ →
    Alpha-Br (_≡_ [ xs ]ʳ) b₁ b₂ →
    Alpha-Br (R   [ xs ]ʳ) b₁ b₂
  Alpha-Br-≡→Alpha-Br xs cl (branch c₁≡c₂ p) = branch c₁≡c₂
    (Alpha-binders-≡→Alpha-binders xs cl p)

  Alpha-binders-≡→Alpha-binders :
    ∀ xs →
    Closed′ (ys₁ ++ List.map proj₁ xs) e₁ →
    Alpha-binders (_≡_ [ xs ]ʳ) ys₁ e₁ ys₂ e₂ →
    Alpha-binders (R   [ xs ]ʳ) ys₁ e₁ ys₂ e₂
  Alpha-binders-≡→Alpha-binders xs cl (nil p) = nil
    (Alpha-≡→Alpha xs cl p)
  Alpha-binders-≡→Alpha-binders
    xs cl (cons {xs₁ = xs₁} {xs₂ = xs₂} p) = cons
    (Alpha-binders-≡→Alpha-binders (_ ∷ xs) (Closed′-++-∷ xs₁ cl) p)

  Alpha-⋆-≡→Alpha-⋆ :
    ∀ xs →
    All (Closed′ (List.map proj₁ xs)) es₁ →
    Listᴾ (Alpha (_≡_ [ xs ]ʳ)) es₁ es₂ →
    Listᴾ (Alpha (R   [ xs ]ʳ)) es₁ es₂
  Alpha-⋆-≡→Alpha-⋆ {es₁ = []} {es₂ = []} _ _ _ =
    _
  Alpha-⋆-≡→Alpha-⋆ {es₁ = _ ∷ _} {es₂ = _ ∷ _} xs cl (p , ps) =
    Alpha-≡→Alpha xs (All.head cl) p ,
    Alpha-⋆-≡→Alpha-⋆ xs (All.tail cl) ps

  Alpha-Br-⋆-≡→Alpha-Br-⋆ :
    ∀ xs →
    All (Closed′-Br (List.map proj₁ xs)) bs₁ →
    Listᴾ (Alpha-Br (_≡_ [ xs ]ʳ)) bs₁ bs₂ →
    Listᴾ (Alpha-Br (R   [ xs ]ʳ)) bs₁ bs₂
  Alpha-Br-⋆-≡→Alpha-Br-⋆ {bs₁ = []} {bs₂ = []} _ _ _ =
    _
  Alpha-Br-⋆-≡→Alpha-Br-⋆ {bs₁ = _ ∷ _} {bs₂ = _ ∷ _} xs cl (p , ps) =
    Alpha-Br-≡→Alpha-Br xs (All.head cl) p ,
    Alpha-Br-⋆-≡→Alpha-Br-⋆ xs (All.tail cl) ps

------------------------------------------------------------------------
-- Several things respect α-equivalence

-- The free variable relation respects α-equivalence.

mutual

  α-∈ : e₁ ≈α e₂ → x ∈FV e₁ → x ∈FV e₂
  α-∈ e₁≈e₂ x∈ with Alpha-∈ e₁≈e₂ x∈
  … | x′ , x≡x′ , x′∈ = subst (_∈FV _) (sym x≡x′) x′∈

  Alpha-∈ :
    Alpha R e₁ e₂ → x₁ ∈FV e₁ → ∃ λ x₂ → R x₁ x₂ × x₂ ∈FV e₂
  Alpha-∈ {R = R} (var Ry₁y₂) (var x₁≡y₁) =
    _ , subst (flip R _) (sym x₁≡y₁) Ry₁y₂ , var refl

  Alpha-∈ (lambda e₁≈e₂) (lambda x₁≢y₁ x₁∈) =
    let (x₂ , x₁Rx₂ , x₂∈e₂ , x₂∉[x₃]) =
          Alpha-binders-∈ e₁≈e₂ x₁∈ [ x₁≢y₁ , id ]
    in x₂ , x₁Rx₂ , lambda (x₂∉[x₃] ∘ inj₁) x₂∈e₂

  Alpha-∈ (rec e₁≈e₂) (rec x₁≢y₁ x₁∈) =
    let (x₂ , x₁Rx₂ , x₂∈e₂ , x₂∉[x₃]) =
          Alpha-binders-∈ e₁≈e₂ x₁∈ [ x₁≢y₁ , id ]
    in x₂ , x₁Rx₂ , rec (x₂∉[x₃] ∘ inj₁) x₂∈e₂

  Alpha-∈ (apply e₁₁≈e₁₂ e₂₁≈e₂₂) (apply-left x₁∈) =
    Σ-map id (Σ-map id apply-left) $ Alpha-∈ e₁₁≈e₁₂ x₁∈
  Alpha-∈ (apply e₁₁≈e₁₂ e₂₁≈e₂₂) (apply-right x₁∈) =
    Σ-map id (Σ-map id apply-right) $ Alpha-∈ e₂₁≈e₂₂ x₁∈

  Alpha-∈ (const _ es₁≈es₂) (const x₁∈ ∈es₁) =
    Σ-map id (Σ-map id $ uncurry λ _ → uncurry const) $
    Alpha-⋆-∈ es₁≈es₂ x₁∈ ∈es₁

  Alpha-∈ (case e₁≈e₂ bs₁≈bs₂) (case-head x₁∈) =
    Σ-map id (Σ-map id case-head) $
    Alpha-∈ e₁≈e₂ x₁∈

  Alpha-∈ (case e₁≈e₂ bs₁≈bs₂) (case-body x₁∈ ∈bs₁ ∉xs₁) =
    Σ-map id (Σ-map id λ (_ , _ , _ , x₂∈ , ∈bs₂ , ∉xs₂) →
                case-body x₂∈ ∈bs₂ ∉xs₂) $
    Alpha-Br-⋆-∈ bs₁≈bs₂ x₁∈ ∈bs₁ ∉xs₁

  Alpha-Br-∈ :
    Alpha-Br R (branch c₁ xs₁ e₁) (branch c₂ xs₂ e₂) →
    x₁ ∈FV e₁ → ¬ x₁ ∈ xs₁ →
    ∃ λ x₂ → R x₁ x₂ × x₂ ∈FV e₂ × ¬ x₂ ∈ xs₂
  Alpha-Br-∈ (branch _ bs₁≈bs₂) = Alpha-binders-∈ bs₁≈bs₂

  Alpha-binders-∈ :
    Alpha-binders R xs₁ e₁ xs₂ e₂ →
    x₁ ∈FV e₁ → ¬ x₁ ∈ xs₁ →
    ∃ λ x₂ → R x₁ x₂ × x₂ ∈FV e₂ × ¬ x₂ ∈ xs₂
  Alpha-binders-∈ (nil e₁≈e₂) x₁∈ _ =
    Σ-map id (Σ-map id (_, λ ())) $
    Alpha-∈ e₁≈e₂ x₁∈
  Alpha-binders-∈ (cons {x₁ = y₁} {x₂ = y₂} bs₁≈bs₂) x₁∈ x₁∉
    with Alpha-binders-∈ bs₁≈bs₂ x₁∈ (x₁∉ ∘ inj₂)
  … | x₂ , inj₂ (_ , y₂≢x₂ , Rx₁x₂) , x₂∈ , x₂∉ =
    x₂ , Rx₁x₂ , x₂∈ , [ y₂≢x₂ ∘ sym , x₂∉ ]
  … | _ , inj₁ (y₁≡x₁ , _) , _ =
    ⊥-elim $ x₁∉ (inj₁ (sym y₁≡x₁))

  Alpha-⋆-∈ :
    Listᴾ (Alpha R) es₁ es₂ →
    x₁ ∈FV e₁ → e₁ ∈ es₁ →
    ∃ λ x₂ → R x₁ x₂ × ∃ λ e₂ → x₂ ∈FV e₂ × e₂ ∈ es₂
  Alpha-⋆-∈
    {es₁ = _ ∷ _} {es₂ = _ ∷ _} (e₁≈e₂ , es₁≈es₂) x₁∈ (inj₁ ≡e₁) =
    Σ-map id (Σ-map id λ x₂∈ → _ , x₂∈ , inj₁ refl) $
    Alpha-∈ e₁≈e₂ (subst (_ ∈FV_) ≡e₁ x₁∈)
  Alpha-⋆-∈
    {es₁ = _ ∷ _} {es₂ = _ ∷ _} (e₁≈e₂ , es₁≈es₂) x₁∈ (inj₂ ∈es₁) =
    Σ-map id (Σ-map id (Σ-map id (Σ-map id inj₂))) $
    Alpha-⋆-∈ es₁≈es₂ x₁∈ ∈es₁

  Alpha-Br-⋆-∈ :
    Listᴾ (Alpha-Br R) bs₁ bs₂ →
    x₁ ∈FV e₁ → branch c₁ xs₁ e₁ ∈ bs₁ → ¬ x₁ ∈ xs₁ →
    ∃ λ x₂ → R x₁ x₂ × ∃ λ c₂ → ∃ λ xs₂ → ∃ λ e₂ →
      x₂ ∈FV e₂ × branch c₂ xs₂ e₂ ∈ bs₂ × ¬ x₂ ∈ xs₂
  Alpha-Br-⋆-∈
    {bs₁ = branch _ _ _ ∷ _} {bs₂ = branch _ _ _ ∷ _}
    (b₁≈b₂ , bs₁≈bs₂) x₁∈ (inj₁ ≡b₁) x₁∉
    with
      Alpha-Br-∈
        b₁≈b₂
        (subst (_ ∈FV_) (cong (λ { (branch _ _ e) → e }) ≡b₁) x₁∈)
        (x₁∉ ∘
         subst (_ ∈_) (cong (λ { (branch _ xs _) → xs }) (sym ≡b₁)))
  … | x₂ , Rx₁x₂ , x₂∈ , x₂∉ =
    x₂ , Rx₁x₂ , _ , _ , _ , x₂∈ , inj₁ refl , x₂∉
  Alpha-Br-⋆-∈
    {bs₁ = _ ∷ _} {bs₂ = _ ∷ _} (b₁≈b₂ , bs₁≈bs₂) x₁∈ (inj₂ ∈bs₁) x₁∉ =
    (Σ-map id $ Σ-map id $ Σ-map id $ Σ-map id $ Σ-map id $ Σ-map id $
     Σ-map inj₂ id) $
    Alpha-Br-⋆-∈ bs₁≈bs₂ x₁∈ ∈bs₁ x₁∉

-- The predicate Closed′ respects α-equivalence.

α-closed′ : e₁ ≈α e₂ → Closed′ xs e₁ → Closed′ xs e₂
α-closed′ e₁≈e₂ cl x x∉ x∈ =
  cl x x∉ (α-∈ (sym-α e₁≈e₂) x∈)

-- The predicate Closed respects α-equivalence.

α-closed : e₁ ≈α e₂ → Closed e₁ → Closed e₂
α-closed = α-closed′

-- If Alpha-binders (R [ x₁ ∼ x₂ ] [ y₁ ∼ y₂ ]) xs₁ e₁ xs₂ e₂ holds,
-- x₁ is not equal to y₁, and x₂ is equal to y₂, then
-- ⟨ xs₁ , e₁ ⟩[ x₁ ← e₁′ ] ≡ e₁ is equal to e₁.

α∼∼≢≡→⟨,⟩[←]≡ :
  Alpha-binders (R [ x₁ ∼ x₂ ] [ y₁ ∼ y₂ ]) xs₁ e₁ xs₂ e₂ →
  x₁ ≢ y₁ → x₂ ≡ y₂ →
  ⟨ xs₁ , e₁ ⟩[ x₁ ← e₁′ ] ≡ e₁
α∼∼≢≡→⟨,⟩[←]≡
  {R = R} {x₁ = x₁} {x₂ = x₂} {y₁ = y₁} {y₂ = y₂}
  {xs₁ = xs₁} {e₁ = e₁} {xs₂ = xs₂} {e₂ = e₂} {e₁′ = e₁′}
  e₁≈e₂ x₁≢y₁ x₂≡y₂ = ⟨,⟩[←]-∉ xs₁

  (x₁ ∈FV e₁ × ¬ x₁ ∈ xs₁                                                 →⟨ uncurry (Alpha-binders-∈ e₁≈e₂) ⟩
   (∃ λ z₂ → (R [ x₁ ∼ x₂ ] [ y₁ ∼ y₂ ]) x₁ z₂ × z₂ ∈FV e₂ × ¬ z₂ ∈ xs₂)  →⟨ Σ-map id proj₁ ⟩
   (∃ λ z₂ → (R [ x₁ ∼ x₂ ] [ y₁ ∼ y₂ ]) x₁ z₂)                           →⟨ ≢≡→¬[∼][∼] R x₁≢y₁ x₂≡y₂ ∘ proj₂ ⟩□
   ⊥                                                                      □)

-- If Alpha-binders (R [ x₁ ∼ x₂ ] [ y₁ ∼ y₂ ]) xs₁ e₁ xs₂ e₂ holds,
-- x₁ is equal to y₁, and x₂ is not equal to y₂, then
-- ⟨ xs₂ , e₂ ⟩[ x₂ ← e₂′ ] ≡ e₂ is equal to e₂.

α∼∼≡≢→⟨,⟩[←]≡ :
  Alpha-binders (R [ x₁ ∼ x₂ ] [ y₁ ∼ y₂ ]) xs₁ e₁ xs₂ e₂ →
  x₁ ≡ y₁ → x₂ ≢ y₂ →
  ⟨ xs₂ , e₂ ⟩[ x₂ ← e₂′ ] ≡ e₂
α∼∼≡≢→⟨,⟩[←]≡
  {R = R} {x₁ = x₁} {x₂ = x₂} {y₁ = y₁} {y₂ = y₂}
  {xs₁ = xs₁} {e₁ = e₁} {xs₂ = xs₂} {e₂ = e₂} {e₂′ = e₂′}
  e₁≈e₂ x₁≡y₁ x₂≢y₂ = ⟨,⟩[←]-∉ xs₂

  (x₂ ∈FV e₂ × ¬ x₂ ∈ xs₂                                                 →⟨ uncurry (Alpha-binders-∈ (sym-Alpha-binders e₁≈e₂)) ⟩
   (∃ λ z₁ → (R [ x₁ ∼ x₂ ] [ y₁ ∼ y₂ ]) z₁ x₂ × z₁ ∈FV e₁ × ¬ z₁ ∈ xs₁)  →⟨ Σ-map id proj₁ ⟩
   (∃ λ z₁ → (R [ x₁ ∼ x₂ ] [ y₁ ∼ y₂ ]) z₁ x₂)                           →⟨ ≡≢→¬[∼][∼] R x₁≡y₁ x₂≢y₂ ∘ proj₂ ⟩□
   ⊥                                                                      □)

-- Substitution does not necessarily respect α-equivalence.

¬-subst-α :
  ¬ (∀ {x₁ x₂ e₁ e₂ e₁′ e₂′} →
     Alpha (_≡_ [ x₁ ∼ x₂ ]) e₁ e₂ →
     e₁′ ≈α e₂′ →
     e₁ [ x₁ ← e₁′ ] ≈α e₂ [ x₂ ← e₂′ ])
¬-subst-α subst-α =
  not-equal (subst-α e¹≈e² e³≈e³)
  where
  x¹ = V.name 0
  x² = V.name 1
  z  = V.name 2

  e¹ = lambda x¹ (var z)
  e² = lambda x² (var z)

  e³ = var x¹

  e¹≈e² : Alpha (_≡_ [ z ∼ z ]) e¹ e²
  e¹≈e² = lambda (cons (nil (var (inj₂
    ( V.distinct-codes→distinct-names (λ ())
    , V.distinct-codes→distinct-names (λ ())
    , inj₁ (refl , refl)
    )))))

  e³≈e³ : e³ ≈α e³
  e³≈e³ = refl-α

  not-equal : ¬ e¹ [ z ← e³ ] ≈α e² [ z ← e³ ]
  not-equal _ with z V.≟ x¹ | z V.≟ x² | z V.≟ z
  not-equal (lambda (cons (nil (var (inj₁ (_ , x²≡x¹))))))
    | no _ | no _ | yes _ =
    from-⊎ (1 Nat.≟ 0) (V.name-injective x²≡x¹)
  not-equal (lambda (cons (nil (var (inj₂ (x¹≢x¹ , _))))))
    | no _ | no _ | yes _ =
    x¹≢x¹ refl
  not-equal _ | yes z≡x¹ | _ | _ =
    from-⊎ (2 Nat.≟ 0) (V.name-injective z≡x¹)
  not-equal _ | _ | yes z≡x² | _ =
    from-⊎ (2 Nat.≟ 1) (V.name-injective z≡x²)
  not-equal _ | _ | _ | no z≢z = z≢z refl

-- However, substitution of closed terms respects α-equivalence.

mutual

  subst-α :
    Closed e₁′ →
    Alpha (_≡_ [ x₁ ∼ x₂ ]) e₁ e₂ → e₁′ ≈α e₂′ →
    e₁ [ x₁ ← e₁′ ] ≈α e₂ [ x₂ ← e₂′ ]
  subst-α = subst-Alpha

  subst-Alpha :
    Closed e₁′ →
    Alpha (R [ x₁ ∼ x₂ ]) e₁ e₂ →
    e₁′ ≈α e₂′ →
    Alpha R (e₁ [ x₁ ← e₁′ ]) (e₂ [ x₂ ← e₂′ ])
  subst-Alpha {x₁ = x₁} {x₂ = x₂}
              cl (var {x₁ = y₁} {x₂ = y₂} y₁≈y₂) e₁′≈e₂′
    with x₁ V.≟ y₁ | x₂ V.≟ y₂ | y₁≈y₂
  … | yes _     | yes _     | _                    = ≈α→Alpha cl e₁′≈e₂′
  … | no _      | no _      | inj₂ (_ , _ , y₁Ry₂) = var y₁Ry₂
  … | _         | no x₂≢y₂  | inj₁ (_ , x₂≡y₂)     = ⊥-elim $ x₂≢y₂ x₂≡y₂
  … | no x₁≢y₁  | _         | inj₁ (x₁≡y₁ , _)     = ⊥-elim $ x₁≢y₁ x₁≡y₁
  … | yes x₁≡y₁ | _         | inj₂ (x₁≢y₁ , _)     = ⊥-elim $ x₁≢y₁ x₁≡y₁
  … | _         | yes x₂≡y₂ | inj₂ (_ , x₂≢y₂ , _) = ⊥-elim $ x₂≢y₂ x₂≡y₂

  subst-Alpha cl (lambda e₁≈e₂) e₁′≈e₂′ =
    lambda (subst-Alpha-binders cl e₁≈e₂ e₁′≈e₂′)

  subst-Alpha cl (apply e₁₁≈e₁₂ e₂₁≈e₂₂) e₁′≈e₂′ =
    apply
      (subst-Alpha cl e₁₁≈e₁₂ e₁′≈e₂′)
      (subst-Alpha cl e₂₁≈e₂₂ e₁′≈e₂′)

  subst-Alpha cl (case e₁≈e₂ bs₁≈bs₂) e₁′≈e₂′ =
    case
      (subst-Alpha cl e₁≈e₂ e₁′≈e₂′)
      (subst-Alpha-Br-⋆ cl bs₁≈bs₂ e₁′≈e₂′)

  subst-Alpha cl (rec e₁≈e₂) e₁′≈e₂′ =
    rec (subst-Alpha-binders cl e₁≈e₂ e₁′≈e₂′)

  subst-Alpha cl (const c₁≡c₂ es₁≈es₂) e₁′≈e₂′ =
    const c₁≡c₂ (subst-Alpha-⋆ cl es₁≈es₂ e₁′≈e₂′)

  subst-Alpha-Br :
    Closed e₁′ →
    Alpha-Br (R [ x₁ ∼ x₂ ]) b₁ b₂ →
    e₁′ ≈α e₂′ →
    Alpha-Br R (b₁ [ x₁ ← e₁′ ]B) (b₂ [ x₂ ← e₂′ ]B)
  subst-Alpha-Br
    {e₁′ = e₁′} {R = R} {x₁ = x₁} {x₂ = x₂} {e₂′ = e₂′} cl
    (branch
       {c₁ = c₁} {c₂ = c₂} {xs₁ = xs₁} {e₁ = e₁} {xs₂ = xs₂} {e₂ = e₂}
       c₁≡c₂ p)
    e₁′≈e₂′ =                                                $⟨ p ⟩

    Alpha-binders (R [ x₁ ∼ x₂ ]) xs₁ e₁ xs₂ e₂              →⟨ flip (subst-Alpha-binders cl) e₁′≈e₂′ ⟩

    Alpha-binders R
      xs₁ ⟨ xs₁ , e₁ ⟩[ x₁ ← e₁′ ]
      xs₂ ⟨ xs₂ , e₂ ⟩[ x₂ ← e₂′ ]                           →⟨ subst id $ cong₂ (flip (Alpha-binders _ _) _)
                                                                  (⟨,⟩[←]≡ xs₁)
                                                                  (⟨,⟩[←]≡ xs₂) ⟩
    Alpha-binders R
      xs₁ (if V.member x₁ xs₁ then e₁ else e₁ [ x₁ ← e₁′ ])
      xs₂ (if V.member x₂ xs₂ then e₂ else e₂ [ x₂ ← e₂′ ])  →⟨ branch c₁≡c₂ ⟩

    Alpha-Br R
      (branch c₁ xs₁ $
       if V.member x₁ xs₁ then e₁ else e₁ [ x₁ ← e₁′ ])
      (branch c₂ xs₂ $
       if V.member x₂ xs₂ then e₂ else e₂ [ x₂ ← e₂′ ])      →⟨ subst id $ cong₂ (Alpha-Br _)
                                                                  (if-then-else-commutes (branch _ _) (V.member x₁ xs₁))
                                                                  (if-then-else-commutes (branch _ _) (V.member x₂ xs₂)) ⟩□
    Alpha-Br R
      (if V.member x₁ xs₁
       then branch c₁ xs₁ e₁
       else branch c₁ xs₁ (e₁ [ x₁ ← e₁′ ]))
      (if V.member x₂ xs₂
       then branch c₂ xs₂ e₂
       else branch c₂ xs₂ (e₂ [ x₂ ← e₂′ ]))                 □

  subst-Alpha-binders :
    Closed e₁′ →
    Alpha-binders (R [ x₁ ∼ x₂ ]) xs₁ e₁ xs₂ e₂ →
    e₁′ ≈α e₂′ →
    Alpha-binders R
      xs₁ ⟨ xs₁ , e₁ ⟩[ x₁ ← e₁′ ] xs₂ ⟨ xs₂ , e₂ ⟩[ x₂ ← e₂′ ]
  subst-Alpha-binders cl (nil p) e₁′≈e₂′ =
    nil (subst-Alpha cl p e₁′≈e₂′)

  subst-Alpha-binders
    {e₁′ = e₁′} {R = R} {x₁ = x₁} {x₂ = x₂} {e₂′ = e₂′} cl
    (cons {x₁ = y₁} {x₂ = y₂}
       {xs₁ = xs₁} {e₁ = e₁} {xs₂ = xs₂} {e₂ = e₂} p)
    e₁′≈e₂′ =
    cons (if-≟-then-else-subst-Alpha-binders cl p e₁′≈e₂′)

  if-≟-then-else-subst-Alpha-binders :
    Closed e₁′ →
    Alpha-binders (R [ x₁ ∼ x₂ ] [ y₁ ∼ y₂ ]) xs₁ e₁ xs₂ e₂ →
    e₁′ ≈α e₂′ →
    Alpha-binders (R [ y₁ ∼ y₂ ])
      xs₁ (if x₁ V.≟ y₁ then e₁ else ⟨ xs₁ , e₁ ⟩[ x₁ ← e₁′ ])
      xs₂ (if x₂ V.≟ y₂ then e₂ else ⟨ xs₂ , e₂ ⟩[ x₂ ← e₂′ ])
  if-≟-then-else-subst-Alpha-binders
    {e₁′ = e₁′} {R = R} {x₁ = x₁} {x₂ = x₂} {y₁ = y₁} {y₂ = y₂}
    {xs₁ = xs₁} {e₁ = e₁} {xs₂ = xs₂} {e₂ = e₂} {e₂′ = e₂′}
    cl e₁≈e₂ e₁′≈e₂′
    with x₁ V.≟ y₁ | x₂ V.≟ y₂
  … | yes x₁≡y₁ | yes x₂≡y₂ =                                $⟨ e₁≈e₂ ⟩
    Alpha-binders (R [ x₁ ∼ x₂ ] [ y₁ ∼ y₂ ]) xs₁ e₁ xs₂ e₂  →⟨ map-Alpha-binders (drop-[∼] R (inj₁ x₁≡y₁)) ⟩□
    Alpha-binders (R [ y₁ ∼ y₂ ]) xs₁ e₁ xs₂ e₂              □

  … | no x₁≢y₁ | no x₂≢y₂ =                                  $⟨ e₁≈e₂ ⟩

    Alpha-binders (R [ x₁ ∼ x₂ ] [ y₁ ∼ y₂ ]) xs₁ e₁ xs₂ e₂  →⟨ map-Alpha-binders (swap-[∼] R x₁≢y₁ x₂≢y₂) ⟩

    Alpha-binders (R [ y₁ ∼ y₂ ] [ x₁ ∼ x₂ ]) xs₁ e₁ xs₂ e₂  →⟨ flip (subst-Alpha-binders cl) e₁′≈e₂′ ⟩□

    Alpha-binders (R [ y₁ ∼ y₂ ])
      xs₁ ⟨ xs₁ , e₁ ⟩[ x₁ ← e₁′ ]
      xs₂ ⟨ xs₂ , e₂ ⟩[ x₂ ← e₂′ ]                           □

  … | yes x₁≡y₁ | no x₂≢y₂ =                                           $⟨ e₁≈e₂ ⟩
    Alpha-binders (R [ x₁ ∼ x₂ ] [ y₁ ∼ y₂ ]) xs₁ e₁ xs₂ e₂            →⟨ map-Alpha-binders (drop-[∼] R (inj₁ x₁≡y₁)) ⟩
    Alpha-binders (R [ y₁ ∼ y₂ ]) xs₁ e₁ xs₂ e₂                        →⟨ subst (Alpha-binders _ _ _ _) $ sym $
                                                                          α∼∼≡≢→⟨,⟩[←]≡ e₁≈e₂ x₁≡y₁ x₂≢y₂ ⟩
    Alpha-binders (R [ y₁ ∼ y₂ ]) xs₁ e₁ xs₂ ⟨ xs₂ , e₂ ⟩[ x₂ ← e₂′ ]  □

  … | no x₁≢y₁ | yes x₂≡y₂ =                                           $⟨ e₁≈e₂ ⟩
    Alpha-binders (R [ x₁ ∼ x₂ ] [ y₁ ∼ y₂ ]) xs₁ e₁ xs₂ e₂            →⟨ map-Alpha-binders (drop-[∼] R (inj₂ x₂≡y₂)) ⟩
    Alpha-binders (R [ y₁ ∼ y₂ ]) xs₁ e₁ xs₂ e₂                        →⟨ subst (λ e → Alpha-binders _ _ e _ _) $ sym $
                                                                          α∼∼≢≡→⟨,⟩[←]≡ e₁≈e₂ x₁≢y₁ x₂≡y₂ ⟩
    Alpha-binders (R [ y₁ ∼ y₂ ]) xs₁ ⟨ xs₁ , e₁ ⟩[ x₁ ← e₁′ ] xs₂ e₂  □

  subst-Alpha-⋆ :
    Closed e₁′ →
    Listᴾ (Alpha (R [ x₁ ∼ x₂ ])) es₁ es₂ →
    e₁′ ≈α e₂′ →
    Listᴾ (Alpha R) (es₁ [ x₁ ← e₁′ ]⋆) (es₂ [ x₂ ← e₂′ ]⋆)
  subst-Alpha-⋆ {es₁ = []} {es₂ = []} _ _ _ =
    _

  subst-Alpha-⋆ {es₁ = _ ∷ _} {es₂ = _ ∷ _} cl (p , ps) e₁′≈e₂′ =
    subst-Alpha cl p e₁′≈e₂′ ,
    subst-Alpha-⋆ cl ps e₁′≈e₂′

  subst-Alpha-Br-⋆ :
    Closed e₁′ →
    Listᴾ (Alpha-Br (R [ x₁ ∼ x₂ ])) bs₁ bs₂ →
    e₁′ ≈α e₂′ →
    Listᴾ (Alpha-Br R) (bs₁ [ x₁ ← e₁′ ]B⋆) (bs₂ [ x₂ ← e₂′ ]B⋆)
  subst-Alpha-Br-⋆ {bs₁ = []} {bs₂ = []} _ _ _ =
    _

  subst-Alpha-Br-⋆ {bs₁ = _ ∷ _} {bs₂ = _ ∷ _} cl (p , ps) e₁′≈e₂′ =
    subst-Alpha-Br cl p e₁′≈e₂′ ,
    subst-Alpha-Br-⋆ cl ps e₁′≈e₂′

-- The predicate Lookup respects α-equivalence (in a certain sense).

Lookup-α :
  Listᴾ (Alpha-Br R) bs₁ bs₂ →
  Lookup c bs₁ xs₁ e₁ →
  ∃ λ xs₂ → ∃ λ e₂ →
    Lookup c bs₂ xs₂ e₂ ×
    Alpha-binders R xs₁ e₁ xs₂ e₂
Lookup-α {bs₁ = _ ∷ _} {bs₂ = _ ∷ _} (branch refl p , _) here =
  _ , _ , here , p
Lookup-α
  {R = R} {bs₁ = _ ∷ bs₁} {bs₂ = _ ∷ bs₂} {c = c} {xs₁ = xs₁} {e₁ = e₁}
  (branch {c₂ = c′} {xs₂ = xs′} {e₂ = e′} refl _ , bs₁≈bs₂)
  (there c≢c′ p) =
                                               $⟨ Lookup-α bs₁≈bs₂ p ⟩
  (∃ λ xs₂ → ∃ λ e₂ →
   Lookup c bs₂ xs₂ e₂ ×
   Alpha-binders R xs₁ e₁ xs₂ e₂)              →⟨ Σ-map id (Σ-map id (Σ-map (there c≢c′) id)) ⟩□

  (∃ λ xs₂ → ∃ λ e₂ →
   Lookup c (branch c′ xs′ e′ ∷ bs₂) xs₂ e₂ ×
   Alpha-binders R xs₁ e₁ xs₂ e₂)              □

-- The predicate _[_←_]↦_ respects α-equivalence (in a certain sense)
-- for sufficiently closed things.

[←]↦-α :
  All Closed es₁ →
  Alpha-binders R xs₁ e₁ xs₂ e₂ →
  Listᴾ _≈α_ es₁ es₂ →
  e₁ [ xs₁ ← es₁ ]↦ e →
  ∃ λ e′ → e₂ [ xs₂ ← es₂ ]↦ e′ × Alpha R e e′
[←]↦-α {es₂ = []} _ (nil p) _ [] =
  _ , [] , p
[←]↦-α
  {es₁ = e₁ ∷ _} {R = R} {es₂ = e₂ ∷ es₂} cl
  (cons {x₁ = x₁} {x₂ = x₂} {xs₁ = xs₁} {e₁ = e} {xs₂ = xs₂} {e₂ = e′}
     p)
  (e₁≈e₂ , es₁≈es₂) (∷_ {e″ = e″} q) =                                $⟨ [←]↦-α (All.tail cl) p es₁≈es₂ q ⟩

  (∃ λ e‴ → e′ [ xs₂ ← es₂ ]↦ e‴ × Alpha (R [ x₁ ∼ x₂ ]) e″ e‴)       →⟨ (λ (e‴ , p , q) →
                                                                              e‴ [ x₂ ← e₂ ]
                                                                            , ∷ p
                                                                            , subst-Alpha (All.head cl) q e₁≈e₂) ⟩□
  (∃ λ e‴ →
       e′ [ x₂ ∷ xs₂ ← e₂ ∷ es₂ ]↦ e‴ × Alpha R (e″ [ x₁ ← e₁ ]) e‴)  □

-- The semantics respects α-equivalence (for closed terms).

mutual

  ⇓-α : Closed e₁ → e₁ ⇓ v₁ → e₁ ≈α e₂ → ∃ λ v₂ → e₂ ⇓ v₂ × v₁ ≈α v₂
  ⇓-α cl (apply {e = e₁} {v₂ = v₂₁} e₁₁⇓ e₂₁⇓ e₁⇓)
    (apply e₁₁≈e₁₂ e₂₁≈e₂₂)
    with ⇓-α (λ _ ∉ → cl _ ∉ ∘ apply-left)  e₁₁⇓ e₁₁≈e₁₂
       | ⇓-α (λ _ ∉ → cl _ ∉ ∘ apply-right) e₂₁⇓ e₂₁≈e₂₂
  … | lambda x₂ e₂ , e₁₂⇓ , lambda {x₁ = x₁} (cons (nil ≈v₁₂))
    | v₂₂ , e₂₂⇓ , ≈v₂₂ =
    case ⇓-α cl-e₁ e₁⇓ e₁≈e₂ of λ
      (_ , e₂⇓ , v₁≈v₂) →
        _ , apply e₁₂⇓ e₂₂⇓ e₂⇓ , v₁≈v₂
    where
    cl-e₁ : Closed (e₁ [ x₁ ← v₂₁ ])
    cl-e₁ = Closed′-closed-under-subst
      (λ _ x∉ x∈e₁ →
         closed⇓closed e₁₁⇓ (λ _ ∉ → cl _ ∉ ∘ apply-left)
           _ (λ ()) (lambda (x∉ ∘ inj₁) x∈e₁))
      (closed⇓closed e₂₁⇓ λ _ ∉ → cl _ ∉ ∘ apply-right)

    e₁≈e₂ : e₁ [ x₁ ← v₂₁ ] ≈α e₂ [ x₂ ← v₂₂ ]
    e₁≈e₂ = subst-α
      (closed⇓closed e₂₁⇓ (λ _ ∉ → cl _ ∉ ∘ apply-right))
      ≈v₁₂ ≈v₂₂

  ⇓-α cl (case {e = e₁} {bs = bs₁} {c = c} {es = vs₁} {xs = xs₁}
               {e′ = e′₁} {e″ = e″₁} e₁⇓ l₁ s₁ e″₁⇓)
    (case e₁≈e₂ bs₁≈bs₂) =
    case ⇓-α (λ _ ∉ → cl _ ∉ ∘ case-head) e₁⇓ e₁≈e₂ of λ where
      (const c vs₂ , e₂⇓ , const refl vs₁≈vs₂) →
        case Lookup-α bs₁≈bs₂ l₁ of λ
          (xs₂ , e′₂ , l₂ , b₁≈b₂) →
            case [←]↦-α cl-vs₁ b₁≈b₂ vs₁≈vs₂ s₁ of λ
              (e″₂ , s₂ , e″₁≈e″₂) →
                Σ-map id (Σ-map (case e₂⇓ l₂ s₂) id)
                  (⇓-α cl-e″₁ e″₁⇓ e″₁≈e″₂)
    where
    cl-vs₁ =                $⟨ cl ⟩
      Closed (case e₁ bs₁)  →⟨ (λ cl → _≃_.to Closed′-case≃ cl .proj₁) ⟩
      Closed e₁             →⟨ closed⇓closed e₁⇓ ⟩
      Closed (const c vs₁)  →⟨ _≃_.to Closed′-const≃ ⟩□
      All Closed vs₁        □

    cl-e″₁ =                   $⟨ cl ⟩
      Closed (case e₁ bs₁)     →⟨ (λ cl → _≃_.to Closed′-case≃ cl .proj₂ _ (Lookup→branch∈ l₁)) ⟩
      Closed′ (xs₁ ++ []) e′₁  →⟨ flip (Closed′-closed-under-[←]↦ s₁) cl-vs₁ ⟩□
      Closed e″₁               □

  ⇓-α cl (rec e₁⇓)
    rec-x₁-e₁≈rec-x₂-e₂@(rec {x₁ = x₁} {e₁ = e₁} (cons (nil e₁≈e₂))) =
    Σ-map id (Σ-map rec id) $
    ⇓-α cl′ e₁⇓ (subst-α cl e₁≈e₂ rec-x₁-e₁≈rec-x₂-e₂)
    where
    cl′ : Closed (e₁ [ x₁ ← rec x₁ e₁ ])
    cl′ = Closed′-closed-under-subst (_≃_.to Closed′-rec≃ cl) cl

  ⇓-α _ lambda (lambda e₁≈e₂) =
    _ , lambda , lambda e₁≈e₂

  ⇓-α cl (const es₁⇓) (const c₁≡c₂ es₁≈es₂) =
    Σ-map (const _) (Σ-map const (const c₁≡c₂)) $
    ⇓⋆-α (_≃_.to Closed′-const≃ cl) es₁⇓ es₁≈es₂

  ⇓⋆-α :
    All Closed es₁ →
    es₁ ⇓⋆ vs₁ → Listᴾ _≈α_ es₁ es₂ →
    ∃ λ vs₂ → es₂ ⇓⋆ vs₂ × Listᴾ _≈α_ vs₁ vs₂
  ⇓⋆-α {es₁ = []} {es₂ = []} _ [] _ =
    _ , [] , _
  ⇓⋆-α {es₁ = _ ∷ _} {es₂ = _ ∷ _} cl (e₁⇓ ∷ es₁⇓) (e₁≈e₂ , es₁≈es₂) =
    Σ-zip _∷_ (Σ-zip _∷_ _,_)
      (⇓-α (All.head cl) e₁⇓ e₁≈e₂)
      (⇓⋆-α (All.tail cl) es₁⇓ es₁≈es₂)

------------------------------------------------------------------------
-- Expressions quotiented by α-equivalence

-- Closed expressions quotiented by α-equivalence.

Closed-exp/α : Type
Closed-exp/α = Closed-exp /ᴱ (_≈α_ on proj₁)

-- Expressions with one free variable, quotiented by α-equivalence.

Almost-closed-exp/α : Type
Almost-closed-exp/α =
  (∃ λ (x : Var) → ∃ λ (e : Exp) → Closed′ (x ∷ []) e)
    /ᴱ
  (λ (x₁ , e₁ , _) (x₂ , e₂ , _) →
     Alpha (_≡_ [ x₁ ∼ x₂ ]) e₁ e₂)

-- Expressions with free variables taken from a given list, quotiented
-- by α-equivalence.

Exp/α : Type
Exp/α =
  (∃ λ (xs : List Var) → ∃ λ (e : Exp) → Closed′ xs e)
    /ᴱ
  (λ (xs₁ , e₁ , _) (xs₂ , e₂ , _) →
     Alpha-binders _≡_ xs₁ e₁ xs₂ e₂)

-- Closed branches quotiented by α-equivalence.

Closed-br/α : Type
Closed-br/α = ∃ Closed-Br /ᴱ (Alpha-Br _≡_ on proj₁)

-- Some "constructors" for Closed-exp/α.

apply/α : Closed-exp/α → Closed-exp/α → Closed-exp/α
apply/α = Q./ᴱ-zip
  (Σ-zip apply Closed′-closed-under-apply)
  refl-α
  refl-α
  apply

lambda/α : Almost-closed-exp/α → Closed-exp/α
lambda/α =
  (λ (x , e , cl) → lambda x e , Closed′-closed-under-lambda cl)
    Q./ᴱ-map
  (λ (x₁ , e₁ , _) (x₂ , e₂ , _) →
     Alpha (_≡_ [ x₁ ∼ x₂ ]) e₁ e₂  →⟨ Alpha.lambda ∘ cons ∘ nil ⟩□
     lambda x₁ e₁ ≈α lambda x₂ e₂   □)

case/α : Closed-exp/α → List Closed-br/α → Closed-exp/α
case/α e =
  List Closed-br/α                                     ↔⟨ inverse $ Q.List/ᴱ refl-α-Br ⟩
  List (∃ Closed-Br) /ᴱ Listᴾ (Alpha-Br _≡_ on proj₁)  →⟨ Q./ᴱ-zip
                                                            case′
                                                            refl-α
                                                            (Listᴾ-preserves-reflexivity refl-α-Br)
                                                            (λ {u = e₁} {v = e₂} → curry (lemma e₁ e₂ _ _))
                                                            e ⟩□
  Closed-exp/α                                         □
  where
  case′ : Closed-exp → List (∃ Closed-Br) → Closed-exp
  case′ (e , cl) =
    List (∃ Closed-Br)                       →⟨ All.List-Σ _ ⟩
    (∃ λ (bs : List Br) → All Closed-Br bs)  →⟨ Σ-map (case e) (Closed′-closed-under-case cl) ⟩□
    Closed-exp                               □

  lemma : ∀ _ _ _ _ _ → _
  lemma e₁ e₂ bs₁ bs₂ =
    (_≈α_ on proj₁) e₁ e₂ × Listᴾ (Alpha-Br _≡_ on proj₁) bs₁ bs₂  ↔⟨ (∃-cong λ _ → inverse All.Listᴾ-List-Σ) ⟩

    (_≈α_ on proj₁) e₁ e₂ ×
    Listᴾ (Alpha-Br _≡_)
      (All.List-Σ _ bs₁ .proj₁) (All.List-Σ _ bs₂ .proj₁)          →⟨ uncurry case ⟩□

    (_≈α_ on proj₁) (case′ e₁ bs₁) (case′ e₂ bs₂)                  □

rec/α : Almost-closed-exp/α → Closed-exp/α
rec/α =
  (λ (x , e , cl) → rec x e , Closed′-closed-under-rec cl)
    Q./ᴱ-map
  (λ (x₁ , e₁ , _) (x₂ , e₂ , _) →
     Alpha (_≡_ [ x₁ ∼ x₂ ]) e₁ e₂  →⟨ Alpha.rec ∘ cons ∘ nil ⟩□
     rec x₁ e₁ ≈α rec x₂ e₂         □)

const/α : Const → List Closed-exp/α → Closed-exp/α
const/α c =
  List Closed-exp/α                         ↔⟨ inverse $ Q.List/ᴱ refl-α ⟩
  List Closed-exp /ᴱ Listᴾ (_≈α_ on proj₁)  →⟨ const′ Q./ᴱ-map lemma ⟩□
  Closed-exp/α                              □
  where
  const′ : List Closed-exp → Closed-exp
  const′ =
    List Closed-exp                        →⟨ All.List-Σ _ ⟩
    (∃ λ (es : List Exp) → All Closed es)  →⟨ Σ-map (const c) Closed′-closed-under-const ⟩□
    Closed-exp                             □

  lemma = λ es₁ es₂ →
    Listᴾ (_≈α_ on proj₁) es₁ es₂                                   ↔⟨ inverse All.Listᴾ-List-Σ ⟩
    Listᴾ _≈α_ (All.List-Σ _ es₁ .proj₁) (All.List-Σ _ es₂ .proj₁)  →⟨ const refl ⟩□
    (_≈α_ on proj₁) (const′ es₁) (const′ es₂)                       □

-- A "constructor" for Closed-br/α.

branch/α : Const → Exp/α → Closed-br/α
branch/α c =
  (λ (xs , e , cl) →
     branch c xs e , Closed′-Br-closed-under-branch c [] cl)
    Q./ᴱ-map
  (λ (xs₁ , e₁ , cl₁) (xs₂ , e₂ , cl₂) →
     Alpha-binders _≡_ xs₁ e₁ xs₂ e₂                   →⟨ branch refl ⟩□
     Alpha-Br _≡_ (branch c xs₁ e₁) (branch c xs₂ e₂)  □)

-- Substitution, stated for Almost-closed-exp/α and Closed-exp/α.

_[_] : Almost-closed-exp/α → Closed-exp/α → Closed-exp/α
_[_] = Q./ᴱ-zip
  (λ (x , e , cl) (e′ , cl′) →
     e [ x ← e′ ] , Closed′-closed-under-subst cl cl′)
  (refl-Alpha _ λ _ _ → [≢→[∼]]→[∼] _≡_ λ _ → refl)
  refl-α
  (λ {(x₁ , e₁ , _)} {(x₂ , e₂ , _)} {(e₁′ , cl-e₁′)} {(e₂′ , _)} →
     curry (
       Alpha (_≡_ [ x₁ ∼ x₂ ]) e₁ e₂ × e₁′ ≈α e₂′  →⟨ uncurry (subst-α cl-e₁′) ⟩□
       e₁ [ x₁ ← e₁′ ] ≈α e₂ [ x₂ ← e₂′ ]          □))

-- The function _[_] computes in a certain way.

_ : Q.[ x , e , p ] [ Q.[ e′ , q ] ] ≡
    Q.[ e [ x ← e′ ] , Closed′-closed-under-subst p q ]
_ = refl

private

  -- Helper functions used to define _⇓α_ and ⇓α-propositional.

  ∃⇓≈α-propositional : Is-proposition (∃ λ v′ → e ⇓ v′ × v ≈α v′)
  ∃⇓≈α-propositional (_ , e⇓v′₁ , _) (_ , e⇓v′₂ , _) =
    Σ-≡,≡→≡
      (⇓-deterministic e⇓v′₁ e⇓v′₂)
      (×-closure 1 ⇓-propositional ≈α-propositional _ _)

  Semantics′ : Closed-exp → Closed-exp/α → Proposition lzero
  Semantics′ (e , _) = Q.rec λ where
    .Q.[]ʳ (v , _) →
      (∃ λ v′ → e ⇓ v′ × v ≈α v′) , ∃⇓≈α-propositional
    .Q.is-setʳ →
      ∃-H-level-H-level-1+ ext opaque-univ 1
    .Q.[]-respects-relationʳ {x = v₁ , _} {y = v₂ , _} →
      v₁ ≈α v₂                                               →⟨ (λ v₁≈v₂ →
                                                                   ∃-cong λ _ → ∃-cong λ _ →
                                                                   record { to   = trans-α (sym-α v₁≈v₂)
                                                                          ; from = trans-α v₁≈v₂
                                                                          }) ⟩

      (∃ λ v → e ⇓ v × v₁ ≈α v) ⇔ (∃ λ v → e ⇓ v × v₂ ≈α v)  ↔⟨ ⇔↔≡ ext opaque-univ ∃⇓≈α-propositional ∃⇓≈α-propositional ⟩

      (∃ λ v → e ⇓ v × v₁ ≈α v) ≡ (∃ λ v → e ⇓ v × v₂ ≈α v)  ↔⟨ ignore-propositional-component
                                                                  (H-level-propositional ext 1) ⟩□
      ((∃ λ v → e ⇓ v × v₁ ≈α v) , ∃⇓≈α-propositional) ≡
      ((∃ λ v → e ⇓ v × v₂ ≈α v) , ∃⇓≈α-propositional)       □

  Semantics : Closed-exp/α → Closed-exp/α → Proposition lzero
  Semantics = Q.rec λ where
    .Q.[]ʳ →
      Semantics′
    .Q.is-setʳ →
      Π-closure ext 2 λ _ →
      ∃-H-level-H-level-1+ ext opaque-univ 1
    .Q.[]-respects-relationʳ {x = e₁ , cl-e₁} {y = e₂ , cl-e₂} e₁≈e₂ →
      ⟨ext⟩ $ Q.elim-prop λ @0 where
        .Q.Elim-prop.is-propositionʳ _ →
          ∃-H-level-H-level-1+ ext opaque-univ 1
        .Q.Elim-prop.[]ʳ (v , _) →                                     $⟨ e₁≈e₂ ⟩

          e₁ ≈α e₂                                                     →⟨ (λ e₁≈e₂ → record
                                                                             { to   = λ (v′ , e₁⇓v′ , v≈v′) →
                                                                                        Σ-map id (Σ-map id (trans-α v≈v′)) $
                                                                                        ⇓-α cl-e₁ e₁⇓v′ e₁≈e₂
                                                                             ; from = λ (v′ , e₂⇓v′ , v≈v′) →
                                                                                        Σ-map id (Σ-map id (trans-α v≈v′)) $
                                                                                        ⇓-α cl-e₂ e₂⇓v′ (sym-α e₁≈e₂)
                                                                             }) ⟩

          (∃ λ v′ → e₁ ⇓ v′ × v ≈α v′) ⇔ (∃ λ v′ → e₂ ⇓ v′ × v ≈α v′)  ↔⟨ ⇔↔≡ ext opaque-univ ∃⇓≈α-propositional ∃⇓≈α-propositional ⟩

          (∃ λ v′ → e₁ ⇓ v′ × v ≈α v′) ≡ (∃ λ v′ → e₂ ⇓ v′ × v ≈α v′)  ↔⟨ ignore-propositional-component
                                                                            (H-level-propositional ext 1) ⟩□
          ((∃ λ v′ → e₁ ⇓ v′ × v ≈α v′) , ∃⇓≈α-propositional) ≡
          ((∃ λ v′ → e₂ ⇓ v′ × v ≈α v′) , ∃⇓≈α-propositional)          □

-- The semantics, stated for Closed-exp/α.

infix 4 _⇓α_

record _⇓α_ (e v : Closed-exp/α) : Type where
  constructor wrap
  field
    unwrap : Semantics e v .proj₁

-- The relation _⇓α_ is pointwise propositional.

⇓α-propositional : Is-proposition (e ⇓α v)
⇓α-propositional {e = e} {v = v} (wrap p) (wrap q) =
  cong wrap $ Semantics e v .proj₂ p q

-- A "computation rule" for _⇓α_.

⇓α≃⇓ : (Q.[ e , p ] ⇓α Q.[ v , q ]) ≃ (∃ λ v′ → e ⇓ v′ × v ≈α v′)
⇓α≃⇓ = Eq.↔→≃ _⇓α_.unwrap wrap (λ _ → refl) (λ _ → refl)
