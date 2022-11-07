------------------------------------------------------------------------
-- Alpha-equivalence
------------------------------------------------------------------------

open import Atom

module Alpha-equivalence (atoms : χ-atoms) where

open import Equality.Propositional.Cubical
open import Logical-equivalence using (_⇔_)
open import Prelude hiding (const; module List)

open import Bag-equivalence equality-with-J using (_∈_)
open import Equivalence equality-with-J using (_≃_)
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level.Closure equality-with-J
open import H-level.Truncation.Propositional equality-with-paths as T
  using (∥_∥)
open import List equality-with-J as List using (_++_)
open import List.All equality-with-J as All using (All)
import Nat equality-with-J as Nat

open import Chi            atoms
open import Free-variables atoms hiding (swap)

open χ-atoms atoms

private
  variable
    A                          : Type
    b₁ b₂                      : Br
    bs₁ bs₂                    : List Br
    c c₁ c₂                    : Const
    e e₁ e₂ e₃ e₁₁ e₁₂ e₂₁ e₂₂ : Exp
    es₁ es₂                    : List Exp
    R R₁ R₂                    : A → A → Type
    x x₁ x₁′ x₂ x₂′ y y₁ y₂    : A
    xs xs₁ xs₂ ys₁ ys₂         : List A

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

-- Alpha-⋆ lifts a binary relation to lists.

infixr 5 _∷_

data Alpha-⋆ (R : A → A → Type) : List A → List A → Type where
  []  : Alpha-⋆ R [] []
  _∷_ : R x₁ x₂ →
        Alpha-⋆ R xs₁ xs₂ →
        Alpha-⋆ R (x₁ ∷ xs₁) (x₂ ∷ xs₂)

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
      Alpha-⋆ (Alpha-Br R) bs₁ bs₂ →
      Alpha R (case e₁ bs₁) (case e₂ bs₂)

    rec :
      Alpha-binders R (x₁ ∷ []) e₁ (x₂ ∷ []) e₂ →
      Alpha R (rec x₁ e₁) (rec x₂ e₂)

    var : R x₁ x₂ → Alpha R (var x₁) (var x₂)

    const :
      Alpha-⋆ (Alpha R) es₁ es₂ →
      Alpha R (const c es₁) (const c es₂)

  data Alpha-Br (R : Var → Var → Type) : Br → Br → Type where
    branch :
      Alpha-binders R xs₁ e₁ xs₂ e₂ →
      Alpha-Br R (branch c xs₁ e₁) (branch c xs₂ e₂)

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
      (refl-Alpha-B⋆ bs λ x ∈bs x∉xs x∈ →
         r x (case-body x∈ ∈bs x∉xs))

  refl-Alpha (rec x e) r =
    rec (refl-Alpha-binders (x ∷ []) e
           (λ y y∉[x] → r y ∘ rec (y∉[x] ∘ inj₁)))

  refl-Alpha (var x) r =
    var (r x (var refl))

  refl-Alpha (const c es) r =
    const (refl-Alpha-⋆ es λ x e e∈es x∈e →
             r x (const x∈e e∈es))

  refl-Alpha-B :
    ∀ c xs e →
    (∀ x → ¬ x ∈ xs → x ∈FV e → R x x) →
    Alpha-Br R (branch c xs e) (branch c xs e)
  refl-Alpha-B _ xs e r =
    branch (refl-Alpha-binders xs e r)

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
    Alpha-⋆ (Alpha R) es es
  refl-Alpha-⋆ []       _ = []
  refl-Alpha-⋆ (e ∷ es) r =
    refl-Alpha e (λ x x∈e → r x e (inj₁ refl) x∈e) ∷
    refl-Alpha-⋆ es (λ x e e∈es x∈e → r x e (inj₂ e∈es) x∈e)

  refl-Alpha-B⋆ :
    ∀ bs →
    (∀ x {c xs e} → branch c xs e ∈ bs → ¬ x ∈ xs → x ∈FV e → R x x) →
    Alpha-⋆ (Alpha-Br R) bs bs
  refl-Alpha-B⋆ []                   r = []
  refl-Alpha-B⋆ (branch c xs e ∷ bs) r =
    refl-Alpha-B c xs e (λ x x∉xs x∈e → r x (inj₁ refl) x∉xs x∈e) ∷
    refl-Alpha-B⋆ bs (λ x ∈bs x∉xs x∈ → r x (inj₂ ∈bs) x∉xs x∈)

-- The α-equivalence relation is reflexive.

refl-α : e ≈α e
refl-α = refl-Alpha _ (λ _ _ → refl)

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

  map-Alpha r (const es₁≈es₂) =
    const (map-Alpha-⋆ r es₁≈es₂)

  map-Alpha r (case e₁≈e₂ bs₁≈bs₂) =
    case (map-Alpha r e₁≈e₂)
         (map-Alpha-Br-⋆ r bs₁≈bs₂)

  map-Alpha-Br :
    (∀ {x₁ x₂} → R₁ x₁ x₂ → R₂ x₁ x₂) →
    Alpha-Br R₁ b₁ b₂ → Alpha-Br R₂ b₁ b₂
  map-Alpha-Br r (branch bs₁≈bs₂) =
    branch (map-Alpha-binders r bs₁≈bs₂)

  map-Alpha-binders :
    (∀ {x₁ x₂} → R₁ x₁ x₂ → R₂ x₁ x₂) →
    Alpha-binders R₁ xs₁ e₁ xs₂ e₂ → Alpha-binders R₂ xs₁ e₁ xs₂ e₂
  map-Alpha-binders r (nil e₁≈e₂) =
    nil (map-Alpha r e₁≈e₂)
  map-Alpha-binders {R₁ = R₁} r (cons b₁≈b₂) =
    cons (map-Alpha-binders (map-[∼] R₁ r) b₁≈b₂)

  map-Alpha-⋆ :
    (∀ {x₁ x₂} → R₁ x₁ x₂ → R₂ x₁ x₂) →
    Alpha-⋆ (Alpha R₁) es₁ es₂ → Alpha-⋆ (Alpha R₂) es₁ es₂
  map-Alpha-⋆ _ []                = []
  map-Alpha-⋆ r (e₁≈e₂ ∷ es₁≈es₂) =
    map-Alpha r e₁≈e₂ ∷ map-Alpha-⋆ r es₁≈es₂

  map-Alpha-Br-⋆ :
    (∀ {x₁ x₂} → R₁ x₁ x₂ → R₂ x₁ x₂) →
    Alpha-⋆ (Alpha-Br R₁) bs₁ bs₂ → Alpha-⋆ (Alpha-Br R₂) bs₁ bs₂
  map-Alpha-Br-⋆ _ []                = []
  map-Alpha-Br-⋆ r (b₁≈b₂ ∷ bs₁≈bs₂) =
    map-Alpha-Br r b₁≈b₂ ∷ map-Alpha-Br-⋆ r bs₁≈bs₂

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

  sym-Alpha (const es₁≈es₂) =
    const (sym-Alpha-⋆ es₁≈es₂)

  sym-Alpha (case e₁≈e₂ bs₁≈bs₂) =
    case (sym-Alpha e₁≈e₂)
         (sym-Alpha-Br-⋆ bs₁≈bs₂)

  sym-Alpha-Br :
    Alpha-Br R b₁ b₂ → Alpha-Br (flip R) b₂ b₁
  sym-Alpha-Br (branch bs₁≈bs₂) =
    branch (sym-Alpha-binders bs₁≈bs₂)

  sym-Alpha-binders :
    Alpha-binders R xs₁ e₁ xs₂ e₂ → Alpha-binders (flip R) xs₂ e₂ xs₁ e₁
  sym-Alpha-binders (nil e₁≈e₂) =
    nil (sym-Alpha e₁≈e₂)
  sym-Alpha-binders {R = R} (cons b₁≈b₂) =
    cons (map-Alpha-binders (sym-[∼] R) (sym-Alpha-binders b₁≈b₂))

  sym-Alpha-⋆ :
    Alpha-⋆ (Alpha R) es₁ es₂ → Alpha-⋆ (Alpha (flip R)) es₂ es₁
  sym-Alpha-⋆ []                = []
  sym-Alpha-⋆ (e₁≈e₂ ∷ es₁≈es₂) =
    sym-Alpha e₁≈e₂ ∷ sym-Alpha-⋆ es₁≈es₂

  sym-Alpha-Br-⋆ :
    Alpha-⋆ (Alpha-Br R) bs₁ bs₂ → Alpha-⋆ (Alpha-Br (flip R)) bs₂ bs₁
  sym-Alpha-Br-⋆ []                = []
  sym-Alpha-Br-⋆ (b₁≈b₂ ∷ bs₁≈bs₂) =
    sym-Alpha-Br b₁≈b₂ ∷ sym-Alpha-Br-⋆ bs₁≈bs₂

-- The α-equivalence relation is symmetric.

sym-α : e₁ ≈α e₂ → e₂ ≈α e₁
sym-α = map-Alpha sym ∘ sym-Alpha

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
  Alpha-≡→Alpha xs cl (const p) = const
    (Alpha-⋆-≡→Alpha-⋆ xs (_≃_.to Closed′-const≃ cl) p)

  Alpha-Br-≡→Alpha-Br :
    ∀ xs →
    Closed′-Br (List.map proj₁ xs) b₁ →
    Alpha-Br (_≡_ [ xs ]ʳ) b₁ b₂ →
    Alpha-Br (R   [ xs ]ʳ) b₁ b₂
  Alpha-Br-≡→Alpha-Br xs cl (branch p) = branch
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
    Alpha-⋆ (Alpha (_≡_ [ xs ]ʳ)) es₁ es₂ →
    Alpha-⋆ (Alpha (R   [ xs ]ʳ)) es₁ es₂
  Alpha-⋆-≡→Alpha-⋆ _ _ [] =
    []
  Alpha-⋆-≡→Alpha-⋆ xs cl (p ∷ ps) =
    Alpha-≡→Alpha xs (All.head cl) p ∷
    Alpha-⋆-≡→Alpha-⋆ xs (All.tail cl) ps

  Alpha-Br-⋆-≡→Alpha-Br-⋆ :
    ∀ xs →
    All (Closed′-Br (List.map proj₁ xs)) bs₁ →
    Alpha-⋆ (Alpha-Br (_≡_ [ xs ]ʳ)) bs₁ bs₂ →
    Alpha-⋆ (Alpha-Br (R   [ xs ]ʳ)) bs₁ bs₂
  Alpha-Br-⋆-≡→Alpha-Br-⋆ _ _ [] =
    []
  Alpha-Br-⋆-≡→Alpha-Br-⋆ xs cl (p ∷ ps) =
    Alpha-Br-≡→Alpha-Br xs (All.head cl) p ∷
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

  Alpha-∈ (const es₁≈es₂) (const x₁∈ ∈es₁) =
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
  Alpha-Br-∈ (branch bs₁≈bs₂) = Alpha-binders-∈ bs₁≈bs₂

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
    Alpha-⋆ (Alpha R) es₁ es₂ →
    x₁ ∈FV e₁ → e₁ ∈ es₁ →
    ∃ λ x₂ → R x₁ x₂ × ∃ λ e₂ → x₂ ∈FV e₂ × e₂ ∈ es₂
  Alpha-⋆-∈ (e₁≈e₂ ∷ es₁≈es₂) x₁∈ (inj₁ ≡e₁) =
    Σ-map id (Σ-map id λ x₂∈ → _ , x₂∈ , inj₁ refl) $
    Alpha-∈ e₁≈e₂ (subst (_ ∈FV_) ≡e₁ x₁∈)
  Alpha-⋆-∈ (e₁≈e₂ ∷ es₁≈es₂) x₁∈ (inj₂ ∈es₁) =
    Σ-map id (Σ-map id (Σ-map id (Σ-map id inj₂))) $
    Alpha-⋆-∈ es₁≈es₂ x₁∈ ∈es₁

  Alpha-Br-⋆-∈ :
    Alpha-⋆ (Alpha-Br R) bs₁ bs₂ →
    x₁ ∈FV e₁ → branch c₁ xs₁ e₁ ∈ bs₁ → ¬ x₁ ∈ xs₁ →
    ∃ λ x₂ → R x₁ x₂ × ∃ λ c₂ → ∃ λ xs₂ → ∃ λ e₂ →
      x₂ ∈FV e₂ × branch c₂ xs₂ e₂ ∈ bs₂ × ¬ x₂ ∈ xs₂
  Alpha-Br-⋆-∈
    (_∷_ {x₁ = branch _ _ _} {x₂ = branch _ _ _} b₁≈b₂ bs₁≈bs₂)
    x₁∈ (inj₁ ≡b₁) x₁∉
    with
      Alpha-Br-∈
        b₁≈b₂
        (subst (_ ∈FV_) (cong (λ { (branch _ _ e) → e }) ≡b₁) x₁∈)
        (x₁∉ ∘
         subst (_ ∈_) (cong (λ { (branch _ xs _) → xs }) (sym ≡b₁)))
  … | x₂ , Rx₁x₂ , x₂∈ , x₂∉ =
    x₂ , Rx₁x₂ , _ , _ , _ , x₂∈ , inj₁ refl , x₂∉
  Alpha-Br-⋆-∈ (b₁≈b₂ ∷ bs₁≈bs₂) x₁∈ (inj₂ ∈bs₁) x₁∉ =
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

-- Substitution does not necessarily respect α-equivalence.

¬-subst-α :
  ¬ (∀ {x₁ x₂ e₁ e₂ e₁′ e₂′} →
     Alpha (_≡_ [ x₁ ∼ x₂ ]) e₁ e₂ →
     e₁′ ≈α e₂′ →
     e₁ [ x₁ ← e₁′ ] ≈α e₂ [ x₂ ← e₂′ ])
¬-subst-α subst-α =
  not-equal (subst-α e¹≈e² e′≈e′)
  where
  x¹ = V.name 0
  x² = V.name 1
  z  = V.name 2

  e¹ = lambda x¹ (var z)
  e² = lambda x² (var z)

  e′ = var x¹

  e¹≈e² : Alpha (_≡_ [ z ∼ z ]) e¹ e²
  e¹≈e² = lambda (cons (nil (var (inj₂
    ( V.distinct-codes→distinct-names (λ ())
    , V.distinct-codes→distinct-names (λ ())
    , inj₁ (refl , refl)
    )))))

  e′≈e′ : e′ ≈α e′
  e′≈e′ = refl-α

  not-equal : ¬ e¹ [ z ← e′ ] ≈α e² [ z ← e′ ]
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

-- TODO: Does substitution of closed terms respect α-equivalence? Does
-- the semantics respect α-equivalence for closed terms?
