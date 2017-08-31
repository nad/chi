------------------------------------------------------------------------
-- Definition of the size of an expression, along with some properties
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Size where

open import Equality.Propositional
open import Prelude hiding (const)

open import List equality-with-J
open import Nat equality-with-J

-- To simplify the development, let's work with actual natural numbers
-- as variables and constants (see
-- Atom.one-can-restrict-attention-to-χ-ℕ-atoms).

open import Atom

open import Chi            χ-ℕ-atoms
open import Combinators
open import Free-variables χ-ℕ-atoms
open import Termination    χ-ℕ-atoms

open χ-atoms χ-ℕ-atoms

------------------------------------------------------------------------
-- A definition

mutual

  -- The size of an expression.

  size : Exp → ℕ
  size (apply e₁ e₂) = 1 + size e₁ + size e₂
  size (lambda x e)  = 1 + size e
  size (case e bs)   = 1 + size e + size-B⋆ bs
  size (rec x e)     = 1 + size e
  size (var x)       = 1
  size (const c es)  = 1 + size-⋆ es

  size-B : Br → ℕ
  size-B (branch c xs e) = 1 + length xs + size e

  size-⋆ : List Exp → ℕ
  size-⋆ []       = 1
  size-⋆ (e ∷ es) = 1 + size e + size-⋆ es

  size-B⋆ : List Br → ℕ
  size-B⋆ []       = 1
  size-B⋆ (b ∷ bs) = 1 + size-B b + size-B⋆ bs

------------------------------------------------------------------------
-- Properties

-- Every expression has size at least one.

1≤size : ∀ e → 1 ≤ size e
1≤size (apply e₁ e₂) = suc≤suc (zero≤ _)
1≤size (lambda x e)  = suc≤suc (zero≤ _)
1≤size (case e bs)   = suc≤suc (zero≤ _)
1≤size (rec x e)     = suc≤suc (zero≤ _)
1≤size (var x)       = suc≤suc (zero≤ _)
1≤size (const c es)  = suc≤suc (zero≤ _)

1≤size-⋆ : ∀ es → 1 ≤ size-⋆ es
1≤size-⋆ []      = suc≤suc (zero≤ _)
1≤size-⋆ (_ ∷ _) = suc≤suc (zero≤ _)

1≤size-B⋆ : ∀ bs → 1 ≤ size-B⋆ bs
1≤size-B⋆ []      = suc≤suc (zero≤ _)
1≤size-B⋆ (_ ∷ _) = suc≤suc (zero≤ _)

-- Closed expressions have size at least two.

closed→2≤size : ∀ e → Closed e → 2 ≤ size e
closed→2≤size (apply e₁ e₂) cl =
  2                      ≤⟨ m≤m+n _ _ ⟩
  2 + size e₂            ≤⟨ (1 ∎≤) +-mono 1≤size e₁ +-mono (size e₂ ∎≤) ⟩∎
  1 + size e₁ + size e₂  ∎≤

closed→2≤size (lambda x e) cl =
  2           ≤⟨ (1 ∎≤) +-mono 1≤size e ⟩∎
  1 + size e  ∎≤

closed→2≤size (case e bs) cl =
  2                        ≤⟨ m≤m+n _ _ ⟩
  2 + size-B⋆ bs           ≤⟨ (1 ∎≤) +-mono 1≤size e +-mono (size-B⋆ bs ∎≤) ⟩∎
  1 + size e + size-B⋆ bs  ∎≤

closed→2≤size (rec x e) cl =
  2           ≤⟨ (1 ∎≤) +-mono 1≤size e ⟩∎
  1 + size e  ∎≤

closed→2≤size (var x) cl = ⊥-elim (cl x (λ ()) (var refl))

closed→2≤size (const c es) cl =
  2              ≤⟨ (1 ∎≤) +-mono 1≤size-⋆ es ⟩∎
  1 + size-⋆ es  ∎≤

-- Closed, non-terminating expressions of size two must have the form
-- "rec x = x" (for some x).

data Is-loop : Exp → Set where
  rec : ∀ {x y} → x ≡ y → Is-loop (rec x (var y))

closed-non-terminating-size≡2→loop :
  ∀ e → Closed e → ¬ Terminates e → size e ≡ 2 → Is-loop e
closed-non-terminating-size≡2→loop (rec x e) cl _ size≡2 with e
... | apply e₁ e₂ = ⊥-elim $ +≮ 1 (4                      ≤⟨ (2 ∎≤) +-mono 1≤size e₁ +-mono 1≤size e₂ ⟩
                                   2 + size e₁ + size e₂  ≡⟨ size≡2 ⟩≤
                                   2                      ∎≤)
... | lambda _ e′ = ⊥-elim $ +≮ 0 (3            ≤⟨ (2 ∎≤) +-mono 1≤size e′ ⟩
                                   2 + size e′  ≡⟨ size≡2 ⟩≤
                                   2            ∎≤)
... | case e′ bs  = ⊥-elim $ +≮ 0 (3                         ≤⟨ (2 ∎≤) +-mono 1≤size e′ +-mono zero≤ _ ⟩
                                   2 + size e′ + size-B⋆ bs  ≡⟨ size≡2 ⟩≤
                                   2                         ∎≤)
... | rec _ e′    = ⊥-elim $ +≮ 0 (3            ≤⟨ (2 ∎≤) +-mono 1≤size e′ ⟩
                                   2 + size e′  ≡⟨ size≡2 ⟩≤
                                   2            ∎≤)
... | const _ es  = ⊥-elim $ +≮ 0 (3              ≤⟨ (2 ∎≤) +-mono 1≤size-⋆ es ⟩
                                   2 + size-⋆ es  ≡⟨ size≡2 ⟩≤
                                   2              ∎≤)
... | var y with x V.≟ y
...   | yes x≡y = rec x≡y
...   | no  x≢y = ⊥-elim (cl y (λ ()) (rec (x≢y ∘ sym) (var refl)))

closed-non-terminating-size≡2→loop (apply e₁ e₂) _ _ size≡2 =
  ⊥-elim $ +≮ 0 (3                      ≤⟨ (1 ∎≤) +-mono 1≤size e₁ +-mono 1≤size e₂ ⟩
                 1 + size e₁ + size e₂  ≡⟨ size≡2 ⟩≤
                 2                      ∎≤)

closed-non-terminating-size≡2→loop (lambda x e) _ ¬⟶ _ =
  ⊥-elim (¬⟶ (_ , lambda))

closed-non-terminating-size≡2→loop (case e bs) _ _ size≡2 =
  ⊥-elim $ +≮ 0 (3                        ≤⟨ (1 ∎≤) +-mono 1≤size e +-mono 1≤size-B⋆ bs ⟩
                 1 + size e + size-B⋆ bs  ≡⟨ size≡2 ⟩≤
                 2                        ∎≤)

closed-non-terminating-size≡2→loop (var x) cl _ _ =
  ⊥-elim (cl x (λ ()) (var refl))

closed-non-terminating-size≡2→loop (const c []) _ ¬⟶ _ =
  ⊥-elim (¬⟶ (_ , const []))

closed-non-terminating-size≡2→loop (const c (e ∷ es)) _ _ size≡2 =
  ⊥-elim $ +≮ 1 (4                       ≤⟨ (2 ∎≤) +-mono 1≤size e +-mono 1≤size-⋆ es ⟩
                 2 + size e + size-⋆ es  ≡⟨ size≡2 ⟩≤
                 2                       ∎≤)

-- Closed, non-terminating expressions of minimal size must have the
-- form "rec x = x" (for some x).

minimal-closed-non-terminating→loop :
  let P = λ e → Closed e × ¬ Terminates e in
  ∀ e → P e → (∀ e′ → P e′ → size e ≤ size e′) → Is-loop e
minimal-closed-non-terminating→loop e (cl , ¬⟶) minimal =
  closed-non-terminating-size≡2→loop e cl ¬⟶ (
    ≤-antisymmetric
      (minimal loop (loop-closed , ¬loop⟶))
      (closed→2≤size e cl))
