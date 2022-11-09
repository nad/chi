------------------------------------------------------------------------
-- Some lemmas and definitions related to substitution
------------------------------------------------------------------------

open import Atom

module Substitution (atoms : χ-atoms) where

open import Equality.Propositional
open import Prelude hiding (const)

open import Bag-equivalence equality-with-J using (_∈_)
open import Sum equality-with-J

open import Chi atoms

open χ-atoms atoms

private
  variable
    c       : Const
    e e′ e″ : Exp
    x y     : Var
    xs      : List Var

-- Some simplification lemmas for the substitution functions.

var-step-≡ : x ≡ y → var y [ x ← e ] ≡ e
var-step-≡ {x = x} {y = y} x≡y with x V.≟ y
… | yes _  = refl
… | no x≢y = ⊥-elim (x≢y x≡y)

var-step-≢ : x ≢ y → var y [ x ← e ] ≡ var y
var-step-≢ {x = x} {y = y} x≢y with x V.≟ y
… | no _    = refl
… | yes x≡y = ⊥-elim (x≢y x≡y)

lambda-step-≡ : x ≡ y → lambda y e [ x ← e′ ] ≡ lambda y e
lambda-step-≡ {x = x} {y = y} x≡y with x V.≟ y
… | yes _  = refl
… | no x≢y = ⊥-elim (x≢y x≡y)

lambda-step-≢ :
  x ≢ y → lambda y e [ x ← e′ ] ≡ lambda y (e [ x ← e′ ])
lambda-step-≢ {x = x} {y = y} x≢y with x V.≟ y
… | no _    = refl
… | yes x≡y = ⊥-elim (x≢y x≡y)

rec-step-≡ : x ≡ y → rec y e [ x ← e′ ] ≡ rec y e
rec-step-≡ {x = x} {y = y} x≡y with x V.≟ y
… | yes _  = refl
… | no x≢y = ⊥-elim (x≢y x≡y)

rec-step-≢ :
  x ≢ y → rec y e [ x ← e′ ] ≡ rec y (e [ x ← e′ ])
rec-step-≢ {x = x} {y = y} x≢y with x V.≟ y
… | no _    = refl
… | yes x≡y = ⊥-elim (x≢y x≡y)

branch-step-∈ :
  x ∈ xs →
  branch c xs e [ x ← e′ ]B ≡ branch c xs e
branch-step-∈ {x = x} {xs = xs} x∈xs with V.member x xs
… | yes _   = refl
… | no x∉xs = ⊥-elim (x∉xs x∈xs)

branch-step-∉ :
  ¬ x ∈ xs →
  branch c xs e [ x ← e′ ]B ≡ branch c xs (e [ x ← e′ ])
branch-step-∉ {x = x} {xs = xs} x∉xs with V.member x xs
… | no _     = refl
… | yes x∈xs = ⊥-elim (x∉xs x∈xs)

-- A "fusion" lemma.

mutual

  fusion : ∀ e → e [ x ← e′ ] [ x ← e″ ] ≡ e [ x ← e′ [ x ← e″ ] ]
  fusion (apply e₁ e₂) =
    cong₂ apply (fusion e₁) (fusion e₂)

  fusion {x = x} {e′ = e′} {e″ = e″} (lambda y e) with x V.≟ y
  … | yes _ = refl
  … | no _  =
    lambda y (e [ x ← e′ ] [ x ← e″ ])  ≡⟨ cong (lambda _) $ fusion e ⟩∎
    lambda y (e [ x ← e′ [ x ← e″ ] ])  ∎

  fusion (case e bs) =
    cong₂ case (fusion e) (fusion-B⋆ bs)

  fusion {x = x} {e′ = e′} {e″ = e″} (rec y e) with x V.≟ y
  … | yes _ = refl
  … | no _  =
    rec y (e [ x ← e′ ] [ x ← e″ ])  ≡⟨ cong (rec _) $ fusion e ⟩∎
    rec y (e [ x ← e′ [ x ← e″ ] ])  ∎

  fusion {x = x} {e″ = e″} (var y) with x V.≟ y
  … | yes _  = refl
  … | no x≢y =
    var y [ x ← e″ ]  ≡⟨ var-step-≢ x≢y ⟩∎
    var y             ∎

  fusion (const c es) =
    cong (const c) (fusion-⋆ es)

  fusion-B :
    ∀ b → b [ x ← e′ ]B [ x ← e″ ]B ≡ b [ x ← e′ [ x ← e″ ] ]B
  fusion-B {x = x} {e′ = e′} {e″ = e″} (branch c xs e)
    with V.member x xs
  … | yes x∈xs =
    branch c xs e [ x ← e″ ]B  ≡⟨ branch-step-∈ x∈xs ⟩∎
    branch c xs e              ∎
  … | no x∉xs =
    branch c xs (e [ x ← e′ ]) [ x ← e″ ]B  ≡⟨ branch-step-∉ x∉xs ⟩
    branch c xs (e [ x ← e′ ] [ x ← e″ ])   ≡⟨ cong (branch _ _) $ fusion e ⟩∎
    branch c xs (e [ x ← e′ [ x ← e″ ] ])   ∎

  fusion-⋆ :
    ∀ es → es [ x ← e′ ]⋆ [ x ← e″ ]⋆ ≡ es [ x ← e′ [ x ← e″ ] ]⋆
  fusion-⋆ []       = refl
  fusion-⋆ (e ∷ es) = cong₂ _∷_ (fusion e) (fusion-⋆ es)

  fusion-B⋆ :
    ∀ bs → bs [ x ← e′ ]B⋆ [ x ← e″ ]B⋆ ≡ bs [ x ← e′ [ x ← e″ ] ]B⋆
  fusion-B⋆ []       = refl
  fusion-B⋆ (b ∷ bs) = cong₂ _∷_ (fusion-B b) (fusion-B⋆ bs)

-- The expression ⟨ ys , e ⟩[ x ← e′ ] is e if x is a member of ys,
-- and otherwise e [ x ← e′ ].

⟨_,_⟩[_←_] : List Var → Exp → Var → Exp → Exp
⟨ []     , e ⟩[ x ← e′ ] = e [ x ← e′ ]
⟨ y ∷ ys , e ⟩[ x ← e′ ] =
  if x V.≟ y then e else ⟨ ys , e ⟩[ x ← e′ ]

⟨,⟩[←]≡ :
  ∀ ys →
  ⟨ ys , e ⟩[ x ← e′ ] ≡
  if V.member x ys then e else e [ x ← e′ ]
⟨,⟩[←]≡ [] =
  refl
⟨,⟩[←]≡ {e = e} {x = x} {e′ = e′} (y ∷ ys) with x V.≟ y
… | yes _   = refl
… | no  x≢y =
  ⟨ ys , e ⟩[ x ← e′ ]                           ≡⟨ ⟨,⟩[←]≡ ys ⟩

  if V.member x ys then e else e [ x ← e′ ]      ≡⟨ sym $ if-⊎-map-then-else (V.member x ys) ⟩∎

  if case V.member x ys of ⊎-map inj₂ [ x≢y ,_]
  then e else e [ x ← e′ ]                       ∎
