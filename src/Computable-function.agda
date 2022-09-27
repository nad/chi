------------------------------------------------------------------------
-- Computable Agda functions
------------------------------------------------------------------------

open import Atom

module Computable-function (atoms : χ-atoms) where

open import Equality.Propositional.Cubical
open import Prelude

open import Bijection equality-with-J using (_↔_)
import Equivalence equality-with-J as Eq
open import Function-universe equality-with-J hiding (id; _∘_)
open import Injection equality-with-J using (Injective)

open import Chi            atoms
open import Coding         atoms
import Coding.Instances    atoms as Dummy
open import Computability  atoms hiding (_∘_)
open import Deterministic  atoms
open import Values         atoms

-- Computable (Agda) functions from a type to a set.

record Computable-function
         {a b} (A : Type a) (B : Type b) (B-set : Is-set B)
         ⦃ rA : Rep A Consts ⦄ ⦃ rB : Rep B Consts ⦄ :
         Type (a ⊔ b) where
  field
    function   : A → B
    computable : Computable (as-partial B-set function)

open Computable-function

-- An unfolding lemma for Computable-function.

Computable-function↔ :
  ∀ {a b} {A : Type a} {B : Type b} {B-set : Is-set B}
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
  ∀ {a b} {A : Type a} {B : Type b} {B-set : Is-set B}
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
    ∀ {a b} {A : Type a} {B : Type b} {B-set : Is-set B}
      ⦃ rA : Rep A Consts ⦄ ⦃ rB : Rep B Consts ⦄ →
    Rep (Computable-function A B B-set) Consts
  rep-Computable-function {A = A} {B = B} {B-set = B-set} = record
    { ⌜_⌝           = ⌜_⌝ ∘ proj₁ ∘ computable
    ; rep-injective = injective
    }
    where
    abstract
      injective :
        Injective {A = Computable-function A B B-set} {B = Consts}
          (⌜_⌝ ∘ proj₁ ∘ computable)
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
