------------------------------------------------------------------------
-- A tactic that can "remove" applications of substitutions to closed
-- expressions
------------------------------------------------------------------------

module Free-variables.Remove-substs where

open import Equality.Propositional
open import Prelude hiding (const)
open import Tactic.By.Propositional using (make-cong)

open import List equality-with-J as L
open import Monad equality-with-J
open import TC-monad equality-with-J hiding (Type)

-- The tactic uses actual natural numbers as variables and constants.

open import Atom
import Chi
import Coding
open import Coding.Instances.Nat

open        Chi            χ-ℕ-atoms
open        Coding         χ-ℕ-atoms
open import Free-variables χ-ℕ-atoms
open import Reasoning      χ-ℕ-atoms
open import Values         χ-ℕ-atoms

private variable
  a             : Level
  A             : Type a
  e e′ e″ e₁ e₂ : Exp
  x y           : A

------------------------------------------------------------------------
-- The tactic

private

  -- A lemma used in some proofs constructed by "proof".

  subst-cong₁ : ∀ x e → e₁ ≡ e₂ → e₁ [ x ← e ] ≡ e₂ [ x ← e ]
  subst-cong₁ _ _ = cong _[ _ ← _ ]

  -- Given the left-hand side of an equality statement an attempt is
  -- made to construct a proof showing that the left-hand side is
  -- equal to the right-hand side.

  proof : List (Name × Term) → Term → TC Term
  proof closed t = the-proof ⟨$⟩ term t
    where
    -- Different kinds of right-hand sides.

    data RHS : Type where
      -- Applications of ⌜_⌝. The Term is the argument of ⌜_⌝.
      rep-rhs : Term → RHS
      -- Closed terms. The Term is a proof showing that the right-hand
      -- side is closed.
      closed-rhs : Term → RHS

    -- Different kinds of attempted proofs.

    data Proof : Type where
      -- A trivial proof attempt: just reflexivity.
      trivial : Proof
      -- A non-trivial proof attempt.
      --
      -- If the constructed proof is (known/intended to be) of the
      -- form "_ ≡ rhs", then the second argument is just rhs.
      non-trivial : Term → Maybe RHS → Proof

    the-proof : Proof → Term
    the-proof trivial           = con (quote refl) []
    the-proof (non-trivial p _) = p

    mutual

      term : Term → TC Proof

      -- Special cases for applications of _[_←_].
      term (def (quote _[_←_])
              (varg (def (quote Coding.Rep.⌜_⌝)
                       (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ varg e₁ ∷ [])) ∷
               varg _ ∷ varg _ ∷ [])) =
        subst-rep-proof e₁
      term (def (quote Chi._[_←_])
              (_ ∷ varg (def (quote Coding.Rep.⌜_⌝)
                           (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ varg e₁ ∷ [])) ∷
               varg _ ∷ varg _ ∷ [])) =
        subst-rep-proof e₁
      term (def f@(quote _[_←_])
              (varg e₁@(def (quote _[_←_]) _) ∷
               varg x ∷ varg e₂ ∷ [])) =
        subst-subst-proof f e₁ x e₂
      term (def f@(quote Chi._[_←_])
              (_ ∷ varg e₁@(def (quote _[_←_]) _) ∷
               varg x ∷ varg e₂ ∷ [])) =
        subst-subst-proof f e₁ x e₂
      term (def f@(quote _[_←_])
              (varg e₁@(def (quote Chi._[_←_]) _) ∷
               varg x ∷ varg e₂ ∷ [])) =
        subst-subst-proof f e₁ x e₂
      term (def f@(quote Chi._[_←_])
              (_ ∷ varg e₁@(def (quote Chi._[_←_]) _) ∷
               varg x ∷ varg e₂ ∷ [])) =
        subst-subst-proof f e₁ x e₂
      term (def (quote _[_←_])
              (varg (def e₁ []) ∷ varg x ∷ varg e₂ ∷ [])) =
        subst-def-proof e₁ x e₂
      term (def (quote Chi._[_←_])
              (_ ∷ varg (def e₁ []) ∷ varg x ∷ varg e₂ ∷ [])) =
        subst-def-proof e₁ x e₂

      -- General cases for applications.
      term (con c ts) = try-cong (con c []) ts
      term (def f ts) = try-cong (def f []) ts
      term (var x ts) = try-cong (var x []) ts

      term (meta m _) = blockOnMeta m
      term _          = return trivial

      subst-rep-proof : Term → TC Proof
      subst-rep-proof e₁ = return $
        non-trivial
          (def (quote subst-rep) (varg e₁ ∷ []))
          (just (rep-rhs e₁))

      subst-subst-proof :
        Name → Term → Term → Term → TC Proof
      subst-subst-proof f e₁ x e₂ = do
        p₁ ← term e₁
        return $ case p₁ of λ where
          trivial             → trivial
          (non-trivial p₁ e₁) → flip non-trivial e₁ $
            let p₁ = def (quote subst-cong₁)
                       (varg x ∷ varg e₂ ∷ varg p₁ ∷ [])
            in case e₁ of λ where
              nothing             → p₁
              (just (rep-rhs e₁)) →
                def (quote trans)
                  (varg p₁ ∷
                   varg (def (quote subst-rep) (varg e₁ ∷ [])) ∷
                   [])
              (just (closed-rhs cl)) →
                def (quote trans)
                  (varg p₁ ∷
                   varg (def (quote subst-closed)
                           (varg x ∷ varg e₂ ∷ varg cl ∷ [])) ∷
                   [])

      subst-def-proof : Name → Term → Term → TC Proof
      subst-def-proof e₁ x e₂ =
        return $ case lookup eq-Name e₁ closed of λ where
          nothing   → trivial
          (just cl) → non-trivial
            (def (quote subst-closed) (varg x ∷ varg e₂ ∷ varg cl ∷ []))
            (just (closed-rhs cl))

      try-cong : Term → List (Arg Term) → TC Proof
      try-cong f [] =
        -- Reflexivity should work fine if there are no arguments.
        return trivial
      try-cong f ts =
        case non-default-modality-after-first-visible-arg of λ where
          true  → return trivial
          false → do
            (ts , triv) ← args ts
            case triv of λ where
              true  → return trivial
              false → do
                cong-proof ← make-cong visible-args
                return
                  (non-trivial (def cong-proof (varg f ∷ ts)) nothing)
        where
        non-default-modality-after-first-visible-arg =
          skip-prefix ts
          where
          skip-prefix : List (Arg Term) → Bool
          skip-prefix ts@(arg (arg-info visible _) _ ∷ _) =
            foldr _∨_ false $
            flip L.map ts λ where
              (arg (arg-info v m) _) →
                not (eq-Modality m (modality relevant quantity-ω))
          skip-prefix (_ ∷ ts) = skip-prefix ts
          skip-prefix []       = true

        visible-args = length $ flip filter ts λ where
          (arg (arg-info v _) _) → eq-Visibility v visible

      -- The returned boolean is true iff the proofs constructed for
      -- all arguments are trivial.

      args : List (Arg Term) → TC (List (Arg Term) × Bool)
      args [] =
        return ([] , true)
      args (arg i@(arg-info visible _) t ∷ ts) = do
        p           ← term t
        (ps , triv) ← args ts
        return $ (arg i (the-proof p) ∷ ps ,_) $
          case p , triv of λ where
            (trivial , true) → true
            _                → false
      args (_ ∷ ts) =
        -- Arguments that are not visible are ignored.
        args ts

  -- Checks that the assumptions are plain names and returns the names
  -- along with the quoted proofs.

  process-closed :
    List (∃ λ (e : Exp) → Closed e) → TC (List (Name × Term))
  process-closed []               = return []
  process-closed ((e , c) ∷ rest) = do
    e ← quoteTC e
    c ← quoteTC c
    case e of λ where
      (def f []) → do
        rest ← process-closed rest
        return ((f , c) ∷ rest)
      _ → typeError $
        termErr e ∷ strErr " is not the name of a definition" ∷ []

  -- A function used to implement remove-substs.

  remove-substs-tactic : List (∃ λ (e : Exp) → Closed e) → Term → TC ⊤
  remove-substs-tactic closed goal =
    inferType goal >>= reduce >>= λ where
      (def (quote _≡_) (_ ∷ _ ∷ arg _ e ∷ _ ∷ [])) → do
        closed ← process-closed closed
        t      ← proof closed e
        debugPrint "remove-substs" 5 $
          strErr "The macro remove-substs constructed the following " ∷
          strErr "proof term:\n" ∷
          strErr "  " ∷ termErr t ∷ []
        unify goal t
      _ → typeError $
        termErr goal ∷ strErr " is not an equality type" ∷ []

macro

  -- A tactic that tries to "remove" applications of substitutions to
  -- closed expressions. The tactic knows that Coding.rep-as-Exp
  -- returns closed terms, and one can provide the tactic with
  -- information about names standing for closed terms.
  --
  -- The tactic can for instance be used to prove the following goal
  -- (where e has type Exp):
  --
  --   Exp.const 12 (⌜ e ⌝ [ x ← e′ ] ∷ []) ≡ Exp.const 12 (⌜ e ⌝ ∷ [])
  --
  -- The tactic does not look at the right-hand side, that side is
  -- assumed to have the right form.
  --
  -- Given the information that e is closed the tactic can also be
  -- used to prove the following goal:
  --
  --   Exp.const 12 (e [ x ← e′ ] ∷ []) ≡ Exp.const 12 (e ∷ [])
  --
  -- The tactic's first argument is a list of pairs of expressions and
  -- proofs that the expressions are closed. The expressions must be
  -- given as names of definitions.

  remove-substs :
    List (∃ λ (e : Exp) → Closed e) → Term → TC ⊤
  remove-substs closed goal = remove-substs-tactic closed goal

------------------------------------------------------------------------
-- Unit tests

private

  _ : Exp.rec 0 (var 0) ≡ rec 0 (var 0)
  _ = remove-substs []

  _ : Exp.const 12 (⌜ e ⌝ [ x ← e′ ] ∷ []) ≡ Exp.const 12 (⌜ e ⌝ ∷ [])
  _ = remove-substs []

  _ : Exp.const 12 (⌜ e ⌝ [ x ← e′ ] [ y ← e″ ] ∷ []) ≡
      Exp.const 12 (⌜ e ⌝ ∷ [])
  _ = remove-substs []

  [id] : Exp
  [id] = lambda 0 (var 0)

  [id]-is-closed : Closed [id]
  [id]-is-closed = from-⊎ $ closed? [id]

  _ : Exp.const 12 ([id] [ x ← e′ ] ∷ []) ≡ Exp.const 12 ([id] ∷ [])
  _ = remove-substs (([id] , [id]-is-closed) ∷ [])

  _ : Exp.const 12 ([id] [ x ← e′ ] [ y ← e″ ] ∷ []) ≡
      Exp.const 12 ([id] ∷ [])
  _ = remove-substs (([id] , [id]-is-closed) ∷ [])

  _ : (n : ℕ) → const 3 (⌜ n ⌝ ∷ []) ⇓ const 3 (⌜ n ⌝ ∷ [])
  _ = λ n →
    const 3 (⌜ n ⌝ ∷ [])                     ≡⟨ sym $ remove-substs [] ⟩⟶
    const 3 (⌜ n ⌝ [ 0 ← const 0 [] ] ∷ [])  ≡⟨ remove-substs [] ⟩⟶
    const 3 (⌜ n ⌝ ∷ [])                     ■⟨ const _ (rep-value n ∷ []) ⟩

  f : Exp → Exp
  f e = const 7 (e ∷ [])

  _ : f (⌜ e ⌝ [ x ← e′ ]) ≡ f ⌜ e ⌝
  _ = remove-substs []

  _ : (f : (n : ℕ) → ∃ λ (m : ℕ) → m ≡ n) (n : ℕ) →
      Exp.const (proj₁ (f n)) (⌜ e ⌝ [ x ← e′ ] ∷ []) ≡
      const (proj₁ (f n)) (⌜ e ⌝ ∷ [])
  _ = λ _ _ → remove-substs []
