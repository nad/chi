------------------------------------------------------------------------
-- A self-interpreter
------------------------------------------------------------------------

module Self-interpreter where

open import Equality.Propositional
open import Prelude hiding (const)
open import Tactic.By.Propositional

open import Equality.Decision-procedures equality-with-J
open import Function-universe equality-with-J using ($⟨_⟩_)
open import Nat equality-with-J as Nat
  using (_≤_; _<_; _∎≤; step-≤; step-≡≤; finally-≤)

-- To simplify the development, let's work with actual natural numbers
-- as variables and constants (see
-- Atom.one-can-restrict-attention-to-χ-ℕ-atoms).

open import Atom

open import Cancellation    χ-ℕ-atoms
open import Chi             χ-ℕ-atoms
open import Coding          χ-ℕ-atoms
open import Compatibility   χ-ℕ-atoms
open import Computability   χ-ℕ-atoms hiding (_∘_)
open import Constants       χ-ℕ-atoms
open import Derivation-size χ-ℕ-atoms
open import Free-variables  χ-ℕ-atoms hiding (case-body)
open import Reasoning       χ-ℕ-atoms
open import Termination     χ-ℕ-atoms
open import Values          χ-ℕ-atoms

open import Coding.Instances.Nat
open import Free-variables.Remove-substs
open import Internal-lookup
open import Internal-substitution

open χ-atoms χ-ℕ-atoms using (Var; Const)

private

  -- A list of branches used in the implementation of map.

  map-branches : Exp → List Br
  map-branches f =
    branch c-nil [] (const c-nil []) ∷
    branch c-cons (v-x ∷ v-xs ∷ []) (
      const c-cons (apply f (var v-x) ∷
                    apply (var v-map) (var v-xs) ∷
                    [])) ∷
    []

  -- A non-abstract variant of map.

  map′ : Exp → Exp
  map′ f = rec v-map (lambda v-xs (case (var v-xs) (map-branches f)))

abstract

  -- A map function. The application of map to the function is done at
  -- the meta-level in order to simplify proofs.

  map : Exp → Exp
  map = map′

  -- If f is closed, then map f is closed.

  map-closed : ∀ {f} → Closed f → Closed (map f)
  map-closed {f = f} cl =
    Closed′-closed-under-rec $
    Closed′-closed-under-lambda $
    Closed′-closed-under-case
      (from-⊎ $ closed′? (var v-xs) (v-xs ∷ v-map ∷ []))
      (λ where
         _ (inj₁ refl) →
           from-⊎ $ closed′? (const c-nil []) (v-xs ∷ v-map ∷ [])
         _ (inj₂ (inj₁ refl)) →
           Closed′-closed-under-const λ where
             .(apply f (var v-x)) (inj₁ refl) →
               Closed′-closed-under-apply
                 (Closed→Closed′ cl)
                 (λ where
                    .v-x v-x∉xs (var refl) →
                      v-x∉xs (inj₁ refl))
             .(apply (var v-map) (var v-xs)) (inj₂ (inj₁ refl)) →
               from-⊎ $
               closed′? (apply (var v-map) (var v-xs))
                 (v-x ∷ v-xs ∷ v-xs ∷ v-map ∷ []))

private

  -- Auxiliary definitions used in the implementation of eval.

  apply-branches : List Br
  apply-branches =
    branch c-lambda (v-x ∷ v-e ∷ []) (
      apply (var v-eval) (
        apply (apply (apply internal-subst (var v-x))
                 (apply (var v-eval) (var v-e₂)))
          (var v-e))) ∷
    []

  case-body : Exp
  case-body =
    case (apply (apply internal-lookup (var v-c)) (var v-bs)) (
      branch c-branch (v-underscore ∷ v-xs ∷ v-e ∷ []) (
        apply (var v-eval) (
          apply (apply (apply internal-substs (var v-xs))
                   (var v-es))
            (var v-e))) ∷
      [])

  branches : List Br
  branches =
    branch c-apply (v-e₁ ∷ v-e₂ ∷ []) (
      case (apply (var v-eval) (var v-e₁)) apply-branches) ∷
    branch c-case (v-e ∷ v-bs ∷ []) (
      case (apply (var v-eval) (var v-e)) (
        branch c-const (v-c ∷ v-es ∷ []) case-body ∷
        [])) ∷
    branch c-rec (v-x ∷ v-e ∷ []) (
      apply (var v-eval) (
        apply (apply (apply internal-subst (var v-x))
                 (const c-rec (var v-x ∷ var v-e ∷ [])))
          (var v-e))) ∷
    branch c-lambda (v-x ∷ v-e ∷ []) (
      const c-lambda (var v-x ∷ var v-e ∷ [])) ∷
    branch c-const (v-c ∷ v-es ∷ []) (
      const c-const (var v-c ∷
                     apply (map′ (var v-eval)) (var v-es) ∷
                     [])) ∷
    []

  eval′ : Exp
  eval′ = rec v-eval (lambda v-p (case (var v-p) branches))

abstract

  -- The self-interpreter.

  eval : Exp
  eval = eval′

  -- The self-interpreter is closed.

  eval-closed : Closed eval
  eval-closed = from-⊎ (closed? eval)

-- The self-interpreter is correctly implemented (part one).

mutual abstract

  eval-correct₁ :
    ∀ {e v} →
    e ⇓ v → apply eval ⌜ e ⌝ ⇓ ⌜ v ⌝
  eval-correct₁ (lambda {x = x} {e = e}) =
    apply eval ⌜ lambda x e ⌝                                     ⟶⟨ apply (rec lambda) (rep⇓rep (lambda x e)) ⟩
    case ⌜ lambda x e ⌝ (branches [ v-eval ← eval ]B⋆)            ⟶⟨ case (rep⇓rep (lambda x e))
                                                                       (there (λ ()) (there (λ ()) (there (λ ()) here))) (∷ ∷ []) ⟩
    const c-lambda (⌜ x ⌝ ∷ ⌜ e ⌝ [ v-x ← ⌜ x ⌝ ] ∷ [])           ≡⟨ remove-substs [] ⟩⟶
    const c-lambda (⌜ x ⌝ ∷ ⌜ e ⌝ ∷ [])                           ≡⟨⟩⟶
    ⌜ lambda x e ⌝                                                ■⟨ rep-value (lambda x e) ⟩

  eval-correct₁ (apply {e₁ = e₁} {e₂ = e₂} {x = x} {e = e}
                       {v₂ = v₂} {v = v} p q r) =
    apply eval ⌜ apply e₁ e₂ ⌝                                         ⟶⟨ apply (rec lambda) (rep⇓rep (apply e₁ e₂)) ⟩

    case ⌜ apply e₁ e₂ ⌝ (branches [ v-eval ← eval ]B⋆)                ⟶⟨ case (rep⇓rep (apply e₁ e₂)) here (∷ ∷ []) ⟩

    case (apply eval ⌜ e₁ ⌝) (
      apply-branches [ v-eval ← eval ]B⋆ [ v-e₂ ← ⌜ e₂ ⌝ ]B⋆
        [ v-e₁ ← ⌜ e₁ ⌝ ]B⋆)                                           ⟶⟨ []⇓ (case ∙) (eval-correct₁ p) ⟩

    case ⌜ lambda x e ⌝ (
      apply-branches [ v-eval ← eval ]B⋆ [ v-e₂ ← ⌜ e₂ ⌝ ]B⋆
        [ v-e₁ ← ⌜ e₁ ⌝ ]B⋆)                                           ⟶⟨ case (rep⇓rep (lambda x e)) here (∷ ∷ []) ⟩

    apply eval
      (apply (apply (apply internal-subst ⌜ x ⌝)
                (apply eval (⌜ e₂ ⌝ [ v-e₁ ← ⌜ e₁ ⌝ ] [ v-e ← ⌜ e ⌝ ]
                               [ v-x ← ⌜ x ⌝ ])))
         (⌜ e ⌝ [ v-x ← ⌜ x ⌝ ]))                                      ≡⟨ remove-substs [] ⟩⟶

    apply eval
      (apply (apply (apply internal-subst ⌜ x ⌝) (apply eval ⌜ e₂ ⌝))
         ⌜ e ⌝)                                                        ⟶⟨ []⇓ (apply→ apply← apply→ ∙) (eval-correct₁ q) ⟩

    apply eval
      (apply (apply (apply internal-subst ⌜ x ⌝) ⌜ v₂ ⌝) ⌜ e ⌝)        ⟶⟨ []⇓ (apply→ ∙) internal-subst-correct₁ ⟩

    apply eval ⌜ e [ x ← v₂ ] ⌝                                        ⇓⟨ eval-correct₁ r ⟩■

    ⌜ v ⌝

  eval-correct₁ (rec {x = x} {e = e} {v = v} p) =
    apply eval ⌜ rec x e ⌝                                            ⟶⟨ apply (rec lambda) (rep⇓rep (rec x e)) ⟩

    case ⌜ rec x e ⌝ (branches [ v-eval ← eval ]B⋆)                   ⟶⟨ case (rep⇓rep (rec x e))
                                                                           (there (λ ()) (there (λ ()) here)) (∷ ∷ []) ⟩
    apply eval
      (apply (apply (apply internal-subst ⌜ x ⌝)
                (const c-rec (⌜ x ⌝ ∷ ⌜ e ⌝ [ v-x ← ⌜ x ⌝ ] ∷ [])))
         (⌜ e ⌝ [ v-x ← ⌜ x ⌝ ]))                                     ≡⟨ remove-substs [] ⟩⟶

    apply eval
      (apply (apply (apply internal-subst ⌜ x ⌝)
                (const c-rec (⌜ x ⌝ ∷ ⌜ e ⌝ ∷ [])))
         ⌜ e ⌝)                                                       ≡⟨⟩⟶

    apply eval
      (apply (apply (apply internal-subst ⌜ x ⌝) ⌜ rec x e ⌝) ⌜ e ⌝)  ⟶⟨ []⇓ (apply→ ∙) internal-subst-correct₁ ⟩

    apply eval ⌜ e [ x ← rec x e ] ⌝                                  ⇓⟨ eval-correct₁ p ⟩■

    ⌜ v ⌝

  eval-correct₁ (const {c = c} {es = es} {vs = vs} ps) =
    apply eval ⌜ const c es ⌝                                   ⟶⟨ apply (rec lambda) (rep⇓rep (const c es)) ⟩

    case ⌜ const c es ⌝ (branches [ v-eval ← eval ]B⋆)          ⟶⟨ case (rep⇓rep (const c es))
                                                                     (there (λ ()) (there (λ ()) (there (λ ()) (there (λ ()) here))))
                                                                     (∷ ∷ []) ⟩
    const c-const
      (⌜ c ⌝ ∷ apply (map eval) (⌜ es ⌝ [ v-c ← ⌜ c ⌝ ]) ∷ [])  ≡⟨ remove-substs [] ⟩⟶

    const c-const (⌜ c ⌝ ∷ apply (map eval) ⌜ es ⌝ ∷ [])        ⇓⟨ const (rep⇓rep c ∷ map-eval-correct₁ ps ∷ []) ⟩■

    const c-const (⌜ c ⌝ ∷ ⌜ vs ⌝ ∷ [])

  eval-correct₁
    (case {e = e} {bs = bs} {c = c} {es = es} {xs = xs} {e′ = e′}
          {e″ = e″} {v = v} p q r s) =
    apply eval ⌜ case e bs ⌝                                        ⟶⟨ apply (rec lambda) (rep⇓rep (case e bs)) ⟩

    case ⌜ case e bs ⌝ (branches [ v-eval ← eval ]B⋆)               ⟶⟨ case (rep⇓rep (case e bs)) (there (λ ()) here) (∷ ∷ []) ⟩

    case (apply eval ⌜ e ⌝) (
      branch c-const (v-c ∷ v-es ∷ []) (
        case-body [ v-eval ← eval ] [ v-bs ← ⌜ bs ⌝ ]
          [ v-e ← ⌜ e ⌝ ]) ∷
      [])                                                           ⟶⟨ case (eval-correct₁ p) here (∷ ∷ []) ⟩

    case-body [ v-eval ← eval ] [ v-bs ← ⌜ bs ⌝ ] [ v-e ← ⌜ e ⌝ ]
      [ v-es ← ⌜ es ⌝ ] [ v-c ← ⌜ c ⌝ ]                             ≡⟨⟩⟶

    case (apply (apply internal-lookup ⌜ c ⌝)
            (⌜ bs ⌝ [ v-e ← ⌜ e ⌝ ] [ v-es ← ⌜ es ⌝ ]
               [ v-c ← ⌜ c ⌝ ])) (
      branch c-branch (v-underscore ∷ v-xs ∷ v-e ∷ []) (
        apply eval
          (apply (apply (apply internal-substs (var v-xs))
                    (⌜ es ⌝ [ v-c ← ⌜ c ⌝ ]))
             (var v-e))) ∷
      [])                                                           ≡⟨ remove-substs [] ⟩⟶

    case (apply (apply internal-lookup ⌜ c ⌝) ⌜ bs ⌝) (
      branch c-branch (v-underscore ∷ v-xs ∷ v-e ∷ []) (
        apply eval
          (apply (apply (apply internal-substs (var v-xs)) ⌜ es ⌝)
             (var v-e))) ∷
      [])                                                           ⟶⟨ []⇓ (case ∙) (internal-lookup-correct₁ q) ⟩

    case ⌜ branch c xs e′ ⌝ (
      branch c-branch (v-underscore ∷ v-xs ∷ v-e ∷ []) (
        apply eval
          (apply (apply (apply internal-substs (var v-xs)) ⌜ es ⌝)
             (var v-e))) ∷
      [])                                                           ⟶⟨ case (rep⇓rep (branch c xs e′)) here (∷ ∷ ∷ []) ⟩

    apply eval
      (apply (apply (apply internal-substs
                       (⌜ xs ⌝ [ v-underscore ← ⌜ c ⌝ ]))
                (⌜ es ⌝ [ v-e ← ⌜ e′ ⌝ ] [ v-xs ← ⌜ xs ⌝ ]
                   [ v-underscore ← ⌜ c ⌝ ]))
         (⌜ e′ ⌝ [ v-xs ← ⌜ xs ⌝ ] [ v-underscore ← ⌜ c ⌝ ]))       ≡⟨ remove-substs [] ⟩⟶

    apply eval
      (apply (apply (apply internal-substs ⌜ xs ⌝) ⌜ es ⌝) ⌜ e′ ⌝)  ⟶⟨ []⇓ (apply→ ∙) (internal-substs-correct₁ r) ⟩

    apply eval ⌜ e″ ⌝                                               ⇓⟨ eval-correct₁ s ⟩■

    ⌜ v ⌝

  map-eval-correct₁ :
    ∀ {es vs} →
    es ⇓⋆ vs → apply (map eval) ⌜ es ⌝ ⇓ ⌜ vs ⌝
  map-eval-correct₁ {es = es} {vs = vs} ps =
    apply (map eval) ⌜ es ⌝                                 ⟶⟨ apply (rec lambda) (rep⇓rep es) ⟩
    case ⌜ es ⌝ (map-branches eval [ v-map ← map eval ]B⋆)  ⇓⟨ lemma ps ⟩■
    ⌜ vs ⌝
    where
    lemma :
      ∀ {es vs} →
      es ⇓⋆ vs →
      case ⌜ es ⌝ (map-branches eval [ v-map ← map eval ]B⋆) ⇓ ⌜ vs ⌝
    lemma [] =
      case ⌜ [] ⦂ List Exp ⌝
        (map-branches eval [ v-map ← map eval ]B⋆)  ⇓⟨ case (rep⇓rep ([] ⦂ List Exp)) here [] (const []) ⟩■

      ⌜ [] ⦂ List Exp ⌝
    lemma {es = e ∷ es} {vs = v ∷ vs} (p ∷ ps) =
      case ⌜ e ∷ es ⌝ (map-branches eval [ v-map ← map eval ]B⋆)      ⟶⟨ case (rep⇓rep (e ∷ es)) (there (λ ()) here) (∷ ∷ []) ⟩

      const c-cons (
        apply eval ⌜ e ⌝ ∷
        apply (map eval) (⌜ es ⌝ [ v-x ← ⌜ e ⌝ ]) ∷
        [])                                                           ≡⟨ remove-substs [] ⟩⟶

      const c-cons (apply eval ⌜ e ⌝ ∷ apply (map eval) ⌜ es ⌝ ∷ [])  ⇓⟨ const (eval-correct₁ p ∷ map-eval-correct₁ ps ∷ []) ⟩■

      ⌜ v ∷ vs ⌝

private

  -- Definitions used in eval-correct₂ and map-eval-correct₂.

  -- The main proof uses well-founded induction on sizes of
  -- derivations.

  P : ℕ → Type
  P n =
    ∀ e {v} (p : apply eval′ ⌜ e ⌝ ⇓ v) → size p ≡ n →
    ∃ λ v′ → e ⇓ v′ × v ≡ ⌜ v′ ⌝

  -- The following lemma uses induction on the structure of the list
  -- es.

  map-lemma :
    ∀ n (ih : ∀ {m} → m < n → P m) es {v}
    (p : apply (map′ eval′) ⌜ es ⌝ ⇓ v) → size p ≤ n →
    ∃ λ vs → es ⇓⋆ vs × v ≡ ⌜ vs ⌝
  map-lemma _ _ []
    (apply (rec lambda) (const [])
       (case (const []) here [] (const [])))
    _ =
    [] , [] , refl

  map-lemma _ _ []
    (apply (rec lambda) (const [])
       (case (const []) (there n≢n _) _ _)) =
    ⊥-elim $ n≢n refl

  map-lemma n ih (e ∷ es)
    (apply (rec lambda)
       q₁@(const (_∷_ {v = v₁} p₁ (_∷_ {v = v₂} p₂ [])))
       (case q₂@(const (_∷_ {v = v₃} p₃ (_∷_ {v = v₄} p₄ [])))
          (there _ here) (∷ ∷ [])
          (const (_∷_ {v = v₅} p₅ (_∷_ {v = v₆} p₆ [])))))
    size≤n =
    let v  , e⇓  , ≡⌜v⌝  = lemma₁
        vs , es⇓ , ≡⌜vs⌝ = lemma₂
    in
      v ∷ vs
    , e⇓ ∷ es⇓
    , (const c-cons (v₅ ∷ v₆ ∷ [])  ≡⟨ cong₂ (λ v₅ v₆ → Exp.const c-cons (v₅ ∷ v₆ ∷ [])) ≡⌜v⌝ ≡⌜vs⌝ ⟩∎
       ⌜ v ∷ vs ⌝                   ∎)
    where
    ⌜e⌝⇓ =
      ⌜ e ⌝  ⇓⟨ p₁ ⟩
      v₁     ⇓⟨ p₃ ⟩■
      v₃

    ⌜es⌝⇓ =
      ⌜ es ⌝  ⇓⟨ p₂ ⟩
      v₂      ⇓⟨ p₄ ⟩■
      v₄

    ⌜es⌝≡ : ⌜ es ⌝ ≡ v₄
    ⌜es⌝≡ = rep⇓≡rep es ⌜es⌝⇓

    v₄-closed : Closed v₄
    v₄-closed =      $⟨ rep-closed es ⟩
      Closed ⌜ es ⌝  →⟨ subst Closed ⌜es⌝≡ ⟩□
      Closed v₄      □

    lem₁ =
      Exp.apply eval′ ⟨ ⌜ e ⌝ ⟩  ≡⟨ ⟨by⟩ (rep⇓≡rep e ⌜e⌝⇓) ⟩∎
      apply eval′ v₃             ∎

    lemma₁ : ∃ λ v → e ⇓ v × v₅ ≡ ⌜ v ⌝
    lemma₁ = ih
      (1 + size (_ ≡⟨ lem₁ ⟩⟶ _ ⇓⟨ p₅ ⟩■ _)                         ≡⟨ cong suc $ size-≡⟨⟩⟶ lem₁ ⟩≤
       1 + size p₅                                                  ≤⟨ Nat.suc≤suc $
                                                                       Nat.≤-trans (Nat.m≤n+m _ 1) $
                                                                       Nat.≤-trans (Nat.m≤m+n _ (size p₆ + 0)) $
                                                                       Nat.≤-trans (Nat.m≤n+m _ (1 + size q₂)) $
                                                                       Nat.m≤n+m _ (2 + size q₁) ⟩
       3 + size q₁ + (1 + size q₂ + (1 + size p₅ + (size p₆ + 0)))  ≤⟨ size≤n ⟩∎
       n                                                            ∎≤)
      e
      (apply eval′ ⌜ e ⌝  ≡⟨ lem₁ ⟩⟶
       apply eval′ v₃     ⇓⟨ p₅ ⟩■
       v₅)
      refl

    lem₂ =
      Exp.apply (map′ eval′) ⟨ ⌜ es ⌝ ⟩     ≡⟨ ⟨by⟩ ⌜es⌝≡ ⟩
      Exp.apply (map′ eval′) v₄             ≡⟨ sym $ remove-substs ((v₄ , v₄-closed) ∷ []) ⟩∎
      apply (map′ eval′) (v₄ [ v-x ← v₃ ])  ∎

    lemma₂ : ∃ λ vs → es ⇓⋆ vs × v₆ ≡ ⌜ vs ⌝
    lemma₂ = map-lemma n ih es
      (apply (map′ eval′) ⌜ es ⌝             ≡⟨ lem₂ ⟩⟶
       apply (map′ eval′) (v₄ [ v-x ← v₃ ])  ⇓⟨ p₆ ⟩■
       v₆)
      (size (_ ≡⟨ lem₂ ⟩⟶ _ ⇓⟨ p₆ ⟩■ _)                             ≡⟨ size-≡⟨⟩⟶ lem₂ ⟩≤
       size p₆                                                      ≤⟨ Nat.≤-trans (Nat.m≤m+n _ 0) $
                                                                       Nat.≤-trans (Nat.m≤n+m _ (1 + size p₅)) $
                                                                       Nat.≤-trans (Nat.m≤n+m _ (1 + size q₂)) $
                                                                       Nat.m≤n+m _ (3 + size q₁) ⟩
       3 + size q₁ + (1 + size q₂ + (1 + size p₅ + (size p₆ + 0)))  ≤⟨ size≤n ⟩∎
       n                                                            ∎≤)

  -- The main lemma.

  eval-correct₂′ :
    ∀ n (ih : ∀ {m} → m < n → P m) e {v}
    (p : apply eval′ ⌜ e ⌝ ⇓ v) → size p ≡ n →
    ∃ λ v′ → e ⇓ v′ × v ≡ ⌜ v′ ⌝
  eval-correct₂′ n ih (apply e₁ e₂)
    (apply (rec lambda)
       q₁@(const (_∷_ {v = v₁} p₁ (_∷_ {v = v₂′} p₂ [])))
       (case q₂@(const (_∷_ {v = v₃} p₃ (_∷_ {v = v₄} p₄ [])))
          here (∷ ∷ [])
          (case {es = e₃ ∷ e₄ ∷ []} p₅ here (∷ ∷ [])
             q₃@(apply {v = v₁₂} p₆
                   (apply {v = v₁₁}
                      (apply {v₂ = v₈} p₇ p₈ p₉) p₁₀ p₁₁)
                   p₁₂))))
    size≡n =
      v
    , (apply e₁ e₂   ⟶⟨ apply (proj₁ (proj₂ (proj₂ lemma₂))) (proj₁ (proj₂ lemma₃)) ⟩
       e [ x ← v₂ ]  ⇓⟨ proj₁ (proj₂ lemma₅) ⟩■
       v)
    , (v₁₂    ≡⟨ proj₂ (proj₂ lemma₅) ⟩∎
       ⌜ v ⌝  ∎)
    where
    ⌜e₁⌝⇓ =
      ⌜ e₁ ⌝  ⇓⟨ p₁ ⟩
      v₁      ⇓⟨ p₃ ⟩■
      v₃

    ⌜e₂⌝⇓ =
      ⌜ e₂ ⌝  ⇓⟨ p₂ ⟩
      v₂′     ⇓⟨ p₄ ⟩■
      v₄

    ⌜e₂⌝≡ : ⌜ e₂ ⌝ ≡ v₄
    ⌜e₂⌝≡ = rep⇓≡rep e₂ ⌜e₂⌝⇓

    cl-v₄ : Closed v₄
    cl-v₄ = subst Closed ⌜e₂⌝≡ (rep-closed e₂)

    lem₁ =
      Exp.apply eval′ ⟨ ⌜ e₁ ⌝ ⟩  ≡⟨ ⟨by⟩ (rep⇓≡rep e₁ ⌜e₁⌝⇓) ⟩∎
      apply eval′ v₃              ∎

    module Abstract₁ where abstract

      lemma₁ : ∃ λ v → e₁ ⇓ v × const c-lambda (e₃ ∷ e₄ ∷ []) ≡ ⌜ v ⌝
      lemma₁ = ih
        (1 + size (_ ≡⟨ lem₁ ⟩⟶ _ ⇓⟨ p₅ ⟩■ _)                   ≡⟨ cong suc $ size-≡⟨⟩⟶ lem₁ ⟩≤
         1 + size p₅                                            ≤⟨ Nat.suc≤suc $
                                                                   Nat.≤-trans (Nat.m≤n+m _ 1) $
                                                                   Nat.≤-trans (Nat.m≤m+n _ (size q₃)) $
                                                                   Nat.≤-trans (Nat.m≤n+m _ (1 + size q₂)) $
                                                                   Nat.m≤n+m _ (2 + size q₁) ⟩
         3 + size q₁ + (1 + size q₂ + (1 + size p₅ + size q₃))  ≡⟨ size≡n ⟩≤
         n                                                      ∎≤)
        e₁
        (apply eval′ ⌜ e₁ ⌝             ≡⟨ lem₁ ⟩⟶
         apply eval′ v₃                 ⇓⟨ p₅ ⟩■
         const c-lambda (e₃ ∷ e₄ ∷ []))
        refl

    open Abstract₁

    module Abstract₂ where abstract

      lemma₂ :
        ∃ λ (x : Var) → ∃ λ (e : Exp) →
          e₁ ⇓ lambda x e × e₃ ≡ ⌜ x ⌝ × e₄ ≡ ⌜ e ⌝
      lemma₂ with lemma₁
      … | lambda x e , p , refl = x , e , p , refl , refl

    open Abstract₂

    x : Var
    x = proj₁ lemma₂

    e : Exp
    e = proj₁ (proj₂ lemma₂)

    cl-e₄ : Closed e₄
    cl-e₄ =
      subst Closed (sym (proj₂ (proj₂ (proj₂ (proj₂ lemma₂)))))
        (rep-closed e)

    lem₂ =
      Exp.apply eval′ ⟨ ⌜ e₂ ⌝ ⟩                                ≡⟨ ⟨by⟩ ⌜e₂⌝≡ ⟩
      Exp.apply eval′ v₄                                        ≡⟨ sym $ remove-substs ((v₄ , cl-v₄) ∷ []) ⟩∎
      apply eval′ (v₄ [ v-e₁ ← v₃ ] [ v-e ← e₄ ] [ v-x ← e₃ ])  ∎

    module Abstract₃ where abstract

      lemma₃ : ∃ λ v₂ → e₂ ⇓ v₂ × v₈ ≡ ⌜ v₂ ⌝
      lemma₃ = ih
        (1 + size (_ ≡⟨ lem₂ ⟩⟶ _ ⇓⟨ p₈ ⟩■ _)                    ≡⟨ cong suc $ size-≡⟨⟩⟶ lem₂ ⟩≤

         1 + size p₈                                             ≤⟨ Nat.suc≤suc $
                                                                    Nat.≤-trans (Nat.m≤n+m _ (1 + size p₇)) $
                                                                    Nat.≤-trans (Nat.m≤m+n _ (size p₉)) $
                                                                    Nat.≤-trans (Nat.m≤n+m _ 1) $
                                                                    Nat.≤-trans (Nat.m≤m+n _ (size p₁₀)) $
                                                                    Nat.≤-trans (Nat.m≤m+n _ (size p₁₁)) $
                                                                    Nat.≤-trans (Nat.m≤n+m _ (1 + size p₆)) $
                                                                    Nat.≤-trans (Nat.m≤m+n _ (size p₁₂)) $
                                                                    Nat.≤-trans (Nat.m≤n+m _ (1 + size p₅)) $
                                                                    Nat.≤-trans (Nat.m≤n+m _ (1 + size q₂)) $
                                                                    Nat.m≤n+m _ (2 + size q₁) ⟩
         3 + size q₁ +
         (1 + size q₂ +
          (1 + size p₅ +
           (1 + size p₆ +
            (1 + (1 + size p₇ + size p₈ + size p₉) + size p₁₀ +
             size p₁₁) +
            size p₁₂)))                                          ≡⟨ size≡n ⟩≤

         n                                                       ∎≤)
        e₂
        (apply eval′ ⌜ e₂ ⌝                                        ≡⟨ lem₂ ⟩⟶
         apply eval′ (v₄ [ v-e₁ ← v₃ ] [ v-e ← e₄ ] [ v-x ← e₃ ])  ⇓⟨ p₈ ⟩■
         v₈)
        refl

    open Abstract₃

    v₂ : Exp
    v₂ = proj₁ lemma₃

    module Abstract₄ where abstract

      lemma₄ : v₁₁ ≡ ⌜ e [ x ← v₂ ] ⌝
      lemma₄ = internal-subst-correct₂ (
        apply (apply (apply internal-subst ⟨ ⌜ x ⌝ ⟩) ⌜ v₂ ⌝) ⌜ e ⌝   ≡⟨ ⟨by⟩ (proj₁ (proj₂ (proj₂ (proj₂ lemma₂)))) ⟩⟶
        apply (apply (apply internal-subst e₃) ⌜ v₂ ⌝) ⟨ ⌜ e ⌝ ⟩      ≡⟨ ⟨by⟩ (proj₂ (proj₂ (proj₂ (proj₂ lemma₂)))) ⟩⟶
        apply (apply (apply internal-subst e₃) ⟨ ⌜ v₂ ⌝ ⟩) e₄         ≡⟨ ⟨by⟩ (proj₂ $ proj₂ lemma₃) ⟩⟶
        apply (apply (apply internal-subst e₃) v₈) e₄                 ≡⟨ sym $ remove-substs ((e₄ , cl-e₄) ∷ []) ⟩⟶
        apply (apply (apply internal-subst e₃) v₈) (e₄ [ v-x ← e₃ ])  ⇓⟨ apply (apply p₇ (values-compute-to-themselves (⇓-Value p₈)) p₉)
                                                                           p₁₀ p₁₁ ⟩■
        v₁₁)

    open Abstract₄

    lem₃ =
      Exp.apply eval′ ⟨ ⌜ e [ x ← v₂ ] ⌝ ⟩  ≡⟨ ⟨by⟩ lemma₄ ⟩∎
      apply eval′ v₁₁                       ∎

    module Abstract₅ where abstract

      lemma₅ : ∃ λ v → e [ x ← v₂ ] ⇓ v × v₁₂ ≡ ⌜ v ⌝
      lemma₅ = ih
        (1 + size (_ ≡⟨ lem₃ ⟩⟶
                   _ ⇓⟨ apply p₆
                          (values-compute-to-themselves (⇓-Value p₁₁))
                          p₁₂ ⟩■
                   _)                                                   ≡⟨ cong suc (size-≡⟨⟩⟶ lem₃) ⟩≤

         2 + size p₆ +
         size (values-compute-to-themselves (⇓-Value p₁₁)) + size p₁₂   ≤⟨ Nat.≤-refl {n = 2 + size p₆}
                                                                             Nat.+-mono
                                                                           size-values-compute-to-themselves-⇓-Value p₁₁
                                                                             Nat.+-mono
                                                                           Nat.≤-refl ⟩

         2 + size p₆ + size p₁₁ + size p₁₂                              ≤⟨ Nat.suc≤suc $
                                                                           Nat.≤-trans
                                                                             (Nat.≤-refl {n = 1 + size p₆}
                                                                                Nat.+-mono
                                                                              Nat.m≤n+m _ _
                                                                                Nat.+-mono
                                                                              Nat.≤-refl) $
                                                                           Nat.≤-trans (Nat.m≤n+m _ (1 + size p₅)) $
                                                                           Nat.≤-trans (Nat.m≤n+m _ (1 + size q₂)) $
                                                                           Nat.m≤n+m _ (2 + size q₁) ⟩
         3 + size q₁ +
         (1 + size q₂ +
          (1 + size p₅ +
           (1 + size p₆ +
            (1 + (1 + size p₇ + size p₈ + size p₉) + size p₁₀ +
             size p₁₁) +
            size p₁₂)))                                                 ≡⟨ size≡n ⟩≤

         n                                                              ∎≤)
        (e [ x ← v₂ ])
        (apply eval′ ⌜ e [ x ← v₂ ] ⌝  ≡⟨ lem₃ ⟩⟶
         apply eval′ v₁₁               ⇓⟨ apply p₆ (values-compute-to-themselves (⇓-Value p₁₁)) p₁₂ ⟩■
         v₁₂)
        refl

    open Abstract₅

    v : Exp
    v = proj₁ lemma₅

  eval-correct₂′ _ _ (apply _ _)
    (apply (rec lambda) (const _) (case (const _) (there a≢a _) _ _))
    _ =
    ⊥-elim (a≢a refl)

  eval-correct₂′ _ _ (lambda x e)
    (apply (rec lambda) (const (_∷_ {v = v₁} p₁ (_∷_ {v = v₂} p₂ [])))
       (case (const (_∷_ {v = v₃} p₃ (_∷_ {v = v₄} p₄ [])))
          (there _ (there _ (there _ here))) (∷ ∷ [])
          (const (_∷_ {v = v₅} p₅ (_∷_ {v = v₆} p₆ [])))))
    _ =
      lambda x e
    , lambda
    , (const c-lambda (v₅ ∷ v₆ ∷ [])  ≡⟨ sym $ cong (const c-lambda) $
                                         cong₂ _∷_ (rep⇓≡rep x ⌜x⌝⇓) $
                                         cong (_∷ []) (rep⇓≡rep e ⌜e⌝⇓) ⟩∎
       ⌜ lambda x e ⌝                 ∎)
    where
    ⌜x⌝⇓ =
      ⌜ x ⌝  ⇓⟨ p₁ ⟩
      v₁     ⇓⟨ p₃ ⟩
      v₃     ⇓⟨ p₅ ⟩■
      v₅

    ⌜e⌝⇓′ =
      ⌜ e ⌝  ⇓⟨ p₂ ⟩
      v₂     ⇓⟨ p₄ ⟩■
      v₄

    v₄-closed : Closed v₄
    v₄-closed =     $⟨ rep-closed e ⟩
      Closed ⌜ e ⌝  →⟨ subst Closed (rep⇓≡rep e ⌜e⌝⇓′) ⟩□
      Closed v₄     □

    ⌜e⌝⇓ =
      ⌜ e ⌝            ⇓⟨ ⌜e⌝⇓′ ⟩
      v₄               ≡⟨ sym $ remove-substs ((v₄ , v₄-closed) ∷ []) ⟩⟶
      v₄ [ v-x ← v₃ ]  ⇓⟨ p₆ ⟩■
      v₆

  eval-correct₂′ _ _ (lambda _ _)
    (apply (rec lambda) (const _)
       (case (const _) (there _ (there _ (there _ (there l≢l _))))
          _ _))
    _ =
    ⊥-elim $ l≢l refl

  eval-correct₂′ n ih (rec x e)
    (apply (rec lambda)
       q₁@(const (_∷_ {v = v₁} p₁ (_∷_ {v = v₂} p₂ [])))
       (case {v = v₅}
          q₂@(const (_∷_ {v = v₃} p₃ (_∷_ {v = v₄} p₄ [])))
          (there _ (there _ here)) (∷ ∷ []) p₅))
    size≡n =
      let v₆ , ⇓v₆ , ≡⌜v₆⌝ = lemma in
      v₆
    , (rec x e  ⇓⟨ rec ⇓v₆ ⟩■
       v₆)
    , (v₅      ≡⟨ ≡⌜v₆⌝ ⟩∎
       ⌜ v₆ ⌝  ∎)
    where
    ⌜x⌝⇓ =
      ⌜ x ⌝  ⇓⟨ p₁ ⟩
      v₁     ⇓⟨ p₃ ⟩■
      v₃

    ⌜e⌝⇓ =
      ⌜ e ⌝  ⇓⟨ p₂ ⟩
      v₂     ⇓⟨ p₄ ⟩■
      v₄

    v₄-closed : Closed v₄
    v₄-closed =     $⟨ rep-closed e ⟩
      Closed ⌜ e ⌝  →⟨ subst Closed (rep⇓≡rep e ⌜e⌝⇓) ⟩□
      Closed v₄     □

    lem =
      Exp.apply eval′
        (apply (apply (apply internal-subst ⌜ x ⌝) ⌜ rec x e ⌝) ⌜ e ⌝)  ≡⟨ cong₂ (λ v₃ v₄ → apply eval′
                                                                                    (apply (apply (apply internal-subst v₃)
                                                                                              (const c-rec (v₃ ∷ v₄ ∷ [])))
                                                                                       v₄))
                                                                             (rep⇓≡rep x ⌜x⌝⇓)
                                                                             (rep⇓≡rep e ⌜e⌝⇓) ⟩
      Exp.apply eval′
        (apply (apply (apply internal-subst v₃)
                  (const c-rec (v₃ ∷ v₄ ∷ [])))
           v₄)                                                          ≡⟨ sym $ remove-substs ((v₄ , v₄-closed) ∷ []) ⟩∎

      apply eval′
        (apply (apply (apply internal-subst v₃)
                  (const c-rec (v₃ ∷ v₄ [ v-x ← v₃ ] ∷ [])))
           (v₄ [ v-x ← v₃ ]))                                           ∎

    abstract

      lemma : ∃ λ v₆ → e [ x ← rec x e ] ⇓ v₆ × v₅ ≡ ⌜ v₆ ⌝
      lemma = ih
        (1 + size (_ ⟶⟨ []⇓⁻¹ (apply→ ∙) internal-subst-correct₁ ⟩
                   _ ≡⟨ lem ⟩⟶
                   _ ⇓⟨ p₅ ⟩■
                   _)                                               ≤⟨ Nat.suc≤suc $
                                                                       size-[]⇓⁻¹ (apply→ ∙) {p = internal-subst-correct₁ {e′ = rec x e}}
                                                                         {q = _ ≡⟨ lem ⟩⟶ _ ⇓⟨ p₅ ⟩■ _} ⟩

         1 + size (_ ≡⟨ lem ⟩⟶ _ ⇓⟨ p₅ ⟩■ _)                        ≡⟨ cong suc $ size-≡⟨⟩⟶ lem ⟩≤

         1 + size p₅                                                ≤⟨ Nat.suc≤suc $
                                                                       Nat.≤-trans (Nat.m≤n+m _ (1 + size q₂)) $
                                                                       Nat.m≤n+m _ (2 + size q₁) ⟩

         3 + size q₁ + (1 + size q₂ + size p₅)                      ≡⟨ size≡n ⟩≤

         n                                                          ∎≤)
        (e [ x ← rec x e ])
        (apply eval′ ⌜ e [ x ← rec x e ] ⌝                          ⟶⟨ []⇓⁻¹ (apply→ ∙) internal-subst-correct₁ ⟩

         apply eval′
           (apply (apply (apply internal-subst ⌜ x ⌝) ⌜ rec x e ⌝)
              ⌜ e ⌝)                                                ≡⟨ lem ⟩⟶

         apply eval′
           (apply (apply (apply internal-subst v₃)
                     (const c-rec (v₃ ∷ v₄ [ v-x ← v₃ ] ∷ [])))
              (v₄ [ v-x ← v₃ ]))                                    ⇓⟨ p₅ ⟩■

         v₅)
        refl

  eval-correct₂′ _ _ (rec _ _)
    (apply (rec lambda) (const _)
       (case (const _) (there _ (there _ (there r≢r _))) _ _))
    _ =
    ⊥-elim $ r≢r refl

  eval-correct₂′ _ _ (var _)
    (apply (rec lambda) (const (_ ∷ []))
       (case (const (_ ∷ []))
          (there _ (there _ (there _ (there _ (there _ ()))))) _ _))
    _

  eval-correct₂′ n ih (const c es)
    (apply (rec lambda)
       q₁@(const (_∷_ {v = v₁} p₁ (_∷_ {v = v₂} p₂ [])))
       (case q₂@(const (_∷_ {v = v₃} p₃ (_∷_ {v = v₄} p₄ [])))
          (there _ (there _ (there _ (there _ here)))) (∷ ∷ [])
          (const (_∷_ {v = v₅} p₅ (_∷_ {v = v₆} p₆ [])))))
    size≡n =
    let vs , ⇓vs , ≡⌜vs⌝ = lemma in
      const c vs
    , (const c es  ⇓⟨ const ⇓vs ⟩■
       const c vs)
    , (const c-const (v₅ ∷ v₆ ∷ [])  ≡⟨ cong₂ (λ v₅ v₆ → const c-const (v₅ ∷ v₆ ∷ []))
                                          (sym $ rep⇓≡rep c ⌜c⌝⇓)
                                          ≡⌜vs⌝ ⟩∎
       ⌜ const c vs ⌝                ∎)
    where
    ⌜c⌝⇓ =
      ⌜ c ⌝  ⇓⟨ p₁ ⟩
      v₁     ⇓⟨ p₃ ⟩
      v₃     ⇓⟨ p₅ ⟩■
      v₅

    ⌜es⌝⇓ =
      ⌜ es ⌝  ⇓⟨ p₂ ⟩
      v₂      ⇓⟨ p₄ ⟩■
      v₄

    v₄-closed : Closed v₄
    v₄-closed =      $⟨ rep-closed es ⟩
      Closed ⌜ es ⌝  →⟨ subst Closed (rep⇓≡rep es ⌜es⌝⇓) ⟩□
      Closed v₄      □

    lem₁ =
      Exp.apply (map′ eval′) ⟨ ⌜ es ⌝ ⟩  ≡⟨ ⟨by⟩ (rep⇓≡rep es ⌜es⌝⇓) ⟩∎
      apply (map′ eval′) v₄              ∎

    lem₂ =
      Exp.apply (map′ eval′) v₄             ≡⟨ sym $ remove-substs ((v₄ , v₄-closed) ∷ []) ⟩∎
      apply (map′ eval′) (v₄ [ v-c ← v₃ ])  ∎

    abstract

      lemma : ∃ λ vs → es ⇓⋆ vs × v₆ ≡ ⌜ vs ⌝
      lemma = map-lemma n ih es
        (apply (map′ eval′) ⌜ es ⌝             ≡⟨ lem₁ ⟩⟶
         apply (map′ eval′) v₄                 ≡⟨ lem₂ ⟩⟶
         apply (map′ eval′) (v₄ [ v-c ← v₃ ])  ⇓⟨ p₆ ⟩■
         v₆)
        (size (_ ≡⟨ lem₁ ⟩⟶ _ ≡⟨ lem₂ ⟩⟶ _ ⇓⟨ p₆ ⟩■ _)                ≡⟨ trans (size-≡⟨⟩⟶ lem₁) (size-≡⟨⟩⟶ lem₂) ⟩≤
         size p₆                                                      ≤⟨ Nat.≤-trans (Nat.m≤m+n _ 0) $
                                                                         Nat.≤-trans (Nat.m≤n+m _ (1 + size p₅)) $
                                                                         Nat.≤-trans (Nat.m≤n+m _ (1 + size q₂)) $
                                                                         Nat.m≤n+m _ (3 + size q₁) ⟩
         3 + size q₁ + (1 + size q₂ + (1 + size p₅ + (size p₆ + 0)))  ≡⟨ size≡n ⟩≤
         n                                                            ∎≤)

  eval-correct₂′ n ih (case e bs)
    (apply (rec lambda)
       q₁@(const (_∷_ {v = v₁} p₁ (_∷_ {v = v₂} p₂ [])))
       (case q₂@(const (_∷_ {v = v₃} p₃ (_∷_ {v = v₄} p₄ [])))
          (there _ here) (∷ ∷ [])
          (case {es = e₁ ∷ e₂ ∷ []} p₅ here (∷ ∷ [])
             q₃@(case {es = e₃ ∷ e₄ ∷ e₅ ∷ []} {v = v₅}
                   p₆ here (∷ ∷ ∷ []) p₇))))
    size≡n = lemma₅
    lemma₄
    (1 + size (_ ≡⟨ lem₂ ⟩⟶ _ ⇓⟨ p₇ ⟩■ _)                       ≡⟨ cong suc $ size-≡⟨⟩⟶ lem₂ ⟩≤

     1 + size p₇                                                ≤⟨ Nat.suc≤suc $
                                                                   Nat.≤-trans (Nat.m≤n+m _ (1 + size p₆)) $
                                                                   Nat.≤-trans (Nat.m≤n+m _ (1 + size p₅)) $
                                                                   Nat.≤-trans (Nat.m≤n+m _ (1 + size q₂)) $
                                                                   Nat.m≤n+m _ (2 + size q₁) ⟩
     3 + size q₁ +
       (1 + size q₂ + (1 + size p₅ + (1 + size p₆ + size p₇)))  ≡⟨ size≡n ⟩≤

     n                                                          ∎≤)
    where
    ⌜e⌝⇓ =
      ⌜ e ⌝  ⇓⟨ p₁ ⟩
      v₁     ⇓⟨ p₃ ⟩■
      v₃

    ⌜bs⌝⇓ =
      ⌜ bs ⌝  ⇓⟨ p₂ ⟩
      v₂      ⇓⟨ p₄ ⟩■
      v₄

    v₄-closed : Closed v₄
    v₄-closed =      $⟨ rep-closed bs ⟩
      Closed ⌜ bs ⌝  →⟨ subst Closed (rep⇓≡rep bs ⌜bs⌝⇓) ⟩□
      Closed v₄      □

    lem₁ =
      Exp.apply eval′ ⟨ ⌜ e ⌝ ⟩  ≡⟨ ⟨by⟩ (rep⇓≡rep e ⌜e⌝⇓) ⟩∎
      apply eval′ v₃             ∎

    module Abstract₁ where abstract

      lemma₁ : ∃ λ v′ → e ⇓ v′ × const c-const (e₁ ∷ e₂ ∷ []) ≡ ⌜ v′ ⌝
      lemma₁ = ih
        (1 + size (_ ≡⟨ lem₁ ⟩⟶ _ ⇓⟨ p₅ ⟩■ _)                   ≡⟨ cong suc $ size-≡⟨⟩⟶ lem₁ ⟩≤
         1 + size p₅                                            ≤⟨ Nat.suc≤suc $
                                                                   Nat.≤-trans (Nat.m≤n+m _ 1) $
                                                                   Nat.≤-trans (Nat.m≤m+n _ (size q₃)) $
                                                                   Nat.≤-trans (Nat.m≤n+m _ (1 + size q₂)) $
                                                                   Nat.m≤n+m _ (2 + size q₁) ⟩
         3 + size q₁ + (1 + size q₂ + (1 + size p₅ + size q₃))  ≡⟨ size≡n ⟩≤
         n                                                      ∎≤)
        e
        (apply eval′ ⌜ e ⌝             ≡⟨ lem₁ ⟩⟶
         apply eval′ v₃                ⇓⟨ p₅ ⟩■
         const c-const (e₁ ∷ e₂ ∷ []))
        refl

    open Abstract₁

    module Abstract₂ where abstract

      lemma₂ :
        ∃ λ c → ∃ λ vs →
          e ⇓ const c vs ×
          const c-const (e₁ ∷ e₂ ∷ []) ≡ ⌜ const c vs ⌝
      lemma₂ with lemma₁
      … | const c vs , p , refl = c , vs , p , refl

    open Abstract₂

    c : Const
    c = proj₁ lemma₂

    vs : List Exp
    vs = proj₁ (proj₂ lemma₂)

    e⇓ : e ⇓ const c vs
    e⇓ = proj₁ (proj₂ (proj₂ lemma₂))

    ≡⌜c⌝∷⌜vs⌝∷[] : e₁ ∷ e₂ ∷ [] ≡ ⌜ c ⌝ ∷ ⌜ vs ⌝ ∷ []
    ≡⌜c⌝∷⌜vs⌝∷[] = proj₂ $ cancel-const (proj₂ (proj₂ (proj₂ lemma₂)))

    ≡⌜c⌝ : e₁ ≡ ⌜ c ⌝
    ≡⌜c⌝ = List.cancel-∷-head ≡⌜c⌝∷⌜vs⌝∷[]

    ≡⌜vs⌝ : e₂ ≡ ⌜ vs ⌝
    ≡⌜vs⌝ = List.cancel-∷-head $ List.cancel-∷-tail ≡⌜c⌝∷⌜vs⌝∷[]

    module Abstract₃ where abstract

      lemma₃ :
        ∃ λ xs → ∃ λ e′ →
          Lookup c bs xs e′ ×
          const c-branch (e₃ ∷ e₄ ∷ e₅ ∷ []) ≡ ⌜ branch c xs e′ ⌝
      lemma₃ = internal-lookup-correct₂
        (apply (apply internal-lookup ⟨ ⌜ c ⌝ ⟩) ⌜ bs ⌝  ≡⟨ ⟨by⟩ ≡⌜c⌝ ⟩⟶

         apply (apply internal-lookup e₁) ⟨ ⌜ bs ⌝ ⟩     ≡⟨ ⟨by⟩ (rep⇓≡rep bs ⌜bs⌝⇓) ⟩⟶

         apply (apply internal-lookup e₁) v₄             ≡⟨ sym $ remove-substs ((v₄ , v₄-closed) ∷ []) ⟩⟶

         apply (apply internal-lookup e₁)
           (v₄ [ v-e ← v₃ ] [ v-es ← e₂ ] [ v-c ← e₁ ])  ⇓⟨ p₆ ⟩■

         const c-branch (e₃ ∷ e₄ ∷ e₅ ∷ []))

    open Abstract₃

    xs : List Var
    xs = proj₁ lemma₃

    e′ : Exp
    e′ = proj₁ (proj₂ lemma₃)

    lkup : Lookup c bs xs e′
    lkup = proj₁ (proj₂ (proj₂ lemma₃))

    ≡⌜xs⌝∷⌜e′⌝∷[] : e₄ ∷ e₅ ∷ [] ≡ ⌜ xs ⌝ ∷ ⌜ e′ ⌝ ∷ []
    ≡⌜xs⌝∷⌜e′⌝∷[] =
      List.cancel-∷-tail $ proj₂ $
      cancel-const (proj₂ (proj₂ (proj₂ lemma₃)))

    ≡⌜xs⌝ : e₄ ≡ ⌜ xs ⌝
    ≡⌜xs⌝ = List.cancel-∷-head ≡⌜xs⌝∷⌜e′⌝∷[]

    ≡⌜e′⌝ : e₅ ≡ ⌜ e′ ⌝
    ≡⌜e′⌝ = List.cancel-∷-head $ List.cancel-∷-tail ≡⌜xs⌝∷⌜e′⌝∷[]

    lem₂ =
      Exp.apply eval′
        (apply (apply (apply internal-substs ⌜ xs ⌝) ⌜ vs ⌝) ⌜ e′ ⌝)   ≡⟨ sym $ remove-substs [] ⟩

      Exp.apply eval′
        (apply (apply (apply internal-substs
                         (⌜ xs ⌝ [ v-underscore ← e₃ ]))
                  (⌜ vs ⌝ [ v-c ← e₁ ] [ v-e ← e₅ ] [ v-xs ← e₄ ]
                     [ v-underscore ← e₃ ]))
           (⌜ e′ ⌝ [ v-xs ← e₄ ] [ v-underscore ← e₃ ]))               ≡⟨⟩

      Exp.apply eval′
        (apply (apply (apply internal-substs
                         (⟨ ⌜ xs ⌝ ⟩ [ v-underscore ← e₃ ]))
                  (⌜ vs ⌝ [ v-c ← e₁ ] [ v-e ← e₅ ] [ v-xs ← e₄ ]
                     [ v-underscore ← e₃ ]))
           (⌜ e′ ⌝ [ v-xs ← e₄ ] [ v-underscore ← e₃ ]))               ≡⟨ ⟨by⟩ ≡⌜xs⌝ ⟩

      Exp.apply eval′
        (apply (apply (apply internal-substs
                         (e₄ [ v-underscore ← e₃ ]))
                  (⟨ ⌜ vs ⌝ ⟩ [ v-c ← e₁ ] [ v-e ← e₅ ] [ v-xs ← e₄ ]
                     [ v-underscore ← e₃ ]))
           (⌜ e′ ⌝ [ v-xs ← e₄ ] [ v-underscore ← e₃ ]))               ≡⟨ ⟨by⟩ ≡⌜vs⌝ ⟩

      Exp.apply eval′
        (apply (apply (apply internal-substs
                         (e₄ [ v-underscore ← e₃ ]))
                  (e₂ [ v-c ← e₁ ] [ v-e ← e₅ ] [ v-xs ← e₄ ]
                     [ v-underscore ← e₃ ]))
           (⟨ ⌜ e′ ⌝ ⟩ [ v-xs ← e₄ ] [ v-underscore ← e₃ ]))           ≡⟨ ⟨by⟩ ≡⌜e′⌝ ⟩∎

      apply eval′
        (apply (apply (apply internal-substs
                         (e₄ [ v-underscore ← e₃ ]))
                  (e₂ [ v-c ← e₁ ] [ v-e ← e₅ ] [ v-xs ← e₄ ]
                     [ v-underscore ← e₃ ]))
           (e₅ [ v-xs ← e₄ ] [ v-underscore ← e₃ ]))                   ∎

    lemma₄ =
      apply eval′
        (apply (apply (apply internal-substs ⌜ xs ⌝) ⌜ vs ⌝) ⌜ e′ ⌝)  ≡⟨ lem₂ ⟩⟶

      apply eval′
        (apply (apply (apply internal-substs
                         (e₄ [ v-underscore ← e₃ ]))
                  (e₂ [ v-c ← e₁ ] [ v-e ← e₅ ] [ v-xs ← e₄ ]
                     [ v-underscore ← e₃ ]))
           (e₅ [ v-xs ← e₄ ] [ v-underscore ← e₃ ]))                  ⇓⟨ p₇ ⟩■

      v₅

    lemma₅ :
      ∀ {v}
      (p : apply eval′
             (apply (apply (apply internal-substs ⌜ xs ⌝) ⌜ vs ⌝)
                ⌜ e′ ⌝)
             ⇓
           v) →
      size p < n →
      ∃ λ v′ → case e bs ⇓ v′ × v ≡ ⌜ v′ ⌝
    lemma₅ (apply {v₂ = v₈} {v = v} (rec lambda) p₈ p₉) size<n =
      let v′ , ⇓v′ , ≡⌜v′⌝ = lemma₇ in
        v′
      , (case e bs  ⇓⟨ case e⇓ lkup e′[xs←vs]↦e″ ⇓v′ ⟩■
         v′)
      , ≡⌜v′⌝
      where
      lemma₆ : ∃ λ e″ → e′ [ xs ← vs ]↦ e″ × v₈ ≡ ⌜ e″ ⌝
      lemma₆ = internal-substs-correct₂ (
        apply (apply (apply internal-substs ⌜ xs ⌝) ⌜ vs ⌝) ⌜ e′ ⌝  ⇓⟨ p₈ ⟩■

        v₈)

      e″ : Exp
      e″ = proj₁ lemma₆

      e′[xs←vs]↦e″ : e′ [ xs ← vs ]↦ e″
      e′[xs←vs]↦e″ = proj₁ (proj₂ lemma₆)

      ≡⌜e″⌝ : v₈ ≡ ⌜ e″ ⌝
      ≡⌜e″⌝ = proj₂ (proj₂ lemma₆)

      lemma₇ : ∃ λ v′ → e″ ⇓ v′ × v ≡ ⌜ v′ ⌝
      lemma₇ = elim¹
        (λ {y = v₈} _ →
           (p₈′ : apply (apply (apply internal-substs ⌜ xs ⌝) ⌜ vs ⌝)
                    ⌜ e′ ⌝
                    ⇓
                  v₈)
           (p₉′ : case v₈ (branches [ v-eval ← eval′ ]B⋆) ⇓ v) →
           size p₈′ ≡ size p₈ →
           size p₉′ ≡ size p₉ →
           ∃ λ v′ → e″ ⇓ v′ × v ≡ ⌜ v′ ⌝)
        (λ p₈′ p₉′ eq₈ eq₉ → ih
           (4 + size (rep⇓rep e″) + size p₉′  ≤⟨ Nat.≤-refl {n = 4}
                                                   Nat.+-mono
                                                 size-values-compute-to-themselves (rep-value e″) p₈′
                                                   Nat.+-mono
                                                 Nat.≤-refl {n = size p₉′} ⟩
            4 + size p₈′ + size p₉′           ≡⟨ cong₂ (λ p₈ p₉ → 4 + p₈ + p₉) eq₈ eq₉ ⟩≤
            4 + size p₈ + size p₉             ≤⟨ size<n ⟩∎
            n                                 ∎≤)
           e″
           (apply eval′ ⌜ e″ ⌝                               ⟶⟨ apply (rec lambda) (rep⇓rep e″) ⟩
            case ⟨ ⌜ e″ ⌝ ⟩ (branches [ v-eval ← eval′ ]B⋆)  ⇓⟨ p₉′ ⟩■
            v)
           refl)
        (sym ≡⌜e″⌝)
        p₈ p₉ refl refl

  eval-correct₂′ _ _ (case _ _)
    (apply (rec lambda) (const _)
       (case (const _) (there _ (there c≢c _)) _ _))
    _ =
    ⊥-elim $ c≢c refl

abstract

  -- The self-interpreter is correctly implemented (part two).

  eval-correct₂ :
    ∀ {e v} →
    apply eval ⌜ e ⌝ ⇓ v →
    ∃ λ v′ → e ⇓ v′ × v ≡ ⌜ v′ ⌝
  eval-correct₂ p =
    Nat.well-founded-elim P eval-correct₂′ (size p) _ p refl

  map-eval-correct₂ :
    ∀ {es vs} →
    apply (map eval) ⌜ es ⌝ ⇓ vs →
    ∃ λ vs′ → es ⇓⋆ vs′ × vs ≡ ⌜ vs′ ⌝
  map-eval-correct₂ p =
    map-lemma _ (λ _ _ p _ → eval-correct₂ p) _ p Nat.≤-refl

  -- If e does not terminate, then apply eval ⌜ e ⌝ does not
  -- terminate.

  eval-preserves-non-termination :
    ∀ {e} → ¬ Terminates e → ¬ Terminates (apply eval ⌜ e ⌝)
  eval-preserves-non-termination {e = e} p =
    Terminates (apply eval ⌜ e ⌝)  →⟨ Σ-map id proj₁ ∘ eval-correct₂ ∘ proj₂ ⟩
    Terminates e                   →⟨ p ⟩□
    ⊥                              □

  -- The self-interpreter implements the χ semantics.

  eval-implements-semantics : Implements id eval semantics
  eval-implements-semantics =
      eval-closed
    , (λ _ _ → eval-correct₁)
    , (λ (e , e-closed) v ⌜e⌝⇓v →
         let v′ , e⇓v′ , v≡⌜v′⌝ = eval-correct₂ ⌜e⌝⇓v in
           (v′ , closed⇓closed e⇓v′ e-closed)
         , (e   ⇓⟨ e⇓v′ ⟩■
            v′)
         , (v       ≡⟨ v≡⌜v′⌝ ⟩∎
            ⌜ v′ ⌝  ∎))

  -- The χ semantics is computable.

  semantics-computable : Computable semantics
  semantics-computable = eval , eval-implements-semantics
