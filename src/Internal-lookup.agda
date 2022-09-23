------------------------------------------------------------------------
-- Internal lookup
------------------------------------------------------------------------

module Internal-lookup where

open import Equality.Propositional
open import Prelude hiding (const)
open import Tactic.By.Propositional

open import Equality.Decision-procedures equality-with-J
open import Function-universe equality-with-J using ($⟨_⟩_)
open import Nat equality-with-J as Nat

-- To simplify the development, let's work with actual natural numbers
-- as variables and constants (see
-- Atom.one-can-restrict-attention-to-χ-ℕ-atoms).

open import Atom

open import Cancellation   χ-ℕ-atoms
open import Chi            χ-ℕ-atoms
open import Coding         χ-ℕ-atoms
open import Compatibility  χ-ℕ-atoms
open import Constants      χ-ℕ-atoms
open import Free-variables χ-ℕ-atoms
open import Reasoning      χ-ℕ-atoms

open import Coding.Instances.Nat
open import Combinators hiding (id)
open import Free-variables.Remove-substs

private

  -- Auxiliary definitions used in the implementation of
  -- internal-lookup.

  branches : List Br
  branches =
    branch c-cons (v-b ∷ v-bs ∷ []) (case (var v-b) (
      branch c-branch (v-c′ ∷ v-underscore ∷ v-underscore ∷ []) (
        case (equal-ℕ (var v-c) (var v-c′)) (
          branch c-false [] (apply (var v-lookup) (var v-bs)) ∷
          branch c-true [] (var v-b) ∷ [])) ∷ [])) ∷ []

  body : Exp
  body = rec v-lookup (lambda v-bs (case (var v-bs) branches))

-- Internal lookup. Searches for a branch matching a given natural
-- number.

internal-lookup : Exp
internal-lookup = lambda v-c body

-- Internal lookup is correct (part one).

internal-lookup-correct₁ :
  ∀ {c bs xs e} →
  Lookup c bs xs e →
  apply (apply internal-lookup ⌜ c ⌝) ⌜ bs ⌝ ⇓ ⌜ branch c xs e ⌝
internal-lookup-correct₁ {c = c} {bs = bs} {xs = xs} {e = e} p =
  apply (apply internal-lookup ⌜ c ⌝) ⌜ bs ⌝          ⟶⟨ apply (apply lambda (rep⇓rep c) (rec lambda)) (rep⇓rep bs) ⟩

  case ⌜ bs ⌝ (
    branches [ v-c ← ⌜ c ⌝ ]B⋆ [ v-lookup ← lkup ]B⋆
      [ v-bs ← ⌜ bs ⌝ ]B⋆)                            ⇓⟨ lemma bs p ⟩■

  ⌜ branch c xs e ⌝
  where
  lkup : Exp
  lkup = body [ v-c ← ⌜ c ⌝ ]

  lkup-closed : Closed lkup
  lkup-closed = Closed′-closed-under-subst
    (from-⊎ (closed′? body (v-c ∷ [])))
    (rep-closed c)

  lemma :
    ∀ bs →
    Lookup c bs xs e →
    case ⌜ bs ⌝ (
      branches [ v-c ← ⌜ c ⌝ ]B⋆ [ v-lookup ← lkup ]B⋆
        [ v-bs ← ⌜ bs ⌝ ]B⋆)
      ⇓
    ⌜ branch c xs e ⌝
  lemma (branch c′ xs′ e′ ∷ bs) p =
    case ⌜ branch c′ xs′ e′ ∷ bs ⌝ (
      branches [ v-c ← ⌜ c ⌝ ]B⋆ [ v-lookup ← lkup ]B⋆
        [ v-bs ← ⌜ branch c′ xs′ e′ ∷ bs ⌝ ]B⋆)                     ⟶⟨ case (rep⇓rep (branch c′ xs′ e′ ∷ bs)) here (∷ ∷ []) ⟩

    case ⌜ branch c′ xs′ e′ ⌝ (
      branch c-branch (v-c′ ∷ v-underscore ∷ v-underscore ∷ []) (
        case (equal-ℕ (⌜ c ⌝ [ v-lookup ← lkup ] [ v-bs ← ⌜ bs ⌝ ]
                         [ v-b ← ⌜ branch c′ xs′ e′ ⌝ ])
               (var v-c′)) (
          branch c-false []
            (apply (lkup [ v-bs ← ⌜ bs ⌝ ]
                      [ v-b ← ⌜ branch c′ xs′ e′ ⌝ ])
               (⌜ bs ⌝ [ v-b ← ⌜ branch c′ xs′ e′ ⌝ ])) ∷
          branch c-true [] ⌜ branch c′ xs′ e′ ⌝ ∷
          [])) ∷
      [])                                                           ≡⟨ remove-substs ((lkup , lkup-closed) ∷ []) ⟩⟶

    case ⌜ branch c′ xs′ e′ ⌝ (
      branch c-branch (v-c′ ∷ v-underscore ∷ v-underscore ∷ []) (
        case (equal-ℕ ⌜ c ⌝ (var v-c′)) (
          branch c-false [] (apply lkup ⌜ bs ⌝) ∷
          branch c-true [] ⌜ branch c′ xs′ e′ ⌝ ∷
          [])) ∷
      [])                                                           ⟶⟨ case (rep⇓rep (branch c′ xs′ e′)) here (∷ ∷ ∷ []) ⟩

    case (equal-ℕ (⌜ c ⌝ [ v-underscore ← ⌜ e′ ⌝ ]
                     [ v-underscore ← ⌜ xs′ ⌝ ] [ v-c′ ← ⌜ c′ ⌝ ])
            ⌜ c′ ⌝) (
      branch c-false [] (
        apply (lkup [ v-underscore ← ⌜ e′ ⌝ ]
                 [ v-underscore ← ⌜ xs′ ⌝ ] [ v-c′ ← ⌜ c′ ⌝ ])
          (⌜ bs ⌝ [ v-underscore ← ⌜ e′ ⌝ ]
             [ v-underscore ← ⌜ xs′ ⌝ ] [ v-c′ ← ⌜ c′ ⌝ ])) ∷
      branch c-true [] (
        ⌜ branch c′ xs′ e′ ⌝ [ v-underscore ← ⌜ e′ ⌝ ]
          [ v-underscore ← ⌜ xs′ ⌝ ] [ v-c′ ← ⌜ c′ ⌝ ]) ∷
      [])                                                            ≡⟨ remove-substs ((lkup , lkup-closed) ∷ []) ⟩⟶

    case (equal-ℕ ⌜ c ⌝ ⌜ c′ ⌝) (
      branch c-false [] (apply lkup ⌜ bs ⌝) ∷
      branch c-true [] ⌜ branch c′ xs′ e′ ⌝ ∷
      [])                                                            ⟶⟨ []⇓ (case ∙) (equal-ℕ-correct c c′) ⟩

    case ⌜ Prelude.if c Nat.≟ c′ then true else false ⌝ (
      branch c-false [] (apply lkup ⌜ bs ⌝) ∷
      branch c-true [] ⌜ branch c′ xs′ e′ ⌝ ∷
      [])                                                            ⇓⟨ if-lemma _ _ _ _ (c Nat.≟ c′) p ⟩■

    ⌜ branch c xs e ⌝
    where
    if-lemma :
      ∀ c′ xs′ e′ bs (b : Dec (c ≡ c′)) →
      Lookup c (branch c′ xs′ e′ ∷ bs) xs e →
      case ⌜ Prelude.if b then true else false ⌝ (
        branch c-false [] (apply lkup ⌜ bs ⌝) ∷
        branch c-true [] ⌜ branch c′ xs′ e′ ⌝ ∷
        [])
        ⇓
      ⌜ branch c xs e ⌝
    if-lemma _ _ _ _ (no c≢c)   here           = ⊥-elim $ c≢c refl
    if-lemma _ _ _ _ (yes c≡c′) (there c≢c′ _) = ⊥-elim $ c≢c′ c≡c′

    if-lemma c xs e bs (yes _) here =
      case ⌜ true ⌝ (
        branch c-false [] (apply lkup ⌜ bs ⌝) ∷
        branch c-true [] ⌜ branch c xs e ⌝ ∷
        [])                                      ⇓⟨ case (rep⇓rep true) (there (λ ()) here) [] (rep⇓rep (branch c xs e)) ⟩■

      ⌜ branch c xs e ⌝

    if-lemma c′ xs′ e′ bs (no _) (there c≢c′ p) =
      case ⌜ false ⌝ (
        branch c-false [] (apply lkup ⌜ bs ⌝) ∷
        branch c-true [] ⌜ branch c′ xs′ e′ ⌝ ∷
        [])                                               ⟶⟨ case (rep⇓rep false) here [] ⟩

      apply lkup ⌜ bs ⌝                                   ⟶⟨ apply (rec lambda) (rep⇓rep bs) ⟩

      case ⌜ bs ⌝ (
        branches [ v-c ← ⌜ c ⌝ ]B⋆ [ v-lookup ← lkup ]B⋆
          [ v-bs ← ⌜ bs ⌝ ]B⋆)                            ⇓⟨ lemma bs p ⟩■

      ⌜ branch c xs e ⌝

-- Internal lookup is correct (part two).

internal-lookup-correct₂ :
  ∀ {c bs v} →
  apply (apply internal-lookup ⌜ c ⌝) ⌜ bs ⌝ ⇓ v →
  ∃ λ xs → ∃ λ e → Lookup c bs xs e × v ≡ ⌜ branch c xs e ⌝
internal-lookup-correct₂ {c = c} {bs = bs} {v = v}
  (apply {v₂ = v₂} (apply {v₂ = v₁} lambda ⌜c⌝⇓v₁ (rec lambda))
     ⌜bs⌝⇓v₂ p) =
  lemma bs (
    case ⟨ ⌜ bs ⌝ ⟩ (
      branches [ v-c ← ⌜ c ⌝ ]B⋆
        [ v-lookup ← lkup ]B⋆ [ v-bs ← ⟨ ⌜ bs ⌝ ⟩ ]B⋆)              ≡⟨ ⟨by⟩ (rep⇓≡rep bs ⌜bs⌝⇓v₂) ⟩⟶

    case v₂ (
      branches [ v-c ← ⟨ ⌜ c ⌝ ⟩ ]B⋆
        [ v-lookup ← body [ v-c ← ⟨ ⌜ c ⌝ ⟩ ] ]B⋆ [ v-bs ← v₂ ]B⋆)  ≡⟨ ⟨by⟩ (rep⇓≡rep c ⌜c⌝⇓v₁) ⟩⟶

    case v₂ (
      branches [ v-c ← v₁ ]B⋆ [ v-lookup ← body [ v-c ← v₁ ] ]B⋆
        [ v-bs ← v₂ ]B⋆)                                            ⇓⟨ p ⟩■

    v)
  where
  lkup : Exp
  lkup = body [ v-c ← ⌜ c ⌝ ]

  lkup-closed : Closed lkup
  lkup-closed = Closed′-closed-under-subst
    (from-⊎ (closed′? body (v-c ∷ [])))
    (rep-closed c)

  lemma :
    ∀ bs →
    case ⌜ bs ⌝ (
      branches [ v-c ← ⌜ c ⌝ ]B⋆
        [ v-lookup ← lkup ]B⋆ [ v-bs ← ⌜ bs ⌝ ]B⋆) ⇓
    v →
    ∃ λ xs → ∃ λ e → Lookup c bs xs e × v ≡ ⌜ branch c xs e ⌝
  lemma [] (case (const _) (there _ ()) _ _)

  lemma (branch c′ xs′ e′ ∷ bs)
    (case (const {vs = _ ∷ v₁ ∷ []}
             (⌜branch-c′-xs′-e′⌝⇓const-c-branch-es ∷ ⌜bs⌝⇓v₁ ∷ []))
       here (∷ ∷ [])
       (case c-es⇓@(const {es = es} {vs = v₂ ∷ v₃ ∷ v₄ ∷ []} _) here
          (∷ ∷ ∷ []) p)) =
    lemma′ (c Nat.≟ c′) (
      case ⌜ Prelude.if c Nat.≟ c′ then true else false ⌝ (
        branch c-false [] (apply lkup ⌜ bs ⌝) ∷
        branch c-true [] (
          const c-branch (⌜ c′ ⌝ ∷ ⌜ xs′ ⌝ ∷ ⌜ e′ ⌝ ∷ [])) ∷
        [])                                                              ⟶⟨ []⇓⁻¹ (case ∙) (equal-ℕ-correct c c′) ⟩

      case (equal-ℕ ⌜ c ⌝ ⌜ c′ ⌝) (
        branch c-false [] (apply lkup ⌜ bs ⌝) ∷
        branch c-true [] (
          const c-branch (⌜ c′ ⌝ ∷ ⌜ xs′ ⌝ ∷ ⌜ e′ ⌝ ∷ [])) ∷
        [])                                                              ≡⟨ sym $ remove-substs ((lkup , lkup-closed) ∷ []) ⟩⟶

      case
        (equal-ℕ
           (⌜ c ⌝ [ v-lookup ← lkup ] [ v-bs ← ⌜ bs ⌝ ]
              [ v-b ← const c-branch (⌜ c′ ⌝ ∷ ⌜ xs′ ⌝ ∷ ⌜ e′ ⌝ ∷ []) ]
              [ v-underscore ← v₄ ] [ v-underscore ← v₃ ]
              [ v-c′ ← ⌜ c′ ⌝ ])
           ⌜ c′ ⌝) (
        branch c-false [] (
          apply (lkup [ v-bs ← ⌜ bs ⌝ ]
                   [ v-b ← const c-branch
                             (⌜ c′ ⌝ ∷ ⌜ xs′ ⌝ ∷ ⌜ e′ ⌝ ∷ []) ]
                   [ v-underscore ← v₄ ] [ v-underscore ← v₃ ]
                   [ v-c′ ← ⌜ c′ ⌝ ])
            (⌜ bs ⌝ [ v-b ← const c-branch
                              (⌜ c′ ⌝ ∷ ⌜ xs′ ⌝ ∷ ⌜ e′ ⌝ ∷ []) ]
               [ v-underscore ← v₄ ] [ v-underscore ← v₃ ]
               [ v-c′ ← ⌜ c′ ⌝ ])) ∷
        branch c-true [] (
          const c-branch (
            ⌜ c′ ⌝ [ v-underscore ← v₄ ] [ v-underscore ← v₃ ]
              [ v-c′ ← ⌜ c′ ⌝ ] ∷
            ⌜ xs′ ⌝ [ v-underscore ← v₄ ] [ v-underscore ← v₃ ]
              [ v-c′ ← ⌜ c′ ⌝ ] ∷
            ⌜ e′ ⌝ [ v-underscore ← v₄ ] [ v-underscore ← v₃ ]
              [ v-c′ ← ⌜ c′ ⌝ ] ∷
            [])) ∷
        [])                                                              ≡⟨ trans
                                                                              (cong (λ es → case (equal-ℕ (var v-c) (var v-c′)) (
                                                                                       branch c-false [] (apply (var v-lookup) (var v-bs)) ∷
                                                                                       branch c-true [] (var v-b) ∷
                                                                                       [])
                                                                                       [ v-c ← ⌜ c ⌝ ] [ v-lookup ← lkup ] [ v-bs ← ⌜ bs ⌝ ]
                                                                                       [ v-b ← const c-branch es ]
                                                                                       [ v-underscore ← v₄ ] [ v-underscore ← v₃ ]
                                                                                       [ v-c′ ← ⌜ c′ ⌝ ]) $
                                                                               ≡es) $
                                                                            cong₂ (λ v₁ v₂ → case (equal-ℕ (var v-c) (var v-c′)) (
                                                                                     branch c-false [] (apply (var v-lookup) (var v-bs)) ∷
                                                                                     branch c-true [] (var v-b) ∷
                                                                                     [])
                                                                                     [ v-c ← ⌜ c ⌝ ] [ v-lookup ← lkup ] [ v-bs ← v₁ ]
                                                                                     [ v-b ← const c-branch es ]
                                                                                     [ v-underscore ← v₄ ] [ v-underscore ← v₃ ] [ v-c′ ← v₂ ])
                                                                              ≡v₁
                                                                              ≡v₂ ⟩⟶
      case (equal-ℕ (var v-c) (var v-c′)) (
        branch c-false [] (apply (var v-lookup) (var v-bs)) ∷
        branch c-true [] (var v-b) ∷
        [])
        [ v-c ← ⌜ c ⌝ ] [ v-lookup ← lkup ] [ v-bs ← v₁ ]
        [ v-b ← const c-branch es ] [ v-underscore ← v₄ ]
        [ v-underscore ← v₃ ] [ v-c′ ← v₂ ]                              ⇓⟨ p ⟩■

      v)
    where
    ≡v₁ : ⌜ bs ⌝ ≡ v₁
    ≡v₁ = rep⇓≡rep bs ⌜bs⌝⇓v₁

    ≡es′ :
      ⌜ branch c′ xs′ e′ ⌝ ⇓ const c-branch es →
      ⌜ c′ ⌝ ∷ ⌜ xs′ ⌝ ∷ ⌜ e′ ⌝ ∷ [] ≡ es
    ≡es′ (const (⌜c′⌝⇓ ∷ ⌜xs′⌝⇓ ∷ ⌜e′⌝⇓ ∷ [])) =
      cong₂ _∷_ (rep⇓≡rep c′ ⌜c′⌝⇓) $
      cong₂ _∷_ (rep⇓≡rep xs′ ⌜xs′⌝⇓) $
      cong (_∷ []) (rep⇓≡rep e′ ⌜e′⌝⇓)

    ≡es : ⌜ c′ ⌝ ∷ ⌜ xs′ ⌝ ∷ ⌜ e′ ⌝ ∷ [] ≡ es
    ≡es = ≡es′ ⌜branch-c′-xs′-e′⌝⇓const-c-branch-es

    ≡v₂ : ⌜ c′ ⌝ ≡ v₂
    ≡v₂ =
      List.cancel-∷-head $
      proj₂ $
      cancel-const $
      rep⇓≡rep (branch c′ xs′ e′) (
        const c-branch (⌜ c′ ⌝ ∷ ⌜ xs′ ⌝ ∷ ⌜ e′ ⌝ ∷ [])  ⇓⟨ ⌜branch-c′-xs′-e′⌝⇓const-c-branch-es ⟩
        const c-branch es                                ⇓⟨ c-es⇓ ⟩■
        const c-branch (v₂ ∷ v₃ ∷ v₄ ∷ []))

    lemma′ :
      (b : Dec (c ≡ c′)) →
      case ⌜ Prelude.if b then true else false ⌝ (
        branch c-false [] (apply lkup ⌜ bs ⌝) ∷
        branch c-true [] (const c-branch (⌜ c′ ⌝ ∷ ⌜ xs′ ⌝ ∷ ⌜ e′ ⌝ ∷ [])) ∷
        []) ⇓
      v →
      ∃ λ xs → ∃ λ e →
        Lookup c (branch c′ xs′ e′ ∷ bs) xs e × v ≡ ⌜ branch c xs e ⌝
    lemma′ (yes refl)
      (case (const []) (there _ here) [] ⌜branch-c-xs′-e′⌝⇓v) =
        xs′ , e′ , here
      , sym (rep⇓≡rep (branch c xs′ e′) ⌜branch-c-xs′-e′⌝⇓v)
    lemma′ (no c≢c′)
      (case (const []) here []
         (apply {v₂ = v′} (rec lambda) ⌜bs⌝⇓v′ p)) =                     $⟨ lem ⟩

      (∃ λ xs → ∃ λ e → Lookup c bs xs e × v ≡ ⌜ branch c xs e ⌝)        →⟨ Σ-map id (Σ-map id (Σ-map (there c≢c′) id)) ⟩□

      (∃ λ xs → ∃ λ e →
         Lookup c (branch c′ xs′ e′ ∷ bs) xs e × v ≡ ⌜ branch c xs e ⌝)  □
      where
      lem = lemma bs (
        case ⟨ ⌜ bs ⌝ ⟩ (
          branches [ v-c ← ⌜ c ⌝ ]B⋆ [ v-lookup ← lkup ]B⋆
            [ v-bs ← ⟨ ⌜ bs ⌝ ⟩ ]B⋆)                        ≡⟨ ⟨by⟩ (rep⇓≡rep bs ⌜bs⌝⇓v′) ⟩⟶

        case v′ (
          branches [ v-c ← ⌜ c ⌝ ]B⋆ [ v-lookup ← lkup ]B⋆
            [ v-bs ← v′ ]B⋆)                                ⇓⟨ p ⟩■

        v)
    lemma′ (no _) (case (const []) (there c-false≢c-false _) [] _) =
      ⊥-elim $ c-false≢c-false refl
