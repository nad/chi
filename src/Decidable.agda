------------------------------------------------------------------------
-- Some aspects of the semantics are decidable
------------------------------------------------------------------------

module Decidable where

open import Dec
open import Equality.Propositional
import Logical-equivalence
open import Prelude hiding (const)
open import Tactic.By.Propositional

open import Function-universe equality-with-J hiding (id)
open import Nat equality-with-J as Nat
  using (_≤_; _<_; _∎≤; step-≤; step-≡≤; finally-≤)
open import Nat.Solver equality-with-J

-- To simplify the development, let's work with actual natural numbers
-- as variables and constants (see
-- Atom.one-can-restrict-attention-to-χ-ℕ-atoms).

open import Atom

open import Cancellation    χ-ℕ-atoms
open import Chi             χ-ℕ-atoms
open import Derivation-size χ-ℕ-atoms
open import Deterministic   χ-ℕ-atoms
open import Reasoning       χ-ℕ-atoms
open import Termination     χ-ℕ-atoms
open import Values          χ-ℕ-atoms

-- The Lookup relation is decidable (in a certain sense).

Lookup-decidable :
  ∀ c bs → Dec (∃ λ xs → ∃ λ e → Lookup c bs xs e)
Lookup-decidable c [] = no λ where
  (_ , _ , ())
Lookup-decidable c (branch c′ xs e ∷ bs) =
  case c Nat.≟ c′ of λ where
    (yes refl) → yes (xs , e , here)
    (no c≢c′)  → case Lookup-decidable c bs of λ where
      (yes (xs , e , p)) → yes (xs , e , there c≢c′ p)
      (no p) → no λ where
        (xs , e , here)      → ⊥-elim $ c≢c′ refl
        (xs , e , there _ q) → p (xs , e , q)

-- The relation _[_←_]↦_ is decidable (in a certain sense).

[←]↦-decidable : ∀ e xs es → Dec (∃ λ e′ → e [ xs ← es ]↦ e′)
[←]↦-decidable e []       []        = yes (e , [])
[←]↦-decidable _ []       (_ ∷ _)   = no (λ { (_ , ()) })
[←]↦-decidable _ (_ ∷ _)  []        = no (λ { (_ , ()) })
[←]↦-decidable e (x ∷ xs) (e′ ∷ es) =
  case [←]↦-decidable e xs es of λ where
    (yes (e″ , p)) → yes (e″ [ x ← e′ ] , ∷ p)
    (no p)         → no λ where
      (_ , ∷ q) → p (_ , q)

private

  -- Definitions used to prove terminates-in.

  P : ℕ → Type
  P n = (e : Exp) → Dec (e ⇓≤ n)

  terminates-in⋆′ :
    (n : ℕ) → (∀ {m} → m ≤ n → P m) → (es : List Exp) → Dec (es ⇓⋆≤ n)
  terminates-in⋆′ n _ [] = yes
    ( []
    , []
    , (0  ≤⟨ Nat.zero≤ n ⟩∎
       n  ∎≤)
    )
  terminates-in⋆′ n ih (e ∷ es) = case ih (n ∎≤) e of λ where
    (no p) → no (
      e ∷ es ⇓⋆≤ n  →⟨ (λ { (v ∷ vs , p ∷ ps , |p∷ps|≤n) →
                              v
                            , (e  ⇓⟨ p ⟩■
                               v)
                            , (size p             ≤⟨ Nat.m≤m+n _ _ ⟩
                               size p + size⋆ ps  ≤⟨ |p∷ps|≤n ⟩∎
                               n                  ∎≤) }) ⟩
      e ⇓≤ n        →⟨ p ⟩□
      ⊥             □)
    (yes (v , p , |p|≤n)) →
      case terminates-in⋆′
             (n ∸ size p)
             (λ {m = m} →
                m ≤ n ∸ size p  →⟨ flip Nat.≤-trans $ Nat.∸≤ _ (size p) ⟩
                m ≤ n           →⟨ ih ⟩□
                P m             □)
             es of λ where
        (no q) → no (
          e ∷ es ⇓⋆≤ n       →⟨ (λ { (v ∷ vs , q ∷ qs , |q∷qs|≤n) →
                                       vs
                                     , qs
                                     , (size⋆ qs                        ≡⟨ trans (sym $ Nat.+∸≡ (size q)) $
                                                                           cong (_∸ size q) $ Nat.+-comm (size⋆ qs) ⟩≤
                                        size q + size⋆ qs ∸ ⟨ size q ⟩  ≡⟨ ⟨by⟩ (size-unique p q) ⟩≤
                                        size q + size⋆ qs ∸ size p      ≤⟨ |q∷qs|≤n Nat.∸-mono (size p ∎≤) ⟩∎
                                        n ∸ size p                      ∎≤) }) ⟩
          es ⇓⋆≤ n ∸ size p  →⟨ q ⟩□
          ⊥                  □)
        (yes (vs , ps , |ps|≤n∸|p|)) → yes
          ( v ∷ vs
          , p ∷ ps
          , (size p + size⋆ ps      ≤⟨ Nat.≤-refl Nat.+-mono |ps|≤n∸|p| ⟩
             size p + (n ∸ size p)  ≡⟨ trans (Nat.+-comm (size p)) $
                                       Nat.∸+≡ |p|≤n ⟩≤
             n                      ∎≤)
          )

  terminates-in′ : (n : ℕ) → (∀ {m} → m < n → P m) → P n
  terminates-in′ zero _ e = no (
    e ⇓≤ 0                                               →⟨ (λ (v , p , ≤0) → v , p , Nat.≤-antisymmetric ≤0 (Nat.zero≤ _) , 1≤size p) ⟩
    (∃ λ v → ∃ λ (p : e ⇓ v) → size p ≡ 0 × 1 ≤ size p)  →⟨ (λ (_ , _ , ≡0 , 1≤) → subst (1 ≤_) ≡0 1≤) ⟩
    0 < 0                                                →⟨ Nat.≮0 _ ⟩□
    ⊥                                                    □)

  terminates-in′ n _ (var x) = no (
    var x ⇓≤ n  →⟨ (λ { (_ , () , _) }) ⟩□
    ⊥           □)

  terminates-in′ (suc n) _ (lambda x e) = yes
    ( lambda x e
    , (lambda x e ⇓⟨ lambda ⟩■
       lambda x e)
    , (1      ≤⟨ Nat.suc≤suc $ Nat.zero≤ n ⟩∎
       1 + n  ∎≤)
    )

  terminates-in′ (suc n) ih (rec x e) =
                                  $⟨ ih (suc n ∎≤) (e [ x ← rec x e ]) ⟩
    Dec (e [ x ← rec x e ] ⇓≤ n)  →⟨ (Dec-map $ ∃-cong λ _ → record
                                        { to   = Σ-map rec Nat.suc≤suc
                                        ; from = λ { (rec p , q) → p , Nat.suc≤suc⁻¹ q }
                                        }) ⟩□
    Dec (rec x e ⇓≤ suc n)        □

  terminates-in′ (suc n) ih (apply e₁ e₂) =
    case ih (suc n ∎≤) e₁ of λ where
      (no p) → no (
        apply e₁ e₂ ⇓≤ suc n  →⟨ (λ { (_ , apply {x = x} {e = e} p q r , 1+|p|+|q|+|r|≤1+n) →
                                        lambda x e
                                      , (e₁          ⇓⟨ p ⟩■
                                         lambda x e)
                                      , (size p                    ≤⟨ Nat.≤-trans (Nat.m≤m+n _ _) $
                                                                      Nat.m≤m+n _ _ ⟩
                                         size p + size q + size r  ≤⟨ Nat.suc≤suc⁻¹ 1+|p|+|q|+|r|≤1+n ⟩∎
                                         n                         ∎≤) }) ⟩
        e₁ ⇓≤ n               →⟨ p ⟩□
        ⊥                     □)
      (yes (v₁ , p , |p|≤n)) → case ⇓-Value p of λ where
        (const _ _) → no (
          apply e₁ e₂ ⇓≤ suc n               →⟨ (λ { (_ , apply p _ _ , _) → _ , _ , p }) ⟩
          (∃ λ x → ∃ λ e → e₁ ⇓ lambda x e)  →⟨ Σ-map id $ Σ-map id $ ⇓-deterministic p ⟩
          (∃ λ x → ∃ λ e → v₁ ≡ lambda x e)  →⟨ (λ { (_ , _ , ()) }) ⟩□
          ⊥                                  □)
        (lambda x e) →
          case ih (suc (n ∸ size p)  ≤⟨ Nat.suc≤suc (Nat.∸≤ _ (size p)) ⟩∎
                   suc n             ∎≤)
                  e₂ of λ where
            (no q) → no (
              apply e₁ e₂ ⇓≤ suc n  →⟨ (λ { (_ , apply {v₂ = v₂} p′ q′ r′ , 1+|p′|+|q′|+|r′|≤1+n) →
                                              v₂
                                            , (e₂  ⇓⟨ q′ ⟩■
                                               v₂)
                                            , (size q′                                  ≡⟨ trans (sym $ Nat.+∸≡ (size p)) $
                                                                                           cong (_∸ size p) $ Nat.+-comm (size q′) ⟩≤
                                               size p + size q′ ∸ size p                ≤⟨ Nat.m≤m+n (size p + size q′) (size r′)
                                                                                             Nat.∸-mono
                                                                                           (size p ∎≤) ⟩
                                               ⟨ size p ⟩ + size q′ + size r′ ∸ size p  ≡⟨ ⟨by⟩ (size-unique p p′) ⟩≤
                                               size p′ + size q′ + size r′ ∸ size p     ≤⟨ Nat.suc≤suc⁻¹ 1+|p′|+|q′|+|r′|≤1+n
                                                                                             Nat.∸-mono
                                                                                           (size p ∎≤) ⟩∎
                                               n ∸ size p                               ∎≤) }) ⟩
              e₂ ⇓≤ n ∸ size p      →⟨ q ⟩□
              ⊥                     □)
            (yes (v₂ , q , |q|≤n∸|p|)) →
              case ih (suc (n ∸ (size p + size q))  ≤⟨ Nat.suc≤suc (Nat.∸≤ _ (size p + size q)) ⟩∎
                       suc n                        ∎≤)
                      (e [ x ← v₂ ]) of λ where
                (no r) → no (
                  apply e₁ e₂ ⇓≤ suc n                   →⟨ (λ { (v , apply {x = x′} {e = e′} {v₂ = v₂′} p′ q′ r′ , 1+|p′|+|q′|+|r′|≤1+n) →
                                                                 case apply-deterministic p q p′ q′ of λ (_ , lem) →
                                                                     v
                                                                   , (e [ x ← v₂ ]     ≡⟨ lem ⟩⟶
                                                                      e′ [ x′ ← v₂′ ]  ⇓⟨ r′ ⟩■
                                                                      v)
                                                                   , (size (_ ≡⟨ lem ⟩⟶ _ ⇓⟨ r′ ⟩■ _)  ≡⟨ size-≡⟨⟩⟶ lem ⟩≤

                                                                      size r′                          ≡⟨ trans (sym $ Nat.+∸≡ (size p + _)) $
                                                                                                          cong (_∸ (size p + size q)) $
                                                                                                          solve 3 (λ p q r′ → r′ :+ (p :+ q) :=
                                                                                                                              p :+ q :+ r′)
                                                                                                            refl (size p) (size q) (size r′) ⟩≤
                                                                      size p + size q + size r′ ∸
                                                                        (size p + size q)              ≡⟨ cong₂ (λ p′ q′ → p′ + q′ + size r′ ∸
                                                                                                                           (size p + _))
                                                                                                            (size-unique p p′)
                                                                                                            (size-unique q q′) ⟩≤
                                                                      size p′ + size q′ + size r′ ∸
                                                                        (size p + size q)              ≤⟨ Nat.suc≤suc⁻¹ 1+|p′|+|q′|+|r′|≤1+n
                                                                                                            Nat.∸-mono
                                                                                                          (size p + _ ∎≤) ⟩∎
                                                                      n ∸ (size p + size q)            ∎≤) }) ⟩
                  e [ x ← v₂ ] ⇓≤ n ∸ (size p + size q)  →⟨ r ⟩□
                  ⊥                                      □)
                (yes (v , r , |r|≤n∸|p|+|q|)) → yes (
                    v
                  , (apply e₁ e₂  ⇓⟨ apply p q r ⟩■
                     v)
                  , (1 + size p + size q + size r                   ≤⟨ (1 + size p + _ ∎≤) Nat.+-mono |r|≤n∸|p|+|q| ⟩

                     1 + size p + size q + (n ∸ (size p + size q))  ≡⟨ cong suc $
                                                                       trans (Nat.+-comm (size p + _)) $
                                                                       Nat.∸+≡ (
                       size p + size q                                   ≤⟨ Nat.≤-refl Nat.+-mono |q|≤n∸|p| ⟩
                       size p + (n ∸ size p)                             ≡⟨ trans (Nat.+-comm (size p)) (Nat.∸+≡ |p|≤n) ⟩≤
                       n                                                 ∎≤) ⟩≤

                     1 + n                                          ∎≤))

  terminates-in′ (suc n) ih (case e bs) =
    case ih (suc n ∎≤) e of λ where
      (no p) → no (
        case e bs ⇓≤ suc n  →⟨ (λ { (_ , case {c = c} {es = vs} p _ _ q , 1+|p|+|q|≤1+n) →
                                      const c vs
                                    , (e           ⇓⟨ p ⟩■
                                       const c vs)
                                    , (size p           ≤⟨ Nat.m≤m+n _ _ ⟩
                                       size p + size q  ≤⟨ Nat.suc≤suc⁻¹ 1+|p|+|q|≤1+n ⟩∎
                                       n                ∎≤) }) ⟩
        e ⇓≤ n              →⟨ p ⟩□
        ⊥                   □)
      (yes (v₁ , p , |p|≤n)) → case ⇓-Value p of λ where
        (lambda _ _) → no (
          case e bs ⇓≤ suc n                  →⟨ (λ { (_ , case p _ _ _ , _) → _ , _ , p }) ⟩
          (∃ λ c → ∃ λ vs → e ⇓ const c vs)   →⟨ Σ-map id $ Σ-map id $ ⇓-deterministic p ⟩
          (∃ λ c → ∃ λ vs → v₁ ≡ const c vs)  →⟨ (λ { (_ , _ , ()) }) ⟩□
          ⊥                                   □)
        (const c {es = vs} _) → case Lookup-decidable c bs of λ where
          (no q) → no (
            case e bs ⇓≤ suc n                   →⟨ (λ { (v , case {c = c′} {xs = xs} {e′ = e′} p′ q′ _ _ , _) →
                                                           xs
                                                         , e′
                                                         , (                    $⟨ q′ ⟩
                                                            Lookup c′ bs xs e′  →⟨ subst (λ c → Lookup c bs xs e′) $ sym $ proj₁ $
                                                                                   cancel-const $ ⇓-deterministic p p′ ⟩□
                                                            Lookup c bs xs e′   □) }) ⟩
            (∃ λ xs → ∃ λ e → Lookup c bs xs e)  →⟨ q ⟩□
            ⊥                                    □)
          (yes (xs , e′ , q)) → case [←]↦-decidable e′ xs vs of λ where
            (no r) → no (
              case e bs ⇓≤ suc n             →⟨ (λ { ( v
                                                     , case {es = vs′} {xs = xs′} {e′ = e′′} {e″ = e‴} p′ q′ r′ _
                                                     , _
                                                     ) →
                                                       e‴
                                                     , (                       $⟨ r′ ⟩
                                                        e′′ [ xs′ ← vs′ ]↦ e‴  →⟨ proj₂ $ case-deterministic₁ p q p′ q′ ⟩□
                                                        e′ [ xs ← vs ]↦ e‴     □) }) ⟩
              (∃ λ e″ → e′ [ xs ← vs ]↦ e″)  →⟨ r ⟩□
              ⊥                              □)
            (yes (e″ , r)) →
              case ih (suc (n ∸ size p)  ≤⟨ Nat.suc≤suc (Nat.∸≤ _ (size p)) ⟩∎
                       suc n             ∎≤)
                      e″ of λ where
                (no s) → no (
                  case e bs ⇓≤ suc n  →⟨ (λ { (v , case {c = c′} {es = vs′} {xs = xs′} {e′ = e′′} {e″ = e‴} p′ q′ r′ s′ , 1+|p′|+|s′|≤1+n) →
                                              case case-deterministic₂ p q r p′ q′ r′ of λ (_ , e″≡e‴) →
                                                  v
                                                , (e″  ≡⟨ e″≡e‴ ⟩⟶
                                                   e‴  ⇓⟨ s′ ⟩■
                                                   v)
                                                , (size (_ ≡⟨ e″≡e‴ ⟩⟶ _ ⇓⟨ s′ ⟩■ _)  ≡⟨ size-≡⟨⟩⟶ {q = s′} e″≡e‴ ⟩≤
                                                   size s′                            ≡⟨ trans (sym $ Nat.+∸≡ (size p′)) $
                                                                                         cong (_∸ size p′) $ Nat.+-comm (size s′) ⟩≤
                                                   size p′ + size s′ ∸ size p′        ≤⟨ Nat.suc≤suc⁻¹ 1+|p′|+|s′|≤1+n Nat.∸-mono (size p′ ∎≤) ⟩
                                                   n ∸ size p′                        ≡⟨ cong (n ∸_) $ size-unique p′ p ⟩≤
                                                   n ∸ size p                         ∎≤) }) ⟩
                  e″ ⇓≤ n ∸ size p    →⟨ s ⟩□
                  ⊥                   □)
                (yes (v , s , |s|≤n∸|p|)) → yes
                  ( v
                  , case p q r s
                  , (1 + size p + size s        ≤⟨ (1 + size p ∎≤) Nat.+-mono |s|≤n∸|p| ⟩
                     1 + size p + (n ∸ size p)  ≡⟨ cong suc $
                                                   trans (Nat.+-comm (size p)) $
                                                   Nat.∸+≡ |p|≤n ⟩≤
                     1 + n                      ∎≤)
                  )

  terminates-in′ (suc n) ih (const c es) =
                               $⟨ terminates-in⋆′ n
                                    (λ {m = m} →
                                       m ≤ n      →⟨ Nat.suc≤suc ⟩
                                       m < suc n  →⟨ ih ⟩□
                                       P m        □)
                                    es ⟩
    Dec (es ⇓⋆≤ n)             →⟨ Dec-map record
                                    { to   = Σ-map (const c) $ Σ-map const Nat.suc≤suc
                                    ; from = λ { (const c vs , const p , q) →
                                                 vs , p , Nat.suc≤suc⁻¹ q }
                                    } ⟩□
    Dec (const c es ⇓≤ suc n)  □

-- It is decidable whether an expression terminates in at most a given
-- number of (derivation) steps (as defined by size).

terminates-in : (e : Exp) (n : ℕ) → Dec (e ⇓≤ n)
terminates-in = flip $ Nat.well-founded-elim P terminates-in′

-- It is decidable whether a list of expressions terminates in at most
-- a given number of (derivation) steps (as defined by size⋆).

terminates-in⋆ : (es : List Exp) (n : ℕ) → Dec (es ⇓⋆≤ n)
terminates-in⋆ es n = terminates-in⋆′ n (λ _ e → terminates-in e _) es

-- A unary variant of terminates-in that returns a boolean.

terminates-in-Bool : Exp × ℕ → Bool
terminates-in-Bool (e , n) =
  if terminates-in e n then true else false

-- If terminates-in-Bool (e , n) is equal to true, then e terminates
-- in at most n steps.

terminates-in-Bool-true :
  ∀ {e n} → terminates-in-Bool (e , n) ≡ true → e ⇓≤ n
terminates-in-Bool-true {e = e} {n = n} hyp =
  lemma (terminates-in e n) hyp
  where
  lemma : (b : Dec (e ⇓≤ n)) → if b then true else false ≡ true → e ⇓≤ n
  lemma (yes p) _ = p

-- If terminates-in-Bool (e , n) is equal to false, then e does not
-- terminate in at most n steps.

terminates-in-Bool-false :
  ∀ {e n} → terminates-in-Bool (e , n) ≡ false → ¬ e ⇓≤ n
terminates-in-Bool-false {e = e} {n = n} hyp =
  lemma (terminates-in e n) hyp
  where
  lemma :
    (b : Dec (e ⇓≤ n)) → if b then true else false ≡ false → ¬ e ⇓≤ n
  lemma (no p) _ = p
