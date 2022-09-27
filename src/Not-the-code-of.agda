------------------------------------------------------------------------
-- The "not the code of" operator ⌞_⌟
------------------------------------------------------------------------

open import Atom

module Not-the-code-of (atoms : χ-atoms) where

open import Equality.Propositional
open import Prelude hiding (const)
open import Tactic.By.Propositional

open import Injection equality-with-J using (Injective)
open import Maybe equality-with-J
open import Monad equality-with-J

open import Chi         atoms
open import Coding      atoms
import Coding.Instances atoms as I
open import Constants   atoms

open χ-atoms atoms

------------------------------------------------------------------------
-- The "not the code of" operator ⌞_⌟

mutual

  -- An extended variant of the abstract syntax with an extra
  -- constructor, ⌞_⌟.

  data Expᴱ : Type where
    apply  : Expᴱ → Expᴱ → Expᴱ
    lambda : Var → Expᴱ → Expᴱ
    case   : Expᴱ → List Brᴱ → Expᴱ
    rec    : Var → Expᴱ → Expᴱ
    var    : Var → Expᴱ
    const  : Const → List Expᴱ → Expᴱ
    ⌞_⌟    : Exp → Expᴱ

  data Brᴱ : Type where
    branch : Const → List Var → Expᴱ → Brᴱ

mutual

  -- Encoders. Note that the "code" of ⌞ e ⌟ is e.

  ⌜_⌝E : Expᴱ → Exp
  ⌜ apply e₁ e₂ ⌝E = const c-apply (⌜ e₁ ⌝E ∷ ⌜ e₂ ⌝E ∷ [])
  ⌜ lambda x e  ⌝E = const c-lambda (⌜ x ⌝ ∷ ⌜ e ⌝E ∷ [])
  ⌜ case e bs   ⌝E = const c-case (⌜ e ⌝E ∷ ⌜ bs ⌝B⋆ ∷ [])
  ⌜ rec x e     ⌝E = const c-rec (⌜ x ⌝ ∷ ⌜ e ⌝E ∷ [])
  ⌜ var x       ⌝E = const c-var (⌜ x ⌝ ∷ [])
  ⌜ const c es  ⌝E = const c-const (⌜ c ⌝ ∷ ⌜ es ⌝E⋆ ∷ [])
  ⌜ ⌞ e ⌟       ⌝E = e

  ⌜_⌝B : Brᴱ → Exp
  ⌜ branch c xs e ⌝B = const c-branch (⌜ c ⌝ ∷ ⌜ xs ⌝ ∷ ⌜ e ⌝E ∷ [])

  ⌜_⌝E⋆ : List Expᴱ → Exp
  ⌜ []     ⌝E⋆ = const c-nil []
  ⌜ e ∷ es ⌝E⋆ = const c-cons (⌜ e ⌝E ∷ ⌜ es ⌝E⋆ ∷ [])

  ⌜_⌝B⋆ : List Brᴱ → Exp
  ⌜ []     ⌝B⋆ = const c-nil []
  ⌜ b ∷ bs ⌝B⋆ = const c-cons (⌜ b ⌝B ∷ ⌜ bs ⌝B⋆ ∷ [])

-- There is no instance of type Rep Expᴱ Exp, because ⌜_⌝E is not
-- injective.

not-injective : ¬ Injective ⌜_⌝E
not-injective =
  Injective ⌜_⌝E                                                     →⟨ (λ hyp → hyp) ⟩
  (⌜ var v-x ⌝E ≡ ⌜ ⌞ ⌜ var v-x ⌝ ⌟ ⌝E → var v-x ≡ ⌞ ⌜ var v-x ⌝ ⌟)  →⟨ _$ refl ⟩
  var v-x ≡ ⌞ ⌜ var v-x ⌝ ⌟                                          →⟨ (λ ()) ⟩□
  ⊥                                                                  □

------------------------------------------------------------------------
-- A translation from Exp to Expᴱ that does not use ⌞_⌟

private

  mutual

    -- One can "encode" expressions as extended expressions.

    cod : Exp → Expᴱ
    cod (apply e₁ e₂) = apply (cod e₁) (cod e₂)
    cod (lambda x e)  = lambda x (cod e)
    cod (case e bs)   = case (cod e) (codB⋆ bs)
    cod (rec x e)     = rec x (cod e)
    cod (var x)       = var x
    cod (const c es)  = const c (cod⋆ es)

    codB : Br → Brᴱ
    codB (branch c xs e) = branch c xs (cod e)

    cod⋆ : List Exp → List Expᴱ
    cod⋆ []       = []
    cod⋆ (e ∷ es) = cod e ∷ cod⋆ es

    codB⋆ : List Br → List Brᴱ
    codB⋆ []       = []
    codB⋆ (e ∷ es) = codB e ∷ codB⋆ es

  mutual

    -- A decoder.

    dec : Expᴱ → Maybe Exp
    dec (apply e₁ e₂) = apply ⟨$⟩ dec e₁ ⊛ dec e₂
    dec (lambda x e)  = lambda x ⟨$⟩ dec e
    dec (case e bs)   = case ⟨$⟩ dec e ⊛ decB⋆ bs
    dec (rec x e)     = rec x ⟨$⟩ dec e
    dec (var x)       = return (var x)
    dec (const c es)  = const c ⟨$⟩ dec⋆ es
    dec ⌞ _ ⌟         = nothing

    decB : Brᴱ → Maybe Br
    decB (branch c xs e) = branch c xs ⟨$⟩ dec e

    dec⋆ : List Expᴱ → Maybe (List Exp)
    dec⋆ []       = return []
    dec⋆ (e ∷ es) = _∷_ ⟨$⟩ dec e ⊛ dec⋆ es

    decB⋆ : List Brᴱ → Maybe (List Br)
    decB⋆ []       = return []
    decB⋆ (e ∷ es) = _∷_ ⟨$⟩ decB e ⊛ decB⋆ es

  mutual

    -- The decoder decodes properly.

    dec-cod : ∀ e → dec (cod e) ≡ just e
    dec-cod (apply e₁ e₂) =
      apply ⟨$⟩ ⟨ dec (cod e₁) ⟩ ⊛ dec (cod e₂)  ≡⟨ ⟨by⟩ (dec-cod e₁) ⟩
      apply ⟨$⟩ return e₁ ⊛ ⟨ dec (cod e₂) ⟩     ≡⟨ ⟨by⟩ (dec-cod e₂) ⟩
      apply ⟨$⟩ return e₁ ⊛ return e₂            ≡⟨⟩
      return (apply e₁ e₂)                       ∎
    dec-cod (lambda x e) =
      lambda x ⟨$⟩ ⟨ dec (cod e) ⟩  ≡⟨ ⟨by⟩ (dec-cod e) ⟩
      lambda x ⟨$⟩ return e         ≡⟨⟩
      return (lambda x e)           ∎
    dec-cod (case e bs) =
      case ⟨$⟩ ⟨ dec (cod e) ⟩ ⊛ decB⋆ (codB⋆ bs)  ≡⟨ ⟨by⟩ (dec-cod e) ⟩
      case ⟨$⟩ return e ⊛ ⟨ decB⋆ (codB⋆ bs) ⟩     ≡⟨ ⟨by⟩ (dec-codB⋆ bs) ⟩
      case ⟨$⟩ return e ⊛ return bs                ≡⟨⟩
      return (case e bs)                           ∎
    dec-cod (rec x e) =
      rec x ⟨$⟩ ⟨ dec (cod e) ⟩  ≡⟨ ⟨by⟩ (dec-cod e) ⟩
      rec x ⟨$⟩ return e         ≡⟨⟩
      return (rec x e)           ∎
    dec-cod (var x) =
      return (var x)  ∎
    dec-cod (const c es) =
      const c ⟨$⟩ ⟨ dec⋆ (cod⋆ es) ⟩  ≡⟨ ⟨by⟩ (dec-cod⋆ es) ⟩
      const c ⟨$⟩ return es           ≡⟨⟩
      return (const c es)             ∎

    dec-codB : ∀ b → decB (codB b) ≡ just b
    dec-codB (branch c xs e) =
      branch c xs ⟨$⟩ ⟨ dec (cod e) ⟩  ≡⟨ ⟨by⟩ (dec-cod e) ⟩
      branch c xs ⟨$⟩ return e         ≡⟨⟩
      return (branch c xs e)           ∎

    dec-cod⋆ : ∀ es → dec⋆ (cod⋆ es) ≡ just es
    dec-cod⋆ [] =
      return []  ∎
    dec-cod⋆ (e ∷ es) =
      _∷_ ⟨$⟩ ⟨ dec (cod e) ⟩ ⊛ dec⋆ (cod⋆ es)  ≡⟨ ⟨by⟩ (dec-cod e) ⟩
      _∷_ ⟨$⟩ return e ⊛ ⟨ dec⋆ (cod⋆ es) ⟩     ≡⟨ ⟨by⟩ (dec-cod⋆ es) ⟩
      _∷_ ⟨$⟩ return e ⊛ return es              ≡⟨⟩
      return (e ∷ es)                           ∎

    dec-codB⋆ : ∀ bs → decB⋆ (codB⋆ bs) ≡ just bs
    dec-codB⋆ [] =
      return []  ∎
    dec-codB⋆ (b ∷ bs) =
      _∷_ ⟨$⟩ ⟨ decB (codB b) ⟩ ⊛ decB⋆ (codB⋆ bs)  ≡⟨ ⟨by⟩ (dec-codB b) ⟩
      _∷_ ⟨$⟩ return b ⊛ ⟨ decB⋆ (codB⋆ bs) ⟩       ≡⟨ ⟨by⟩ (dec-codB⋆ bs) ⟩
      _∷_ ⟨$⟩ return b ⊛ return bs                  ≡⟨⟩
      return (b ∷ bs)                               ∎

-- A translation from Exp to Expᴱ that does not use ⌞_⌟.

code-Exp-Expᴱ : Code Exp Expᴱ
code-Exp-Expᴱ .code        = cod
code-Exp-Expᴱ .decode      = dec
code-Exp-Expᴱ .decode∘code = dec-cod

code-Br-Brᴱ : Code Br Brᴱ
code-Br-Brᴱ .code        = codB
code-Br-Brᴱ .decode      = decB
code-Br-Brᴱ .decode∘code = dec-codB

code-List-Exp-List-Expᴱ : Code (List Exp) (List Expᴱ)
code-List-Exp-List-Expᴱ .code        = cod⋆
code-List-Exp-List-Expᴱ .decode      = dec⋆
code-List-Exp-List-Expᴱ .decode∘code = dec-cod⋆

code-List-Br-List-Brᴱ : Code (List Br) (List Brᴱ)
code-List-Br-List-Brᴱ .code        = codB⋆
code-List-Br-List-Brᴱ .decode      = decB⋆
code-List-Br-List-Brᴱ .decode∘code = dec-codB⋆

instance

  -- A translation from Exp to Expᴱ that does not use ⌞_⌟.

  rep-Exp-Expᴱ : Rep Exp Expᴱ
  rep-Exp-Expᴱ = rep ⦃ code-Exp-Expᴱ ⦄

  rep-Br-Brᴱ : Rep Br Brᴱ
  rep-Br-Brᴱ = rep ⦃ code-Br-Brᴱ ⦄

  rep-List-Exp-List-Expᴱ : Rep (List Exp) (List Expᴱ)
  rep-List-Exp-List-Expᴱ = rep ⦃ code-List-Exp-List-Expᴱ ⦄

  rep-List-Br-List-Brᴱ : Rep (List Br) (List Brᴱ)
  rep-List-Br-List-Brᴱ = rep ⦃ code-List-Br-List-Brᴱ ⦄

mutual

  -- If the translation above is applied to an expression and ⌜_⌝E is
  -- applied to the result, then the result is the same as if the
  -- expression had been encoded in the regular way.

  ⌜⌜⌝⌝E≡⌜⌝ : (e : Exp) → ⌜ ⌜ e ⌝ ⌝E ≡ ⌜ e ⌝
  ⌜⌜⌝⌝E≡⌜⌝ (apply e₁ e₂) =
    Exp.const c-apply (⟨ ⌜ ⌜ e₁ ⌝ ⌝E ⟩ ∷ ⌜ ⌜ e₂ ⌝ ⌝E ∷ [])  ≡⟨ ⟨by⟩ (⌜⌜⌝⌝E≡⌜⌝ e₁) ⟩
    const c-apply (⌜ e₁ ⌝ ∷ ⟨ ⌜ ⌜ e₂ ⌝ ⌝E ⟩ ∷ [])           ≡⟨ ⟨by⟩ (⌜⌜⌝⌝E≡⌜⌝ e₂) ⟩∎
    const c-apply (⌜ e₁ ⌝ ∷ ⌜ e₂ ⌝ ∷ [])                    ∎
  ⌜⌜⌝⌝E≡⌜⌝ (lambda x e) =
    Exp.const c-lambda (⌜ x ⌝ ∷ ⟨ ⌜ ⌜ e ⌝ ⌝E ⟩ ∷ [])  ≡⟨ ⟨by⟩ (⌜⌜⌝⌝E≡⌜⌝ e) ⟩∎
    const c-lambda (⌜ x ⌝ ∷ ⌜ e ⌝ ∷ [])               ∎
  ⌜⌜⌝⌝E≡⌜⌝ (case e bs) =
    Exp.const c-case (⟨ ⌜ ⌜ e ⌝ ⌝E ⟩ ∷ ⌜ ⌜ bs ⌝ ⌝B⋆ ∷ [])  ≡⟨ ⟨by⟩ (⌜⌜⌝⌝E≡⌜⌝ e) ⟩
    const c-case (⌜ e ⌝ ∷ ⟨ ⌜ ⌜ bs ⌝ ⌝B⋆ ⟩ ∷ [])           ≡⟨ ⟨by⟩ (⌜⌜⌝⌝B⋆≡⌜⌝ bs) ⟩∎
    const c-case (⌜ e ⌝ ∷ ⌜ bs ⌝ ∷ [])                     ∎
  ⌜⌜⌝⌝E≡⌜⌝ (rec x e) =
    Exp.const c-rec (⌜ x ⌝ ∷ ⟨ ⌜ ⌜ e ⌝ ⌝E ⟩ ∷ [])  ≡⟨ ⟨by⟩ (⌜⌜⌝⌝E≡⌜⌝ e) ⟩∎
    const c-rec (⌜ x ⌝ ∷ ⌜ e ⌝ ∷ [])               ∎
  ⌜⌜⌝⌝E≡⌜⌝ (var x) =
    ⌜ var x ⌝  ∎
  ⌜⌜⌝⌝E≡⌜⌝ (const c es) =
    Exp.const c-const (⌜ c ⌝ ∷ ⟨ ⌜ ⌜ es ⌝ ⌝E⋆ ⟩ ∷ [])  ≡⟨ ⟨by⟩ (⌜⌜⌝⌝E⋆≡⌜⌝ es) ⟩∎
    const c-const (⌜ c ⌝ ∷ ⌜ es ⌝ ∷ [])                ∎

  ⌜⌜⌝⌝B≡⌜⌝ : (b : Br) → ⌜ ⌜ b ⌝ ⌝B ≡ ⌜ b ⌝
  ⌜⌜⌝⌝B≡⌜⌝ (branch c xs e) =
    Exp.const c-branch (⌜ c ⌝ ∷ ⌜ xs ⌝ ∷ ⟨ ⌜ ⌜ e ⌝ ⌝E ⟩ ∷ [])  ≡⟨ ⟨by⟩ (⌜⌜⌝⌝E≡⌜⌝ e) ⟩∎
    const c-branch (⌜ c ⌝ ∷ ⌜ xs ⌝ ∷ ⌜ e ⌝ ∷ [])               ∎

  ⌜⌜⌝⌝E⋆≡⌜⌝ : (es : List Exp) → ⌜ ⌜ es ⌝ ⌝E⋆ ≡ ⌜ es ⌝
  ⌜⌜⌝⌝E⋆≡⌜⌝ [] =
    ⌜ [] ⦂ List Exp ⌝  ∎
  ⌜⌜⌝⌝E⋆≡⌜⌝ (e ∷ es) =
    Exp.const c-cons (⟨ ⌜ ⌜ e ⌝ ⌝E ⟩ ∷ ⌜ ⌜ es ⌝ ⌝E⋆ ∷ [])  ≡⟨ ⟨by⟩ (⌜⌜⌝⌝E≡⌜⌝ e) ⟩
    const c-cons (⌜ e ⌝ ∷ ⟨ ⌜ ⌜ es ⌝ ⌝E⋆ ⟩ ∷ [])           ≡⟨ ⟨by⟩ (⌜⌜⌝⌝E⋆≡⌜⌝ es) ⟩∎
    const c-cons (⌜ e ⌝ ∷ ⌜ es ⌝ ∷ [])                     ∎

  ⌜⌜⌝⌝B⋆≡⌜⌝ : (bs : List Br) → ⌜ ⌜ bs ⌝ ⌝B⋆ ≡ ⌜ bs ⌝
  ⌜⌜⌝⌝B⋆≡⌜⌝ [] =
    ⌜ [] ⦂ List Br ⌝  ∎
  ⌜⌜⌝⌝B⋆≡⌜⌝ (b ∷ bs) =
    Exp.const c-cons (⟨ ⌜ ⌜ b ⌝ ⌝B ⟩ ∷ ⌜ ⌜ bs ⌝ ⌝B⋆ ∷ [])  ≡⟨ ⟨by⟩ (⌜⌜⌝⌝B≡⌜⌝ b) ⟩
    const c-cons (⌜ b ⌝ ∷ ⟨ ⌜ ⌜ bs ⌝ ⌝B⋆ ⟩ ∷ [])           ≡⟨ ⟨by⟩ (⌜⌜⌝⌝B⋆≡⌜⌝ bs) ⟩∎
    const c-cons (⌜ b ⌝ ∷ ⌜ bs ⌝ ∷ [])                     ∎
