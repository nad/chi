------------------------------------------------------------------------
-- Encoders and decoders
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Atom

module Coding (atoms : χ-atoms) where

open import Equality.Propositional
open import Prelude hiding (const)
open import Tactic.By

open import Bijection equality-with-J as Bijection using (_↔_)
open import Equality.Decision-procedures equality-with-J
open import Function-universe equality-with-J hiding (id; _∘_)
open import Injection equality-with-J using (Injective)
open import List equality-with-J using (foldr)
open import Maybe equality-with-J
open import Monad equality-with-J

open import Chi            atoms
open import Constants      atoms
open import Free-variables atoms
open import Values         atoms

open χ-atoms atoms

------------------------------------------------------------------------
-- General definitions

-- Representation functions.

record Rep {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    -- Representation function.
    ⌜_⌝ : A → B

    -- ⌜_⌝ is injective.
    rep-injective : Injective ⌜_⌝

open Rep ⦃ … ⦄ public

-- An identity encoder.

id-rep : ∀ {a} {A : Set a} → Rep A A
id-rep = record
  { ⌜_⌝           = id
  ; rep-injective = id
  }

-- Composition of representation functions.

infixr 9 _∘-rep_

_∘-rep_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
          Rep B C → Rep A B → Rep A C
r₁ ∘-rep r₂ = record
  { ⌜_⌝           = R₁.⌜_⌝ ∘ R₂.⌜_⌝
  ; rep-injective = λ {x y} →
      R₁.⌜ R₂.⌜ x ⌝ ⌝ ≡ R₁.⌜ R₂.⌜ y ⌝ ⌝  ↝⟨ R₁.rep-injective ⟩
      R₂.⌜ x ⌝ ≡ R₂.⌜ y ⌝                ↝⟨ R₂.rep-injective ⟩□
      x ≡ y                              □
  }
  where
  module R₁ = Rep r₁
  module R₂ = Rep r₂

-- Encoder/decoder pairs.

record Code {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    -- Encoder.
    code : A → B

    -- Partial decoder.
    decode : B → Maybe A

    -- The decoder must decode encoded values successfully.
    decode∘code : ∀ x → decode (code x) ≡ just x

  -- The encoder is injective.

  code-injective : Injective code
  code-injective {x} {y} eq = ⊎.cancel-inj₂ (
    just x           ≡⟨ by decode∘code ⟩
    decode (code x)  ≡⟨ by eq ⟩
    decode (code y)  ≡⟨ by decode∘code ⟩∎
    just y           ∎)

  -- Encoder/decoder pairs can be turned into representation
  -- functions.

  rep : Rep A B
  rep = record
    { ⌜_⌝           = code
    ; rep-injective = code-injective
    }

open Code ⦃ … ⦄ public

-- Converts bijections to encoders.

↔→Code : ∀ {a b} {A : Set a} {B : Set b} → A ↔ B → Code A B
↔→Code A↔B = record
  { code        = to
  ; decode      = λ b → just (from b)
  ; decode∘code = λ a →
      just (from (to a))  ≡⟨ cong just (left-inverse-of a) ⟩
      just a              ∎
  }
  where
  open _↔_ A↔B

-- An identity encoder.

id-code : ∀ {a} {A : Set a} → Code A A
id-code = ↔→Code Bijection.id

-- Composition of encoders.

infixr 9 _∘-code_

_∘-code_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
           Code B C → Code A B → Code A C
c₁ ∘-code c₂ = record
  { code        = C₁.code ∘ C₂.code
  ; decode      = λ c → C₁.decode c >>=′ C₂.decode
  ; decode∘code = λ a →
      C₁.decode (C₁.code (C₂.code a)) >>=′ C₂.decode  ≡⟨ cong (_>>=′ _) (C₁.decode∘code (C₂.code a)) ⟩
      return (C₂.code a) >>=′ C₂.decode               ≡⟨⟩
      C₂.decode (C₂.code a)                           ≡⟨ by C₂.decode∘code ⟩∎
      return a                                        ∎
  }
  where
  module C₁ = Code c₁
  module C₂ = Code c₂

------------------------------------------------------------------------
-- Some general definitions related to χ

-- Constructor applications can be encoded as expressions (that are
-- also constructor applications).

code-Consts : ∃ λ (cd : Code Consts Exp) →
                ∀ c → Constructor-application (Code.code cd c)
code-Consts = record
  { code        = cd
  ; decode      = dc
  ; decode∘code = dc∘cd
  } , cd-cs
  where
  mutual

    cd : Consts → Exp
    cd (const c cs) = const c (cd⋆ cs)

    cd⋆ : List Consts → List Exp
    cd⋆ []       = []
    cd⋆ (c ∷ cs) = cd c ∷ cd⋆ cs

  mutual

    cd-cs : ∀ c → Constructor-application (cd c)
    cd-cs (const c cs) = const c (cd⋆-cs cs)

    cd⋆-cs : ∀ cs → Constructor-applications (cd⋆ cs)
    cd⋆-cs []       = []
    cd⋆-cs (c ∷ cs) = cd-cs c ∷ cd⋆-cs cs

  mutual

    dc : Exp → Maybe Consts
    dc (const c es) = const c ⟨$⟩ dc⋆ es
    dc _            = nothing

    dc⋆ : List Exp → Maybe (List Consts)
    dc⋆ []       = return []
    dc⋆ (e ∷ es) = _∷_ ⟨$⟩ dc e ⊛ dc⋆ es

  mutual

    dc∘cd : ∀ c → dc (cd c) ≡ just c
    dc∘cd (const c cs) =
      const c ⟨$⟩ dc⋆ (cd⋆ cs)  ≡⟨ by (dc∘cd⋆ cs) ⟩
      const c ⟨$⟩ return cs     ≡⟨ refl ⟩∎
      return (const c cs)       ∎

    dc∘cd⋆ : ∀ cs → dc⋆ (cd⋆ cs) ≡ just cs
    dc∘cd⋆ [] = refl
    dc∘cd⋆ (c ∷ cs) =
      _∷_ ⟨$⟩ dc (cd c) ⊛ dc⋆ (cd⋆ cs)  ≡⟨ by (dc∘cd c) ⟩
      _∷_ ⟨$⟩ return c ⊛ dc⋆ (cd⋆ cs)   ≡⟨ by (dc∘cd⋆ cs) ⟩
      _∷_ ⟨$⟩ return c ⊛ return cs      ≡⟨⟩
      return (c ∷ cs)                   ∎

-- Converts instances of the form Rep A Consts to Rep A Exp.

rep-Consts-Exp : ∀ {a} {A : Set a} ⦃ r : Rep A Consts ⦄ →
                 Rep A Exp
rep-Consts-Exp ⦃ r ⦄ = rep ⦃ proj₁ code-Consts ⦄ ∘-rep r

-- Represents something as an expression.

rep-as-Exp : ∀ {a} {A : Set a} ⦃ r : Rep A Consts ⦄ → A → Exp
rep-as-Exp = ⌜_⌝ ⦃ rep-Consts-Exp ⦄

-- rep-as-Exp returns constructor applications.

rep-const :
  ∀ {a} {A : Set a} ⦃ r : Rep A Consts ⦄
  (x : A) → Constructor-application (rep-as-Exp x)
rep-const = proj₂ code-Consts ∘ ⌜_⌝

-- rep-as-Exp returns closed expressions.

rep-closed :
  ∀ {a} {A : Set a} ⦃ r : Rep A Consts ⦄
  (x : A) → Closed (rep-as-Exp x)
rep-closed = const→closed ∘ rep-const

-- Constructor applications can be encoded as closed expressions.

code-Consts-Closed : Code Consts Closed-exp
Code.code code-Consts-Closed c =
  code ⦃ r = proj₁ code-Consts ⦄ c , const→closed (proj₂ code-Consts c)

Code.decode code-Consts-Closed (e , _) =
  decode ⦃ r = proj₁ code-Consts ⦄ e

Code.decode∘code code-Consts-Closed c =
  decode ⦃ r = proj₁ code-Consts ⦄ (code ⦃ r = proj₁ code-Consts ⦄ c)  ≡⟨ decode∘code ⦃ r = proj₁ code-Consts ⦄ c ⟩∎
  just c                                                              ∎

-- Converts instances of the form Rep A Consts to Rep A Closed-exp.

rep-Consts-Closed-exp :
  ∀ {a} {A : Set a} ⦃ r : Rep A Consts ⦄ → Rep A Closed-exp
rep-Consts-Closed-exp ⦃ r ⦄ = rep ⦃ r = code-Consts-Closed ⦄ ∘-rep r

-- rep-as-Exp returns values.

rep-value :
  ∀ {a} {A : Set a} ⦃ r : Rep A Consts ⦄
  (x : A) → Value (rep-as-Exp x)
rep-value = const→value ∘ rep-const

-- Some derived lemmas.

subst-rep :
  ∀ {a} {A : Set a} ⦃ r : Rep A Consts ⦄ (x : A) {y e} →
  rep-as-Exp x [ y ← e ] ≡ rep-as-Exp x
subst-rep x = subst-closed _ _ (rep-closed x)

substs-rep :
  ∀ {a} {A : Set a} ⦃ r : Rep A Consts ⦄ (x : A) ps →
  foldr (λ ye → _[ proj₁ ye ← proj₂ ye ]) (rep-as-Exp x) ps ≡
  rep-as-Exp x
substs-rep x = substs-closed (rep-as-Exp x) (rep-closed x)

rep⇓rep :
  ∀ {a} {A : Set a} ⦃ r : Rep A Consts ⦄
  (x : A) → rep-as-Exp x ⇓ rep-as-Exp x
rep⇓rep x = values-compute-to-themselves (rep-value x)

rep⇓≡rep :
  ∀ {a} {A : Set a} ⦃ r : Rep A Consts ⦄ {v}
  (x : A) → rep-as-Exp x ⇓ v → rep-as-Exp x ≡ v
rep⇓≡rep x = values-only-compute-to-themselves (rep-value x)

------------------------------------------------------------------------
-- Specifications of how a number of types are encoded as χ
-- constructor applications

-- Encoder for booleans.

code-Bool : Code Bool Consts
code-Bool = record
  { code        = cd
  ; decode      = dc
  ; decode∘code = dc∘cd
  }
  where
  cd : Bool → Consts
  cd true  = const c-true  []
  cd false = const c-false []

  dc : Consts → Maybe Bool
  dc (const c args) with c-true C.≟ c | c-false C.≟ c
  dc (const c [])   | yes _ | _     = return true
  dc (const c [])   | _     | yes _ = return false
  dc (const c _)    | _     | _     = nothing

  dc∘cd : ∀ b → dc (cd b) ≡ just b
  dc∘cd true with c-true C.≟ c-true
  ... | yes _   = refl
  ... | no  t≢t = ⊥-elim (t≢t refl)
  dc∘cd false with c-true C.≟ c-false | c-false C.≟ c-false
  ... | no  _   | no f≢f = ⊥-elim (f≢f refl)
  ... | yes t≡f | _      = ⊥-elim (C.distinct-codes→distinct-names
                                     (λ ()) t≡f)
  ... | no _    | yes _  = refl

-- Encoder for natural numbers.

code-ℕ : Code ℕ Consts
code-ℕ = record
  { code        = cd
  ; decode      = dc
  ; decode∘code = dc∘cd
  }
  where
  cd : ℕ → Consts
  cd zero    = const c-zero []
  cd (suc n) = const c-suc (cd n ∷ [])

  dc : Consts → Maybe ℕ
  dc (const c args)     with c-zero C.≟ c | c-suc C.≟ c
  dc (const c [])       | yes eq | _      = return zero
  dc (const c (n ∷ [])) | _      | yes eq = map suc (dc n)
  dc (const c _)        | _      | _      = nothing

  dc∘cd : ∀ n → dc (cd n) ≡ just n
  dc∘cd zero with c-zero C.≟ c-zero
  ... | yes _   = refl
  ... | no  z≢z = ⊥-elim (z≢z refl)
  dc∘cd (suc n) with c-zero C.≟ c-suc | c-suc C.≟ c-suc
  ... | no  _   | no s≢s = ⊥-elim (s≢s refl)
  ... | yes z≡s | _      = ⊥-elim (C.distinct-codes→distinct-names
                                     (λ ()) z≡s)
  ... | no _    | yes _  =
    map suc (dc (cd n))  ≡⟨ by (dc∘cd n) ⟩
    map suc (return n)   ≡⟨ refl ⟩∎
    return (suc n)       ∎

-- Encoder for variables.

code-Var : Code Var Consts
code-Var = code-ℕ ∘-code ↔→Code V.countably-infinite

-- Encoder for constants.

code-Const : Code Const Consts
code-Const = code-ℕ ∘-code ↔→Code C.countably-infinite

-- Encoders for products.

module _ {a b} {A : Set a} {B : Set b} where

  private

    encode : (A → Consts) → (B → Consts) → A × B → Consts
    encode encA encB (x , y) = const c-pair (encA x ∷ encB y ∷ [])

  rep-× : ⦃ r : Rep A Consts ⦄ ⦃ s : Rep B Consts ⦄ →
          Rep (A × B) Consts
  rep-× ⦃ r ⦄ ⦃ s ⦄ = record
    { ⌜_⌝           = encode ⌜_⌝ ⌜_⌝
    ; rep-injective = λ { {x₁ , x₂} {y₁ , y₂} →
        const c-pair (⌜ x₁ ⌝ ∷ ⌜ x₂ ⌝ ∷ []) ≡
        const c-pair (⌜ y₁ ⌝ ∷ ⌜ y₂ ⌝ ∷ [])    ↝⟨ lemma ⟩

        ⌜ x₁ ⌝ ≡ ⌜ y₁ ⌝ × ⌜ x₂ ⌝ ≡ ⌜ y₂ ⌝      ↝⟨ Σ-map rep-injective rep-injective ⟩

        x₁ ≡ y₁ × x₂ ≡ y₂                      ↝⟨ uncurry (cong₂ _,_) ⟩□

        (x₁ , x₂) ≡ (y₁ , y₂)                  □ }
    }
    where
    lemma :
      ∀ {c₁ c₂ x₁ x₂ y₁ y₂} →
      Consts.const c₁ (x₁ ∷ x₂ ∷ []) ≡ const c₂ (y₁ ∷ y₂ ∷ []) →
      x₁ ≡ y₁ × x₂ ≡ y₂
    lemma refl = refl , refl

  code-× : ⦃ c : Code A Consts ⦄ ⦃ d : Code B Consts ⦄ →
           Code (A × B) Consts
  code-× = record
    { code        = cd
    ; decode      = dc
    ; decode∘code = dc∘cd
    }
    where
    cd : A × B → Consts
    cd = encode code code

    dc : Consts → Maybe (A × B)
    dc (const c args)         with c-pair C.≟ c
    dc (const c (x ∷ y ∷ [])) | yes _ = decode x >>=′ λ x →
                                        decode y >>=′ λ y →
                                        just (x , y)
    dc (const c args)         | _     = nothing

    dc∘cd : ∀ x → dc (cd x) ≡ just x
    dc∘cd (x , y) with c-pair C.≟ c-pair
    ... | no p≢p = ⊥-elim (p≢p refl)
    ... | yes _  =
      (⟨ decode (code x) ⟩ >>=′ λ x →
       decode (code y) >>=′ λ y →
       just (x , y))                      ≡⟨ ⟨by⟩ decode∘code ⟩

      (return x >>=′ λ x →
       decode (code y) >>=′ λ y →
       just (x , y))                      ≡⟨⟩

      (⟨ decode (code y) ⟩ >>=′ λ y →
       just (x , y))                      ≡⟨ ⟨by⟩ decode∘code ⟩

      (return y >>=′ λ y → just (x , y))  ≡⟨ refl ⟩∎

      return (x , y)                      ∎

-- Encoders for lists.

module _ {a} {A : Set a} where

  private

    encode : (A → Consts) → List A → Consts
    encode enc []       = const c-nil []
    encode enc (x ∷ xs) = const c-cons (enc x ∷ encode enc xs ∷ [])

  rep-List : ⦃ r : Rep A Consts ⦄ → Rep (List A) Consts
  rep-List = record
    { ⌜_⌝           = encode ⌜_⌝
    ; rep-injective = injective
    }
    where
    injective : ∀ {xs ys} → encode ⌜_⌝ xs ≡ encode ⌜_⌝ ys → xs ≡ ys
    injective {[]}     {[]}     = λ _ → refl
    injective {[]}     {_ ∷ _}  = λ ()
    injective {_ ∷ _}  {[]}     = λ ()
    injective {x ∷ xs} {y ∷ ys} =
      const c-cons (⌜ x ⌝ ∷ encode ⌜_⌝ xs ∷ []) ≡
      const c-cons (⌜ y ⌝ ∷ encode ⌜_⌝ ys ∷ [])      ↝⟨ lemma ⟩

      ⌜ x ⌝ ≡ ⌜ y ⌝ × encode ⌜_⌝ xs ≡ encode ⌜_⌝ ys  ↝⟨ Σ-map rep-injective injective ⟩

      x ≡ y × xs ≡ ys                                ↝⟨ uncurry (cong₂ _∷_) ⟩□

      x ∷ xs ≡ y ∷ ys                                □
      where
      lemma :
        ∀ {c₁ x₁ y₁ c₂ x₂ y₂} →
        Consts.const c₁ (x₁ ∷ y₁ ∷ []) ≡ const c₂ (x₂ ∷ y₂ ∷ []) →
        x₁ ≡ x₂ × y₁ ≡ y₂
      lemma refl = refl , refl

  code-List : ⦃ c : Code A Consts ⦄ → Code (List A) Consts
  code-List = record
    { code        = cd
    ; decode      = dc
    ; decode∘code = dc∘cd
    }
    where
    cd : List A → Consts
    cd = encode code

    dc : Consts → Maybe (List A)
    dc (const c args)           with c-nil C.≟ c | c-cons C.≟ c
    dc (const c [])             | yes eq | _      = return []
    dc (const c′ (x ∷ xs ∷ [])) | _      | yes eq =
      _∷_ ⟨$⟩ decode x ⊛ dc xs
    dc (const c args) | _ | _ = nothing

    dc∘cd : ∀ x → dc (cd x) ≡ just x
    dc∘cd [] with c-nil C.≟ c-nil
    ... | yes _   = refl
    ... | no  n≢n = ⊥-elim (n≢n refl)
    dc∘cd (x ∷ xs) with c-nil C.≟ c-cons | c-cons C.≟ c-cons
    ... | no _    | no c≢c = ⊥-elim (c≢c refl)
    ... | yes n≡c | _      = ⊥-elim (C.distinct-codes→distinct-names
                                       (λ ()) n≡c)
    ... | no _    | yes _  =
      _∷_ ⟨$⟩ ⟨ decode (code x) ⟩ ⊛ dc (cd xs)  ≡⟨ ⟨by⟩ decode∘code ⟩
      _∷_ ⟨$⟩ return x ⊛ ⟨ dc (cd xs) ⟩         ≡⟨ ⟨by⟩ (dc∘cd xs) ⟩
      _∷_ ⟨$⟩ return x ⊛ return xs              ≡⟨⟩
      return (x ∷ xs)                           ∎

-- Encoder for lists of variables.

code-Var⋆ : Code (List Var) Consts
code-Var⋆ = code-List ⦃ code-Var ⦄

private

  module Var   = Code code-Var
  module Var⋆  = Code code-Var⋆
  module Const = Code code-Const

  -- Encoder for the abstract syntax.

  mutual

    code-E : Exp → Consts
    code-E (apply e₁ e₂) = const c-apply (code-E e₁ ∷ code-E e₂ ∷ [])
    code-E (lambda x e)  = const c-lambda (code ⦃ code-Var ⦄ x ∷ code-E e ∷ [])
    code-E (case e bs)   = const c-case (code-E e ∷ code-B⋆ bs ∷ [])
    code-E (rec x e)     = const c-rec (code ⦃ code-Var ⦄ x ∷ code-E e ∷ [])
    code-E (var x)       = const c-var (code ⦃ code-Var ⦄ x ∷ [])
    code-E (const c es)  = const c-const (code ⦃ code-Const ⦄ c ∷ code-⋆ es ∷ [])

    code-B : Br → Consts
    code-B (branch c xs e) =
      const c-branch
        (code ⦃ code-Const ⦄ c ∷ code ⦃ code-Var⋆ ⦄ xs ∷ code-E e ∷ [])

    -- TODO: One could presumably use sized types to avoid repetitive
    -- code. However, I did not want to use sized types in the
    -- specification of χ.

    code-⋆ : List Exp → Consts
    code-⋆ []       = const c-nil []
    code-⋆ (e ∷ es) = const c-cons (code-E e ∷ code-⋆ es ∷ [])

    code-B⋆ : List Br → Consts
    code-B⋆ []       = const c-nil []
    code-B⋆ (b ∷ bs) = const c-cons (code-B b ∷ code-B⋆ bs ∷ [])

  mutual

    decode-E : Consts → Maybe Exp
    decode-E (const c args) with c-apply  C.≟ c
                               | c-lambda C.≟ c
                               | c-case   C.≟ c
                               | c-rec    C.≟ c
                               | c-var    C.≟ c
                               | c-const  C.≟ c

    decode-E (const c (e₁ ∷ e₂ ∷ [])) | yes eq | _ | _ | _ | _ | _ =
      apply ⟨$⟩ decode-E e₁ ⊛ decode-E e₂

    decode-E (const c (x ∷ e ∷ [])) | _ | yes eq | _ | _ | _ | _ =
      lambda ⟨$⟩ decode ⦃ code-Var ⦄ x ⊛ decode-E e

    decode-E (const c (e ∷ bs ∷ [])) | _ | _ | yes eq | _ | _ | _ =
      case ⟨$⟩ decode-E e ⊛ decode-B⋆ bs

    decode-E (const c (x ∷ e ∷ [])) | _ | _ | _ | yes eq | _ | _ =
      rec ⟨$⟩ decode ⦃ code-Var ⦄ x ⊛ decode-E e

    decode-E (const c (x ∷ [])) | _ | _ | _ | _ | yes eq | _ =
      var ⟨$⟩ decode ⦃ code-Var ⦄ x

    decode-E (const c (c′ ∷ es ∷ [])) | _ | _ | _ | _ | _ | yes eq =
      const ⟨$⟩ decode ⦃ code-Const ⦄ c′ ⊛ decode-⋆ es

    decode-E (const c args) | _ | _ | _ | _ | _ | _ = nothing

    decode-B : Consts → Maybe Br
    decode-B (const c args)               with c-branch C.≟ c
    decode-B (const c (c′ ∷ xs ∷ e ∷ [])) | yes eq =
      branch ⟨$⟩ decode ⦃ code-Const ⦄ c′
               ⊛ decode ⦃ code-Var⋆ ⦄ xs
               ⊛ decode-E e
    decode-B (const c args) | _ = nothing

    decode-⋆ : Consts → Maybe (List Exp)
    decode-⋆ (const c args)           with c-nil C.≟ c | c-cons C.≟ c
    decode-⋆ (const c [])             | yes eq | _      = return []
    decode-⋆ (const c′ (e ∷ es ∷ [])) | _      | yes eq =
      _∷_ ⟨$⟩ decode-E e ⊛ decode-⋆ es
    decode-⋆ (const c args) | _ | _ = nothing

    decode-B⋆ : Consts → Maybe (List Br)
    decode-B⋆ (const c args)           with c-nil C.≟ c | c-cons C.≟ c
    decode-B⋆ (const c [])             | yes eq | _      = return []
    decode-B⋆ (const c′ (b ∷ bs ∷ [])) | _      | yes eq =
      _∷_ ⟨$⟩ decode-B b ⊛ decode-B⋆ bs
    decode-B⋆ (const c args) | _ | _ = nothing

  mutual

    decode∘code-E : ∀ e → decode-E (code-E e) ≡ just e

    decode∘code-E (apply e₁ e₂) with c-apply C.≟ c-apply
    ... | no c≢c = ⊥-elim (c≢c refl)
    ... | yes _  =
      apply ⟨$⟩ decode-E (code-E e₁) ⊛ decode-E (code-E e₂)  ≡⟨ by (decode∘code-E e₁) ⟩
      apply ⟨$⟩ return e₁ ⊛ decode-E (code-E e₂)             ≡⟨ by (decode∘code-E e₂) ⟩
      apply ⟨$⟩ return e₁ ⊛ return e₂                        ≡⟨⟩
      return (apply e₁ e₂)                                   ∎

    decode∘code-E (lambda x e) with c-apply  C.≟ c-lambda
                                  | c-lambda C.≟ c-lambda
    ... | _       | no l≢l = ⊥-elim (l≢l refl)
    ... | yes a≡l | _      = ⊥-elim (C.distinct-codes→distinct-names
                                       (λ ()) a≡l)
    ... | no _    | yes _  =
      lambda ⟨$⟩ Var.decode (code ⦃ code-Var ⦄ x) ⊛ decode-E (code-E e)  ≡⟨ by Var.decode∘code ⟩
      lambda ⟨$⟩ return x ⊛ decode-E (code-E e)                          ≡⟨ by (decode∘code-E e) ⟩
      lambda ⟨$⟩ return x ⊛ return e                                     ≡⟨⟩
      return (lambda x e)                                                ∎

    decode∘code-E (case e bs) with c-apply  C.≟ c-case
                                 | c-lambda C.≟ c-case
                                 | c-case   C.≟ c-case
    ... | _       | _       | no c≢c = ⊥-elim (c≢c refl)
    ... | _       | yes l≡c | _      = ⊥-elim (C.distinct-codes→distinct-names
                                                 (λ ()) l≡c)
    ... | yes a≡c | _       | _      = ⊥-elim (C.distinct-codes→distinct-names
                                                 (λ ()) a≡c)
    ... | no _    | no _    | yes _  =
      case ⟨$⟩ decode-E (code-E e) ⊛ decode-B⋆ (code-B⋆ bs)  ≡⟨ by (decode∘code-E e) ⟩
      case ⟨$⟩ return e ⊛ decode-B⋆ (code-B⋆ bs)             ≡⟨ by (decode∘code-B⋆ bs) ⟩
      case ⟨$⟩ return e ⊛ return bs                          ≡⟨⟩
      return (case e bs)                                     ∎

    decode∘code-E (rec x e) with c-apply  C.≟ c-rec
                               | c-lambda C.≟ c-rec
                               | c-case   C.≟ c-rec
                               | c-rec    C.≟ c-rec
    ... | _       | _       | _       | no r≢r = ⊥-elim (r≢r refl)
    ... | _       | _       | yes c≡r | _      = ⊥-elim (C.distinct-codes→distinct-names
                                                           (λ ()) c≡r)
    ... | _       | yes l≡r | _       | _      = ⊥-elim (C.distinct-codes→distinct-names
                                                           (λ ()) l≡r)
    ... | yes a≡r | _       | _       | _      = ⊥-elim (C.distinct-codes→distinct-names
                                                           (λ ()) a≡r)
    ... | no _    | no _    | no _    | yes _  =
      rec ⟨$⟩ Var.decode (code ⦃ code-Var ⦄ x) ⊛ decode-E (code-E e)  ≡⟨ by Var.decode∘code ⟩
      rec ⟨$⟩ return x ⊛ decode-E (code-E e)                          ≡⟨ by (decode∘code-E e) ⟩
      rec ⟨$⟩ return x ⊛ return e                                     ≡⟨⟩
      return (rec x e)                                                ∎

    decode∘code-E (var x) with c-apply  C.≟ c-var
                             | c-lambda C.≟ c-var
                             | c-case   C.≟ c-var
                             | c-rec    C.≟ c-var
                             | c-var    C.≟ c-var
    ... | _       | _       | _       | _       | no v≢v = ⊥-elim (v≢v refl)
    ... | _       | _       | _       | yes r≡v | _      = ⊥-elim (C.distinct-codes→distinct-names
                                                                     (λ ()) r≡v)
    ... | _       | _       | yes c≡v | _       | _      = ⊥-elim (C.distinct-codes→distinct-names
                                                                     (λ ()) c≡v)
    ... | _       | yes l≡v | _       | _       | _      = ⊥-elim (C.distinct-codes→distinct-names
                                                                     (λ ()) l≡v)
    ... | yes a≡v | _       | _       | _       | _      = ⊥-elim (C.distinct-codes→distinct-names
                                                                     (λ ()) a≡v)
    ... | no _    | no _    | no _    | no _    | yes _  =
      var ⟨$⟩ Var.decode (code ⦃ code-Var ⦄ x)  ≡⟨ by Var.decode∘code ⟩
      var ⟨$⟩ return x                          ≡⟨ refl ⟩∎
      return (var x)                            ∎

    decode∘code-E (const c es) with c-apply  C.≟ c-const
                                  | c-lambda C.≟ c-const
                                  | c-case   C.≟ c-const
                                  | c-rec    C.≟ c-const
                                  | c-var    C.≟ c-const
                                  | c-const  C.≟ c-const
    ... | _       | _       | _       | _       | _       | no c≢c = ⊥-elim (c≢c refl)
    ... | _       | _       | _       | _       | yes v≡c | _      = ⊥-elim (C.distinct-codes→distinct-names
                                                                               (λ ()) v≡c)
    ... | _       | _       | _       | yes r≡c | _       | _      = ⊥-elim (C.distinct-codes→distinct-names
                                                                               (λ ()) r≡c)
    ... | _       | _       | yes c≡c | _       | _       | _      = ⊥-elim (C.distinct-codes→distinct-names
                                                                               (λ ()) c≡c)
    ... | _       | yes l≡c | _       | _       | _       | _      = ⊥-elim (C.distinct-codes→distinct-names
                                                                               (λ ()) l≡c)
    ... | yes a≡c | _       | _       | _       | _       | _      = ⊥-elim (C.distinct-codes→distinct-names
                                                                               (λ ()) a≡c)
    ... | no _    | no _    | no _    | no _    | no _    | yes _  =
      const ⟨$⟩ Const.decode (code ⦃ code-Const ⦄ c) ⊛ decode-⋆ (code-⋆ es)  ≡⟨ by Const.decode∘code ⟩
      const ⟨$⟩ return c ⊛ decode-⋆ (code-⋆ es)                              ≡⟨ by (decode∘code-⋆ es) ⟩
      const ⟨$⟩ return c ⊛ return es                                         ≡⟨⟩
      return (const c es)                                                    ∎

    decode∘code-B : ∀ b → decode-B (code-B b) ≡ just b
    decode∘code-B (branch c xs e) with c-branch C.≟ c-branch
    ... | no b≢b = ⊥-elim (b≢b refl)
    ... | yes _  =
      branch ⟨$⟩ Const.decode (code ⦃ code-Const ⦄ c) ⊛
                 Var⋆.decode (code ⦃ code-Var⋆ ⦄ xs) ⊛
                 decode-E (code-E e)                         ≡⟨ by Const.decode∘code ⟩

      branch ⟨$⟩ return c ⊛
                 Var⋆.decode (code ⦃ code-Var⋆ ⦄ xs) ⊛
                 decode-E (code-E e)                         ≡⟨ by Var⋆.decode∘code ⟩

      branch ⟨$⟩ return c ⊛ return xs ⊛ decode-E (code-E e)  ≡⟨ by (decode∘code-E e) ⟩

      branch ⟨$⟩ return c ⊛ return xs ⊛ return e             ≡⟨⟩

      return (branch c xs e)                                 ∎

    decode∘code-⋆ : ∀ es → decode-⋆ (code-⋆ es) ≡ just es
    decode∘code-⋆ [] with c-nil C.≟ c-nil
    ... | no  n≢n = ⊥-elim (n≢n refl)
    ... | yes _   = refl
    decode∘code-⋆ (e ∷ es) with c-nil C.≟ c-cons | c-cons C.≟ c-cons
    ... | no _    | no c≢c = ⊥-elim (c≢c refl)
    ... | yes n≡c | _      = ⊥-elim (C.distinct-codes→distinct-names
                                       (λ ()) n≡c)
    ... | no _    | yes _  =
      _∷_ ⟨$⟩ decode-E (code-E e) ⊛ decode-⋆ (code-⋆ es)  ≡⟨ by (decode∘code-E e) ⟩
      _∷_ ⟨$⟩ return e ⊛ decode-⋆ (code-⋆ es)             ≡⟨ by (decode∘code-⋆ es) ⟩
      _∷_ ⟨$⟩ return e ⊛ return es                        ≡⟨⟩
      return (e ∷ es)                                     ∎

    decode∘code-B⋆ : ∀ bs → decode-B⋆ (code-B⋆ bs) ≡ just bs
    decode∘code-B⋆ [] with c-nil C.≟ c-nil
    ... | no  n≢n = ⊥-elim (n≢n refl)
    ... | yes _   = refl
    decode∘code-B⋆ (b ∷ bs) with c-nil C.≟ c-cons | c-cons C.≟ c-cons
    ... | no _    | no c≢c = ⊥-elim (c≢c refl)
    ... | yes n≡c | _      = ⊥-elim (C.distinct-codes→distinct-names
                                       (λ ()) n≡c)
    ... | no _    | yes _  =
      _∷_ ⟨$⟩ decode-B (code-B b) ⊛ decode-B⋆ (code-B⋆ bs)  ≡⟨ by (decode∘code-B b) ⟩
      _∷_ ⟨$⟩ return b ⊛ decode-B⋆ (code-B⋆ bs)             ≡⟨ by (decode∘code-B⋆ bs) ⟩
      _∷_ ⟨$⟩ return b ⊛ return bs                          ≡⟨⟩
      return (b ∷ bs)                                       ∎

code-Exp : Code Exp Consts
Code.code        code-Exp = code-E
Code.decode      code-Exp = decode-E
Code.decode∘code code-Exp = decode∘code-E

code-Br : Code Br Consts
Code.code        code-Br = code-B
Code.decode      code-Br = decode-B
Code.decode∘code code-Br = decode∘code-B

code-Exps : Code (List Exp) Consts
Code.code        code-Exps = code-⋆
Code.decode      code-Exps = decode-⋆
Code.decode∘code code-Exps = decode∘code-⋆

code-Brs : Code (List Br) Consts
Code.code        code-Brs = code-B⋆
Code.decode      code-Brs = decode-B⋆
Code.decode∘code code-Brs = decode∘code-B⋆

-- Encoder for closed expressions.

code-Closed : Code Closed-exp Consts
Code.code   code-Closed = code ⦃ code-Exp ⦄ ∘ proj₁
Code.decode code-Closed c with decode ⦃ code-Exp ⦄ c
... | nothing = nothing
... | just e  with closed? e
...   | yes cl = just (e , cl)
...   | no _   = nothing
Code.decode∘code code-Closed (c , cl)
  with decode ⦃ r = code-Exp ⦄ (code ⦃ code-Exp ⦄ c)
     | decode∘code ⦃ r = code-Exp ⦄ c
... | .(just c) | refl with closed? c
...   | no  ¬cl = ⊥-elim (¬cl cl)
...   | yes cl′ =
  cong just (closed-equal-if-expressions-equal refl)
