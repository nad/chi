------------------------------------------------------------------------
-- Encoder and decoder instances
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Atom

module Coding.Instances (atoms : χ-atoms) where

open import Prelude

open import Chi            atoms
open import Free-variables atoms
open import Values         atoms

open χ-atoms atoms

open import Coding atoms as Coding using (Code)

instance

  code-Consts-Exp : ∀ {a} {A : Set a} ⦃ c : Code A Consts ⦄ →
                    Code A Exp
  code-Consts-Exp = Coding.code-Consts-Exp

  code-Consts-Closed-exp :
    ∀ {a} {A : Set a} ⦃ c : Code A Consts ⦄ → Code A Closed-exp
  code-Consts-Closed-exp = Coding.code-Consts-Closed-exp

  code-Bool : Code Bool Consts
  code-Bool = Coding.code-Bool

  code-ℕ : Code ℕ Consts
  code-ℕ = Coding.code-ℕ

  code-Var : Code Var Consts
  code-Var = Coding.code-Var

  code-Const : Code Const Consts
  code-Const = Coding.code-Const

  code-× : ∀ {a b} {A : Set a} {B : Set b}
             ⦃ c : Code A Consts ⦄ ⦃ d : Code B Consts ⦄ →
           Code (A × B) Consts
  code-× = Coding.code-×

  code-Var⋆ : Code (List Var) Consts
  code-Var⋆ = Coding.code-Var⋆

  code-Exp : Code Exp Consts
  code-Exp = Coding.code-Exp

  code-Br : Code Br Consts
  code-Br = Coding.code-Br

  code-Exps : Code (List Exp) Consts
  code-Exps = Coding.code-Exps

  code-Brs : Code (List Br) Consts
  code-Brs = Coding.code-Brs

  code-Closed : Code Closed-exp Consts
  code-Closed = Coding.code-Closed
