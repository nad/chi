------------------------------------------------------------------------
-- Encoder and decoder instances
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

open import Atom

module Coding.Instances (atoms : χ-atoms) where

open import Prelude

open import Chi            atoms
open import Free-variables atoms
open import Values         atoms

open χ-atoms atoms

open import Coding atoms as Coding using (Rep; module Code)

instance

  rep-Consts-Exp : ∀ {a} {A : Type a} ⦃ r : Rep A Consts ⦄ →
                   Rep A Exp
  rep-Consts-Exp = Coding.rep-Consts-Exp

  rep-Consts-Closed-exp :
    ∀ {a} {A : Type a} ⦃ r : Rep A Consts ⦄ → Rep A Closed-exp
  rep-Consts-Closed-exp = Coding.rep-Consts-Closed-exp

  rep-Bool : Rep Bool Consts
  rep-Bool = Code.rep Coding.code-Bool

  rep-ℕ : Rep ℕ Consts
  rep-ℕ = Code.rep Coding.code-ℕ

  rep-Var : Rep Var Consts
  rep-Var = Code.rep Coding.code-Var

  rep-Const : Rep Const Consts
  rep-Const = Code.rep Coding.code-Const

  rep-× : ∀ {a b} {A : Type a} {B : Type b}
            ⦃ c : Rep A Consts ⦄ ⦃ d : Rep B Consts ⦄ →
          Rep (A × B) Consts
  rep-× = Coding.rep-×

  rep-Var⋆ : Rep (List Var) Consts
  rep-Var⋆ = Code.rep Coding.code-Var⋆

  rep-Exp : Rep Exp Consts
  rep-Exp = Code.rep Coding.code-Exp

  rep-Br : Rep Br Consts
  rep-Br = Code.rep Coding.code-Br

  rep-Exps : Rep (List Exp) Consts
  rep-Exps = Code.rep Coding.code-Exps

  rep-Brs : Rep (List Br) Consts
  rep-Brs = Code.rep Coding.code-Brs

  rep-Closed : Rep Closed-exp Consts
  rep-Closed = Code.rep Coding.code-Closed
