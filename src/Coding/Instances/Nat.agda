------------------------------------------------------------------------
-- Encoder and decoder instances for Atom.χ-ℕ-atoms
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Coding.Instances.Nat where

open import Atom

-- The code-Var and code-Const instances are hidden: they are replaced
-- by the code-ℕ instance.

open import Coding.Instances χ-ℕ-atoms public
  hiding (code-Var; code-Const)
