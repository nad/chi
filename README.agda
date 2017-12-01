------------------------------------------------------------------------
-- A formalisation of one variant of the language χ, along with a
-- number of properties
--
-- Nils Anders Danielsson
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module README where

-- Atoms.

import Atom

-- Various constants.

import Constants

-- A specification of the language χ.

import Chi

-- The semantics is deterministic.

import Deterministic

-- Values.

import Values

-- Some cancellation lemmas.

import Cancellation

-- "Reasoning" combinators.

import Reasoning

-- The abstract syntax is a set, and the semantics is propositional.

import Propositional

-- The "terminates" relation.

import Termination

-- Compatibility lemmas.

import Compatibility

-- Definitions of "free in" and "closed", along with some properties.

import Free-variables

-- Encoders and decoders.

import Coding

-- Encoder and decoder instances.

import Coding.Instances

-- Encoder and decoder instances for Atom.χ-ℕ-atoms.

import Coding.Instances.Nat

-- Internal coding.

import Internal-coding

-- Some χ program combinators.

import Combinators

-- Definition of the size of an expression, along with some
-- properties.

import Size

-- A self-interpreter (without correctness proof).

import Self-interpreter

-- Partial functions, computability.

import Computability

-- The halting problem.

import Halting-problem

-- Rice's theorem.

import Rices-theorem

-- A theorem related to pointwise equality.

import Pointwise-equality
