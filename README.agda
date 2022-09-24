------------------------------------------------------------------------
-- A formalisation of one variant of the language χ, along with a
-- number of properties
--
-- Nils Anders Danielsson
------------------------------------------------------------------------

-- A description of the language χ, as well as some of the definitions
-- and proofs used in this development, can be found in "The language
-- χ" by Bengt Nordström (edited by me):
--
-- * https://chalmers.instructure.com/courses/10744/file_contents/course%20files/reading/The_language_chi.pdf
--
-- See also the following lecture slides:
--
-- * https://chalmers.instructure.com/courses/10744/file_contents/course%20files/lectures/L4.pdf
-- * https://chalmers.instructure.com/courses/10744/file_contents/course%20files/lectures/L5.pdf
-- * https://chalmers.instructure.com/courses/10744/file_contents/course%20files/lectures/L6.pdf

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

-- Some substitution lemmas.

import Substitution

-- Definitions of "free in" and "closed", along with some properties.

import Free-variables

-- Alpha-equivalence.

import Alpha-equivalence

-- Encoders and decoders.

import Coding

-- Encoder and decoder instances.

import Coding.Instances

-- Encoder and decoder instances for Atom.χ-ℕ-atoms.

import Coding.Instances.Nat

-- A tactic that can "remove" applications of substitutions to closed
-- expressions.

import Free-variables.Remove-substs

-- Internal coding.

import Internal-coding

-- Some χ program combinators.

import Combinators

-- The rec construction can be encoded using λ-terms.

import Recursion-without-rec

-- Definition of the size of an expression, along with some
-- properties.

import Expression-size

-- A definition of the size of an operational semantics derivation,
-- along with some properties.

import Derivation-size

-- Internal substitution.

import Internal-substitution

-- Internal lookup.

import Internal-lookup

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
