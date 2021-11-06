------------------------------------------------------------------------
-- Various constants
------------------------------------------------------------------------

open import Atom

module Constants (atoms : χ-atoms) where

open χ-atoms atoms

c-zero : Const
c-zero = C.name 0

c-suc : Const
c-suc = C.name 1

c-nil : Const
c-nil = C.name 2

c-cons : Const
c-cons = C.name 3

c-apply : Const
c-apply = C.name 4

c-case : Const
c-case = C.name 5

c-rec : Const
c-rec = C.name 6

c-lambda : Const
c-lambda = C.name 7

c-const : Const
c-const = C.name 8

c-var : Const
c-var = C.name 9

c-branch : Const
c-branch = C.name 10

c-true : Const
c-true = C.name 11

c-false : Const
c-false = C.name 12

c-pair : Const
c-pair = C.name 13

v-equal : Var
v-equal = V.name 0

v-m : Var
v-m = V.name 1

v-n : Var
v-n = V.name 2

v-x : Var
v-x = V.name 3

v-new : Var
v-new = V.name 4

v-e : Var
v-e = V.name 5

v-subst : Var
v-subst = V.name 6

v-e₁ : Var
v-e₁ = V.name 7

v-e₂ : Var
v-e₂ = V.name 8

v-bs : Var
v-bs = V.name 9

v-y : Var
v-y = V.name 10

v-c : Var
v-c = V.name 11

v-es : Var
v-es = V.name 12

v-ys : Var
v-ys = V.name 13

v-member : Var
v-member = V.name 14

v-xs : Var
v-xs = V.name 15

v-lookup : Var
v-lookup = V.name 16

v-b : Var
v-b = V.name 17

v-c′ : Var
v-c′ = V.name 18

v-underscore : Var
v-underscore = V.name 19

v-substs : Var
v-substs = V.name 20

v-e′ : Var
v-e′ = V.name 21

v-map : Var
v-map = V.name 22

v-p : Var
v-p = V.name 23

v-eval : Var
v-eval = V.name 24

v-internal-code : Var
v-internal-code = V.name 25

v-halts : Var
v-halts = V.name 26

v-z : Var
v-z = V.name 27

v-f : Var
v-f = V.name 28

v-g : Var
v-g = V.name 29
