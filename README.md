Agda-style Equational Reasoning in Haskell by Data Kinds
=========================================================

What is this?
--------------
This library provides means to prove equations in Haskell.
You can prove equations in Agda's EqReasoning like style.

See blow for an example:

```haskell
plusZeroL :: SNat m -> Zero :+: m :=: m
plusZeroL SZero = Refl
plusZeroL (SSucc m) =
  start (SZero %+ (SSucc m))
    === SSucc (SZero %+ m)    `because`   plusSuccR SZero m
    === SSucc m               `because`   succCongEq (plusZeroL m)

```

It also provides some utility functions to use an induction.

For more detail, please read source codes!


TODOs
------
I suspect that implementing todos below require GHC HEAD?

* Generalize equality other than `(:=:)`.
* Automatic generation for induction schema for any inductive types.
