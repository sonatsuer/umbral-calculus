/-
# Simple types

The simple types over a set `B` of base sorts: `σ ::= b | σ → σ`. Base sorts do
not occur in the types of the language (`Core/SystemF.lean`); they are the sets
at which its type variables are instantiated, and the simple types are what a
quantifier ranges over (write-up, Chapter 2, the semantics).
-/

namespace FreeThms

universe u

/-- Simple types over a set `B` of base sorts. -/
inductive Ty (B : Type u) : Type u
  | base : B → Ty B
  | arrow : Ty B → Ty B → Ty B
  deriving Repr, DecidableEq

namespace Ty

/-- Function type. -/
scoped infixr:25 " ⇒ " => Ty.arrow

end Ty

end FreeThms
