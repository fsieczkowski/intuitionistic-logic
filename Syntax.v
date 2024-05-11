Require Import Utf8.

Inductive prop {X : Set} :=
| pvar (x : X)
| ptrue | pfalse
| pconj (φ₁ φ₂ : prop)
| pdisj (φ₁ φ₂ : prop)
| pimpl (φ₁ φ₂ : prop).
Arguments prop : clear implicits.
Declare Scope prop_scope.
Delimit Scope prop_scope with prop.

Notation "` x" := (pvar x) (at level 15) : prop_scope.
Notation "φ ⊻ ψ" := (pdisj φ ψ) (at level 50, left associativity) : prop_scope.
Notation "φ ⊼ ψ" := (pconj φ ψ) (at level 45, left associativity) : prop_scope.
Notation "φ ↣ ψ" := (pimpl φ ψ) (at level 55, right associativity) : prop_scope.
Notation "⊤" := ptrue : prop_scope.
Notation "⊥" := pfalse : prop_scope.
