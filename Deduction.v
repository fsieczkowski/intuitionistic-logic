Require Import Utf8.
Require Import List.
Require Import Syntax.

Reserved Notation "Γ ⊢ φ" (at level 70, no associativity).

Inductive proves {X} (Γ : list (prop X)) : prop X → Prop :=
| Ax {φ} (In : In φ Γ) : Γ ⊢ φ
| TrueI : Γ ⊢ ⊤
| ConjI {φ ψ} (PL : Γ ⊢ φ) (PR : Γ ⊢ ψ) : Γ ⊢ φ ⊼ ψ
| DisjIL {φ} (P : Γ ⊢ φ) ψ : Γ ⊢ φ ⊻ ψ
| DisjIR φ {ψ} (P : Γ ⊢ ψ) : Γ ⊢ φ ⊻ ψ
| ImplI {φ ψ} (P : φ :: Γ ⊢ ψ) : Γ ⊢ φ ↣ ψ
| FalseE φ (P : Γ ⊢ ⊥) : Γ ⊢ φ
| ConjEL {φ ψ} (P : Γ ⊢ φ ⊼ ψ) : Γ ⊢ φ
| ConjER {φ ψ} (P : Γ ⊢ φ ⊼ ψ) : Γ ⊢ ψ
| DisjE {φ₁ φ₂ ψ} (P : Γ ⊢ φ₁ ⊻ φ₂) (PL : φ₁ :: Γ ⊢ ψ) (PR : φ₂ :: Γ ⊢ ψ) : Γ ⊢ ψ
| ImplE {φ ψ} (PI : Γ ⊢ φ ↣ ψ) (PA : Γ ⊢ φ) : Γ ⊢ ψ
where "Γ ⊢ φ" := (proves Γ φ%prop).

Lemma wknG {X} (Γ₁ Γ₂ Γ₃ : list (prop X)) φ : Γ₁ ++ Γ₃ ⊢ φ → Γ₁ ++ Γ₂ ++ Γ₃ ⊢ φ.
Proof.
  intros HP; remember (Γ₁ ++ Γ₃) as Γ eqn: EQΓ; revert Γ₁ EQΓ; induction HP; intros; subst;
    eauto 4 using @proves; [| |].
  - apply Ax; rewrite !in_app_iff in *; tauto.
  - now apply ImplI, IHHP with (Γ₁ := φ :: Γ₁).
  - eapply DisjE; [now eauto | ..].
    + now apply IHHP2 with (Γ₁ := φ₁ :: Γ₁).
    + now apply IHHP3 with (Γ₁ := φ₂ :: Γ₁).
Qed.

Lemma wkn {X} (Γ : list (prop X)) φ ψ : Γ ⊢ ψ → φ :: Γ ⊢ ψ.
Proof.
  apply wknG with (Γ₁ := nil) (Γ₂ := φ :: nil).
Qed.
