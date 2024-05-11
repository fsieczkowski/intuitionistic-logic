Require Import Utf8.
Require Import List.
Require Import Syntax.
Require Import Heyting.

Reserved Notation "〚 φ 〛 ϑ" (at level 30).
Reserved Notation "〚 Γ '〛ᶜ' ϑ" (at level 30).

Section Interp.
  Context {H} {HO : HOps H} {HH : Heyt H}.

  Fixpoint den {X : Set} (ϑ : X → H) (φ : prop X) : H :=
    match φ with
    | ` x => ϑ x
    | ⊤ => ⊤%ha
    | ⊥ => ⊥%ha
    | φ₁ ⊼ φ₂ => 〚 φ₁ 〛 ϑ ⊓ 〚 φ₂ 〛 ϑ
    | φ₁ ⊻ φ₂ => 〚 φ₁ 〛 ϑ ⊔ 〚 φ₂ 〛 ϑ
    | φ₁ ↣ φ₂ => 〚 φ₁ 〛 ϑ ⇒ 〚 φ₂ 〛 ϑ
    end%prop%ha
  where "〚 φ 〛 ϑ" := (den ϑ φ).

  Fixpoint denC {X : Set} (ϑ : X → H) (Γ : list (prop X)) : H :=
    match Γ with
    | nil => ⊤
    | φ :: Γ => 〚 φ 〛 ϑ ⊓ 〚 Γ 〛ᶜ ϑ
    end%ha
  where "〚 Γ 〛ᶜ ϑ" := (denC ϑ Γ).

  Definition holdsH {X} (Γ : list (prop X)) (φ : prop X) :=
    ∀ ϑ, (〚 Γ 〛ᶜ ϑ ≦ 〚 φ 〛 ϑ)%ha.

End Interp.

Notation "〚 φ 〛 ϑ" := (den ϑ φ).
Notation "〚 Γ 〛ᶜ ϑ" := (denC ϑ Γ).

Arguments holdsH H {HO X} Γ φ.

Definition holds {X} Γ (φ : prop X) :=
  ∀ (H : HAlg), holdsH H Γ φ.

Notation "Γ ⊨ φ" := (holds Γ φ) (at level 70, no associativity).
