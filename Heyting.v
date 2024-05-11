Require Import Utf8.
Require Import Setoid RelationClasses Morphisms.

Arguments Basics.flip {A B C} _ _ _/.

Declare Scope ha_scope.
Delimit Scope ha_scope with ha.

Class HOps (H : Set) :=
  { hord : H → H → Prop;
    htop : H;
    hbot : H;
    hlub : H → H → H;
    hglb : H → H → H;
    hrpc : H → H → H
  }.

Definition heq {H} {HO : HOps H} x y := hord x y ∧ hord y x.

Notation "⊤" := htop : ha_scope.
Notation "⊥" := hbot : ha_scope.
Notation "x ⊓ y" := (hlub x y) (at level 45, left associativity) : ha_scope.
Notation "x ⊔ y" := (hglb x y) (at level 50, left associativity) : ha_scope.
Notation "x ⇒ y" := (hrpc x y) (at level 55, right associativity) : ha_scope.
Notation "x ≦ y" := (hord x y) (at level 70, no associativity) : ha_scope.
Notation "x ≡ y" := (heq x y) (at level 70, no associativity) : ha_scope.

Local Open Scope ha_scope.

Class Heyt (H : Set) {HO : HOps H} :=
  { hpreo :: PreOrder hord;
    htopU x : x ≦ ⊤;
    hbotB x : ⊥ ≦ x;
    hlubMon :: Proper (hord ==> hord ==> hord) hlub;
    hglbMon :: Proper (hord ==> hord ==> hord) hglb;
    hrpcMon :: Proper (hord --> hord ++> hord) hrpc;
    hlubC x y : x ⊓ y ≡ y ⊓ x;
    hglbC x y : x ⊔ y ≡ y ⊔ x;
    hlubA x y z : x ⊓ y ⊓ z ≡ x ⊓ (y ⊓ z);
    hglbA x y z : x ⊔ y ⊔ z ≡ x ⊔ (y ⊔ z);
    hlubI x : x ⊓ x ≡ x;
    hglbI x : x ⊔ x ≡ x;
    hlubT x : x ⊓ ⊤ ≡ x;
    hglbB x : x ⊔ ⊥ ≡ x;
    hglblubD x y z : x ⊓ y ⊔ z ≡ (x ⊔ z) ⊓ (y ⊔ z);
    hlubglbD x y z : (x ⊔ y) ⊓ z ≡ (x ⊓ z) ⊔ (y ⊓ z);
    hGalL x y z : x ⊓ z ≦ y → z ≦ x ⇒ y;
    hGalR x y z : z ≦ x ⇒ y → x ⊓ z ≦ y;
  }.

Section Instances.
  Context H {HO : HOps H} {HH : Heyt H}.

  #[export] Instance heq_sub : subrelation heq hord.
  Proof.
    now intros x y [LE _].
  Qed.

  #[export] Instance heq_subF : subrelation heq (Basics.flip hord).
  Proof.
    now intros x y [_ GE].
  Qed.

  #[export] Instance hequiv : Equivalence heq.
  Proof.
    split.
    - now split.
    - intros x y [LE GE]; now split.
    - intros x y z [LE₁ GE₁] [LE₂ GE₂]; split; etransitivity; eassumption.
  Qed.

  #[export] Instance hlubEQ : Proper (heq ==> heq ==> heq) hlub.
  Proof.
    intros x1 x2 EQx y1 y2 EQy.
    split; [now rewrite EQx, EQy | now rewrite <- EQx, <- EQy].
  Qed.

  #[export] Instance hglbEQ : Proper (heq ==> heq ==> heq) hglb.
  Proof.
    intros x1 x2 EQx y1 y2 EQy.
    split; [now rewrite EQx, EQy | now rewrite <- EQx, <- EQy].
  Qed.

  #[export] Instance hrpcEQ : Proper (heq ==> heq ==> heq) hrpc.
  Proof.
    intros x1 x2 EQx y1 y2 EQy.
    split; [now rewrite EQx, EQy | now rewrite <- EQx, <- EQy].
  Qed.

End Instances.

Record HAlg :=
  { HCarr :> Set;
    Hops  :: HOps HCarr;
    Hheyt :: Heyt HCarr
  }.

Notation "⟨ X ⟩ᴴ" := (Build_HAlg X _ _).
