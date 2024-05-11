Require Import Utf8.
Require Import List Syntax.
Require Import Heyting Interp.
Require Import Deduction.
Require Import RelationClasses Morphisms.

Section Lindenbaum.

  (* Carrier of Lindenbaum algebra does not depend on Γ, but its
     algebraic structure does, hence the definition. *)
  Definition LC {X} (Γ : list (prop X)) := prop X.

  Context {X : Set} (Γ : list (prop X)).

  #[export] Instance LOps : HOps (LC Γ) :=
    {|
      hord φ ψ := Γ ⊢ φ ↣ ψ;
      htop := ⊤;
      hbot := ⊥;
      hlub φ₁ φ₂ := φ₁ ⊼ φ₂;
      hglb φ₁ φ₂ := φ₁ ⊻ φ₂;
      hrpc φ ψ := φ ↣ ψ
    |}%prop.

  #[export] Instance LHeyt : Heyt (LC Γ).
  Proof.
    split.
    - split.
      + intros φ; simpl.
        apply ImplI, Ax; now left.
      + intros φ ψ χ HP₁ HP₂; simpl in *.
        apply ImplI, ImplE with ψ, ImplE with φ, Ax; [now apply wkn .. | now left].
    - intros φ; simpl.
      apply ImplI, TrueI.
    - intros φ; simpl.
      apply ImplI, FalseE, Ax; now left.
    - intros φ₁ ψ₁ HP₁ φ₂ ψ₂ HP₂; simpl in *.
      apply ImplI, ConjI.
      + apply ImplE with φ₁, ConjEL with φ₂, Ax; [now apply wkn | now left].
      + apply ImplE with φ₂, ConjER with φ₁, Ax; [now apply wkn | now left].
    - intros φ₁ ψ₁ HP₁ φ₂ ψ₂ HP₂; simpl in *.
      apply ImplI, DisjE with φ₁ φ₂; [apply Ax; now left | |].
      + apply DisjIL, ImplE with φ₁, Ax; [now apply wkn, wkn | now left].
      + apply DisjIR, ImplE with φ₂, Ax; [now apply wkn, wkn | now left].
    - intros φ₁ ψ₁ HP₁ φ₂ ψ₂ HP₂; simpl in *.
      apply ImplI, ImplI.
      apply ImplE with φ₂, ImplE with φ₁, ImplE with ψ₁, Ax; [.. | now left].
      + now apply wkn, wkn.
      + apply wkn, Ax; now left.
      + now apply wkn, wkn.
    - intros φ₁ φ₂; split; simpl;
        (apply ImplI, ConjI; [eapply ConjER | eapply ConjEL]; apply Ax; now left).
    - intros φ₁ φ₂; split; simpl; apply ImplI.
      + eapply DisjE; [apply Ax; now left | apply DisjIR, Ax; now left | apply DisjIL, Ax; now left].
      + eapply DisjE; [apply Ax; now left | apply DisjIR, Ax; now left | apply DisjIL, Ax; now left].
    - intros φ₁ φ₂ φ₃; split; simpl; apply ImplI.
      + apply ConjI, ConjI; [eapply ConjEL, ConjEL, Ax | eapply ConjER, ConjEL, Ax | eapply ConjER, Ax]; now left.
      + eapply ConjI, ConjER, ConjER, Ax; [apply ConjI | now left].
        * eapply ConjEL, Ax; now left.
        * eapply ConjEL, ConjER, Ax; now left.
    - intros φ₁ φ₂ φ₃; split; simpl; apply ImplI.
      + eapply DisjE; [apply Ax; now left | eapply DisjE; [apply Ax; now left | |] |].
        * apply DisjIL, Ax; now left.
        * apply DisjIR, DisjIL, Ax; now left.
        * apply DisjIR, DisjIR, Ax; now left.
      + eapply DisjE; [apply Ax; now left | | eapply DisjE; [apply Ax; now left | |]].
        * apply DisjIL, DisjIL, Ax; now left.
        * apply DisjIL, DisjIR, Ax; now left.
        * apply DisjIR, Ax; now left.
    - intros φ; split; simpl; apply ImplI; [| apply ConjI; apply Ax; now left].
      eapply ConjEL, Ax; now left.
    - intros φ; split; simpl; apply ImplI; [| apply DisjIL, Ax; now left].
      eapply DisjE; apply Ax; now left.
    - intros φ; split; simpl; apply ImplI; [eapply ConjEL, Ax; now left |].
      apply ConjI; [apply Ax; now left | apply TrueI].
    - intros φ; split; simpl; apply ImplI; [| apply DisjIL, Ax; now left].
      eapply DisjE; [apply Ax; now left .. | apply FalseE, Ax; now left].
    - intros φ₁ φ₂ ψ; split; simpl; apply ImplI.
      + apply ConjI; (eapply DisjE; [apply Ax; now left | | apply DisjIR, Ax; now left]).
        * eapply DisjIL, ConjEL, Ax; now left.
        * eapply DisjIL, ConjER, Ax; now left.
      + eapply DisjE; [eapply ConjEL, Ax; now left | | apply DisjIR, Ax; now left].
        eapply DisjE; [eapply ConjER, Ax; right; now left | | apply DisjIR, Ax; now left].
        apply DisjIL, ConjI; apply Ax; simpl; tauto.
    - intros φ₁ φ₂ ψ; split; simpl; apply ImplI.
      + eapply DisjE; [eapply ConjEL, Ax; now left | |].
        * apply DisjIL, ConjI; [apply Ax; now left | eapply ConjER, Ax; right; now left].
        * apply DisjIR, ConjI; [apply Ax; now left | eapply ConjER, Ax; right; now left].
      + eapply DisjE; [apply Ax; now left | apply ConjI; [| eapply ConjER, Ax; now left] ..].
        * eapply DisjIL, ConjEL, Ax; now left.
        * eapply DisjIR, ConjEL, Ax; now left.
    - intros φ ψ χ HP; simpl in *; apply ImplI, ImplI.
      eapply ImplE; [apply wkn, wkn, HP | apply ConjI; apply Ax; simpl; tauto].
    - intros φ ψ χ HP; simpl in *; apply ImplI.
      apply ImplE with φ; [| eapply ConjEL, Ax; now left].
      apply ImplE with χ; [| eapply ConjER, Ax; now left].
      now apply wkn.
  Qed.

End Lindenbaum.

Section Completeness.
  Context {X : Set}.

  Lemma modLpf (φ : prop X) : ∀ Γ, Γ ⊢ 〚 φ 〛 (pvar : X → LC Γ) ↔ Γ ⊢ φ.
  Proof.
    induction φ; intros Γ; simpl in *; try tauto; [| |]; split; intros HP.
    - apply ConjI; [eapply IHφ1, ConjEL, HP | eapply IHφ2, ConjER, HP].
    - apply ConjI; [eapply IHφ1, ConjEL, HP | eapply IHφ2, ConjER, HP].
    - eapply DisjE; [exact HP | apply DisjIL, IHφ1, Ax; now left | apply DisjIR, IHφ2, Ax; now left].
    - eapply DisjE; [exact HP | apply DisjIL, (IHφ1 (_ :: _)), Ax; now left | apply DisjIR, (IHφ2 (_ :: _)), Ax; now left].
    - eapply ImplI, IHφ2, ImplE; [apply wkn, HP |].
      apply (IHφ1 (_ :: _)), Ax; now left.
    - eapply ImplI, (IHφ2 (_ :: _)), ImplE; [apply wkn, HP |].
      apply (IHφ1 (_ :: _)), Ax; now left.
  Qed.

  Lemma modLC Γ : Γ ⊢ 〚 Γ 〛ᶜ (pvar : X → LC Γ).
  Proof.
    induction Γ; simpl; [apply TrueI | apply ConjI; [| apply wkn, IHΓ]].
    apply modLpf, Ax; now left.
  Qed.

  Theorem completeness Γ (φ : prop X) : Γ ⊨ φ → Γ ⊢ φ.
  Proof.
    intros HM; specialize (HM ⟨ LC Γ ⟩ᴴ); simpl in HM; unfold holdsH, LC in HM.
    specialize (HM pvar); simpl in HM.
    eapply modLpf, ImplE; [eassumption | apply modLC].
  Qed.

End Completeness.
