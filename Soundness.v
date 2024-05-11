Require Import Utf8.
Require Import List Syntax.
Require Import Heyting Interp.
Require Import Deduction.

Section Soundness.
  Context {H} {HO : HOps H} {HH : Heyt H} {X : Set}.

  Lemma soundI Γ (φ : prop X) (HP : Γ ⊢ φ) : holdsH H Γ φ.
  Proof.
    intros ϑ; induction HP; simpl.
    - induction Γ; [contradiction | destruct In as [EQ | In]; [subst a |]; simpl].
      + now rewrite (htopU (〚 Γ 〛ᶜ ϑ)), hlubT.
      + rewrite (htopU (〚 a 〛 ϑ)), hlubC, hlubT.
        now apply IHΓ.
    - apply htopU.
    - rewrite <- (hlubI (〚 Γ 〛ᶜ ϑ)), IHHP1 at 1; now rewrite IHHP2.
    - now rewrite <- (hbotB (〚 ψ 〛 ϑ)), hglbB.
    - now rewrite <- (hbotB (〚 φ 〛 ϑ)), hglbC, hglbB.
    - apply hGalL, IHHP.
    - rewrite IHHP; simpl.
      apply hbotB.
    - rewrite IHHP; simpl.
      now rewrite (htopU (〚 ψ 〛 ϑ)), hlubT.
    - rewrite IHHP; simpl.
      now rewrite (htopU (〚 φ 〛 ϑ)), hlubC, hlubT.
    - rewrite <- (hlubI (〚 Γ 〛ᶜ ϑ)), IHHP1 at 1; simpl.
      now rewrite hlubglbD, IHHP2, IHHP3, hglbI.
    - rewrite <- (hlubI (〚 Γ 〛ᶜ ϑ)), IHHP2 at 1; simpl.
      now apply hGalR.
  Qed.

End Soundness.

Theorem soundness {X} Γ (φ : prop X) : Γ ⊢ φ → Γ ⊨ φ.
Proof.
  intros HP HH; now apply soundI.
Qed.
