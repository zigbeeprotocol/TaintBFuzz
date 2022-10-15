Require Import List.

Inductive mark : Set := Start | NotSeen | Modif | SameVal.

Lemma m_eq : forall m1 m2 : mark, {m1=m2}+{m1<>m2}.
Proof.
induction m1; induction m2; try solve [left; auto]; right; intro H; discriminate H.
Qed.

Definition merge m1 m2 : mark := match m1, m2 with
    | Start, _ | _, Start => Start
    | NotSeen, m | m, NotSeen => m
    | Modif, _ | _, Modif => Modif
    | SameVal, SameVal => SameVal
end.

Lemma mergeNotSeen : forall m1 m2, merge m1 m2 = NotSeen -> m1 = NotSeen /\ m2 = NotSeen.
Proof.
intros m1 m2 H.
destruct m1; destruct m2; simpl in H; try discriminate H; auto.
Qed.

Fixpoint lmerge (l:list mark) : mark := match l with
| nil => NotSeen
| m::tl => merge m (lmerge tl)
end.

Lemma lmergeNotSeen : forall l, lmerge l = NotSeen ->
  forall m, In m l -> m = NotSeen.
Proof.
induction l; intros H m Im.
elim Im.
simpl In in Im; destruct Im.
subst a.
simpl in H.
unfold merge in H; destruct m; try discriminate H;
  destruct (lmerge l); try discriminate H; auto.
simpl in H.
destruct (mergeNotSeen _ _ H).
apply IHl; auto.
Qed.

Lemma lmergeSameVal : forall l, lmerge l = SameVal ->
  forall m, In m l -> m <> NotSeen -> m = SameVal.
Proof.
induction l.
intro H; simpl in H; discriminate H.
intros H m Im Hn.
simpl in H.
simpl in Im; destruct Im.
subst a.
destruct m; try discriminate Hn; auto.
elim Hn; auto.
simpl in H. destruct (lmerge l) in H; discriminate H.

unfold merge in H; destruct a; try discriminate H;
  destruct (lmerge l) in H; try discriminate H; auto.
elim Hn; apply (lmergeNotSeen l Heqm0); auto.
Qed.

Lemma lmergeStart : forall l,
  lmerge l = Start -> In Start l.
Proof.
induction l; intros H.
simpl in H. discriminate H.

simpl.
destruct (m_eq a Start).
subst a; auto. right; apply IHl.

simpl in H; unfold merge in H.
destruct a; simpl in H.
elim n; auto.

destruct (lmerge l) in H; auto; try discriminate H.
destruct (lmerge l) in H; auto; try discriminate H.
destruct (lmerge l) in H; auto; try discriminate H.
Qed.

Lemma Start_in_lmerge : forall l,
  In Start l -> lmerge l = Start.
Proof.
induction l; intros H.
elim H.
simpl In in H; destruct H.
subst a; simpl; auto.
simpl.
rewrite (IHl H).
unfold merge; destruct a; auto.
Qed.


(* Lemma lmergeModif : forall l, 
  lmerge l <> Modif -> lmerge l <> Start -> forall m, In m l -> m <> Modif.
Proof.
induction l; intros Hm Hs m I.
elim I.

destruct (m_eq a m).
subst a; clear I.
intro H; elim Hm; subst m.
simpl.
simpl in Hm, Hs.
destruct (lmerge l); auto.
elim Hs; auto.

apply IHl.
intro H; elim Hm; simpl.
rewrite H; unfold merge; simpl.

SearchAbout In.
*)

Parameter inst : Set.
Parameter modif : inst -> bool.
Parameter succ : inst -> list inst.
Parameter pred : inst -> list inst.
Axiom pred_succ : forall i1 i2, In i1 (pred i2) <-> In i2 (succ i1).

(** fonction de transfert *)
Definition trans inst m := 
  if modif inst then Modif else if m_eq m Start then SameVal else m.

(** La fonction de transfert ne donne jamais Start *)
Lemma trans_not_Start : forall i m, trans i m <> Start.
Proof.
intros i m. 
unfold trans. 
destruct (modif i); auto; 
  destruct (m_eq m Start); auto; discriminate. 
Qed.

Lemma transModif : forall i m, trans i m = Modif -> modif i = true \/ m = Modif.
Proof.
intros i m.
unfold trans.
destruct (modif i); auto.
destruct (m_eq m Start); intro H.
discriminate H.
right; auto.
Qed.

Lemma transSameValnotModif : forall i m, trans i m = SameVal -> modif i = false.
Proof.
intros i m.
unfold trans.
destruct (modif i); auto.
intro H; discriminate H.
Qed.

Lemma transSameVal : forall i m, 
  trans i m = SameVal -> m <> Start -> m = SameVal.
Proof.
intros i m.
unfold trans.
destruct (modif i); auto.
intro H; discriminate H.
destruct (m_eq m Start); auto.
intros _ H; elim H; auto.
Qed.

Lemma transNotSeen : forall i m, m <> NotSeen -> trans i m <> NotSeen.
Proof.
intros i m H.
unfold trans.
destruct (modif i); auto.
discriminate.
destruct (m_eq m Start); auto; discriminate.
Qed.

(*---------------------------------------------------------------------------------*)
(** Marquage par analyse avant *)
Parameter ma : inst -> inst -> mark.

Axiom maStart : forall L I, ma L I = Start -> L = I.
Axiom maL : forall L, ma L L = Start.

(** propriété du marquage après stabilité *)
Axiom Pma : forall L i', 
  ma L i' = lmerge (List.map (fun i => trans i (ma L i)) (pred i')).

(** Scope Sc_a *)
Inductive sa (L i :inst) : Prop :=
| Sst : ma L i = Start -> sa L i
| Ssv : ma L i = SameVal -> sa L i
.

Lemma maSameValnotModif : forall L i, 
  ma L i = SameVal -> forall p, In p (pred i) -> ma L p <> NotSeen -> modif p = false.
Proof.
intros L i Hsv p Ip Hns.
rewrite (Pma L i) in Hsv.
apply (transSameValnotModif p (ma L p)).
apply (lmergeSameVal _ Hsv).

set (f := fun i0 : inst => trans i0 (ma L i0)) in *.
assert (M := in_map f (pred i) p Ip).
apply M.
apply transNotSeen; auto.
Qed.

Theorem Psa1 : forall L P, sa L P -> L <> P -> 
  forall I, In I (pred P) -> ma L I <> NotSeen -> modif I = false.
Proof.
intros L P saP LP I inI Hn.
destruct saP; auto.
elim LP; apply maStart; auto.
eapply (maSameValnotModif L); eauto.
Qed.

Theorem Psa2 : forall L P, sa L P -> L <> P -> 
  forall I, In I (pred P) -> ma L I <> NotSeen ->
  sa L I.
Proof.
intros L P saP LP I inI Hn.
destruct saP; auto.
elim LP; apply maStart; auto.
destruct (m_eq (ma L I) Start).
apply Sst; auto.

apply Ssv; auto.
apply (transSameVal I); auto.
assert (A := Pma L P).
rewrite H in A. symmetry in A.
eapply  lmergeSameVal; eauto.

set (f := fun i0 : inst => trans i0 (ma L i0)) in *.
replace (trans I (ma L I)) with (f I).
apply in_map; auto.
unfold f; simpl; auto.

apply transNotSeen; auto.
Qed.
