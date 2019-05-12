(*Tested under Coq 8.9.0 in Windows, Coq 8.8.1 and Coq 8.4pl6 in Linux*)
(*==========timed data argument stream=============*)
Require Import Reals.
Require Import Streams.

Open Scope type_scope.
Definition Time := R.
Definition Data := nat.
(*using 2 extra arguments in this example,
can be modified for other examples.*)
Definition Arg := R*R.
Definition TAD := Time*Arg*Data.
Definition PrL {A B C: Type}(pair: A * B * C) :=
  match pair with
  | (a, b, c) => a
  end.
Definition PrR {A B C: Type}(pair: A * B * C) :=
  match pair with
  | (a, b, c) => c
  end.
Definition PrM0 {A B C D: Type}(pair: A * (B * C) * D) :=
  match pair with
  | (a, (b, c), d) => b
  end.
Definition PrM1 {A B C D: Type}(pair: A * (B * C) * D) :=
  match pair with
  | (a, (b, c), d) => c
  end.

Definition Deq(s1 s2:Stream TAD) : Prop :=
  forall n:nat, PrR(Str_nth n s1) = PrR(Str_nth n s2).

Open Scope R_scope.

(*===========channal definitiom=============*)
Definition hyCon1(Input Output:Stream TAD):Prop:=
(Deq Input Output)/\
(forall n:nat,(PrM0(Str_nth n Input)<=PrM1(Str_nth n Input) ->(
PrM0(Str_nth n Input)=PrM0(Str_nth n Output) /\
PrM1(Str_nth n Input)=PrM1(Str_nth n Output) /\
PrL(Str_nth n Input)=PrL(Str_nth n Output)
))/\(PrM0(Str_nth n Input)>=PrM1(Str_nth n Input)->(
PrM1(Str_nth n Input)=PrM0(Str_nth n Output) /\
PrM1(Str_nth n Input)=PrM1(Str_nth n Output) /\
PrL(Str_nth n Input)+PrM0(Str_nth n Input)-PrM1(Str_nth n Input)
=PrL(Str_nth n Output)
))).

Definition hyCon2(Input Output:Stream TAD):Prop:=
(Deq Input Output)/\
(forall n:nat,(PrM0(Str_nth n Input)>=PrM1(Str_nth n Input) ->(
PrM0(Str_nth n Input)=PrM0(Str_nth n Output) /\
PrM1(Str_nth n Input)=PrM1(Str_nth n Output) /\
PrL(Str_nth n Input)=PrL(Str_nth n Output)
))/\(PrM0(Str_nth n Input)<=PrM1(Str_nth n Input)->(
PrM0(Str_nth n Input)=PrM1(Str_nth n Output) /\
PrM0(Str_nth n Input)=PrM0(Str_nth n Output) /\
PrL(Str_nth n Input)+PrM1(Str_nth n Input)-PrM0(Str_nth n Input)
=PrL(Str_nth n Output)
))).

(*===========lemma list============*)
Lemma R_eq:forall(a b:R),a+b-b=a.
Proof.
intros.
assert(a+b-b=a+(b-b)).
apply Rplus_assoc.
rewrite H.
assert(b-b=0).
apply Rplus_opp_r.
rewrite H0.
apply Rplus_0_r.
Qed.

Lemma R_total:forall(a b:R),a<=b\/a>b.
Proof.
intros.
assert(a<=b\/b<a).
apply Rle_or_lt.
destruct H;auto.
Qed.

Lemma transfer_eq:forall(s1 s2 s3:Stream TAD),
Deq s1 s2 /\ Deq s2 s3 -> Deq s1 s3.
Proof.
intros.
destruct H.
intro.
assert(PrR (Str_nth n s1) = PrR (Str_nth n s2)).
apply H.
assert(PrR (Str_nth n s2) = PrR (Str_nth n s3)).
apply H0.
rewrite H1.
apply H2.
Qed.

Lemma reflex_eq:forall(s1 s2:Stream TAD),
Deq s1 s2->Deq s2 s1.
Proof.
intros.
intro.
pose(H1:=H(n)).
symmetry.
assumption.
Qed.

Lemma eq_PrM1:forall(A B:Stream TAD)(n:nat),
(PrM0 (Str_nth n A) <= PrM1 (Str_nth n A))/\(hyCon1 A B)->
PrM1 (Str_nth n A) = PrM1 (Str_nth n B).
Proof.
intros.
destruct H.
destruct H0.
pose(H2:=H1(n)).
destruct H2.
apply H2.
assumption.
Qed.

Lemma exist_output:forall(A:Stream TAD),(exists D,hyCon2 A D).
admit.
Admitted.

Theorem Example:forall(A B:Stream TAD),
(exists C,(hyCon1 A C)/\(hyCon2 C B))->
(exists D,(hyCon2 A D)/\(hyCon1 D B)).
Proof.
intros.
destruct H as [E].
destruct H.
(*prove the relation between A and B*)
assert((Deq A B)/\
(forall n:nat,(PrM0(Str_nth n A)>=PrM1(Str_nth n A) ->(
PrM1(Str_nth n A)=PrM0(Str_nth n B) /\
PrM1(Str_nth n A)=PrM1(Str_nth n B) /\
PrL(Str_nth n A)+PrM0(Str_nth n A)-PrM1(Str_nth n A)
=PrL(Str_nth n B)
))/\(PrM0(Str_nth n A)<=PrM1(Str_nth n A)->(
PrM0(Str_nth n A)=PrM1(Str_nth n B) /\
PrM0(Str_nth n A)=PrM0(Str_nth n B) /\
PrL(Str_nth n A)+PrM1(Str_nth n A)-PrM0(Str_nth n A)
=PrL(Str_nth n B)
)))).

split.
assert(Deq A E).
apply H.
assert(Deq E B).
apply H0.
apply(transfer_eq (A)(E)(B)).
auto.

intro.
split.
intro.

assert(PrM1 (Str_nth n E) = PrM0 (Str_nth n E)).
assert(PrM1 (Str_nth n A) = PrM0 (Str_nth n E)).
apply H.
assumption.
assert(PrM1 (Str_nth n A) = PrM1 (Str_nth n E)).
apply H.
assumption.
rewrite<-H2.
symmetry.
assumption.

split.
assert(PrM1 (Str_nth n A) = PrM0 (Str_nth n E)).
apply H.
assumption.
assert(PrM0 (Str_nth n E) = PrM0 (Str_nth n B)).
apply H0.
rewrite H2.
apply Req_le.
auto.
rewrite H3.
assumption.

split.
assert(PrM1 (Str_nth n A) = PrM1 (Str_nth n E)).
apply H.
assumption.
assert(PrM1 (Str_nth n B) = PrM1 (Str_nth n E)).
rewrite H2.
symmetry.
apply H0.
rewrite H2.
apply Req_le.
auto.
rewrite H3.
symmetry.
assumption.

assert(PrL (Str_nth n A) + PrM0 (Str_nth n A) - PrM1 (Str_nth n A) 
= PrL (Str_nth n E)).
apply H.
assumption.
rewrite H3.
apply H0.
rewrite H2.
apply Req_le.
auto.

intros.
assert(PrM0 (Str_nth n A) = PrM0 (Str_nth n E)).
apply H.
assumption.
assert(PrL (Str_nth n A) = PrL (Str_nth n E)).
apply H.
assumption.
assert(PrM1 (Str_nth n A) = PrM1 (Str_nth n E)).
apply eq_PrM1.
split.
assumption.
assumption.

split.
rewrite H2.
apply H0.
rewrite<-H2.
rewrite<-H4.
assumption.

split.
rewrite H2.
apply H0.
rewrite<-H2.
rewrite<-H4.
assumption.

rewrite H2.
rewrite H3.
rewrite H4.
apply H0.
rewrite<-H2.
rewrite<-H4.
assumption.

(*verify the relation between D and B*)
pose(H2:=exist_output(A)).
destruct H2 as [D].
exists D.
split.
assumption.
split.
destruct H2.
destruct H1.
assert(Deq D A).
apply reflex_eq.
assumption.
apply (transfer_eq D A B).
split;assumption.
destruct H2.
(*divided into 2 cases*)
assert(forall(n:nat),PrM0 (Str_nth n A) <= PrM1 (Str_nth n A)\/
PrM0 (Str_nth n A) > PrM1 (Str_nth n A)).
intro.
apply R_total.
intro.
pose(H5:=H4(n)).
destruct H5.

(*Case1:PrM0 (Str_nth n A) <= PrM1 (Str_nth n A)*)
split.
intro.
split.
pose(H8:=H3(n)).
assert(PrM0 (Str_nth n A) = PrM0 (Str_nth n D)).
apply H8.
assumption.
rewrite<-H7.
apply H1.
assumption.
split.
pose(H8:=H3(n)).
assert(PrM0 (Str_nth n A) = PrM1 (Str_nth n D)).
apply H8.
assumption.
rewrite<-H7.
apply H1.
assumption.
pose(H8:=H3(n)).
assert(PrL (Str_nth n A) + PrM1 (Str_nth n A) - PrM0 (Str_nth n A) = 
PrL (Str_nth n D)).
apply H8.
assumption.
rewrite<-H7.
apply H1.
assumption.
intro.
split.
pose(H8:=H3(n)).
assert(PrM0 (Str_nth n A) = PrM1 (Str_nth n D)).
apply H8.
assumption.
rewrite<-H7.
apply H1.
assumption.
split.
pose(H8:=H3(n)).
assert(PrM0 (Str_nth n A) = PrM1 (Str_nth n D)).
apply H8.
assumption.
rewrite<-H7.
apply H1.
assumption.
assert(PrM0 (Str_nth n D) = PrM1 (Str_nth n D)).
pose(H8:=H3(n)).
assert(PrM0 (Str_nth n A) = PrM1 (Str_nth n D)).
apply H8.
assumption.
rewrite<-H7.
symmetry.
apply H8.
assumption.
rewrite H7.
pose(H9:=H3(n)).
assert(PrL (Str_nth n A) + PrM1 (Str_nth n A) - PrM0 (Str_nth n A) 
= PrL (Str_nth n D)).
apply H9.
assumption.
assert(PrL (Str_nth n D)=PrL (Str_nth n B)).
rewrite<-H8.
apply H1.
assumption.
rewrite H10.
apply R_eq.

(*Case2:PrM0 (Str_nth n A) > PrM1 (Str_nth n A)*)
pose(H7:=H3(n)).
split.
intro.
assert(PrM0 (Str_nth n D) > PrM1 (Str_nth n D)).
assert(PrM0 (Str_nth n D) = PrM0 (Str_nth n A)).
destruct H7.
symmetry.
apply H7.
apply Rgt_ge.
assumption.
assert(PrM1 (Str_nth n D) = PrM1 (Str_nth n A)).
symmetry.
apply H7.
apply Rgt_ge.
assumption.
rewrite H8.
rewrite H9.
assumption.
assert(~(PrM0 (Str_nth n D) <= PrM1 (Str_nth n D))).
apply Rgt_not_le.
assumption.
pose(pf_False:=H9 H6).
case pf_False.
intro.
split.
assert(PrM1 (Str_nth n D) = PrM1 (Str_nth n A)).
symmetry.
apply H7.
apply Rgt_ge.
assumption.
rewrite H8.
apply H1.
apply Rgt_ge.
assumption.
split.
assert(PrM1 (Str_nth n D) = PrM1 (Str_nth n A)).
symmetry.
apply H7.
apply Rgt_ge.
assumption.
rewrite H8.
apply H1.
apply Rgt_ge.
assumption.
assert(PrL (Str_nth n A) + PrM0 (Str_nth n A) - PrM1 (Str_nth n A) 
= PrL (Str_nth n B)).
apply H1.
apply Rgt_ge.
assumption.
rewrite<-H8.
assert(PrM1 (Str_nth n D) = PrM1 (Str_nth n A)).
symmetry.
apply H7.
apply Rgt_ge.
assumption.
rewrite H9.
assert(PrL (Str_nth n D) = PrL (Str_nth n A)).
symmetry.
apply H7.
apply Rgt_ge.
assumption.
rewrite H10.
assert(PrM0 (Str_nth n D) = PrM0 (Str_nth n A)).
destruct H7.
symmetry.
apply H7.
apply Rgt_ge.
assumption.
rewrite H11.
auto.
Qed.
