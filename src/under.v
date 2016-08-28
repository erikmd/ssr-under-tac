From mathcomp Require Import ssrmatching ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div choice fintype tuple finfun bigop.
From mathcomp Require Import prime binomial ssralg finset matrix.

(* Without this line, doesn't compile with Coq 8.5... (issue with ssrpattern) *)
Declare ML Module "ssreflect".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Erik Martin-Dorel, 2016 *)

(** * Additional lemma for [matrix] *)

Lemma eq_mx R m n (k : unit) (F1 F2 : 'I_m -> 'I_n -> R) : (F1 =2 F2) ->
  (\matrix[k]_(i, j) F1 i j)%R = (\matrix[k]_(i, j) F2 i j)%R.
Proof. by move=> Heq2; apply/matrixP => i j; rewrite !mxE Heq2. Qed.
Arguments eq_mx [R m n k F1] F2 _.

(** * Additional lemma for [finset] *)

Lemma eq_set (T : finType) (P1 P2 : pred T) :
  P1 =1 P2 -> [set x | P1 x] = [set x | P2 x].
Proof. by move=> H; apply/setP => x; rewrite !inE H. Qed.

(** [under_big] allows one to apply a given tactic under some bigop
or some matrix, and so on *)

(** * Tactic for rewriting under lambdas in MathComp *)

(** ** Preliminary tactics *)

Ltac clear_all h :=
  try unfold h in * |- *; try clear h.

Ltac clear_all3 h1 h2 h3 :=
  clear_all h1; clear_all h2; clear_all h3.

(** [do_pad_tac lem tac] pads lem with _'s, as Ltac does not handle implicits *)
Ltac do_pad_tac lem tac :=
  match type of lem with
  | forall x1 : ?A, forall x2 : _, forall p : _, _ =>
    (* idtac A; *)
    let a := fresh "a" in
    evar (a : A);
    let lem' := eval unfold a in (lem a) in
    do_pad_tac lem' tac; clear_all a
    | forall x2 : _, forall p : _, _ => tac lem
    | _ => fail 100 "Expecting a lemma whose type end with a function and a side-condition."
               "Cannot proceed with:" lem
    end.

(*
Tactic Notation "do_pad" open_constr(lem) tactic(tac) :=
  do_pad_tac lem tac.

Tactic Notation "ssrpat" ssrpatternarg(p) :=
  ssrpattern p.

(* This doesn't work:

Tactic Notation "rew" ssrpatternarg(pat) open_constr(equ) :=
  rewrite [pat]equ.
*)

(* Tests *)

Goal forall (R : ringType) (a b : R), (\sum_(i < 1) a + b = a + b)%R -> True.
intros.
do_pad eq_bigr (fun lhs => idtac lhs).
Abort.

Goal forall (R : ringType) (a b : 'M[R]_2), (a + b = b + a)%R.
intros.
do_pad eq_mx (fun l => pose proof l as L1).
apply: L1.
by move=> i j; rewrite GRing.addrC.
Qed.

Goal forall P1 P2,
    \big[addn/O]_(i < 5 | P1 i) i = \big[addn/O]_(i < 5 | P2 i) i.
intros.
do_pad (@eq_bigl _ _ _ _ _ _ _) (fun l => pose proof l as L1).
rewrite -> L1.
2: done.
set b := bigop _ _ _.
ssrpat [b].
Abort.
*)

(*
Ltac do_lhs_tac equ tac :=
  match type of equ with
  | forall p : _, ?a = ?b =>
    tac a
  | ?a = ?b =>
    tac a
  end.

Ltac do_rhs_tac equ tac :=
  match type of equ with
  | forall p : _, ?a = ?b =>
    tac b
  | ?a = ?b =>
    tac b
  end.

(* Test *)

Goal exists a : nat, a = a + 1 -> False.
eexists => H.
do_lhs_tac H ltac:(fun lhs => idtac lhs).
Abort.
 *)

Ltac do_sides_tac equ taclr :=
  match type of equ with
  | forall p : _, ?a = ?b =>
    taclr a b
  | ?a = ?b =>
    taclr a b
  end.

(** [rew_tac pat x2 equ] uses [equ] to rewrite occurrences of [pat]
and uses [x2] to avoid "evars leaking". *)
(* Can we do variable refolding? *)
Ltac rew_tac pat x2 equ :=
  ssrpattern pat; let top := fresh in move=> top;
  do_sides_tac
    equ
    ltac:(fun lhs rhs =>
            let top' := eval unfold top in top in
            let lhs' := eval unfold x2 in lhs in
            unify top' lhs' with typeclass_instances;
            rewrite [top]equ);
  clear_all top.

Ltac do_pat pat tac :=
  match goal with
    |- context [?x] =>
    unify pat x with typeclass_instances;
    tac x
  end.

(*
Tactic Notation "trypat" open_constr(pat) tactic(tac) :=
  do_pat pat tac.

(* Test *)
Goal forall (a : nat), \sum_(i < 1) (0 + a) = \sum_(i < 1) (0 + 0 + a).
intros.
trypat (bigop _ _ _) (fun l => have->: l = \sum_(i < 1) (a)).
Abort.
*)

(** [rew_tac1] is similar to [rew_tac] but ignores the [pat] variable.
Instead, it uses [equ] to rewrite the first occurrence of equ's lhs *)
Ltac rew_tac1 pat x2 equ :=
  (* rewrite equ. (* causes some evars leaking *) *)
  (* rewrite -> equ. (* could be possible also *) *)
  do_sides_tac
    equ
    ltac:(fun lhs rhs =>
            let lhs' := eval unfold x2 in lhs in
            do_pat
              lhs'
              ltac:(fun x =>
                let top := fresh in set top := x;
             (* let top' := eval unfold top in top in
                unify top' lhs' with typeclass_instances; (* unneeded *) *)
                rewrite [top]equ; clear_all top)).

(** ** The main tactic *)
Ltac under_tac rew pat lem intro_tac tac :=
  do_pad_tac
    lem
    ltac:(fun l =>
            let I := fresh "I" in
            let R := fresh "R" in
            let x2 := fresh "x2" in
            evar (I : Type);
            evar (R : Type);
            evar (x2 : I -> R);
            let lx2 := constr:(l x2) in
            rew pat x2 lx2;
            [clear_all3 x2 R I; cbv beta
            |intro_tac; (tac || fail 100 "Cannot apply tactic under lemma" lem);
             clear_all3 x2 R I; try done]).

(** ** The under tacticals (with no ssr pattern) *)

Tactic Notation "under"
       open_constr(lem) simple_intropattern(i) tactic(tac) :=
  under_tac rew_tac1 false lem ltac:(move=> i) tac.

Tactic Notation "under"
       open_constr(lem) "[" simple_intropattern(i) "]" tactic(tac) :=
  under_tac rew_tac1 false lem ltac:(move=> i) tac.

Tactic Notation "under"
       open_constr(lem) "[" simple_intropattern(i) simple_intropattern(Hi) "]" tactic(tac) :=
  under_tac rew_tac1 false lem ltac:(move=> i Hi) tac.

Tactic Notation "under"
       open_constr(lem) "[" simple_intropattern(i) simple_intropattern(j) simple_intropattern(Hij) "]" tactic(tac) :=
  under_tac rew_tac1 false lem ltac:(move=> i j Hij) tac.

(** ** The under tacticals, upto 3 vars to introduce in the context *)

Tactic Notation "under"
       ssrpatternarg(p) open_constr(lem) simple_intropattern(i) tactic(tac) :=
  under_tac rew_tac p lem ltac:(move=> i) tac.

(* Given the tactic grammar, we need to write "["..."]" below, else
the into_pattern would lead to unwanted case analysis. *)
Tactic Notation "under"
       ssrpatternarg(p) open_constr(lem) "[" simple_intropattern(i) "]" tactic(tac) :=
  under_tac rew_tac p lem ltac:(move=> i) tac.

Tactic Notation "under"
       ssrpatternarg(p) open_constr(lem) "[" simple_intropattern(i) simple_intropattern(Hi) "]" tactic(tac) :=
  under_tac rew_tac p lem ltac:(move=> i Hi) tac.

Tactic Notation "under"
       ssrpatternarg(p) open_constr(lem) "[" simple_intropattern(i) simple_intropattern(j) simple_intropattern(Hij) "]" tactic(tac) :=
  under_tac rew_tac p lem ltac:(move=> i j Hij) tac.

(** A shortcut when we want to rewrite the first occurrence of [bigop _ _ _] *)
Notation big := (bigop _ _ _) (only parsing).

(** [under] allows one to apply a given tactic under some bigop:
    if [pat] is a local variable (let-in) that appears in the goal,
    only the occurrences of [pat] will be rewritten;
    otherwise the occurrences of the first bigop that matches [pat]
    will be rewritten. *)

(** [underp...in] allows one to apply a given tactic for rewriting
    some bigop predicate:
    if [pat] is a local variable (let-in) that appears in H,
    only the occurrences of [pat] will be rewritten;
    otherwise the occurrences of the first bigop that matches [pat]
    will be rewritten. *)

(** * Tests and examples *)

Section Tests.

(* A test lemma covering several testcases. *)
Let test1 (n : nat) (R : ringType) (f1 f2 g : nat -> R) :
  (\big[+%R/0%R]_(i < n) ((f1 i + f2 i) * g i) +
  \big[+%R/0%R]_(i < n) ((f1 i + f2 i) * g i) =
  \big[+%R/0%R]_(i < n) ((f1 i + f2 i) * g i) +
  \big[+%R/0%R]_(i < n) (f1 i * g i) + \big[+%R/0%R]_(i < n) (f2 i * g i))%R.
Proof.
set b1 := {2}(bigop _ _ _).
under [b1] eq_bigr x rewrite GRing.mulrDl. (* only b1 is rewritten *)

Undo 1. rewrite /b1; clear b1.
under eq_bigr x rewrite GRing.mulrDl. (* 3 occurrences are rewritten *)

rewrite big_split /=.
by rewrite GRing.addrA.
Qed.

(* A test with a side-condition. *)
Let test2 (n : nat) (R : fieldType) (f : nat -> R) :
  (forall k : 'I_n, 0%R != f k) ->
  (\big[+%R/0%R]_(k < n) (f k / f k) = n%:R)%R.
Proof.
move=> Hneq0.
do [under eq_bigr ? rewrite GRing.divff]; last first. (* the bigop variable becomes "i" *)
by rewrite eq_sym.

rewrite big_const cardT /= size_enum_ord /GRing.natmul.
case: {Hneq0} n =>// n.
by rewrite iteropS iterSr GRing.addr0.
Qed.

(* Another test lemma when the bigop appears in some hypothesis *)
Let test3 (n : nat) (R : fieldType) (f : nat -> R) :
  (forall k : 'I_n, f k != 0%R) ->
  (\big[+%R/0%R]_(k < n) (f k / f k) +
  \big[+%R/0%R]_(k < n) (f k / f k) = n%:R + n%:R)%R -> True.
Proof.
move=> Hneq0 H.
set b1 := {2}big in H.
do [under [b1] eq_bigr ? rewrite GRing.divff] in H. (* only b1 is rewritten *)
done.
Qed.

(* A test lemma for [underp] *)
Let testp1 (A : finType) (n : nat) (F : A -> nat) :
  \big[addn/O]_(0 <= k < n)
  \big[addn/O]_(J in {set A} | #|J :&: [set: A]| == k)
  \big[addn/O]_(j in J) F j >= 0.
Proof.
under eq_bigr ? under eq_bigl J rewrite setIT. (* the bigop variables are NOT kept *)
done.
Qed.

(* A test lemma for [underp...in] *)
Let testp2 (A : finType) (n : nat) (F : A -> nat) :
  \big[addn/O]_(J in {set A} | #|J :&: [set: A]| == 1)
  \big[addn/O]_(j in J) F j = \big[addn/O]_(j in A) F j -> True.
Proof.
move=> H.
do [under eq_bigl J rewrite setIT] in H. (* the bigop variable "J" is NOT kept *)
done.
Qed.

(* A test lemma for matrices *)
Let test_addmxC (T : zmodType) (m n : nat) (A B : 'M[T]_(m, n)) :
  (A + B = B + A)%R.
Proof. by under eq_mx [? ?] rewrite GRing.addrC. Qed.

(* A test lemma for sets *)
Let test_setIC (T : finType) (A B : {set T}) : A :&: B = B :&: A.
Proof. by under eq_set ? rewrite andbC. Qed.

End Tests.
