From mathcomp Require Import under.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div choice fintype tuple finfun bigop.
From mathcomp Require Import prime binomial ssralg finset matrix.

(** * Additional lemma for [matrix] *)

Lemma eq_mx R m n (k : unit) (F1 F2 : 'I_m -> 'I_n -> R) : (F1 =2 F2) ->
  (\matrix[k]_(i, j) F1 i j)%R = (\matrix[k]_(i, j) F2 i j)%R.
Proof. by move=> Heq2; apply/matrixP => i j; rewrite !mxE Heq2. Qed.
Arguments eq_mx [R m n k F1] F2 _.

(** * Additional lemma for [finfun] *)

Lemma eq_ffun (aT : finType) rT (g1 g2 : aT -> rT) : g1 =1 g2 ->
  [ffun x => g1 x] = [ffun x => g2 x].
Proof. by move=> Heq1; apply/ffunP => x; rewrite !ffunE Heq1. Qed.

(** * Additional lemma for [finset] *)

Lemma eq_set (T : finType) (P1 P2 : pred T) :
  P1 =1 P2 -> [set x | P1 x] = [set x | P2 x].
Proof. by move=> H; apply/setP => x; rewrite !inE H. Qed.

(** * Examples and tests *)

Section Tests.

Local Open Scope ring_scope.
Import GRing.Theory.

(* A test with a ssr pattern arg *)
Let test_ssrpat (n : nat) (R : ringType) (f1 f2 g : nat -> R) :
  (\big[+%R/0%R]_(i < n) ((f1 i + f2 i) * g i) +
  \big[+%R/0%R]_(i < n) ((f1 i + f2 i) * g i) =
  \big[+%R/0%R]_(i < n) ((f1 i + f2 i) * g i) +
  \big[+%R/0%R]_(i < n) (f1 i * g i) + \big[+%R/0%R]_(i < n) (f2 i * g i))%R.
Proof.
under eq_bigr x rewrite mulrDl.
(* 3 occurrences are rewritten; the bigop variable becomes "x" *)

Undo 1.

under [[X in _ + X = _]] eq_bigr x rewrite mulrDl.

rewrite big_split /=.
by rewrite addrA.
Qed.

(* A test with a side-condition. *)
Let test_sc (n : nat) (R : fieldType) (f : nat -> R) :
  (forall k : 'I_n, 0%R != f k) ->
  (\big[+%R/0%R]_(k < n) (f k / f k) = n%:R)%R.
Proof.
move=> Hneq0; under eq_bigr ? rewrite divff; last by rewrite eq_sym.
under eq_bigr ? rewrite -[1]/(1%:R); rewrite -natr_sum.
by rewrite sum1_card cardT size_enum_ord.
Qed.

(* A test lemma for [under eq_bigr in] *)
Let test_rin (n : nat) (R : fieldType) (f : nat -> R) :
  (forall k : 'I_n, f k != 0%R) ->
  (\big[+%R/0%R]_(k < n) (f k / f k) = n%:R)%R -> True.
Proof.
move=> Hneq0 H.
do [under eq_bigr [? H] rewrite divff] in H.
done.
Qed.

(* A test lemma for [under eq_bigr under eq_bigl] *)
Let test_rl (A : finType) (n : nat) (F : A -> nat) :
  \big[addn/O]_(0 <= k < n)
  \big[addn/O]_(J in {set A} | #|J :&: [set: A]| == k)
  \big[addn/O]_(j in J) F j >= 0.
Proof.
under eq_bigr [k Hk] under eq_bigl J rewrite setIT. (* the bigop variables are kept *)
done.
Qed.

(* A test lemma for [under eq_bigl in] *)
Let test_lin (A : finType) (n : nat) (F : A -> nat) :
  \big[addn/O]_(J in {set A} | #|J :&: [set: A]| == 1%N)
  \big[addn/O]_(j in J) F j = \big[addn/O]_(j in A) F j -> True.
Proof.
move=> H.
do [under eq_bigl J rewrite setIT] in H. (* the bigop variable "J" is kept *)
done.
Qed.

(* A test lemma for matrices *)
Let test_addmxC (T : zmodType) (m n : nat) (A B : 'M[T]_(m, n)) :
  (A + B = B + A)%R.
Proof. by under eq_mx [? ?] rewrite addrC. Qed.

(* A test lemma for sets *)
Let test_setIC (T : finType) (A B : {set T}) : A :&: B = B :&: A.
Proof. by under eq_set ? rewrite andbC. Qed.

(* A test with several side-conditions *)
Let test_sc2 (n : nat) :
  \big[addn/O]_(i < n.+1) (n - i)%N = \big[addn/O]_(j < n.+1) j.
Proof.
rewrite (reindex (fun i : 'I_n.+1 => inord (n - i))); last first.
  apply/onW_bij/inv_bij=> -[i Hi]; rewrite inordK ?ltnS ?leq_subr // subKn //.
  by rewrite inord_val.
by under eq_bigr i do [rewrite inordK ?ltnS ?leq_subr // subKn; case: i].
Qed.

End Tests.
