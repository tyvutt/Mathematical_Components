From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Example Gauss n : \sum_(0 <= i < n.+1) i = (n * n.+1) %/ 2.
Proof.
elim: n =>[|n IHn]; first by apply: big_nat1.
rewrite big_nat_recr //= IHn addnC -divnMDl //.
by rewrite mulnS muln1 -addnA -mulSn -mulnS.
Qed.