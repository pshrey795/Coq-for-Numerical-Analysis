From Coq Require Import ZArith Reals Psatz Arith.Arith Ring. 
Require Import Coq.Logic.FunctionalExtensionality. 
From Coquelicot Require Import Coquelicot. 
From Flocq Require Import Core.
Require Import vcfloat.RAux.
Require Import Interval.Tactic.

Lemma Rplus_lt_r : forall r r' : R, (0 < r') -> (r < r + r'). 
Proof.
    intros r r' Hr'. 
    assert (H0 : (r + 0 < r + r')). {
        exact (Rplus_lt_compat_l r 0 r' Hr'). 
    }
    rewrite Rplus_0_r in H0. assumption. 
Qed.

Lemma Rplus_le_r : forall r r' : R, (0 <= r') -> (r <= r + r'). 
Proof.
    intros r r' Hr'. 
    assert (H0 : (r + 0 <= r + r')). {
        exact (Rplus_le_compat_l r 0 r' Hr'). 
    }
    rewrite Rplus_0_r in H0. assumption. 
Qed.

Lemma Rabs_scalar : forall x y : R, (0 < x) -> (Rabs (x * y) = x * Rabs y). 
Proof.
    intros x y Hx. rewrite Rabs_mult. rewrite Rabs_pos_eq. 
    - reflexivity. 
    - unfold "<=". left. assumption. 
Qed.