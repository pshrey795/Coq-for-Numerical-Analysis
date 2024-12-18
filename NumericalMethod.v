From Coq Require Import ZArith Reals Psatz Arith.Arith Ring. 
Require Import Coq.Logic.FunctionalExtensionality. 
From Coquelicot Require Import Coquelicot. 
From Project Require Import Base.

Open Scope R_scope. 

(* Numerical Algorithm: Forward Euler *)
Definition euler_step (dt : R) (lambda : R) (yn : R) : R := (yn * (1 - dt * lambda)). 

Fixpoint euler (y0 : R) (lambda : R) (dt : R) (n : nat) : R := 
match n with
| 0%nat => y0 
| S n'  => euler_step dt lambda (euler y0 lambda dt n') 
end.

Close Scope R_scope. 