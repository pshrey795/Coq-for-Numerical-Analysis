From Coq Require Import ZArith Reals Psatz Arith.Arith Ring. 
Require Import Coq.Logic.FunctionalExtensionality. 
From Coquelicot Require Import Coquelicot. 
From Project Require Import Base ODE NumericalMethod LocalError.

Open Scope R_scope. 

Theorem global_error_bounded :
    forall y : R -> R,
    forall lambda t0 dt : R,
    0 < lambda -> 
    0 < dt ->  
    0 < (lambda * dt) < 1 -> 
    exp_ode lambda y ->
    forall n : nat,
    (Rabs ((y (t0 + (INR n) * dt)) - (euler (y t0) lambda dt n))) <= INR n * (((lambda * dt)^2 * (Rabs (y t0))) / INR 2).
Proof. 
    intros y lambda t0 dt Hl Hdt Hlt Hy n. 
    (* Step 1: Induction *)
    induction n. 
    - simpl. repeat rewrite (Rmult_0_l). rewrite Rplus_0_r. 
        rewrite Rminus_diag. rewrite Rabs_right; try lra. 
    (* Step 2: Simplify *)
    - assert (Hsimpl : forall n0 : nat, INR (S n0) = (INR n0) + 1). 
    { 
        induction n0. 
        - simpl. rewrite Rplus_0_l. reflexivity. 
        - reflexivity. 
    }
    rewrite Hsimpl.
    assert (Hsimpl' : forall n0 : nat, t0 <= t0 + INR n0 * dt). 
    { 
        intros n0. apply (Rplus_le_r t0 (INR n0 * dt)). induction n0. 
        - simpl. rewrite Rmult_0_l. lra.   
        - rewrite Hsimpl. rewrite (Rmult_plus_distr_r (INR n0) 1 dt). 
            apply (Rle_trans (0) (INR n0 * dt) (INR n0 * dt + 1 * dt)). 
            + assumption. 
            + rewrite Rmult_1_l. apply (Rplus_le_r (INR n0 * dt) dt). left. assumption. 
    }
    assert (Hsimpl2 : t0 + (INR n + 1) * dt = t0 + (INR n) * dt + dt). { lra. }
    rewrite Hsimpl2. clear Hsimpl2. 
    assert (Hsimpl2 : forall r1 r2 : R, r1 - r2 + r2 = r1). { intros r1 r2. lra. }
    rewrite <- (Hsimpl2 (y (t0 + INR n * dt + dt)) (euler_step dt lambda (y (t0 + INR n * dt)))).
    clear Hsimpl2. 
    rewrite (Rplus_comm (INR n) 1). 
    rewrite (Rmult_plus_distr_r 1 (INR n) (((lambda * dt) ^ 2 * Rabs (y t0)) / INR 2)). rewrite Rmult_1_l. 
    apply (Rle_trans (Rabs
(y (t0 + INR n * dt + dt) - euler_step dt lambda (y (t0 + INR n * dt)) + euler_step dt lambda (y (t0 + INR n * dt)) - euler (y t0) lambda dt (S n))) 
(Rabs (y (t0 + INR n * dt + dt) - euler_step dt lambda (y (t0 + INR n * dt))) + Rabs (euler_step dt lambda (y (t0 + INR n * dt)) - euler (y t0) lambda dt (S n))) 
((lambda * dt) ^ 2 * Rabs (y t0) / INR 2 + INR n * ((lambda * dt) ^ 2 * Rabs (y t0) / INR 2))). 
    (* Step 3: Triangle Inequality *)
    - assert (Hsimpl2 : y (t0 + INR n * dt + dt) - euler_step dt lambda (y (t0 + INR n * dt)) +
euler_step dt lambda (y (t0 + INR n * dt)) - euler (y t0) lambda dt (S n) = y (t0 + INR n * dt + dt) - euler_step dt lambda (y (t0 + INR n * dt)) +
(euler_step dt lambda (y (t0 + INR n * dt)) - euler (y t0) lambda dt (S n))). { lra. }
        rewrite Hsimpl2. rewrite (Rabs_triang (y (t0 + INR n * dt + dt) - euler_step dt lambda (y (t0 + INR n * dt))) 
        (euler_step dt lambda (y (t0 + INR n * dt)) - euler (y t0) lambda dt (S n))). 
        apply Rle_refl. 
    (* Step 4: Induction Hypothesis *)
    - apply (Rplus_le_compat (Rabs (y (t0 + INR n * dt + dt) - euler_step dt lambda (y (t0 + INR n * dt)))) 
    ((lambda * dt) ^ 2 * Rabs (y t0) / INR 2)
    (Rabs (euler_step dt lambda (y (t0 + INR n * dt)) - euler (y t0) lambda dt (S n)))
    ((INR n * ((lambda * dt) ^ 2 * Rabs (y t0) / INR 2)))).
    + apply (local_error_bounded y lambda t0 (t0 + INR n * dt) dt Hl Hdt (Hsimpl' n) Hlt Hy).
    + simpl in *. clear Hsimpl Hsimpl'. unfold euler_step. 
    assert (Hsimpl : forall r1 r2 r3 : R, (r1 * r3 - r2 * r3 = (r1 - r2) * r3)). { intros. lra. }
    rewrite (Hsimpl (y (t0 + INR n * dt)) (euler (y t0) lambda dt n) ((1 - dt * lambda))). 
    apply (Rle_trans (Rabs ((y (t0 + INR n * dt) - euler (y t0) lambda dt n) * (1 - dt * lambda)))
    (Rabs (y (t0 + INR n * dt) - euler (y t0) lambda dt n))
    (INR n * (lambda * dt * (lambda * dt * 1) * Rabs (y t0) / (1 + 1)))).
    * rewrite (Rmult_comm (y (t0 + INR n * dt) - euler (y t0) lambda dt n) (1 - dt * lambda)). 
        rewrite <- (Rmult_1_l (Rabs (y (t0 + INR n * dt) - euler (y t0) lambda dt n))).
        rewrite (Rabs_scalar (1 - dt * lambda) (y (t0 + INR n * dt) - euler (y t0) lambda dt n)). 
        -- apply (Rmult_le_compat_r (Rabs (y (t0 + INR n * dt) - euler (y t0) lambda dt n)) (1 - dt * lambda) 1). 
            apply Rabs_pos. lra. 
        -- lra.
    * apply IHn. 
Qed.

Close Scope R_scope. 