From Coq Require Import ZArith Reals Psatz Arith.Arith Ring.
Require Import Coq.Logic.FunctionalExtensionality. 
From Coquelicot Require Import Coquelicot. 
From Project Require Import Base ODE NumericalMethod.

Open Scope R_scope. 

Theorem local_error_bounded : 
    forall y : R -> R, 
    forall lambda t0 tn dt : R,
    0 < lambda ->
    0 < dt -> 
    t0 <= tn -> 
    0 < (lambda * dt) < 1 -> 
    exp_ode lambda y -> 
    (Rabs ((y (tn + dt)) - (euler_step dt lambda (y tn)))) <= ((lambda * dt)^2 * (Rabs (y t0))) / INR 2.
Proof.
    (* Step 1: Simplify *)
    intros y lambda t0 tn dt Hl Hdt Ht Hlt Hy. 
    pose proof Hy as Hy'.
    unfold exp_ode in Hy'. destruct Hy' as [Hydiff Hyeqn].
    unfold euler_step. unfold is_differentiable in Hydiff. 
    (* Step 2: Taylor Expansion *)
    assert (HTaylor : exists zeta : R, tn < zeta < (tn + dt) /\ 
    y (tn + dt) = sum_f_R0 (fun m => (tn + dt - tn) ^ m / INR (fact m) * Derive_n y m tn) 1
        + (tn + dt - tn) ^ (S 1) / INR (fact (S 1)) * Derive_n y (S 1) zeta).
    {
        apply Taylor_Lagrange with (f := y) (n := 1%nat) (x := tn) (y := tn + dt).  
        - exact (Rplus_lt_r tn dt Hdt). 
        - intros t Ht' k Hk. apply Hydiff.
    }
    destruct HTaylor as [zeta [Hz HTaylor]]. 
    rewrite Rplus_minus_l in HTaylor. rewrite HTaylor. clear HTaylor.
    (* Step 3: Substitution/Simplification *) 
    unfold sum_f_R0. 
    rewrite (double_deriv lambda zeta y Hyeqn). simpl. 
    rewrite (Rdiv_diag 1). 2 : { auto. }
    rewrite Rmult_1_r. rewrite Rdiv_1_r. rewrite Rmult_1_l. 
    simpl in Hyeqn. rewrite Hyeqn.
    assert (Hsimpl : dt * - (lambda * y tn) = - dt * lambda * y tn). { lra. }
    rewrite Hsimpl. clear Hsimpl.  
    assert (Hsimpl : y tn + - dt * lambda * y tn = y tn * (1 - dt * lambda)). { lra. } 
    rewrite Hsimpl. clear Hsimpl. 
    rewrite Rplus_minus_l. 
    assert (Hsimpl : lambda * dt * (lambda * dt * 1) * Rabs (y t0) / (1 + 1) = 
    dt * dt * lambda * lambda / (1 + 1) * Rabs (y t0)). { lra. }
    rewrite Hsimpl. clear Hsimpl. 
    assert (Hsimpl : dt * dt / (1 + 1) * (lambda * lambda * y zeta) = 
    dt * dt * lambda * lambda / (1 + 1) * y zeta). { lra. }
    rewrite Hsimpl. clear Hsimpl.
    assert (Haux : 0 < (dt * dt * lambda * lambda / (1 + 1))).
    {
        apply (Rdiv_lt_0_compat). 
        - rewrite <- (Rmult_0_l lambda). apply (Rmult_lt_compat_r lambda 0 (dt * dt * lambda) Hl).
          rewrite <- (Rmult_0_l lambda). apply (Rmult_lt_compat_r lambda 0 (dt * dt) Hl).   
          rewrite <- (Rmult_0_l dt). apply (Rmult_lt_compat_r dt 0 dt Hdt). apply Hdt. 
        - lra. 
    }
    rewrite (Rabs_scalar (dt * dt * lambda * lambda / (1 + 1)) (y zeta) Haux).
    assert (Haux2 : 0 <= (dt * dt * lambda * lambda / (1 + 1))). { left. apply Haux. }
    apply (Rmult_le_compat_l (dt * dt * lambda * lambda / (1 + 1)) (Rabs (y zeta)) (Rabs (y t0)) Haux2).  
    clear Haux Haux2.  
    (* Step 4: Inequality *)
    apply (exp_eqv lambda t0 y) in Hy. 
    rewrite Hy. unfold exp_ode_exact. 
    rewrite (Rabs_mult (y t0) (exp (- (lambda * zeta)))).
    rewrite (Rabs_mult (y t0) (exp (- (lambda * t0)))). 
    apply (Rmult_le_compat_l (Rabs (y t0)) _ _ (Rabs_pos (y t0))).
    assert (Hsimpl : forall t : R, Rabs (exp t) = exp t). 
    { intros t. apply (Rabs_right (exp t)). unfold ">=". left. apply exp_pos. }
    rewrite (Hsimpl (- (lambda * zeta))). rewrite (Hsimpl (- (lambda * t0))). clear Hsimpl. 
    unfold "<=". left. apply exp_increasing. apply (Ropp_lt_contravar).
    apply (Rmult_lt_compat_l lambda t0 zeta Hl).
    lra.  
Qed.

Close Scope R_scope. 