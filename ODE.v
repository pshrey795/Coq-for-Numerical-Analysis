From Coq Require Import ZArith Reals Psatz Arith.Arith Ring. 
Require Import Coq.Logic.FunctionalExtensionality. 
From Coquelicot Require Import Coquelicot. 
From Project Require Import Base NumericalMethod.

Require Import Coquelicot.AutoDerive. 

Open Scope R_scope. 

(* Differential Equation for Exponential Decay *)
Definition is_differentiable (f: R -> R): Prop :=
  forall (x: R) (n: nat),  
  ex_derive_n f n x.

Definition exp_ode_exact (lambda y0 : R) := fun (t : R) => (y0 * (exp (- (lambda * t)))).

Definition exp_ode (lambda : R) (y : R -> R) := 
    (is_differentiable y) /\ 
    (forall t : R, Derive_n y 1 t = - (lambda * (y t))). 

(* Lemmas for given ODE *)
Lemma double_deriv : forall lambda zeta : R, forall y : R -> R,
    (forall t : R, Derive_n y 1 t = - (lambda * y t)) -> 
    Derive_n y 2 zeta = lambda * lambda * y zeta. 
Proof.
    intros lambda zeta y H.
    Open Scope nat_scope. 
    assert (Hsimpl : 2%nat = 1%nat + 1%nat). { auto. } 
    rewrite Hsimpl. clear Hsimpl. 
    rewrite <- (Derive_n_comp y 1 1 zeta). 
    Close Scope nat_scope. 
    assert (Hsimpl : forall t : R,  - (lambda * y t) = (- lambda) * y t). { intros t. lra. }
    assert (Hsimpl2 : Derive_n y 1 = fun t => -lambda * y t). 
    { 
        apply functional_extensionality. 
        intros x. rewrite H. rewrite Hsimpl. reflexivity. 
    }
    rewrite Hsimpl2. clear Hsimpl Hsimpl2. 
    rewrite (Derive_n_scal_l y 1 (-lambda) zeta).
    rewrite H. lra. 
Qed.

(* Theorem to prove that the exact solution is the only solution of the given ODE *)
Theorem exp_eqv : forall lambda t0 : R, forall y : R -> R,
  exp_ode lambda y -> y = exp_ode_exact lambda (y t0). 
Proof.
  intros lambda t0 y Hy. unfold exp_ode in Hy. 
  destruct Hy as [Hydiff Hyeqn]. unfold is_differentiable. 
  apply functional_extensionality. intros x. 
  unfold exp_ode_exact. 
Admitted. 

Close Scope R_scope. 