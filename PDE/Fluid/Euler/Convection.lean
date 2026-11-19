/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.TrilinearForm
public import PDE.Spaces.Sobolev.Calculus.Product.IntegrationByParts

/-!
# Euler convection on whole-space Sobolev fields

The transport pairing uses the weak first derivatives of H¹ fields and bounded
W^{1,∞} velocity coefficients. Polarized integration by parts proves its skew symmetry
when the advecting velocity is divergence free. Compatible H¹ and W^{1,∞} realizations
then give the coupled Euler difference estimate in the L² energy, without a derivative norm
of the difference.

## Main results

* `sobolevTransport`, `sobolevConvectionPairing`: the weak transport term `a · ∇u` and its `L²`
  pairing.
* `sobolevConvectionPairing_skew`, `sobolevConvectionPairing_self_eq_zero`: skew symmetry and
  energy cancellation for a divergence-free advecting velocity.
* `abs_sobolevConvectionPairing_difference_le`, `sobolevTransport_difference_energy_le`: the
  difference estimate, with only the reference velocity gradient on the right.
* `realizedSobolevConvectionForm`, `abs_realizedSobolevConvectionForm_difference_le`: the same
  for a continuous trilinear form on a state space.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set SobolevSpace.GraphSpace
open scoped ENNReal InnerProductSpace Sobolev

namespace Euler

variable {n : ℕ}

/-- The weak transport term `a · ∇u`, component by component in L². -/
def sobolevTransport (A : Fin n → W^{1,∞}((Set.univ : Set (ℝ^n))))
    (U : Fin n → H¹((Set.univ : Set (ℝ^n))))
    (i : Fin n) : DerivLp n 2 univ :=
  ∑ j, wkpCoordinateCLM (baseIndex n 1) (A j) •
    wkpCoordinateCLM (singleDerivIndex n j) (U i)

/-- The L² pairing of the weak transport term with a test velocity. -/
def sobolevConvectionPairing (A : Fin n → W^{1,∞}((Set.univ : Set (ℝ^n))))
    (U V : Fin n → H¹((Set.univ : Set (ℝ^n)))) : ℝ :=
  ∑ i, ⟪sobolevTransport A U i, wkpCoordinateCLM (baseIndex n 1) (V i)⟫_ℝ

/-- Polarized transport integration by parts involves the weak divergence of the
advecting velocity. No compact support assumption is needed for the H¹ test fields. -/
theorem sobolevConvectionPairing_add_swap
    (A : Fin n → W^{1,∞}((Set.univ : Set (ℝ^n)))) (U V : Fin n → H¹((Set.univ : Set (ℝ^n)))) :
    sobolevConvectionPairing A U V + sobolevConvectionPairing A V U =
      -(∑ i, ⟪(∑ j, wkpCoordinateCLM (singleDerivIndex n j) (A j)) •
        wkpCoordinateCLM (baseIndex n 1) (U i),
          wkpCoordinateCLM (baseIndex n 1) (V i)⟫_ℝ) := by
  classical
  have hmul (u : DerivLp n 2 univ) (s : Finset (Fin n)) :
      (∑ j ∈ s, wkpCoordinateCLM (singleDerivIndex n j) (A j)) • u =
        ∑ j ∈ s, (wkpCoordinateCLM (singleDerivIndex n j) (A j)) • u := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj hs => simp only [Finset.sum_insert hj, Lp.smul_add, hs]
  simp only [sobolevConvectionPairing, sobolevTransport, sum_inner]
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ i, ∑ j, -⟪wkpCoordinateCLM (singleDerivIndex n j) (A j) •
        wkpCoordinateCLM (baseIndex n 1) (U i),
          wkpCoordinateCLM (baseIndex n 1) (V i)⟫_ℝ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      exact inner_mul_deriv_add_inner_mul_deriv_univ (A j) j (U i) (V i)
    _ = _ := by simp only [hmul, sum_inner, Finset.sum_neg_distrib]

/-- Divergence-free transport is skew in the two H¹ slots. -/
theorem sobolevConvectionPairing_skew
    (A : Fin n → W^{1,∞}((Set.univ : Set (ℝ^n))))
    (hdiv : (∑ j, wkpCoordinateCLM (singleDerivIndex n j) (A j)) = 0)
    (U V : Fin n → H¹((Set.univ : Set (ℝ^n)))) :
    sobolevConvectionPairing A U V = -sobolevConvectionPairing A V U := by
  have h := sobolevConvectionPairing_add_swap A U V
  rw [hdiv] at h
  simp only [Lp.zero_smul, inner_zero_left, Finset.sum_const_zero, neg_zero] at h
  linarith only [h]

/-- The transport nonlinearity contributes zero to the L² energy when its advecting
velocity is divergence free. -/
theorem sobolevConvectionPairing_self_eq_zero
    (A : Fin n → W^{1,∞}((Set.univ : Set (ℝ^n))))
    (hdiv : (∑ j, wkpCoordinateCLM (singleDerivIndex n j) (A j)) = 0)
    (U : Fin n → H¹((Set.univ : Set (ℝ^n)))) : sobolevConvectionPairing A U U = 0 := by
  have h := sobolevConvectionPairing_skew A hdiv U U
  linarith only [h]

/-- The bounded and square-integrable Sobolev coordinates describe the same velocity and
its weak first derivatives. This compares representatives, without changing either norm. -/
def SobolevVelocityCompatible (A : Fin n → W^{1,∞}((Set.univ : Set (ℝ^n))))
    (U : Fin n → H¹((Set.univ : Set (ℝ^n)))) : Prop :=
  ∀ i a, (wkpCoordinateCLM a (A i) : ℝ^n → ℝ) =ᵐ[volume.restrict univ]
    (wkpCoordinateCLM a (U i) : ℝ^n → ℝ)

/-- Compatibility of Sobolev realizations is preserved under velocity differences. -/
theorem SobolevVelocityCompatible.sub
    {A B : Fin n → W^{1,∞}((Set.univ : Set (ℝ^n)))} {U V : Fin n → H¹((Set.univ : Set (ℝ^n)))}
    (hU : SobolevVelocityCompatible A U) (hV : SobolevVelocityCompatible B V) :
    SobolevVelocityCompatible (A - B) (U - V) := by
  intro i a
  simp only [Pi.sub_apply, map_sub]
  filter_upwards [Lp.coeFn_sub (wkpCoordinateCLM a (A i)) (wkpCoordinateCLM a (B i)),
    Lp.coeFn_sub (wkpCoordinateCLM a (U i)) (wkpCoordinateCLM a (V i)),
    hU i a, hV i a] with x hA hB hU hV
  simp only [Pi.sub_apply] at hA hB
  rw [hA, hB, hU, hV]

/-- The two compatible realizations allow the transport product to be written with the
bounded derivative and the square-integrable advecting velocity. -/
theorem SobolevVelocityCompatible.mul_deriv_eq
    {A B : Fin n → W^{1,∞}((Set.univ : Set (ℝ^n)))} {U V : Fin n → H¹((Set.univ : Set (ℝ^n)))}
    (hU : SobolevVelocityCompatible A U) (hV : SobolevVelocityCompatible B V)
    (i j : Fin n) :
    wkpCoordinateCLM (baseIndex n 1) (A j) •
        wkpCoordinateCLM (singleDerivIndex n j) (V i) =
      (wkpCoordinateCLM (singleDerivIndex n j) (B i) •
        wkpCoordinateCLM (baseIndex n 1) (U j) : DerivLp n 2 univ) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞))
      (wkpCoordinateCLM (baseIndex n 1) (A j))
      (wkpCoordinateCLM (singleDerivIndex n j) (V i)),
    Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞))
      (wkpCoordinateCLM (singleDerivIndex n j) (B i))
      (wkpCoordinateCLM (baseIndex n 1) (U j)),
    hU j (baseIndex n 1), hV i (singleDerivIndex n j)] with x hleft hright hbase hderiv
  simp only [smul_eq_mul, Pi.mul_apply] at hleft hright
  rw [hleft, hright, hbase, hderiv, mul_comm]

/-- Transport is linear in its advecting velocity. -/
theorem sobolevTransport_sub_left (A B : Fin n → W^{1,∞}((Set.univ : Set (ℝ^n))))
    (U : Fin n → H¹((Set.univ : Set (ℝ^n)))) (i : Fin n) :
    sobolevTransport (A - B) U i = sobolevTransport A U i - sobolevTransport B U i := by
  simp only [sobolevTransport, Pi.sub_apply, map_sub]
  simp only [sub_eq_add_neg, Lp.smul_add, Lp.neg_smul, Finset.sum_add_distrib,
    Finset.sum_neg_distrib]

/-- Transport is linear in its transported velocity. -/
theorem sobolevTransport_sub_right (A : Fin n → W^{1,∞}((Set.univ : Set (ℝ^n))))
    (U V : Fin n → H¹((Set.univ : Set (ℝ^n)))) (i : Fin n) :
    sobolevTransport A (U - V) i = sobolevTransport A U i - sobolevTransport A V i := by
  simp only [sobolevTransport, Pi.sub_apply, map_sub]
  simp only [sub_eq_add_neg, Lp.add_smul, Lp.smul_neg, Finset.sum_add_distrib,
    Finset.sum_neg_distrib]

/-- Coupled Euler convection tested against a velocity difference reduces exactly to the
term in which only the reference velocity is differentiated. -/
theorem sobolevConvectionPairing_difference_identity
    (A B : Fin n → W^{1,∞}((Set.univ : Set (ℝ^n)))) (U V : Fin n → H¹((Set.univ : Set (ℝ^n))))
    (hdiv : (∑ j, wkpCoordinateCLM (singleDerivIndex n j) (A j)) = 0) :
    sobolevConvectionPairing A U (U - V) - sobolevConvectionPairing B V (U - V) =
      sobolevConvectionPairing (A - B) V (U - V) := by
  have hzero := sobolevConvectionPairing_self_eq_zero A hdiv (U - V)
  have hsplit :
      sobolevConvectionPairing A U (U - V) - sobolevConvectionPairing B V (U - V) =
        sobolevConvectionPairing A (U - V) (U - V) +
          sobolevConvectionPairing (A - B) V (U - V) := by
    simp only [sobolevConvectionPairing, sobolevTransport_sub_left,
      sobolevTransport_sub_right, inner_sub_left, Finset.sum_sub_distrib]
    abel
  rw [hsplit, hzero, zero_add]

/-- The nonlinear Euler difference pairing has an L² bound involving only the bounded
first derivatives of the reference velocity. In particular, no derivative norm of the
velocity difference occurs on the right-hand side. -/
theorem abs_sobolevConvectionPairing_difference_le
    (A B : Fin n → W^{1,∞}((Set.univ : Set (ℝ^n)))) (U V : Fin n → H¹((Set.univ : Set (ℝ^n))))
    (hU : SobolevVelocityCompatible A U) (hV : SobolevVelocityCompatible B V)
    (hdiv : (∑ j, wkpCoordinateCLM (singleDerivIndex n j) (A j)) = 0) :
    |sobolevConvectionPairing A U (U - V) - sobolevConvectionPairing B V (U - V)| ≤
      (∑ i, ∑ j, ‖wkpCoordinateCLM (singleDerivIndex n j) (B i)‖) *
        ∑ i, ‖wkpCoordinateCLM (baseIndex n 1) ((U - V) i)‖ ^ 2 := by
  rw [sobolevConvectionPairing_difference_identity A B U V hdiv]
  simp only [sobolevConvectionPairing, sobolevTransport, sum_inner]
  simp_rw [(hU.sub hV).mul_deriv_eq hV]
  exact Lp.abs_sum_inner_lpSMul_le
    (fun i j ↦ wkpCoordinateCLM (singleDerivIndex n j) (B i))
    (fun i ↦ wkpCoordinateCLM (baseIndex n 1) ((U - V) i))

/-- A bounded spatial realization, for example a finite-dimensional trial map or a bounded
regularization, gives a continuous trilinear form for Euler convection. -/
def realizedSobolevConvectionForm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E →L[ℝ] (Fin n → W^{1,∞}((Set.univ : Set (ℝ^n)))))
    (u : E →L[ℝ] (Fin n
      → H¹((Set.univ : Set (ℝ^n))))) : PDE.Analysis.ContinuousTrilinearForm E E E :=
  -- Materialize the canonical normed structures before summing nested CLMs.
  -- Without them, elaboration cannot infer the outer AddCommMonoid.
  letI : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
  letI : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  let mul : DerivLp n ∞ univ →L[ℝ] DerivLp n 2 univ →L[ℝ] DerivLp n 2 univ :=
    (ContinuousLinearMap.mul ℝ ℝ).holderL (volume.restrict univ) ∞ 2 2
  ∑ i, ∑ j,
    (ContinuousLinearMap.compL ℝ E (DerivLp n 2 univ) (E →L[ℝ] ℝ)
      ((innerSL ℝ).bilinearComp (ContinuousLinearMap.id ℝ (DerivLp n 2 univ))
        (((wkpCoordinateCLM (baseIndex n 1)).comp (ContinuousLinearMap.proj i)).comp u))).comp
      (mul.bilinearComp
        (((wkpCoordinateCLM (baseIndex n 1)).comp (ContinuousLinearMap.proj j)).comp a)
        (((wkpCoordinateCLM (singleDerivIndex n j)).comp
          (ContinuousLinearMap.proj i)).comp u))

/-- The bounded form evaluates to the weak-derivative transport pairing. -/
@[simp]
theorem realizedSobolevConvectionForm_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E →L[ℝ] (Fin n → W^{1,∞}((Set.univ : Set (ℝ^n)))))
    (u : E →L[ℝ] (Fin n → H¹((Set.univ : Set (ℝ^n))))) (x y z : E) :
    realizedSobolevConvectionForm a u x y z =
      sobolevConvectionPairing (a x) (u y) (u z) := by
  classical
  have hmul (a : DerivLp n ∞ univ) (u : DerivLp n 2 univ) :
      (ContinuousLinearMap.mul ℝ ℝ).holder (2 : ℝ≥0∞) a u =
        (a • u : DerivLp n 2 univ) := by
    apply Lp.ext
    filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder
        (r := (2 : ℝ≥0∞)) a u, Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) a u] with x h1 h2
    simpa only [ContinuousLinearMap.mul_apply', smul_eq_mul, Pi.mul_apply] using
      h1.trans h2.symm
  simp only [realizedSobolevConvectionForm, sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.holderL_apply_apply, innerSL_apply_apply, hmul,
    sobolevConvectionPairing, sobolevTransport, sum_inner]

/-- Divergence-free spatial realization proves skew symmetry for the Euler form. -/
theorem realizedSobolevConvectionForm_isSkewInLastTwo
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E →L[ℝ] (Fin n → W^{1,∞}((Set.univ : Set (ℝ^n)))))
    (u : E →L[ℝ] (Fin n → H¹((Set.univ : Set (ℝ^n)))))
    (hdiv : ∀ x, (∑ j, wkpCoordinateCLM (singleDerivIndex n j) (a x j)) = 0) :
    (realizedSobolevConvectionForm a u).IsSkewInLastTwo := by
  intro x y z
  simp only [realizedSobolevConvectionForm_apply]
  exact sobolevConvectionPairing_skew (a x) (hdiv x) (u y) (u z)

/-- An L² consistency residual can be added to the coupled transport difference estimate.
The coefficient of the difference energy depends only on the reference velocity gradient;
its value is independent of finite-dimensional norm equivalences or projection norms. -/
theorem sobolevTransport_difference_energy_le
    (A B : Fin n → W^{1,∞}((Set.univ : Set (ℝ^n)))) (U V : Fin n → H¹((Set.univ : Set (ℝ^n))))
    (hU : SobolevVelocityCompatible A U) (hV : SobolevVelocityCompatible B V)
    (hdiv : (∑ j, wkpCoordinateCLM (singleDerivIndex n j) (A j)) = 0)
    (R : PiLp 2 (fun _ : Fin n ↦ DerivLp n 2 univ)) :
    let w := WithLp.toLp 2 (fun i ↦ wkpCoordinateCLM (baseIndex n 1) ((U - V) i));
    let drift := fun (C : Fin n → W^{1,∞}((Set.univ : Set (ℝ^n))))
      (W : Fin n → H¹((Set.univ : Set (ℝ^n)))) ↦
      WithLp.toLp 2 (fun i ↦ -sobolevTransport C W i);
    2 * ⟪drift A U - drift B V + R, w⟫_ℝ ≤
      (2 * (∑ i, ∑ j, ‖wkpCoordinateCLM (singleDerivIndex n j) (B i)‖) + 1) *
        ‖w‖ ^ 2 + ‖R‖ ^ 2 := by
  classical
  let w := WithLp.toLp 2 (fun i ↦ wkpCoordinateCLM (baseIndex n 1) ((U - V) i))
  let drift := fun (C : Fin n → W^{1,∞}((Set.univ : Set (ℝ^n))))
    (W : Fin n → H¹((Set.univ : Set (ℝ^n)))) ↦
      WithLp.toLp 2 (fun i ↦ -sobolevTransport C W i)
  change 2 * ⟪drift A U - drift B V + R, w⟫_ℝ ≤ _
  have hpair : ⟪drift A U - drift B V, w⟫_ℝ =
      -(sobolevConvectionPairing A U (U - V) -
        sobolevConvectionPairing B V (U - V)) := by
    simp only [drift, w, PiLp.inner_apply, sobolevConvectionPairing,
      inner_sub_left, inner_neg_left, Finset.sum_neg_distrib]
    abel
  have hbound := abs_sobolevConvectionPairing_difference_le A B U V hU hV hdiv
  have hnorm : ‖w‖ ^ 2 = ∑ i, ‖wkpCoordinateCLM (baseIndex n 1) ((U - V) i)‖ ^ 2 :=
    PiLp.norm_sq_eq_of_L2 _ w
  have htransport : ⟪drift A U - drift B V, w⟫_ℝ ≤
      (∑ i, ∑ j, ‖wkpCoordinateCLM (singleDerivIndex n j) (B i)‖) * ‖w‖ ^ 2 := by
    rw [hpair, hnorm]
    exact (neg_le_abs _).trans hbound
  have hresidual : 2 * ⟪R, w⟫_ℝ ≤ ‖R‖ ^ 2 + ‖w‖ ^ 2 := by
    have hinner := real_inner_le_norm R w
    nlinarith [sq_nonneg (‖R‖ - ‖w‖)]
  rw [inner_add_left]
  linarith only [htransport, hresidual]

/-- The coupled convection form on a state space `E` is controlled in the
weaker, reconstructed L² velocity energy. Only the reference velocity gradient enters. -/
theorem abs_realizedSobolevConvectionForm_difference_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E →L[ℝ] (Fin n → W^{1,∞}((Set.univ : Set (ℝ^n)))))
    (u : E →L[ℝ] (Fin n → H¹((Set.univ : Set (ℝ^n)))))
    (hcompatible : ∀ x, SobolevVelocityCompatible (a x) (u x))
    (hdiv : ∀ x, (∑ j, wkpCoordinateCLM (singleDerivIndex n j) (a x j)) = 0)
    (x y : E) :
    |realizedSobolevConvectionForm a u x x (x - y) -
        realizedSobolevConvectionForm a u y y (x - y)| ≤
      (∑ i, ∑ j, ‖wkpCoordinateCLM (singleDerivIndex n j) (a y i)‖) *
        ∑ i, ‖wkpCoordinateCLM (baseIndex n 1) (u (x - y) i)‖ ^ 2 := by
  simp only [realizedSobolevConvectionForm_apply, u.map_sub]
  exact abs_sobolevConvectionPairing_difference_le (a x) (a y) (u x) (u y)
      (hcompatible x) (hcompatible y) (hdiv x)

end Euler
