/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Rademacher
public import PDE.Analysis.Calculus.AveragedFDeriv
public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.InitialValue

/-!
# The transport equation for differences of weak Hamilton–Jacobi solutions

At common differentiability points, subtracting the Hamilton–Jacobi equations
gives a linear transport equation. Its drift is the segment average of
the Hamiltonian derivative, expressed as a continuous linear functional.
The fundamental theorem of calculus for `averagedFDeriv` supplies the exact
identity, including equal spatial gradients.

These are steps 1 and 2 of the proof of Theorem 7 in Evans, §3.3.3(b): the transport
equation (39) and its composition (40) with a cutoff. They apply to arbitrary forward
Lipschitz AE solutions. Semiconcavity enters only later, in the divergence estimate and the
energy argument.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.3.3(b), proof of Theorem 7, steps 1, 2 and 7.
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Gradient

@[expose] public section

noncomputable section

namespace HamiltonJacobi.Weak

open MeasureTheory Filter
open scoped Topology RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

/-- The averaged derivative is Evans's vector drift paired with a
direction. The affine segment parametrizations give the same integral. -/
theorem averagedFDeriv_eq_inner_integral_gradient {H : E → ℝ} (hH : ContDiff ℝ 1 H) (p q v : E) :
    PDE.Analysis.averagedFDeriv H q p v = ⟪∫ r in (0 : ℝ)..1, ∇ H (r • p + (1 - r) • q), v⟫ := by
  have hpath : Continuous (fun r : ℝ ↦ r • p + (1 - r) • q) :=
    (continuous_id.smul continuous_const).add
      ((continuous_const.sub continuous_id).smul continuous_const)
  have hgrad : Continuous (fun r : ℝ ↦ ∇ H (r • p + (1 - r) • q)) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp
      ((hH.continuous_fderiv one_ne_zero).comp hpath)
  have hsegment (r : ℝ) : q + r • (p - q) = r • p + (1 - r) • q := by
    simp only [smul_sub, sub_smul, one_smul]
    abel
  unfold PDE.Analysis.averagedFDeriv
  simp_rw [hsegment]
  have hdf : IntervalIntegrable (fun r : ℝ ↦ fderiv ℝ H (r • p + (1 - r) • q)) volume 0 1 :=
    ((hH.continuous_fderiv one_ne_zero).comp hpath).intervalIntegrable 0 1
  rw [ContinuousLinearMap.intervalIntegral_apply hdf v]
  calc
    (∫ r in (0 : ℝ)..1, fderiv ℝ H (r • p + (1 - r) • q) v) =
        ∫ r in (0 : ℝ)..1, ⟪∇ H (r • p + (1 - r) • q), v⟫ :=
      intervalIntegral.integral_congr fun r _ ↦ InnerProductSpace.toDual_symm_apply.symm
    _ = ⟪∫ r in (0 : ℝ)..1, ∇ H (r • p + (1 - r) • q), v⟫ := by
      simpa only [innerSL_apply_apply, real_inner_comm] using
        (innerSL ℝ v).intervalIntegral_comp_comm (hgrad.intervalIntegrable 0 1)

/-- At common differentiability points, the spatial gradient of a difference
is the difference of the gradients of the spatial slices. -/
theorem gradient_spaceSlice_sub {u v : E × ℝ → ℝ} {z : E × ℝ}
    (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) :
    ∇ (fun x ↦ u (x, z.2) - v (x, z.2)) z.1 =
      ∇ (fun x ↦ u (x, z.2)) z.1 - ∇ (fun x ↦ v (x, z.2)) z.1 := by
  have hw : DifferentiableAt ℝ (fun w ↦ u w - v w) z := hu.sub hv
  rw [gradient_spaceSlice_eq hw, gradient_spaceSlice_eq hu,
    gradient_spaceSlice_eq hv, fderiv_fun_sub hu hv]
  simp only [ContinuousLinearMap.sub_comp, map_sub]

/-- Subtracting the two Hamilton–Jacobi equations gives the transport equation
with the averaged derivative of the Hamiltonian as drift. -/
theorem transport_sub_eq_zero {H : E → ℝ} (hH : ContDiff ℝ 1 H) {u v : E × ℝ → ℝ} {z : E × ℝ}
    (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z)
    (hu_eq : fderiv ℝ u z (0, 1) + H (∇ (fun x ↦ u (x, z.2)) z.1) = 0)
    (hv_eq : fderiv ℝ v z (0, 1) + H (∇ (fun x ↦ v (x, z.2)) z.1) = 0) :
    fderiv ℝ (fun w ↦ u w - v w) z (0, 1) + PDE.Analysis.averagedFDeriv H
      (∇ (fun x ↦ v (x, z.2)) z.1) (∇ (fun x ↦ u (x, z.2)) z.1)
      (∇ (fun x ↦ u (x, z.2) - v (x, z.2)) z.1) = 0 := by
  rw [fderiv_fun_sub hu hv, sub_apply,
    gradient_spaceSlice_sub hu hv, PDE.Analysis.averagedFDeriv_apply_sub hH]
  linarith

/-- A differentiable scalar composition satisfies the same transport equation.
This is the chain rule behind Evans's equation (40) for a cutoff of the difference. -/
theorem transport_comp_eq_zero {w : E × ℝ → ℝ} {z : E × ℝ} (hw : DifferentiableAt ℝ w z)
    {b : E →L[ℝ] ℝ} (heq : fderiv ℝ w z (0, 1) + b (∇ (fun x ↦ w (x, z.2)) z.1) = 0) {φ : ℝ → ℝ}
    (hφ : DifferentiableAt ℝ φ (w z)) :
    fderiv ℝ (fun y ↦ φ (w y)) z (0, 1) + b (∇ (fun x ↦ φ (w (x, z.2))) z.1) = 0 := by
  have hcomp : HasFDerivAt (fun y ↦ φ (w y)) (deriv φ (w z) • fderiv ℝ w z) z :=
    hφ.hasDerivAt.comp_hasFDerivAt z hw.hasFDerivAt
  have hg : ∇ (fun x ↦ φ (w (x, z.2))) z.1 =
      deriv φ (w z) • ∇ (fun x ↦ w (x, z.2)) z.1 := by
    rw [gradient_spaceSlice_eq hcomp.differentiableAt, gradient_spaceSlice_eq hw, hcomp.fderiv]
    simp only [ContinuousLinearMap.smul_comp, map_smul]
  rw [hcomp.fderiv, smul_apply, hg, map_smul, smul_eq_mul, smul_eq_mul, ← mul_add, heq, mul_zero]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Agreement at the initial time and forward Lipschitz bounds control the
difference on every later time slice. This gives the slice `{t = ε}` on which Evans's cutoff
vanishes (step 7). -/
theorem abs_sub_le_of_initial_eq {u v : E × ℝ → ℝ} {Ku Kv : NNReal}
    (hu : LipschitzOnWith Ku u {w | 0 ≤ w.2}) (hv : LipschitzOnWith Kv v {w | 0 ≤ w.2})
    (hinit : ∀ x, u (x, 0) = v (x, 0)) (x : E) {t : ℝ} (ht : 0 ≤ t) :
    |u (x, t) - v (x, t)| ≤ ((Ku : ℝ) + (Kv : ℝ)) * t := by
  have hu' : dist (u (x, t)) (u (x, 0)) ≤ (Ku : ℝ) * t := by
    simpa [Prod.dist_eq, Real.dist_eq, abs_of_nonneg ht, max_eq_right ht] using
      hu.dist_le_mul (x, t) (show 0 ≤ t from ht) (x, 0) (show (0 : ℝ) ≤ 0 from le_rfl)
  have hv' : dist (v (x, 0)) (v (x, t)) ≤ (Kv : ℝ) * t := by
    simpa [Prod.dist_eq, Real.dist_eq, abs_of_nonneg ht, max_eq_right ht] using
      hv.dist_le_mul (x, 0) (show (0 : ℝ) ≤ 0 from le_rfl) (x, t) (show 0 ≤ t from ht)
  calc
    |u (x, t) - v (x, t)| = dist (u (x, t)) (v (x, t)) := (Real.dist_eq _ _).symm
    _ ≤ dist (u (x, t)) (u (x, 0)) + dist (u (x, 0)) (v (x, t)) := dist_triangle _ _ _
    _ = dist (u (x, t)) (u (x, 0)) + dist (v (x, 0)) (v (x, t)) := by rw [hinit]
    _ ≤ (Ku : ℝ) * t + (Kv : ℝ) * t := add_le_add hu' hv'
    _ = ((Ku : ℝ) + (Kv : ℝ)) * t := (add_mul _ _ _).symm

variable [MeasurableSpace E] [BorelSpace E]
    {μ : Measure (E × ℝ)} [μ.IsAddHaarMeasure]

/-- Rademacher's theorem on the closed forward half-space gives ordinary
differentiability almost everywhere at positive times. -/
theorem ae_differentiableAt_of_lipschitzOn_forward
    {u : E × ℝ → ℝ} {K : NNReal} (hu : LipschitzOnWith K u {w | 0 ≤ w.2}) :
    ∀ᵐ z ∂μ.restrict positiveTimeDomain, DifferentiableAt ℝ u z := by
  apply (ae_restrict_iff' isOpen_positiveTimeDomain.measurableSet).2
  filter_upwards [hu.ae_differentiableWithinAt_of_mem (μ := μ)] with z hz ht
  apply (hz (show 0 ≤ z.2 from (show 0 < z.2 from ht).le)).differentiableAt
  exact mem_of_superset (isOpen_positiveTimeDomain.mem_nhds ht)
    fun w hw ↦ show 0 ≤ w.2 from (show 0 < w.2 from hw).le

/-- The difference of any two forward Lipschitz AE solutions satisfies the
transport equation almost everywhere on the positive-time domain. -/
theorem ae_transport_sub_eq_zero {H : E → ℝ} (hH : ContDiff ℝ 1 H) {u v : E × ℝ → ℝ}
    {Ku Kv : NNReal} (hu : LipschitzOnWith Ku u {w | 0 ≤ w.2})
    (hv : LipschitzOnWith Kv v {w | 0 ≤ w.2})
    (hu_eq : ∀ᵐ z ∂μ.restrict positiveTimeDomain,
      fderiv ℝ u z (0, 1) + H (∇ (fun x ↦ u (x, z.2)) z.1) = 0)
    (hv_eq : ∀ᵐ z ∂μ.restrict positiveTimeDomain,
      fderiv ℝ v z (0, 1) + H (∇ (fun x ↦ v (x, z.2)) z.1) = 0) :
    ∀ᵐ z ∂μ.restrict positiveTimeDomain, fderiv ℝ (fun w ↦ u w - v w) z (0, 1) +
      PDE.Analysis.averagedFDeriv H (∇ (fun x ↦ v (x, z.2)) z.1) (∇ (fun x ↦ u (x, z.2)) z.1)
      (∇ (fun x ↦ u (x, z.2) - v (x, z.2)) z.1) = 0 := by
  filter_upwards [ae_differentiableAt_of_lipschitzOn_forward hu (μ := μ),
    ae_differentiableAt_of_lipschitzOn_forward hv (μ := μ), hu_eq, hv_eq] with z hdu hdv hzu hzv
  exact transport_sub_eq_zero hH hdu hdv hzu hzv

/-- Every differentiable scalar cutoff of the difference of two AE solutions
satisfies the same transport equation almost everywhere. -/
theorem ae_transport_comp_sub_eq_zero {H : E → ℝ} (hH : ContDiff ℝ 1 H) {u v : E × ℝ → ℝ}
    {Ku Kv : NNReal} (hu : LipschitzOnWith Ku u {w | 0 ≤ w.2})
    (hv : LipschitzOnWith Kv v {w | 0 ≤ w.2})
    (hu_eq : ∀ᵐ z ∂μ.restrict positiveTimeDomain,
      fderiv ℝ u z (0, 1) + H (∇ (fun x ↦ u (x, z.2)) z.1) = 0)
    (hv_eq : ∀ᵐ z ∂μ.restrict positiveTimeDomain,
      fderiv ℝ v z (0, 1) + H (∇ (fun x ↦ v (x, z.2)) z.1) = 0)
    {φ : ℝ → ℝ} (hφ : Differentiable ℝ φ) :
    ∀ᵐ z ∂μ.restrict positiveTimeDomain, fderiv ℝ (fun w ↦ φ (u w - v w)) z (0, 1) +
      PDE.Analysis.averagedFDeriv H (∇ (fun x ↦ v (x, z.2)) z.1) (∇ (fun x ↦ u (x, z.2)) z.1)
      (∇ (fun x ↦ φ (u (x, z.2) - v (x, z.2))) z.1) = 0 := by
  filter_upwards [ae_differentiableAt_of_lipschitzOn_forward hu (μ := μ),
    ae_differentiableAt_of_lipschitzOn_forward hv (μ := μ),
    ae_transport_sub_eq_zero hH hu hv hu_eq hv_eq] with z hdu hdv heq
  exact transport_comp_eq_zero (hdu.sub hdv) heq (hφ _)

end HamiltonJacobi.Weak
