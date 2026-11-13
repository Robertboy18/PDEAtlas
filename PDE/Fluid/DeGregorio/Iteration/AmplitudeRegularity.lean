/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Characteristics.Data
public import PDE.Fluid.DeGregorio.Iteration.FlowJacobian
public import PDE.Fluid.DeGregorio.Iteration.HilbertCoefficientDerivative
public import PDE.Analysis.Calculus.PartialRegularity
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Regularity of the characteristic amplitude

The bounded H² input gives a jointly continuous spatial derivative of the
Hilbert coefficient. Differentiation under the interval integral therefore
gives the spatial derivative of the characteristic amplitude. The time
derivative follows from the fundamental theorem of calculus.

The input curve is continuous in time for the L² topology, and the amplitude is
defined on the same interval as the position flow.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set PDE.Analysis
open scoped Topology

open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

/-- A uniformly bounded stretching coefficient bounds its exponential integral
along any curve `X`. -/
theorem norm_exp_integral_flow_le
    {c X : ℝ → ℝ → ℝ} {B : NNReal} {T : ℝ}
    (hcbound : ∀ x t, ‖c x t‖ ≤ 2 * (B : ℝ))
    (x t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    ‖Real.exp (∫ s in 0..t, c (X x s) s)‖ ≤ Real.exp (2 * (B : ℝ) * T) := by
  have hi : |∫ s in 0..t, c (X x s) s| ≤ 2 * (B : ℝ) * t := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := t) (f := fun s ↦ c (X x s) s)
      (fun s _ ↦ hcbound (X x s) s)
    simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht.1] using h
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  exact ((le_abs_self _).trans hi).trans (mul_le_mul_of_nonneg_left ht.2
    (mul_nonneg (by norm_num) B.coe_nonneg))

private theorem contDiff_one_primitive_of_continuous_partial
    {k d : ℝ → ℝ → ℝ} {M : ℝ}
    (hk : Continuous (Function.uncurry k)) (hd : Continuous (Function.uncurry d))
    (hderiv : ∀ x t, HasDerivAt (fun y ↦ k y t) (d x t) x)
    (hbound : ∀ x t, ‖d x t‖ ≤ M) :
    ContDiff ℝ 1 (fun p : ℝ × ℝ ↦ ∫ s in 0..p.2, k p.1 s) := by
  have hfirst (x t : ℝ) :
      HasDerivAt (fun y ↦ ∫ s in 0..t, k y s) (∫ s in 0..t, d x s) x := by
    apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := k) (F' := d) (bound := fun _ ↦ M) (s := univ) (Filter.univ_mem)
      (.of_forall fun y ↦
        (hk.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
      ((hk.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)
      ((hd.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
      (.of_forall fun s _ y _ ↦ hbound y s) intervalIntegrable_const
      (.of_forall fun s _ y _ ↦ hderiv y s)).2
  have hsecond (x t : ℝ) :
      HasDerivAt (fun s ↦ ∫ r in 0..s, k x r) (k x t) t :=
    ((hk.comp (continuous_const.prodMk continuous_id)).integral_hasStrictDerivAt 0 t).hasDerivAt
  rw [← contDiffOn_univ]
  apply contDiffOn_one_of_partial_derivatives isOpen_univ
    ((ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.comp
      (intervalIntegral.continuous_parametric_primitive_of_continuous
        (μ := volume) (a₀ := (0 : ℝ)) hd)).continuousOn
    ((ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.comp hk).continuousOn
  · intro p _
    exact (hfirst p.1 p.2).hasFDerivAt
  · intro p _
    exact (hsecond p.1 p.2).hasFDerivAt

private theorem contDiff_one_hkCurve_clamped_primitive
    {A : Set (ℝ^1)} {B : NNReal} {T : ℝ} (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, supportedHkBaseBall 1 2 univ A B))
    {c X : ℝ → ℝ → ℝ} (hchar : HkForwardCharacteristics hT f c X) :
    ContDiff ℝ 1
      (fun p : ℝ × ℝ ↦ ∫ s in 0..p.2, c (X p.1 (projIcc 0 T hT s)) s) := by
  obtain ⟨d, hd, hcd, hdbound, _hdmod⟩ :=
    exists_hkCurve_hilbert_coefficient_hasDerivAt hT f hchar.coefficient_continuous
      hchar.hilbert_pair
  let Z : ℝ → ℝ → ℝ := fun x t ↦ X x (projIcc 0 T hT t)
  have hZ : Continuous (Function.uncurry Z) :=
    hchar.flow_continuous.comp (continuous_fst.prodMk ((continuous_projIcc (h := hT)).comp
      continuous_snd))
  have hZX (x t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : Z x t = X x t := by
    simp only [Z, projIcc_of_mem hT ht]
  let k : ℝ → ℝ → ℝ := fun x t ↦ c (Z x t) t
  have hk : Continuous (Function.uncurry k) := hchar.coefficient_continuous.comp (hZ.prodMk
    continuous_snd)
  let J : ℝ → ℝ → ℝ :=
    fun x t ↦ Real.exp (∫ s in 0..(projIcc 0 T hT t : ℝ), k x s)
  have hJ : Continuous (Function.uncurry J) :=
    (intervalIntegral.continuous_parametric_primitive_of_continuous hk).rexp.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp
        ((continuous_projIcc (h := hT)).comp continuous_snd)))
  have hint (x t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      (∫ s in 0..t, k x s) = ∫ s in 0..t, c (X x s) s := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    change c (Z x s) s = c (X x s) s
    rw [hZX x s ⟨hs.1, hs.2.trans ht.2⟩]
  have hZ' (x t : ℝ) : HasDerivAt (fun y ↦ Z y t) (J x t) x := by
    have h := hasDerivAt_hkCurve_hilbert_flow_space hT f hchar.velocity_derivative
      hchar.flow_initial hchar.flow_derivative
      x (projIcc 0 T hT t) (projIcc 0 T hT t).property
    change HasDerivAt (fun y ↦ X y (projIcc 0 T hT t))
      (Real.exp (∫ s in 0..(projIcc 0 T hT t : ℝ), k x s)) x
    rw [hint x _ (projIcc 0 T hT t).property]
    exact h
  have hJbound (x t : ℝ) : ‖J x t‖ ≤ Real.exp (2 * (B : ℝ) * T) := by
    change ‖Real.exp (∫ s in 0..(projIcc 0 T hT t : ℝ), k x s)‖ ≤ _
    rw [hint x _ (projIcc 0 T hT t).property]
    exact norm_exp_integral_flow_le hchar.coefficient_bound x _
      (projIcc 0 T hT t).property
  let D : ℝ → ℝ → ℝ := fun x t ↦ d (Z x t) t * J x t
  have hD : Continuous (Function.uncurry D) :=
    (hd.comp (hZ.prodMk continuous_snd)).mul hJ
  have hk' (x t : ℝ) : HasDerivAt (fun y ↦ k y t) (D x t) x := by
    change HasDerivAt (fun y ↦ c (Z y t) t) (d (Z x t) t * J x t) x
    simpa only [Function.comp_def] using (hcd (Z x t) t).comp x (hZ' x t)
  have hDbound (x t : ℝ) :
      ‖D x t‖ ≤ 2 * (B : ℝ) * Real.exp (2 * (B : ℝ) * T) := by
    change ‖d (Z x t) t * J x t‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul (hdbound (Z x t) t) (hJbound x t) (norm_nonneg _)
      (mul_nonneg (by norm_num) B.coe_nonneg)
  exact contDiff_one_primitive_of_continuous_partial hk hD hk' hDbound

/-- The exponential characteristic formula defines a jointly C¹ amplitude
on the entire open time cylinder for every bounded H² input curve and C¹
initial datum. Its differentiability is derived from the Hilbert
coefficient and flow. -/
theorem contDiffOn_one_hkCurve_amplitude
    {A : Set (ℝ^1)} {B : NNReal} {T : ℝ} (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, supportedHkBaseBall 1 2 univ A B))
    {c X : ℝ → ℝ → ℝ} (hchar : HkForwardCharacteristics hT f c X)
    {w₀ : ℝ → ℝ} (hw₀ : ContDiff ℝ 1 w₀) :
    ContDiffOn ℝ 1
      (fun p : ℝ × ℝ ↦ w₀ p.1 * Real.exp (∫ s in 0..p.2, c (X p.1 s) s))
      (univ ×ˢ Ioo (0 : ℝ) T) := by
  have hprimitive := contDiff_one_hkCurve_clamped_primitive hT f hchar
  have hV := (hw₀.comp contDiff_fst).mul hprimitive.exp
  apply hV.contDiffOn.congr
  intro p hp
  congr 2
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hp.2.1.le] at hs
  change c (X p.1 s) s = c (X p.1 (projIcc 0 T hT s)) s
  rw [projIcc_of_mem hT ⟨hs.1, hs.2.trans hp.2.2.le⟩]

/-- Each spatial Jacobian slice is C¹, including at both endpoints of the
prescribed time interval. -/
theorem contDiff_one_hkCurve_jacobian_slice
    {A : Set (ℝ^1)} {B : NNReal} {T : ℝ} (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, supportedHkBaseBall 1 2 univ A B))
    {c X : ℝ → ℝ → ℝ} (hchar : HkForwardCharacteristics hT f c X)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ContDiff ℝ 1 (fun x ↦ Real.exp (∫ s in 0..t, c (X x s) s)) := by
  have hprimitive := contDiff_one_hkCurve_clamped_primitive hT f hchar
  have hs := (hprimitive.comp (contDiff_id.prodMk (contDiff_const (c := t)))).exp
  convert hs using 1
  funext x
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht.1] at hs
  change c (X x s) s = c (X x (projIcc 0 T hT s)) s
  rw [projIcc_of_mem hT ⟨hs.1, hs.2.trans ht.2⟩]

end DeGregorio.Iteration
