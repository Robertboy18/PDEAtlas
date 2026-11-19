/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.AmplitudeRegularity
import CAS.ExactTactic
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# The spatial derivative of the flow Jacobian

Differentiation under the characteristic integral gives
`J_x = J * ∫ c_x(X,s) J ds`. The Hilbert coefficient gives the continuous
derivative and its uniform bound. The result holds throughout the prescribed
closed time interval, with only L² time continuity of the input.

The quantitative bound tends to zero with the interval length. It controls
the coefficient multiplying the highest weak derivative when proving
Sobolev regularity of the transported vorticity.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set PDE.Analysis
open scoped Topology

open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

private theorem hasDerivAt_integral_hkCurve_coefficient
    {A : Set (ℝ^1)} {B : NNReal} {T : ℝ} (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, supportedHkBaseBall 1 2 univ A B))
    {c d X : ℝ → ℝ → ℝ} (hc : Continuous (Function.uncurry c))
    (hd : Continuous (Function.uncurry d))
    (hcd : ∀ x t, HasDerivAt (fun y ↦ c y t) (d x t) x)
    (hdbound : ∀ x t, ‖d x t‖ ≤ 2 * (B : ℝ))
    (hbc : ∀ x t, HasDerivAt (fun y ↦ hkCurveHilbertVelocity hT f y t) (c x t) x)
    (hcbound : ∀ x t, ‖c x t‖ ≤ 2 * (B : ℝ))
    (hX₀ : ∀ x, X x 0 = x)
    (hX' : ∀ x t, t ∈ Icc (0 : ℝ) T →
      HasDerivAt (X x) (hkCurveHilbertVelocity hT f (X x t) t) t)
    (hX : Continuous (fun p : ℝ × Icc (0 : ℝ) T ↦ X p.1 p.2))
    (x t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivAt (fun y ↦ ∫ s in 0..t, c (X y s) s)
      (∫ s in 0..t, d (X x s) s * Real.exp (∫ r in 0..s, c (X x r) r)) x := by
  let Z : ℝ → ℝ → ℝ := fun y s ↦ X y (projIcc 0 T hT s)
  have hZ : Continuous (Function.uncurry Z) :=
    hX.comp (continuous_fst.prodMk ((continuous_projIcc (h := hT)).comp continuous_snd))
  have hZX (y s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) : Z y s = X y s := by
    simp only [Z, projIcc_of_mem hT hs]
  let k : ℝ → ℝ → ℝ := fun y s ↦ c (Z y s) s
  have hk : Continuous (Function.uncurry k) := hc.comp (hZ.prodMk continuous_snd)
  let J : ℝ → ℝ → ℝ :=
    fun y s ↦ Real.exp (∫ r in 0..(projIcc 0 T hT s : ℝ), k y r)
  have hJ : Continuous (Function.uncurry J) :=
    (intervalIntegral.continuous_parametric_primitive_of_continuous hk).rexp.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp
        ((continuous_projIcc (h := hT)).comp continuous_snd)))
  have hint (y s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
      (∫ r in 0..s, k y r) = ∫ r in 0..s, c (X y r) r := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le hs.1] at hr
    change c (Z y r) r = c (X y r) r
    rw [hZX y r ⟨hr.1, hr.2.trans hs.2⟩]
  have hJX (y s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
      J y s = Real.exp (∫ r in 0..s, c (X y r) r) := by
    dsimp only [J]
    rw [projIcc_of_mem hT hs, hint y s hs]
  have hZ' (y s : ℝ) : HasDerivAt (fun z ↦ Z z s) (J y s) y := by
    change HasDerivAt (fun z ↦ X z (projIcc 0 T hT s))
      (Real.exp (∫ r in 0..(projIcc 0 T hT s : ℝ), k y r)) y
    rw [hint y _ (projIcc 0 T hT s).property]
    exact hasDerivAt_hkCurve_hilbert_flow_space hT f hbc hX₀ hX'
      y _ (projIcc 0 T hT s).property
  have hJbound (y s : ℝ) : ‖J y s‖ ≤ Real.exp (2 * (B : ℝ) * T) := by
    change ‖Real.exp (∫ r in 0..(projIcc 0 T hT s : ℝ), k y r)‖ ≤ _
    rw [hint y _ (projIcc 0 T hT s).property]
    exact norm_exp_integral_flow_le hcbound y _ (projIcc 0 T hT s).property
  let D : ℝ → ℝ → ℝ := fun y s ↦ d (Z y s) s * J y s
  have hD : Continuous (Function.uncurry D) :=
    (hd.comp (hZ.prodMk continuous_snd)).mul hJ
  have hk' (y s : ℝ) : HasDerivAt (fun z ↦ k z s) (D y s) y := by
    simpa only [Function.comp_def] using (hcd (Z y s) s).comp y (hZ' y s)
  have hDbound (y s : ℝ) :
      ‖D y s‖ ≤ 2 * (B : ℝ) * Real.exp (2 * (B : ℝ) * T) := by
    change ‖d (Z y s) s * J y s‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul (hdbound (Z y s) s) (hJbound y s) (norm_nonneg _)
      (mul_nonneg (by norm_num) B.coe_nonneg)
  have hderiv := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := k) (F' := D) (μ := volume) (a := (0 : ℝ)) (b := t)
    (bound := fun _ ↦ 2 * (B : ℝ) * Real.exp (2 * (B : ℝ) * T))
    (s := univ) (x₀ := x) (Filter.univ_mem)
    (.of_forall fun y ↦
      (hk.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    ((hk.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)
    ((hD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (.of_forall fun s _ y _ ↦ hDbound y s) intervalIntegrable_const
    (.of_forall fun s _ y _ ↦ hk' y s)).2
  have heq : (fun y ↦ ∫ s in 0..t, k y s) =
      fun y ↦ ∫ s in 0..t, c (X y s) s := funext fun y ↦ hint y t ht
  have heq' : (∫ s in 0..t, D x s) =
      ∫ s in 0..t, d (X x s) s * Real.exp (∫ r in 0..s, c (X x r) r) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans ht.2⟩
    change d (Z x s) s * J x s = _
    rw [hZX x s hsT, hJX x s hsT]
  rwa [heq, heq'] at hderiv

/-- The flow Jacobian has the differentiated characteristic integral
as its spatial derivative, including at both endpoints of the time interval. -/
theorem hasDerivAt_hkCurve_jacobian
    {A : Set (ℝ^1)} {B : NNReal} {T : ℝ} (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, supportedHkBaseBall 1 2 univ A B))
    {c X : ℝ → ℝ → ℝ} (hchar : HkForwardCharacteristics hT f c X)
    (x t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivAt (fun y ↦ Real.exp (∫ s in 0..t, c (X y s) s))
      (Real.exp (∫ s in 0..t, c (X x s) s) *
        ∫ s in 0..t, deriv (fun y ↦ c y s) (X x s) *
          Real.exp (∫ r in 0..s, c (X x r) r)) x := by
  obtain ⟨d, hd, hcd, hdbound, _⟩ :=
    exists_hkCurve_hilbert_coefficient_hasDerivAt hT f hchar.coefficient_continuous
      hchar.hilbert_pair
  have h := (hasDerivAt_integral_hkCurve_coefficient hT f hchar.coefficient_continuous hd hcd
    hdbound hchar.velocity_derivative
    hchar.coefficient_bound hchar.flow_initial hchar.flow_derivative hchar.flow_continuous x t
      ht).exp
  have heq (y s : ℝ) : deriv (fun z ↦ c z s) y = d y s := (hcd y s).deriv
  simpa only [heq, mul_comm] using h

/-- The derivative of the Jacobian is uniformly bounded by
`2 B T exp(4 B T)`. This bound vanishes as the time interval shrinks. -/
theorem norm_deriv_hkCurve_jacobian_le
    {A : Set (ℝ^1)} {B : NNReal} {T : ℝ} (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, supportedHkBaseBall 1 2 univ A B))
    {c X : ℝ → ℝ → ℝ} (hchar : HkForwardCharacteristics hT f c X)
    (x t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    ‖deriv (fun y ↦ Real.exp (∫ s in 0..t, c (X y s) s)) x‖ ≤
      2 * (B : ℝ) * T * Real.exp (4 * (B : ℝ) * T) := by
  obtain ⟨d, _hd, hcd, hdbound, _⟩ :=
    exists_hkCurve_hilbert_coefficient_hasDerivAt hT f hchar.coefficient_continuous
      hchar.hilbert_pair
  rw [(hasDerivAt_hkCurve_jacobian hT f hchar x t ht).deriv,
    norm_mul]
  have hint : ‖∫ s in 0..t, deriv (fun y ↦ c y s) (X x s) *
      Real.exp (∫ r in 0..s, c (X x r) r)‖ ≤
      (2 * (B : ℝ) * Real.exp (2 * (B : ℝ) * T)) * T := by
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := t)
      (C := 2 * (B : ℝ) * Real.exp (2 * (B : ℝ) * T))
      (f := fun s ↦ deriv (fun y ↦ c y s) (X x s) *
        Real.exp (∫ r in 0..s, c (X x r) r)) (fun s hs ↦ ?_)
    · simp only [sub_zero, abs_of_nonneg ht.1] at hi
      exact hi.trans (mul_le_mul_of_nonneg_left ht.2 (by positivity))
    · rw [uIoc_of_le ht.1] at hs
      rw [norm_mul, (hcd (X x s) s).deriv]
      exact mul_le_mul (hdbound (X x s) s)
        (norm_exp_integral_flow_le hchar.coefficient_bound x s ⟨hs.1.le, hs.2.trans ht.2⟩)
        (norm_nonneg _) (mul_nonneg (by norm_num) B.coe_nonneg)
  calc
    _ ≤ Real.exp (2 * (B : ℝ) * T) *
        ((2 * (B : ℝ) * Real.exp (2 * (B : ℝ) * T)) * T) :=
      mul_le_mul (norm_exp_integral_flow_le hchar.coefficient_bound x t ht) hint
        (norm_nonneg _) (Real.exp_nonneg _)
    _ = 2 * (B : ℝ) * T * Real.exp (4 * (B : ℝ) * T) := by
      have he : 4 * (B : ℝ) * T = 2 * (B : ℝ) * T + 2 * (B : ℝ) * T := by cas
      rw [he, Real.exp_add]
      cas

end DeGregorio.Iteration
