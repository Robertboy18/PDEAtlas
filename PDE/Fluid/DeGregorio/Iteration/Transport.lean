/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Transport.Data
public import PDE.Fluid.DeGregorio.Iteration.EulerianCoordinates
public import PDE.Fluid.DeGregorio.Iteration.HilbertCoefficient
public import PDE.Analysis.MeasureTheory.Lp.CommonSupportConvergence

/-!
# Transported vorticity for a curve in the bounded H² class

The normalized Hilbert velocity constructs forward and inverse
characteristics on the prescribed interval. The exponential integral of its
spatial derivative then constructs a jointly continuous Eulerian
field. Its initial trace, characteristic ODE, sign, and support follow from
this construction.

The input curve is frozen: the Hilbert pair in the conclusion relates the input
curve, not the transported field, to the stretching coefficient.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set PDE.Analysis PDE.Analysis.Evolution
open scoped Topology

open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

private theorem exists_continuous_L2_of_common_support
    {w : ℝ → ℝ → ℝ} {T R : ℝ}
    (hw : Continuous (fun p : ℝ × Icc (0 : ℝ) T ↦ w p.1 p.2))
    (hsupp : ∀ y t, t ∈ Icc (0 : ℝ) T → R < |y| → w y t = 0) :
    ∃ F : C(Icc (0 : ℝ) T, Lp ℝ 2 volume),
      ∀ t, (F t : ℝ → ℝ) =ᵐ[volume] fun y ↦ w y t := by
  have hcont (t : Icc (0 : ℝ) T) : Continuous (fun y ↦ w y t) :=
    hw.comp (continuous_id.prodMk continuous_const)
  have hsupport (t : Icc (0 : ℝ) T) : Function.support (fun y ↦ w y t) ⊆ Icc (-R) R :=
    fun y hy ↦ abs_le.mp (le_of_not_gt fun h ↦ hy (hsupp y t t.property h))
  have hcompact (t : Icc (0 : ℝ) T) : HasCompactSupport (fun y ↦ w y t) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) <|
      closure_minimal (hsupport t) isClosed_Icc
  have hmem (t : Icc (0 : ℝ) T) : MemLp (fun y ↦ w y t) 2 volume :=
    (hcont t).memLp_of_hasCompactSupport (hcompact t)
  let F (t : Icc (0 : ℝ) T) : Lp ℝ 2 volume := (hmem t).toLp (fun y ↦ w y t)
  have hF : Continuous F := by
    refine continuous_iff_continuousAt.mpr fun t₀ ↦ ?_
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun t : Icc (0 : ℝ) T ↦ fun y ↦ w y t) hmem _ (hmem t₀)).mpr
    have huniform : TendstoUniformlyOn (fun t : Icc (0 : ℝ) T ↦ fun y ↦ w y t)
        (fun y ↦ w y t₀) (𝓝 t₀) (Icc (-R) R) := by
      apply tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
      exact Continuous.tendstoUniformly
        (fun t : Icc (0 : ℝ) T ↦ fun y : Icc (-R) R ↦ w y t)
        (hw.comp ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst)) t₀
    exact tendsto_eLpNorm_sub_of_tendstoUniformlyOn (by norm_num)
      measurableSet_Icc.nullMeasurableSet (by simp)
      (.of_forall fun t ↦ ((hmem t).sub (hmem t₀)).aestronglyMeasurable)
      (.of_forall hsupport) (hsupport t₀) huniform
  exact ⟨⟨F, hF⟩, fun t ↦ (hmem t).coeFn_toLp⟩

/-- Every curve in the complete bounded H² class constructs an Eulerian field
on the whole prescribed interval. The field solves the stretching ODE
along the constructed characteristics and preserves zeros and signs there.
Its support is contained in the explicit enclosure `S * exp (2 B T)`, and it
represents a continuous L²-valued curve. -/
theorem exists_hkCurve_transport_along_characteristics
    {A : Set (ℝ^1)} {B : NNReal} {T S : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (f : C(Icc (0 : ℝ) T, supportedHkBaseBall 1 2 univ A B))
    {w₀ : ℝ → ℝ} (hw₀ : Continuous w₀)
    (hsupp₀ : ∀ x, S < |x| → w₀ x = 0) :
    ∃ c X Y w : ℝ → ℝ → ℝ, HkTransportResult hT f S w₀ c X Y w := by
  obtain ⟨c, hc, hpair, hcderiv, hcbound, _hmodulus⟩ :=
    exists_hkCurve_hilbert_coefficient hT f
  obtain ⟨X, Y, hX₀, hX', hX, hY, hYX, hXY, hYlip, hgrowth⟩ :=
    exists_hkCurve_hilbert_eulerian_coordinates hT f
  let k : ℝ → ℝ → ℝ := fun x t ↦ c (X x (projIcc 0 T hT t)) t
  have hk : Continuous (Function.uncurry k) :=
    hc.comp ((hX.comp (continuous_fst.prodMk
      ((continuous_projIcc (h := hT)).comp continuous_snd))).prodMk continuous_snd)
  have hk_eq (x t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : k x t = c (X x t) t := by
    simp only [k, projIcc_of_mem hT ht]
  let v : ℝ → ℝ → ℝ := fun x t ↦ w₀ x * Real.exp (∫ s in 0..t, k x s)
  have hv : Continuous (Function.uncurry v) :=
    (hw₀.comp continuous_fst).mul
      (intervalIntegral.continuous_parametric_primitive_of_continuous hk).rexp
  have hv₀ (x : ℝ) : v x 0 = w₀ x := by
    simp only [v, intervalIntegral.integral_same, Real.exp_zero, mul_one]
  have hv' (x t : ℝ) : HasDerivAt (v x) (k x t * v x t) t := by
    have hkx : Continuous (k x) := hk.comp (continuous_const.prodMk continuous_id)
    simpa only [v, mul_comm, mul_left_comm, mul_assoc] using
      ((hkx.integral_hasStrictDerivAt 0 t).hasDerivAt.exp.const_mul (w₀ x))
  let w : ℝ → ℝ → ℝ := fun y t ↦ v (Y y t) t
  have hwpath (x t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      w (X x t) t = v x t := by
    simp only [w, hYX x t ht]
  have hformula (x t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      w (X x t) t = w₀ x * Real.exp (∫ s in 0..t, c (X x s) s) := by
    rw [hwpath x t ht]
    refine congrArg (fun I ↦ w₀ x * Real.exp I) (intervalIntegral.integral_congr fun s hs ↦ ?_)
    rw [uIcc_of_le ht.1] at hs
    exact hk_eq x s ⟨hs.1, hs.2.trans ht.2⟩
  have hwbound (y t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      ‖w y t‖ ≤ ‖w₀ (Y y t)‖ * Real.exp (2 * (B : ℝ) * t) := by
    have hi : (∫ s in 0..t, k (Y y t) s) ≤ 2 * (B : ℝ) * t := by
      have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := 0) (b := t) (f := k (Y y t)) (C := 2 * (B : ℝ))
        (fun s _ ↦ hcbound _ s)
      simpa only [sub_zero, abs_of_nonneg ht.1] using (le_abs_self _).trans hnorm
    simpa only [w, v, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hi) (norm_nonneg (w₀ (Y y t)))
  have hw : Continuous (fun p : ℝ × Icc (0 : ℝ) T ↦ w p.1 p.2) :=
    hv.comp (hY.prodMk (continuous_subtype_val.comp continuous_snd))
  have hwsupp (y t : ℝ) (ht : t ∈ Icc (0 : ℝ) T)
      (hy : S * Real.exp (2 * (B : ℝ) * T) < |y|) : w y t = 0 := by
    by_cases hx : S < |Y y t|
    · simp only [w, v, hsupp₀ _ hx, zero_mul]
    · have hbound := hgrowth (Y y t) t ht
      rw [hXY y t ht] at hbound
      refine absurd hy (not_lt_of_ge (hbound.trans ?_))
      gcongr
      exacts [le_of_not_gt hx, ht.2]
  refine ⟨c, X, Y, w, {
    toHkTransportData := {
      toHkCharacteristics := {
        toHkForwardCharacteristics := ⟨hc, hpair, hcderiv, hcbound, hX₀, hX', hX⟩
        inverse_continuous := hY
        inverse_flow := hYX
        flow_inverse := hXY
        inverse_lipschitz := hYlip }
      continuous := hw
      initial := fun x ↦ by
        simpa only [w, show Y x 0 = x by simpa only [hX₀] using hYX x 0 ⟨le_rfl, hT⟩] using hv₀ x
      formula := hformula
      along_flow := fun x t ht ↦ by
        simpa only [hk_eq x t ht, ← hwpath x t ht] using
          (hv' x t).hasDerivWithinAt.congr_of_mem (hwpath x) ht }
    zero_iff := fun x t ht ↦ by
      rw [hformula x t ht]; exact mul_eq_zero_iff_right (Real.exp_ne_zero _)
    pos_iff := fun x t ht ↦ by
      rw [hformula x t ht]; exact mul_pos_iff_of_pos_right (Real.exp_pos _)
    neg_iff := fun x t ht ↦ by
      rw [hformula x t ht]
      simpa only [zero_mul] using mul_lt_mul_iff_left₀ (Real.exp_pos
        (∫ s in 0..t, c (X x s) s)) (b := w₀ x) (c := 0)
    norm_le := hwbound
    support := hwsupp
    representative := exists_continuous_L2_of_common_support hw hwsupp }⟩

end DeGregorio.Iteration
