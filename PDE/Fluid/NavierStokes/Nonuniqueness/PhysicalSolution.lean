/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Nonuniqueness.PhysicalEnergyClass
public import PDE.Analysis.MeasureTheory.Lp.Composition.DilationOrbit

/-!
# The physical solutions

Fix an unstable profile `D`, a radius `R ≥ D.ancientThreshold` (the threshold of the ancient family)
and `s ∈ [0, 1]`. The physical velocity `u = physicalVelocity D R s` and the Riesz pressure
`p = physicalPressure D R s` of its slices form a classical solution of the unforced Navier–Stokes
equations on `(0, 1) × ℝ³` in the classical energy class, with `L²` initial trace the localized
datum `u_loc = localizedDatum (fun x ↦ ‖x‖⁻¹ • D.A x) R`. Distinct parameters `s` give distinct
velocities at time one.

## Main results

* `physical_classical`: at every point of `(0, 1) × ℝ³`, `u` and `p` are smooth, `u` is divergence
  free and the momentum equation with datum `u_loc` holds.
* `physical_classicalEnergyClass`: `(u, p)` lies in the classical energy class on `(0, 1]`.
* `physical_trace`: `u(t) → u_loc` in `L²` as `t → 0⁺`, for every `R > 0`.
* `physical_injective_at_one`: `s ↦ u(1)` is injective on `[0, 1]`.

## How it works

In similarity variables `u(t) = e^{σ/2} W(log t)(e^{σ/2} ·)` with `σ = -log t` and
`W = similarityVelocity D R s`, and the dilation `X ↦ e^{σ/2} X(e^{σ/2} ·)` multiplies `L²` norms by
`t^{1/4}` (`eLpNorm_dilate`). The slices are continuous into `L²` at positive times
(`tendsto_eLpNorm_velocitySlice_sub`) because `W` is (`tendsto_eLpNorm_similarityVelocity_sub`) and
so are the dilation orbits (`tendsto_eLpNorm_dilate_sub`). For the trace we split `W(τ)` into the
profile `D.U` minus the time-one heat flow of the homogeneous field `‖x‖⁻¹ D.A x`, the time-one heat
flow of the rescaled localized datum, and the correction field. The first and last parts are bounded
in `L²` for `τ ≤ 0`, so after dilation they carry the factor `t^{1/4}` and tend to `0`; the middle
part is the heat flow `e^{tΔ} u_loc` (`dilate_gaussianFlow_localizedDatum`), which tends to `u_loc`
in `L²`. The pressure slices satisfy `‖p(t)‖_{L²} ≤ 9 ‖u(t)‖²_{L⁴}`
(`toReal_eLpNorm_physicalPressure_slice_le`), so a bound `A t^{-1/8} + B t^{-3/8}` of the velocity
slices in `L⁴` puts the pressure in `L¹(0, 1; L²)` (`integrableOn_eLpNorm_physicalPressure`); its
measurability in time comes from the pressure path in `H³`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology SobolevSpace SobolevSpace.GraphSpace
open HeatEquation.WholeSpace IncompressibleFlow PDE.Common PDE.Analysis.Evolution
open scoped NNReal ENNReal Sobolev

namespace NavierStokes.Nonuniqueness

set_option linter.missingDocs true

variable {D : UnstableProfile} {R s : ℝ}

/-! ### Continuity of the velocity slices in `L²` -/

/-- **The velocity slices are continuous into `L²`** at every positive time. -/
theorem tendsto_eLpNorm_velocitySlice_sub (hR : 0 < R) {t₀ : ℝ} (ht₀ : 0 < t₀) :
    Tendsto (fun t ↦ eLpNorm (velocitySlice (physicalVelocity D R s) t -
      velocitySlice (physicalVelocity D R s) t₀) 2 volume) (𝓝 t₀) (𝓝 0) := by
  set W := similarityVelocity D R s
  set dil : ℝ → (ℝ^3 → ℝ^3) → ℝ^3 → ℝ^3 := fun σ f x ↦
    Real.exp (σ / 2) • f (Real.exp (σ / 2) • x)
  have hW (τ : ℝ) := memLp_similarityVelocity D s hR (le_refl (2 : ℝ≥0∞)) τ
  have hslice {t : ℝ} (ht : 0 < t) :
      velocitySlice (physicalVelocity D R s) t = dil (-Real.log t) (W (Real.log t)) := by
    rw [velocitySlice_physicalVelocity_eq D R s ht]
  have hsplit {t : ℝ} (ht : 0 < t) :
      velocitySlice (physicalVelocity D R s) t - velocitySlice (physicalVelocity D R s) t₀ =
        dil (-Real.log t) (W (Real.log t) - W (Real.log t₀)) +
          (dil (-Real.log t) (W (Real.log t₀)) - dil (-Real.log t₀) (W (Real.log t₀))) := by
    rw [hslice ht, hslice ht₀]
    funext x
    simp only [dil, Pi.sub_apply, Pi.add_apply, smul_sub]
    abel
  -- the first term
  have hlog : Tendsto Real.log (𝓝 t₀) (𝓝 (Real.log t₀)) :=
    (Real.continuousAt_log ht₀.ne').tendsto
  have hfac : Tendsto (fun t ↦ ENNReal.ofReal (Real.exp (-Real.log t / 2 *
      (1 - Module.finrank ℝ (ℝ^3) * (2 : ℝ≥0∞)⁻¹.toReal)))) (𝓝 t₀)
      (𝓝 (ENNReal.ofReal (Real.exp (-Real.log t₀ / 2 *
        (1 - Module.finrank ℝ (ℝ^3) * (2 : ℝ≥0∞)⁻¹.toReal))))) := by
    refine ENNReal.tendsto_ofReal ((Real.continuous_exp.tendsto _).comp ?_)
    exact ((hlog.neg.div_const 2).mul_const _)
  have hW₀ := (tendsto_eLpNorm_similarityVelocity_sub D s hR (le_refl (2 : ℝ≥0∞))
    (Real.log t₀)).comp hlog
  have h₁ : Tendsto (fun t ↦ eLpNorm (dil (-Real.log t) (W (Real.log t) - W (Real.log t₀))) 2
      volume) (𝓝 t₀) (𝓝 0) := by
    have h := ENNReal.Tendsto.mul hfac (Or.inr ENNReal.zero_ne_top) hW₀
      (Or.inr ENNReal.ofReal_ne_top)
    rw [mul_zero] at h
    refine h.congr fun t ↦ ?_
    exact (eLpNorm_dilate ((hW _).aestronglyMeasurable.sub (hW _).aestronglyMeasurable)
      (-Real.log t)).symm
  -- the second term
  have h₂ : Tendsto (fun t ↦ eLpNorm (dil (-Real.log t) (W (Real.log t₀)) -
      dil (-Real.log t₀) (W (Real.log t₀))) 2 volume) (𝓝 t₀) (𝓝 0) :=
    (tendsto_eLpNorm_dilate_sub (hW (Real.log t₀)) one_le_two ENNReal.ofNat_ne_top
      (-Real.log t₀)).comp hlog.neg
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa using h₁.add h₂) (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [Ioi_mem_nhds ht₀] with t ht
  rw [hsplit ht]
  exact eLpNorm_add_le one_le_two

/-! ### The initial trace -/

/-- Undoing the parabolic scaling of the time-one heat flow of the rescaled localized datum gives
the heat flow of the datum: `e^{-τ/2} (G₁ * (u_loc)_τ)(e^{-τ/2} x) = (e^{e^τ Δ} u_loc)(x)`. -/
theorem dilate_gaussianFlow_localizedDatum (D : UnstableProfile) (R : ℝ) {t : ℝ} (ht : 0 < t)
    (x : ℝ^3) :
    Real.exp (-Real.log t / 2) • (gaussianFlow 1 fun y ↦ Real.exp (Real.log t / 2) •
        localizedDatum (fun x ↦ ‖x‖⁻¹ • D.A x) R (Real.exp (Real.log t / 2) • y))
          (Real.exp (-Real.log t / 2) • x) =
      gaussianFlow t (localizedDatum (fun x ↦ ‖x‖⁻¹ • D.A x) R) x := by
  set u := localizedDatum (fun x ↦ ‖x‖⁻¹ • D.A x) R
  set b := Real.exp (Real.log t / 2)
  have hb : 0 < b := Real.exp_pos _
  have hscale := gaussianFlow_scaling hb 1 u (Real.exp (-Real.log t / 2) • x)
  have hb2 : b ^ 2 * 1 = t := by
    rw [mul_one, sq, ← Real.exp_add, add_halves, Real.exp_log ht]
  have hbb : b • Real.exp (-Real.log t / 2) • x = x := by
    rw [smul_smul, ← Real.exp_add]
    ring_nf
    simp
  rw [hb2, hbb] at hscale
  rw [gaussianFlow_const_smul 1 b (fun y ↦ u (b • y)), Pi.smul_apply, ← hscale, smul_smul,
    ← Real.exp_add]
  ring_nf
  simp

/-- **The `L²` initial trace of the physical solutions.** For `R > 0` the velocity slices tend
to the localized datum in `L²` as `t → 0⁺`. -/
theorem physical_trace (hR : 0 < R) :
    Tendsto (fun t ↦ eLpNorm (velocitySlice (physicalVelocity D R s) t -
      localizedDatum (fun x ↦ ‖x‖⁻¹ • D.A x) R) 2 volume) (𝓝[>] 0) (𝓝 0) := by
  set u := localizedDatum (fun x ↦ ‖x‖⁻¹ • D.A x) R
  set V := D.U - gaussianFlow 1 fun x ↦ ‖x‖⁻¹ • D.A x
  set H : ℝ → ℝ^3 → ℝ^3 := fun τ ↦ gaussianFlow 1 fun x ↦ Real.exp (τ / 2) •
    u (Real.exp (τ / 2) • x)
  set dil : ℝ → (ℝ^3 → ℝ^3) → ℝ^3 → ℝ^3 := fun σ f x ↦
    Real.exp (σ / 2) • f (Real.exp (σ / 2) • x)
  obtain ⟨hV2, -⟩ := D.memLp_sub_gaussianFlow_farField
  obtain ⟨K, hK0, hK⟩ := exists_eLpNorm_correctionField_le D
  have hu2 : MemLp u 2 volume := D.memLp_localizedDatum hR (by norm_num)
  -- the decomposition
  have hsplit {t : ℝ} (ht : 0 < t) :
      velocitySlice (physicalVelocity D R s) t - u =
        dil (-Real.log t) V + (gaussianFlow t u - u) +
          dil (-Real.log t) (correctionField D R s (Real.log t)) := by
    rw [velocitySlice_physicalVelocity_eq D R s ht]
    funext x
    have hW : similarityVelocity D R s (Real.log t) =
        V + H (Real.log t) + correctionField D R s (Real.log t) := by
      rw [similarityVelocity, profile_add_cutoffField]
    have hH := dilate_gaussianFlow_localizedDatum D R ht x
    simp only [dil, Pi.sub_apply, Pi.add_apply, hW, smul_add] at hH ⊢
    rw [hH]
    abel
  -- the factor `t^{1/4}`
  have hfac : Tendsto (fun t ↦ ENNReal.ofReal (Real.exp (-Real.log t / 2 *
      (1 - Module.finrank ℝ (ℝ^3) * (2 : ℝ≥0∞)⁻¹.toReal)))) (𝓝[>] 0) (𝓝 0) := by
    have hlim : Tendsto (fun t ↦ -Real.log t / 2 *
        (1 - Module.finrank ℝ (ℝ^3) * (2 : ℝ≥0∞)⁻¹.toReal)) (𝓝[>] 0) atBot := by
      have hc : (1 - (Module.finrank ℝ (ℝ^3) : ℝ) * (2 : ℝ≥0∞)⁻¹.toReal) = -(1 / 2) := by
        simp [finrank_euclideanSpace]
        norm_num
      rw [hc]
      have h := Real.tendsto_log_nhdsGT_zero.atBot_mul_const (r := 1 / 4) (by norm_num)
      refine h.congr fun t ↦ ?_
      ring
    simpa using ENNReal.tendsto_ofReal (Real.tendsto_exp_atBot.comp hlim)
  have h₁ : Tendsto (fun t ↦ eLpNorm (dil (-Real.log t) V) 2 volume) (𝓝[>] 0) (𝓝 0) := by
    have h := ENNReal.Tendsto.mul_const hfac (Or.inr hV2.eLpNorm_ne_top)
    rw [zero_mul] at h
    exact h.congr fun t ↦ (eLpNorm_dilate hV2.aestronglyMeasurable (-Real.log t)).symm
  have h₂ := tendsto_eLpNorm_gaussianFlow_sub_self hu2
  have h₃ : Tendsto (fun t ↦ eLpNorm (dil (-Real.log t)
      (correctionField D R s (Real.log t))) 2 volume) (𝓝[>] 0) (𝓝 0) := by
    have hb := ENNReal.Tendsto.mul_const hfac (b := ENNReal.ofReal (K * ‖ancientCorrection D R s‖))
      (Or.inr ENNReal.ofReal_ne_top)
    rw [zero_mul] at hb
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb
      (Eventually.of_forall fun _ ↦ zero_le) ?_
    filter_upwards [Ioo_mem_nhdsGT (one_pos : (0 : ℝ) < 1)] with t ht
    have hτ : Real.log t ≤ 0 := Real.log_nonpos ht.1.le ht.2.le
    rw [eLpNorm_dilate (hK R s le_rfl (Real.log t) 0).1.aestronglyMeasurable]
    refine mul_le_mul_right ((hK R s le_rfl (Real.log t) 0).2.1.trans
      (ENNReal.ofReal_le_ofReal ?_)) _
    refine mul_le_mul_of_nonneg_left ((norm_ancientLift_le _ _ _).trans ?_) hK0
    exact mul_le_of_le_one_right (norm_nonneg _)
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos D.dichotomy.η_pos.le hτ))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa using (h₁.add h₂).add h₃) (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [hsplit ht]
  exact (eLpNorm_add_le one_le_two).trans (add_le_add (eLpNorm_add_le one_le_two) le_rfl)

/-! ### The pressure -/

/-- Every slice of the physical pressure is square integrable. -/
theorem memLp_physicalPressure_slice (D : UnstableProfile) (R s t : ℝ) :
    MemLp (fun x ↦ physicalPressure D R s (timeSpaceCons t x)) 2 volume := by
  rcases le_or_gt t 0 with ht | ht
  · simp only [physicalPressure_timeSpaceCons_of_nonpos D R s ht]
    exact MemLp.zero
  · simp only [physicalPressure_timeSpaceCons D R s ht]
    exact memLp_two_rieszPressure _

/-- The pressure slices are bounded by the velocity in `L⁴`: `‖p(t)‖_{L²} ≤ 9 ‖u(t)‖²_{L⁴}`. -/
theorem toReal_eLpNorm_physicalPressure_slice_le (hR : 0 < R) {t : ℝ} (ht : 0 < t) :
    (eLpNorm (fun x ↦ physicalPressure D R s (timeSpaceCons t x)) 2 volume).toReal ≤
      9 * (eLpNorm (velocitySlice (physicalVelocity D R s) t) 4 volume).toReal ^ 2 := by
  simp only [physicalPressure_timeSpaceCons D R s ht]
  have h := toReal_eLpNorm_rieszPressure_le
    (memLp_velocitySlice_physicalVelocity D s hR (q := 4) (by norm_num) ht)
  norm_num at h
  exact h

/-- **The pressure lies in `L¹(0, 1; L²)`.** -/
theorem integrableOn_eLpNorm_physicalPressure (hR : D.ancientThreshold ≤ R)
    (hs : s ∈ Icc (0 : ℝ) 1) :
    IntegrableOn (fun t ↦ (eLpNorm (fun x ↦ physicalPressure D R s (timeSpaceCons t x)) 2
      volume).toReal) (Ioc 0 1) := by
  have hR0 : 0 < R := lt_of_lt_of_le one_pos (D.one_le_ancientThreshold.trans hR)
  obtain ⟨A, B, hA, hB, hAB⟩ := exists_toReal_eLpNorm_velocitySlice_le D s hR0 (p := 2) (q := 4)
    one_le_two (by norm_num) (by norm_num) (by norm_num)
  -- measurability from the continuity of the pressure path
  have hmeas : AEStronglyMeasurable (fun t ↦ (eLpNorm (fun x ↦
      physicalPressure D R s (timeSpaceCons t x)) 2 volume).toReal)
      (volume.restrict (Ioc 0 1)) := by
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    have hc : ContinuousOn (fun t ↦ ‖wkpBaseCoordinateCLM (physicalPressureSobolev D R s 3 t)‖)
        (Ioo 0 1) :=
      continuous_norm.comp_continuousOn ((wkpBaseCoordinateCLM :
        W^{3,2}(ℝ^3) →L[ℝ] DerivLp 3 2 univ).continuous.comp_continuousOn
          (contDiffOn_physicalPressureSobolev hR hs 3).continuousOn)
    refine (hc.aestronglyMeasurable measurableSet_Ioo).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simp only [physicalPressure_timeSpaceCons D R s ht.1]
    rw [eLpNorm_congr_ae (rieszPressure_velocitySlice_ae_eq hR hs 3 ht.1 ht.2.le), Lp.norm_def]
    simp only [domainMeasure, Measure.restrict_univ]
    rfl
  have hint : IntegrableOn (fun t : ℝ ↦ 18 * A ^ 2 * t ^ (-(1 / 4) : ℝ) +
      18 * B ^ 2 * t ^ (-(3 / 4) : ℝ)) (Ioc 0 1) := by
    refine Integrable.add (Integrable.const_mul ?_ _) (Integrable.const_mul ?_ _)
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        (intervalIntegral.intervalIntegrable_rpow' (by norm_num))
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        (intervalIntegral.intervalIntegrable_rpow' (by norm_num))
  refine Integrable.mono' hint hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  have h₁ := toReal_eLpNorm_physicalPressure_slice_le (D := D) (s := s) hR0 ht.1
  have h₂ := hAB t ht
  rw [show ENNReal.ofReal 4 = 4 by norm_num] at h₂
  have h₀ : 0 ≤ (eLpNorm (velocitySlice (physicalVelocity D R s) t) 4 volume).toReal :=
    ENNReal.toReal_nonneg
  have e₁ : t ^ ((3 / (4 : ℝ) - 1) / 2) = t ^ (-(1 / 8) : ℝ) := by norm_num
  have e₂ : t ^ ((3 / (4 : ℝ) - 3 / 2) / 2) = t ^ (-(3 / 8) : ℝ) := by norm_num
  rw [e₁, e₂] at h₂
  have q₁ : (t ^ (-(1 / 8) : ℝ)) ^ 2 = t ^ (-(1 / 4) : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.1.le]
    norm_num
  have q₂ : (t ^ (-(3 / 8) : ℝ)) ^ 2 = t ^ (-(3 / 4) : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.1.le]
    norm_num
  have hsq := pow_le_pow_left₀ h₀ h₂ 2
  have hx₁ : 0 ≤ t ^ (-(1 / 8) : ℝ) := Real.rpow_nonneg ht.1.le _
  have hx₂ : 0 ≤ t ^ (-(3 / 8) : ℝ) := Real.rpow_nonneg ht.1.le _
  rw [← q₁, ← q₂]
  nlinarith [sq_nonneg (A * t ^ (-(1 / 8) : ℝ) - B * t ^ (-(3 / 8) : ℝ))]

/-! ### The physical solutions -/

/-- The slices of the physical velocity are bounded in `L²` on `(0, 1]`. -/
theorem exists_eLpNorm_velocitySlice_le (hR : 0 < R) :
    ∃ C : ℝ, ∀ t ∈ Ioc (0 : ℝ) 1,
      eLpNorm (velocitySlice (physicalVelocity D R s) t) 2 volume ≤ ENNReal.ofReal C := by
  obtain ⟨A, B, hA, hB, hAB⟩ := exists_toReal_eLpNorm_velocitySlice_le D s hR (p := 2) (q := 2)
    one_le_two (by norm_num) le_rfl le_rfl
  refine ⟨A + B, fun t ht ↦ ?_⟩
  have h := hAB t ht
  rw [show ENNReal.ofReal 2 = 2 by norm_num] at h
  have hfin := (memLp_velocitySlice_physicalVelocity D s hR (q := 2) le_rfl ht.1).eLpNorm_ne_top
  rw [← ENNReal.ofReal_toReal hfin]
  refine ENNReal.ofReal_le_ofReal (h.trans ?_)
  have e : t ^ ((3 / (2 : ℝ) - 3 / 2) / 2) = 1 := by norm_num
  have h₁ : t ^ ((3 / (2 : ℝ) - 1) / 2) ≤ 1 :=
    Real.rpow_le_one ht.1.le ht.2 (by norm_num)
  rw [e]
  nlinarith

/-- **The energy class of the physical solutions.** Above the threshold radius and for
`s ∈ [0, 1]` the physical velocity and pressure lie in the classical energy class on `(0, 1]`. -/
theorem physical_classicalEnergyClass (hR : D.ancientThreshold ≤ R) (hs : s ∈ Icc (0 : ℝ) 1) :
    ClassicalEnergyClass (physicalVelocity D R s) (physicalPressure D R s) 1 := by
  have hR0 : 0 < R := lt_of_lt_of_le one_pos (D.one_le_ancientThreshold.trans hR)
  exact
    { time_pos := one_pos
      slice_contDiff := fun t ht ↦
        (contDiff_velocitySlice_physicalVelocity hR hs ht.1 ht.2).of_le (by simp)
      velocity_memLp := fun t ht ↦ memLp_velocitySlice_physicalVelocity D s hR0 le_rfl ht.1
      gradient_memLp := fun t ht ↦ memLp_fderiv_velocitySlice_physicalVelocity hR hs ht.1 ht.2
      pressure_memLp := fun t _ ↦ memLp_physicalPressure_slice D R s t
      velocity_bounded := exists_eLpNorm_velocitySlice_le hR0
      gradient_sq_integrableOn :=
        integrableOn_sq_eLpNorm_fderiv_velocitySlice_physicalVelocity hR hs
      pressure_integrableOn := integrableOn_eLpNorm_physicalPressure hR hs
      tendsto_velocity := fun t ht ↦
        (tendsto_eLpNorm_velocitySlice_sub hR0 ht.1).mono_left nhdsWithin_le_nhds }

/-- **The physical solutions are classical.** Above the threshold radius and for `s ∈ [0, 1]`,
at every point of `(0, 1) × ℝ³` the physical velocity and pressure are smooth, the velocity is
divergence free, and they satisfy the momentum equation of the unforced Navier–Stokes problem
with datum the localized far field. -/
theorem physical_classical (hR : D.ancientThreshold ≤ R) (hs : s ∈ Icc (0 : ℝ) 1)
    (hu₀ : DistributionallyDivergenceFree (localizedDatum (fun x ↦ ‖x‖⁻¹ • D.A x) R)) :
    ∀ z ∈ IncompressibleFlow.finiteTimeDomain 3 1,
      ContDiffAt ℝ (⊤ : ℕ∞) (physicalVelocity D R s) z ∧
        ContDiffAt ℝ (⊤ : ℕ∞) (physicalPressure D R s) z ∧
        DivergenceFreeAt (physicalVelocity D R s) z ∧
        MomentumEquationAt (unforcedProblem (localizedDatum (fun x ↦ ‖x‖⁻¹ • D.A x) R) hu₀)
          (physicalVelocity D R s) (physicalPressure D R s) z :=
  fun _ hz ↦ ⟨(physical_time_regularity D R s hR hs).2 _ hz, contDiffAt_physicalPressure hR hs hz,
    divergenceFreeAt_physical hR hs hz, momentumEquationAt_physical hR hs hu₀ hz⟩

/-- **Distinct parameters give distinct solutions at time one.** Above the threshold radius,
`s ↦ u(1)` is injective on `[0, 1]`. -/
theorem physical_injective_at_one (hR : D.ancientThreshold ≤ R) :
    InjOn (fun s ↦ velocitySlice (physicalVelocity D R s) 1) (Icc 0 1) :=
  fun _ hs _ hs' h ↦ eq_of_velocitySlice_physicalVelocity_one_ae_eq hR hs hs'
    (Filter.EventuallyEq.of_eq h)

end NavierStokes.Nonuniqueness
