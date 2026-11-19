/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.CenteredTrace
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.IntegralEnergy
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.TraceL2
public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.Bounds
import PDE.Analysis.Calculus.LocalExtension.TimeBand
import PDE.FDeriv.PartialDeriv.Regularity

/-!
# Physical energy and scaled L² bounds for integral trajectories

The identified H¹ displacement and L² velocity give the spatial energy of the C¹ field, including
the initial slice. Conservation then controls its velocity on every ball. A C¹ representative on a
proper closed prefix supplies the retarded trace, whose scaled L² norm is bounded using the initial
displacement. The bound applies to any H¹ representative of that trace.

These are the physical-energy inputs to the proof of Theorem 3 of Evans, §12.3.3. The scaled L²
bound replaces (23)-(24): we integrate the velocity in time up to the cone instead of using
Poincaré's inequality and the bound on the average. All real powers at least one are allowed.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.3.3, proof of Theorem 3, equations (23)-(24).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory Metric PDE PDE.Common PDE.Analysis WaveEquation
open SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev SobolevSpace.WholeSpaceHilbert Topology Laplacian

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
/-- The physical spatial energy is exactly the energy of its identified H¹/L²
representatives. Integrability of the potential is retained explicitly. -/
private theorem spatialEnergy_eq_of_energy_representatives {V : ℝ → ℝ} {u : ℝ^4 → ℝ} {t : ℝ}
    {q : H¹(ℝ^3)} {v : DerivLp 3 2 univ}
    (hq : ∀ j : Fin 3, (wkpCoordinateCLM (singleDerivIndex 3 j) q : ℝ^3 → ℝ)
      =ᵐ[domainMeasure 3 univ] fun x ↦ (∂[j.succ] u) (timeSpaceCons t x))
    (hv : (v : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 univ] fun x ↦ (∂[0] u) (timeSpaceCons t x))
    (hV : Integrable (fun x : ℝ^3 ↦ V (u (timeSpaceCons t x)))) :
    Integrable (semilinearWaveSpatialEnergyDensity V u t) ∧
      semilinearWaveSpatialEnergy V u t = (1 / 2 : ℝ) * (gradientForm 3 q q + ‖v‖ ^ 2) + ∫ x : ℝ^3,
        V (u (timeSpaceCons t x)) := by
  have hvSq : Integrable (fun x : ℝ^3 ↦ ((∂[0] u) (timeSpaceCons t x)) ^ 2) := by
    have h := (Lp.memLp v).integrable_sq
    simp only [domainMeasure, Measure.restrict_univ] at h hv
    exact h.congr (hv.mono fun x hx ↦ congrArg (fun z : ℝ ↦ z ^ 2) hx)
  have hqSq (j : Fin 3) :
      Integrable (fun x : ℝ^3 ↦ ((∂[j.succ] u) (timeSpaceCons t x)) ^ 2) := by
    have h := (Lp.memLp (wkpCoordinateCLM (singleDerivIndex 3 j) q)).integrable_sq
    simp only [domainMeasure, Measure.restrict_univ] at h hq
    exact h.congr ((hq j).mono fun x hx ↦ congrArg (fun z : ℝ ↦ z ^ 2) hx)
  have hgrad : Integrable (fun x : ℝ^3 ↦
      ‖classicalWaveSpatialGradient u (timeSpaceCons t x)‖ ^ 2) := by
    simpa only [EuclideanSpace.real_norm_sq_eq, classicalWaveSpatialGradient_apply] using
      integrable_finsetSum Finset.univ (fun j _ ↦ hqSq j)
  have heV : (∫ x : ℝ^3, ((∂[0] u) (timeSpaceCons t x)) ^ 2) = ‖v‖ ^ 2 := by
    rw [Lp.norm_sq_eq_integral_sq]
    simp only [domainMeasure, Measure.restrict_univ] at hv ⊢
    exact integral_congr_ae (hv.symm.mono fun x hx ↦ congrArg (fun z : ℝ ↦ z ^ 2) hx)
  have heQ : (∫ x : ℝ^3, ‖classicalWaveSpatialGradient u (timeSpaceCons t x)‖ ^ 2) =
      gradientForm 3 q q := by
    simp only [EuclideanSpace.real_norm_sq_eq, classicalWaveSpatialGradient_apply]
    rw [integral_finsetSum _ (fun j _ ↦ hqSq j), gradientForm_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [real_inner_self_eq_norm_sq, Lp.norm_sq_eq_integral_sq]
    simp only [domainMeasure, Measure.restrict_univ] at hq ⊢
    exact integral_congr_ae ((hq j).symm.mono fun x hx ↦ congrArg (fun z : ℝ ↦ z ^ 2) hx)
  have hkin : Integrable (fun x : ℝ^3 ↦ (1 / 2 : ℝ) * (((∂[0] u) (timeSpaceCons t x)) ^ 2 +
        ‖classicalWaveSpatialGradient u (timeSpaceCons t x)‖ ^ 2)) := (hvSq.add hgrad).const_mul _
  have hi := hkin.add hV
  refine ⟨hi, ?_⟩
  unfold semilinearWaveSpatialEnergy semilinearWaveSpatialEnergyDensity
    semilinearWaveEnergyDensity classicalWaveEnergyDensity
  rw [integral_add hkin hV, integral_const_mul,
    integral_add hvSq hgrad, heV, heQ, add_comm (‖v‖ ^ 2)]

/-- The H¹/L² energy representatives of a product-space field give its physical
spatial energy after the canonical spacetime identification. Only first
pointwise differentiability on the chosen slice is required. -/
private theorem spatialEnergy_eq_of_product_energy_representatives {V : ℝ → ℝ} {u : ℝ × ℝ^3 → ℝ}
    {t : ℝ} (hu : ∀ x : ℝ^3, DifferentiableAt ℝ u (t, x)) {q : H¹(ℝ^3)} {v : DerivLp 3 2 univ}
    (hq : ∀ j : Fin 3, (wkpCoordinateCLM (singleDerivIndex 3 j) q : ℝ^3 → ℝ)
      =ᵐ[domainMeasure 3 univ] ∂[j] (fun x ↦ u (t, x)))
    (hv : (v : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 univ] fun x ↦ fderiv ℝ u (t, x) (1, 0))
    (hV : Integrable (fun x : ℝ^3 ↦ V (u (t, x)))) :
    Integrable (semilinearWaveSpatialEnergyDensity V
      (fun p : ℝ^4 ↦ u (timeSpaceContinuousLinearEquiv 3 p)) t) ∧
      semilinearWaveSpatialEnergy V
        (fun p : ℝ^4 ↦ u (timeSpaceContinuousLinearEquiv 3 p)) t =
        (1 / 2 : ℝ) * (gradientForm 3 q q + ‖v‖ ^ 2) +
          ∫ x : ℝ^3, V (u (t, x)) := by
  let e := timeSpaceContinuousLinearEquiv 3
  let U : ℝ^4 → ℝ := fun p ↦ u (e p)
  have hd (x : ℝ^3) : DifferentiableAt ℝ U (timeSpaceCons t x) :=
    (hu x).comp (timeSpaceCons t x) e.differentiableAt
  have hspace (x : ℝ^3) (j : Fin 3) :
      (∂[j.succ] U) (timeSpaceCons t x) = (∂[j] (fun y ↦ u (t, y))) x := by
    rw [← partialDeriv_timeSpaceCons_spatial j U t x (hd x)]
    rfl
  have htime (x : ℝ^3) :
      (∂[0] U) (timeSpaceCons t x) = fderiv ℝ u (t, x) (1, 0) := by
    have h := (hu x).hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
    exact (hasDerivAt_timeSpaceCons U t x (hd x)).unique h
  have h := spatialEnergy_eq_of_energy_representatives (u := U) (t := t) (q := q) (v := v)
    (fun j ↦ (hq j).mono fun x hx ↦ hx.trans (hspace x j).symm)
    (hv.mono fun x hx ↦ hx.trans (htime x).symm) hV
  exact h

/-- The C¹ integral trajectory has integrable spatial energy, equal to
its initial energy on every proper closed prefix. -/
theorem IsIntegralTrajectoryBefore.spatialEnergy_eq_of_support {r b L R : ℝ} (hr : 1 ≤ r)
    (hb : 0 < b) {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h)
    {u : ℝ × ℝ^3 → ℝ}
    (hu : IsIntegralTrajectoryBefore r b (cauchyFreeField g h) L u)
    (hvel : ∀ x : ℝ^3, HasDerivAt (fun t ↦ u (t, x)) (h x) 0)
    (hsupp : ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 L → R + p.1 < ‖p.2‖ → u p = 0) {S : ℝ} (hS : 0 < S)
    (hSL : S < L) :
    let U : ℝ^4 → ℝ := fun p ↦ u (timeSpaceContinuousLinearEquiv 3 p)
    ∀ t ∈ Icc 0 S,
      Integrable (semilinearWaveSpatialEnergyDensity (Real.signedPowerPotential r) U t) ∧
      semilinearWaveSpatialEnergy (Real.signedPowerPotential r) U t =
        semilinearWaveSpatialEnergy (Real.signedPowerPotential r) U 0 := by
  have hhs : HasCompactSupport h := hu.hasCompactSupport_initial_velocity hvel hsupp
  dsimp only
  obtain ⟨q, v, _, _, hae, he⟩ :=
    hu.hasConservedEnergyOn_of_support hr hb hg hh hvel hsupp hS hSL
  have hO : IsOpen {p : ℝ × ℝ^3 | -b < p.1 ∧ p.1 < L} :=
    (isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_fst continuous_const)
  have hm (t : ℝ) (ht : t ∈ Icc 0 S) (x : ℝ^3) : (t, x) ∈ {p : ℝ × ℝ^3 | -b < p.1 ∧ p.1 < L} :=
    ⟨by linarith [ht.1], ht.2.trans_lt hSL⟩
  have hd (t : ℝ) (ht : t ∈ Icc 0 S) (x : ℝ^3) : DifferentiableAt ℝ u (t, x) :=
    (hu.regular.contDiffAt (hO.mem_nhds (hm t ht x))).differentiableAt one_ne_zero
  have hV (t : ℝ) (ht : t ∈ Icc 0 S) :
      Integrable (fun x : ℝ^3 ↦ Real.signedPowerPotential r (u (t, x))) := by
    have hc : Continuous (fun x : ℝ^3 ↦ u (t, x)) :=
      hu.regular.continuousOn.comp_continuous (continuous_const.prodMk continuous_id) (hm t ht)
    apply ((Real.contDiff_one_signedPowerPotential hr).continuous.comp
      hc).integrable_of_hasCompactSupport
    apply HasCompactSupport.intro (isCompact_closedBall (0 : ℝ^3) (R + S))
    intro x hx
    have hx' : R + S < ‖x‖ := by
      simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx
    change Real.signedPowerPotential r (u (t, x)) = 0
    rw [hsupp (t, x) ⟨ht.1, ht.2.trans_lt hSL⟩
      ((add_le_add (le_refl R) ht.2).trans_lt hx'), Real.signedPowerPotential_zero hr]
  have hid (t : ℝ) (ht : t ∈ Icc 0 S) :=
    spatialEnergy_eq_of_product_energy_representatives (hd t ht)
      (hae t ht).2.1 (hae t ht).2.2 (hV t ht)
  intro t ht
  refine ⟨(hid t ht).1, ?_⟩
  rw [(hid t ht).2, (hid 0 ⟨le_rfl, hS.le⟩).2]
  exact he t ht

/-- First-order regularity suffices for the kinetic-energy bound on every ball. -/
private theorem lpNorm_velocity_ball_le_of_contDiff_one {V : ℝ → ℝ} {u : ℝ^4 → ℝ}
    (hV : ∀ z, 0 ≤ V z) (hu : ContDiff ℝ 1 u) (t : ℝ)
    (hi : Integrable (semilinearWaveSpatialEnergyDensity V u t)) {E : ℝ} (hE : 0 ≤ E)
    (he : 2 * semilinearWaveSpatialEnergy V u t ≤ E ^ 2) (c : ℝ^3) (r : ℝ) :
    lpNorm (fun x ↦ (∂[0] u) (timeSpaceCons t x)) 2 (domainMeasure 3 (Metric.ball c r)) ≤ E := by
  have hc : Continuous (fun x : ℝ^3 ↦ (∂[0] u) (timeSpaceCons t x)) :=
    (hu.continuous_partialDeriv 0).comp (contDiff_timeSpaceCons_spatial 3 t (m := 1)).continuous
  have hpoint (x : ℝ^3) : ((∂[0] u) (timeSpaceCons t x)) ^ 2 ≤
      2 * semilinearWaveSpatialEnergyDensity V u t x := by
    have h := semilinearWaveSpatialKineticEnergyDensity_le_spatialEnergyDensity V hV u t x
    unfold semilinearWaveSpatialKineticEnergyDensity at h
    linarith
  have hs : Integrable (fun x : ℝ^3 ↦ ((∂[0] u) (timeSpaceCons t x)) ^ 2) := by
    apply (hi.const_mul 2).mono' (hc.pow 2).aestronglyMeasurable
    filter_upwards [] with x
    change |((∂[0] u) (timeSpaceCons t x)) ^ 2| ≤ _
    rw [abs_of_nonneg (sq_nonneg _)]
    exact hpoint x
  have hm : MemLp (fun x : ℝ^3 ↦ (∂[0] u) (timeSpaceCons t x)) 2
      (domainMeasure 3 (Metric.ball c r)) :=
    (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).mpr
      (hs.mono_measure Measure.restrict_le_self)
  have hb := setIntegral_le_integral (s := Metric.ball c r) hs
    (Filter.Eventually.of_forall fun x ↦ sq_nonneg ((∂[0] u) (timeSpaceCons t x)))
  have hwhole : (∫ x : ℝ^3, ((∂[0] u) (timeSpaceCons t x)) ^ 2) ≤
      2 * semilinearWaveSpatialEnergy V u t := by
    simpa only [semilinearWaveSpatialEnergy, integral_const_mul] using
      integral_mono hs (hi.const_mul 2) hpoint
  rw [hm.integral_sq_eq_lpNorm_sq] at hb
  nlinarith [lpNorm_nonneg (f := fun x : ℝ^3 ↦ (∂[0] u) (timeSpaceCons t x))
    (p := 2) (μ := domainMeasure 3 (Metric.ball c r))]

/-- Spatial energy depends only on the field and its first derivative germs. -/
private theorem spatialEnergyDensity_eq_of_eventuallyEq {V : ℝ → ℝ} {u v : ℝ^4 → ℝ} {t : ℝ}
    (h : ∀ x : ℝ^3, u =ᶠ[𝓝 (timeSpaceCons t x)] v) :
    semilinearWaveSpatialEnergyDensity V u t = semilinearWaveSpatialEnergyDensity V v t := by
  funext x
  have hg : classicalWaveSpatialGradient u (timeSpaceCons t x) =
      classicalWaveSpatialGradient v (timeSpaceCons t x) := by
    ext j
    exact partialDeriv_eq_of_fderiv_eq (h x).fderiv_eq j.succ
  simp only [semilinearWaveSpatialEnergyDensity, semilinearWaveEnergyDensity,
    classicalWaveEnergyDensity, (h x).eq_of_nhds, hg,
    partialDeriv_eq_of_fderiv_eq (h x).fderiv_eq 0]

/-- Conserved energy of the C¹ lifespan bounds its time derivative on
all spatial balls throughout a proper closed prefix, including time zero. -/
theorem IsIntegralTrajectoryBefore.lpNorm_velocity_ball_le {r b L R : ℝ} (hr : 1 ≤ r) (hb : 0 < b)
    {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h)
    {u : ℝ × ℝ^3 → ℝ} (hu : IsIntegralTrajectoryBefore r b (cauchyFreeField g h) L u)
    (hvel : ∀ x : ℝ^3, HasDerivAt (fun t ↦ u (t, x)) (h x) 0)
    (hsupp : ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 L → R + p.1 < ‖p.2‖ → u p = 0) {S : ℝ} (hS : 0 < S)
    (hSL : S < L) {E : ℝ} (hE : 0 ≤ E)
    (henergy : 2 * semilinearWaveSpatialEnergy (Real.signedPowerPotential r)
      (fun p : ℝ^4 ↦ u (timeSpaceContinuousLinearEquiv 3 p)) 0 ≤ E ^ 2)
    {t : ℝ} (ht : t ∈ Icc 0 S) (c : ℝ^3) (ρ : ℝ) :
    lpNorm (fun x : ℝ^3 ↦ (∂[0] (fun p : ℝ^4 ↦ u (timeSpaceContinuousLinearEquiv 3 p)))
      (timeSpaceCons t x)) 2 (domainMeasure 3 (Metric.ball c ρ)) ≤ E := by
  have hhs : HasCompactSupport h := hu.hasCompactSupport_initial_velocity hvel hsupp
  obtain ⟨v, hv, he⟩ := hu.regular.exists_contDiff_eventuallyEq_on_band
    (ContinuousLinearMap.fst ℝ ℝ (ℝ^3)) (s := 0) (τ := S) (by linarith) hSL
  let e := timeSpaceContinuousLinearEquiv 3
  let U : ℝ^4 → ℝ := fun p ↦ u (e p)
  let V : ℝ^4 → ℝ := fun p ↦ v (e p)
  have hV : ContDiff ℝ 1 V := hv.comp e.contDiff
  have hl (s : ℝ) (hs : s ∈ Icc 0 S) (x : ℝ^3) : U =ᶠ[𝓝 (timeSpaceCons s x)] V :=
    (he (s, x) hs).comp_tendsto e.continuousAt
  have hden := spatialEnergyDensity_eq_of_eventuallyEq (V := Real.signedPowerPotential r) (hl t ht)
  have hi := hu.spatialEnergy_eq_of_support hr hb hg hh hvel hsupp hS hSL t ht
  have henergyV : 2 * semilinearWaveSpatialEnergy (Real.signedPowerPotential r) V t ≤
      E ^ 2 := by
    change 2 * (∫ x, semilinearWaveSpatialEnergyDensity _ V t x) ≤ _
    rw [← hden]
    exact (by rw [hi.2]; exact henergy :
      2 * semilinearWaveSpatialEnergy (Real.signedPowerPotential r) U t ≤ E ^ 2)
  have hbound := lpNorm_velocity_ball_le_of_contDiff_one
    (Real.signedPowerPotential_nonneg hr) hV t (hden ▸ hi.1) hE henergyV c ρ
  have hp : (fun x : ℝ^3 ↦ (∂[0] U) (timeSpaceCons t x)) = fun x ↦ (∂[0] V) (timeSpaceCons t x) :=
    funext fun x ↦ partialDeriv_eq_of_fderiv_eq (hl t ht x).fderiv_eq 0
  change lpNorm (fun x ↦ (∂[0] U) (timeSpaceCons t x)) 2 _ ≤ _
  rw [hp]
  exact hbound

/-- Every H¹ representative of a centered retarded trace obeys the
scaled L² estimate from initial displacement and conserved energy. -/
theorem IsIntegralTrajectoryBefore.norm_base_centered_retardedTrace_div_le {r b L R : ℝ}
    (hr : 1 ≤ r) (hb : 0 < b) {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h)
    {u : ℝ × ℝ^3 → ℝ}
    (hu : IsIntegralTrajectoryBefore r b (cauchyFreeField g h) L u)
    (hvel : ∀ x : ℝ^3, HasDerivAt (fun t ↦ u (t, x)) (h x) 0)
    (hsupp : ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 L → R + p.1 < ‖p.2‖ → u p = 0) {T A E G : ℝ} (hT : 0 < T)
    (hTL : T < L) (hTA : T ≤ A) (hE : 0 ≤ E) (hG : 0 ≤ G) (hinit : ∀ x : ℝ^3, ‖u (0, x)‖ ≤ G)
    (henergy : 2 * semilinearWaveSpatialEnergy (Real.signedPowerPotential r)
      (fun p : ℝ^4 ↦ u (timeSpaceContinuousLinearEquiv 3 p)) 0 ≤ E ^ 2)
    (c : ℝ^3) (W : H¹(Metric.ball (0 : ℝ^3) T))
    (hW : baseRepresentative W =ᵐ[domainMeasure 3 (Metric.ball 0 T)] fun x ↦ u (T - ‖x‖, c + x)) :
    ‖wkpBaseCoordinateCLM W‖ / T ≤ E + G * √(A * volume.real (Metric.ball (0 : ℝ^3) 1)) := by
  have hhs : HasCompactSupport h := hu.hasCompactSupport_initial_velocity hvel hsupp
  obtain ⟨v, hv, he⟩ := hu.regular.exists_contDiff_eventuallyEq_on_band
    (ContinuousLinearMap.fst ℝ ℝ (ℝ^3)) (s := 0) (τ := T) (by linarith) hTL
  let e := timeSpaceContinuousLinearEquiv 3
  let U : ℝ^4 → ℝ := fun p ↦ u (e p)
  let V : ℝ^4 → ℝ := fun p ↦ v (e p)
  have hV : ContDiff ℝ 1 V := hv.comp e.contDiff
  have hl (s : ℝ) (hs : s ∈ Icc 0 T) (x : ℝ^3) : U =ᶠ[𝓝 (timeSpaceCons s x)] V :=
    (he (s, x) hs).comp_tendsto e.continuousAt
  have hvbound (s : ℝ) (hs : s ∈ Icc 0 T) : lpNorm (fun x ↦ (∂[0] V) (timeSpaceCons s x)) 2
        (domainMeasure 3 (Metric.ball c T)) ≤ E := by
    have hp : (fun x : ℝ^3 ↦ (∂[0] U) (timeSpaceCons s x)) = fun x ↦ (∂[0] V) (timeSpaceCons s x) :=
      funext fun x ↦ partialDeriv_eq_of_fderiv_eq (hl s hs x).fderiv_eq 0
    rw [← hp]
    exact hu.lpNorm_velocity_ball_le hr hb hg hh hvel hsupp hT hTL hE henergy hs c T
  obtain ⟨Q, hQ, _⟩ := exists_h1_retardedTrace hV c T T
  have hbQ := norm_base_retardedTrace_le hV c hT.le hE hvbound Q hQ
  obtain ⟨W₀, hW₀, hbW₀, _⟩ := exists_centered_retardedTrace Q hQ
  have hW₀u : baseRepresentative W₀ =ᵐ[domainMeasure 3 (Metric.ball 0 T)]
      fun x ↦ u (T - ‖x‖, c + x) := by
    filter_upwards [hW₀, ae_restrict_mem measurableSet_ball] with x hx hxT
    have ht : T - ‖x‖ ∈ Icc 0 T :=
      ⟨(sub_pos.mpr (by simpa only [Metric.mem_ball, dist_zero_right] using hxT)).le,
        sub_le_self _ (norm_nonneg _)⟩
    exact hx.trans (he (T - ‖x‖, c + x) ht).eq_of_nhds.symm
  have hWeq : W = W₀ :=
    wkpBaseCoordinateCLM_injective Metric.isOpen_ball (Lp.ext (hW.trans hW₀u.symm))
  rw [hWeq, hbW₀]
  have hinitV (x : ℝ^3) : ‖V (timeSpaceCons 0 x)‖ ≤ G := by
    change ‖v (0, x)‖ ≤ G
    rw [← (he (0, x) ⟨le_rfl, hT.le⟩).eq_of_nhds]
    exact hinit x
  have hb := div_le_div_of_nonneg_right hbQ hT.le
  rw [add_div, mul_div_cancel_left₀ E hT.ne'] at hb
  have hi := lpNorm_initial_div_radius_le hG hinitV c hT hTA
  exact hb.trans (by linarith)

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
