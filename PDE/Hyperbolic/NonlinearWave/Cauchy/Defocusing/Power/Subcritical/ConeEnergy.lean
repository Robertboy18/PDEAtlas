/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.RetardedTrace
public import PDE.Hyperbolic.NonlinearWave.FinitePropagation.ConeEnergyIdentity
public import PDE.Analysis.Calculus.PowerPotential.Classical

/-!
# Energy control of the retarded trace

The cone flux identity bounds the weak gradient of the retarded H¹ trace. With the energy density
normalized by one half, the gradient energy is at most twice the energy at the base. The potential
is nonnegative. This is the bound (22) in the proof of Theorem 3 of Evans, §12.3.3, which Evans
derives from the flux identity (3) of §12.1.2 and states with the constant one.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.1.2, Theorem 2(i), equation (3); §12.3.3, proof
  of Theorem 3, equation (22).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set MeasureTheory Metric PDE PDE.Common PDE.Analysis
open SobolevSpace SobolevSpace.GraphSpace WaveEquation
open scoped Sobolev

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- The null flux pulled back to space is the tangential gradient energy plus
potential energy, including at the totalized vertex. -/
theorem coneDissipation_eq_retardedGradient (V : ℝ → ℝ) (u : ℝ^4 → ℝ) (c : ℝ^3) (T : ℝ) (x : ℝ^3) :
    semilinearWaveConeDissipation V u c (backwardConeGraph c T x) =
      (1 / 2 : ℝ) * ‖retardedGradient u c T x‖ ^ 2 + V (retardedTrace u c T x) := by
  simp only [semilinearWaveConeDissipation, semilinearWaveNullFlux,
    backwardConeGraph, spatialPart_timeSpaceCons, retardedGradient,
    retardedTrace, Function.comp_apply]
  rw [norm_sub_rev]

/-- The PDE and nonnegative potential control the weak gradient of any H¹
representative of the cone trace. -/
theorem norm_gradient_retardedTrace_sq_le {V : ℝ → ℝ} {u : ℝ^4 → ℝ} (hV : ContDiff ℝ 1 V)
    (hV0 : ∀ z, 0 ≤ V z) (hu : ContDiff ℝ 2 u) (c : ℝ^3) {T : ℝ} (hT : 0 ≤ T)
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x ∈ ball c (T - t),
      semilinearWaveOperator V u (timeSpaceCons t x) = 0)
    (U : H¹(ball c T))
    (hgrad : (∇ U : ℝ^3 → ℝ^3) =ᵐ[domainMeasure 3 (ball c T)] retardedGradient u c T) :
    ‖∇ U‖ ^ 2 ≤ 2 * semilinearBackwardConeEnergy V u c T 0 := by
  have hflux := normalized_integral_semilinearWaveConeDissipation hV hu c hT hwave
  rw [normalized_integral_backwardConeLateralSurface c T _
    (measurable_semilinearWaveConeDissipation hV.continuous hu c).aestronglyMeasurable] at hflux
  have hG : Integrable (fun x ↦ ‖∇ U x‖ ^ 2) (domainMeasure 3 (ball c T)) :=
    (Lp.memLp (∇ U)).norm.integrable_sq
  have hD := integrableOn_semilinearWaveConeDissipation_graph hV.continuous hu c T
  have hle : (1 / 2 : ℝ) * ‖∇ U‖ ^ 2 ≤
      ∫ x in ball c T, semilinearWaveConeDissipation V u c (backwardConeGraph c T x) := by
    rw [Lp.norm_sq_eq_integral_norm_sq, ← integral_const_mul]
    apply integral_mono_ae (hG.const_mul _) hD
    filter_upwards [hgrad] with x hx
    rw [hx, coneDissipation_eq_retardedGradient]
    exact le_add_of_nonneg_right (hV0 _)
  rw [hflux] at hle
  linarith

/-- A classical real-power solution supplies its H¹ cone trace and gradient
bound directly from the PDE. The exponent need not be an integer. -/
theorem exists_h1_retardedTrace_of_power_solution {p : ℝ} (hp : 1 ≤ p)
    {u : ℝ^4 → ℝ} (hu : ContDiff ℝ 2 u) (c : ℝ^3) {T : ℝ} (hT : 0 ≤ T)
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x ∈ ball c (T - t),
      waveOperator u (timeSpaceCons t x) + Real.signedPower p (u (timeSpaceCons t x)) = 0) :
    ∃ U : H¹(ball c T),
      baseRepresentative U =ᵐ[domainMeasure 3 (ball c T)] retardedTrace u c T ∧
      (∇ U : ℝ^3 → ℝ^3) =ᵐ[domainMeasure 3 (ball c T)] retardedGradient u c T ∧
      ‖∇ U‖ ^ 2 ≤ 2 * semilinearBackwardConeEnergy (Real.signedPowerPotential p) u c T 0 := by
  obtain ⟨U, hbase, hgrad⟩ := exists_h1_retardedTrace (hu.of_le (by norm_num)) c T T
  refine ⟨U, hbase, hgrad, norm_gradient_retardedTrace_sq_le
    (Real.contDiff_one_signedPowerPotential hp) (Real.signedPowerPotential_nonneg hp)
    hu c hT ?_ U hgrad⟩
  intro t ht x hx
  simpa only [semilinearWaveOperator, (Real.hasDerivAt_signedPowerPotential hp _).deriv]
    using hwave t ht x hx

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
