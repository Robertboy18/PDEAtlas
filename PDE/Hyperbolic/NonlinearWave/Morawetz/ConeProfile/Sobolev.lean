/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Morawetz.ConeProfile.Calculus
public import PDE.Hyperbolic.NonlinearWave.Morawetz.ConeProfile.RemovablePoint
public import PDE.Spaces.Sobolev.GraphSpace.Representatives.FirstOrder
public import PDE.Spaces.Sobolev.Variational.Spaces.H1
import PDE.FDeriv.Calculus

/-!
# Sobolev membership of a cone profile

Finite tangential derivative energy and finite sixth-power potential supply
an H¹ element on the ball. The exceptional tip is removed by coordinate-line integration by parts.
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set Filter SobolevSpace SobolevSpace.GraphSpace PDE PDE.Common
open scoped Sobolev Topology

namespace WaveEquation.ConeProfile

private theorem aestronglyMeasurable_punctured {n : ℕ} (hn : 0 < n) {F : Type*}
    [NormedAddCommGroup F] [SecondCountableTopology F] {c : ℝ^n} {r : ℝ} {f : ℝ^n → F}
    (hf : ContinuousOn f (ball c r \ {c})) :
    AEStronglyMeasurable f (domainMeasure n (ball c r)) := by
  let : Nontrivial (ℝ^n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simpa using hn)
  have hμ : domainMeasure n (ball c r \ {c}) = domainMeasure n (ball c r) := by
    apply Measure.restrict_congr_set
    filter_upwards [volume.ae_ne c] with x hx
    simp [hx]
  rw [← hμ]
  exact hf.aestronglyMeasurable (isOpen_ball.sdiff isClosed_singleton).measurableSet

/-- Finite cone densities construct H¹ membership and identify the weak gradient.
The ambient field is required to be C¹ only at points of the punctured cone. -/
theorem exists_h1_of_integrable_densities {n : ℕ} (hn : 2 ≤ n) {T r : ℝ} {c : ℝ^n}
    {u : ℝ^(n + 1) → ℝ}
    (hu : ∀ x ∈ ball c r, x ≠ c → ContDiffAt ℝ 1 u (timeSpaceCons (T - ‖x - c‖) x))
    (hgradient : IntegrableOn (fun x ↦ ‖coneProfileGradient T c u x‖ ^ 2) (ball c r))
    (hpotential : IntegrableOn (fun x ↦ coneProfile T c u x ^ 6) (ball c r)) :
    ∃ U : H¹(ball c r), baseRepresentative U =ᵐ[domainMeasure n (ball c r)] coneProfile T c u ∧
      (∇ U : ℝ^n → ℝ^n) =ᵐ[domainMeasure n (ball c r)] coneProfileGradient T c u := by
  let : IsFiniteMeasure (domainMeasure n (ball c r)) :=
    isFiniteMeasure_domainMeasure_of_isBounded isBounded_ball
  let : Nontrivial (ℝ^n) := Module.nontrivial_of_finrank_pos (R := ℝ)
    (by simpa using (show 0 < n by omega))
  let w := coneProfile T c u
  let G := coneProfileGradient T c u
  have hw (x : ℝ^n) (hx : x ∈ ball c r) (hne : x ≠ c) : ContDiffAt ℝ 1 w x :=
    contDiffAt_coneProfile hne (hu x hx hne)
  have hm : AEStronglyMeasurable w (domainMeasure n (ball c r)) :=
    aestronglyMeasurable_punctured (by omega)
      (fun x hx ↦ (hw x hx.1 hx.2).continuousAt.continuousWithinAt)
  have hGc : ContinuousOn G (ball c r \ {c}) := by
    have hcoords : ContinuousOn (fun x ↦ fun i : Fin n ↦ (∂[i] w) x) (ball c r \ {c}) :=
      continuousOn_pi.mpr fun i x hx ↦
        (contDiffAt_partialDeriv 0 (hw x hx.1 hx.2) i).continuousAt.continuousWithinAt
    have h := (PiLp.continuous_toLp 2 (fun _ : Fin n ↦ ℝ)).comp_continuousOn hcoords
    refine h.congr fun x hx ↦ ?_
    refine PiLp.ext fun i ↦ ?_
    exact (partialDeriv_coneProfile hx.2 ((hu x hx.1 hx.2).differentiableAt one_ne_zero) i).symm
  have hGm : AEStronglyMeasurable G (domainMeasure n (ball c r)) :=
    aestronglyMeasurable_punctured (by omega) hGc
  have hG : MemLp G 2 (domainMeasure n (ball c r)) :=
    (memLp_two_iff_integrable_sq_norm hGm).2 hgradient
  have h6 : Integrable (fun x ↦ ‖w x‖ ^ 6) (domainMeasure n (ball c r)) := by
    simpa only [w, Real.norm_eq_abs, (by decide : Even 6).pow_abs,
      IntegrableOn, domainMeasure] using hpotential
  have h2 : Integrable (fun x ↦ ‖w x‖ ^ 2) (domainMeasure n (ball c r)) :=
    integrable_norm_pow_of_le hm (by omega : 2 ≤ 6) h6
  have hwmem : MemLp w 2 (domainMeasure n (ball c r)) := (memLp_two_iff_integrable_sq_norm hm).2 h2
  refine exists_of_weakGradient hwmem hG fun i ↦ ?_
  have heq : (∂[i] w) =ᵐ[domainMeasure n (ball c r)] fun x ↦ G x i := by
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet,
      ae_restrict_of_ae (volume.ae_ne c)] with x hx hne
    exact partialDeriv_coneProfile hne ((hu x hx hne).differentiableAt one_ne_zero) i
  have hcoord : MemLp (fun x ↦ G x i) 2 (domainMeasure n (ball c r)) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' hG
  have hpartial : MemLp (∂[i] w) 2 (domainMeasure n (ball c r)) := (memLp_congr_ae heq).mpr hcoord
  have hweak : HasWeakDerivativeOn (ball c r) [i] w (∂[i] w) := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
    exact hasWeakDerivativeOn_punctured (by omega)
      (fun x hx hne ↦ (hw x hx hne).differentiableAt one_ne_zero)
      (hwmem.integrable (by norm_num)) i (hpartial.integrable (by norm_num))
  exact hweak.congr_ae EventuallyEq.rfl heq

end WaveEquation.ConeProfile
