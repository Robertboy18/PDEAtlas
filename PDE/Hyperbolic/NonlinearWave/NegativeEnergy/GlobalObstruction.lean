/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.DominatedData
import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.Conservation
import PDE.Hyperbolic.NonlinearWave.NegativeEnergy.Concavity
import PDE.Solution.Singularity.FiniteTime.Comparison.Concavity.HalfLine
import PDE.Solution.Singularity.FiniteTime.Comparison.Concavity.LeftEndpoint

/-!
# Global obstruction for negative-energy semilinear waves

The negative-energy virial inequality is incompatible with a classical
semilinear wave on either complete time half-line. The first two theorems
assume conservation of the spatial energy directly. The final two derive
that conservation law from the local energy identity.

These are continuation obstructions, not norm blow-up statements.
A model-specific continuation criterion determines which state-space norm
must become unbounded at a finite maximal endpoint.

The result is Evans, §12.5.1, Theorem 1, proved by Levine's concavity method: a compactly supported
classical solution of `u_tt - Δu + V'(u) = 0` with `z V'(z) ≤ Λ V(z)`, `Λ > 2`, and negative energy
cannot exist for all `t ≥ t₀`. The dominated-differentiation data are explicit hypotheses.

## Main results

* `not_global_forward_semilinearWave_of_negative_conserved_energy`,
  `not_global_backward_semilinearWave_of_negative_conserved_energy`: the
  obstruction on `[t₀, ∞)` and on `(-∞, t₀]`, assuming energy conservation.
* `not_global_forward_semilinearWave_of_negative_energy`,
  `not_global_backward_semilinearWave_of_negative_energy`: the same, with
  conservation derived from the local energy identity of
  `GlobalEnergy.Conservation`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.5.1, Theorem 1 and its proof, equations (1)-(7).
  <https://doi.org/10.1090/gsm/019>
* H. A. Levine, *Instability and nonexistence of global solutions to nonlinear wave equations
  of the form `Pu_tt = -Au + F(u)`*, Trans. Amer. Math. Soc. 192 (1974), 1-21, Theorem I(A) and its
  proof, pp. 4-7.
  <https://doi.org/10.1090/S0002-9947-1974-0344697-2>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open PDE.Solution.Singularity.FiniteTime.Concavity
open scoped Topology

namespace WaveEquation

variable {n : ℕ}

/-- A classical semilinear wave cannot continue for all future times while
retaining negative conserved energy and satisfying the analytic hypotheses of
the concavity method.

This is a continuation obstruction, not by itself a statement that a
particular Sobolev norm diverges. Any continuation criterion may turn this
contradiction into a norm blow-up result once its additional hypotheses have
been formalized. -/
theorem not_global_forward_semilinearWave_of_negative_conserved_energy {V : ℝ → ℝ}
    {u : ℝ^(n + 1) → ℝ} {Λ t₀ : ℝ} (hVzero : V 0 = 0) (hV : ContDiff ℝ 1 V) (hu : ContDiff ℝ 2 u)
    (hΛ : 2 < Λ) (hgrowth : ∀ z, z * deriv V z ≤ Λ * V z)
    (hwave : ∀ t, t₀ ≤ t → ∀ x : ℝ^n, semilinearWaveOperator (n := n) V u
      (PDE.Common.timeSpaceCons (n := n) t x) = 0)
    (hD : DominatedVirialData u (Ici t₀))
    (henergyConserved : ∀ t, t₀ ≤ t → semilinearWaveSpatialEnergy (n := n) V u t =
      semilinearWaveSpatialEnergy (n := n) V u t₀)
    (henergyNeg : semilinearWaveSpatialEnergy (n := n) V u t₀ < 0) :
    False := by
  have hmassHasDeriv := hasDerivAt_waveSpatialQuadraticMass_on (times := Ici t₀)
      (fun _ _ ↦ Eventually.of_forall fun _ _ ↦ (hu.of_le (by norm_num)).contDiffAt)
      hD.compact_support hD.mass_mem_nhds hD.mass_dominated hD.mass_bound_integrable
  have hmomentumDifferentiable := differentiableAt_waveSpatialQuadraticMomentum_on (times := Ici t₀)
      (fun _ _ ↦ Eventually.of_forall fun _ _ ↦ hu.contDiffAt)
      hD.compact_support hD.momentum_mem_nhds hD.momentum_dominated hD.momentum_bound_integrable
  have hmassPos := waveSpatialQuadraticMass_pos_on_of_negative_conserved_energy
      (times := Ici t₀) hVzero
      (fun _ _ _ ↦ (hu.of_le (by norm_num)).contDiffAt)
      hD.compact_support henergyConserved henergyNeg
  have hconcavity := waveSpatialQuadraticMomentum_concavity_inequality_on_of_conserved_energy
      (times := Ici t₀) hVzero hV (fun _ _ ↦ Eventually.of_forall fun _ _ ↦ hu.contDiffAt)
      hΛ.le hgrowth hwave hD.compact_support
      hD.momentum_mem_nhds hD.momentum_dominated hD.momentum_bound_integrable henergyConserved
  have ha : 0 < (Λ - 2) / 4 := by
    linarith
  have hb : 0 <
        -Λ * semilinearWaveSpatialEnergy (n := n) V u t₀ := by
    exact mul_pos_of_neg_of_neg
      (neg_lt_zero.mpr (by linarith)) henergyNeg
  apply (not_concavity_inequality_on_Ici (I := waveSpatialQuadraticMass (n := n) u)
      (P := waveSpatialQuadraticMomentum (n := n) u) (a := (Λ - 2) / 4)
      (b := -Λ * semilinearWaveSpatialEnergy (n := n) V u t₀)
      ha hb hmassHasDeriv hmomentumDifferentiable hmassPos)
  exact hconcavity

/-- A classical semilinear wave cannot continue for all past times while
retaining negative conserved energy and satisfying the analytic hypotheses of
the concavity method.

The virial inequality is unchanged in the past direction. The scalar
concavity obstruction applies after reflecting time, with quadratic momentum
changing sign and its square therefore remaining unchanged. As in the forward
theorem, the conclusion obstructs classical continuation rather than naming a
particular norm that must diverge. -/
theorem not_global_backward_semilinearWave_of_negative_conserved_energy {V : ℝ → ℝ}
    {u : ℝ^(n + 1) → ℝ} {Λ t₀ : ℝ} (hVzero : V 0 = 0) (hV : ContDiff ℝ 1 V) (hu : ContDiff ℝ 2 u)
    (hΛ : 2 < Λ) (hgrowth : ∀ z, z * deriv V z ≤ Λ * V z)
    (hwave : ∀ t, t ≤ t₀ → ∀ x : ℝ^n, semilinearWaveOperator (n := n) V u
      (PDE.Common.timeSpaceCons (n := n) t x) = 0)
    (hD : DominatedVirialData u (Iic t₀))
    (henergyConserved : ∀ t, t ≤ t₀ → semilinearWaveSpatialEnergy (n := n) V u t =
      semilinearWaveSpatialEnergy (n := n) V u t₀)
    (henergyNeg : semilinearWaveSpatialEnergy (n := n) V u t₀ < 0) :
    False := by
  have hmassHasDeriv := hasDerivAt_waveSpatialQuadraticMass_on (times := Iic t₀)
      (fun _ _ ↦ Eventually.of_forall fun _ _ ↦ (hu.of_le (by norm_num)).contDiffAt)
      hD.compact_support hD.mass_mem_nhds hD.mass_dominated hD.mass_bound_integrable
  have hmomentumDifferentiable := differentiableAt_waveSpatialQuadraticMomentum_on (times := Iic t₀)
      (fun _ _ ↦ Eventually.of_forall fun _ _ ↦ hu.contDiffAt)
      hD.compact_support hD.momentum_mem_nhds hD.momentum_dominated hD.momentum_bound_integrable
  have hmassPos := waveSpatialQuadraticMass_pos_on_of_negative_conserved_energy
      (times := Iic t₀) hVzero
      (fun _ _ _ ↦ (hu.of_le (by norm_num)).contDiffAt)
      hD.compact_support henergyConserved henergyNeg
  have hconcavity := waveSpatialQuadraticMomentum_concavity_inequality_on_of_conserved_energy
      (times := Iic t₀) hVzero hV (fun _ _ ↦ Eventually.of_forall fun _ _ ↦ hu.contDiffAt)
      hΛ.le hgrowth hwave hD.compact_support
      hD.momentum_mem_nhds hD.momentum_dominated hD.momentum_bound_integrable henergyConserved
  have ha : 0 < (Λ - 2) / 4 := by
    linarith
  have hb : 0 <
        -Λ * semilinearWaveSpatialEnergy (n := n) V u t₀ := by
    exact mul_pos_of_neg_of_neg
      (neg_lt_zero.mpr (by linarith)) henergyNeg
  apply (not_concavity_inequality_on_Iic (I := waveSpatialQuadraticMass (n := n) u)
      (P := waveSpatialQuadraticMomentum (n := n) u) (a := (Λ - 2) / 4)
      (b := -Λ * semilinearWaveSpatialEnergy (n := n) V u t₀)
      ha hb hmassHasDeriv hmomentumDifferentiable hmassPos)
  exact hconcavity

/-- Negative initial energy obstructs a classical continuation for all future
times under the explicit hypotheses required by the local energy identity and
the concavity method.

The theorem derives energy conservation from
`semilinearWaveSpatialEnergy_eq_of_wave_on_uIcc` and then applies the preceding
continuation obstruction. -/
theorem not_global_forward_semilinearWave_of_negative_energy {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    {Λ t₀ : ℝ} (hVzero : V 0 = 0) (hV : ContDiff ℝ 1 V) (hu : ContDiff ℝ 2 u) (hΛ : 2 < Λ)
    (hgrowth : ∀ z, z * deriv V z ≤ Λ * V z)
    (hwave : ∀ t, t₀ ≤ t → ∀ x : ℝ^n, semilinearWaveOperator (n := n) V u
      (PDE.Common.timeSpaceCons (n := n) t x) = 0)
    (hD : DominatedVirialData u (Ici t₀)) (hE : DominatedEnergyData V u (Ici t₀))
    (henergyNeg : semilinearWaveSpatialEnergy (n := n) V u t₀ < 0) :
    False := by
  apply not_global_forward_semilinearWave_of_negative_conserved_energy
      hVzero hV hu hΛ hgrowth hwave hD (henergyNeg := henergyNeg)
  intro t ht
  have hsubset : uIcc t₀ t ⊆ Ici t₀ := by
    intro r hr
    rw [uIcc_of_le ht] at hr
    exact hr.1
  let E := hE.mono hsubset
  symm
  apply semilinearWaveSpatialEnergy_eq_of_wave_on_uIcc hV
    (fun _ _ ↦ Eventually.of_forall fun _ _ ↦ hu.contDiffAt)
  · intro r hr
    exact hwave r (hsubset hr)
  · exact E.energy_integrable
  · exact E.mem_nhds
  · exact E.dominated
  · exact E.bound_integrable
  · exact E.flux_compact_support

/-- Negative initial energy obstructs a classical continuation for all past
times under the explicit hypotheses required by the local energy identity and
the concavity method.

For each `t ≤ t₀`, the unoriented interval `uIcc t₀ t` is the closed interval
`[t, t₀]`. Thus all hypotheses needed to derive conservation remain inside the
past half-line before the conserved-energy backward obstruction is applied. -/
theorem not_global_backward_semilinearWave_of_negative_energy {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    {Λ t₀ : ℝ} (hVzero : V 0 = 0) (hV : ContDiff ℝ 1 V) (hu : ContDiff ℝ 2 u) (hΛ : 2 < Λ)
    (hgrowth : ∀ z, z * deriv V z ≤ Λ * V z)
    (hwave : ∀ t, t ≤ t₀ → ∀ x : ℝ^n, semilinearWaveOperator (n := n) V u
      (PDE.Common.timeSpaceCons (n := n) t x) = 0)
    (hD : DominatedVirialData u (Iic t₀)) (hE : DominatedEnergyData V u (Iic t₀))
    (henergyNeg : semilinearWaveSpatialEnergy (n := n) V u t₀ < 0) :
    False := by
  apply not_global_backward_semilinearWave_of_negative_conserved_energy
      hVzero hV hu hΛ hgrowth hwave hD (henergyNeg := henergyNeg)
  intro t ht
  have hsubset : uIcc t₀ t ⊆ Iic t₀ := by
    intro r hr
    rw [uIcc_of_ge ht] at hr
    exact hr.2
  let E := hE.mono hsubset
  symm
  apply semilinearWaveSpatialEnergy_eq_of_wave_on_uIcc hV
    (fun _ _ ↦ Eventually.of_forall fun _ _ ↦ hu.contDiffAt)
  · intro r hr
    exact hwave r (hsubset hr)
  · exact E.energy_integrable
  · exact E.mem_nhds
  · exact E.dominated
  · exact E.bound_integrable
  · exact E.flux_compact_support

end WaveEquation
