/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.Lifespan
import PDE.Analysis.Normed.Group.CompactSupport
import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.Conservation
import PDE.Hyperbolic.NonlinearWave.NegativeEnergy.CompactData.GlobalObstruction
import PDE.Hyperbolic.NonlinearWave.NegativeEnergy.Lifespan
import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.FinitePropagation
import CAS.ExactTactic

/-!
# Lifespan of negative-energy waves from compact data

Let `V` be `C²` with `V 0 = 0` and `z V'(z) ≤ Λ V(z)` for some `Λ > 2`, and let `g`, `h` be
compactly supported Cauchy data on `ℝ^n`, `n ≥ 1`, with negative energy
`∫ ½ (h² + |∇g|²) + V(g) < 0`. For the classical solutions of `u_tt - Δu + V'(u) = 0`,
`WaveEquation.SmallData.Classical.IsSolutionBefore (deriv V) g h T u`, we prove:

* `bddAbove_existenceTimes_of_compact_negative_energy`: the durations `T` of all such solutions
  have a common finite bound;
* `lifespan_le_of_compact_negative_energy`: when moreover `∫ g h > 0`, every such solution has
  `T ≤ 2 ∫ g² / ((Λ - 2) ∫ g h)`.

Both theorems take the data and nothing else: support, domination and conservation of the energy
are derived. They bound the durations of the solutions that exist; they do not construct a
solution, and they say nothing about a norm of it.

## How it works

The first theorem is `not_global_forward_semilinearWave_of_compact_negative_energy` after gluing
arbitrarily long solutions into a global one
(`WaveEquation.SmallData.Classical.exists_globalSolution_of_unbounded`).

The second discharges the hypotheses of
`WaveEquation.right_endpoint_le_riccati_horizon_of_negative_conserved_energy` at the initial
time, where it reads `T ≤ ((Λ - 2) / 4 · P(0) / I(0))⁻¹` with `I(0) = ½ ∫ g²` and `P(0) = ∫ g h`.
A solution before `T` is `C²` on `{t < T}` and solves the equation on `[0, T)`; at negative times
it is only a regular representative, with no control of its support. For `0 < S < T`,
`IsSolutionBefore.exists_compact_representative` replaces it by a `C²` function `U` on the whole
space-time whose slices lie in one ball at all times, that agrees with the solution near every
point of `(0, S) × ℝ^n` and has the Cauchy data `g`, `h`. The cone-support constructions
`dominatedVirialDataOfConeSupport` and `dominatedEnergyDataOfConeSupport` give its virial and
energy domination data, the equation at time zero follows by continuity
(`waveOperator_add_eq_zero_of_mem_Icc`), and the Riccati horizon gives
`S ≤ 2 ∫ g² / ((Λ - 2) ∫ g h)`.

## References

The two theorems restate, for the solution class `IsSolutionBefore`, the results of
`PDE.Hyperbolic.NonlinearWave.NegativeEnergy.CompactData.GlobalObstruction` and
`PDE.Hyperbolic.NonlinearWave.NegativeEnergy.Lifespan`. Their module docs cite the sources of the
concavity argument; this module adds none of its own.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Common
open WaveEquation.SmallData.Classical
open scoped Topology BigOperators

namespace WaveEquation.NegativeEnergy

variable {n : ℕ} [Fact (0 < n)] {g h : ℝ^n → ℝ} {V : ℝ → ℝ} {Λ : ℝ}

/-- Compact Cauchy data of negative energy `∫ ½ (h² + |∇g|²) + V(g)` bound the durations of all
classical solutions of `u_tt - Δu + V'(u) = 0`, when `V` is `C²` with `V 0 = 0` and
`z V'(z) ≤ Λ V(z)` for some `Λ > 2`. -/
theorem bddAbove_existenceTimes_of_compact_negative_energy (hV : ContDiff ℝ 2 V)
    (hVzero : V 0 = 0) (hΛ : 2 < Λ) (hgrowth : ∀ z, z * deriv V z ≤ Λ * V z)
    (hgc : HasCompactSupport g) (hhc : HasCompactSupport h)
    (henergy :
      (∫ x : ℝ^n, (1 / 2 : ℝ) * ((h x) ^ 2 + ∑ i : Fin n, ((∂[i] g) x) ^ 2) + V (g x)) < 0) :
    BddAbove (existenceTimes (deriv V) g h) := by
  by_contra hbound
  obtain ⟨u, hu⟩ := exists_globalSolution_of_unbounded hV.deriv'.locallyLipschitz hbound
  refine not_global_forward_semilinearWave_of_compact_negative_energy hV hVzero hΛ hgrowth hgc hhc
    henergy hu.regular.contDiffOn (hu.regular.of_le (by norm_num)).contDiffOn (fun t ht x ↦ ?_)
    hu.position fun x ↦ ?_
  · rw [hu.equation _ (by simpa using ht.le), neg_add_cancel]
  · rw [← hu.velocity x]
    exact (PDE.hasDerivAt_timeSpaceCons u 0 x
      (hu.regular.differentiable (by norm_num) _)).hasDerivWithinAt.derivWithin
        (uniqueDiffOn_Ici 0 0 (by simp))

/-- **Lifespan from compact data.** Let `V` be `C²` with `V 0 = 0` and `z V'(z) ≤ Λ V(z)` for some
`Λ > 2`. A classical solution before `T` of `u_tt - Δu + V'(u) = 0` from compactly supported data
`g`, `h` with negative energy `∫ ½ (h² + |∇g|²) + V(g)` and `∫ g h > 0` has
`T ≤ 2 ∫ g² / ((Λ - 2) ∫ g h)`. -/
theorem lifespan_le_of_compact_negative_energy {u : ℝ^(n + 1) → ℝ} {T : ℝ} (hV : ContDiff ℝ 2 V)
    (hVzero : V 0 = 0) (hΛ : 2 < Λ) (hgrowth : ∀ z, z * deriv V z ≤ Λ * V z)
    (hgc : HasCompactSupport g) (hhc : HasCompactSupport h)
    (henergy :
      (∫ x : ℝ^n, (1 / 2 : ℝ) * ((h x) ^ 2 + ∑ i : Fin n, ((∂[i] g) x) ^ 2) + V (g x)) < 0)
    (hmomentum : 0 < ∫ x : ℝ^n, g x * h x) (hu : IsSolutionBefore (deriv V) g h T u) :
    T ≤ 2 * (∫ x : ℝ^n, g x ^ 2) / ((Λ - 2) * ∫ x : ℝ^n, g x * h x) := by
  refine le_of_forall_lt_imp_le_of_dense fun S hST ↦ ?_
  rcases le_or_gt S 0 with hS | hS
  · exact hS.trans (div_nonneg (mul_nonneg zero_le_two (integral_nonneg fun x ↦ sq_nonneg _))
      (mul_nonneg (by linarith) hmomentum.le))
  obtain ⟨R, hR, hgR, hhR⟩ := hgc.exists_common_radius hhc
  have hV₁ : ContDiff ℝ 1 V := hV.of_le (by norm_num)
  have hV' : ContDiff ℝ 1 (deriv V) := hV.deriv'
  obtain ⟨U, hU, hUsupp, hgerm, hU0, hUt⟩ := hu.exists_compact_representative hV'.locallyLipschitz
    (deriv_potential_zero_of_growth hV hVzero hΛ hgrowth) hgR hhR hR hS hST
  have hUs (r : ℝ) (_ : -1 < r) (x : ℝ^n) (hx : R + S + 2 + r < ‖x‖) :
      U (timeSpaceCons r x) = 0 := hUsupp r x (by linarith)
  have hUx (i : Fin n) (x : ℝ^n) : (∂[i.succ] U) (timeSpaceCons 0 x) = (∂[i] g) x := by
    rw [← PDE.partialDeriv_timeSpaceCons_spatial i U 0 x (hU.differentiable (by norm_num) _)]
    exact congrArg (fun f ↦ (∂[i] f) x) (funext hU0)
  have hmass : waveSpatialQuadraticMass U 0 = 1 / 2 * ∫ x : ℝ^n, g x ^ 2 := by
    simp only [waveSpatialQuadraticMass, hU0, integral_const_mul]
  have hmom : waveSpatialQuadraticMomentum U 0 = ∫ x : ℝ^n, g x * h x := by
    simp only [waveSpatialQuadraticMomentum, waveSpatialQuadraticMomentumDensity, hU0, hUt]
  have henergy0 : semilinearWaveSpatialEnergy V U 0 =
      ∫ x : ℝ^n, (1 / 2 : ℝ) * ((h x) ^ 2 + ∑ i : Fin n, ((∂[i] g) x) ^ 2) + V (g x) := by
    simp only [semilinearWaveSpatialEnergy, semilinearWaveSpatialEnergyDensity,
      semilinearWaveEnergyDensity, classicalWaveEnergyDensity, EuclideanSpace.real_norm_sq_eq,
      classicalWaveSpatialGradient_apply, hU0, hUt, hUx]
  -- The equation for `U` on `[0, S)`, at time zero by continuity.
  have hUwave (t : ℝ) (ht : t ∈ Ico 0 S) (x : ℝ^n) :
      semilinearWaveOperator V U (timeSpaceCons t x) = 0 :=
    waveOperator_add_eq_zero_of_mem_Icc hV'.continuous hU hS (fun r hr ↦ by
      rw [waveOperator_congr_nhds (hgerm r hr x), (hgerm r hr x).eq_of_nhds,
        hu.equation _ (by simpa using And.intro hr.1.le (hr.2.trans hST)), neg_add_cancel])
      ⟨ht.1, ht.2.le⟩
  -- Domination, conservation of the energy and the Riccati horizon.
  have hsub : Ico 0 S ⊆ Ioi (-1 : ℝ) := fun t ht ↦ lt_of_lt_of_le (by norm_num) ht.1
  have hconserved (t : ℝ) (ht : t ∈ Ico 0 S) :
      semilinearWaveSpatialEnergy V U t = semilinearWaveSpatialEnergy V U 0 := by
    have hsubset : uIcc 0 t ⊆ Ico 0 S := by
      rw [uIcc_of_le ht.1]
      exact fun r hr ↦ ⟨hr.1, hr.2.trans_lt ht.2⟩
    let E := (dominatedEnergyDataOfConeSupport hV₁ hVzero hU hUs).mono (hsubset.trans hsub)
    exact (semilinearWaveSpatialEnergy_eq_of_wave_on_uIcc hV₁
      (fun _ _ ↦ Eventually.of_forall fun _ _ ↦ hU.contDiffAt) (fun r hr ↦ hUwave r (hsubset hr))
      E.energy_integrable E.mem_nhds E.dominated E.bound_integrable E.flux_compact_support).symm
  have hfinal := right_endpoint_le_riccati_horizon_of_negative_conserved_energy hVzero hV₁
    (fun _ _ ↦ Eventually.of_forall fun _ _ ↦ hU.contDiffAt) hΛ hS hgrowth hUwave
    ((dominatedVirialDataOfConeSupport hU hUs).mono hsub) hconserved (henergy0.trans_lt henergy)
    (hmomentum.trans_eq hmom.symm)
  rw [hmass, hmom, zero_add] at hfinal
  refine hfinal.trans (le_of_eq ?_)
  cas using [hmomentum.ne', (sub_pos.mpr hΛ).ne']

end WaveEquation.NegativeEnergy
