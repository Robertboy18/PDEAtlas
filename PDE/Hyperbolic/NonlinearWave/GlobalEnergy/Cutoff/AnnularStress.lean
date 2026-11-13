/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.Cutoff.Balance
public import PDE.Spaces.Sobolev.Approximation.Mollification.SobolevApproximation.Cutoff
import PDE.Hyperbolic.NonlinearWave.Momentum.Estimates
import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.Cutoff.CompactSlices
import PDE.Spaces.Sobolev.Approximation.Mollification.SobolevApproximation.Cutoff.DerivativeSupport

/-!
# Wave stress on the cutoff annulus

For the cutoff `χ_R`, equal to one on the ball of radius `R` and supported in the ball
of radius `2 R`, only the annulus `R ≤ |x| ≤ 2 R` contributes to the stress paired with
the Hessian of `χ_R`. For large `R`, the energy difference between two times is a
time-weighted integral of this stress.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE PDE.Common PDE.Analysis SobolevSpace.Approximation

namespace WaveEquation

/-- The rescaled cutoff is the Mathlib bump function with radii `R` and `2 R`. -/
private theorem cutoff_eq_bump {n : ℕ} {R : ℝ} (hR : 0 < R) :
    cutoff (n := n) R =
      (⟨R, 2 * R, hR, by linarith⟩ : ContDiffBump (0 : ℝ^n)) := by
  funext x
  simp [cutoff, ContDiffBump.apply, standardBump, hR.ne']

/-- For `0 ≤ s ≤ t` there is a radius `R₀` such that for every `R ≥ R₀` the spatial energy
at time `t` minus that at time `s` equals `∫ r in s..t, (t - r) * cutoffStress (cutoff R) V u r`.
-/
theorem exists_radius_energy_sub_eq_scaledCutoffStress {n : ℕ} [Fact (0 < n)] {V : ℝ → ℝ}
    {u : ℝ^(n + 1) → ℝ} (hV : ContDiff ℝ 1 V) (hVzero : V 0 = 0) (hu : ContDiff ℝ 3 u)
    (hwave : ∀ r, 0 < r → ∀ x, semilinearWaveOperator V u (timeSpaceCons r x) = 0)
    (hs : ∀ r, 0 ≤ r → HasCompactSupport (fun x : ℝ^n ↦ u (timeSpaceCons r x))) {s t : ℝ}
    (hs0 : 0 ≤ s) (hst : s ≤ t) :
    ∃ R₀ > 0, ∀ R, R₀ ≤ R → semilinearWaveSpatialEnergy V u t - semilinearWaveSpatialEnergy V u s =
      ∫ r in s..t, (t - r) * cutoffStress (cutoff R) V u r := by
  obtain ⟨R₀, hR₀, hcap⟩ := exists_radius_energy_sub_eq_timeWeightedStress
    hV hVzero hu hwave hs hs0 hst
  refine ⟨R₀, hR₀, fun R hR ↦ ?_⟩
  rw [cutoff_eq_bump (hR₀.trans_le hR)]
  exact hcap _ hR

/-- Let `A` be the annulus `R ≤ |x| ≤ 2 R`. If `|∂ⱼ∂ᵢ (cutoff R)| ≤ c i j` and `|V(u)| ≤ M`
on `A` at time `r`, then the cutoff stress at time `r` is at most
`(∑ i, ∑ j, c i j) * (∫_A e + |A| * M)`, with `e` the classical wave energy density. -/
theorem norm_cutoffStress_le_annular {n : ℕ} {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ} {R M r : ℝ}
    (hu : ContDiff ℝ 2 u) (hR : 0 < R)
    (hpot : ∀ x ∈ Metric.closedBall (0 : ℝ^n) (2 * R) \ Metric.ball 0 R,
      |V (u (timeSpaceCons r x))| ≤ M)
    {c : Fin n → Fin n → ℝ} (hc : ∀ i j, 0 ≤ c i j)
    (hb : ∀ (i j : Fin n) (x : ℝ^n), |(∂[j] (∂[i] (cutoff R))) x| ≤ c i j) :
    ‖cutoffStress (cutoff R) V u r‖ ≤ (∑ i, ∑ j, c i j) *
      ((∫ x in Metric.closedBall (0 : ℝ^n) (2 * R) \ Metric.ball 0 R,
        classicalWaveEnergyDensity u (timeSpaceCons r x)) +
       volume.real (Metric.closedBall (0 : ℝ^n) (2 * R) \ Metric.ball 0 R) * M) := by
  classical
  let A := Metric.closedBall (0 : ℝ^n) (2 * R) \ Metric.ball 0 R
  let K := fun x : ℝ^n ↦ classicalWaveEnergyDensity u (timeSpaceCons r x)
  have hA : IsCompact A := (isCompact_closedBall _ _).diff Metric.isOpen_ball
  have hK : Continuous K := (contDiff_classicalWaveEnergyDensity (m := 1) hu).continuous.comp
    (contDiff_timeSpaceCons_spatial n r (m := 1)).continuous
  have hKi : IntegrableOn K A := hK.continuousOn.integrableOn_compact hA
  have hMi : IntegrableOn (fun _ : ℝ^n ↦ M) A := integrableOn_const hA.measure_ne_top
  have hentry (i j : Fin n) : ‖∫ x : ℝ^n, (∂[j] (∂[i] (cutoff R))) x *
        waveSpatialStress V u i j (timeSpaceCons r x)‖ ≤
      c i j * ((∫ x in A, K x) + volume.real A * M) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := A)
      (fun x hx ↦ by
        rw [partialDeriv_partialDeriv_cutoff_eq_zero_of_notMem_annulus hR i j hx, zero_mul])]
    have hmajor := MeasureTheory.norm_integral_le_of_norm_le ((hKi.add hMi).const_mul (c i j))
      (f := fun x : ℝ^n ↦ (∂[j] (∂[i] (cutoff R))) x *
        waveSpatialStress V u i j (timeSpaceCons r x))
      (by
        filter_upwards [ae_restrict_mem hA.measurableSet] with x hx
        rw [Real.norm_eq_abs, abs_mul]
        apply mul_le_mul (hb i j x) _ (abs_nonneg _) (hc i j)
        exact (abs_waveSpatialStress_le_energy_add_abs_potential V u i j _).trans
          (add_le_add le_rfl (hpot x hx)))
    simpa only [Pi.add_apply, integral_const_mul, integral_add hKi hMi,
      integral_const, smul_eq_mul, Measure.real, Measure.restrict_apply_univ] using hmajor
  unfold cutoffStress
  calc
    _ ≤ ∑ i : Fin n, ‖∑ j : Fin n, ∫ x : ℝ^n,
        (∂[j] (∂[i] (cutoff R))) x * waveSpatialStress V u i j (timeSpaceCons r x)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, c i j *
        ((∫ x in A, K x) + volume.real A * M) := by
      refine Finset.sum_le_sum fun i _ ↦ ?_
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ hentry i j)
    _ = _ := by simp only [Finset.sum_mul, A, K]

end WaveEquation
