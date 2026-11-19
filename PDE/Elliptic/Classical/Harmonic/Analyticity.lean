/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.TaylorSeries
public import PDE.Elliptic.Classical.Harmonic.IteratedDerivativeEstimates

/-!
# Real analyticity of harmonic functions

Every classical harmonic function on an open subset of positive-dimensional Euclidean
space is real analytic. This is the analyticity theorem in Evans, *Partial Differential
Equations*, second edition, §2.2.3.

The interior derivative estimates imply `‖Dᵏu(x)‖ ≤ k! M (e n/R)ᵏ` when `|u| ≤ M` on the
closed ball of radius `R`. Compactness supplies such a bound on a larger ball, uniformly
for centers in a smaller ball. The factorial criterion in
`PDE.Analysis.Calculus.TaylorSeries` then proves convergence to the original function.
Smoothness and all derivative bounds follow from the original `C²` harmonicity hypothesis.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.3, Theorem 10 (Analyticity) and its proof, (22)-(23),
  pp. 31-32.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open Filter Metric Set
open scoped Topology ContDiff NNReal ENNReal

noncomputable section

namespace LaplacianEquation

/-- A factorial form of the interior derivative estimate. A bound `|u| ≤ M` on a closed
ball of radius `R` gives `‖Dᵏu(x)‖ ≤ k! M (e n/R)ᵏ` at its center. -/
theorem IsHarmonicPDE.norm_iteratedFDeriv_le_factorial
    {n : ℕ} [Fact (0 < n)] {u : ℝ^n → ℝ} {U : Set (ℝ^n)}
    (hu : IsHarmonicPDE n u U) (hU : IsOpen U)
    {x : ℝ^n} {R M : ℝ} (hR : 0 < R)
    (hball : closedBall x R ⊆ U)
    (hM : ∀ y ∈ closedBall x R, |u y| ≤ M) (k : ℕ) :
    ‖iteratedFDeriv ℝ k u x‖ ≤
      (k.factorial : ℝ) * M * (Real.exp 1 * (n : ℝ) / R) ^ k := by
  have hM0 : 0 ≤ M :=
    (abs_nonneg _).trans (hM x (mem_closedBall_self hR.le))
  obtain rfl | hk := k.eq_zero_or_pos
  · simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, Nat.factorial_zero,
      Nat.cast_one, one_mul, pow_zero, mul_one] using
      hM x (mem_closedBall_self hR.le)
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  have hbudget : (k : ℝ) * (R / k) = R := by field_simp [hk'.ne']
  have hderiv : ‖iteratedFDeriv ℝ k u x‖ ≤ (n : ℝ) ^ k * M / (R / k) ^ k :=
    hu.norm_iteratedFDeriv_le hU (div_pos hR hk')
      (by simpa only [hbudget] using hball)
      (by simpa only [hbudget] using hM)
  have hfactorial : (k : ℝ) ^ k ≤ (k.factorial : ℝ) * (Real.exp 1) ^ k := by
    have h := (div_le_iff₀ (by positivity : (0 : ℝ) < k.factorial)).mp
      (Real.pow_div_factorial_le_exp (k : ℝ) (Nat.cast_nonneg k) k)
    calc
      (k : ℝ) ^ k ≤ Real.exp (k : ℝ) * k.factorial := h
      _ = (k.factorial : ℝ) * (Real.exp 1) ^ k := by
        rw [← Real.exp_nat_mul, mul_one, mul_comm]
  calc
    ‖iteratedFDeriv ℝ k u x‖ ≤ (n : ℝ) ^ k * M / (R / k) ^ k := hderiv
    _ = M * ((n : ℝ) / R) ^ k * (k : ℝ) ^ k := by
      rw [div_pow, div_pow]
      field_simp [hk'.ne', hR.ne']
    _ ≤ M * ((n : ℝ) / R) ^ k * ((k.factorial : ℝ) * (Real.exp 1) ^ k) :=
      mul_le_mul_of_nonneg_left hfactorial (by positivity)
    _ = (k.factorial : ℝ) * M * (Real.exp 1 * (n : ℝ) / R) ^ k := by
      rw [mul_div_assoc, mul_pow]
      ring

/-- Every classical harmonic function on an open subset of positive-dimensional Euclidean
space is real analytic there. Smoothness, factorial derivative bounds, and convergence
of the Taylor series are all consequences of the original `C²` harmonicity hypothesis. -/
theorem IsHarmonicPDE.analyticOnNhd
    {n : ℕ} [Fact (0 < n)] {u : ℝ^n → ℝ} {U : Set (ℝ^n)}
    (hu : IsHarmonicPDE n u U) (hU : IsOpen U) :
    AnalyticOnNhd ℝ u U := by
  intro x hx
  obtain ⟨ε, hε, hεball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  let R : ℝ := ε / 4
  have hR : 0 < R := by dsimp [R]; positivity
  have hclosed : closedBall x (2 * R) ⊆ U :=
    (closedBall_subset_ball (by dsimp [R]; linarith)).trans hεball
  obtain ⟨M, hM⟩ := (isCompact_closedBall x (2 * R)).exists_bound_of_continuousOn
    (hu.contDiffOn.continuousOn.mono hclosed)
  have hM0 : 0 ≤ M :=
    (norm_nonneg _).trans (hM x (mem_closedBall_self (by positivity)))
  let K : ℝ := Real.exp 1 * (n : ℝ) / R
  have hn : 0 < (n : ℝ) := by exact_mod_cast (Fact.out : 0 < n)
  have hK : 0 < K := by dsimp [K]; positivity
  let r : ℝ≥0 := ⟨min R K⁻¹, (lt_min hR (inv_pos.mpr hK)).le⟩
  have hr : 0 < r := lt_min hR (inv_pos.mpr hK)
  have hrR : (r : ℝ) ≤ R := min_le_left _ _
  have hKr : K * r ≤ 1 := by
    calc
      K * r ≤ K * K⁻¹ := mul_le_mul_of_nonneg_left (min_le_right _ _) hK.le
      _ = 1 := mul_inv_cancel₀ hK.ne'
  have hsmall (y : ℝ^n) (hy : y ∈ ball x (r : ℝ)) :
      closedBall y R ⊆ closedBall x (2 * R) := by
    apply closedBall_subset_closedBall'
    have := (mem_ball.mp hy).le.trans hrR
    linarith
  have hinner : ball x (r : ℝ) ⊆ U := by
    intro y hy
    exact hclosed (hsmall y hy (mem_closedBall_self hR.le))
  have hsmooth : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) u (ball x (r : ℝ)) :=
    (hu.contDiffOn_of_isOpen hU (m := ⊤)).mono hinner
  refine ⟨_, r, hsmooth.hasFPowerSeriesOnBall_of_iteratedFDeriv_bound
    hr hM0 hK hKr ?_⟩
  intro k y hy
  exact hu.norm_iteratedFDeriv_le_factorial hU hR ((hsmall y hy).trans hclosed)
    (fun z hz ↦ by simpa only [Real.norm_eq_abs] using hM z (hsmall y hy hz)) k

end LaplacianEquation
