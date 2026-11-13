/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.SecondDifference
public import PDE.Hyperbolic.HamiltonJacobi.HopfLax.Semiconcavity.Velocity

/-!
# Spatial semiconcavity of the multidimensional Hopf–Lax value

The Hopf–Lax value preserves any spatial semiconcavity constant of
the initial datum: translating the minimizing footpoint by the spatial
displacement keeps its velocity and Lagrangian cost unchanged.

For a twice continuously differentiable superlinear Lagrangian,
`value L g t` satisfies a spatial second-difference bound `C * ‖z‖² / t` for
every Lipschitz datum, including unbounded data. The constant depends only on
the Lagrangian and the Lipschitz constant.

Superlinearity bounds all minimizing velocities. The Hessian is bounded on
a slightly larger compact ball. For `‖z‖ ≤ t`, keep the minimizing footpoint
fixed and use the velocities `q ± z / t`. For larger displacements, spatial
Lipschitz continuity gives the same form of bound.

Preservation is Lemma 3 of Evans, §3.3.3(a). The regularization theorem follows the proof of
Lemma 4 there, with a bound on the Hessian of `L` on a compact ball in place of the estimate (37),
which in Evans comes from the uniform convexity of `H`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.3.3(a), Lemmas 3 and 4.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace HamiltonJacobi.HopfLax

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Hopf–Lax evolution preserves the initial datum's spatial semiconcavity
constant. This uses continuous superlinear costs and attained minimizers;
the datum need not be bounded. -/
theorem second_difference_value_le_of_initial_semiconcavity [ProperSpace E] {L g : E → ℝ}
    (hcont : Continuous L) (hL : Superlinear L) {K : NNReal} (hg : LipschitzWith K g) {C : ℝ}
    (hsemi : ∀ x z, g (x + z) - 2 * g x + g (x - z) ≤ C * ‖z‖ ^ 2) {t : ℝ} (ht : 0 ≤ t) (x z : E) :
    value L g t (x + z) - 2 * value L g t x + value L g t (x - z) ≤ C * ‖z‖ ^ 2 := by
  rcases ht.eq_or_lt with rfl | ht
  · simpa only [value_zero] using hsemi x z
  obtain ⟨q, hq, _⟩ := exists_minimizer hcont hL hg ht x
  have hp := value_le_cost hL hg ht.le (x + z) q
  have hm := value_le_cost hL hg ht.le (x - z) q
  have hplus : x + z - t • q = (x - t • q) + z := by abel
  have hminus : x - z - t • q = (x - t • q) - z := by abel
  simp only [cost, hplus] at hp
  simp only [cost, hminus] at hm
  rw [hq]
  dsimp only [cost]
  linarith [hsemi (x - t • q) z]

/-- Keeping an attained minimizing footpoint fixed compares the spatial second
difference with the second difference of the Lagrangian at its minimizing velocity. -/
theorem second_difference_value_le_at_minimizer {L g : E → ℝ}
    (hL : Superlinear L) {K : NNReal} (hg : LipschitzWith K g)
    {t : ℝ} (ht : 0 < t) {x q : E} (hq : value L g t x = cost L g t x q) (z : E) :
    value L g t (x + z) - 2 * value L g t x + value L g t (x - z) ≤
      t * (L (q + t⁻¹ • z) - 2 * L q + L (q - t⁻¹ • z)) := by
  have hp := value_le_cost hL hg ht.le (x + z) (q + t⁻¹ • z)
  have hm := value_le_cost hL hg ht.le (x - z) (q - t⁻¹ • z)
  have hplus : x + z - t • (q + t⁻¹ • z) = x - t • q := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
    abel
  have hminus : x - z - t • (q - t⁻¹ • z) = x - t • q := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
    abel
  simp only [cost, hplus] at hp
  simp only [cost, hminus] at hm
  rw [hq]
  dsimp only [cost]
  nlinarith

/-- A local Hessian bound suffices for spatial displacements of size at most `t`,
provided the minimizing velocity lies in the smaller ball. -/
theorem second_difference_value_le_of_hessian_bound {L g : E → ℝ} (hL : Superlinear L)
    (hsmooth : ContDiff ℝ 2 L) {K : NNReal} (hg : LipschitzWith K g) {R M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ p ∈ Metric.closedBall (0 : E) (R + 1), ‖fderiv ℝ (fderiv ℝ L) p‖ ≤ M) {t : ℝ}
    (ht : 0 < t) {x q z : E} (hq : value L g t x = cost L g t x q) (hR : ‖q‖ ≤ R) (hz : ‖z‖ ≤ t) :
    value L g t (x + z) - 2 * value L g t x + value L g t (x - z) ≤ (2 * M / t) * ‖z‖ ^ 2 := by
  have hnorm : ‖t⁻¹ • z‖ = ‖z‖ / t := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht, div_eq_inv_mul]
  have hsmall : ‖t⁻¹ • z‖ ≤ 1 := by
    rw [hnorm, div_le_one ht]
    exact hz
  have hqmem : q ∈ Metric.closedBall (0 : E) (R + 1) := by
    simp only [Metric.mem_closedBall, dist_zero_right]
    linarith
  have hp : q + t⁻¹ • z ∈ Metric.closedBall (0 : E) (R + 1) := by
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact (norm_add_le _ _).trans (add_le_add hR hsmall)
  have hm : q - t⁻¹ • z ∈ Metric.closedBall (0 : E) (R + 1) := by
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact (norm_sub_le _ _).trans (add_le_add hR hsmall)
  have hdf : ContDiff ℝ 1 (fderiv ℝ L) := hsmooth.fderiv_right (by norm_num)
  have hsecond := PDE.Analysis.second_difference_le_of_hessian_bound hM
    (convex_closedBall (0 : E) (R + 1)) (hsmooth.differentiable (by norm_num))
    hdf.differentiable_one hbound hqmem hp hm
  calc
    value L g t (x + z) - 2 * value L g t x + value L g t (x - z) ≤
        t * (L (q + t⁻¹ • z) - 2 * L q + L (q - t⁻¹ • z)) :=
      second_difference_value_le_at_minimizer hL hg ht hq z
    _ ≤ t * (2 * M * ‖t⁻¹ • z‖ ^ 2) := mul_le_mul_of_nonneg_left hsecond ht.le
    _ = (2 * M / t) * ‖z‖ ^ 2 := by
      rw [hnorm]
      field_simp

/-- At positive time, a `C²` superlinear Lagrangian regularizes every
`K`-Lipschitz datum to a spatially semiconcave function. The same constant works
for all such data, every spatial point, and every positive time. -/
theorem exists_semiconcavity_constant [ProperSpace E] {L : E → ℝ}
    (hL : Superlinear L) (hsmooth : ContDiff ℝ 2 L) (K : NNReal) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : E → ℝ), LipschitzWith K g → ∀ (t : ℝ), 0 < t → ∀ x z,
      value L g t (x + z) - 2 * value L g t x + value L g t (x - z) ≤ (C / t) * ‖z‖ ^ 2 := by
  obtain ⟨R, _, hR⟩ := exists_minimizing_velocity_bound hL K
  obtain ⟨M, hM, hbound⟩ := PDE.Analysis.exists_hessian_bound_closedBall hsmooth (R + 1)
  let C : ℝ := 2 * M + 2 * (K : ℝ) + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  have hMC : 2 * M ≤ C :=
    (le_add_of_nonneg_right (show 0 ≤ 2 * (K : ℝ) by positivity)).trans
      (le_add_of_nonneg_right zero_le_one)
  have hKC : 2 * (K : ℝ) ≤ C := by dsimp only [C]; linarith
  refine ⟨C, hC, fun g hg t ht x z ↦ ?_⟩
  by_cases hz : ‖z‖ ≤ t
  · obtain ⟨q, hq, _⟩ := exists_minimizer hsmooth.continuous hL hg ht x
    exact (second_difference_value_le_of_hessian_bound hL hsmooth hg hM hbound
      ht hq (hR g hg t ht x q hq) hz).trans
      (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hMC ht.le) (sq_nonneg _))
  · have hspatial := lipschitzWith_value hL hg ht.le
    have hp := hspatial.dist_le_mul (x + z) x
    have hm := hspatial.dist_le_mul (x - z) x
    have hsub : x - z - x = -z := by abel
    simp only [dist_eq_norm, add_sub_cancel_left] at hp
    simp only [dist_eq_norm, hsub, norm_neg] at hm
    have hlinear : value L g t (x + z) - 2 * value L g t x + value L g t (x - z) ≤
          2 * (K : ℝ) * ‖z‖ := by
      linarith [(le_abs_self _).trans hp, (le_abs_self _).trans hm]
    have htz : t ≤ ‖z‖ := (lt_of_not_ge hz).le
    have hquadratic : ‖z‖ ≤ ‖z‖ ^ 2 / t := by
      rw [le_div_iff₀ ht]
      nlinarith [norm_nonneg z]
    calc
      value L g t (x + z) - 2 * value L g t x + value L g t (x - z) ≤ 2 * (K : ℝ) * ‖z‖ := hlinear
      _ ≤ C * ‖z‖ := mul_le_mul_of_nonneg_right hKC (norm_nonneg z)
      _ ≤ C * (‖z‖ ^ 2 / t) := mul_le_mul_of_nonneg_left hquadratic hC.le
      _ = (C / t) * ‖z‖ ^ 2 := by ring

end HamiltonJacobi.HopfLax
