/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.MeanValue.PDEToMeanValue
public import PDE.Analysis.Geometry.BallChain
public import PDE.Elliptic.Classical.MeanValue.Formulas

/-!
# Harnack inequalities for harmonic functions

We prove the Harnack inequalities from Evans, *Partial Differential
Equations*, second edition, §2.2.3, for nonnegative harmonic functions.

The local estimate compares `x` and `y` when `dist x y ≤ r` and `B̄(x, 2r)`
lies in the harmonicity domain. Ball mean values and monotonicity of the
integral give

`u(y) ≤ 2ⁿ u(x)`.

For a compact set `K` contained in an open preconnected domain `U`, overlapping
admissible balls use the geometric ball-chain theorem. Topological
preconnectedness gives finite paths, while compactness bounds their lengths
uniformly for points of `K`.  The resulting global constant is chosen before the harmonic
function, so it depends only on `n`, `K`, and `U`.

If the observation set is connected, only its component of `U` is needed.
This gives the supremum–infimum formulation on relatively compact connected
sets even when the ambient open set has several components.

The statements use `IsHarmonicPDE`. On the open domain of the global result
this is equivalent to Mathlib's `HarmonicOnNhd` by `IsHarmonicPDE.harmonicOnNhd`
and `HarmonicOnNhd.isHarmonicPDE`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.3, Theorem 11 (Harnack's inequality) and its proof,
  pp. 32-33.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace LaplacianEquation

open MeasureTheory PDE.Analysis Set
open scoped BigOperators

/-- Local Harnack inequality on a ball, following Evans §2.2.3.

If `u` is nonnegative and harmonic on a set containing `B̄(x, 2r)`, then
`dist x y ≤ r` implies `u(y) ≤ 2ⁿ u(x)`. No openness assumption on the ambient
set is needed because the closed-ball containment is explicit. -/
theorem IsHarmonicPDE.le_two_pow_mul_of_dist_le
    {n : ℕ} [Fact (0 < n)] {u : ℝ^n → ℝ} {U : Set (ℝ^n)}
    (hu : IsHarmonicPDE n u U)
    (hu_nonneg : ∀ z ∈ U, 0 ≤ u z)
    {x y : ℝ^n} {r : ℝ} (hr : 0 < r)
    (hxy : dist x y ≤ r)
    (hball : Metric.closedBall x (2 * r) ⊆ U) :
    u y ≤ (2 : ℝ) ^ n * u x := by
  have h2r : 0 < 2 * r := by positivity
  have hsmall_large : Metric.ball y r ⊆ Metric.ball x (2 * r) :=
    Metric.ball_subset_ball' (by rw [dist_comm]; linarith)
  have hsmall_closed : Metric.closedBall y r ⊆ U :=
    (Metric.closedBall_subset_closedBall' (by rw [dist_comm]; linarith)).trans hball
  have hu_int_large : IntegrableOn u (Metric.ball x (2 * r)) :=
    ((hu.contDiffOn.mono hball).continuousOn.integrableOn_compact
      (isCompact_closedBall x (2 * r))).mono_set Metric.ball_subset_closedBall
  have hmono : (∫ z in Metric.ball y r, u z) ≤ ∫ z in Metric.ball x (2 * r), u z := by
    refine setIntegral_mono_set hu_int_large ?_ (.of_forall fun z hz ↦ hsmall_large hz)
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    exact hu_nonneg z (hball (Metric.ball_subset_closedBall hz))
  have hmean_y : u y = (∫ z in Metric.ball y r, u z) / ballVolume n r := by
    simpa [ballAverage, ballIntegral, hr] using hu.hasSphereMeanValueProperty.eq_ballAverage
      y (hsmall_closed (Metric.mem_closedBall_self hr.le)) r hr hsmall_closed
      (hu_int_large.mono_set hsmall_large)
  have hmean_x : u x = (∫ z in Metric.ball x (2 * r), u z) / ballVolume n (2 * r) := by
    simpa [ballAverage, ballIntegral, h2r] using hu.hasSphereMeanValueProperty.eq_ballAverage
      x (hball (Metric.mem_closedBall_self h2r.le)) (2 * r) h2r hball hu_int_large
  have hvolume_r : 0 < ballVolume n r := by
    rw [ballVolume_eq_unitBallVolume_mul_pow n r hr.le]
    exact mul_pos (unitBallVolume_pos n) (pow_pos hr n)
  have hvolume_scale : ballVolume n (2 * r) = (2 : ℝ) ^ n * ballVolume n r := by
    rw [ballVolume_eq_unitBallVolume_mul_pow n (2 * r) h2r.le,
      ballVolume_eq_unitBallVolume_mul_pow n r hr.le, mul_pow]
    ring
  rw [hmean_y, hmean_x, hvolume_scale, mul_div_assoc', mul_div_mul_left _ _ (by positivity)]
  exact (div_le_div_iff_of_pos_right hvolume_r).2 hmono

/-- Uniform Harnack comparison on a compact subset of a connected domain.

This is the global compactly-contained form of Evans §2.2.3.  If `K` is a
compact subset of the open preconnected set `U`, there is a positive constant
`C`, chosen independently of `u`, such that every nonnegative PDE-harmonic
function on `U` satisfies `u(x) ≤ C u(y)` for `x, y ∈ K`. The set `K`
itself need not be connected because the comparison chains may travel
through `U`. -/
theorem IsHarmonicPDE.exists_harnack_constant_on_isCompact
    {n : ℕ} [Fact (0 < n)] {U K : Set (ℝ^n)}
    (hUopen : IsOpen U) (hUconn : IsPreconnected U)
    (hKcompact : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {u : ℝ^n → ℝ}, IsHarmonicPDE n u U →
        (∀ z ∈ U, 0 ≤ u z) →
        ∀ x ∈ K, ∀ y ∈ K, u x ≤ C * u y := by
  obtain ⟨C, hC, hcompare⟩ := exists_comparison_constant_of_ballChain
    hUopen hUconn hKcompact hKU (L := 2) (ρ := 1) (A := (2 : ℝ) ^ n)
    (by norm_num) zero_lt_one (one_le_pow₀ (by norm_num))
  refine ⟨C, hC, ?_⟩
  intro u hu hu_nonneg
  apply hcompare u hu_nonneg
  intro x y hxy
  obtain ⟨r, hr, _, hdist, _, hyball⟩ := hxy
  exact hu.le_two_pow_mul_of_dist_le hu_nonneg hr
    (by simpa only [dist_comm] using hdist) hyball

/-- Harnack comparison on a compact connected set inside any open domain.

All points of `K` lie in one connected component of `U`. That component is
open, so the compact-set comparison applies there. Other components of `U`
have no effect on the constant. -/
theorem IsHarmonicPDE.exists_harnack_constant_of_isPreconnected
    {n : ℕ} [Fact (0 < n)] {U K : Set (ℝ^n)}
    (hUopen : IsOpen U) (hKcompact : IsCompact K)
    (hKconn : IsPreconnected K) (hKU : K ⊆ U) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {u : ℝ^n → ℝ}, IsHarmonicPDE n u U →
        (∀ z ∈ U, 0 ≤ u z) →
        ∀ x ∈ K, ∀ y ∈ K, u x ≤ C * u y := by
  obtain rfl | ⟨x₀, hx₀⟩ := K.eq_empty_or_nonempty
  · exact ⟨1, zero_lt_one, by simp⟩
  have hcomponent := connectedComponentIn_subset U x₀
  obtain ⟨C, hC, hcompare⟩ := exists_harnack_constant_on_isCompact
    hUopen.connectedComponentIn isPreconnected_connectedComponentIn
    hKcompact (hKconn.subset_connectedComponentIn hx₀ hKU)
  exact ⟨C, hC, fun hu hnonneg ↦
    hcompare (hu.mono hcomponent) (fun z hz ↦ hnonneg z (hcomponent hz))⟩

/-- Harnack's supremum–infimum inequality on a relatively compact connected set.

The closure of `V` stays inside the harmonicity domain. A single constant,
chosen before `u`, compares its largest and smallest values on `V`; neither
extremum needs to be attained there. The open set `U` may be disconnected. -/
theorem IsHarmonicPDE.exists_harnack_constant_sup_le_mul_inf
    {n : ℕ} [Fact (0 < n)] {U V : Set (ℝ^n)}
    (hUopen : IsOpen U) (hVcompact : IsCompact (closure V))
    (hVconn : IsPreconnected V) (hVU : closure V ⊆ U) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {u : ℝ^n → ℝ}, IsHarmonicPDE n u U →
        (∀ z ∈ U, 0 ≤ u z) →
        sSup (u '' V) ≤ C * sInf (u '' V) := by
  obtain ⟨C, hC, hcompare⟩ := exists_harnack_constant_of_isPreconnected
    hUopen hVcompact hVconn.closure hVU
  refine ⟨C, hC, ?_⟩
  intro u hu hnonneg
  obtain rfl | hV := V.eq_empty_or_nonempty
  · simp
  apply csSup_le (hV.image u)
  rintro _ ⟨x, hx, rfl⟩
  rw [mul_comm C, ← div_le_iff₀ hC]
  apply le_csInf (hV.image u)
  rintro _ ⟨y, hy, rfl⟩
  rw [div_le_iff₀ hC, mul_comm]
  exact hcompare hu hnonneg x (subset_closure hx) y (subset_closure hy)

end LaplacianEquation
