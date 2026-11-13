/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-!
# Finite families of normalized bumps with independent weighted moments

For a finite index type `ι`, let `W : ℝ → ι → ℝ` be continuous. If its
values at centers in an open set form the columns of a nonsingular square
matrix, normalized smooth bumps with disjoint compact supports in that
set have a nonsingular matrix of actual weighted integrals.

Shrinking normalized convolutions give entrywise convergence to the
point-evaluation matrix. Determinant continuity and finite conjunctions
select one stage with nonzero determinant and the required supports.
A separate surjectivity theorem realizes every signed target vector using
any fixed family whose weighted products are integrable and whose moment
matrix is nonsingular. Empty index types are allowed throughout.
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory Metric Set
open scoped BigOperators ContDiff Convolution Matrix Topology

namespace PDE.Analysis

/-- Rows index the weight coordinates and columns index the bumps.
Each entry is a Lebesgue integral; finiteness is not needed to define it. -/
def bumpMomentMatrix {ι : Type*} (W : ℝ → ι → ℝ) (β : ι → ℝ → ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j ↦ ∫ t, β j t * W t i

/-- Matrix multiplication gives the weighted integrals of a signed bump
combination. Integrability permits the finite sum to pass through the integral. -/
theorem bumpMomentMatrix_mulVec_eq_integral {ι : Type*} [Fintype ι]
    (W : ℝ → ι → ℝ) (β : ι → ℝ → ℝ)
    (hβ : ∀ j i, Integrable (fun t ↦ β j t * W t i))
    (c : ι → ℝ) (i : ι) :
    (bumpMomentMatrix W β *ᵥ c) i =
      ∫ t, (∑ j, c j * β j t) * W t i := by
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum Finset.univ (fun j _ ↦ (hβ j i).const_mul (c j))]
  simp [bumpMomentMatrix, Matrix.mulVec, dotProduct, integral_const_mul, mul_comm]

/-- For a fixed family, a nonzero moment determinant makes its actual
weighted-integral map surjective. The coefficients may have either sign;
smoothness and support restrictions are supplied separately by the construction. -/
theorem surjective_integral_sum_mul_of_bumpMomentMatrix_det_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : ℝ → ι → ℝ) (β : ι → ℝ → ℝ)
    (hβ : ∀ j i, Integrable (fun t ↦ β j t * W t i))
    (hdet : (bumpMomentMatrix W β).det ≠ 0) :
    Function.Surjective (fun c : ι → ℝ ↦ fun i : ι ↦
      ∫ t, (∑ j, c j * β j t) * W t i) := by
  have hsurj : Function.Surjective (bumpMomentMatrix W β).mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet))
  intro v
  obtain ⟨c, hc⟩ := hsurj v
  refine ⟨c, funext fun i ↦ ?_⟩
  change (∫ t, (∑ j, c j * β j t) * W t i) = v i
  rw [← bumpMomentMatrix_mulVec_eq_integral W β hβ c i, hc]

private def normalizedBumpAt (φ : ContDiffBump (0 : ℝ)) (x : ℝ) : ℝ → ℝ :=
  fun t ↦ φ.normed volume (x - t)

private theorem contDiff_normalizedBumpAt (φ : ContDiffBump (0 : ℝ)) (x : ℝ) :
    ContDiff ℝ ∞ (normalizedBumpAt φ x) :=
  φ.contDiff_normed.comp (contDiff_const.sub contDiff_id)

private theorem tsupport_normalizedBumpAt_subset (φ : ContDiffBump (0 : ℝ)) (x : ℝ) :
    tsupport (normalizedBumpAt φ x) ⊆ closedBall x φ.rOut := by
  apply closure_minimal _ isClosed_closedBall
  intro t ht
  have ht' : x - t ∈ Function.support (φ.normed volume) := ht
  rw [φ.support_normed_eq] at ht'
  have hnorm : ‖x - t‖ < φ.rOut := by
    simpa only [mem_ball, dist_zero_right] using ht'
  exact mem_closedBall.mpr (by simpa only [dist_eq_norm_sub'] using hnorm.le)

private theorem hasCompactSupport_normalizedBumpAt
    (φ : ContDiffBump (0 : ℝ)) (x : ℝ) : HasCompactSupport (normalizedBumpAt φ x) :=
  (isCompact_closedBall x φ.rOut).of_isClosed_subset
    (isClosed_tsupport _) (tsupport_normalizedBumpAt_subset φ x)

private theorem nonneg_normalizedBumpAt (φ : ContDiffBump (0 : ℝ)) (x t : ℝ) :
    0 ≤ normalizedBumpAt φ x t :=
  φ.nonneg_normed (x - t)

private theorem integral_normalizedBumpAt (φ : ContDiffBump (0 : ℝ)) (x : ℝ) :
    ∫ t, normalizedBumpAt φ x t = 1 := by
  change (∫ t, φ.normed volume (x - t)) = 1
  rw [integral_sub_left_eq_self (φ.normed volume) volume x]
  exact φ.integral_normed

private theorem integrable_normalizedBumpAt_mul
    (φ : ContDiffBump (0 : ℝ)) (x : ℝ) {w : ℝ → ℝ} (hw : Continuous w) :
    Integrable (fun t ↦ normalizedBumpAt φ x t * w t) :=
  ((contDiff_normalizedBumpAt φ x).continuous.mul hw).integrable_of_hasCompactSupport
    (hasCompactSupport_normalizedBumpAt φ x).mul_right

private theorem tendsto_integral_normalizedBumpAt_mul
    {φ : ℕ → ContDiffBump (0 : ℝ)}
    (hφ : Tendsto (fun n ↦ (φ n).rOut) atTop (𝓝 0))
    {w : ℝ → ℝ} (hw : Continuous w) (x : ℝ) :
    Tendsto (fun n ↦ ∫ t, normalizedBumpAt (φ n) x t * w t) atTop (𝓝 (w x)) := by
  simpa only [normalizedBumpAt, convolution_eq_swap,
    ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
    (ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume) hφ hw x)

private def shrinkingMomentBump (n : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := (1 / ((n : ℝ) + 1)) / 2
  rOut := 1 / ((n : ℝ) + 1)
  rIn_pos := half_pos (by positivity)
  rIn_lt_rOut := half_lt_self (by positivity)

private theorem tendsto_shrinkingMomentBump_rOut :
    Tendsto (fun n ↦ (shrinkingMomentBump n).rOut) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- Nonsingular evaluation at finitely many centers in an open set yields
nonnegative smooth unit-mass bumps with disjoint compact supports in that
set and a nonsingular matrix of actual weighted moments.

The family is chosen at one common stage. The evaluation determinant
itself forces distinct centers; no moment-rank assumption is required.
Apply `surjective_integral_sum_mul_of_bumpMomentMatrix_det_ne_zero` to the
returned family to obtain arbitrary signed target moments. -/
theorem exists_bumps_moment_matrix_det_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {W : ℝ → ι → ℝ} (hW : Continuous W)
    {U : Set ℝ} (hU : IsOpen U) (x : ι → ℝ) (hx : ∀ j, x j ∈ U)
    (hdet : (Matrix.of fun i j : ι ↦ W (x j) i).det ≠ 0) :
    ∃ β : ι → ℝ → ℝ,
      (∀ j, ContDiff ℝ ∞ (β j) ∧ HasCompactSupport (β j) ∧
        tsupport (β j) ⊆ U ∧ (∀ t, 0 ≤ β j t) ∧
        (∫ t, β j t) = 1 ∧ ∀ i, Integrable (fun t ↦ β j t * W t i)) ∧
      Pairwise (fun j k ↦ Disjoint (tsupport (β j)) (tsupport (β k))) ∧
      (bumpMomentMatrix W β).det ≠ 0 := by
  classical
  let β : ℕ → ι → ℝ → ℝ := fun n j ↦ normalizedBumpAt (shrinkingMomentBump n) (x j)
  have hφ := tendsto_shrinkingMomentBump_rOut
  have hlim : Tendsto (fun n ↦ bumpMomentMatrix W (β n)) atTop
      (𝓝 (Matrix.of fun i j : ι ↦ W (x j) i)) := by
    refine tendsto_pi_nhds.2 fun i ↦ tendsto_pi_nhds.2 fun j ↦ ?_
    exact tendsto_integral_normalizedBumpAt_mul hφ ((continuous_apply i).comp hW) (x j)
  have hdetlim : Tendsto (fun n ↦ (bumpMomentMatrix W (β n)).det) atTop
      (𝓝 (Matrix.of fun i j : ι ↦ W (x j) i).det) :=
    ((continuous_id : Continuous (fun A : Matrix ι ι ℝ ↦ A)).matrix_det.tendsto
      (Matrix.of fun i j : ι ↦ W (x j) i)).comp hlim
  have hdet_eventually : ∀ᶠ n in atTop, (bumpMomentMatrix W (β n)).det ≠ 0 :=
    hdetlim.eventually (eventually_ne_nhds hdet)
  have hinside : ∀ᶠ n in atTop, ∀ j, tsupport (β n j) ⊆ U := by
    apply eventually_all.2
    intro j
    obtain ⟨ε, hε, hball⟩ : ∃ ε, 0 < ε ∧ closedBall (x j) ε ⊆ U :=
      Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds (hx j))
    filter_upwards [hφ.eventually (Iio_mem_nhds hε)] with n hn
    exact (tsupport_normalizedBumpAt_subset (shrinkingMomentBump n) (x j)).trans
      ((closedBall_subset_closedBall hn.le).trans hball)
  have hinj : Function.Injective x := by
    intro j k hjk
    by_contra hne
    apply hdet
    apply Matrix.det_zero_of_column_eq hne
    intro i
    change W (x j) i = W (x k) i
    rw [hjk]
  have hsum : Tendsto
      (fun n ↦ (shrinkingMomentBump n).rOut + (shrinkingMomentBump n).rOut)
      atTop (𝓝 0) := by
    simpa only [zero_add] using hφ.add hφ
  have hdisjoint : ∀ᶠ n in atTop,
      Pairwise (fun j k ↦ Disjoint (tsupport (β n j)) (tsupport (β n k))) := by
    change ∀ᶠ n in atTop, ∀ j k, j ≠ k →
      Disjoint (tsupport (β n j)) (tsupport (β n k))
    apply eventually_all.2
    intro j
    apply eventually_all.2
    intro k
    by_cases hjk : j = k
    · exact Eventually.of_forall fun _ hne ↦ (hne hjk).elim
    · have hdist : 0 < dist (x j) (x k) := dist_pos.mpr (fun h ↦ hjk (hinj h))
      filter_upwards [hsum.eventually (Iio_mem_nhds hdist)] with n hn
      intro _
      exact (closedBall_disjoint_closedBall hn).mono
        (tsupport_normalizedBumpAt_subset (shrinkingMomentBump n) (x j))
        (tsupport_normalizedBumpAt_subset (shrinkingMomentBump n) (x k))
  obtain ⟨n, hn_inside, hn_disjoint, hn_det⟩ :=
    (hinside.and (hdisjoint.and hdet_eventually)).exists
  refine ⟨β n, ?_, hn_disjoint, hn_det⟩
  intro j
  exact ⟨contDiff_normalizedBumpAt (shrinkingMomentBump n) (x j),
    hasCompactSupport_normalizedBumpAt (shrinkingMomentBump n) (x j), hn_inside j,
    nonneg_normalizedBumpAt (shrinkingMomentBump n) (x j),
    integral_normalizedBumpAt (shrinkingMomentBump n) (x j),
    fun i ↦ integrable_normalizedBumpAt_mul (shrinkingMomentBump n) (x j)
      ((continuous_apply i).comp hW)⟩

end PDE.Analysis
