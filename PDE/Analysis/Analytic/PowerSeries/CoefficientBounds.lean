/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Analytic.PowerSeries.Multiindex

/-!
# Exponential bounds for analytic coordinate coefficients

Native positive-radius multilinear expansions give exponential bounds on their
commutative coordinate coefficients. The extra factor counting coordinate words
is absorbed in the exponential base, including an empty coordinate type.
-/

@[expose] public section

open scoped BigOperators

namespace FormalMultilinearSeries

variable {ι G : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A single commutative coefficient is bounded by the sum of the coordinate-word norms. -/
theorem norm_multiindexCoeff_le (p : FormalMultilinearSeries ℝ (ι → ℝ) G) (a : ι →₀ ℕ) :
    ‖p.multiindexCoeff a‖ ≤
      (Fintype.card ι : ℝ) ^ (a.sum fun _ ↦ id) * ‖p (a.sum fun _ ↦ id)‖ := by
  classical
  apply le_trans _ (ContinuousMultilinearMap.sum_norm_symCoefficient_le
    (p (a.sum fun _ ↦ id)))
  exact Finset.single_le_sum
    (f := fun s ↦ ‖(p (a.sum fun _ ↦ id)).symCoefficient s‖)
    (fun s hs ↦ norm_nonneg _) (Finset.mem_univ _)

/-- A positive native convergence radius supplies exponential coefficient bounds;
no independent convergence or majorant hypothesis is required. -/
theorem exists_pos_multiindexCoeff_bound (p : FormalMultilinearSeries ℝ (ι → ℝ) G)
    (hp : 0 < p.radius) :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ ∀ a, ‖p.multiindexCoeff a‖ ≤ C * r ^ (a.sum fun _ ↦ id) := by
  obtain ⟨C, r, hC, hr, hbound⟩ := p.le_mul_pow_of_radius_pos hp
  let N : ℝ := Fintype.card ι + 1
  have hN : 0 < N := by positivity
  refine ⟨C, N * r, hC, mul_pos hN hr, ?_⟩
  intro a
  calc
    ‖p.multiindexCoeff a‖ ≤
        (Fintype.card ι : ℝ) ^ (a.sum fun _ ↦ id) * ‖p (a.sum fun _ ↦ id)‖ :=
      p.norm_multiindexCoeff_le a
    _ ≤ N ^ (a.sum fun _ ↦ id) * ‖p (a.sum fun _ ↦ id)‖ := by
      gcongr
      simp [N]
    _ ≤ N ^ (a.sum fun _ ↦ id) * (C * r ^ (a.sum fun _ ↦ id)) :=
      mul_le_mul_of_nonneg_left (hbound _) (pow_nonneg hN.le _)
    _ = C * (N * r) ^ (a.sum fun _ ↦ id) := by rw [mul_pow]; ring

end FormalMultilinearSeries
