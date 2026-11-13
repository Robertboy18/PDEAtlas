/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean

/-!
# Open rectangular neighborhoods

Every point of an open Euclidean set lies in an open coordinate box contained
in the set. Rectangles are used for local coordinate integration.
-/

@[expose] public noncomputable section

open Set Metric

namespace EuclideanSpace

/-- A coordinate box with open interval factors is open. -/
theorem isOpen_box {n : ℕ} (a b : Fin n → ℝ) :
    IsOpen {x : ℝ^n | ∀ i, x i ∈ Ioo (a i) (b i)} := by
  simpa only [ofPred_forall, EuclideanSpace.coe_proj, Set.preimage, Set.mem_Ioo] using
    isOpen_iInter_of_finite (fun i : Fin n ↦
      isOpen_Ioo.preimage (EuclideanSpace.proj i).continuous)

/-- Open coordinate boxes form a neighborhood basis in Euclidean space. -/
theorem exists_box_subset_of_mem_open {n : ℕ} {U : Set (ℝ^n)}
    (hU : IsOpen U) {x : ℝ^n} (hx : x ∈ U) :
    ∃ a b : Fin n → ℝ, (∀ i, a i < b i) ∧
      x ∈ {y : ℝ^n | ∀ i, y i ∈ Ioo (a i) (b i)} ∧
      {y : ℝ^n | ∀ i, y i ∈ Ioo (a i) (b i)} ⊆ U := by
  classical
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hU x hx
  let ε := r / ((n : ℝ) + 1)
  have hε : 0 < ε := div_pos hr (by positivity)
  refine ⟨fun i ↦ x i - ε, fun i ↦ x i + ε,
    fun i ↦ by linarith, fun i ↦ ⟨by linarith, by linarith⟩, ?_⟩
  intro y hy
  apply hsub
  rw [mem_ball, dist_eq_norm]
  have heq : y - x =
      ∑ i : Fin n, (y i - x i) • EuclideanSpace.single i (1 : ℝ) := by
    ext j
    simp [Pi.single_apply]
  calc
    ‖y - x‖ = ‖∑ i : Fin n, (y i - x i) • EuclideanSpace.single i (1 : ℝ)‖ :=
      congrArg norm heq
    _ ≤ ∑ i : Fin n, ‖(y i - x i) • EuclideanSpace.single i (1 : ℝ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, ε := by
      apply Finset.sum_le_sum
      intro i _
      have hi : |y i - x i| < ε :=
        abs_lt.mpr ⟨by linarith [(hy i).1], by linarith [(hy i).2]⟩
      simpa only [norm_smul, PiLp.norm_single, norm_one, mul_one,
        Real.norm_eq_abs] using hi.le
    _ = (n : ℝ) * ε := by simp
    _ < r := by
      have he : ε * ((n : ℝ) + 1) = r := div_mul_cancel₀ _ (by positivity)
      nlinarith

end EuclideanSpace
