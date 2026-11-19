/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Jet.NormalTaylor
public import PDE.Analysis.Calculus.LocalExtension.Cutoff.QuadraticError
public import PDE.Analysis.Calculus.LocalExtension.Logarithmic.Pullback

/-!
# A uniform estimate for the actual normal cutoff product

The Taylor and coordinate bounds are fixed before either cutoff parameter.
The value and first derivative become small with the outer radius. The Hessian
stays close to the prescribed quadratic part, with error controlled separately
by the outer radius and the inverse logarithmic width.

The coordinate map is explicit. Its norm must agree with the distance to the
chosen base point; a curve chart supplies that identity in the application.
This theorem estimates the local product. Compact support and extension across
the chart boundary are separate geometric steps.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace PDE.Analysis

variable {D E F : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A fixed positive constant controls the actual radial cutoff product and its
first two derivatives, uniformly in both cutoff parameters. The quadratic jet
can be large: only the error relative to its cutoff multiple is small.

The closed normal segment may have zero length. The derivative bounds on the
coordinate map and the third derivative bound on `Q` are independent of `δ,L`;
no global regularity, completeness or finite-dimensionality is required. -/
theorem exists_pos_radial_cutoff_product_bounds
    {M K A B : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ L : ℝ), 0 < δ → δ ≤ 1 → 1 ≤ L →
      ∀ (z : D → E) (Q : D → F) (base x : D),
      ContDiffAt ℝ 2 z x →
      ‖fderiv ℝ z x‖ ≤ A → ‖fderiv ℝ (fderiv ℝ z) x‖ ≤ B →
      ‖z x‖ = ‖x - base‖ → ‖x - base‖ ≤ δ →
      (∀ y ∈ segment ℝ base x, ContDiffAt ℝ 3 Q y) →
      (∀ y ∈ segment ℝ base x,
        ContinuousLinearMap.opNorm (𝕜 := ℝ) (𝕜₂ := ℝ) (E := D)
          (F := D →L[ℝ] D →L[ℝ] F) (fderiv ℝ (fderiv ℝ (fderiv ℝ Q)) y) ≤ K) →
      Q base = 0 → fderiv ℝ Q base = 0 →
      ‖fderiv ℝ (fderiv ℝ Q) base‖ ≤ M →
      ‖radialLogarithmicCutoff δ L (z x) • Q x‖ ≤ C * δ ^ 2 ∧
        ‖fderiv ℝ (fun y ↦ radialLogarithmicCutoff δ L (z y) • Q y) x‖ ≤ C * δ ∧
        ‖fderiv ℝ (fderiv ℝ
            (fun y ↦ radialLogarithmicCutoff δ L (z y) • Q y)) x -
          radialLogarithmicCutoff δ L (z x) • fderiv ℝ (fderiv ℝ Q) base‖ ≤
            C * δ + C / L := by
  obtain ⟨c, hc, hpullback⟩ :=
    exists_pos_radialLogarithmicCutoff_pullback_bounds (D := D) (E := E)
  -- The cubic Taylor remainder is absorbed on the fixed unit outer tube.
  let m := M + K / 3
  let k := c * max A (3 * A ^ 2 + B)
  let c₁ := m + K / 2 + k * m / 2
  let c₂ := K * (1 + k)
  let c₃ := (5 / 2 : ℝ) * k * m
  let C := 1 + m / 2 + c₁ + c₂ + c₃
  have hm : 0 ≤ m := by dsimp [m]; positivity
  have hk : 0 ≤ k := mul_nonneg hc.le (hA.trans (le_max_left _ _))
  have hc₁ : 0 ≤ c₁ := by dsimp [c₁]; positivity
  have hc₂ : 0 ≤ c₂ := by dsimp [c₂]; positivity
  have hc₃ : 0 ≤ c₃ := by dsimp [c₃]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hmC : m / 2 ≤ C := by dsimp [C]; linarith
  have hc₁C : c₁ ≤ C := by dsimp [C]; linarith
  have hc₂C : c₂ ≤ C := by dsimp [C]; linarith
  have hc₃C : c₃ ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro δ L hδ hδ₁ hL z Q base x hz hz₁ hz₂ hdist hrδ hQ hthird hzero hDzero hHbase
  let r := ‖x - base‖
  let χ : D → ℝ := radialLogarithmicCutoff δ L ∘ z
  have hr : 0 ≤ r := norm_nonneg _
  have hr₁ : r ≤ 1 := hrδ.trans hδ₁
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  obtain ⟨_, _, hradial⟩ := exists_pos_radialLogarithmicCutoff_bounds (E := E)
  have hχ : ContDiffAt ℝ 2 χ x :=
    (((hradial δ L hδ hL).1).of_le (by simp)).contDiffAt.comp x hz
  obtain ⟨_, _, _, hχrange, hχbounds⟩ := hpullback δ L hδ hL z
  have hweighted :
      r * ‖fderiv ℝ χ x‖ ≤ k / L ∧
        r ^ 2 * ‖fderiv ℝ (fderiv ℝ χ) x‖ ≤ k / L := by
    by_cases hrzero : r = 0
    · simp only [hrzero, zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        and_self]
      exact div_nonneg hk hLpos.le
    · obtain ⟨hfirst, _, hsecond⟩ :=
        hχbounds x A B hz (hdist ▸ lt_of_le_of_ne hr (Ne.symm hrzero)) hz₁ hz₂
      rw [hdist] at hfirst hsecond
      exact ⟨hfirst.trans (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_max_left _ _) hc.le) hLpos.le),
        (hsecond hr₁).trans (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_max_right _ _) hc.le) hLpos.le)⟩
  obtain ⟨hH, hD, hvalue⟩ :=
    normal_segment_taylor_bounds hQ hthird hzero hDzero hHbase
  have hMle : M ≤ m := le_add_of_nonneg_right (div_nonneg hK (by norm_num))
  have hvalue' : ‖Q x‖ ≤ m * r ^ 2 / 2 := calc
    ‖Q x‖ ≤ M * r ^ 2 / 2 + K * r ^ 3 / 6 := hvalue
    _ ≤ m * r ^ 2 / 2 := by
      dsimp only [m]
      linarith [mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr hr₁ (by norm_num : 2 ≤ 3)) hK]
  have hD' : ‖fderiv ℝ Q x‖ ≤ m * r + K * r ^ 2 / 2 :=
    hD.trans (add_le_add (mul_le_mul_of_nonneg_right hMle hr) le_rfl)
  have hQ₂ : ContDiffAt ℝ 2 Q x :=
    (hQ x (right_mem_segment ℝ base x)).of_le (by norm_num)
  obtain ⟨hv, hd, hh⟩ := quadratic_cutoff_error_bounds hχ hQ₂ (hχrange x)
    hm hK hk ⟨hr, hrδ⟩ hδ₁ hL hvalue' hD' hH hweighted.1 hweighted.2
  refine ⟨hv.trans ?_, hd.trans ?_, hh.trans ?_⟩
  · linarith [mul_le_mul_of_nonneg_right hmC (sq_nonneg δ)]
  · exact mul_le_mul_of_nonneg_right hc₁C hδ.le
  · exact add_le_add (mul_le_mul_of_nonneg_right hc₂C hδ.le)
      (div_le_div_of_nonneg_right hc₃C hLpos.le)

end PDE.Analysis
