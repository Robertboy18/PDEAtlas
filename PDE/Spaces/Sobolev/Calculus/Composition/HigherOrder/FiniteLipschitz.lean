/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Composition.HigherOrder.DifferenceOperator

/-!
# Local Lipschitz continuity of finite Sobolev composition

For `n < 2k`, smooth reactions fixing zero act locally Lipschitz continuously on finite families
in `Hᵏ`. The proof applies the quantitative composition estimate to the averaged derivative with a
normalized direction, and needs no additional derivative margin. The reaction `f(Du, u_t, u)` of
Evans §12.2.2, Theorem 3, is of this kind, with `f` applied to the first jet; Evans's contraction
step (12) measures differences in a lower norm and uses only a pointwise Lipschitz bound for `f`
(p. 669).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.2.2, Theorems 2 and 3, pp. 666-670: estimate (7) bounds
  `f(u_1, ..., u_m)` in `Hᵏ`, and the proof of Theorem 3 uses it for the reaction `f(Du, u_t, u)`.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Sobolev Topology

namespace SobolevSpace.Composition

open GraphSpace

variable {n k : ℕ} [NeZero n] {ι : Type*} [Fintype ι]

/-- If `n < 2k`, `f` is smooth and `f 0 = 0`, then `U ↦ f ∘ U` on finite families in
`Hᵏ(ℝ^n)` is Lipschitz on every closed ball about zero. -/
theorem exists_lipschitzOn_finiteComposition (hk : (n : ℝ) < 2 * (k : ℝ))
    {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0) (R : ℝ) :
    ∃ K, LipschitzOnWith K (finiteComposition hk hf hf0) (Metric.closedBall 0 R) := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_finiteComposition_bound hk
    (contDiff_differenceReaction hf)
    (show differenceReaction f 0 = 0 from averagedDerivative_zero f 0 0) (max R 1)
  refine ⟨⟨C, hC⟩, LipschitzOnWith.of_dist_le_mul ?_⟩
  intro U hU V hV
  have hU' : ‖U‖ ≤ R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hU
  have hV' : ‖V‖ ≤ R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hV
  by_cases hUV : U = V
  · simp [hUV]
  have hd : 0 < ‖U - V‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hUV)
  let Z : Fin 3 × ι → W^{k,2}(ℝ^n) :=
    fun ji ↦ ![U, V, ‖U - V‖⁻¹ • (U - V)] ji.1 ji.2
  have hunit : ‖‖U - V‖⁻¹ • (U - V)‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hd.ne']
  have hZ : ‖Z‖ ≤ max R 1 := by
    apply (pi_norm_le_iff_of_nonneg (zero_le_one.trans (le_max_right R 1))).mpr
    rintro ⟨j, i⟩
    fin_cases j
    · exact (norm_le_pi_norm U i).trans
        (hU'.trans (le_max_left R 1))
    · exact (norm_le_pi_norm V i).trans
        (hV'.trans (le_max_left R 1))
    · exact (norm_le_pi_norm (‖U - V‖⁻¹ • (U - V)) i).trans
        (hunit.le.trans (le_max_right R 1))
  rw [dist_eq_norm, dist_eq_norm,
    finiteComposition_sub_eq_smul hk hf hf0 U V hd.ne', norm_smul,
    Real.norm_eq_abs, abs_norm]
  exact (mul_le_mul_of_nonneg_left (hbound Z hZ) hd.le).trans_eq (mul_comm _ _)

/-- If `n < 2k`, `f` is smooth and `f 0 = 0`, then `U ↦ f ∘ U` on finite families in
`Hᵏ(ℝ^n)` is locally Lipschitz in the `Hᵏ` norm. -/
theorem locallyLipschitz_finiteComposition (hk : (n : ℝ) < 2 * (k : ℝ))
    {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0) :
    LocallyLipschitz (finiteComposition hk hf hf0) := by
  intro U
  obtain ⟨K, hK⟩ := exists_lipschitzOn_finiteComposition hk hf hf0 (‖U‖ + 1)
  refine ⟨K, Metric.closedBall 0 (‖U‖ + 1), ?_, hK⟩
  apply Metric.closedBall_mem_nhds_of_mem
  simp only [Metric.mem_ball, dist_zero_right]
  exact lt_add_one ‖U‖

end SobolevSpace.Composition
