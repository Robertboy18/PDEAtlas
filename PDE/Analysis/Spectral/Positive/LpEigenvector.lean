/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Spectral.Positive.LpHomotopy

/-!
# A nonnegative eigenvector of a compact positive operator

A nonzero nonnegative subeigenvector yields a normalized nonnegative eigenvector.
We normalize the arbitrarily large perturbed eigenvectors from Schaefer. Their
normalized perturbations tend to zero; compactness supplies a joint limit of the
operator images and the bounded scalar parameters.

This is step 5 of the proof of Evans, §6.5.2, Theorem 3, (29)-(32), with the cone replaced
by the almost-everywhere order of Mathlib's `Lp`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.5.2, Theorem 3, p. 361, step 5 of its proof,
  (29)-(32), pp. 362-363. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open Filter MeasureTheory Set Metric
open scoped ENNReal Topology

namespace ContinuousLinearMap

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A compact positive operator with a nonzero nonnegative subeigenvector has a
normalized nonnegative eigenvector. The equation uses the reciprocal eigenvalue
parameter, which is bounded above by the subeigenvector parameter. -/
theorem exists_nonneg_eigenvector_of_subeigenvector
    (A : Lp ℝ p μ →L[ℝ] Lp ℝ p μ) (hcompact : IsCompactOperator A)
    (hA : ∀ v : Lp ℝ p μ, (∀ᵐ x ∂μ, 0 ≤ v x) → ∀ᵐ x ∂μ, 0 ≤ A v x)
    {w : Lp ℝ p μ} {M : ℝ}
    (hw : ∀ᵐ x ∂μ, 0 ≤ w x) (hw0 : w ≠ 0)
    (hM : 0 < M) (hsub : ∀ᵐ x ∂μ, w x ≤ M * A w x) :
    ∃ (v : Lp ℝ p μ) (η : ℝ),
      ‖v‖ = 1 ∧ (∀ᵐ x ∂μ, 0 ≤ v x) ∧ 0 < η ∧ η ≤ M ∧ v = η • A v := by
  have hex (n : ℕ) := A.exists_large_nonneg_perturbed_eigenvector hcompact hA
    hw hw0 hM hsub zero_lt_one ((n : ℝ) + 1)
  choose u η hunorm hunonneg hη0 hηM hueq using hex
  have hupos (n : ℕ) : 0 < ‖u n‖ := (Nat.cast_add_one_pos n).trans_le (hunorm n)
  let r : ℕ → ℝ := fun n ↦ ‖u n‖⁻¹
  let v : ℕ → Lp ℝ p μ := fun n ↦ r n • u n
  have hr0 (n : ℕ) : 0 ≤ r n := (inv_pos.mpr (hupos n)).le
  have hrbound (n : ℕ) : r n ≤ 1 / ((n : ℝ) + 1) := by
    simpa only [r, one_div] using
      (one_div_le_one_div_of_le (Nat.cast_add_one_pos n) (hunorm n))
  have hr1 (n : ℕ) : r n ≤ 1 := by
    exact (hrbound n).trans ((div_le_one (Nat.cast_add_one_pos n)).mpr
      (by linarith [Nat.cast_nonneg (α := ℝ) n]))
  have hr : Tendsto r atTop (𝓝 0) :=
    squeeze_zero hr0 hrbound tendsto_one_div_add_atTop_nhds_zero_nat
  have hvnorm (n : ℕ) : ‖v n‖ = 1 := by
    dsimp [v, r]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hupos n)),
      inv_mul_cancel₀ (hupos n).ne']
  have hvnonneg (n : ℕ) : ∀ᵐ x ∂μ, 0 ≤ v n x := by
    filter_upwards [hunonneg n, Lp.coeFn_smul (r n) (u n)] with x hx hscale
    change 0 ≤ (r n • u n) x
    rw [hscale]
    exact mul_nonneg (hr0 n) hx
  have hveq (n : ℕ) : v n = η n • A (v n + r n • w) := by
    calc
      v n = r n • (η n • A (u n + w)) := by
        exact congrArg (fun z : Lp ℝ p μ ↦ r n • z)
          (by simpa only [one_smul] using hueq n)
      _ = η n • A (v n + r n • w) := by
        rw [smul_comm, ← map_smul, smul_add]
  have hin (n : ℕ) : v n + r n • w ∈ closedBall (0 : Lp ℝ p μ) (1 + ‖w‖) := by
    rw [mem_closedBall_zero_iff]
    calc
      ‖v n + r n • w‖ ≤ ‖v n‖ + ‖r n • w‖ := norm_add_le _ _
      _ = 1 + r n * ‖w‖ := by
        rw [hvnorm, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hr0 n)]
      _ ≤ 1 + ‖w‖ := add_le_add le_rfl
        (by simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (hr1 n) (norm_nonneg w))
  have hK := (isCompact_Icc : IsCompact (Icc (0 : ℝ) M)).prod
    (hcompact.isCompact_closure_image_closedBall (f := A.toLinearMap) (1 + ‖w‖))
  obtain ⟨z, hz, φ, hφ, hlimit⟩ := hK.tendsto_subseq
    (x := fun n ↦ (η n, A (v n + r n • w)))
    (fun n ↦ ⟨⟨hη0 n, (hηM n).le⟩, subset_closure (mem_image_of_mem A (hin n))⟩)
  have hηlimit : Tendsto (fun n ↦ η (φ n)) atTop (𝓝 z.1) := by
    simpa only [Function.comp_def] using (continuous_fst.tendsto z).comp hlimit
  have hAlimit : Tendsto (fun n ↦ A (v (φ n) + r (φ n) • w)) atTop (𝓝 z.2) := by
    simpa only [Function.comp_def] using (continuous_snd.tendsto z).comp hlimit
  let v₀ : Lp ℝ p μ := z.1 • z.2
  have hvlimit : Tendsto (fun n ↦ v (φ n)) atTop (𝓝 v₀) := by
    apply (hηlimit.smul hAlimit).congr'
    exact Eventually.of_forall fun n ↦ (hveq (φ n)).symm
  have hperturb : Tendsto (fun n ↦ r (φ n) • w) atTop (𝓝 (0 : Lp ℝ p μ)) := by
    simpa only [zero_smul, Function.comp_def] using (hr.comp hφ.tendsto_atTop).smul_const w
  have hinput : Tendsto (fun n ↦ v (φ n) + r (φ n) • w) atTop (𝓝 v₀) := by
    simpa only [add_zero] using hvlimit.add hperturb
  have hzA : z.2 = A v₀ := tendsto_nhds_unique hAlimit
    (A.continuous.continuousAt.tendsto.comp hinput)
  have hnorm : ‖v₀‖ = 1 := tendsto_nhds_unique hvlimit.norm
    (by simpa only [hvnorm] using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ))
      atTop (𝓝 1)))
  have hnonneg : ∀ᵐ x ∂μ, 0 ≤ v₀ x :=
    Lp.isClosed_nonneg_ae.mem_of_tendsto hvlimit (Eventually.of_forall fun n ↦ hvnonneg (φ n))
  have heq : v₀ = z.1 • A v₀ := by
    change z.1 • z.2 = z.1 • A v₀
    rw [hzA]
  have hpos : 0 < z.1 := by
    refine lt_of_le_of_ne hz.1.1 ?_
    intro hzero
    have hvzero : v₀ = 0 := by simpa only [← hzero, zero_smul] using heq
    rw [hvzero, norm_zero] at hnorm
    exact zero_ne_one hnorm
  exact ⟨v₀, z.1, hnorm, hnonneg, hpos, hz.1.2, heq⟩

end ContinuousLinearMap
