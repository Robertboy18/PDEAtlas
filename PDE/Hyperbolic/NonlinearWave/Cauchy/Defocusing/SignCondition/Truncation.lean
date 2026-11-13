/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition.Potential

/-!
# Sign-preserving reaction truncations

A smooth bump preserves an arbitrary-growth reaction on a prescribed amplitude interval and makes it
globally Lipschitz. The sign condition survives, and the truncated potential is bounded above by the
original potential. Consequently finite initial potential energy remains finite under these
truncations. This is the truncation `f_k` of step 1 of the proof of Theorem 1 of Evans, §12.3.1.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.3.1, step 1 of the proof of Theorem 1.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set
open PDE.Analysis (primitive continuous_primitive)

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition

/-- A sign-preserving reaction admits compactly supported Lipschitz replacements
with the same differentiability order, pointwise norm domination, and dominated
normalized potentials. -/
theorem exists_sign_preserving_lipschitz_reaction {m : ℕ∞} {f : ℝ → ℝ} (hf : ContDiff ℝ m f)
    (hm : m ≠ 0) (hs : ∀ z, 0 ≤ z * f z) {R : ℝ} (hR : 0 < R) :
    ∃ (g : ℝ → ℝ) (K : NNReal), ContDiff ℝ m g ∧ HasCompactSupport g ∧ LipschitzWith K g ∧
      EqOn g f (Metric.closedBall 0 R) ∧ (∀ z, 0 ≤ z * g z) ∧ (∀ z, |g z| ≤ |f z|) ∧ ∀ z,
      primitive g z ≤ primitive f z := by
  let b : ContDiffBump (0 : ℝ) :=
    { rIn := R
      rOut := R + 1
      rIn_pos := hR
      rIn_lt_rOut := lt_add_one R }
  let g : ℝ → ℝ := fun z ↦ b z * f z
  have hg : ContDiff ℝ m g := b.contDiff.mul hf
  have hc : HasCompactSupport g := b.hasCompactSupport.mul_right
  obtain ⟨K, hK⟩ := hg.lipschitzWith_of_hasCompactSupport hc (by simpa using hm)
  refine ⟨g, K, hg, hc, hK, ?_, ?_, ?_, ?_⟩
  · intro z hz
    change b z * f z = f z
    rw [b.one_of_mem_closedBall hz, one_mul]
  · intro z
    change 0 ≤ z * (b z * f z)
    rw [mul_left_comm]
    exact mul_nonneg (b.nonneg' z) (hs z)
  · intro z
    change |b z * f z| ≤ |f z|
    rw [abs_mul, abs_of_nonneg (b.nonneg' z)]
    exact mul_le_of_le_one_left (abs_nonneg _) b.le_one
  · exact primitive_mul_le hf.continuous b.continuous hs (fun _ ↦ b.le_one)

/-- The original finite potential energy dominates that of a sign-preserving
cutoff on an arbitrary measure space. No integrability of the reaction is needed. -/
theorem integrable_potential_mul {α : Type*} [MeasurableSpace α] {μ : Measure α} {u : α → ℝ}
    {f χ : ℝ → ℝ} (hf : Continuous f) (hχ : Continuous χ) (hs : ∀ z, 0 ≤ z * f z)
    (hχ₀ : ∀ z, 0 ≤ χ z) (hχ₁ : ∀ z, χ z ≤ 1) (hu : AEStronglyMeasurable u μ)
    (hF : Integrable (fun x ↦ primitive f (u x)) μ) :
    Integrable (fun x ↦ primitive (fun z ↦ χ z * f z) (u x)) μ := by
  have hsign (z : ℝ) : 0 ≤ z * (χ z * f z) := by
    rw [mul_left_comm]
    exact mul_nonneg (hχ₀ z) (hs z)
  apply hF.mono' ((continuous_primitive (hχ.mul hf)).comp_aestronglyMeasurable hu)
  exact Filter.Eventually.of_forall fun x ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (primitive_nonneg (hχ.mul hf) hsign (u x))]
    exact primitive_mul_le hf hχ hs hχ₁ (u x)

/-- Truncating a sign-preserving reaction cannot increase the initial potential energy. -/
theorem integral_potential_mul_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {u : α → ℝ}
    {f χ : ℝ → ℝ} (hf : Continuous f) (hχ : Continuous χ) (hs : ∀ z, 0 ≤ z * f z)
    (hχ₀ : ∀ z, 0 ≤ χ z) (hχ₁ : ∀ z, χ z ≤ 1) (hu : AEStronglyMeasurable u μ)
    (hF : Integrable (fun x ↦ primitive f (u x)) μ) :
    (∫ x, primitive (fun z ↦ χ z * f z) (u x) ∂μ) ≤ ∫ x, primitive f (u x) ∂μ :=
  integral_mono (integrable_potential_mul hf hχ hs hχ₀ hχ₁ hu hF) hF
    (fun x ↦ primitive_mul_le hf hχ hs hχ₁ (u x))

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition
