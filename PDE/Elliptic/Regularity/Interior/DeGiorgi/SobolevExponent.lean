/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Sobolev.FirstOrder.ZeroTrace

/-!
# A gradient Sobolev estimate in every positive dimension

The finite-exponent H¹₀ embedding also applies in dimensions one and two.
Combining its bounded inclusion with Poincaré removes the zeroth-order
norm. This supplies a strict Sobolev gain for De Giorgi iteration without
excluding the low-dimensional cases.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Sobolev ENNReal

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set ℝ^n}

/-- The gradient controls every finite Sobolev exponent of H¹₀ on a
bounded open set. In dimensions one and two there is no finite upper
bound on the target exponent. -/
theorem exists_eLpNorm_le_gradient_of_sobolevExponent
    (hn : 0 < n) (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {q : ℝ} (hq : 2 ≤ q)
    (hnq : 2 < n → q ≤ 2 * (n : ℝ) / ((n : ℝ) - 2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : H¹₀(Ω),
      MemLp (baseRepresentative (u : H¹(Ω))) (ENNReal.ofReal q) (domainMeasure n Ω) ∧
      eLpNorm (baseRepresentative (u : H¹(Ω))) (ENNReal.ofReal q) (domainMeasure n Ω) ≤
        ENNReal.ofReal (C * ‖∇ (u : H¹(Ω))‖) := by
  have : IsFiniteMeasure (domainMeasure n Ω) :=
    isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  have : Fact (1 ≤ ENNReal.ofReal q) := ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  obtain ⟨C, hC⟩ := exists_norm_le_wkpGradientCLM hn hb (p := 2) (by norm_num)
  let J := h10LpEmbedding hn hΩ.measurableSet hq hnq
  let : SeminormedAddCommGroup (H¹₀(Ω)) :=
    (inferInstance : NormedAddCommGroup (H¹₀(Ω))).toSeminormedAddCommGroup
  obtain ⟨D, hD0, hD⟩ := ContinuousLinearMap.bound
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := H¹₀(Ω)) (F := DerivLp n (ENNReal.ofReal q) Ω)
    (σ₁₂ := RingHom.id ℝ) J
  refine ⟨D * (C + 1), mul_pos hD0 (by positivity), fun u ↦ ?_⟩
  have hmem : MemLp (baseRepresentative (u : H¹(Ω))) (ENNReal.ofReal q)
      (domainMeasure n Ω) :=
    memLp_baseCoord_of_sobolevExponent hn hΩ.measurableSet hq hnq u
  refine ⟨hmem, ?_⟩
  have he : ‖J u‖ =
      (eLpNorm (baseRepresentative (u : H¹(Ω))) (ENNReal.ofReal q)
        (domainMeasure n Ω)).toReal := by
    rw [Lp.norm_def, eLpNorm_congr_ae (h10LpEmbedding_ae hn hΩ.measurableSet hq hnq u)]
    rfl
  have hh : ‖J u‖ ≤ (D * (C + 1)) * ‖∇ (u : H¹(Ω))‖ :=
    (hD u).trans <| calc
      D * ‖u‖ ≤ D * (C * ‖∇ (u : H¹(Ω))‖) :=
        mul_le_mul_of_nonneg_left (hC u) hD0.le
      _ ≤ (D * (C + 1)) * ‖∇ (u : H¹(Ω))‖ := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hD0.le)
          (norm_nonneg _)
  rw [he] at hh
  simpa only [ENNReal.ofReal_toReal hmem.eLpNorm_ne_top] using
    ENNReal.ofReal_le_ofReal hh

end SobolevSpace.GraphSpace
