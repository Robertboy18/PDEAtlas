/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.WholeSpaceVector
import PDE.Spaces.Sobolev.Calculus.Product.Interpolation
import PDE.Analysis.MeasureTheory.Lp.EuclideanFields
import PDE.Analysis.MeasureTheory.Lp.IntermediateExponent
import PDE.Analysis.Normed.PiLp.CompareExp

/-!
# Lebesgue exponents of Sobolev fields above the continuity threshold

For `n < 2k` Fourier reconstruction bounds every `u ∈ W^{k,2}(ℝⁿ)` essentially,
`‖u‖_{L∞} ≤ C ‖u‖_{W^{k,2}}` (`SobolevSpace.Product.exists_coordinate_lpNorm_bound`). With
`‖u‖_{Lᵠ} ≤ ‖u‖_{L²} + ‖u‖_{L∞}` the space `W^{k,2}(ℝⁿ)` embeds into every `Lᵠ`, `2 ≤ q ≤ ∞`,
with one constant for all `q`, and so does the field of base representatives of a vector field
with components in `W^{k,2}(ℝⁿ)`.

## Main results

* `exists_eLpNorm_baseRepresentative_le_of_dimension_lt`
* `exists_eLpNorm_toLp_baseRepresentative_le_of_dimension_lt`
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal Sobolev

namespace SobolevSpace.GraphSpace

variable {n k : ℕ} [NeZero n]

/-- Above the continuity threshold `n < 2k`, every `u ∈ W^{k,2}(ℝⁿ)` lies in every `Lᵠ`,
`2 ≤ q ≤ ∞`, with `‖u‖_{Lᵠ} ≤ C ‖u‖_{W^{k,2}}` for one constant `C`. -/
theorem exists_eLpNorm_baseRepresentative_le_of_dimension_lt (hk : (n : ℝ) < 2 * k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : W^{k,2}(ℝ^n)) {q : ℝ≥0∞}, 2 ≤ q →
      MemLp (baseRepresentative u) q volume ∧
        eLpNorm (baseRepresentative u) q volume ≤ ENNReal.ofReal (C * ‖u‖) := by
  obtain ⟨C, hC1, hC⟩ := Product.exists_coordinate_lpNorm_bound hk
  refine ⟨1 + C, by linarith, fun u q hq ↦ ?_⟩
  have hbound := hC 0 (Nat.zero_le k) (baseIndex n 0) u
  have hmem := Product.memLp_coordinate_derivativeExponent hk (Nat.zero_le k) (baseIndex n 0) u
  simp only [DerivIndex.castOrder_baseIndex, baseIndex_toList, List.length_nil,
    GagliardoNirenberg.derivativeExponent_zero, domainMeasure,
    Measure.restrict_univ] at hbound hmem
  change MemLp (baseRepresentative u) ∞ volume at hmem
  change lpNorm (baseRepresentative u) ∞ volume ≤ C * ‖u‖ at hbound
  have htop : eLpNorm (baseRepresentative u) ∞ volume ≤ ENNReal.ofReal (C * ‖u‖) := by
    rw [← ofReal_lpNorm hmem]
    exact ENNReal.ofReal_le_ofReal hbound
  have htwo : eLpNorm (baseRepresentative u) 2 volume ≤ ENNReal.ofReal ‖u‖ := by
    have h := wkpBaseCoordinateCLM_norm_le (n := n) (m := k) (p := 2) (Ω := univ) u
    rw [wkpBaseCoordinateCLM_apply, Lp.norm_def] at h
    have hfin := Lp.eLpNorm_ne_top ((u : WkpAmbientOn n k 2 univ) (baseIndex n k))
    simp only [domainMeasure, Measure.restrict_univ] at h hfin
    change eLpNorm (⇑((u : WkpAmbientOn n k 2 univ) (baseIndex n k))) 2 volume ≤ _
    rw [← ENNReal.ofReal_toReal hfin]
    exact ENNReal.ofReal_le_ofReal h
  have hle : eLpNorm (baseRepresentative u) q volume ≤ ENNReal.ofReal ((1 + C) * ‖u‖) := by
    refine (eLpNorm_le_eLpNorm_add_eLpNorm_top two_ne_zero hq).trans ?_
    rw [add_mul, one_mul, ENNReal.ofReal_add (norm_nonneg u)
      (mul_nonneg ((zero_le_one).trans hC1) (norm_nonneg u))]
    exact add_le_add htwo htop
  exact ⟨lt_of_le_of_lt hle ENNReal.ofReal_lt_top, hle⟩

/-- Above the continuity threshold `n < 2k`, the field of base representatives of a vector
field `v` with components in `W^{k,2}(ℝⁿ)` lies in every `Lᵠ`, `2 ≤ q ≤ ∞`, with
`‖v‖_{Lᵠ} ≤ C ‖v‖` for one constant `C`. -/
theorem exists_eLpNorm_toLp_baseRepresentative_le_of_dimension_lt (hk : (n : ℝ) < 2 * k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : VectorH n k) {q : ℝ≥0∞}, 2 ≤ q →
      MemLp (fun x ↦ WithLp.toLp 2 fun j ↦ baseRepresentative (v j) x) q volume ∧
        eLpNorm (fun x ↦ WithLp.toLp 2 fun j ↦ baseRepresentative (v j) x) q volume ≤
          ENNReal.ofReal (C * ‖v‖) := by
  obtain ⟨C, hC, hbase⟩ := exists_eLpNorm_baseRepresentative_le_of_dimension_lt hk
  refine ⟨n * C, by positivity, fun v q hq ↦ ?_⟩
  have hq1 : 1 ≤ q := one_le_two.trans hq
  have hmeas (j : Fin n) : AEStronglyMeasurable (baseRepresentative (v j)) volume :=
    ((hbase (v j) hq).1).aestronglyMeasurable
  set F : ℝ^n → ℝ^n := fun x ↦ WithLp.toLp 2 fun j ↦ baseRepresentative (v j) x
  have hF : AEStronglyMeasurable F volume := aestronglyMeasurable_toLp hmeas
  have hle : eLpNorm F q volume ≤ ENNReal.ofReal (n * C * ‖v‖) := by
    calc
      eLpNorm F q volume ≤ eLpNorm (fun x ↦ ∑ j, ‖baseRepresentative (v j) x‖) q volume := by
        refine eLpNorm_mono hF fun x ↦ ?_
        rw [Real.norm_of_nonneg (Finset.sum_nonneg fun j _ ↦ norm_nonneg _)]
        exact PiLp.norm_le_sum_norm (F x)
      _ = eLpNorm (∑ j, fun x ↦ ‖baseRepresentative (v j) x‖) q volume := by
        congr 1
        funext x
        rw [Finset.sum_apply]
      _ ≤ ∑ j, eLpNorm (fun x ↦ ‖baseRepresentative (v j) x‖) q volume := eLpNorm_sum_le hq1
      _ ≤ ∑ _j : Fin n, ENNReal.ofReal (C * ‖v‖) := by
        refine Finset.sum_le_sum fun j _ ↦ ?_
        rw [eLpNorm_norm _ (hmeas j)]
        refine (hbase (v j) hq).2.trans (ENNReal.ofReal_le_ofReal ?_)
        exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le v j) hC
      _ = ENNReal.ofReal (n * C * ‖v‖) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          mul_assoc, ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
  exact ⟨lt_of_le_of_lt hle ENNReal.ofReal_lt_top, hle⟩

end SobolevSpace.GraphSpace
