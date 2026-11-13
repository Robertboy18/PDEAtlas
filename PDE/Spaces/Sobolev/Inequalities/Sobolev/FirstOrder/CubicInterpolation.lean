/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Sobolev.FirstOrder.Smooth
import PDE.Analysis.MeasureTheory.Lp.IntermediateExponent

/-!
# The cubic integral of a three-dimensional `H¹` function

For a continuously differentiable `f : ℝ^3 → H` with `f` and its derivative square
integrable, Hölder's inequality between `L²` and `L⁶` and the Sobolev inequality
`‖f‖₆ ≤ C ‖Df‖₂` give `∫ ‖f‖³ ≤ C ‖f‖₂^{3/2} ‖Df‖₂^{3/2}`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SobolevSpace.Inequalities

/-- The cubic integral of a continuously differentiable `L²` function on `ℝ^3` with `L²`
derivative is bounded by `‖f‖₂^{3/2} ‖Df‖₂^{3/2}`, with one constant for all such functions. -/
theorem exists_integral_norm_cube_le {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℝ^3 → H, ContDiff ℝ 1 f → MemLp f 2 volume →
      MemLp (fderiv ℝ f) 2 volume →
        Integrable (fun x ↦ ‖f x‖ ^ 3) ∧
          ∫ x, ‖f x‖ ^ 3 ≤ C * (eLpNorm f 2 volume).toReal ^ (3 / 2 : ℝ) *
            (eLpNorm (fderiv ℝ f) 2 volume).toReal ^ (3 / 2 : ℝ) := by
  set K : ℝ := (eLpNormLESNormFDerivOfEqInnerConst (volume : Measure ℝ^3) 2 : ℝ)
  refine ⟨K ^ (3 / 2 : ℝ), by positivity, fun f hf hf2 hDf ↦ ?_⟩
  have hf2' : MemLp f ((2 : NNReal) : ℝ≥0∞) volume := by exact_mod_cast hf2
  have hDf' : MemLp (fderiv ℝ f) ((2 : NNReal) : ℝ≥0∞) volume := by exact_mod_cast hDf
  have hq : ((6 : NNReal) : ℝ)⁻¹ = ((2 : NNReal) : ℝ)⁻¹ - ((3 : ℕ) : ℝ)⁻¹ := by norm_num
  have hf6 : MemLp f 6 volume := by
    exact_mod_cast memLp_of_memLp_fderiv_inner volume hf hf2' hDf' (by norm_num) (by norm_num) hq
  have hsob : (eLpNorm f 6 volume).toReal ≤ K * (eLpNorm (fderiv ℝ f) 2 volume).toReal := by
    exact_mod_cast eLpNorm_toReal_le_eLpNorm_fderiv_of_memLp_inner volume hf hf2' hDf'
      (by norm_num) (by norm_num) hq
  have hmeas : AEStronglyMeasurable (fun x ↦ ‖f x‖ ^ 3) volume :=
    (hf.continuous.norm.pow 3).aestronglyMeasurable
  have hlin := lintegral_enorm_cube_le hf.continuous.aestronglyMeasurable (μ := volume)
  have hfin : eLpNorm f 2 volume ^ (3 / 2 : ℝ) * eLpNorm f 6 volume ^ (3 / 2 : ℝ) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hf2.eLpNorm_ne_top)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hf6.eLpNorm_ne_top)
  have hcube : ∀ x, ENNReal.ofReal (‖f x‖ ^ 3) = ‖f x‖ₑ ^ 3 := fun x ↦ by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  refine ⟨⟨hmeas, ?_⟩, ?_⟩
  · simp only [HasFiniteIntegral, enorm_pow, enorm_norm]
    exact hlin.trans_lt hfin.lt_top
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x ↦ by positivity)
    hmeas]
  simp_rw [hcube]
  calc (∫⁻ x, ‖f x‖ₑ ^ 3).toReal
      ≤ (eLpNorm f 2 volume ^ (3 / 2 : ℝ) * eLpNorm f 6 volume ^ (3 / 2 : ℝ)).toReal :=
        ENNReal.toReal_mono hfin hlin
    _ = (eLpNorm f 2 volume).toReal ^ (3 / 2 : ℝ) *
          (eLpNorm f 6 volume).toReal ^ (3 / 2 : ℝ) := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_rpow, ENNReal.toReal_rpow]
    _ ≤ (eLpNorm f 2 volume).toReal ^ (3 / 2 : ℝ) *
          (K * (eLpNorm (fderiv ℝ f) 2 volume).toReal) ^ (3 / 2 : ℝ) := by
        gcongr
    _ = K ^ (3 / 2 : ℝ) * (eLpNorm f 2 volume).toReal ^ (3 / 2 : ℝ) *
          (eLpNorm (fderiv ℝ f) 2 volume).toReal ^ (3 / 2 : ℝ) := by
        rw [Real.mul_rpow (by positivity) (by positivity)]
        ring

end SobolevSpace.Inequalities
