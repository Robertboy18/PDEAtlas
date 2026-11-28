/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.Gradient
public import PDE.Spaces.Sobolev.Variational.Spaces.H1
public import PDE.Spaces.Sobolev.Inequalities.Sobolev.Sharp.WholeSpace
import PDE.Analysis.MeasureTheory.Lp.RealL2
import PDE.Spaces.Sobolev.Approximation.Density.Global
import PDE.Spaces.Sobolev.GraphSpace.Topology.SmoothData
import PDE.Spaces.Sobolev.Inequalities.Hardy.Ball
import PDE.Spaces.Sobolev.Inequalities.Sobolev.HigherOrder.ContinuousEmbedding
import PDE.Spaces.Sobolev.Inequalities.Sobolev.HigherOrder.Global
import PDE.Spaces.Sobolev.Variational.Spaces.ZeroBoundaryCoordinates

/-!
# The sharp Sobolev inequality on `H¹(ℝⁿ)`

Every `u` in the Sobolev space `H¹(ℝⁿ)`, `n ≥ 3`, satisfies

`‖u‖_{2n/(n-2)} ≤ S_n ‖∇u‖₂`

with the constant `S_n = sharpSobolevConstant n` of Aubin and Talenti, where `‖∇u‖₂` is the `L²`
norm of the weak gradient. This extends `eLpNorm_le_sharpSobolevConstant_mul_eLpNorm_fderiv`
from Lipschitz functions with compact support to all of `H¹(ℝⁿ)`. That `S_n` is the best
constant is not proved, and the spaces `W^{1,p}` with `p ≠ 2` are not treated.

## Main results

* `memLp_pStar_H1`: for `n ≥ 3` the representative of every `u ∈ H¹(ℝⁿ)` lies in `L^q`,
  `q = pStar n 2 = 2n / (n - 2)`. It is `memLp_of_inv_eq` for one derivative and the exponent `2`.
* `toReal_eLpNorm_le_sharpSobolevConstant_mul_norm_wkpGradientCLM`: `‖u‖_q ≤ S_n ‖∇u‖₂` for every
  `u ∈ H¹(ℝⁿ)`, `n ≥ 3`, with the weak gradient `wkpGradientCLM u`.
* `eLpNorm_le_ofReal_sharpSobolevConstant_mul_norm`: `‖u‖_q ≤ S_n ‖u‖_{H¹}` for the same `u`.

## How it works

A smooth function with compact support is Lipschitz, so the inequality holds for it. For the
element of `H¹(ℝⁿ)` that it defines, the `L^q` norm of the representative is the `L^q` norm of
the function, and the norm of the weak gradient is the `L²` norm of the classical one
(`SobolevSpace.GraphSpace.norm_wkpGradientCLM_mkWkpSpaceOnOfContDiff_sq`). Smooth functions with
compact support are dense in `H¹(ℝⁿ)` (`SobolevSpace.GraphSpace.globalApproximation_WkpSpace`).
Both sides are continuous there: the gradient norm, and the `L^q` norm by `memLp_pStar_H1` and
the closed graph theorem (`embeddingCLMOfMemLp`). So the set where the inequality holds is
closed and dense.

## References

* G. Talenti, "Best constant in Sobolev inequality", *Ann. Mat. Pura Appl.* 110 (1976), 353-372:
  the inequality, with the constant in formula (2). <https://doi.org/10.1007/BF02418013>
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Module SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal NNReal Sobolev Topology

namespace SobolevSpace.Inequalities

/-! ## Smooth functions with compact support -/

/-- The sharp Sobolev inequality for smooth functions with compact support on `ℝⁿ`, `n ≥ 3`:
`‖f‖_q ≤ S_n ‖∇f‖₂` with `q = 2n / (n - 2)`, both norms as real numbers. It is a case of
`eLpNorm_le_sharpSobolevConstant_mul_eLpNorm_fderiv`. -/
private theorem toReal_eLpNorm_le_of_contDiff {n : ℕ} (hn : 3 ≤ n) {f : ℝ^n → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    (eLpNorm f (pStar n 2) volume).toReal ≤
      sharpSobolevConstant n * (eLpNorm (fderiv ℝ f) 2 volume).toReal := by
  obtain ⟨L, hL⟩ := hf.lipschitzWith_of_hasCompactSupport hc (by simp)
  have h := eLpNorm_le_sharpSobolevConstant_mul_eLpNorm_fderiv hL hc
    (by rw [finrank_euclideanSpace_fin]; exact hn)
  rw [finrank_euclideanSpace_fin] at h
  have hfin : eLpNorm (fderiv ℝ f) 2 volume ≠ ∞ :=
    ((hf.continuous_fderiv (by simp)).memLp_of_hasCompactSupport (hc.fderiv ℝ)).eLpNorm_ne_top
  have h' := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) h
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sharpSobolevConstant_pos hn).le] at h'

/-! ## The Sobolev space -/

/-- **The Sobolev embedding of `H¹(ℝⁿ)`**, `n ≥ 3`: the representative of every element lies in
`L^q`, `q = pStar n 2 = 2n / (n - 2)`. This is `memLp_of_inv_eq` for one derivative and the
exponent `2`. -/
theorem memLp_pStar_H1 {n : ℕ} (hn : 3 ≤ n) (U : H¹(ℝ^n)) :
    MemLp (baseRepresentative U) (pStar n 2) (domainMeasure n univ) := by
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have h2n : ((2 : ℝ≥0) : ℝ) < n := by
    push_cast
    linarith
  have h := memLp_of_inv_eq (n := n) (k := 1) (p := 2) (q := pStar n 2) (by norm_num) (by omega)
    (by push_cast; linarith)
    (by rw [inv_pStar_eq (by omega) (by norm_num) h2n]; push_cast; ring) U
  simpa [baseRepresentative, domainMeasure] using h

/-- **The sharp Sobolev inequality on `H¹(ℝⁿ)`**, `n ≥ 3` (Aubin, Talenti): every `u` in
`H¹(ℝⁿ)` satisfies `‖u‖_q ≤ S_n ‖∇u‖₂` with `q = pStar n 2 = 2n / (n - 2)` and
`S_n = sharpSobolevConstant n`. The left side is the `L^q` norm of the representative of `u`,
which is finite by `memLp_pStar_H1`, and the right side has the `L²` norm of the weak gradient
`wkpGradientCLM u`. Both sides are continuous on `H¹(ℝⁿ)`, the inequality holds for smooth
functions with compact support, and these are dense. That `S_n` is the smallest constant is
not proved. -/
theorem toReal_eLpNorm_le_sharpSobolevConstant_mul_norm_wkpGradientCLM {n : ℕ} (hn : 3 ≤ n)
    (u : H¹(ℝ^n)) :
    (eLpNorm (baseRepresentative u) (pStar n 2) volume).toReal ≤
      sharpSobolevConstant n * ‖wkpGradientCLM u‖ := by
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn2 : (0 : ℝ) < (n : ℝ) - 2 := by linarith
  have hq1 : (1 : ℝ) ≤ 2 * (n : ℝ) / (n - 2) := by
    rw [le_div_iff₀ hn2]
    linarith
  have : Fact ((1 : ℝ≥0∞) ≤ (pStar n 2 : ℝ≥0)) :=
    ⟨by rw [coe_pStar_two]; exact ENNReal.one_le_ofReal.mpr hq1⟩
  -- the inclusion in `L^q` is continuous
  set J : H¹(ℝ^n) →L[ℝ] Lp ℝ (pStar n 2 : ℝ≥0) (domainMeasure n univ) :=
    embeddingCLMOfMemLp (memLp_pStar_H1 hn) with hJ
  have hJn (U : H¹(ℝ^n)) :
      ‖J U‖ = (eLpNorm (baseRepresentative U) (pStar n 2) volume).toReal := by
    rw [Lp.norm_def, hJ, embeddingCLMOfMemLp_apply, domainMeasure, Measure.restrict_univ]
  rw [← hJn]
  let S : Set (H¹(ℝ^n)) := {V | ‖J V‖ ≤ sharpSobolevConstant n * ‖wkpGradientCLM V‖}
  have hS : IsClosed S :=
    isClosed_le J.continuous.norm (continuous_const.mul wkpGradientCLM.continuous.norm)
  -- smooth functions with compact support are dense
  obtain ⟨f, hf, hcs, hlim⟩ := globalApproximation_WkpSpace
    (Approximation.standardMollifier n) (by norm_num : (2 : ℝ≥0∞) ≠ ∞) 1 u
  let V : ℕ → H¹(ℝ^n) := fun m ↦
    mkWkpSpaceOnOfContDiff (n := n) (k := 1) (p := 2) (Ω := univ) (f m) (hf m) (hcs m)
  have hV : Tendsto V atTop (𝓝 u) := tendsto_iff_norm_sub_tendsto_zero.mpr hlim
  refine hS.mem_of_tendsto hV (Eventually.of_forall fun m ↦ ?_)
  -- the inequality for a smooth function with compact support
  have hbase : baseRepresentative (V m) =ᵐ[volume] f m := by
    have h := wkpBaseCoordinateCLM_mkWkpSpaceOnOfContDiff_ae (k := 1) (Ω := univ) (hf m) (hcs m)
    have hae : ae (domainMeasure n univ) = ae (volume : Measure (ℝ^n)) := by
      rw [domainMeasure, Measure.restrict_univ]
    rw [hae] at h
    exact h
  have hmem : MemLp (fun x ↦ ‖fderiv ℝ (f m) x‖) 2 (volume : Measure (ℝ^n)) :=
    (((hf m).continuous_fderiv (by simp)).memLp_of_hasCompactSupport ((hcs m).fderiv ℝ)).norm
  have hgrad : ‖wkpGradientCLM (V m)‖ = (eLpNorm (fderiv ℝ (f m)) 2 volume).toReal := by
    have h2 : ‖wkpGradientCLM (V m)‖ ^ 2 = (eLpNorm (fderiv ℝ (f m)) 2 volume).toReal ^ 2 := by
      rw [norm_wkpGradientCLM_mkWkpSpaceOnOfContDiff_sq (hf m) (hcs m), domainMeasure,
        Measure.restrict_univ, integral_sq_eq_eLpNorm_toReal_sq hmem,
        eLpNorm_norm _ ((hf m).continuous_fderiv (by simp)).aestronglyMeasurable]
    exact (sq_eq_sq₀ (norm_nonneg _) ENNReal.toReal_nonneg).mp h2
  change ‖J (V m)‖ ≤ _
  rw [hJn, eLpNorm_congr_ae hbase, hgrad]
  exact toReal_eLpNorm_le_of_contDiff hn (hf m) (hcs m)

/-- **The `L^q` bound of `H¹(ℝⁿ)` with the constant of Aubin and Talenti**, `n ≥ 3`,
`q = pStar n 2`: `‖u‖_q ≤ S_n ‖u‖_{H¹}`. -/
theorem eLpNorm_le_ofReal_sharpSobolevConstant_mul_norm {n : ℕ} (hn : 3 ≤ n) (u : H¹(ℝ^n)) :
    eLpNorm (baseRepresentative u) (pStar n 2) volume ≤
      ENNReal.ofReal (sharpSobolevConstant n * ‖u‖) := by
  have hfin : eLpNorm (baseRepresentative u) (pStar n 2) volume ≠ ∞ := by
    have h := (memLp_pStar_H1 hn u).eLpNorm_ne_top
    rwa [domainMeasure, Measure.restrict_univ] at h
  rw [← ENNReal.ofReal_toReal hfin]
  exact ENNReal.ofReal_le_ofReal
    ((toReal_eLpNorm_le_sharpSobolevConstant_mul_norm_wkpGradientCLM hn u).trans
      (mul_le_mul_of_nonneg_left (norm_wkpGradientCLM_apply_le u) (sharpSobolevConstant_pos hn).le))

end SobolevSpace.Inequalities
