/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Gagliardo.Realization

/-!
# The Gagliardo graph norm in Fourier variables

In positive dimension and for `0 < s < 1`, write `J` for the kernel integral at a unit vector,
with Fourier character `exp(2π i ⟪h, ξ⟫)`. The graph norm of the complete real Gagliardo space
on `ℝ^n` satisfies the exact identity

`‖u‖G² = ‖u‖₂² + J ‖‖ξ‖^s 𝓕u‖₂²`,

with the physical `L²` term retained and Mathlib's Fourier normalization. Since Mathlib's Bessel
weight is `(1 + ‖ξ‖²)^(s/2)`, the graph norm controls the Bessel norm:
`‖u‖Hˢ ≤ (1 + (√J)⁻¹) ‖u‖G`. The reverse bound and the equivalence are in
`Gagliardo.Equivalence`.
-/

@[expose] public section

noncomputable section

open MeasureTheory TemperedDistribution BesselPotentialSpace
open scoped BesselPotentialSpace ENNReal FourierTransform Real SchwartzMap Sobolev

namespace SobolevSpace.Fractional

variable {n : ℕ} {s : ℝ}

/-- The Gagliardo–Fourier kernel integral at the first Euclidean unit vector.
The character in `gagJ` is `exp(2π i ⟪h, ξ⟫)`, matching Mathlib's Fourier normalization. -/
def gagliardoFourierConstant (n : ℕ) (s : ℝ) (hn : 1 ≤ n) : ℝ :=
  GagliardoKernel.gagJ n s (EuclideanSpace.single ⟨0, hn⟩ (1 : ℝ))

/-- The kernel constant is strictly positive in the fractional range. Its finiteness is
proved by `GagliardoKernel.integrable_gagKernel`. -/
theorem gagliardoFourierConstant_pos (hn : 1 ≤ n) (hs0 : 0 < s) (hs1 : s < 1) :
    0 < gagliardoFourierConstant n s hn := by
  apply GagliardoKernel.gagJ_pos hn hs0 hs1
  intro hzero
  have hnorm := congrArg norm hzero
  simp at hnorm

namespace GagliardoSpace

/-- The raw seminorm of a physical representative is the squared norm of the stored
difference-quotient coordinate in the complete graph space. -/
theorem gagliardoSq_toL2CLM (u : GagliardoSpace n s Set.univ) :
    gagliardoSq n s Set.univ (toL2CLM n s u) =
      ENNReal.ofReal (‖differenceQuotient n s Set.univ u‖ ^ 2) := by
  have hbase :
      (toLp n s Set.univ u : ℝ^n → ℝ) =ᵐ[volume.restrict Set.univ] toL2CLM n s u := by
    simpa only [Measure.restrict_univ] using (toL2CLM_apply_ae u).symm
  have hdiff := (differenceQuotient_apply_ae u).trans
    (diffQuot_congr_ae (n := n) (s := s) hbase)
  calc
    gagliardoSq n s Set.univ (toL2CLM n s u) =
        ∫⁻ p, ‖(differenceQuotient n s Set.univ u : ℝ^n × ℝ^n → ℝ) p‖ₑ ^ 2
          ∂gagliardoProductMeasure n Set.univ := by
      exact lintegral_congr_ae (hdiff.fun_comp (fun t : ℝ ↦ ‖t‖ₑ ^ 2)).symm
    _ = eLpNorm (differenceQuotient n s Set.univ u : ℝ^n × ℝ^n → ℝ)
        2 (gagliardoProductMeasure n Set.univ) ^ 2 := by
      simpa [ENNReal.rpow_two] using
        (eLpNorm_nnreal_pow_eq_lintegral (p := (2 : NNReal)) (by norm_num)
          (Lp.aestronglyMeasurable (differenceQuotient n s Set.univ u))).symm
    _ = ENNReal.ofReal (‖differenceQuotient n s Set.univ u‖ ^ 2) := by
      rw [ENNReal.ofReal_pow (norm_nonneg _), Lp.norm_def,
        ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]

/-- The difference-quotient norm on the complete graph space satisfies the exact
Gagliardo–Fourier identity, with the kernel constant retained. -/
theorem norm_differenceQuotient_sq_eq (hn : 1 ≤ n) (hs0 : 0 < s) (hs1 : s < 1)
    (u : GagliardoSpace n s Set.univ) :
    ‖differenceQuotient n s Set.univ u‖ ^ 2 =
      gagliardoFourierConstant n s hn *
        ‖homogeneousFourierLp hs0.le (toHsSpaceReal hs0 hs1 u).1‖ ^ 2 := by
  have h := gagliardoSq_univ_eq_gagJ_mul_fourierSq hs0 hs1
    (e := EuclideanSpace.single ⟨0, hn⟩ (1 : ℝ)) (by simp)
    (toL2CLM n s u : ℝ^n → ℝ) (Lp.memLp (toL2CLM n s u)).ofReal
  have hphysical :
      Complex.ofRealCLM.compLpL 2 volume (toL2CLM n s u) =
        toL2Fun hs0.le (toHsSpaceReal hs0 hs1 u).1 := by
    rw [← toL2FunCLM_toHsSpaceReal hs0 hs1 u, HsSpaceReal.ofReal_toL2FunCLM]
  rw [gagliardoSq_toL2CLM, ofReal_toLp_eq, hphysical,
    fourierSq_eq_norm_homogeneousFourierLp_sq] at h
  have hc : 0 ≤ GagliardoKernel.gagJ n s
      (EuclideanSpace.single ⟨0, hn⟩ (1 : ℝ)) := GagliardoKernel.gagJ_nonneg _
  simpa only [gagliardoFourierConstant, ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hc] using congrArg ENNReal.toReal h

/-- The graph norm is the inhomogeneous physical `L²` term plus the homogeneous
Fourier term with its exact kernel constant. -/
theorem norm_sq_eq_fourier (hn : 1 ≤ n) (hs0 : 0 < s) (hs1 : s < 1)
    (u : GagliardoSpace n s Set.univ) :
    ‖u‖ ^ 2 = ‖toL2CLM n s u‖ ^ 2 + gagliardoFourierConstant n s hn *
      ‖homogeneousFourierLp hs0.le (toHsSpaceReal hs0 hs1 u).1‖ ^ 2 := by
  rw [norm_sq_eq, norm_toL2CLM_eq, norm_differenceQuotient_sq_eq hn hs0 hs1]

theorem norm_differenceQuotient_eq (hn : 1 ≤ n) (hs0 : 0 < s) (hs1 : s < 1)
    (u : GagliardoSpace n s Set.univ) :
    ‖differenceQuotient n s Set.univ u‖ =
      √(gagliardoFourierConstant n s hn) *
        ‖homogeneousFourierLp hs0.le (toHsSpaceReal hs0 hs1 u).1‖ := by
  have hc := (gagliardoFourierConstant_pos hn hs0 hs1).le
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt hc, norm_differenceQuotient_sq_eq hn hs0 hs1]

theorem norm_toL2Fun_toHsSpaceReal (hs0 : 0 < s) (hs1 : s < 1)
    (u : GagliardoSpace n s Set.univ) :
    ‖toL2Fun hs0.le (toHsSpaceReal hs0 hs1 u).1‖ = ‖toL2CLM n s u‖ := by
  rw [← HsSpaceReal.norm_toL2FunCLM_eq, toL2FunCLM_toHsSpaceReal]

/-- The graph norm controls the Bessel norm. The positive kernel constant is
proved, rather than supplied as an assumption. -/
theorem norm_toHsSpaceReal_le (hn : 1 ≤ n) (hs0 : 0 < s) (hs1 : s < 1)
    (u : GagliardoSpace n s Set.univ) :
    ‖toHsSpaceReal hs0 hs1 u‖ ≤
      (1 + (√(gagliardoFourierConstant n s hn))⁻¹) * ‖u‖ := by
  have hgraph := norm_sq_eq u
  have hbase : ‖toL2CLM n s u‖ ≤ ‖u‖ := by
    rw [norm_toL2CLM_eq]
    nlinarith [norm_nonneg u, norm_nonneg (toLp n s Set.univ u),
      sq_nonneg ‖differenceQuotient n s Set.univ u‖]
  have hdiff : ‖differenceQuotient n s Set.univ u‖ ≤ ‖u‖ := by
    nlinarith [norm_nonneg u, norm_nonneg (differenceQuotient n s Set.univ u),
      sq_nonneg ‖toLp n s Set.univ u‖]
  have hc : 0 < √(gagliardoFourierConstant n s hn) :=
    Real.sqrt_pos.mpr (gagliardoFourierConstant_pos hn hs0 hs1)
  have hhom :
      ‖homogeneousFourierLp hs0.le (toHsSpaceReal hs0 hs1 u).1‖ ≤
        (√(gagliardoFourierConstant n s hn))⁻¹ * ‖u‖ := by
    rw [norm_differenceQuotient_eq hn hs0 hs1] at hdiff
    exact (le_inv_mul_iff₀ hc).mpr hdiff
  calc
    ‖toHsSpaceReal hs0 hs1 u‖ ≤
        ‖toL2Fun hs0.le (toHsSpaceReal hs0 hs1 u).1‖ +
          ‖homogeneousFourierLp hs0.le (toHsSpaceReal hs0 hs1 u).1‖ :=
      norm_le_toL2Fun_add_homogeneousFourierLp hs0.le (by linarith) _
    _ ≤ ‖u‖ + (√(gagliardoFourierConstant n s hn))⁻¹ * ‖u‖ := by
      rw [norm_toL2Fun_toHsSpaceReal]
      exact add_le_add hbase hhom
    _ = (1 + (√(gagliardoFourierConstant n s hn))⁻¹) * ‖u‖ := by rw [add_mul, one_mul]

end GagliardoSpace

end SobolevSpace.Fractional
