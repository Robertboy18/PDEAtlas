/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Gagliardo.Quotient

/-!
# Realizing Bessel restriction classes in intrinsic domain spaces

The canonical minimal extension of a Bessel restriction class gives a continuous
linear injection into the intrinsic Gagliardo space on `Ω`, for `0 < s < 1` and any set `Ω`.
Its range consists exactly of the restrictions of whole-space Gagliardo elements, by the
quotient equivalence of `Gagliardo.Quotient`. No geometric assumption on `Ω` is needed for
these constructions. Surjectivity onto the intrinsic space requires a separate extension
theorem.
-/

@[expose] public section

noncomputable section

open scoped FractionalSobolev

open MeasureTheory

namespace SobolevSpace.Fractional

variable {n : ℕ} {s : ℝ} {Ω : Set (ℝ^n)}

namespace HsRestrictionSpace

/-- Realize a Bessel restriction class in the intrinsic Gagliardo space by restricting
the whole-space Gagliardo element corresponding to its minimal Bessel extension. -/
def toGagliardoCLM
    (hs0 : 0 < s) (hs1 : s < 1) (Ω : Set (ℝ^n)) :
    HsRestrictionSpace n s hs0.le Ω →L[ℝ] W^{s,2}(Ω) :=
  (GagliardoSpace.restrictCLM (Set.subset_univ Ω)).comp
    ((GagliardoSpace.equivHsSpaceReal hs0 hs1).symm.toContinuousLinearMap.comp
      (minimalExtension n s hs0.le Ω))

/-- The intrinsic realization preserves the physical `L²(Ω)` class. -/
@[simp]
theorem toLp_toGagliardoCLM
    (hs0 : 0 < s) (hs1 : s < 1)
    (q : HsRestrictionSpace n s hs0.le Ω) :
    GagliardoSpace.toLp n s Ω (toGagliardoCLM hs0 hs1 Ω q) =
      toLp n s hs0.le Ω q := by
  change GagliardoSpace.toLp n s Ω
    (GagliardoSpace.restrictCLM (Set.subset_univ Ω)
      ((GagliardoSpace.equivHsSpaceReal hs0 hs1).symm
        (minimalExtension n s hs0.le Ω q))) = _
  rw [GagliardoSpace.toLp_restrictCLM_eq_hsRestrictionCLM hs0 hs1,
    ContinuousLinearEquiv.apply_symm_apply, toLp_minimalExtension]

/-- Distinct restriction classes have distinct intrinsic Gagliardo realizations. -/
theorem toGagliardoCLM_injective
    (hs0 : 0 < s) (hs1 : s < 1) :
    Function.Injective (toGagliardoCLM hs0 hs1 Ω) := by
  intro q₁ q₂ h
  apply toLp_injective hs0.le
  simpa only [toLp_toGagliardoCLM] using congrArg (GagliardoSpace.toLp n s Ω) h

/-- Realizing the restriction of a whole-space Bessel element agrees with directly
restricting its whole-space Gagliardo counterpart. -/
@[simp]
theorem toGagliardoCLM_ofWholeSpace
    (hs0 : 0 < s) (hs1 : s < 1)
    (u : HsSpaceReal n s) :
    toGagliardoCLM hs0 hs1 Ω (ofWholeSpace n s hs0.le Ω u) =
      GagliardoSpace.restrictCLM (Set.subset_univ Ω)
        ((GagliardoSpace.equivHsSpaceReal hs0 hs1).symm u) := by
  apply GagliardoSpace.toLp_injective
  rw [toLp_toGagliardoCLM, toLp_ofWholeSpace,
    GagliardoSpace.toLp_restrictCLM_eq_hsRestrictionCLM hs0 hs1,
    ContinuousLinearEquiv.apply_symm_apply]

/-- The intrinsic realization is bounded by the inverse whole-space comparison constant.
The minimal extension has exactly the quotient norm, and restriction is contractive. -/
theorem norm_toGagliardoCLM_apply_le
    (hn : 1 ≤ n) (hs0 : 0 < s) (hs1 : s < 1)
    (q : HsRestrictionSpace n s hs0.le Ω) :
    ‖toGagliardoCLM hs0 hs1 Ω q‖ ≤
      (1 + √(gagliardoFourierConstant n s hn)) * ‖q‖ := by
  calc
    ‖toGagliardoCLM hs0 hs1 Ω q‖ ≤
        ‖(GagliardoSpace.equivHsSpaceReal hs0 hs1).symm
          (minimalExtension n s hs0.le Ω q)‖ :=
      GagliardoSpace.norm_restrictCLM_apply_le (Set.subset_univ Ω) _
    _ ≤ (1 + √(gagliardoFourierConstant n s hn)) *
        ‖minimalExtension n s hs0.le Ω q‖ :=
      GagliardoSpace.norm_equivHsSpaceReal_symm_le hn hs0 hs1 _
    _ = (1 + √(gagliardoFourierConstant n s hn)) * ‖q‖ := by
      rw [norm_minimalExtension]

/-- The operator norm of the intrinsic realization is controlled by the same Fourier constant. -/
theorem norm_toGagliardoCLM_le
    (hn : 1 ≤ n) (hs0 : 0 < s) (hs1 : s < 1) :
    ‖toGagliardoCLM hs0 hs1 Ω‖ ≤ 1 + √(gagliardoFourierConstant n s hn) :=
  (toGagliardoCLM hs0 hs1 Ω).opNorm_le_bound
    (add_nonneg zero_le_one (Real.sqrt_nonneg _))
    (norm_toGagliardoCLM_apply_le hn hs0 hs1)

/-- The image of the intrinsic realization consists exactly of the elements admitting
a whole-space Gagliardo extension. -/
theorem range_toGagliardoCLM
    (hs0 : 0 < s) (hs1 : s < 1) :
    Set.range (toGagliardoCLM hs0 hs1 Ω) =
      Set.range (GagliardoSpace.restrictCLM (n := n) (s := s) (Set.subset_univ Ω)) := by
  ext u
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨(GagliardoSpace.equivHsSpaceReal hs0 hs1).symm
      (minimalExtension n s hs0.le Ω q), rfl⟩
  · rintro ⟨v, rfl⟩
    refine ⟨ofWholeSpace n s hs0.le Ω (GagliardoSpace.equivHsSpaceReal hs0 hs1 v), ?_⟩
    rw [toGagliardoCLM_ofWholeSpace, ContinuousLinearEquiv.symm_apply_apply]

end HsRestrictionSpace
end SobolevSpace.Fractional
