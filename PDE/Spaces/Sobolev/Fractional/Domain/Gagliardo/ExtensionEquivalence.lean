/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Gagliardo.Comparison

/-!
# Intrinsic and restriction spaces on fractional extension domains

A bounded extension from the intrinsic Gagliardo space to the whole space makes
the canonical map from the real restriction Hilbert space an equivalence.
The inverse extends an intrinsic element, applies the whole-space real
Gagliardo/Bessel equivalence, and takes its restriction quotient.

The construction and physical compatibility hold in every dimension. The explicit
operator bounds use the positive-dimensional Fourier constant. The resulting
equivalence is independent of the chosen extension, since its forward map is the
canonical `HsRestrictionSpace.toGagliardoCLM`.
-/

@[expose] public section

noncomputable section

open scoped FractionalSobolev

namespace SobolevSpace.Fractional

variable {n : ℕ} {s : ℝ} {Ω : Set (ℝ^n)}

namespace GagliardoSpace

/-- Extend an intrinsic element, realize it in the real whole-space Hilbert space,
and take its restriction quotient. -/
def toHsRestrictionCLMOfExtension (hs0 : 0 < s) (hs1 : s < 1)
    (E : W^{s,2}(Ω; ℝ) →L[ℝ]
      W^{s,2}(ℝ^n; ℝ)) :
    W^{s,2}(Ω; ℝ) →L[ℝ] HsRestrictionSpace n s hs0.le Ω :=
  (HsRestrictionSpace.ofWholeSpace n s hs0.le Ω).comp
    ((equivHsSpaceReal hs0 hs1).toContinuousLinearMap.comp E)

/-- The canonical comparison recovers an intrinsic element from any extension. -/
@[simp]
theorem toGagliardoCLM_toHsRestrictionCLMOfExtension (hs0 : 0 < s) (hs1 : s < 1)
    (E : W^{s,2}(Ω; ℝ) →L[ℝ]
      W^{s,2}(ℝ^n; ℝ))
    (hE : (restrictCLM (Set.subset_univ Ω)).comp E =
      ContinuousLinearMap.id ℝ (W^{s,2}(Ω; ℝ)))
    (u : W^{s,2}(Ω; ℝ)) :
    HsRestrictionSpace.toGagliardoCLM hs0 hs1 Ω
      (toHsRestrictionCLMOfExtension hs0 hs1 E u) = u := by
  change HsRestrictionSpace.toGagliardoCLM hs0 hs1 Ω
    (HsRestrictionSpace.ofWholeSpace n s hs0.le Ω (equivHsSpaceReal hs0 hs1 (E u))) = u
  rw [HsRestrictionSpace.toGagliardoCLM_ofWholeSpace,
    ContinuousLinearEquiv.symm_apply_apply]
  exact DFunLike.congr_fun hE u

/-- Injectivity of the canonical physical comparison gives the other inverse
identity on the restriction quotient. -/
@[simp]
theorem toHsRestrictionCLMOfExtension_toGagliardoCLM (hs0 : 0 < s) (hs1 : s < 1)
    (E : W^{s,2}(Ω; ℝ) →L[ℝ]
      W^{s,2}(ℝ^n; ℝ))
    (hE : (restrictCLM (Set.subset_univ Ω)).comp E =
      ContinuousLinearMap.id ℝ (W^{s,2}(Ω; ℝ)))
    (q : HsRestrictionSpace n s hs0.le Ω) :
    toHsRestrictionCLMOfExtension hs0 hs1 E
      (HsRestrictionSpace.toGagliardoCLM hs0 hs1 Ω q) = q := by
  apply HsRestrictionSpace.toGagliardoCLM_injective hs0 hs1
  exact toGagliardoCLM_toHsRestrictionCLMOfExtension hs0 hs1 E hE _

/-- The quotient obtained from an extension has the original physical `L²(Ω)`
realization. -/
@[simp]
theorem toLp_toHsRestrictionCLMOfExtension (hs0 : 0 < s) (hs1 : s < 1)
    (E : W^{s,2}(Ω; ℝ) →L[ℝ]
      W^{s,2}(ℝ^n; ℝ))
    (hE : (restrictCLM (Set.subset_univ Ω)).comp E =
      ContinuousLinearMap.id ℝ (W^{s,2}(Ω; ℝ)))
    (u : W^{s,2}(Ω; ℝ)) :
    HsRestrictionSpace.toLp n s hs0.le Ω (toHsRestrictionCLMOfExtension hs0 hs1 E u) =
      toLp n s Ω u := by
  rw [← HsRestrictionSpace.toLp_toGagliardoCLM hs0 hs1,
    toGagliardoCLM_toHsRestrictionCLMOfExtension hs0 hs1 E hE]

/-- Quantitative control of extension followed by the real whole-space comparison
and the contractive restriction quotient. -/
theorem norm_toHsRestrictionCLMOfExtension_apply_le (hn : 1 ≤ n)
    (hs0 : 0 < s) (hs1 : s < 1)
    (E : W^{s,2}(Ω; ℝ) →L[ℝ]
      W^{s,2}(ℝ^n; ℝ))
    (u : W^{s,2}(Ω; ℝ)) :
    ‖toHsRestrictionCLMOfExtension hs0 hs1 E u‖ ≤
      ((1 + (√(gagliardoFourierConstant n s hn))⁻¹) * ‖E‖) * ‖u‖ := by
  calc
    _ ≤ ‖equivHsSpaceReal hs0 hs1 (E u)‖ :=
      Submodule.Quotient.norm_mk_le (hsRestrictionCLM n s hs0.le Ω).ker _
    _ ≤ (1 + (√(gagliardoFourierConstant n s hn))⁻¹) * ‖E u‖ :=
      norm_equivHsSpaceReal_le hn hs0 hs1 _
    _ ≤ (1 + (√(gagliardoFourierConstant n s hn))⁻¹) * (‖E‖ * ‖u‖) :=
      mul_le_mul_of_nonneg_left (E.le_opNorm u) (by positivity)
    _ = _ := (mul_assoc _ _ _).symm

/-- Operator norm of the restriction map constructed from a bounded intrinsic
extension. No right-inverse hypothesis is needed for this estimate. -/
theorem norm_toHsRestrictionCLMOfExtension_le (hn : 1 ≤ n)
    (hs0 : 0 < s) (hs1 : s < 1)
    (E : W^{s,2}(Ω; ℝ) →L[ℝ]
      W^{s,2}(ℝ^n; ℝ)) :
    ‖toHsRestrictionCLMOfExtension hs0 hs1 E‖ ≤
      (1 + (√(gagliardoFourierConstant n s hn))⁻¹) * ‖E‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    (norm_toHsRestrictionCLMOfExtension_apply_le hn hs0 hs1 E)

/-- Different bounded extensions induce the same map into the physical restriction
quotient. -/
theorem toHsRestrictionCLMOfExtension_eq (hs0 : 0 < s) (hs1 : s < 1)
    (E F : W^{s,2}(Ω; ℝ) →L[ℝ]
      W^{s,2}(ℝ^n; ℝ))
    (hE : (restrictCLM (Set.subset_univ Ω)).comp E =
      ContinuousLinearMap.id ℝ (W^{s,2}(Ω; ℝ)))
    (hF : (restrictCLM (Set.subset_univ Ω)).comp F =
      ContinuousLinearMap.id ℝ (W^{s,2}(Ω; ℝ))) :
    toHsRestrictionCLMOfExtension hs0 hs1 E = toHsRestrictionCLMOfExtension hs0 hs1 F := by
  ext u
  apply HsRestrictionSpace.toLp_injective hs0.le
  rw [toLp_toHsRestrictionCLMOfExtension hs0 hs1 E hE,
    toLp_toHsRestrictionCLMOfExtension hs0 hs1 F hF]

end GagliardoSpace

namespace HsRestrictionSpace

/-- On an intrinsic fractional extension domain, the canonical physical comparison
is a continuous linear equivalence. -/
def equivGagliardoOfExtension (hs0 : 0 < s) (hs1 : s < 1)
    (E : W^{s,2}(Ω; ℝ) →L[ℝ]
      W^{s,2}(ℝ^n; ℝ))
    (hE : (GagliardoSpace.restrictCLM (Set.subset_univ Ω)).comp E =
      ContinuousLinearMap.id ℝ (W^{s,2}(Ω; ℝ))) :
    HsRestrictionSpace n s hs0.le Ω ≃L[ℝ] W^{s,2}(Ω; ℝ) :=
  ContinuousLinearEquiv.equivOfInverse (toGagliardoCLM hs0 hs1 Ω)
    (GagliardoSpace.toHsRestrictionCLMOfExtension hs0 hs1 E)
    (GagliardoSpace.toHsRestrictionCLMOfExtension_toGagliardoCLM hs0 hs1 E hE)
    (GagliardoSpace.toGagliardoCLM_toHsRestrictionCLMOfExtension hs0 hs1 E hE)

variable (hs0 : 0 < s) (hs1 : s < 1)
    (E : W^{s,2}(Ω; ℝ) →L[ℝ]
      W^{s,2}(ℝ^n; ℝ))
    (hE : (GagliardoSpace.restrictCLM (Set.subset_univ Ω)).comp E =
      ContinuousLinearMap.id ℝ (W^{s,2}(Ω; ℝ)))

/-- The forward map is the canonical physical comparison. -/
@[simp]
theorem equivGagliardoOfExtension_toContinuousLinearMap :
    (equivGagliardoOfExtension hs0 hs1 E hE).toContinuousLinearMap =
      toGagliardoCLM hs0 hs1 Ω :=
  rfl

/-- The inverse extends, applies the whole-space equivalence, and takes the
restriction quotient. -/
@[simp]
theorem equivGagliardoOfExtension_symm_toContinuousLinearMap :
    (equivGagliardoOfExtension hs0 hs1 E hE).symm.toContinuousLinearMap =
      GagliardoSpace.toHsRestrictionCLMOfExtension hs0 hs1 E :=
  rfl

/-- The forward equivalence preserves the physical `L²(Ω)` class. -/
@[simp]
theorem toLp_equivGagliardoOfExtension (q : HsRestrictionSpace n s hs0.le Ω) :
    GagliardoSpace.toLp n s Ω (equivGagliardoOfExtension hs0 hs1 E hE q) =
      toLp n s hs0.le Ω q :=
  toLp_toGagliardoCLM hs0 hs1 q

/-- The inverse equivalence preserves the physical `L²(Ω)` class. -/
@[simp]
theorem toLp_equivGagliardoOfExtension_symm (u : W^{s,2}(Ω; ℝ)) :
    toLp n s hs0.le Ω ((equivGagliardoOfExtension hs0 hs1 E hE).symm u) =
      GagliardoSpace.toLp n s Ω u :=
  GagliardoSpace.toLp_toHsRestrictionCLMOfExtension hs0 hs1 E hE u

/-- The canonical forward norm bound is independent of the extension operator. -/
theorem norm_equivGagliardoOfExtension_le (hn : 1 ≤ n) :
    ‖(equivGagliardoOfExtension hs0 hs1 E hE).toContinuousLinearMap‖ ≤
      1 + √(gagliardoFourierConstant n s hn) :=
  norm_toGagliardoCLM_le hn hs0 hs1

/-- The inverse bound consists of the whole-space comparison factor and the
intrinsic extension norm. -/
theorem norm_equivGagliardoOfExtension_symm_le (hn : 1 ≤ n) :
    ‖(equivGagliardoOfExtension hs0 hs1 E hE).symm.toContinuousLinearMap‖ ≤
      (1 + (√(gagliardoFourierConstant n s hn))⁻¹) * ‖E‖ :=
  GagliardoSpace.norm_toHsRestrictionCLMOfExtension_le hn hs0 hs1 E

/-- The domain equivalence does not depend on the chosen intrinsic extension.
This statement concerns restriction quotients, not boundary-surface chart norms. -/
theorem equivGagliardoOfExtension_eq
    (F : W^{s,2}(Ω; ℝ) →L[ℝ]
      W^{s,2}(ℝ^n; ℝ))
    (hF : (GagliardoSpace.restrictCLM (Set.subset_univ Ω)).comp F =
      ContinuousLinearMap.id ℝ (W^{s,2}(Ω; ℝ))) :
    equivGagliardoOfExtension hs0 hs1 E hE = equivGagliardoOfExtension hs0 hs1 F hF := by
  ext q
  rfl

end HsRestrictionSpace

end SobolevSpace.Fractional
