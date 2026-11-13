/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Extension.ReflectionQuadratic
public import PDE.Spaces.Sobolev.Fractional.Domain.Gagliardo.Comparison

/-!
# Intrinsic and Fourier definitions on a half-space

For `0 < s < 1`, every intrinsic Gagliardo element on the upper half-space extends
by even reflection. The whole-space Gagliardo–Bessel equivalence then gives a Bessel
restriction class with the same physical function. This makes the canonical injection
from the restriction space onto, and identifies the two spaces by a continuous
linear equivalence.

The inverse construction has bound `2 * (1 + 1 / √J)`, where `J` is the whole-space
Fourier comparison constant. The factor two comes from the intrinsic reflection
estimate. In the other direction, restriction retains the bound `1 + √J`.
Both maps preserve the physical `L²` class on the half-space.
-/

@[expose] public section

noncomputable section

open scoped FractionalSobolev

open SobolevSpace.HalfSpace

namespace SobolevSpace.Fractional

open SobolevSpace.Fractional.Extension

variable {n : ℕ} [Fact (0 < n)] {s : ℝ}

/-- Every intrinsic half-space element is realized by a Bessel restriction class:
even reflection supplies the extension required by the general range theorem. -/
theorem HsRestrictionSpace.toGagliardoCLM_halfSpace_surjective
    (hs0 : 0 < s) (hs1 : s < 1) :
    Function.Surjective (toGagliardoCLM hs0 hs1 (upper n)) := by
  intro u
  have hu : u ∈ Set.range
      (GagliardoSpace.restrictCLM (Set.subset_univ (upper n))) :=
    surjective_restrictCLM_halfSpace (add_nonneg (by positivity) hs0.le) u
  rwa [← range_toGagliardoCLM hs0 hs1] at hu

namespace GagliardoSpace

/-- Take the Bessel restriction class of the even extension. -/
def halfSpaceToRestrictionCLM (hs0 : 0 < s) (hs1 : s < 1) :
    W^{s,2}(ℝ^n₊) →L[ℝ] HsRestrictionSpace n s hs0.le (upper n) :=
  (HsRestrictionSpace.ofWholeSpace n s hs0.le (upper n)).comp
    ((equivHsSpaceReal hs0 hs1).toContinuousLinearMap.comp
      (evenReflectionCLM (add_nonneg (by positivity) hs0.le)))

/-- Intrinsic realization recovers the original half-space element. -/
@[simp]
theorem toGagliardoCLM_halfSpaceToRestrictionCLM
    (hs0 : 0 < s) (hs1 : s < 1) (u : W^{s,2}(ℝ^n₊)) :
    HsRestrictionSpace.toGagliardoCLM hs0 hs1 (upper n)
      (halfSpaceToRestrictionCLM hs0 hs1 u) = u := by
  change HsRestrictionSpace.toGagliardoCLM hs0 hs1 (upper n)
    (HsRestrictionSpace.ofWholeSpace n s hs0.le (upper n)
      (equivHsSpaceReal hs0 hs1
        (evenReflectionCLM (add_nonneg (by positivity) hs0.le) u))) = u
  rw [HsRestrictionSpace.toGagliardoCLM_ofWholeSpace,
    ContinuousLinearEquiv.symm_apply_apply, restrict_evenReflectionCLM]

/-- The extension construction also recovers every Bessel restriction class. -/
@[simp]
theorem halfSpaceToRestrictionCLM_toGagliardoCLM
    (hs0 : 0 < s) (hs1 : s < 1) (q : HsRestrictionSpace n s hs0.le (upper n)) :
    halfSpaceToRestrictionCLM hs0 hs1
      (HsRestrictionSpace.toGagliardoCLM hs0 hs1 (upper n) q) = q := by
  apply HsRestrictionSpace.toGagliardoCLM_injective hs0 hs1
  exact toGagliardoCLM_halfSpaceToRestrictionCLM hs0 hs1 _

/-- Reflection costs at most two in graph norm; taking a quotient is contractive. -/
theorem norm_halfSpaceToRestrictionCLM_apply_le
    (hs0 : 0 < s) (hs1 : s < 1) (u : W^{s,2}(ℝ^n₊)) :
    ‖halfSpaceToRestrictionCLM hs0 hs1 u‖ ≤
      ((1 + (√(gagliardoFourierConstant n s (Fact.out : 0 < n)))⁻¹) * 2) * ‖u‖ := by
  let hker : 0 ≤ (n : ℝ) / 2 + s := add_nonneg (by positivity) hs0.le
  calc
    _ ≤ ‖equivHsSpaceReal hs0 hs1 (evenReflectionCLM hker u)‖ :=
      Submodule.Quotient.norm_mk_le (hsRestrictionCLM n s hs0.le (upper n)).ker _
    _ ≤ (1 + (√(gagliardoFourierConstant n s (Fact.out : 0 < n)))⁻¹) *
        ‖evenReflectionCLM hker u‖ :=
      norm_equivHsSpaceReal_le (Fact.out : 0 < n) hs0 hs1 _
    _ ≤ (1 + (√(gagliardoFourierConstant n s (Fact.out : 0 < n)))⁻¹) * (2 * ‖u‖) :=
      mul_le_mul_of_nonneg_left (norm_evenReflection_le hker u) (by positivity)
    _ = _ := (mul_assoc _ _ _).symm

/-- Operator norm bound for the extension followed by Bessel restriction. -/
theorem norm_halfSpaceToRestrictionCLM_le (hs0 : 0 < s) (hs1 : s < 1) :
    ‖halfSpaceToRestrictionCLM (n := n) hs0 hs1‖ ≤
      (1 + (√(gagliardoFourierConstant n s (Fact.out : 0 < n)))⁻¹) * 2 :=
  (halfSpaceToRestrictionCLM hs0 hs1).opNorm_le_bound (by positivity)
    (norm_halfSpaceToRestrictionCLM_apply_le hs0 hs1)

/-- The restriction class represents the same physical `L²` function. -/
@[simp]
theorem toLp_halfSpaceToRestrictionCLM (hs0 : 0 < s) (hs1 : s < 1)
    (u : W^{s,2}(ℝ^n₊)) :
    HsRestrictionSpace.toLp n s hs0.le (upper n) (halfSpaceToRestrictionCLM hs0 hs1 u) =
      toLp n s (upper n) u := by
  have h := HsRestrictionSpace.toLp_toGagliardoCLM hs0 hs1
    (halfSpaceToRestrictionCLM hs0 hs1 u)
  rw [toGagliardoCLM_halfSpaceToRestrictionCLM] at h
  exact h.symm

/-- The intrinsic Gagliardo and Bessel restriction spaces on a half-space agree
as real Banach spaces, through their physical `L²` realization. -/
def halfSpaceEquivHsRestrictionSpace (hs0 : 0 < s) (hs1 : s < 1) :
    W^{s,2}(ℝ^n₊) ≃L[ℝ] HsRestrictionSpace n s hs0.le (upper n) :=
  ContinuousLinearEquiv.equivOfInverse (halfSpaceToRestrictionCLM hs0 hs1)
    (HsRestrictionSpace.toGagliardoCLM hs0 hs1 (upper n))
    (toGagliardoCLM_halfSpaceToRestrictionCLM hs0 hs1)
    (halfSpaceToRestrictionCLM_toGagliardoCLM hs0 hs1)

/-- The forward equivalence has the bound provided by even reflection. -/
theorem norm_halfSpaceEquivHsRestrictionSpace_le (hs0 : 0 < s) (hs1 : s < 1) :
    ‖(halfSpaceEquivHsRestrictionSpace (n := n) hs0 hs1).toContinuousLinearMap‖ ≤
      (1 + (√(gagliardoFourierConstant n s (Fact.out : 0 < n)))⁻¹) * 2 :=
  norm_halfSpaceToRestrictionCLM_le hs0 hs1

/-- The inverse equivalence retains the whole-space comparison bound. -/
theorem norm_halfSpaceEquivHsRestrictionSpace_symm_le (hs0 : 0 < s) (hs1 : s < 1) :
    ‖(halfSpaceEquivHsRestrictionSpace (n := n) hs0 hs1).symm.toContinuousLinearMap‖ ≤
      1 + √(gagliardoFourierConstant n s (Fact.out : 0 < n)) :=
  HsRestrictionSpace.norm_toGagliardoCLM_le (Fact.out : 0 < n) hs0 hs1

/-- Forward realization preserves the physical `L²` class. -/
theorem toLp_halfSpaceEquivHsRestrictionSpace (hs0 : 0 < s) (hs1 : s < 1)
    (u : W^{s,2}(ℝ^n₊)) :
    HsRestrictionSpace.toLp n s hs0.le (upper n)
      (halfSpaceEquivHsRestrictionSpace hs0 hs1 u) = toLp n s (upper n) u :=
  toLp_halfSpaceToRestrictionCLM hs0 hs1 u

/-- Inverse realization preserves the physical `L²` class. -/
theorem toLp_halfSpaceEquivHsRestrictionSpace_symm (hs0 : 0 < s) (hs1 : s < 1)
    (q : HsRestrictionSpace n s hs0.le (upper n)) :
    toLp n s (upper n) ((halfSpaceEquivHsRestrictionSpace hs0 hs1).symm q) =
      HsRestrictionSpace.toLp n s hs0.le (upper n) q :=
  HsRestrictionSpace.toLp_toGagliardoCLM hs0 hs1 q

end GagliardoSpace
end SobolevSpace.Fractional
