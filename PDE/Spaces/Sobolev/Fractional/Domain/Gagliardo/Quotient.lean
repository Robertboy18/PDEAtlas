/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Restriction
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Gagliardo.Equivalence

/-!
# Gagliardo restriction quotients

For `0 < s < 1` in every dimension, the whole-space Gagliardo–Bessel equivalence preserves
physical `L²` restriction to every set `Ω`. It therefore identifies the restriction
kernels and descends to an equivalence of their quotients. For `1 ≤ n`, the quotient
maps retain the two explicit bounds in terms of the Gagliardo–Fourier constant. No geometric
assumption on `Ω` is needed.
-/

@[expose] public section

noncomputable section

open scoped FractionalSobolev

open MeasureTheory

namespace SobolevSpace.Fractional

variable {n : ℕ} {s : ℝ} {Ω : Set (ℝ^n)}

namespace GagliardoSpace

/-- Restriction of a whole-space graph element agrees with restriction of its physical
`L²` class, including the identification of volume restricted to `univ`. -/
theorem toLp_restrictCLM_univ (u : W^{s,2}(ℝ^n)) :
    toLp n s Ω (restrictCLM (Set.subset_univ Ω) u) =
      restrictL2 n Ω (toL2CLM n s u) := by
  apply Lp.ext
  have hphysical :
      (toL2CLM n s u : ℝ^n → ℝ)
        =ᵐ[(volume : Measure (ℝ^n)).restrict Ω] (toLp n s Set.univ u : ℝ^n → ℝ) :=
    ae_restrict_of_ae (s := Ω) (toL2CLM_apply_ae u)
  exact (toLp_restrictCLM_apply_ae (Set.subset_univ Ω) u).trans
    (hphysical.symm.trans
      (Lp.restrictionCLMOfLE_apply_ae
        Measure.restrict_le_self (toL2CLM n s u)).symm)

/-- The whole-space equivalence commutes with physical restriction to any set. -/
theorem toLp_restrictCLM_eq_hsRestrictionCLM
    (hs0 : 0 < s) (hs1 : s < 1)
    (u : W^{s,2}(ℝ^n)) :
    toLp n s Ω (restrictCLM (Set.subset_univ Ω) u) =
      hsRestrictionCLM n s hs0.le Ω (equivHsSpaceReal hs0 hs1 u) := by
  rw [toLp_restrictCLM_univ]
  change _ = restrictL2 n Ω (HsSpaceReal.toL2FunCLM n hs0.le _)
  rw [toL2FunCLM_equivHsSpaceReal]

/-- Vanishing on a set is preserved by the whole-space Gagliardo–Bessel equivalence. -/
theorem restrictCLM_eq_zero_iff_hsRestrictionCLM_eq_zero
    (hs0 : 0 < s) (hs1 : s < 1)
    (u : W^{s,2}(ℝ^n)) :
    restrictCLM (Set.subset_univ Ω) u = 0 ↔
      hsRestrictionCLM n s hs0.le Ω (equivHsSpaceReal hs0 hs1 u) = 0 := by
  rw [← toLp_restrictCLM_eq_hsRestrictionCLM hs0 hs1 u]
  constructor
  · intro h
    rw [h, map_zero]
  · intro h
    apply toLp_injective
    simpa only [map_zero] using h

/-- The quotient of the whole-space Gagliardo space by the kernel of restriction to `Ω`
is continuously real-linearly equivalent to the Bessel restriction space on `Ω`. -/
def quotientEquivHsRestrictionSpace
    (hs0 : 0 < s) (hs1 : s < 1) (Ω : Set (ℝ^n)) :
    (W^{s,2}(ℝ^n; ℝ) ⧸
      (restrictCLM (n := n) (s := s) (p := 2) (F := ℝ) (Set.subset_univ Ω)).ker) ≃L[ℝ]
        HsRestrictionSpace n s hs0.le Ω :=
  ContinuousLinearMap.KernelQuotient.congr
    (restrictCLM (n := n) (s := s) (p := 2) (F := ℝ) (Set.subset_univ Ω))
    (hsRestrictionCLM n s hs0.le Ω)
    (equivHsSpaceReal hs0 hs1)
    (restrictCLM_eq_zero_iff_hsRestrictionCLM_eq_zero hs0 hs1)

/-- On representatives, the quotient equivalence is the whole-space equivalence followed
by passage to the Bessel restriction class. -/
@[simp]
theorem quotientEquivHsRestrictionSpace_mk
    (hs0 : 0 < s) (hs1 : s < 1)
    (u : W^{s,2}(ℝ^n)) :
    quotientEquivHsRestrictionSpace hs0 hs1 Ω (Submodule.Quotient.mk u) =
      HsRestrictionSpace.ofWholeSpace n s hs0.le Ω (equivHsSpaceReal hs0 hs1 u) :=
  rfl

/-- The forward quotient map has the same explicit bound as the whole-space equivalence. -/
theorem norm_quotientEquivHsRestrictionSpace_le
    (hn : 1 ≤ n) (hs0 : 0 < s) (hs1 : s < 1)
    (q : W^{s,2}(ℝ^n; ℝ) ⧸
      (restrictCLM (n := n) (s := s) (p := 2) (F := ℝ) (Set.subset_univ Ω)).ker) :
    ‖quotientEquivHsRestrictionSpace hs0 hs1 Ω q‖ ≤
      (1 + (√(gagliardoFourierConstant n s hn))⁻¹) * ‖q‖ :=
  ContinuousLinearMap.KernelQuotient.norm_map_apply_le
    (restrictCLM (n := n) (s := s) (p := 2) (F := ℝ) (Set.subset_univ Ω))
    (hsRestrictionCLM n s hs0.le Ω)
    (equivHsSpaceReal hs0 hs1).toContinuousLinearMap
    (fun u h ↦ (restrictCLM_eq_zero_iff_hsRestrictionCLM_eq_zero hs0 hs1 u).mp h)
    (norm_equivHsSpaceReal_le hn hs0 hs1) q

/-- The inverse quotient map retains the whole-space bound with the same Fourier constant. -/
theorem norm_quotientEquivHsRestrictionSpace_symm_le
    (hn : 1 ≤ n) (hs0 : 0 < s) (hs1 : s < 1)
    (q : HsRestrictionSpace n s hs0.le Ω) :
    ‖(quotientEquivHsRestrictionSpace hs0 hs1 Ω).symm q‖ ≤
      (1 + √(gagliardoFourierConstant n s hn)) * ‖q‖ :=
  ContinuousLinearMap.KernelQuotient.norm_map_apply_le
    (hsRestrictionCLM n s hs0.le Ω)
    (restrictCLM (n := n) (s := s) (p := 2) (F := ℝ) (Set.subset_univ Ω))
    (equivHsSpaceReal hs0 hs1).symm.toContinuousLinearMap
    (fun v h ↦
      (restrictCLM_eq_zero_iff_hsRestrictionCLM_eq_zero hs0 hs1
        ((equivHsSpaceReal hs0 hs1).symm v)).mpr (by simpa using h))
    (norm_equivHsSpaceReal_symm_le hn hs0 hs1) q

end GagliardoSpace

end SobolevSpace.Fractional
