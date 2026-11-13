/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Extension.Reflection

/-!
# Scalar and quadratic even reflection

For scalar functions the base coordinate of the even reflection of `Reflection` agrees
with the even `Lp` extension, and the quadratic estimates retain the bound two.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal FractionalSobolev

namespace SobolevSpace.Fractional.Extension

open SobolevSpace.HalfSpace GagliardoSpace

variable {n : ℕ} [Fact (0 < n)] {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The canonical scalar `Lp` extension is represented by composition with folding. -/
theorem evenExtendLp_apply_ae_foldUpper (u : Lp ℝ p (volume.restrict ℝ^n₊)) :
    (evenExtendLp (n := n) (p := p) u : ℝ^n → ℝ) =ᵐ[volume]
      (u : ℝ^n → ℝ) ∘ foldUpper n := by
  filter_upwards [evenExtendLp_apply_ae_piecewise_of_ae_eq (n := n) (p := p) u
    (u : ℝ^n → ℝ) (ae_eq_refl _)] with x hx
  rw [hx]
  by_cases hxL : x (PDE.Common.lastIndex (n := n)) < 0 <;>
    simp [foldUpper, lower, hxL]

/-- The scalar base coordinate agrees with the even `Lp` extension. -/
@[simp] theorem toLp_evenReflection (hs : 0 ≤ (n : ℝ) / p.toReal + s)
    (u : W^{s,p}(ℝ^n₊)) :
    toLp n s Set.univ (evenReflection hs u) =
      evenExtendLp (n := n) (p := p) (toLp n s ℝ^n₊ u) := by
  apply Lp.ext
  simpa only [Measure.restrict_univ] using
    (toLp_evenReflection_apply_ae hs u).trans
      (evenExtendLp_apply_ae_foldUpper (toLp n s ℝ^n₊ u)).symm

/-- Intrinsic Gagliardo membership of the canonical scalar even `Lp` extension. -/
theorem memGagliardo_evenExtendLp (hs : 0 ≤ (n : ℝ) / p.toReal + s)
    (u : W^{s,p}(ℝ^n₊)) :
    MemGagliardo n s Set.univ
      (evenExtendLp (n := n) (p := p) (toLp n s ℝ^n₊ u)) (p := p) := by
  have hu : MemGagliardo n s ℝ^n₊ (toLp n s ℝ^n₊ u) (p := p) :=
    ⟨Lp.memLp _, toLp_mem_domain u⟩
  apply (memGagliardo_comp_foldUpper hs hu).congr_ae
  simpa only [Measure.restrict_univ] using
    (evenExtendLp_apply_ae_foldUpper (toLp n s ℝ^n₊ u)).symm

/-- Squared difference-quotient norms grow by at most four under even reflection. -/
theorem norm_differenceQuotient_evenReflection_sq_le (hs : 0 ≤ (n : ℝ) / 2 + s)
    (u : W^{s,2}(ℝ^n₊)) :
    ‖differenceQuotient n s Set.univ (evenReflection (p := 2) hs u)‖ ^ 2 ≤
      4 * ‖differenceQuotient n s ℝ^n₊ u‖ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    norm_differenceQuotient_evenReflection_rpow_le (by norm_num) hs u

/-- The full squared graph norm satisfies the separate base and seminorm estimate. -/
theorem norm_evenReflection_sq_le (hs : 0 ≤ (n : ℝ) / 2 + s)
    (u : W^{s,2}(ℝ^n₊)) :
    ‖evenReflection (p := 2) hs u‖ ^ 2 ≤
      2 * ‖toLp n s ℝ^n₊ u‖ ^ 2 + 4 * ‖differenceQuotient n s ℝ^n₊ u‖ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    norm_evenReflection_rpow_le (by norm_num) hs u

/-- At exponent two, even reflection has graph-norm bound two. -/
theorem norm_evenReflection_le (hs : 0 ≤ (n : ℝ) / 2 + s)
    (u : W^{s,2}(ℝ^n₊)) :
    ‖evenReflection (p := 2) hs u‖ ≤ 2 * ‖u‖ := by
  have h := norm_evenReflection_sq_le hs u
  have hu := norm_sq_eq u
  nlinarith [norm_nonneg u, norm_nonneg (evenReflection (p := 2) hs u),
    sq_nonneg ‖toLp n s ℝ^n₊ u‖]

/-- The scalar quadratic reflection operator has norm at most two. -/
theorem norm_evenReflectionCLM_le (hs : 0 ≤ (n : ℝ) / 2 + s) :
    ‖evenReflectionCLM (p := 2) (F := ℝ) hs‖ ≤ 2 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (norm_evenReflection_le hs)

end SobolevSpace.Fractional.Extension
