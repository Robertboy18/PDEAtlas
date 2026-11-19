/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.Localized.Interior

/-!
# Bounds for interior quotient tests

The cutoff terms depend only on the original field near the cutoff.
The signed backward test is bounded by a first derivative of the forward
field, using the sharp whole-space Sobolev quotient estimate. Neither
estimate introduces a boundary norm of the original input.
-/

@[expose] public noncomputable section

open TopologicalSpace
open scoped Distributions

namespace SobolevSpace.GraphSpace.DifferenceQuotient

open MeasureTheory Set
open SobolevSpace.Extension.Lp
open scoped ENNReal RealInnerProductSpace Sobolev

variable {n : ℕ} {Ω S : Set (ℝ^n)}

/-- A cutoff equal to one on a measurable set controls restriction to
that set with constant one. -/
theorem norm_restrict_le_testFunction_smul
    (hS : MeasurableSet S) (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hone : ∀ x ∈ S, η.toFun x = 1) (q : DerivLp n 2 univ) :
    ‖restrictDerivLp (subset_univ S) q‖ ≤ ‖testFunctionLpTop (Ω := univ) η • q‖ := by
  have heq : restrictDerivLp (subset_univ S) (testFunctionLpTop (Ω := univ) η • q) =
      restrictDerivLp (subset_univ S) q := by
    rw [restrictDerivLp_lpSMul hS, restrict_testFunctionLpTop]
    apply Lp.ext
    filter_upwards [mulLpLeft_apply_ae (testFunctionLpTop (Ω := S) η)
      (restrictDerivLp (subset_univ S) q), testFunctionLpTop_apply_ae (Ω := S) η,
      ae_restrict_mem hS] with x hx hη hxS
    simp only [mulLpLeft_apply] at hx
    rw [hx, hη, hone x hxS, one_mul]
  exact heq ▸ norm_restrictDerivLp_le (subset_univ S) (testFunctionLpTop (Ω := univ) η • q)

/-- A supported multiplier discards the part of its input outside the
supporting measurable set. -/
theorem testFunction_smul_zeroExtend_restrict
    (hS : MeasurableSet S) (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hη : tsupport η.toFun ⊆ S) (q : DerivLp n 2 univ) :
    testFunctionLpTop (Ω := univ) η •
        zeroExtendLp hS (restrictDerivLp (subset_univ S) q) =
      testFunctionLpTop (Ω := univ) η • q := by
  rw [← zeroExtendLp_restrict_lpSMul, restrict_testFunctionLpTop]
  exact zeroExtendLp_testFunction_smul_restrict hS η hη q

/-- A cutoff multiplier needs only the local `L²` norm of its input. -/
theorem norm_testFunction_smul_le_restrict
    (hS : MeasurableSet S) (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hη : tsupport η.toFun ⊆ S) (q : DerivLp n 2 univ) :
    ‖testFunctionLpTop (Ω := univ) η • q‖ ≤
      ‖testFunctionLpTop (Ω := univ) η‖ *
        ‖restrictDerivLp (subset_univ S) q‖ := by
  rw [← testFunction_smul_zeroExtend_restrict hS η hη q]
  simpa only [norm_zeroExtendLp] using Lp.norm_smul_le
    (testFunctionLpTop (Ω := univ) η) (zeroExtendLp hS (restrictDerivLp (subset_univ S) q))

/-- The derivative of a squared cutoff also discards data outside the
cutoff support, without enlarging that support. -/
theorem partialSquaredCutoff_smul_zeroExtend_restrict
    (hS : MeasurableSet S) (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hη : tsupport η.toFun ⊆ S) (i : Fin n) (q : DerivLp n 2 univ) :
    partialTestFunctionLpTop (Ω := univ) (squaredCutoff η) i •
        zeroExtendLp hS (restrictDerivLp (subset_univ S) q) =
      partialTestFunctionLpTop (Ω := univ) (squaredCutoff η) i • q := by
  rw [partialSquaredCutoff_smul, partialSquaredCutoff_smul]
  simp only [lpSMul_top_top_two_comm (testFunctionLpTop (Ω := univ) η),
    testFunction_smul_zeroExtend_restrict hS η hη q]

/-- The cutoff-error pairing is controlled by the localized principal
field and a local norm of the lower-order field. -/
theorem abs_inner_partialSquaredCutoff_le_restrict
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hη : tsupport η.toFun ⊆ S) (i : Fin n) (v q : DerivLp n 2 univ) :
    |⟪v, partialTestFunctionLpTop (Ω := univ) (squaredCutoff η) i • q⟫| ≤
      2 * ‖testFunctionLpTop (Ω := univ) η • v‖ *
        ‖partialTestFunctionLpTop (Ω := univ) η i‖ *
          ‖restrictDerivLp (subset_univ S) q‖ := by
  -- the bound with the (closed, hence measurable) support of `η`, then restrict further
  have hT : MeasurableSet (tsupport η.toFun) := (isClosed_tsupport _).measurableSet
  have hmain := partialSquaredCutoff_smul_zeroExtend_restrict hT η subset_rfl i q ▸
    abs_inner_partialSquaredCutoff_le η i v
      (zeroExtendLp hT (restrictDerivLp (subset_univ (tsupport η.toFun)) q))
  rw [norm_zeroExtendLp] at hmain
  refine hmain.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  rw [← restrictDerivLp_comp hη (subset_univ S)]
  exact norm_restrictDerivLp_le hη _

/-- The signed backward base coordinate is bounded by the forward
field's derivative in the quotient direction. -/
theorem norm_interior_backward_test_le
    (hΩ : IsOpen Ω) (hS : IsOpen S) (hSΩ : S ⊆ Ω)
    (χ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hχ : tsupport χ.toFun ⊆ Ω)
    (hone : ∀ x ∈ S, χ.toFun x = 1)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hη : tsupport η.toFun ⊆ S)
    (k : Fin n) {h : ℝ} (hh : h ≠ 0)
    (hshift : MapsTo (fun x ↦ x + coordinateStep k h) (tsupport η.toFun) S)
    (u : H¹(Ω)) :
    let E := zeroExtendLp (p := 2) hΩ.measurableSet
    ‖-restrictDerivLp (subset_univ Ω)
      (differenceQuotientLp 2 k (-h)
        (testFunctionLpTop (Ω := univ) (squaredCutoff η) •
          differenceQuotientLp 2 k h (E (u.val (baseIndex n 1)))))‖ ≤
      ‖testFunctionLpTop (Ω := univ) (squaredCutoff η) •
          differenceQuotientLp 2 k h (E (u.val (singleDerivIndex n k))) +
        partialTestFunctionLpTop (Ω := univ) (squaredCutoff η) k •
          differenceQuotientLp 2 k h (E (u.val (baseIndex n 1)))‖ := by
  let w := localizedDifferenceH10 hΩ η (hη.trans hSΩ) k h
    (cutoffH1ToH10 hΩ χ hχ u)
  let Z := ZeroTrace.zeroExtendH10 hΩ.measurableSet w
  obtain ⟨hbase, hderiv⟩ := zeroExtended_localizedDifference_cutoffH1ToH10
    hΩ hS hSΩ χ hχ hone η hη k h hshift u
  dsimp only
  rw [← hbase, ← hderiv k, norm_neg]
  exact (norm_restrictDerivLp_le _ _).trans
    (norm_differenceQuotientLp_base_le_deriv_of_ne_top 2 (by norm_num) k (neg_ne_zero.mpr hh) Z)

end SobolevSpace.GraphSpace.DifferenceQuotient
