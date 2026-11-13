/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Quasilinear.Boundary.LocalizedTest

/-!
# A support buffer for the tangential energy test

The signed backward quotient of `η² Dₖʰu` is supported in the support of `η`
and its translate by `h eₖ`. A larger cutoff equal to one on both sets fixes
the test in the zero-trace space.
-/

@[expose] public noncomputable section

open scoped Sobolev

open TopologicalSpace
open scoped Distributions

namespace PDE.Elliptic.Regularity.Quasilinear

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity SobolevSpace.GraphSpace.DifferenceQuotient
open scoped ENNReal

variable {n : ℕ} [Fact (0 < n)]

/-- The forward test has a base representative supported where `η` is supported. -/
theorem baseCoord_localizedTangentialForward_ae
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n)) (h : ℝ)
    (u : H¹₀(HalfSpace.upper n)) :
    (baseCoordCLM (localizedTangentialForward η k hk h u) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n (HalfSpace.upper n)]
        fun x ↦ η.toFun x ^ 2 *
          tangentialDifferenceQuotientLp 2 k hk h (baseCoordCLM u) x := by
  rw [baseCoord_localizedTangentialForward]
  filter_upwards [Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞))
    (testFunctionLpTop (Ω := HalfSpace.upper n) (squaredCutoff η))
    (tangentialDifferenceQuotientLp 2 k hk h (baseCoordCLM u)),
    testFunctionLpTop_apply_ae (Ω := HalfSpace.upper n) (squaredCutoff η)] with x hx hη
  rw [hx]
  change testFunctionLpTop (Ω := HalfSpace.upper n) (squaredCutoff η) x *
      tangentialDifferenceQuotientLp 2 k hk h (baseCoordCLM u) x = _
  rw [hη]
  change (η.toFun x * η.toFun x) * _ = _
  rw [pow_two]

/-- The cutoff buffer fixes the exact signed backward difference-quotient
test. Only the base representative is used; the equality then holds in `H¹₀`. -/
theorem cutoffH10_localizedTangentialTest
    (χ η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n)) (h : ℝ)
    (hχ : ∀ x ∈ tsupport η.toFun, χ.toFun x = 1)
    (hshift : ∀ x ∈ tsupport η.toFun, χ.toFun (x + coordinateStep k h) = 1)
    (u : H¹₀(HalfSpace.upper n)) :
    cutoffH10 (HalfSpace.isOpen_upper n) χ (localizedTangentialTest η k hk h u) =
      localizedTangentialTest η k hk h u := by
  let w := localizedTangentialForward η k hk h u
  have hw : (baseCoordCLM w : ℝ^n → ℝ) =ᵐ[domainMeasure n (HalfSpace.upper n)]
      fun x ↦ η.toFun x ^ 2 *
        tangentialDifferenceQuotientLp 2 k hk h (baseCoordCLM u) x :=
    baseCoord_localizedTangentialForward_ae η k hk h u
  have hwt := (tangentialTranslation_measurePreserving k hk (-h)).quasiMeasurePreserving.ae_eq_comp
    hw
  apply cutoffH10_eq_self_of_base_ae
  have hbase : baseCoordCLM (localizedTangentialTest η k hk h u) =
      -tangentialDifferenceQuotientLp 2 k hk (-h) (baseCoordCLM w) := by
    rw [localizedTangentialTest, map_neg, baseCoord_tangentialDifferenceQuotientH10]
  rw [hbase]
  filter_upwards [Lp.coeFn_neg (tangentialDifferenceQuotientLp 2 k hk (-h) (baseCoordCLM w)),
    tangentialDifferenceQuotientLp.apply_ae 2 k hk (-h) (baseCoordCLM w),
    hw, hwt] with x hn hd hx ht
  rw [hn]
  change χ.toFun x *
    (-tangentialDifferenceQuotientLp 2 k hk (-h) (baseCoordCLM w) x) =
    -tangentialDifferenceQuotientLp 2 k hk (-h) (baseCoordCLM w) x
  rw [hd]
  by_cases hxχ : χ.toFun x = 1
  · rw [hxχ, one_mul]
  · have hxη : x ∉ tsupport η.toFun := fun hmem ↦ hxχ (hχ x hmem)
    have hxtη : x + coordinateStep k (-h) ∉ tsupport η.toFun := by
      intro hmem
      have hs := hshift (x + coordinateStep k (-h)) hmem
      have heq : x + coordinateStep k (-h) + coordinateStep k h = x := by
        simp [coordinateStep]
      rw [heq] at hs
      exact hxχ hs
    have hz : η.toFun x = 0 := image_eq_zero_of_notMem_tsupport hxη
    have hzt : η.toFun (x + coordinateStep k (-h)) = 0 :=
      image_eq_zero_of_notMem_tsupport hxtη
    change baseCoordCLM w (x + coordinateStep k (-h)) =
      η.toFun (x + coordinateStep k (-h)) ^ 2 *
        tangentialDifferenceQuotientLp 2 k hk h (baseCoordCLM u)
          (x + coordinateStep k (-h)) at ht
    rw [hx, ht, hz, hzt]
    simp only [zero_pow (by norm_num : 2 ≠ 0), zero_mul, sub_self, mul_zero, neg_zero]

end PDE.Elliptic.Regularity.Quasilinear
