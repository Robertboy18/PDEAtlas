/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.SphericalBessel.Enclosure
public import CAS.CEGA
public meta import PDE.Analysis.SpecialFunctions.SphericalBessel.Enclosure
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses

/-!
# Certified values of spherical Bessel functions

Each value below is proved by comparing the rational endpoints of `sphericalBesselInterval`
with the stated bounds by `cega`, checked in the kernel. The examples cover the regimes of the
evaluator: the series far below the turning point (`j_100 1`, about `7.4 × 10 ^ (-190)`, where
the two terms of the Rayleigh form have size about `10 ^ 187`), the series at the turning point
(`j_100 100`), the series in the oscillatory range, where its terms reach `e ^ 50 / 50`
(`j_2 50`), and the Rayleigh form (`j_3 1000`). A certified sign change locates the first zero
of `j_1` in `(4.49, 4.5)`.
-/

@[expose] public section

namespace PDE.Analysis.SpecialFunctions

/-- `j_100 1 = 7.444727741661076890… × 10 ^ (-190)`. -/
theorem sphericalBesselJ_hundred_one_mem :
    sphericalBesselJ 100 1 ∈
      Set.Icc (7444727741661076890 / 10 ^ 208 : ℝ) (7444727741661076891 / 10 ^ 208) := by
  have h : sphericalBesselJ 100 ((1 : ℚ) : ℝ) ∈
      Set.Icc (((7444727741661076890 / 10 ^ 208 : ℚ)) : ℝ) ((7444727741661076891 / 10 ^ 208 : ℚ)) :=
    sphericalBesselJ_mem_Icc_of_le (by cega) (by cega)
  simpa using h

/-- `j_100 100 = 0.010880477011438336…`, at the turning point of the order. -/
theorem sphericalBesselJ_hundred_hundred_mem :
    sphericalBesselJ 100 100 ∈
      Set.Icc (10880477011438336 / 10 ^ 18 : ℝ) (10880477011438337 / 10 ^ 18) := by
  have h : sphericalBesselJ 100 ((100 : ℚ) : ℝ) ∈
      Set.Icc (((10880477011438336 / 10 ^ 18 : ℚ)) : ℝ) ((10880477011438337 / 10 ^ 18 : ℚ)) :=
    sphericalBesselJ_mem_Icc_of_le (by cega) (by cega)
  simpa using h

/-- `j_2 50 = 0.0040832408433991454…`, in the oscillatory range of the series. -/
theorem sphericalBesselJ_two_fifty_mem :
    sphericalBesselJ 2 50 ∈
      Set.Icc (40832408433991454 / 10 ^ 19 : ℝ) (40832408433991455 / 10 ^ 19) := by
  have h : sphericalBesselJ 2 ((50 : ℚ) : ℝ) ∈
      Set.Icc (((40832408433991454 / 10 ^ 19 : ℚ)) : ℝ) ((40832408433991455 / 10 ^ 19 : ℚ)) :=
    sphericalBesselJ_mem_Icc_of_le (by cega) (by cega)
  simpa using h

/-- `j_3 1000 = 0.00055740937576455972…`, from the Rayleigh form. -/
theorem sphericalBesselJ_three_thousand_mem :
    sphericalBesselJ 3 1000 ∈
      Set.Icc (55740937576455972 / 10 ^ 20 : ℝ) (55740937576455973 / 10 ^ 20) := by
  have h : sphericalBesselJ 3 ((1000 : ℚ) : ℝ) ∈
      Set.Icc (((55740937576455972 / 10 ^ 20 : ℚ)) : ℝ) ((55740937576455973 / 10 ^ 20 : ℚ)) :=
    sphericalBesselJ_mem_Icc_of_le (by cega) (by cega)
  simpa using h

/-- `j_1` has a zero in `(4.49, 4.5)`. -/
theorem exists_sphericalBesselJ_one_eq_zero :
    ∃ x ∈ Set.Ioo (449 / 100 : ℝ) (9 / 2), sphericalBesselJ 1 x = 0 := by
  have h := exists_sphericalBesselJ_eq_zero_of_sign_change (l := 1) (a := 449 / 100) (b := 9 / 2)
    (by norm_num) (Or.inl ⟨by cega, by cega⟩)
  simpa using h

end PDE.Analysis.SpecialFunctions
