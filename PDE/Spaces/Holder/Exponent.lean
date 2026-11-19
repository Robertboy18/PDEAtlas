/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Basic.NNReal.Defs

/-!
# Hölder exponents

`HolderSpace.Exponent` is the type of Hölder exponents `γ` with `0 < γ ≤ 1`, the range fixed at the
start of Evans §5.1. It indexes the spaces `HolderSpace.C0GammaOn` and `HolderSpace.CKGammaOn`.
Mathlib's quantitative Hölder predicates `HolderWith` and `HolderOnWith` accept any exponent
`r : ℝ≥0`. The exponent `1` gives the Lipschitz condition, Evans §5.1, (1).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.1, (1)-(2), p. 254.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open NNReal

namespace HolderSpace

/-- A Hölder exponent in the classical range `0 < γ ≤ 1`.

This is a standard subtype rather than a project-specific structure, so the
ambient `NNReal` order and coercion API are available without duplication. -/
abbrev Exponent := {γ : ℝ≥0 // 0 < γ ∧ γ ≤ 1}

namespace Exponent

/-- A Hölder exponent is strictly positive. -/
theorem pos (γ : Exponent) : 0 < (γ : ℝ≥0) :=
  γ.property.1

/-- A classical Hölder exponent is at most one. -/
theorem le_one (γ : Exponent) : (γ : ℝ≥0) ≤ 1 :=
  γ.property.2

/-- The Lipschitz endpoint `γ = 1`. -/
instance : OfNat Exponent 1 where
  ofNat := ⟨1, zero_lt_one, le_rfl⟩

/-- The Lipschitz endpoint has underlying exponent one. -/
@[simp]
theorem coe_one : ((1 : Exponent) : ℝ≥0) = 1 :=
  rfl

end Exponent

end HolderSpace
