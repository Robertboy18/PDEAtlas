/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean.SpaceTime

/-!
# Cylinders in canonical Euclidean spacetime

The cylinder `spaceTimeCylinder Ω I` is the set of spacetime points `(t, x)` with `t ∈ I` and
`x ∈ Ω`. The time-first continuous linear equivalence identifies it with the product `I × Ω`,
so it is open when both factors are open, bounded when both are bounded, and its closure is the
cylinder over `closure Ω` and `closure I` (also when `Ω` is empty).

For `I = Ioc 0 T`, with time written first, `spaceTimeCylinder U I` is the set `U_T = U × (0, T]`
of Evans, §2.4.3(a).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.4.3(a), p. 82.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

namespace PDE.Common

open Set

variable {n : ℕ}

/-- The spacetime cylinder with spatial base `Ω` and time set `I`. -/
def spaceTimeCylinder (Ω : Set (ℝ^n)) (I : Set ℝ) : Set (ℝ^(n + 1)) :=
  timeSpaceContinuousLinearEquiv n ⁻¹' (I ×ˢ Ω)

/-- Membership in a cylinder in curried coordinates. -/
@[simp]
theorem timeSpaceCons_mem_spaceTimeCylinder {Ω : Set (ℝ^n)} {I : Set ℝ}
    {t : ℝ} {x : ℝ^n} :
    timeSpaceCons t x ∈ spaceTimeCylinder Ω I ↔ t ∈ I ∧ x ∈ Ω := by
  simp [spaceTimeCylinder, time]

/-- Open factors give an open spacetime cylinder. -/
theorem isOpen_spaceTimeCylinder {Ω : Set (ℝ^n)} {I : Set ℝ}
    (hΩ : IsOpen Ω) (hI : IsOpen I) : IsOpen (spaceTimeCylinder Ω I) :=
  (hI.prod hΩ).preimage (timeSpaceContinuousLinearEquiv n).continuous

/-- Closure commutes with forming a spacetime cylinder. -/
theorem closure_spaceTimeCylinder (Ω : Set (ℝ^n)) (I : Set ℝ) :
    closure (spaceTimeCylinder Ω I) = spaceTimeCylinder (closure Ω) (closure I) := by
  change closure ((timeSpaceContinuousLinearEquiv n).toHomeomorph ⁻¹' (I ×ˢ Ω)) =
    (timeSpaceContinuousLinearEquiv n).toHomeomorph ⁻¹' (closure I ×ˢ closure Ω)
  rw [← (timeSpaceContinuousLinearEquiv n).toHomeomorph.preimage_closure, closure_prod_eq]

/-- A bounded base and bounded time interval give a bounded cylinder. -/
theorem isBounded_spaceTimeCylinder {Ω : Set (ℝ^n)} {I : Set ℝ}
    (hΩ : Bornology.IsBounded Ω) (hI : Bornology.IsBounded I) :
    Bornology.IsBounded (spaceTimeCylinder Ω I) := by
  have hK := (hI.isCompact_closure.prod hΩ.isCompact_closure).image
    (timeSpaceContinuousLinearEquiv n).symm.continuous
  apply hK.isBounded.subset
  intro p hp
  refine ⟨timeSpaceContinuousLinearEquiv n p, ?_, by simp⟩
  exact ⟨subset_closure hp.1, subset_closure hp.2⟩

end PDE.Common
