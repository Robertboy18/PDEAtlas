/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Foundations.Representatives.Definitions

/-!
# Restriction of Representative-Level Sobolev Functions

The representative-level restriction map from a domain to a measurable subdomain, corresponding
to Evans §5.2.3, Theorem 1(iii), when both domains are open.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.2.3, Theorem 1(iii), p. 261.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace

open MeasureTheory Set Function ENNReal
open scoped NNReal

/-!
## Restriction to subdomains

The generalized weak-derivative relation is monotone under measurable restriction: data on `Ω`
restricts to any measurable `Ω' ⊆ Ω`. When both sets are open, this is the standard restriction map
`W^{k,p}(Ω) → W^{k,p}(Ω')` of Evans §5.2.3, Theorem 1(iii). For nonopen `Ω'`, the target retains the
generalized test-function interpretation documented above.

Since `SobolevSpaceOn` stores an explicit representative `toFun : ℝ^n → ℝ`, this is not a
quotient-level restriction. It keeps the same ambient function and restricts its `L^p` and
weak-derivative witnesses to the smaller domain.
-/

namespace SobolevSpaceOn

open MeasureTheory

variable {n k : ℕ} {p : ℝ≥0∞}
variable {Ω Ω' : Set (ℝ^n)}

/-- Restrict a packaged weak-derivative family from `Ω` to a smaller measurable set `Ω' ⊆ Ω`.
For open domains this is the usual Sobolev restriction. -/
noncomputable def restrict (hΩ' : MeasurableSet Ω') (hΩ'Ω : Ω' ⊆ Ω) :
    SobolevSpaceOn n k p Ω → SobolevSpaceOn n k p Ω' := fun u ↦
  { toFun := u.toFun
    memLp := by
      -- `MemLp` is monotone in the measure.
      simpa [domainMeasure, Measure.restrict_restrict_of_subset hΩ'Ω] using
        (u.memLp.restrict Ω')
    weak_derivs_inLp := by
      intro α hα
      rcases u.weak_derivs_inLp α hα with ⟨g, hgLp, hgWeak⟩
      refine ⟨g, ?_, ?_⟩
      · simpa [domainMeasure, Measure.restrict_restrict_of_subset hΩ'Ω] using
          (hgLp.restrict Ω')
      · exact (HasWeakDerivativeOn.mono (n := n) (Ω := Ω) (Ω' := Ω') (α := α)
          (hΩ' := hΩ') (hΩ'Ω := hΩ'Ω) hgWeak) }

/-- Domain restriction retains the ambient representative function. -/
@[simp] theorem restrict_toFun
    (hΩ' : MeasurableSet Ω') (hΩ'Ω : Ω' ⊆ Ω) (u : SobolevSpaceOn n k p Ω) :
    (restrict (n := n) (k := k) (p := p) (Ω := Ω) (Ω' := Ω') hΩ' hΩ'Ω u).toFun = u.toFun := rfl

/-- Restriction preserves every ambient point value, including values outside the smaller domain. -/
@[simp] theorem restrict_apply
    (hΩ' : MeasurableSet Ω') (hΩ'Ω : Ω' ⊆ Ω)
    (u : SobolevSpaceOn n k p Ω) (x : ℝ^n) :
    restrict (n := n) (k := k) (p := p) (Ω := Ω) (Ω' := Ω') hΩ' hΩ'Ω u x = u x :=
  rfl

/-- Restriction to the same measurable domain is the identity. -/
@[simp] theorem restrict_self (hΩ : MeasurableSet Ω) (u : SobolevSpaceOn n k p Ω) :
    restrict (n := n) (k := k) (p := p) (Ω := Ω) (Ω' := Ω) hΩ (Subset.rfl) u = u := by
  apply SobolevSpaceOn.ext
  rfl

/-- Successive representative restrictions agree with direct restriction. -/
theorem restrict_restrict {Ω'' : Set (ℝ^n)}
    (hΩ' : MeasurableSet Ω') (hΩ'' : MeasurableSet Ω'')
    (hΩ'Ω : Ω' ⊆ Ω) (hΩ''Ω' : Ω'' ⊆ Ω')
    (u : SobolevSpaceOn n k p Ω) :
    restrict (n := n) (k := k) (p := p) (Ω := Ω') (Ω' := Ω'') hΩ'' hΩ''Ω'
        (restrict (n := n) (k := k) (p := p) (Ω := Ω) (Ω' := Ω') hΩ' hΩ'Ω u) =
      restrict (n := n) (k := k) (p := p) (Ω := Ω) (Ω' := Ω'') hΩ''
        (hΩ''Ω'.trans hΩ'Ω) u := by
  apply SobolevSpaceOn.ext
  rfl

end SobolevSpaceOn

end SobolevSpace

end
