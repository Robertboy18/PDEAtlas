/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Derivatives on level sets

The derivative of an arbitrary real-valued function on `ℝ` vanishes almost
everywhere on each level set. No regularity assumption is
needed: Mathlib defines `deriv` to be zero at points of nondifferentiability,
and the one-sided isolated points of a subset of the real line are countable.

The result is the level-set ingredient in one-dimensional nonsmooth Sobolev
chain rules. Its Sobolev counterpart is the statement `Du = 0` almost everywhere on
`{u = 0}` in Evans, §5.10, Problem 18. The countability is Mathlib's
`countable_setOfPred_isolated_right_within`, and at the remaining points the derivative
vanishes by `deriv_zero_of_frequently_const`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.10, Problem 18, p. 308.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace PDE.Analysis.Calculus

/-- The derivative of a real function vanishes almost everywhere on each
level set. -/
theorem ae_deriv_eq_zero_on_levelSet (f : ℝ → ℝ) (c : ℝ) :
    ∀ᵐ x ∂volume, f x = c → deriv f x = 0 := by
  let s : Set ℝ := {x | f x = c}
  let isolatedRight : Set ℝ :=
    {x ∈ s | 𝓝[s ∩ Ioi x] x = ⊥}
  have hcountable : isolatedRight.Countable := by
    exact countable_setOfPred_isolated_right_within
  filter_upwards
    [compl_mem_ae_iff.mpr (hcountable.measure_zero volume)] with x hx
  intro hfx
  have hxs : x ∈ s := hfx
  have hright : (𝓝[s ∩ Ioi x] x).NeBot := by
    rw [neBot_iff]
    intro hbot
    exact hx ⟨hxs, hbot⟩
  have hpunctured : (𝓝[s \ {x}] x).NeBot := by
    apply hright.mono
    apply nhdsWithin_mono
    rintro y ⟨hys, hxy⟩
    exact ⟨hys, by simpa using hxy.ne'⟩
  have hacc : AccPt x (𝓟 s) :=
    accPt_principal_iff_nhdsWithin.mpr hpunctured
  apply deriv_zero_of_frequently_const
  exact (accPt_iff_frequently_nhdsNE.mp hacc).mono fun _ hy ↦ hy

end PDE.Analysis.Calculus
