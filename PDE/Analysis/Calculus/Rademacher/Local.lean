/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Rademacher

/-!
# Rademacher's theorem on an open domain

A locally Lipschitz map on an open subset of a finite-dimensional real space is
differentiable almost everywhere there, for any additive Haar measure. This is Rademacher's
theorem, `LocallyLipschitzOn.ae_differentiableAt`. Evans, §5.8.3, Theorem 6, states it for a
real-valued function on an open subset of `ℝ^n` and deduces it from his Theorem 5 on
`W^{1,p}_loc` functions with `p > n`; here the values lie in any finite-dimensional real
space. A countable subcover of Lipschitz neighborhoods reduces the statement to Mathlib's
`LipschitzOnWith.ae_differentiableWithinAt_of_mem`, Rademacher's theorem on a set.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.8.3, Theorem 6 (Rademacher's theorem), p. 296.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open Filter MeasureTheory MeasureTheory.Measure Set
open scoped Topology

/-- A locally Lipschitz map between finite-dimensional real spaces is differentiable
almost everywhere on its open domain, with respect to any additive Haar measure. -/
theorem LocallyLipschitzOn.ae_differentiableAt
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {μ : Measure E} [IsAddHaarMeasure μ] {s : Set E} {f : E → F}
    (hf : LocallyLipschitzOn s f) (hs : IsOpen s) :
    ∀ᵐ x ∂μ.restrict s, DifferentiableAt ℝ f x := by
  classical
  have hlocal (x : s) :
      ∃ t : Set E, IsOpen t ∧ x.val ∈ t ∧ ∃ K, LipschitzOnWith K f t := by
    obtain ⟨K, t, ht, hK⟩ := hf x.property
    rw [hs.nhdsWithin_eq x.property] at ht
    exact ⟨interior t, isOpen_interior, mem_interior_iff_mem_nhds.mpr ht,
      K, hK.mono interior_subset⟩
  choose t ht hmem K hK using hlocal
  obtain ⟨c, hc, hcover⟩ :=
    (HereditarilyLindelofSpace.isLindelof s).elim_countable_subcover t ht
      (fun x hx ↦ mem_iUnion.mpr ⟨⟨x, hx⟩, hmem ⟨x, hx⟩⟩)
  have hgood : ∀ x ∈ c, ∀ᵐ y ∂μ, y ∈ t x → DifferentiableAt ℝ f y := by
    intro x _
    filter_upwards [(hK x).ae_differentiableWithinAt_of_mem (μ := μ)] with y hy hyt
    exact (hy hyt).differentiableAt ((ht x).mem_nhds hyt)
  rw [ae_restrict_iff' hs.measurableSet]
  filter_upwards [ae_ball_iff hc |>.mpr hgood] with y hy hys
  obtain ⟨x, hxc, hyt⟩ := mem_iUnion₂.mp (hcover hys)
  exact hy x hxc hyt
