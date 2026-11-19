/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.MaximumPrinciple
public import PDE.Parabolic.Heat.MaximumPrinciple.Strong

/-!
# Positive initial heat reaches the interior

The weak principle first keeps a supersolution nonnegative. If it were zero at an interior point at
positive time, the strong principle would force it to have been zero everywhere earlier, including
the initial point where it was positive. Thus a single positive initial value gives strict
positivity throughout a connected cylinder at every positive time.

Evans draws this conclusion from his §2.3.3(a), Theorem 4 for solutions with zero lateral values, as
an instance of infinite propagation speed. Our function is only a supersolution, its values on the
parabolic boundary are only nonnegative, and the positive initial value may sit at a point of the
closure.

## Main results

* `heat_supersolution_pos_of_initial_pos`: strict positivity in the spatial interior at every
  positive time, including the final time.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.3(a), Theorem 4 (Strong maximum principle for the heat
  equation), pp. 55-56, and the remark Infinite propagation speed again, p. 57.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace HeatEquation

open ParabolicMaximum Set

/-- Nonnegative parabolic boundary values and one positive initial value force
a heat supersolution to be strictly positive in the spatial interior at every
positive time, including the final time. -/
theorem heat_supersolution_pos_of_initial_pos {n : ℕ}
    {U : Set (ℝ^n)} {T : ℝ} {u : ℝ^n → ℝ → ℝ}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hcompact : IsCompact (closure U))
    (hucont : ContinuousOn (fun p : ℝ^n × ℝ ↦ u p.1 p.2) (closedCylinder U T))
    (huspace : ∀ x ∈ U, ∀ t ∈ Ioo 0 T, ContDiffAt ℝ 2 (fun y ↦ u y t) x)
    (hutime : ∀ x ∈ U, ∀ t ∈ Ioo 0 T, DifferentiableAt ℝ (u x) t)
    (hsuper : ∀ x ∈ U, ∀ t ∈ Ioo 0 T, 0 ≤ heatParabolicOperator u x t)
    (hboundary : ∀ p ∈ parabolicBoundary U T, 0 ≤ u p.1 p.2)
    (hinitial : ∃ y ∈ closure U, 0 < u y 0)
    {x : ℝ^n} (hx : x ∈ U) {t : ℝ} (ht : t ∈ Ioc 0 T) :
    0 < u x t := by
  have hnonneg := boundary_le_heat_supersolution hU ⟨x, hx⟩ hcompact
    (ht.1.trans_le ht.2) u hucont huspace hutime hsuper hboundary
  have hxclosed : (x, t) ∈ closedCylinder U T :=
    ⟨subset_closure hx, ht.1.le, ht.2⟩
  refine lt_of_le_of_ne (hnonneg _ hxclosed) ?_
  intro hzero
  have hmin : IsMinOn (fun p : ℝ^n × ℝ ↦ u p.1 p.2) (closedCylinder U T) (x, t) := by
    intro p hp
    change u x t ≤ u p.1 p.2
    rw [← hzero]
    exact hnonneg p hp
  have hconst := eqOn_const_of_isMinOn hU hconn hucont huspace hutime hx ht hsuper hmin
  obtain ⟨y, hy, hypos⟩ := hinitial
  have heq := hconst (show (y, 0) ∈ closedCylinder U t from ⟨hy, le_rfl, ht.1.le⟩)
  exact (ne_of_gt hypos) (heq.trans hzero.symm)

end HeatEquation
