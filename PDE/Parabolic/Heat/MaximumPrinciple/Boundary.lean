/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.MaximumPrinciple

/-!
# Where a heat solution attains its extrema

On a bounded cylinder a continuous heat subsolution attains its maximum on the initial or lateral
boundary. A supersolution attains its minimum there. This is the attained-extremum form of part (i)
of Evans's §2.3.3(a), Theorem 4, for subsolutions and supersolutions.

Compactness supplies a boundary extremum; the weak principle shows that it also controls every
interior value. No connectedness is needed for this step.

## Main results

* `exists_isMaxOn_parabolicBoundary`, `exists_isMinOn_parabolicBoundary`: the boundary extrema.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.3(a), Theorem 4 (Strong maximum principle for the heat
  equation), pp. 55-56.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace HeatEquation

open ParabolicMaximum Set

variable {n : ℕ} {U : Set (ℝ^n)} {T : ℝ} {u : ℝ^n → ℝ → ℝ}
  (hU : IsOpen U) (hne : U.Nonempty) (hcompact : IsCompact (closure U)) (hT : 0 < T)
  (hucont : ContinuousOn (fun p : ℝ^n × ℝ ↦ u p.1 p.2) (closedCylinder U T))
  (huspace : ∀ x ∈ U, ∀ t ∈ Ioo 0 T, ContDiffAt ℝ 2 (fun y ↦ u y t) x)
  (hutime : ∀ x ∈ U, ∀ t ∈ Ioo 0 T, DifferentiableAt ℝ (u x) t)

include hU hne hcompact hT hucont huspace hutime

/-- A continuous heat subsolution attains its maximum on the parabolic boundary.
The maximizing value is also a maximum over the whole closed cylinder. -/
theorem exists_isMaxOn_parabolicBoundary
    (hsub : ∀ x ∈ U, ∀ t ∈ Ioo 0 T, heatParabolicOperator u x t ≤ 0) :
    ∃ p ∈ parabolicBoundary U T,
      IsMaxOn (fun q : ℝ^n × ℝ ↦ u q.1 q.2) (closedCylinder U T) p := by
  have hsubset : parabolicBoundary U T ⊆ closedCylinder U T := by
    intro p hp
    rcases hp with hp | hp
    · exact ⟨frontier_subset_closure hp.1, hp.2⟩
    · refine ⟨hp.1, ?_⟩
      have ht : p.2 = 0 := hp.2
      rw [ht]
      exact ⟨le_rfl, hT.le⟩
  have hboundary : IsCompact (parabolicBoundary U T) :=
    ((hcompact.of_isClosed_subset isClosed_frontier frontier_subset_closure).prod
      isCompact_Icc).union (hcompact.prod isCompact_singleton)
  obtain ⟨x, hx⟩ := hne
  have hboundary_ne : (parabolicBoundary U T).Nonempty :=
    ⟨(x, 0), Or.inr ⟨subset_closure hx, rfl⟩⟩
  obtain ⟨p, hp, hmax⟩ :=
    hboundary.exists_isMaxOn hboundary_ne (hucont.mono hsubset)
  exact ⟨p, hp, heat_subsolution_le_of_boundary_le hU ⟨x, hx⟩ hcompact hT
    u hucont huspace hutime hsub hmax⟩

/-- A continuous heat supersolution attains its minimum on the parabolic boundary.
This follows from the boundary maximum of its negative. -/
theorem exists_isMinOn_parabolicBoundary
    (hsuper : ∀ x ∈ U, ∀ t ∈ Ioo 0 T, 0 ≤ heatParabolicOperator u x t) :
    ∃ p ∈ parabolicBoundary U T,
      IsMinOn (fun q : ℝ^n × ℝ ↦ u q.1 q.2) (closedCylinder U T) p := by
  obtain ⟨p, hp, hmax⟩ := exists_isMaxOn_parabolicBoundary hU hne hcompact hT
    hucont.neg (fun x hx t ht ↦ (huspace x hx t ht).neg)
    (fun x hx t ht ↦ (hutime x hx t ht).neg) (u := fun x t ↦ -u x t)
    (fun x hx t ht ↦ by
      rw [heatParabolicOperator_neg]
      exact neg_nonpos.mpr (hsuper x hx t ht))
  exact ⟨p, hp, fun q hq ↦ neg_le_neg_iff.mp (hmax hq)⟩

end HeatEquation
