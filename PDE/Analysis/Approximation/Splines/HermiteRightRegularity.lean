/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.Splines.HermiteCompactProfile
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Right derivatives of the curvature of a Hermite spline

The exact second-jet matching equations identify the classical curvature with
either adjacent polynomial at a knot. On a half-open panel its right derivative
is the third jet of that panel. The third jets need not match across a knot.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology

namespace CAS.Splines

/-- Half-open panels cover the knot interval with its final endpoint removed.
A shared knot belongs to the panel on its right. -/
theorem StrictKnotMesh.exists_mem_panel_Ico
    {panels : ℕ} (mesh : StrictKnotMesh panels) (hpanels : 0 < panels) {x : ℝ}
    (hx : x ∈ Ico (mesh.knot 0) (mesh.knot (Fin.last panels))) :
    ∃ i : Fin panels, x ∈ Ico (mesh.panelLeft i) (mesh.panelRight i) := by
  obtain ⟨i, hi⟩ := mesh.exists_mem_panel_of_mem_Icc hpanels ⟨hx.1, hx.2.le⟩
  by_cases hright : x < mesh.panelRight i
  · exact ⟨i, hi.1, hright⟩
  · have heq : x = mesh.panelRight i := le_antisymm hi.2 (le_of_not_gt hright)
    have hnext : i.val + 1 < panels := by
      by_contra hn
      have hlast : i.succ = Fin.last panels := by
        apply Fin.ext
        change i.val + 1 = panels
        omega
      have hendpoint : mesh.panelRight i = mesh.knot (Fin.last panels) := by
        rw [StrictKnotMesh.panelRight, hlast]
      exact (ne_of_lt hx.2) (heq.trans hendpoint)
    refine ⟨StrictKnotMesh.rightNeighbor i hnext, ?_⟩
    rw [heq, mesh.panelRight_eq_panelLeft_rightNeighbor i hnext]
    exact ⟨le_rfl, mesh.panelLeft_lt_panelRight _⟩

namespace HermiteData

variable {panels : ℕ}

/-- Shared first jets identify the derivative on a closed panel, including its endpoints. -/
theorem deriv_assembledEvaluator_eq_piece
    (data : HermiteData panels) (mesh : StrictKnotMesh panels)
    (i : Fin panels) {x : ℝ}
    (hx : x ∈ Icc (mesh.panelLeft i) (mesh.panelRight i)) :
    deriv (data.assembledEvaluator mesh) x =
      ((data.polynomialData mesh).piece i).derivative.eval x := by
  have hf := (data.contDiff_assembledEvaluator mesh).differentiable (by norm_num)
  exact (uniqueDiffOn_Icc (mesh.panelLeft_lt_panelRight i) x hx).eq_deriv _
    (hf x).hasDerivAt.hasDerivWithinAt
    ((((data.polynomialData mesh).piece i).hasDerivAt x).hasDerivWithinAt.congr_of_mem
      (fun y hy ↦ data.assembledEvaluator_eq_piece mesh i hy) hx)

/-- Exact second-jet matching identifies curvature on both sides of a closed panel. -/
theorem deriv_deriv_assembledEvaluator_eq_piece
    (data : HermiteData panels) (mesh : StrictKnotMesh panels)
    (heq : data.C2SlopeEquations mesh) (i : Fin panels) {x : ℝ}
    (hx : x ∈ Icc (mesh.panelLeft i) (mesh.panelRight i)) :
    deriv (deriv (data.assembledEvaluator mesh)) x =
      ((data.polynomialData mesh).piece i).derivative.derivative.eval x := by
  have hf := (data.contDiff_two_assembledEvaluator mesh heq).differentiable_deriv_two
  exact (uniqueDiffOn_Icc (mesh.panelLeft_lt_panelRight i) x hx).eq_deriv _
    (hf x).hasDerivAt.hasDerivWithinAt
    ((((data.polynomialData mesh).piece i).derivative.hasDerivAt x
      ).hasDerivWithinAt.congr_of_mem
      (fun y hy ↦ data.deriv_assembledEvaluator_eq_piece mesh i hy) hx)

/-- Inside the support, curvature of the compact profile agrees with every
containing closed panel, including either side of an interior knot. -/
theorem deriv_deriv_compactOddProfile_eq_piece
    (data : HermiteData (panels + 1)) (mesh : StrictKnotMesh (panels + 1))
    (hmesh : mesh.knot 0 = 0) (hzero : data.value 0 = 0)
    (heq : data.C2SlopeEquations mesh) (i : Fin (panels + 1)) {x : ℝ}
    (hx : x ∈ Ioo 0 (mesh.knot (Fin.last (panels + 1))))
    (hpanel : x ∈ Icc (mesh.panelLeft i) (mesh.panelRight i)) :
    deriv (deriv (data.compactOddProfile mesh)) x =
      ((data.polynomialData mesh).piece i).derivative.derivative.eval x := by
  have hg : data.compactOddProfile mesh =ᶠ[𝓝 x] data.assembledEvaluator mesh :=
    Filter.mem_of_superset (Ioo_mem_nhds hx.1 hx.2) fun _ hy ↦
      data.compactOddProfile_eq_assembled mesh hmesh hzero ⟨hy.1.le, hy.2.le⟩
  exact hg.deriv.deriv_eq.trans
    (data.deriv_deriv_assembledEvaluator_eq_piece mesh heq i hpanel)

/-- On a half-open panel the curvature has the right derivative
given by that panel's third polynomial jet. No classical third derivative
at the left knot is assumed. -/
theorem hasDerivWithinAt_deriv_deriv_compactOddProfile_right
    (data : HermiteData (panels + 1)) (mesh : StrictKnotMesh (panels + 1))
    (hmesh : mesh.knot 0 = 0) (hzero : data.value 0 = 0)
    (heq : data.C2SlopeEquations mesh) (i : Fin (panels + 1)) {x : ℝ}
    (hx : x ∈ Ioo 0 (mesh.knot (Fin.last (panels + 1))))
    (hpanel : x ∈ Ico (mesh.panelLeft i) (mesh.panelRight i)) :
    HasDerivWithinAt (deriv (deriv (data.compactOddProfile mesh)))
      (((data.polynomialData mesh).piece i).derivative.derivative.derivative.eval x)
      (Ioi x) x := by
  apply (((data.polynomialData mesh).piece i).derivative.derivative.hasDerivAt x
    ).hasDerivWithinAt.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hpanel.2),
      nhdsWithin_le_nhds (Iio_mem_nhds hx.2)] with y hy hright hend
    exact data.deriv_deriv_compactOddProfile_eq_piece mesh hmesh hzero heq i
      ⟨hx.1.trans hy, hend⟩ ⟨hpanel.1.trans hy.le, hright.le⟩
  · exact data.deriv_deriv_compactOddProfile_eq_piece mesh hmesh hzero heq i hx
      ⟨hpanel.1, hpanel.2.le⟩

/-- Every strictly positive interior point, including every mesh knot,
has a right derivative of the curvature. -/
theorem differentiableWithinAt_deriv_deriv_compactOddProfile_right
    (data : HermiteData (panels + 1)) (mesh : StrictKnotMesh (panels + 1))
    (hmesh : mesh.knot 0 = 0) (hzero : data.value 0 = 0)
    (heq : data.C2SlopeEquations mesh) {x : ℝ}
    (hx : x ∈ Ioo 0 (mesh.knot (Fin.last (panels + 1)))) :
    DifferentiableWithinAt ℝ (deriv (deriv (data.compactOddProfile mesh))) (Ioi x) x := by
  have hmem : x ∈ Ico (mesh.knot 0) (mesh.knot (Fin.last (panels + 1))) := by
    rw [hmesh]
    exact ⟨hx.1.le, hx.2⟩
  obtain ⟨i, hi⟩ := mesh.exists_mem_panel_Ico (Nat.succ_pos _) hmem
  exact (data.hasDerivWithinAt_deriv_deriv_compactOddProfile_right mesh hmesh hzero
    heq i hx hi).differentiableWithinAt

end HermiteData

end CAS.Splines
