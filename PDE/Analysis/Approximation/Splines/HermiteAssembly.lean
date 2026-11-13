/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.Splines.AssembledPolynomialSpline
public import PDE.Analysis.Approximation.Splines.HermiteC2

/-!
# Assembled Hermite interpolation

Shared finite Hermite data define a single `C¹` function. The function interpolates
every node of a nonempty strict mesh. Exact interior slope equations give `C²`
regularity without changing this function or requiring zero endpoint slopes.
The outside tails are polynomial; compact odd extension is a separate operation.
-/

@[expose] public section

noncomputable section

open Set

namespace CAS.Splines.HermiteData

variable {panels : ℕ}

/-- Assemble the cubic Hermite interpolant, with its first and last polynomial tails. -/
def assembledEvaluator (data : HermiteData panels) (mesh : StrictKnotMesh panels) : ℝ → ℝ :=
  (data.toSpline mesh).assembledEvaluator

/-- The function is `C¹` for arbitrary shared nodal values and physical slopes. -/
theorem contDiff_assembledEvaluator (data : HermiteData panels) (mesh : StrictKnotMesh panels) :
    ContDiff ℝ 1 (data.assembledEvaluator mesh) :=
  (data.toSpline mesh).contDiff_assembledEvaluator

/-- On a closed panel the assembled interpolant is its physical Hermite polynomial. -/
theorem assembledEvaluator_eq_piece (data : HermiteData panels) (mesh : StrictKnotMesh panels)
    (panel : Fin panels) {x : ℝ}
    (hx : x ∈ Icc (mesh.panelLeft panel) (mesh.panelRight panel)) :
    data.assembledEvaluator mesh x = ((data.polynomialData mesh).piece panel).eval x :=
  (data.toSpline mesh).assembledEvaluator_eq_piece panel hx

/-- Every node, including both outer endpoints, has its prescribed value. -/
theorem assembledEvaluator_knot (data : HermiteData panels) (mesh : StrictKnotMesh panels)
    (hpanels : 0 < panels) (node : Fin (panels + 1)) :
    data.assembledEvaluator mesh (mesh.knot node) = data.value node := by
  cases panels with
  | zero => omega
  | succ n =>
      refine Fin.cases ?_ (fun i ↦ ?_) node
      · have hmem : mesh.panelLeft 0 ∈ Icc (mesh.panelLeft 0) (mesh.panelRight 0) :=
          ⟨le_rfl, (mesh.panelLeft_lt_panelRight 0).le⟩
        have hzero : (0 : Fin (n + 1)).castSucc = 0 := rfl
        rw [show mesh.knot 0 = mesh.panelLeft 0 from rfl,
          data.assembledEvaluator_eq_piece mesh 0 hmem]
        simpa only [polynomialJet_zero, hzero] using data.value_left mesh 0
      · have hmem : mesh.panelRight i ∈ Icc (mesh.panelLeft i) (mesh.panelRight i) :=
          ⟨(mesh.panelLeft_lt_panelRight i).le, le_rfl⟩
        rw [show mesh.knot i.succ = mesh.panelRight i from rfl,
          data.assembledEvaluator_eq_piece mesh i hmem]
        simpa only [polynomialJet_zero] using data.value_right mesh i

/-- Exact nonuniform interior slope equations make this same interpolant `C²`.
This says nothing about regularity of a subsequent zero extension at the outer knots. -/
theorem contDiff_two_assembledEvaluator (data : HermiteData panels)
    (mesh : StrictKnotMesh panels) (heq : data.C2SlopeEquations mesh) :
    ContDiff ℝ 2 (data.assembledEvaluator mesh) :=
  (data.toC2Spline mesh heq).contDiff_assembledEvaluator

/-- The exact uniform `1,4,1` slope system also upgrades the assembled function to `C²`. -/
theorem contDiff_two_assembledEvaluator_of_uniform (data : HermiteData panels)
    (mesh : StrictKnotMesh panels) (h : ℝ)
    (hmesh : ∀ i, mesh.panelRight i - mesh.panelLeft i = h)
    (heq : data.UniformSlopeEquations h) :
    ContDiff ℝ 2 (data.assembledEvaluator mesh) :=
  data.contDiff_two_assembledEvaluator mesh
    ((data.c2SlopeEquations_iff_uniform mesh h hmesh).mpr heq)

end CAS.Splines.HermiteData
