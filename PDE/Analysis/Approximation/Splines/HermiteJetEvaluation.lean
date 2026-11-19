/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.Splines.HermiteAssembly

/-!
# Derivatives of the assembled Hermite spline on closed panels

Uniqueness of derivatives within a nondegenerate closed interval identifies
the global derivatives with the panel jets, including at knots. The second
derivative statement requires the exact interior slope equations.
-/

@[expose] public section

noncomputable section

namespace CAS.Splines.HermiteData

open Set

variable {panels : ℕ}

/-- The assembled first derivative agrees with either panel jet at a knot. -/
theorem deriv_assembledEvaluator_eq_jet (data : HermiteData panels)
    (mesh : StrictKnotMesh panels) (panel : Fin panels) {x : ℝ}
    (hx : x ∈ Icc (mesh.panelLeft panel) (mesh.panelRight panel)) :
    deriv (data.assembledEvaluator mesh) x =
      polynomialJet 1 ((data.polynomialData mesh).piece panel) x := by
  have hu := uniqueDiffOn_Icc (mesh.panelLeft_lt_panelRight panel) x hx
  have hf := ((data.contDiff_assembledEvaluator mesh).differentiable (by norm_num) x).hasDerivAt
  have hp := (PolynomialSplineData.hasDerivAt_polynomialJet 0
    ((data.polynomialData mesh).piece panel) x).hasDerivWithinAt
      (s := Icc (mesh.panelLeft panel) (mesh.panelRight panel))
  have h := hp.congr_of_mem
    (fun y hy ↦ data.assembledEvaluator_eq_piece mesh panel hy) hx
  calc
    _ = derivWithin (data.assembledEvaluator mesh)
        (Icc (mesh.panelLeft panel) (mesh.panelRight panel)) x :=
      (hf.hasDerivWithinAt.derivWithin hu).symm
    _ = _ := h.derivWithin hu

/-- Exact C² matching identifies the global second derivative with the panel jet
even at the endpoints of a panel. -/
theorem deriv_deriv_assembledEvaluator_eq_jet (data : HermiteData panels)
    (mesh : StrictKnotMesh panels) (heq : data.C2SlopeEquations mesh)
    (panel : Fin panels) {x : ℝ}
    (hx : x ∈ Icc (mesh.panelLeft panel) (mesh.panelRight panel)) :
    deriv (deriv (data.assembledEvaluator mesh)) x =
      polynomialJet 2 ((data.polynomialData mesh).piece panel) x := by
  have hu := uniqueDiffOn_Icc (mesh.panelLeft_lt_panelRight panel) x hx
  have hf := ((data.contDiff_two_assembledEvaluator mesh heq).differentiable_deriv_two x).hasDerivAt
  have hp := (PolynomialSplineData.hasDerivAt_polynomialJet 1
    ((data.polynomialData mesh).piece panel) x).hasDerivWithinAt
      (s := Icc (mesh.panelLeft panel) (mesh.panelRight panel))
  have h := hp.congr_of_mem
    (fun y hy ↦ data.deriv_assembledEvaluator_eq_jet mesh panel hy) hx
  calc
    _ = derivWithin (deriv (data.assembledEvaluator mesh))
        (Icc (mesh.panelLeft panel) (mesh.panelRight panel)) x :=
      (hf.hasDerivWithinAt.derivWithin hu).symm
    _ = _ := h.derivWithin hu

end CAS.Splines.HermiteData
