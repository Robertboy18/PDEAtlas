/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Jacobian.Calculus
public import PDE.Analysis.Calculus.Prod.ParameterDerivative

/-!
# Spatial Jacobians of parameterized maps

For a jointly `C²` family, its spatial Jacobian is jointly `C¹`.
Differentiating this Jacobian along the parameter gives the Jacobian of
the parameter derivative. Both statements depend only on the germ of
the family at the point.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Elementwise Topology

namespace PDE.Analysis

variable {n m : ℕ} {U : ℝ → ℝ^n → ℝ^m}

/-- The spatial Jacobian of a jointly `C²` germ is jointly `C¹`. -/
theorem contDiffAt_family_jacobianMatrix {p : ℝ × ℝ^n}
    (hU : ContDiffAt ℝ 2 (fun q : ℝ × ℝ^n ↦ U q.1 q.2) p) :
    ContDiffAt ℝ 1 (fun q : ℝ × ℝ^n ↦ jacobianMatrix (U q.1) q.2) p := by
  apply contDiffAt_pi.mpr
  intro k
  apply contDiffAt_pi.mpr
  intro i
  have hnear : (fun q : ℝ × ℝ^n ↦ jacobianMatrix (U q.1) q.2 k i) =ᶠ[𝓝 p]
      (fun q ↦ fderiv ℝ (fun r : ℝ × ℝ^n ↦ U r.1 r.2) q
        (0, EuclideanSpace.single i 1) k) := by
    filter_upwards [hU.eventually (by norm_num)] with q hq
    have hdiff : DifferentiableAt ℝ (fun r : ℝ × ℝ^n ↦ U r.1 r.2) q :=
      hq.differentiableAt (by norm_num)
    have hslice : DifferentiableAt ℝ (U q.1) q.2 :=
      (hdiff.hasFDerivAt.comp q.2
        (g := fun r : ℝ × ℝ^n ↦ U r.1 r.2) (f := fun y : ℝ^n ↦ (q.1, y))
        (hasFDerivAt_prodMk_right q.1 q.2)).differentiableAt
    rw [jacobianMatrix_apply_eq_fderiv hslice, fderiv_space_apply hdiff]
  apply ContDiffAt.congr_of_eventuallyEq _ hnear
  exact (EuclideanSpace.proj k : ℝ^m →L[ℝ] ℝ).contDiff.contDiffAt.comp p
    ((hU.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const)

/-- Differentiating the spatial Jacobian along a parameter gives the
Jacobian of the parameter derivative, under local joint `C²` regularity. -/
theorem hasDerivAt_jacobianMatrix {t : ℝ} {x : ℝ^n}
    (hU : ContDiffAt ℝ 2 (fun p : ℝ × ℝ^n ↦ U p.1 p.2) (t, x)) :
    HasDerivAt (fun s ↦ jacobianMatrix (U s) x)
      (jacobianMatrix (fun y ↦ deriv (fun s ↦ U s y) t) x) t := by
  have hv := (contDiffAt_parameter_deriv hU).differentiableAt (by norm_num)
  apply hasDerivAt_pi.mpr
  intro k
  apply hasDerivAt_pi.mpr
  intro i
  rw [jacobianMatrix_apply_eq_fderiv hv]
  have h := (EuclideanSpace.proj k : ℝ^m →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_fderiv_space hU (EuclideanSpace.single i 1))
  apply h.congr_of_eventuallyEq
  filter_upwards [(continuousAt_id.prodMk continuousAt_const).eventually
    (hU.eventually (by norm_num))] with s hs
  exact jacobianMatrix_apply_eq_fderiv
    ((hs.differentiableAt (by norm_num)).comp x
      ((differentiableAt_const s).prodMk differentiableAt_id)) k i

end PDE.Analysis
