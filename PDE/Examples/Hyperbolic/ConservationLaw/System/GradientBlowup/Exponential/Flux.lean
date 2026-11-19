/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Jacobian.Basic
public import PDE.Hyperbolic.ConservationLaw.System.GradientBlowup.Global
import CAS.ExactTactic
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import PDE.Symbolic.PDEDerivatives

/-!
# A conservative exponential system with two nonlinear families

The flux `(exp(-(a-b)) + exp b, exp b)` is globally strictly hyperbolic.
Its constant eigenvectors are `(1,0)` and `(1,1)`, but both ordered speeds
vary. The off-diagonal Jacobian entry is strictly positive everywhere.
-/

@[expose] public noncomputable section

open PDE.Hyperbolic.ConservationLaw.System
open scoped ContDiff

namespace PDE.Examples.Hyperbolic.ConservationLaw.System.GradientBlowup.Exponential

/-- A coupled conservative exponential flux. -/
def flux (q : ℝ^2) : ℝ^2 := !₂[Real.exp (-(q 0 - q 1)) + Real.exp (q 1), Real.exp (q 1)]

/-- The flux is globally smooth. -/
theorem contDiff_flux : ContDiff ℝ ∞ flux := by
  rw [contDiff_piLp]
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun q : ℝ^2 ↦ Real.exp (-(q 0 - q 1)) + Real.exp (q 1))
    cas
  · change ContDiff ℝ ∞ (fun q : ℝ^2 ↦ Real.exp (q 1))
    cas

/-- The Jacobian matrix of the flux. -/
theorem jacobianMatrix_flux (q : ℝ^2) :
    PDE.Analysis.jacobianMatrix flux q =
      !![-Real.exp (-(q 0 - q 1)), Real.exp (-(q 0 - q 1)) + Real.exp (q 1);
        0, Real.exp (q 1)] := by
  ext i j
  fin_cases i <;> fin_cases j
  · change (∂[0]
      (fun y : ℝ^2 ↦ Real.exp (-(y 0 - y 1)) + Real.exp (y 1))) q =
        -Real.exp (-(q 0 - q 1))
    cas
  · change (∂[1]
      (fun y : ℝ^2 ↦ Real.exp (-(y 0 - y 1)) + Real.exp (y 1))) q =
        Real.exp (-(q 0 - q 1)) + Real.exp (q 1)
    cas
  · change (∂[0] (fun y : ℝ^2 ↦ Real.exp (y 1))) q = 0
    cas
  · change (∂[1] (fun y : ℝ^2 ↦ Real.exp (y 1))) q = Real.exp (q 1)
    cas

/-- The Jacobian of the flux applied to a vector `v`. -/
theorem fderiv_flux (q v : ℝ^2) :
    fderiv ℝ flux q v =
      !₂[-Real.exp (-(q 0 - q 1)) * v 0 +
        (Real.exp (-(q 0 - q 1)) + Real.exp (q 1)) * v 1,
        Real.exp (q 1) * v 1] := by
  rw [fderiv_apply_eq_sum_smul_partialDeriv]
  ext i
  simp only [Fin.sum_univ_two, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have hj (j : Fin 2) :
      (∂[j] flux) q i =
        (!![-Real.exp (-(q 0 - q 1)), Real.exp (-(q 0 - q 1)) + Real.exp (q 1);
          0, Real.exp (q 1)] : Matrix (Fin 2) (Fin 2) ℝ) i j := by
    rw [← jacobianMatrix_flux q]
    exact (PDE.Analysis.jacobianMatrix_apply_eq_fderiv
      (contDiff_flux.differentiable (by simp) q) i j).symm
  rw [hj 0, hj 1]
  fin_cases i
  · change v 0 * -Real.exp (-(q 0 - q 1)) +
        v 1 * (Real.exp (-(q 0 - q 1)) + Real.exp (q 1)) =
      -Real.exp (-(q 0 - q 1)) * v 0 +
        (Real.exp (-(q 0 - q 1)) + Real.exp (q 1)) * v 1
    cas
  · change v 0 * 0 + v 1 * Real.exp (q 1) = Real.exp (q 1) * v 1
    cas

private def eigenvector (k : Fin 2) : ℝ^2 :=
  if k = 0 then !₂[1, 0] else !₂[1, 1]

private theorem independent_eigenvectors : LinearIndependent ℝ eigenvector := by
  rw [linearIndependent_fin2]
  constructor
  · intro h
    have hc := congrArg (fun v : ℝ^2 ↦ v 1) h
    norm_num [eigenvector] at hc
  · intro a h
    have hc := congrArg (fun v : ℝ^2 ↦ v 1) h
    norm_num [eigenvector] at hc
    subst a
    have hz := congrArg (fun v : ℝ^2 ↦ v 0) h
    norm_num [eigenvector] at hz

private def eigenbasis : Module.Basis (Fin 2) ℝ (ℝ^2) :=
  basisOfLinearIndependentOfCardEqFinrank independent_eigenvectors (by simp)

private theorem eigenbasis_apply (k : Fin 2) : eigenbasis k = eigenvector k :=
  congrFun (coe_basisOfLinearIndependentOfCardEqFinrank _ _) k

/-- The characteristic speeds `-exp(-(q₀ - q₁)) < exp q₁`. -/
def speed (q : ℝ^2) (k : Fin 2) : ℝ :=
  if k = 0 then -Real.exp (-(q 0 - q 1)) else Real.exp (q 1)

private theorem eigenvector_equation (q : ℝ^2) (k : Fin 2) :
    fderiv ℝ flux q (eigenbasis k) = speed q k • eigenbasis k := by
  rw [eigenbasis_apply, fderiv_flux]
  ext i
  fin_cases k <;> fin_cases i <;> simp [eigenvector, speed]

private theorem speed_strictMono (q : ℝ^2) : StrictMono (speed q) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact False.elim (lt_irrefl _ hij)
  · change -Real.exp (-(q 0 - q 1)) < Real.exp (q 1)
    exact lt_trans (neg_neg_of_pos (Real.exp_pos _)) (Real.exp_pos _)
  · norm_num at hij
  · exact False.elim (lt_irrefl _ hij)

/-- The flux is strictly hyperbolic at every state. -/
theorem isStrictlyHyperbolicAt_flux (q : ℝ^2) : IsStrictlyHyperbolicAt flux q :=
  ⟨contDiff_flux.differentiable (by simp) q, eigenbasis, speed q,
    (speed_strictMono q).injective,
    fun k ↦ ⟨Module.End.mem_eigenspace_iff.mpr (eigenvector_equation q k),
      eigenbasis.ne_zero k⟩⟩

/-- The ordered characteristic speeds of the flux are `speed q`. -/
theorem characteristicSpeed_flux (k : Fin 2) (q : ℝ^2) :
    characteristicSpeed flux k q = speed q k :=
  congrFun (characteristicSpeed_eq_of_eigenbasis eigenbasis
    (speed_strictMono q) (eigenvector_equation q)) k

end PDE.Examples.Hyperbolic.ConservationLaw.System.GradientBlowup.Exponential
