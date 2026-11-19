/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.SecondPartial
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Exponential tilting of one-dimensional heat solutions

If `vₜ = vₓₓ`, then `exp(kx + νk²t) v(νt, x + 2νkt)` solves `wₜ = νwₓₓ`.
The formulas below concern coordinate derivatives of locally smooth fields.
They also expose the spatial derivative needed for initial traces.
-/

@[expose] public noncomputable section

namespace HeatEquation

/-- The time dilation and spatial translation accompanying an exponential tilt. -/
def exponentialTiltChart (ν k : ℝ) (p : ℝ^2) : ℝ^2 :=
  !₂[ν * p 0, p 1 + 2 * ν * k * p 0]

/-- The exponential weight accompanying a heat-equation tilt. -/
def exponentialTiltWeight (ν k : ℝ) (p : ℝ^2) : ℝ :=
  Real.exp (k * p 1 + ν * k ^ 2 * p 0)

/-- Exponential tilting converts unit diffusivity to diffusivity `ν`. -/
def exponentialTilt (ν k : ℝ) (v : ℝ^2 → ℝ) (p : ℝ^2) : ℝ :=
  exponentialTiltWeight ν k p * v (exponentialTiltChart ν k p)

/-- The affine tilt chart is smooth. -/
theorem contDiff_exponentialTiltChart (ν k : ℝ) {r : WithTop ℕ∞} :
    ContDiff ℝ r (exponentialTiltChart ν k) := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i <;> dsimp [exponentialTiltChart] <;> fun_prop

/-- The exponential tilt weight is smooth. -/
theorem contDiff_exponentialTiltWeight (ν k : ℝ) {r : WithTop ℕ∞} :
    ContDiff ℝ r (exponentialTiltWeight ν k) := by
  unfold exponentialTiltWeight
  fun_prop

/-- Local regularity is preserved under the tilt. -/
theorem contDiffAt_exponentialTilt (ν k : ℝ) (v : ℝ^2 → ℝ) (p : ℝ^2)
    {r : WithTop ℕ∞} (hv : ContDiffAt ℝ r v (exponentialTiltChart ν k p)) :
    ContDiffAt ℝ r (exponentialTilt ν k v) p :=
  (contDiff_exponentialTiltWeight ν k).contDiffAt.mul
    (hv.comp p (contDiff_exponentialTiltChart ν k).contDiffAt)

private theorem tiltChart_time (ν k : ℝ) (p : ℝ^2) :
    (∂[0] (fun q ↦ exponentialTiltChart ν k q 0)) p = ν ∧
      (∂[0] (fun q ↦ exponentialTiltChart ν k q 1)) p = 2 * ν * k := by
  constructor <;> simp only [exponentialTiltChart, PiLp.toLp_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one] <;> cas

private theorem tiltChart_space (ν k : ℝ) (p : ℝ^2) :
    (∂[1] (fun q ↦ exponentialTiltChart ν k q 0)) p = 0 ∧
      (∂[1] (fun q ↦ exponentialTiltChart ν k q 1)) p = 1 := by
  constructor <;> simp only [exponentialTiltChart, PiLp.toLp_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one] <;> cas

private theorem tiltWeight_time (ν k : ℝ) (p : ℝ^2) :
    (∂[0] (exponentialTiltWeight ν k)) p =
      ν * k ^ 2 * exponentialTiltWeight ν k p := by
  unfold exponentialTiltWeight
  cas

private theorem tiltWeight_space (ν k : ℝ) :
    (∂[1] (exponentialTiltWeight ν k)) =
      fun p ↦ k * exponentialTiltWeight ν k p := by
  funext p
  unfold exponentialTiltWeight
  cas

private theorem partialDeriv_tiltChart_time (ν k : ℝ) (v : ℝ^2 → ℝ) (p : ℝ^2)
    (hv : DifferentiableAt ℝ v (exponentialTiltChart ν k p)) :
    (∂[0] (fun q ↦ v (exponentialTiltChart ν k q))) p =
      ν * (∂[0] v) (exponentialTiltChart ν k p) +
        (2 * ν * k) * (∂[1] v) (exponentialTiltChart ν k p) := by
  rw [PDE.partialDeriv_comp _ _ _ _ hv
    ((contDiff_exponentialTiltChart ν k (r := 1)).differentiable (by norm_num) p),
    Fin.sum_univ_two, (tiltChart_time ν k p).1, (tiltChart_time ν k p).2]
  cas

private theorem partialDeriv_tiltChart_space (ν k : ℝ) (v : ℝ^2 → ℝ) (p : ℝ^2)
    (hv : DifferentiableAt ℝ v (exponentialTiltChart ν k p)) :
    (∂[1] (fun q ↦ v (exponentialTiltChart ν k q))) p =
      (∂[1] v) (exponentialTiltChart ν k p) := by
  rw [PDE.partialDeriv_comp _ _ _ _ hv
    ((contDiff_exponentialTiltChart ν k (r := 1)).differentiable (by norm_num) p),
    Fin.sum_univ_two, (tiltChart_space ν k p).1, (tiltChart_space ν k p).2,
    mul_zero, zero_add, mul_one]

private theorem secondPartialDeriv_tiltChart_space
    (ν k : ℝ) (v : ℝ^2 → ℝ) (p : ℝ^2)
    (hv : ContDiffAt ℝ 2 v (exponentialTiltChart ν k p)) :
    (∂[1] (∂[1] (fun q ↦ v (exponentialTiltChart ν k q)))) p =
      (∂[1] (∂[1] v)) (exponentialTiltChart ν k p) := by
  have hzero : (∂[1] (fun q ↦ exponentialTiltChart ν k q 0)) = fun _ ↦ 0 :=
    funext fun q ↦ (tiltChart_space ν k q).1
  have hone : (∂[1] (fun q ↦ exponentialTiltChart ν k q 1)) = fun _ ↦ 1 :=
    funext fun q ↦ (tiltChart_space ν k q).2
  rw [PDE.partialDeriv_partialDeriv_comp_at _ _ _ _ _ hv
    (contDiff_exponentialTiltChart ν k).contDiffAt]
  simp only [Fin.sum_univ_two, hzero, hone, PDE.partialDeriv_const, mul_zero, mul_one,
    zero_add, add_zero]

/-- The spatial derivative of an exponentially tilted field. -/
theorem partialDeriv_exponentialTilt_space
    (ν k : ℝ) (v : ℝ^2 → ℝ) (p : ℝ^2)
    (hv : DifferentiableAt ℝ v (exponentialTiltChart ν k p)) :
    (∂[1] (exponentialTilt ν k v)) p =
      exponentialTiltWeight ν k p *
        (k * v (exponentialTiltChart ν k p) +
          (∂[1] v) (exponentialTiltChart ν k p)) := by
  have hc : DifferentiableAt ℝ (fun q ↦ v (exponentialTiltChart ν k q)) p :=
    hv.comp p
      ((contDiff_exponentialTiltChart ν k (r := 1)).differentiable (by norm_num) p)
  unfold exponentialTilt
  rw [PDE.partialDeriv_mul
    ((contDiff_exponentialTiltWeight ν k (r := 1)).differentiable (by norm_num) p) hc,
    tiltWeight_space, partialDeriv_tiltChart_space ν k v p hv]
  cas

/-- An exponentially tilted unit heat solution satisfies the heat equation with
diffusivity `ν`, by its time and second spatial derivatives. -/
theorem exponentialTilt_heat_equation
    (ν k : ℝ) (v : ℝ^2 → ℝ) (p : ℝ^2)
    (hv : ContDiffAt ℝ 2 v (exponentialTiltChart ν k p))
    (hheat : (∂[0] v) (exponentialTiltChart ν k p) =
      (∂[1] (∂[1] v)) (exponentialTiltChart ν k p)) :
    (∂[0] (exponentialTilt ν k v)) p =
      ν * (∂[1] (∂[1] (exponentialTilt ν k v))) p := by
  have hw : ContDiffAt ℝ 2 (exponentialTiltWeight ν k) p :=
    (contDiff_exponentialTiltWeight ν k).contDiffAt
  have hc : ContDiffAt ℝ 2 (fun q ↦ v (exponentialTiltChart ν k q)) p :=
    hv.comp p (contDiff_exponentialTiltChart ν k).contDiffAt
  have hwd := hw.differentiableAt (by norm_num)
  have hvd := hv.differentiableAt (by norm_num)
  have hww : (∂[1] (∂[1] (exponentialTiltWeight ν k))) p =
      k ^ 2 * exponentialTiltWeight ν k p := by
    rw [tiltWeight_space]
    unfold exponentialTiltWeight
    cas
  unfold exponentialTilt
  rw [PDE.partialDeriv_mul hwd (hc.differentiableAt (by norm_num)),
    PDE.secondPartialDeriv_mul_at 1 1 hw hc, tiltWeight_time, hww, tiltWeight_space,
    partialDeriv_tiltChart_time ν k v p hvd,
    partialDeriv_tiltChart_space ν k v p hvd,
    secondPartialDeriv_tiltChart_space ν k v p hv, hheat]
  cas

end HeatEquation
