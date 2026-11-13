/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Classical.VariableCoefficient.Operator
public import PDE.Hyperbolic.GeometricOptics.Residual

/-!
# The variable-speed wave residual

The real operator is the nondivergence operator with principal matrix
`c(x)² I`. Its complex extension is defined using coordinate derivatives
and agrees with that real operator on both components of a C² field.

No derivative of the speed enters this operator. Accordingly, these identities
need no regularity or positivity of `c`; positive smooth speeds are included.
The divergence-form operator `uₜₜ - div(c² ∇u)` has different lower-order terms.
-/

@[expose] public noncomputable section

open PDE PDE.Common

namespace WaveEquation.GeometricOptics.VariableSpeed

variable {n : ℕ}

/-- The isotropic principal matrix associated with a spatial wave speed. -/
def principalMatrix (c : ℝ^n → ℝ) (x : ℝ^n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun _ ↦ c x ^ 2)

/-- The real wave operator with principal matrix `c² I` is `uₜₜ - c² Δu`. -/
theorem waveOperator_principalMatrix (c : ℝ^n → ℝ) (u : ℝ^(n + 1) → ℝ) (z : ℝ^(n + 1)) :
    VariableCoefficient.waveOperator (principalMatrix c) u z =
      (∂[0] (∂[0] u)) z - c (spatialPart z) ^ 2 * ∑ i : Fin n, (∂[i.succ] (∂[i.succ] u)) z := by
  simp [VariableCoefficient.waveOperator, principalMatrix, Matrix.diagonal_apply, ← Finset.mul_sum]

/-- Continuous speed and a C² field give a continuous real residual at the point. -/
theorem continuousAt_waveOperator_principalMatrix {c : ℝ^n → ℝ} {u : ℝ^(n + 1) → ℝ} {z : ℝ^(n + 1)}
    (hc : ContinuousAt c (spatialPart z)) (hu : ContDiffAt ℝ 2 u z) :
    ContinuousAt (VariableCoefficient.waveOperator (principalMatrix c) u) z := by
  have hsecond (i : Fin (n + 1)) : ContinuousAt (∂[i] (∂[i] u)) z :=
    (contDiffAt_partialDeriv 0 (contDiffAt_partialDeriv 1 hu i) i).continuousAt
  rw [funext (waveOperator_principalMatrix c u)]
  exact (hsecond 0).sub (((hc.comp (spatialPartCLM n).continuous.continuousAt).pow 2).mul
      (tendsto_finsetSum (s := Finset.univ) fun i _ ↦ hsecond i.succ))

/-- The complex extension of the variable-speed wave operator. -/
def residual (c : ℝ^n → ℝ) (u : ℝ^(n + 1) → ℂ) (z : ℝ^(n + 1)) : ℂ :=
  (∂[0] (∂[0] u)) z -
    (c (spatialPart z) ^ 2 : ℝ) * ∑ i : Fin n, (∂[i.succ] (∂[i.succ] u)) z

/-- Real-to-complex inclusion preserves the variable-speed residual. -/
theorem residual_ofReal (c : ℝ^n → ℝ) (u : ℝ^(n + 1) → ℝ) (z : ℝ^(n + 1)) :
    residual c (fun y ↦ (u y : ℂ)) z =
      (VariableCoefficient.waveOperator (principalMatrix c) u z : ℂ) := by
  simp only [residual, partialDeriv_ofReal, waveOperator_principalMatrix,
    Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_sum]

/-- A real continuous linear functional sends the complex residual to the canonical
real wave operator of the corresponding component. -/
theorem map_residual (c : ℝ^n → ℝ) (L : ℂ →L[ℝ] ℝ)
    {u : ℝ^(n + 1) → ℂ} {z : ℝ^(n + 1)} (hu : ContDiffAt ℝ 2 u z) :
    L (residual c u z) =
      VariableCoefficient.waveOperator (principalMatrix c) (fun y ↦ L (u y)) z := by
  have hsecond (i : Fin (n + 1)) :
      (∂[i] (∂[i] (fun y ↦ L (u y)))) z = L ((∂[i] (∂[i] u)) z) := by
    have hfirst : (∂[i] (fun y ↦ L (u y))) =ᶠ[nhds z]
        fun y ↦ L ((∂[i] u) y) := by
      filter_upwards [hu.eventually (by norm_num)] with y hy
      exact L.partialDeriv_comp i (hy.differentiableAt (by norm_num))
    rw [partialDeriv_congr_nhds i hfirst]
    exact L.partialDeriv_comp i
      ((contDiffAt_partialDeriv 1 hu i).differentiableAt (by norm_num))
  rw [waveOperator_principalMatrix]
  simp only [hsecond, residual, ← Complex.real_smul, map_sub, map_smul, map_sum, smul_eq_mul]

/-- The real component solves the real equation whenever the complex residual vanishes. -/
theorem waveOperator_re_eq_zero {c : ℝ^n → ℝ} {u : ℝ^(n + 1) → ℂ}
    {z : ℝ^(n + 1)} (hu : ContDiffAt ℝ 2 u z) (hres : residual c u z = 0) :
    VariableCoefficient.waveOperator (principalMatrix c) (fun y ↦ (u y).re) z = 0 := by
  simpa only [hres, map_zero, Complex.reCLM_apply] using (map_residual c Complex.reCLM hu).symm

/-- The imaginary component has the same canonical real wave equation. -/
theorem waveOperator_im_eq_zero {c : ℝ^n → ℝ} {u : ℝ^(n + 1) → ℂ}
    {z : ℝ^(n + 1)} (hu : ContDiffAt ℝ 2 u z) (hres : residual c u z = 0) :
    VariableCoefficient.waveOperator (principalMatrix c) (fun y ↦ (u y).im) z = 0 := by
  simpa only [hres, map_zero, Complex.imCLM_apply] using (map_residual c Complex.imCLM hu).symm

end WaveEquation.GeometricOptics.VariableSpeed
