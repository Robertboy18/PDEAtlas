/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Calculus.ScalarComposition
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import CAS.ExactTactic

/-!
# Hopf–Cole linearization of quadratic viscous Hamilton–Jacobi

For nonzero viscosity `ν`, the substitutions
`v = exp (-u / (2ν))` and `u = -2ν log v` identify
`u_t + ‖∇u‖² / 2 = ν Δu` with `v_t = ν Δv`, wherever `v > 0`.
The physically parabolic case is `ν > 0`; the identities also hold for negative viscosity.

The main equivalences are `exponentialTransform_solves_heat_iff` and
`logarithmicTransform_solves_iff`. Their hypotheses are pointwise: a differentiable time
trace and a `C²` spatial slice. The residual identities derive every derivative from the transforms
themselves. The substitutions preserve this regularity and are mutual inverses on positive fields.

This is the Cole–Hopf transformation (2) of Evans, §4.4.1(a), for the equation (1) with `a = ν`
and `b = 1/2`; Evans takes `a > 0`. For `n = 1` the equation is the potential form (8) of the
viscous Burgers equation in §4.4.1(b). The Cauchy solution is constructed in
`Viscous.InitialValue`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.4.1(a), equations (1)-(3); §4.4.1(b), equation (8).
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Gradient

@[expose] public section

open PDE (laplacian)

namespace HamiltonJacobi.ColeHopf

variable {n : ℕ}

/-- The exponential substitution that linearizes quadratic viscous Hamilton–Jacobi. -/
noncomputable def exponentialTransform (ν : ℝ) (u : ℝ^n → ℝ → ℝ) :
    ℝ^n → ℝ → ℝ :=
  fun x t ↦ Real.exp (-u x t / (2 * ν))

/-- The inverse Hopf–Cole substitution, mathematically used where the input is positive. -/
noncomputable def logarithmicTransform (ν : ℝ) (v : ℝ^n → ℝ → ℝ) :
    ℝ^n → ℝ → ℝ :=
  fun x t ↦ -2 * ν * Real.log (v x t)

/-- The quadratic viscous Hamilton–Jacobi residual, with separate space and time arguments. -/
noncomputable def viscousHamiltonJacobiResidual (ν : ℝ) (u : ℝ^n → ℝ → ℝ)
    (x : ℝ^n) (t : ℝ) : ℝ :=
  deriv (u x) t + ‖∇ (fun y ↦ u y t) x‖ ^ 2 / 2 -
    ν * laplacian (fun y ↦ u y t) x

/-- The exponential transform is strictly positive at every point. -/
theorem exponentialTransform_pos (ν : ℝ) (u : ℝ^n → ℝ → ℝ) (x : ℝ^n) (t : ℝ) :
    0 < exponentialTransform ν u x t :=
  Real.exp_pos _

/-- The logarithmic substitution recovers the original potential. -/
@[simp]
theorem logarithmicTransform_exponentialTransform {ν : ℝ} (hν : ν ≠ 0) (u : ℝ^n → ℝ → ℝ) :
    logarithmicTransform ν (exponentialTransform ν u) = u := by
  funext x t
  simp only [logarithmicTransform, exponentialTransform, Real.log_exp]
  cas using hν

/-- The exponential substitution recovers a positive field pointwise. -/
theorem exponentialTransform_logarithmicTransform {ν : ℝ} (hν : ν ≠ 0)
    {v : ℝ^n → ℝ → ℝ} {x : ℝ^n} {t : ℝ} (hv : 0 < v x t) :
    exponentialTransform ν (logarithmicTransform ν v) x t = v x t := by
  unfold exponentialTransform logarithmicTransform
  rw [show -(-2 * ν * Real.log (v x t)) / (2 * ν) = Real.log (v x t) by
    cas using hν]
  exact Real.exp_log hv

/-- The exponential substitution preserves differentiability of each time trace. -/
theorem differentiableAt_exponentialTransform_time (ν : ℝ) {u : ℝ^n → ℝ → ℝ} {x : ℝ^n} {t : ℝ}
    (hu : DifferentiableAt ℝ (u x) t) :
    DifferentiableAt ℝ (exponentialTransform ν u x) t :=
  (hu.neg.div_const (2 * ν)).exp

/-- The exponential substitution preserves local `C²` spatial regularity. -/
theorem contDiffAt_exponentialTransform_space (ν : ℝ) {u : ℝ^n → ℝ → ℝ} {x : ℝ^n} {t : ℝ}
    (hu : ContDiffAt ℝ 2 (fun y ↦ u y t) x) :
    ContDiffAt ℝ 2 (fun y ↦ exponentialTransform ν u y t) x :=
  (hu.neg.div_const (2 * ν)).exp

/-- The logarithmic substitution preserves time differentiability at a positive point. -/
theorem differentiableAt_logarithmicTransform_time (ν : ℝ) {v : ℝ^n → ℝ → ℝ} {x : ℝ^n} {t : ℝ}
    (hv : DifferentiableAt ℝ (v x) t) (hpos : 0 < v x t) :
    DifferentiableAt ℝ (logarithmicTransform ν v x) t :=
  (hv.log hpos.ne').const_mul (-2 * ν)

/-- The logarithmic substitution preserves local `C²` spatial regularity at a positive point. -/
theorem contDiffAt_logarithmicTransform_space (ν : ℝ) {v : ℝ^n → ℝ → ℝ} {x : ℝ^n} {t : ℝ}
    (hv : ContDiffAt ℝ 2 (fun y ↦ v y t) x) (hpos : 0 < v x t) :
    ContDiffAt ℝ 2 (fun y ↦ logarithmicTransform ν v y t) x :=
  (hv.log hpos.ne').const_smul (-2 * ν)

/-- The heat residual of the exponential substitution is a nonzero multiple of the
quadratic viscous Hamilton–Jacobi residual. -/
theorem heat_residual_exponentialTransform {ν : ℝ} (hν : ν ≠ 0) {u : ℝ^n → ℝ → ℝ} {x : ℝ^n} {t : ℝ}
    (ht : DifferentiableAt ℝ (u x) t) (hx : ContDiffAt ℝ 2 (fun y ↦ u y t) x) :
    deriv (exponentialTransform ν u x) t - ν * laplacian (fun y ↦ exponentialTransform ν u y t) x =
      -exponentialTransform ν u x t / (2 * ν) * viscousHamiltonJacobiResidual ν u x t := by
  let F : ℝ → ℝ := fun z ↦ Real.exp (-z / (2 * ν))
  have hF : ContDiff ℝ 2 F := by
    dsimp only [F]
    fun_prop
  have hfirst (z : ℝ) : HasDerivAt F (-F z / (2 * ν)) z := by
    dsimp only [F]
    cas using hν
  have hsecond : deriv (deriv F) (u x t) = F (u x t) / (4 * ν ^ 2) := by
    dsimp only [F]
    cas using hν
  have htime : deriv (exponentialTransform ν u x) t = -F (u x t) / (2 * ν) * deriv (u x) t :=
    ((hfirst (u x t)).comp t ht.hasDerivAt).deriv
  have hspace := PDE.laplacian_comp_real (g := F) hF.contDiffAt hx
  rw [(hfirst (u x t)).deriv, hsecond] at hspace
  change laplacian (fun y ↦ exponentialTransform ν u y t) x = _ at hspace
  rw [htime, hspace]
  unfold viscousHamiltonJacobiResidual
  change -F (u x t) / (2 * ν) * deriv (u x) t -
        ν * (-F (u x t) / (2 * ν) * laplacian (fun y ↦ u y t) x +
          F (u x t) / (4 * ν ^ 2) * ‖∇ (fun y ↦ u y t) x‖ ^ 2) = -F (u x t) / (2 * ν) *
        (deriv (u x) t + ‖∇ (fun y ↦ u y t) x‖ ^ 2 / 2 - ν * laplacian (fun y ↦ u y t) x)
  generalize F (u x t) = a, deriv (u x) t = b,
    laplacian (fun y ↦ u y t) x = c, ‖∇ (fun y ↦ u y t) x‖ = d
  cas using hν

/-- Hopf–Cole linearization in arbitrary spatial dimension, under separate first-time
and second-space regularity. For positive viscosity this is an equivalence with the heat PDE. -/
theorem exponentialTransform_solves_heat_iff {ν : ℝ} (hν : ν ≠ 0) {u : ℝ^n → ℝ → ℝ} {x : ℝ^n}
    {t : ℝ} (ht : DifferentiableAt ℝ (u x) t) (hx : ContDiffAt ℝ 2 (fun y ↦ u y t) x) :
    deriv (exponentialTransform ν u x) t = ν * laplacian (fun y ↦ exponentialTransform ν u y t) x ↔
      viscousHamiltonJacobiResidual ν u x t = 0 := by
  rw [← sub_eq_zero, heat_residual_exponentialTransform hν ht hx, mul_eq_zero]
  simp [exponentialTransform, hν]

/-- The Hamilton–Jacobi residual of the logarithmic substitution is a multiple of the
heat residual. Positivity is required only at the evaluation point. -/
theorem viscousHamiltonJacobiResidual_logarithmicTransform (ν : ℝ) {v : ℝ^n → ℝ → ℝ} {x : ℝ^n}
    {t : ℝ} (ht : DifferentiableAt ℝ (v x) t) (hx : ContDiffAt ℝ 2 (fun y ↦ v y t) x)
    (hpos : 0 < v x t) :
    viscousHamiltonJacobiResidual ν (logarithmicTransform ν v) x t =
      (-2 * ν / v x t) * (deriv (v x) t - ν * laplacian (fun y ↦ v y t) x) := by
  let F : ℝ → ℝ := fun z ↦ -2 * ν * Real.log z
  have hF : ContDiffAt ℝ 2 F (v x t) := (Real.contDiffAt_log.mpr hpos.ne').const_smul (-2 * ν)
  have hfirst : HasDerivAt F (-2 * ν / v x t) (v x t) := by
    dsimp only [F]
    cas using hpos
  have hsecond : deriv (deriv F) (v x t) = 2 * ν / (v x t) ^ 2 := by
    have hnear :
        deriv F =ᶠ[nhds (v x t)] fun z ↦ -2 * ν / z := by
      filter_upwards [Ioi_mem_nhds hpos] with z hz
      dsimp only [F]
      cas using hz
    rw [hnear.deriv_eq]
    cas using hpos
  have htime : deriv (logarithmicTransform ν v x) t = (-2 * ν / v x t) * deriv (v x) t :=
    (hfirst.comp t ht.hasDerivAt).deriv
  have hspace := PDE.laplacian_comp_real (g := F) hF hx
  rw [hfirst.deriv, hsecond] at hspace
  have hgradient := PDE.gradient_comp_real hfirst.differentiableAt
    (hx.differentiableAt (by norm_num))
  rw [hfirst.deriv] at hgradient
  change ∇ (fun y ↦ logarithmicTransform ν v y t) x = _ at hgradient
  change laplacian (fun y ↦ logarithmicTransform ν v y t) x = _ at hspace
  unfold viscousHamiltonJacobiResidual
  rw [htime, hspace, hgradient, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hv : v x t ≠ 0 := hpos.ne'
  generalize v x t = a at hv ⊢
  generalize deriv (v x) t = b, laplacian (fun y ↦ v y t) x = c, ‖∇ (fun y ↦ v y t) x‖ = d
  cas using hv

/-- Every positive classical heat field yields a quadratic viscous Hamilton–Jacobi field,
and the implication is reversible. Regularity of the logarithmic field follows from the
preceding time and space regularity lemmas. -/
theorem logarithmicTransform_solves_iff {ν : ℝ} (hν : ν ≠ 0) {v : ℝ^n → ℝ → ℝ} {x : ℝ^n} {t : ℝ}
    (ht : DifferentiableAt ℝ (v x) t) (hx : ContDiffAt ℝ 2 (fun y ↦ v y t) x) (hpos : 0 < v x t) :
    viscousHamiltonJacobiResidual ν (logarithmicTransform ν v) x t = 0 ↔
      deriv (v x) t = ν * laplacian (fun y ↦ v y t) x := by
  rw [viscousHamiltonJacobiResidual_logarithmicTransform ν ht hx hpos, mul_eq_zero]
  simp [hν, hpos.ne', sub_eq_zero]

end HamiltonJacobi.ColeHopf
