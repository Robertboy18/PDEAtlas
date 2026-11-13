/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.Noether.Invariance

/-!
# Noether identities with the domain variation on the right

Suppose the varied field density at `x` equals the original field density at `Φ t x`,
multiplied by the Jacobian determinant of `Φ t`. Differentiating this finite
identity gives the transport and volume terms. The general off-shell current identity
then gives `div(P v - L X) = -Σₖ ELₖ vₖ`, where `v` and `X` are the parameter
velocities. Euler–Lagrange solutions therefore conserve this current.

This is the density form of Evans, §8.6.2, Theorem 1: the off-shell identity is his (7)
and the conservation law is (8). `Noether/IntegralInvariance` derives the density equality
used here from invariance of the action integrals over open sets, Evans's (6), by change of
variables and localization. Evans treats scalar fields; the results here allow any finite
field dimension and require only local `C²` germs.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.6.1, equation (6), and §8.6.2, Theorem 1.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Matrix.Norms.Elementwise Topology

namespace PDE.CalculusOfVariations.Noether

open Analysis

variable {n m : ℕ}
  {L : Matrix (Fin m) (Fin n) ℝ → ℝ^m → ℝ^n → ℝ}
  {U : ℝ → ℝ^n → ℝ^m} {Φ : ℝ → ℝ^n → ℝ^n} {x : ℝ^n}

/-- Finite invariance with the domain moved on the right gives the off-shell Noether
identity. Differentiation of the finite density equality supplies the infinitesimal law. -/
theorem divergence_noetherCurrent_of_domain_invariance
    (hL : ContDiffAt ℝ 2
      (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦ L a.1 a.2.1 a.2.2)
      (jacobianMatrix (U 0) x, (U 0 x, x)))
    (hU : ContDiffAt ℝ 2 (fun p : ℝ × ℝ^n ↦ U p.1 p.2) (0, x))
    (hΦ : ContDiffAt ℝ 2 (fun p : ℝ × ℝ^n ↦ Φ p.1 p.2) (0, x))
    (hΦ₀ : Φ 0 =ᶠ[𝓝 x] id)
    (hinvariant : (fun t ↦ fieldDensity L (U t) x) =ᶠ[𝓝 0]
      (fun t ↦ transformedDensity L (fun _ ↦ U 0) Φ t x)) :
    ∇· (noetherCurrent L (U 0)
      (fun y ↦ deriv (fun t ↦ U t y) 0)
      (fun y ↦ -deriv (fun t ↦ Φ t y) 0)) x =
      -∑ k, classicalEulerLagrange L (U 0) x k *
        deriv (fun t ↦ U t x) 0 k := by
  have hu : ContDiffAt ℝ 2 (U 0) x :=
    hU.comp x (contDiffAt_const.prodMk contDiffAt_id)
  have hbase : Φ 0 x = x := hΦ₀.eq_of_nhds
  have hd := (contDiffAt_fieldDensity hL hu).differentiableAt (by norm_num)
  have hΦx : ContDiffAt ℝ 2 (fun t : ℝ ↦ Φ t x) 0 :=
    hΦ.comp 0 (contDiffAt_id.prodMk contDiffAt_const)
  have hmove := hd.hasFDerivAt.comp_hasDerivAt_of_eq 0
    (hΦx.differentiableAt (by norm_num)).hasDerivAt hbase.symm
  have hdet : jacobianMatrix (Φ 0) x = 1 := by
    rw [jacobianMatrix_eq_of_eventuallyEq hΦ₀]
    exact jacobianMatrix_id x
  have hpull : HasDerivAt (fun t ↦ transformedDensity L (fun _ ↦ U 0) Φ t x)
      (fderiv ℝ (fieldDensity L (U 0)) x (deriv (fun t ↦ Φ t x) 0) +
        fieldDensity L (U 0) x * ∇· (fun y ↦ deriv (fun t ↦ Φ t y) 0) x) 0 := by
    simpa only [transformedDensity, Function.comp_apply, hdet, Matrix.det_one, mul_one, hbase] using
      hmove.fun_mul (hasDerivAt_spatial_volume hΦ hΦ₀)
  have hinf := (hasDerivAt_fieldDensity hL hU).unique
    (hpull.congr_of_eventuallyEq hinvariant)
  have hX := (contDiffAt_parameter_deriv hΦ).differentiableAt (by norm_num)
  rw [divergence_noetherCurrent hL hu
    ((contDiffAt_parameter_deriv hU).differentiableAt (by norm_num)) hX.fun_neg]
  have hneg : ∇· (fun y ↦ -deriv (fun t ↦ Φ t y) 0) x =
      -∇· (fun y ↦ deriv (fun t ↦ Φ t y) 0) x := by
    simp only [divergence, PiLp.neg_apply]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact partialDeriv_neg
  rw [map_neg, hneg]
  linarith

/-- Euler–Lagrange solutions conserve the current obtained from finite domain invariance.
The spatial velocity is negated because the domain is varied on the right of the action law. -/
theorem noether_of_domain_invariance
    (hL : ContDiffAt ℝ 2
      (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦ L a.1 a.2.1 a.2.2)
      (jacobianMatrix (U 0) x, (U 0 x, x)))
    (hU : ContDiffAt ℝ 2 (fun p : ℝ × ℝ^n ↦ U p.1 p.2) (0, x))
    (hΦ : ContDiffAt ℝ 2 (fun p : ℝ × ℝ^n ↦ Φ p.1 p.2) (0, x))
    (hΦ₀ : Φ 0 =ᶠ[𝓝 x] id)
    (hinvariant : (fun t ↦ fieldDensity L (U t) x) =ᶠ[𝓝 0]
      (fun t ↦ transformedDensity L (fun _ ↦ U 0) Φ t x))
    (hEL : ∀ k, classicalEulerLagrange L (U 0) x k = 0) :
    ∇· (noetherCurrent L (U 0)
      (fun y ↦ deriv (fun t ↦ U t y) 0)
      (fun y ↦ -deriv (fun t ↦ Φ t y) 0)) x = 0 := by
  rw [divergence_noetherCurrent_of_domain_invariance hL hU hΦ hΦ₀ hinvariant]
  simp only [hEL, zero_mul, Finset.sum_const_zero, neg_zero]

end PDE.CalculusOfVariations.Noether
