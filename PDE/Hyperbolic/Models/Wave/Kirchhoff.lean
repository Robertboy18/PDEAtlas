/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.EuclideanBall
public import Mathlib.Analysis.Calculus.Gradient.Basic
import PDE.FDeriv.Calculus

/-!
# Kirchhoff formula for the three-dimensional wave equation

We define the Kirchhoff candidate representation

`u(x, t) = (1 / (4π t²)) ∫_{∂B(x,t)} (t h(y) + g(y) + ∇g(y) · (y - x)) dS(y)`

(Kirchhoff's formula (22) of Evans, §2.4.1) and prove its
sharp wavefront-vanishing property for compactly supported initial data. The
propagation speed is normalized to `c = 1`. The support statement depends only
on the geometry of the sphere `∂B(x, t)`. The PDE and both limiting Cauchy traces
are proved in `Kirchhoff.ClassicalSolution` for `C³` displacement and `C²`
velocity data.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.4.1, equation (22) and Huygens' principle after Theorem 3.
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Gradient

@[expose] public section

namespace WaveEquation

open PDE.Analysis

/-- Candidate right-hand side of Kirchhoff's formula for the three-dimensional wave equation.

Analytically this representation is meant for `t > 0`.  This definition is only a total Lean
candidate expression: it uses `|t|` as the Metric.sphere radius and returns the initial position
data at `t = 0`.

`kirchhoffFormula_satisfiesResidualAssignedCauchyData` in `Kirchhoff.ClassicalSolution`
proves the wave equation and initial data; the same module proves joint `C²` regularity
and both limiting traces. -/
noncomputable def kirchhoffFormula
    (g h : ℝ^3 → ℝ)
    (x : ℝ^3) (t : ℝ) : ℝ :=
  let r := |t|
  if _hr : r = 0 then g x else
    (1 / (4 * Real.pi * r ^ 2)) *
      sphereIntegral 3 (fun y ↦ t * h y + g y + ∑ i, (∇ g y) i * (y i - x i)) x r

/--
Sharp Huygens principle for Kirchhoff's representation (Evans, §2.4.1, after Theorem 3).

If the initial displacement and velocity are supported in the closed ball of
radius `R`, then at a fixed point `x` Kirchhoff's formula vanishes after the
spherical wavefront has passed, namely for `t > R + ‖x‖`.
-/
theorem kirchhoffFormula_eq_zero_after_wavefront {g h : ℝ^3 → ℝ} {R t : ℝ} (x : ℝ^3) (hR : 0 ≤ R)
    (ht : R + ‖x‖ < t) (hg : Function.support g ⊆ Metric.closedBall 0 R)
    (hh : Function.support h ⊆ Metric.closedBall 0 R) :
    kirchhoffFormula g h x t = 0 := by
  have htpos : 0 < t := lt_of_le_of_lt (add_nonneg hR (norm_nonneg x)) ht
  simp only [kirchhoffFormula, abs_of_pos htpos, htpos.ne', dite_false]
  have hintegrand : Set.EqOn (fun y : ℝ^3 ↦ t * h y + g y + ∑ i, (∇ g y) i * (y i - x i))
        (fun _ ↦ (0 : ℝ))
        (Metric.sphere x t) := by
    intro y hy
    have hdist : t = dist y x := by
      simpa [Metric.mem_sphere] using hy.symm
    have hyNorm : R < ‖y‖ := by
      have htriangle : dist y x ≤ ‖y‖ + ‖x‖ := by
        rw [dist_eq_norm]
        exact norm_sub_le y x
      linarith
    have hyOutside : y ∉ Metric.closedBall (0 : ℝ^3) R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using (not_le_of_gt hyNorm)
    have hgy : g y = 0 := by
      by_contra hne
      exact hyOutside (hg hne)
    have hhy : h y = 0 := by
      by_contra hne
      exact hyOutside (hh hne)
    have hlocal :
        g =ᶠ[nhds y] (fun _ : ℝ^3 ↦ (0 : ℝ)) := by
      filter_upwards [Metric.isClosed_closedBall.isOpen_compl.mem_nhds hyOutside] with z hz
      by_contra hne
      exact hz (hg hne)
    have hgrad : ∇ g y = 0 := by
      ext i
      change ∇ g y i = 0
      rw [PDE.gradient_apply_eq_partialDeriv]
      calc
        (∂[i] g) y = (∂[i] (fun _ : ℝ^3 ↦ (0 : ℝ))) y :=
          PDE.partialDeriv_congr_nhds (n := 3) i hlocal
        _ = 0 := PDE.partialDeriv_const 0
    simp [hgy, hhy, hgrad]
  rw [sphereIntegral_congr_on_sphere htpos hintegrand]
  simp [sphereIntegral]

end WaveEquation
