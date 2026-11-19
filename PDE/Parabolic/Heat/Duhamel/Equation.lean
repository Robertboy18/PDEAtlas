/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Duhamel.Representation
public import PDE.Parabolic.Heat.InitialValueProblem
import PDE.FDeriv.SpaceTime
import PDE.Parabolic.Heat.ConvolutionSpace.Equation

/-!
# The forced heat equation from Duhamel's formula

The homogeneous heat identity and the time and space differentiation formulas combine to give
`u_t - Δu = f` for the Duhamel term, part (ii) of Evans's §2.3.1(c), Theorem 2. With the zero
initial value, this makes the Duhamel term a solution of the forced heat `PDEProblem`. The
interchange and joint differentiability hypotheses are explicit here and are proved for classical
sources in `DuhamelClassical`.

## How it works

Evans moves the derivatives onto `f` by the change of variables
`u = ∫₀ᵗ ∫ Φ(y, s) f(x - y, t - s) dy ds`, splits the time integral at `ε` in (14), and integrates
by parts in (16). We differentiate the source-time integral directly: by
`deriv_initialValueSolution_time_eq_laplacian` each slice `s < t` solves the homogeneous heat
equation, and the moving upper limit contributes `f(t, x)`, the approximate-identity limit recorded
in the hypothesis `hleibniz` of `nonhomogeneousSolution_positive_time_residual`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.1(c), Duhamel's principle, (13), p. 49, and Theorem 2
  (Solution of nonhomogeneous problem) and its proof, (14)-(16), pp. 50-51.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (laplacian SatisfiesPDEProblem)

namespace HeatEquation

open scoped Pointwise Topology Interval
open PDE.Common
open MeasureTheory

variable {n : ℕ}

/-- Part (ii) of Evans's §2.3.1(c), Theorem 2 at a positive-time point.

`hleibniz` is the moving-boundary differentiation statement; its explicit `f(t,x)` term records
the approximate-identity limit at the singular corner. `hsecond` and `hsecond_integrable` state
that both spatial derivatives pass through the source-time integral. Under exactly these
calculus hypotheses, every interior source slice solves the homogeneous heat equation by
`deriv_initialValueSolution_time_eq_laplacian`, so the Duhamel term satisfies
`u_t - Δu = f`. -/
theorem nonhomogeneousSolution_positive_time_residual
    (f : ℝ^(n + 1) → ℝ)
    (x : ℝ^n) (t : ℝ) (ht : 0 < t)
    (hf_cont : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      Continuous fun y : ℝ^n ↦
        f (timeSpaceCons (n := n) s y))
    (hf_bdd : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      ∃ M : ℝ, ∀ y : ℝ^n,
        |f (timeSpaceCons (n := n) s y)| ≤ M)
    (hleibniz :
      HasDerivAt (fun τ ↦ nonhomogeneousSolution (n := n) f x τ)
        (f (timeSpaceCons (n := n) t x) +
          ∫ s in Set.Icc 0 t,
            deriv
              (fun r ↦
                initialValueSolution (n := n)
                  (fun y : ℝ^n ↦
                    f (timeSpaceCons (n := n) s y))
                  x r)
              (t - s))
        t)
    (hsecond : ∀ i : Fin n,
      (∂[i]
          (fun z ↦
            (∂[i]
              (fun x' : ℝ^n ↦
                nonhomogeneousSolution (n := n) f x' t))
              z))
          x =
        ∫ s in Set.Icc 0 t,
          (∂[i]
            (fun z ↦
              (∂[i]
                (fun x' : ℝ^n ↦
                  initialValueSolution (n := n)
                    (fun y : ℝ^n ↦
                      f (timeSpaceCons (n := n) s y))
                    x' (t - s)))
                z))
            x)
    (hsecond_integrable : ∀ i : Fin n,
      IntervalIntegrable
        (fun s ↦
          (∂[i]
            (fun z ↦
              (∂[i]
                (fun x' : ℝ^n ↦
                  initialValueSolution (n := n)
                    (fun y : ℝ^n ↦
                      f (timeSpaceCons (n := n) s y))
                    x' (t - s)))
                z))
            x)
        volume 0 t) :
    deriv (fun τ ↦ nonhomogeneousSolution (n := n) f x τ) t -
        laplacian (n := n)
          (fun x' ↦ nonhomogeneousSolution (n := n) f x' t) x =
      f (timeSpaceCons (n := n) t x) := by
  have hinterior : (∫ s in Set.Icc 0 t, deriv (fun r ↦ initialValueSolution (n := n)
        (fun y : ℝ^n ↦ f (timeSpaceCons (n := n) s y)) x r) (t - s)) =
      ∫ s in Set.Icc 0 t, laplacian (n := n) (fun x' ↦ initialValueSolution (n := n)
        (fun y : ℝ^n ↦ f (timeSpaceCons (n := n) s y)) x' (t - s)) x := by
    rw [integral_Icc_eq_integral_Ioo, integral_Icc_eq_integral_Ioo]
    exact setIntegral_congr_fun measurableSet_Ioo fun s hs ↦
      deriv_initialValueSolution_time_eq_laplacian _ x (t - s) (sub_pos.mpr hs.2) (hf_cont s hs)
        (hf_bdd s hs)
  rw [hleibniz.deriv, hinterior]
  simp only [laplacian]
  rw [Finset.sum_congr rfl fun i _ ↦ hsecond i, ← integral_finsetSum _ fun i _ ↦
    (intervalIntegrable_iff_integrableOn_Icc_of_le ht.le).mp (hsecond_integrable i)]
  ring

/-- The zero-data Duhamel term satisfies the nonhomogeneous heat `PDEProblem`.

`hjoint` is needed because the `PDEProblem` coordinate derivative is the full spacetime
Fréchet derivative evaluated in the time direction. -/
theorem nonhomogeneousSolution_satisfiesPDEProblem_of_residual
    (f : ℝ^(n + 1) → ℝ)
    (hres : ∀ (x : ℝ^n) (t : ℝ), 0 < t →
      deriv (fun τ ↦ nonhomogeneousSolution (n := n) f x τ) t -
          laplacian (n := n)
            (fun x' ↦ nonhomogeneousSolution (n := n) f x' t) x =
        f (timeSpaceCons (n := n) t x))
    (hjoint : ∀ xt : ℝ^(n + 1), 0 < xt 0 →
      DifferentiableAt ℝ
        (fun zt : ℝ^(n + 1) ↦
          nonhomogeneousSolution (n := n) f (spatialPartCLM n zt) (zt 0))
        xt) :
    SatisfiesPDEProblem
      (forcedHeatResidualAssignedInitialValueProblem (n := n) f
        (fun _ : ℝ^n ↦ 0))
      (fun xt : ℝ^(n + 1) ↦
        nonhomogeneousSolution (n := n) f (spatialPartCLM n xt) (xt 0)) := by
  let U : ℝ^(n + 1) → ℝ := fun xt ↦
    nonhomogeneousSolution (n := n) f (spatialPartCLM n xt) (xt 0)
  refine forcedHeatResidualAssignedInitialValueProblem.of_residual_initial (n := n)
    (u := U) (fun xt hxt ↦ ?_) fun xt hxt ↦ by simp [U, hxt, nonhomogeneousSolution_initial_value]
  have hp : timeSpaceCons (n := n) (xt 0) (spatialPartCLM n xt) = xt := by simp
  unfold heatOperator
  rw [← hp, PDE.partialDeriv_timeSpaceCons_eq_deriv (n := n) U _ _ (hp ▸ hjoint xt hxt)]
  simpa only [U, timeSpaceCons_zero, spatialPartCLM_timeSpaceCons] using hres _ _ hxt

end HeatEquation
