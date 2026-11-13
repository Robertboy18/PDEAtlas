/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.PartialDeriv
public import PDE.Parabolic.Heat.Duhamel.Representation
import PDE.Analysis.Calculus.Support.Parametric
import PDE.FDeriv.SpaceTime.SpatialJets
import PDE.FDeriv.PartialDeriv.Support.Parametric
import PDE.Parabolic.Heat.DuhamelClassical.ClassicalSolution.SpatialJets.TimeDerivative

/-!
# Moving-boundary differentiation for classical Duhamel solutions

The time derivative of Duhamel's formula contains the source at the moving endpoint and
the integral of the heat evolution of its Laplacian. Compact spatial derivative bounds
justify differentiation through the integral, including where the heat age vanishes.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.1, Theorem 2 (solution of nonhomogeneous problem).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace HeatEquation

open Set MeasureTheory Filter PDE.Common
open scoped Interval Topology

variable {n : ℕ}

/-- Classical moving-boundary differentiation of Duhamel's formula. The derivative bound at
heat age zero comes from the source's second spatial derivatives. -/
theorem hasDerivAt_nonhomogeneousSolution_classical
    (f : ℝ^(n + 1) → ℝ)
    (hf2 : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (x : ℝ^n) (t : ℝ) (ht : 0 < t) :
    HasDerivAt
      (fun τ ↦ nonhomogeneousSolution (n := n) f x τ)
      (f (timeSpaceCons (n := n) t x) +
        ∫ s in (0 : ℝ)..t,
          ∑ i : Fin n,
            initialValueSolution (n := n)
              (fun y ↦
                (∂[i]
                  (fun z ↦
                    (∂[i]
                      (fun w ↦ f (timeSpaceCons (n := n) s w))) z))
                  y)
              x (t - s))
      t := by
  let g : ℝ → ℝ^n → ℝ := fun s y ↦ f (timeSpaceCons s y)
  have hg : Continuous (Function.uncurry g) :=
    (hf2.comp (contDiff_timeSpaceCons_uncurry n)).continuous
  have hg2 (s : ℝ) : ContDiff ℝ 2 (g s) :=
    hf2.comp (contDiff_timeSpaceCons_spatial n s)
  have hglobal : HasCompactSupport (Function.uncurry g) :=
    hfc.comp_homeomorph (timeSpaceContinuousLinearEquiv n).symm.toHomeomorph
  have hgc (s : ℝ) : HasCompactSupport (g s) := hglobal.slice_snd s
  have hfirst (i : Fin n) : Continuous
      (fun p : ℝ × ℝ^n ↦ (∂[i] (g p.1)) p.2) :=
    PDE.continuous_partialDeriv_timeSpaceCons_spatial f (hf2.of_le (by norm_num)) i
  have hsecond (i j : Fin n) : Continuous
      (fun p : ℝ × ℝ^n ↦ (∂[i] (∂[j] (g p.1))) p.2) :=
    PDE.continuous_secondPartialDeriv_timeSpaceCons_spatial f hf2 i j
  obtain ⟨M, _, B, hM, _, hB⟩ :=
    PDE.FDeriv.exists_uniform_spatial_jet_bounds _ hg hglobal hfirst hsecond
  have hd := hasDerivAt_integral_initialValueSolution_of_spatial_jets
    g hg hg2 hgc (fun s y ↦ hM (s, y)) (fun i ↦ hsecond i i)
      (fun i ↦ B i i) (fun i s y ↦ hB i i (s, y)) x t ht
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds ht] with τ hτ
  rw [nonhomogeneousSolution_eq_integral_initialValueSolution f x τ hτ,
    intervalIntegral.integral_of_le hτ.le, ← integral_Icc_eq_integral_Ioc]

end HeatEquation
