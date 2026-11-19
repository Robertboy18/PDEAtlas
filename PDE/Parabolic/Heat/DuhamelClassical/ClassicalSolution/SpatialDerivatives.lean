/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Duhamel.SpatialDifferentiation
import PDE.Analysis.Calculus.Support.Parametric
import PDE.FDeriv.SpaceTime.SpatialJets
import PDE.FDeriv.PartialDeriv.Support.Parametric
import PDE.Parabolic.Heat.ConvolutionSpace.JointContinuity
import PDE.Parabolic.Heat.DuhamelClassical.ClassicalSolution.SpatialJets.SpatialDerivatives

/-!
# Spatial derivatives of classical Duhamel solutions

Spatial derivatives pass through Duhamel's time integral by differentiating the source.
The source derivatives have compact support and uniform bounds, so the interchange also
holds near heat age zero. Here the argument is applied to a globally `C²` source.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.1, Theorem 2 and step 1 of its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace HeatEquation

open Set MeasureTheory Filter PDE.Common
open scoped Interval Topology

variable {n : ℕ}

/-- For a globally `C²`, compactly supported source, each mixed second spatial derivative passes
through the Duhamel source-time integral. -/
theorem nonhomogeneousSolution_secondPartial_classical
    (f : ℝ^(n + 1) → ℝ)
    (hf2 : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (x : ℝ^n) (t : ℝ) (ht : 0 < t) (i j : Fin n) :
    (∂[i]
        (fun z ↦
          (∂[j]
            (fun x' : ℝ^n ↦
              nonhomogeneousSolution (n := n) f x' t))
            z))
        x =
      ∫ s in Set.Icc 0 t,
        (∂[i]
          (fun z ↦
            (∂[j]
              (fun x' : ℝ^n ↦
                initialValueSolution (n := n)
                  (fun y : ℝ^n ↦
                    f (timeSpaceCons (n := n) s y))
                  x' (t - s)))
              z))
          x ∧
    IntervalIntegrable
      (fun s ↦
        (∂[i]
          (fun z ↦
            (∂[j]
              (fun x' : ℝ^n ↦
                initialValueSolution (n := n)
                  (fun y : ℝ^n ↦
                    f (timeSpaceCons (n := n) s y))
                  x' (t - s)))
              z))
          x)
      volume 0 t := by
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
  obtain ⟨M, C, B, hM, hC, hB⟩ :=
    PDE.FDeriv.exists_uniform_spatial_jet_bounds _ hg hglobal hfirst hsecond
  have hsource (s : ℝ) :
      (∂[i] (∂[j] (fun z ↦ initialValueSolution (g s) z (t - s)))) x =
        initialValueSolution (∂[i] (∂[j] (g s))) x (t - s) :=
    secondPartial_initialValueSolution_eq_source_all_time (g s) (hg2 s) (hgc s) x (t - s) i j
  change _ = ∫ s in Icc 0 t,
      (∂[i] (∂[j] (fun z ↦ initialValueSolution (g s) z (t - s)))) x ∧ _
  have hrepr : (fun z ↦ nonhomogeneousSolution f z t) =
      fun z ↦ ∫ s in 0..t, initialValueSolution (g s) z (t - s) := by
    funext z
    rw [nonhomogeneousSolution_eq_integral_initialValueSolution f z t ht,
      intervalIntegral.integral_of_le ht.le, ← integral_Icc_eq_integral_Ioc]
  constructor
  · rw [hrepr]
    simp_rw [hsource]
    rw [secondPartial_integral_initialValueSolution_eq_source
      g hg hg2 hgc (fun s y ↦ hM (s, y)) hfirst C (fun i s y ↦ hC i (s, y))
        hsecond B (fun i j s y ↦ hB i j (s, y)),
      intervalIntegral.integral_of_le ht.le, ← integral_Icc_eq_integral_Ioc]
  · change IntervalIntegrable
      (fun s ↦ (∂[i]
        (∂[j] (fun z ↦ initialValueSolution (g s) z (t - s)))) x) volume 0 t
    simp_rw [hsource]
    exact ((continuous_initialValueSolution_family (hsecond i j)
      (fun p ↦ hB i j p)).comp
        (continuous_id.prodMk
          (continuous_const.prodMk (continuous_const.sub continuous_id)))).intervalIntegrable 0 t

end HeatEquation
