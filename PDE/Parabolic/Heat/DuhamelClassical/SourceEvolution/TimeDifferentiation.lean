/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.ConvolutionTime.SourceDerivatives
public import PDE.Parabolic.Heat.Duhamel.Representation
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import PDE.FDeriv.SpaceTime
import PDE.Parabolic.Heat.Kernel.Integrability

/-!
# Dependence of heat evolution on source time

At a fixed positive heat age, differentiation in the source parameter passes through the
convolution. These formulas support the heat-age representation of Duhamel's integral, Evans's
change of variables `u(x, t) = ∫₀ᵗ ∫ Φ(y, s) f(x - y, t - s) dy ds` in step 1 of his proof of
§2.3.1(c), Theorem 2. Derivatives in heat age itself belong to `ConvolutionTime.SourceDerivatives`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.1(c), proof of Theorem 2 (Solution of nonhomogeneous
  problem), step 1, p. 50.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace HeatEquation

open scoped Pointwise Topology Interval Convolution
open PDE.Common
open MeasureTheory

variable {n : ℕ}

/-- Duhamel's formula after the substitution from source time to heat age. -/
theorem nonhomogeneousSolution_eq_age_integral
    (f : ℝ^(n + 1) → ℝ)
    (x : ℝ^n) (t : ℝ) (ht : 0 < t) :
    nonhomogeneousSolution (n := n) f x t =
      ∫ r in (0 : ℝ)..t,
        initialValueSolution (n := n)
          (fun y : ℝ^n ↦
            f (timeSpaceCons (n := n) (t - r) y))
          x r := by
  rw [nonhomogeneousSolution_eq_integral_initialValueSolution (n := n) f x t ht,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht.le]
  simpa using intervalIntegral.integral_comp_sub_left (fun r ↦ initialValueSolution (n := n)
    (fun y : ℝ^n ↦ f (timeSpaceCons (n := n) (t - r) y)) x r) t (a := (0 : ℝ)) (b := t)

/-- Every source-time slice of `f` vanishes off the spatial shadow of the support of `f`. -/
private theorem apply_timeSpaceCons_eq_zero_of_notMem (f : ℝ^(n + 1) → ℝ) (q : ℝ) {y : ℝ^n}
    (hy : y ∉ spatialPart '' tsupport f) : f (timeSpaceCons (n := n) q y) = 0 := by
  by_contra hne
  exact hy ⟨_, subset_closure hne, by ext i; simp only [spatialPart_apply, timeSpaceCons_succ]⟩

/-- At fixed positive heat age, heat evolution is jointly Fréchet differentiable in the
source time and observation point. -/
theorem hasFDerivAt_initialValueSolution_sourceTimeSpace
    (f : ℝ^(n + 1) → ℝ)
    (hf2 : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (x : ℝ^n) (r s : ℝ) (hr : 0 < r) :
    HasFDerivAt
      (fun p : ℝ × ℝ^n ↦
        initialValueSolution (n := n)
          (fun y : ℝ^n ↦
            f (timeSpaceCons (n := n) p.1 y))
          p.2 r)
      (convolution
        (fun z : ℝ^n ↦
          fundamentalSolutionHeat (n := n) z r)
        (fun y : ℝ^n ↦
          fderiv ℝ
            (fun p : ℝ × ℝ^n ↦
              f (timeSpaceCons (n := n) p.1 p.2))
            (s, y))
        ((ContinuousLinearMap.mul ℝ ℝ).precompR
          (ℝ × ℝ^n))
        volume x)
      (s, x) := by
  have hg1 : ContDiff ℝ 1 fun p : ℝ × ℝ^n ↦ f (timeSpaceCons (n := n) p.1 p.2) := by
    simpa [Function.comp_def] using
      (hf2.comp (contDiff_timeSpaceCons_uncurry n)).of_le (by norm_num)
  rw [show (fun p : ℝ × ℝ^n ↦ initialValueSolution (n := n)
      (fun y : ℝ^n ↦ f (timeSpaceCons (n := n) p.1 y)) p.2 r) = fun p ↦ convolution
        (fun z : ℝ^n ↦ fundamentalSolutionHeat (n := n) z r)
        (fun y ↦ f (timeSpaceCons (n := n) p.1 y)) (ContinuousLinearMap.mul ℝ ℝ) volume p.2 from
    funext fun p ↦ initialValueSolution_eq_convolution _ p.2 r hr]
  exact MeasureTheory.hasFDerivAt_convolution_right_with_param
    (g := fun q y ↦ f (timeSpaceCons (n := n) q y)) _ isOpen_univ
    (hfc.isCompact.image (spatialPartCLM n).continuous)
    (fun q _ _ hy ↦ apply_timeSpaceCons_eq_zero_of_notMem f q hy)
    (fundamentalSolutionHeat_integrable (n := n) r hr).locallyIntegrable hg1.contDiffOn (s, x)
    (Set.mem_univ s)

/-- At fixed positive heat age, source-time differentiation commutes with heat evolution.

Compact support supplies one common spatial support for all source-time slices, so Mathlib's
parameterized convolution derivative applies directly. -/
theorem hasDerivAt_initialValueSolution_sourceTime
    (f : ℝ^(n + 1) → ℝ)
    (hf2 : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (x : ℝ^n) (r s : ℝ) (hr : 0 < r) :
    HasDerivAt
      (fun q ↦
        initialValueSolution (n := n)
          (fun y : ℝ^n ↦
            f (timeSpaceCons (n := n) q y))
          x r)
      (initialValueSolution (n := n)
        (fun y : ℝ^n ↦
          deriv (fun q ↦ f (timeSpaceCons (n := n) q y)) s)
        x r)
      s := by
  have hK : IsCompact (spatialPart '' tsupport f) :=
    hfc.isCompact.image (spatialPartCLM n).continuous
  have hg1 : ContDiff ℝ 1 fun p : ℝ × ℝ^n ↦ f (timeSpaceCons (n := n) p.1 p.2) := by
    simpa [Function.comp_def] using
      (hf2.comp (contDiff_timeSpaceCons_uncurry n)).of_le (by norm_num)
  have hDcompact : HasCompactSupport fun y : ℝ^n ↦
      fderiv ℝ (fun p : ℝ × ℝ^n ↦ f (timeSpaceCons (n := n) p.1 p.2)) (s, y) := by
    refine HasCompactSupport.intro hK fun y hy ↦ ?_
    have hzero : (fun p : ℝ × ℝ^n ↦ f (timeSpaceCons (n := n) p.1 p.2)) =ᶠ[nhds (s, y)]
        fun _ ↦ 0 :=
      Filter.mem_of_superset ((continuous_snd.continuousAt (x := (s, y))).preimage_mem_nhds
        (hK.isClosed.isOpen_compl.mem_nhds hy)) fun p hp ↦
          apply_timeSpaceCons_eq_zero_of_notMem f p.1 hp
    exact (hasFDerivAt_zero_of_eventually_const (0 : ℝ) hzero).fderiv
  have hdg (y : ℝ^n) : fderiv ℝ (fun p : ℝ × ℝ^n ↦ f (timeSpaceCons (n := n) p.1 p.2)) (s, y)
      ((1 : ℝ), (0 : ℝ^n)) = deriv (fun q ↦ f (timeSpaceCons (n := n) q y)) s := by
    have h : HasDerivAt (fun q ↦ f (timeSpaceCons (n := n) q y))
        (fderiv ℝ (fun p : ℝ × ℝ^n ↦ f (timeSpaceCons (n := n) p.1 p.2)) (s, y)
          ((1 : ℝ), (0 : ℝ^n))) s := by
      simpa only [Function.comp_apply, id_eq] using!
        (hg1.differentiable one_ne_zero (s, y)).hasFDerivAt.comp_hasDerivAt s
          ((hasDerivAt_id s).prodMk (hasDerivAt_const s y))
    exact h.deriv.symm
  have hcomp := (hasFDerivAt_initialValueSolution_sourceTimeSpace f hf2 hfc x r s
    hr).comp_hasDerivAt s ((hasDerivAt_id s).prodMk (hasDerivAt_const s x))
  rw [MeasureTheory.convolution_precompR_apply (L := ContinuousLinearMap.mul ℝ ℝ)
    (fundamentalSolutionHeat_integrable (n := n) r hr).locallyIntegrable hDcompact
    ((hg1.continuous_fderiv one_ne_zero).comp (continuous_const.prodMk continuous_id))] at hcomp
  rw [initialValueSolution_eq_convolution _ x r hr]
  simpa only [Function.comp_apply, id_eq, hdg] using! hcomp

end HeatEquation
