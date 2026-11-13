/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

import Mathlib.MeasureTheory.Measure.Haar.Unique
public import PDE.FDeriv.Calculus
public import Mathlib.Analysis.Convolution
public import PDE.Parabolic.Heat.InitialValue
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import PDE.Analysis.Integration.ConvolutionDerivative
import PDE.Parabolic.Heat.Kernel.Integrability

/-!
# Spatial differentiation of heat evolution

For a compactly supported `C²` datum `g` and heat age `r > 0`, spatial derivatives of
`initialValueSolution g · r` can be transferred to `g` rather than to the kernel:
`∂ᵢ∂ⱼ (Γ_r * g) = Γ_r * (∂ᵢ∂ⱼ g)` and `∇(Γ_r * g) = Γ_r * ∇g`. This is the form needed
for Duhamel's formula, where the source slices are smooth with compact support while the
heat age `t - s` degenerates as `s → t`; putting the derivatives on the source gives
bounds uniform in the heat age.  The interchange is Mathlib's differentiation of
convolutions with a locally integrable left factor and a compactly supported smooth right
factor.

## Main results

* `initialValueSolution_eq_convolution`: at positive time `initialValueSolution` is Mathlib's
  `convolution` of the kernel with `g`.
* `secondPartial_initialValueSolution_eq_convolution_source`: every mixed second spatial
  derivative of the heat evolution equals the heat evolution of `∂ᵢ∂ⱼ g`.
* `hasFDerivAt_initialValueSolution_space_source`: the spatial Fréchet derivative is
  `∑ᵢ (Γ_r * ∂ᵢ g)(x) · projᵢ`, for `g` of class `C¹` with compact support.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.1, Theorem 2; step 1 of its proof moves the
  derivatives onto the source in the same way.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (partialDeriv iteratedPartialDeriv)

namespace HeatEquation

open scoped Pointwise Topology Interval Convolution
open PDE.Common
open MeasureTheory

variable {n : ℕ}

/-- At positive time, `initialValueSolution` is the ordinary convolution with the heat kernel. -/
theorem initialValueSolution_eq_convolution
    (g : ℝ^n → ℝ)
    (x : ℝ^n) (r : ℝ) (hr : 0 < r) :
    initialValueSolution (n := n) g x r =
      convolution
        (fun z : ℝ^n ↦
          fundamentalSolutionHeat (n := n) z r)
        g (ContinuousLinearMap.mul ℝ ℝ) volume x := by
  let Γ : (ℝ^n) → ℝ := fun z ↦ fundamentalSolutionHeat (n := n) z r
  let L := ContinuousLinearMap.mul ℝ ℝ
  simp only [initialValueSolution, not_le_of_gt hr, ↓reduceIte]
  change
    (∫ y : (ℝ^n), Γ (x - y) * g y) =
      convolution Γ g L volume x
  simpa [L] using
    (MeasureTheory.convolution_eq_swap
      (f := Γ) (g := g) (L := L) (μ := volume) (x := x)).symm

/-- For a compactly supported `C²` datum, any two spatial coordinate derivatives
of its heat evolution can be transferred to the datum. The coordinates may differ. -/
theorem secondPartial_initialValueSolution_eq_convolution_source
    (g : ℝ^n → ℝ)
    (hg2 : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (x : ℝ^n) (r : ℝ) (hr : 0 < r) (i j : Fin n) :
    (∂[i]
        (fun z ↦
          (∂[j]
            (fun x' ↦ initialValueSolution (n := n) g x' r)) z))
        x =
      initialValueSolution (n := n)
        (fun y ↦
          (∂[i]
            (fun z ↦ (∂[j] g) z)) y)
        x r := by
  let Γ : (ℝ^n) → ℝ := fun z ↦ fundamentalSolutionHeat (n := n) z r
  let L := ContinuousLinearMap.mul ℝ ℝ
  have hΓ : LocallyIntegrable Γ (volume : Measure (ℝ^n)) :=
    (fundamentalSolutionHeat_integrable (n := n) r hr).locallyIntegrable
  have hleft :
      (fun x' ↦ initialValueSolution (n := n) g x' r) =
        convolution Γ g L volume := by
    funext x'
    exact initialValueSolution_eq_convolution g x' r hr
  rw [hleft, initialValueSolution_eq_convolution _ x r hr]
  simpa [iteratedPartialDeriv] using
    PDE.Analysis.convolution_iteratedPartialDeriv_two_right
      Γ g hΓ hgc hg2 i j x

/-- At positive heat age, the full spatial derivative is obtained by evolving the coordinate
derivatives of the source. -/
theorem hasFDerivAt_initialValueSolution_space_source
    (g : ℝ^n → ℝ)
    (hg1 : ContDiff ℝ 1 g) (hgc : HasCompactSupport g)
    (x : ℝ^n) (r : ℝ) (hr : 0 < r) :
    HasFDerivAt
      (fun z ↦ initialValueSolution (n := n) g z r)
      (∑ i : Fin n,
        (initialValueSolution (n := n)
          (fun y ↦ (∂[i] g) y) x r) •
            (EuclideanSpace.proj i :
              ℝ^n →L[ℝ] ℝ))
      x := by
  let Γ : (ℝ^n) → ℝ := fun z ↦ fundamentalSolutionHeat (n := n) z r
  let L := ContinuousLinearMap.mul ℝ ℝ
  let D : (ℝ^n) →L[ℝ] ℝ :=
    convolution Γ (fderiv ℝ g) (L.precompR (ℝ^n)) volume x
  have hΓ : LocallyIntegrable Γ (volume : Measure (ℝ^n)) :=
    (fundamentalSolutionHeat_integrable (n := n) r hr).locallyIntegrable
  have hbase :
      HasFDerivAt (fun z ↦ convolution Γ g L volume z) D x := by
    simpa [D, L] using
      hgc.hasFDerivAt_convolution_right
        (L := ContinuousLinearMap.mul ℝ ℝ) hΓ hg1 x
  have hcoeff (i : Fin n) :
      D (EuclideanSpace.single i (1 : ℝ)) =
        initialValueSolution (n := n)
          (fun y ↦ (∂[i] g) y) x r := by
    have hprecomp :
        D (EuclideanSpace.single i (1 : ℝ)) =
          convolution Γ
            (fun y ↦ fderiv ℝ g y (EuclideanSpace.single i (1 : ℝ)))
            L volume x := by
      simpa [D, L] using
        MeasureTheory.convolution_precompR_apply
          (L := ContinuousLinearMap.mul ℝ ℝ) hΓ (hgc.fderiv ℝ)
          (hg1.continuous_fderiv one_ne_zero) x
          (EuclideanSpace.single i (1 : ℝ))
    rw [hprecomp, initialValueSolution_eq_convolution
      (n := n) (fun y ↦ (∂[i] g) y) x r hr]
    rfl
  rw [show (fun z ↦ initialValueSolution (n := n) g z r) = fun z ↦ convolution Γ g L volume z
    from funext fun z ↦ initialValueSolution_eq_convolution (n := n) g z r hr]
  convert hbase using 1
  rw [← hbase.fderiv, PDE.fderiv_eq_sum_partialDeriv_smul_proj]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← hcoeff i, ← hbase.fderiv]
  rfl

/-- Spatial differentiation commutes with heat evolution, including the constant extension to
nonpositive heat ages. -/
theorem hasFDerivAt_initialValueSolution_space_source_all_time
    (g : ℝ^n → ℝ) (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g)
    (x : ℝ^n) (r : ℝ) :
    HasFDerivAt (fun z ↦ initialValueSolution g z r)
      (∑ i : Fin n, initialValueSolution (∂[i] g) x r •
        (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ)) x := by
  by_cases hr : r ≤ 0
  · simp only [initialValueSolution_of_t_le_zero _ _ hr]
    rw [← PDE.fderiv_eq_sum_partialDeriv_smul_proj]
    exact (hg.differentiable one_ne_zero x).hasFDerivAt
  · exact hasFDerivAt_initialValueSolution_space_source g hg hgc x r (lt_of_not_ge hr)

/-- A spatial coordinate derivative of heat evolution is the heat evolution of the corresponding
derivative of the datum. -/
theorem partialDeriv_initialValueSolution_eq_source
    (g : ℝ^n → ℝ) (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g)
    (x : ℝ^n) (r : ℝ) (i : Fin n) :
    (∂[i] (fun z ↦ initialValueSolution g z r)) x =
      initialValueSolution (∂[i] g) x r := by
  simp [partialDeriv,
    (hasFDerivAt_initialValueSolution_space_source_all_time g hg hgc x r).fderiv]

/-- Both pure and mixed second spatial derivatives transfer to the datum at every heat age. -/
theorem secondPartial_initialValueSolution_eq_source_all_time
    (g : ℝ^n → ℝ) (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (x : ℝ^n) (r : ℝ) (i j : Fin n) :
    (∂[i] (∂[j] (fun z ↦ initialValueSolution g z r))) x =
      initialValueSolution (∂[i] (∂[j] g)) x r := by
  by_cases hr : r ≤ 0
  · simp only [initialValueSolution_of_t_le_zero _ _ hr]
  · exact secondPartial_initialValueSolution_eq_convolution_source
      g hg hgc x r (lt_of_not_ge hr) i j

end HeatEquation
