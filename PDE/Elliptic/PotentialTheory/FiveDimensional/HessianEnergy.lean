/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.FiveDimensional.NewtonianPotential
public import PDE.Analysis.Integration.HessianEnergy
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import PDE.Elliptic.PotentialTheory.FundamentalSolution.LocalIntegrability

/-!
# Energy of the five-dimensional Newtonian Hessian

For a smooth compact source, the sum of the squared L² norms of all Cartesian
Hessian entries equals the squared source norm. The four axial mixed entries
have combined norm at most half the source norm.

The potential need not have compact support. Its first three derivative orders
belong to L², which supplies the hypotheses of the global integration-by-parts
identities. The Poisson equation identifies the Laplacian with the source.
-/

@[expose] public section

open PDE (iteratedPartialDeriv)
open MeasureTheory
open scoped BigOperators
open PDE.Analysis

namespace PotentialTheory

/-- Compact source regularity passes to the convolution through the locally integrable kernel. -/
private theorem gammaConvolution_contDiff_three
    (f : ℝ^5 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) :
    ContDiff ℝ 3
      (convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume) := by
  exact hfc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    (locallyIntegrable_fundamentalSolution 5) (hf.of_le (WithTop.coe_le_coe.mpr le_top))

/-- Squaring the Poisson equation removes its sign before we integrate. -/
private theorem gammaConvolution_integral_laplacian_sq
    (f : ℝ^5 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) :
    (∫ X : ℝ^5, (∑ i : Fin 5, (∂[i]
      (∂[i]
        (convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume))) X) ^ 2) =
      ∫ X : ℝ^5, (f X) ^ 2 := by
  apply integral_congr_ae
  filter_upwards [] with X
  have hp : -(∑ i : Fin 5, (∂[i]
      (∂[i]
        (convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume))) X) =
      f X := by
    simpa only [iteratedPartialDeriv] using
      fundamentalSolution_five_convolution_solves_poisson f X hf hfc
  rw [← hp, neg_sq]

/-- The full Cartesian Hessian of the Newtonian convolution has the same squared
L² norm as its source. Smoothness and compact support of the source provide
all derivative integrability needed for the two integrations by parts. The sum
counts both orders of every mixed derivative. -/
theorem fundamentalSolution_five_convolution_hessian_energy
    (f : ℝ^5 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) :
    (∑ i : Fin 5, ∑ j : Fin 5, ∫ X : ℝ^5,
      ((∂[i] (∂[j]
        (convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume))) X) ^ 2) =
      ∫ X : ℝ^5, (f X) ^ 2 := by
  have h1 (i : Fin 5) :
      MemLp (∂[i]
        (convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume)) 2 volume :=
    fundamentalSolution_five_convolution_iteratedPartialDeriv_memLp_two f hf hfc [i]
  have h2 (i j : Fin 5) :
      MemLp (∂[i] (∂[j]
        (convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume))) 2 volume :=
    fundamentalSolution_five_convolution_iteratedPartialDeriv_memLp_two f hf hfc [i, j]
  have h3 (i j k : Fin 5) : MemLp
      (∂[i] (∂[j] (∂[k]
        (convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume))))
      2 volume :=
    fundamentalSolution_five_convolution_iteratedPartialDeriv_memLp_two f hf hfc [i, j, k]
  exact (PDE.Analysis.sum_integral_partialDeriv_sq_eq_laplacian_sq
    (gammaConvolution_contDiff_three f hf hfc) h1 h2 h3).trans
      (gammaConvolution_integral_laplacian_sq f hf hfc)

/-- The four axial mixed derivatives of the Newtonian convolution have combined
L² norm at most half the source norm. The factor follows from the nonnegative
square of the transverse Laplacian minus the axial second derivative. -/
theorem fundamentalSolution_five_convolution_axial_mixed_l2_le_half
    (f : ℝ^5 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) :
    Real.sqrt (∑ i : Fin 4, ∫ X : ℝ^5,
      ((∂[i.castSucc]
        (∂[(Fin.last 4)]
          (convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume))) X) ^ 2) ≤
      (1 / 2 : ℝ) * Real.sqrt (∫ X : ℝ^5, (f X) ^ 2) := by
  have h1 (i : Fin 5) :
      MemLp (∂[i]
        (convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume)) 2 volume :=
    fundamentalSolution_five_convolution_iteratedPartialDeriv_memLp_two f hf hfc [i]
  have h2 (i j : Fin 5) :
      MemLp (∂[i] (∂[j]
        (convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume))) 2 volume :=
    fundamentalSolution_five_convolution_iteratedPartialDeriv_memLp_two f hf hfc [i, j]
  have h3 (i j k : Fin 5) : MemLp
      (∂[i] (∂[j] (∂[k]
        (convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume))))
      2 volume :=
    fundamentalSolution_five_convolution_iteratedPartialDeriv_memLp_two f hf hfc [i, j, k]
  have h := PDE.Analysis.sqrt_sum_integral_axial_mixed_sq_le (n := 4)
    (gammaConvolution_contDiff_three f hf hfc) h1 h2 h3
  rw [gammaConvolution_integral_laplacian_sq f hf hfc] at h
  exact h

end PotentialTheory
