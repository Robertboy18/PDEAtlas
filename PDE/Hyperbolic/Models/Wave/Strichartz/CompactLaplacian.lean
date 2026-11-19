/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Strichartz.KirchhoffNewton
import PDE.Elliptic.Classical.Poisson.FundamentalSolution
import PDE.FDeriv.Laplacian.Regularity

/-!
# The free wave in terms of a compact displacement's Laplacian

Poisson inversion identifies the Newtonian potential of the negative Laplacian
of a compact C³ displacement with the displacement itself. The signed-time
Kirchhoff/Newton identity then expresses its free wave using the exterior kernel.
This identity does not require the Newtonian potential of arbitrary data to be in L².
-/

@[expose] public section

open MeasureTheory Set
open PDE (laplacian)

namespace WaveEquation.Strichartz

/-- For compactly supported C³ displacement, the free wave is the exterior Newtonian
kernel applied to its negative Laplacian, with the Poisson normalization. -/
theorem kirchhoffFormula_eq_integral_exteriorNewtonKernel_laplacian {g : ℝ^3 → ℝ}
    (hg : ContDiff ℝ 3 g) (hgc : HasCompactSupport g) (x : ℝ^3) {t : ℝ} (ht : t ≠ 0) :
    kirchhoffFormula g (fun _ ↦ 0) x t = (4 * Real.pi)⁻¹ *
      ∫ y, exteriorNewtonKernel |t| (x - y) * (-laplacian g y) := by
  let g₂ : TestFunction (⊤ : TopologicalSpace.Opens (ℝ^3)) ℝ 2 :=
    ⟨g, hg.of_le (by norm_num), hgc, subset_univ _⟩
  have hinv : convolution (PotentialTheory.fundamentalSolution 3)
      (fun y ↦ -laplacian g y) (ContinuousLinearMap.mul ℝ ℝ) = g := by
    funext z
    have h := PoissonEquation.negative_laplacian_fundamentalSolutionConvolution
      (by norm_num : 2 ≤ 3) g₂ z
    rw [PoissonEquation.laplacian_fundamentalSolutionConvolution] at h
    simpa only [g₂, TestFunction.coe_mk, convolution_mul, mul_neg, integral_neg] using h
  have h := kirchhoffFormula_convolution_fundamentalSolution
    (hg.coordinate_laplacian (k := 1) (by norm_num)).neg hgc.coordinate_laplacian.neg x ht
  rwa [hinv] at h

end WaveEquation.Strichartz
