/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Elliptic.Classical.Poisson.FundamentalSolution
public import PDE.Elliptic.Classical.Harmonic.SymbolDecay

/-!
# The Newtonian potential of a smooth source of mean zero

Let `f` be smooth, compactly supported and of mean zero on `ℝⁿ`, `n ≥ 3`. The potential `Φ ⋆ f`,
which solves `-Δu = f`, has symbol decay of order `1 - n`: its `j`th derivative is
`O(|x|^{1-n-j})`, one order better than the kernel. Hou, Wang and Yang invert the Laplacian for
such a source in their (2.3) and state that "the function `P_c` is smooth, and `∇ʲ P_c` decays
sufficiently fast as `O(|ξ|^{-j-2})`". This module proves that sentence in every dimension
`n ≥ 3`; the smoothness is `PoissonEquation.contDiff_fundamentalSolutionConvolution`. Without the
mean-zero hypothesis the potential only has the order `2 - n` of the kernel, a case not stated
here (`PoissonEquation.exists_bound_fundamentalSolutionConvolution` bounds it). In dimension two
the kernel is logarithmic and is not covered.

## Main results

* `PotentialTheory.hasSymbolDecay_fundamentalSolution`: for `n ≥ 3` the Newtonian kernel has
  symbol decay of order `2 - n`.
* `PoissonEquation.hasSymbolDecay_fundamentalSolutionConvolution`: for `n ≥ 3` and every smooth
  compactly supported source of mean zero, `Φ ⋆ f` has symbol decay of order `1 - n`.

## How it works

The kernel `Φ` is homogeneous of degree `2 - n` and smooth off the origin, so it has symbol decay
of that order. A source of mean zero gains one order: far from the support we may subtract `Φ(x)`
under the integral, and `Φ(t) - Φ(x)` is of order `‖x‖ ^ (1 - n)` for `t` near `x`
(`PDE.Analysis.HasSymbolDecay.exists_norm_convolution_le_of_integral_eq_zero`). That is the bound
of order zero. Outside the support of `f` the potential is harmonic
(`PoissonEquation.negative_laplacian_fundamentalSolutionConvolution`), and for a harmonic function
a bound on the function bounds every derivative with the right power
(`LaplacianEquation.IsHarmonicPDE.hasSymbolDecay`). No derivative of the singular kernel is taken
under the integral.

## References

* T. Y. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116, (2.3) and the sentence after it.
  <https://arxiv.org/abs/2509.25116>
-/

@[expose] public section

open PDE (laplacian)
open MeasureTheory PDE.Analysis PotentialTheory TopologicalSpace LaplacianEquation
open scoped Distributions ContDiff

namespace PotentialTheory

/-- In dimension at least three the Newtonian kernel has symbol decay of order `2 - n`: it is
homogeneous of that degree and smooth away from the origin. -/
theorem hasSymbolDecay_fundamentalSolution {n : ℕ} (hn : 3 ≤ n) :
    HasSymbolDecay (2 - n) (fundamentalSolution n) := by
  refine hasSymbolDecay_of_homogeneous
    (fun x hx ↦ (contDiffAt_fundamentalSolution n x hx).contDiffWithinAt) fun x c hc ↦ ?_
  rw [fundamentalSolution_of_three_le hn, fundamentalSolution_of_three_le hn, norm_smul,
    Real.norm_of_nonneg hc.le, mul_pow, smul_eq_mul,
    show (2 : ℤ) - n = -((n - 2 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast]
  generalize ((n : ℝ) - 2) * n * unitBallVolume n = A
  rw [one_div, one_div]
  simp only [mul_inv]
  ring

end PotentialTheory

namespace PoissonEquation

/-- **The potential of a source of mean zero** (Hou, Wang and Yang, (2.3) and the sentence after
it). In dimension `n ≥ 3`, if `f` is smooth with compact support and `∫ f = 0`, then the
potential `Φ ⋆ f`, which solves `-Δ(Φ ⋆ f) = f`, has symbol decay of order `1 - n`: its `j`th
derivative is `O(‖x‖ ^ (1 - n - j))`. In dimension three this is the printed `O(|ξ|^{-j-2})`.

The mean-zero hypothesis gives the bound of order zero, and harmonicity outside the support of
`f` gives the derivatives. -/
theorem hasSymbolDecay_fundamentalSolutionConvolution {n : ℕ} (hn : 3 ≤ n)
    (f : 𝓓^{2}((⊤ : Opens (ℝ^n)), ℝ)) (hf : ContDiff ℝ ∞ f) (hmean : ∫ x, f x = 0) :
    HasSymbolDecay (1 - n) (fundamentalSolutionConvolution n f) := by
  have : Fact (0 < n) := ⟨by omega⟩
  obtain ⟨R, hR⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall (0 : ℝ^n)
  have hsupp : ∀ y : ℝ^n, R < ‖y‖ → f y = 0 := fun y hy ↦
    image_eq_zero_of_notMem_tsupport fun h ↦ by
      have h' := hR h
      rw [Metric.mem_closedBall, dist_zero_right] at h'
      linarith
  have hsmooth := contDiff_fundamentalSolutionConvolution n f hf
  -- The bound of order zero, from the mean-zero gain.
  obtain ⟨C, hC⟩ :=
    (hasSymbolDecay_fundamentalSolution hn).exists_norm_convolution_le_of_integral_eq_zero
      (μ := volume) (ContinuousLinearMap.mul ℝ ℝ)
      (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport) hsupp hmean
  -- Outside the support the potential is harmonic.
  have hharm : IsHarmonicPDE n (fundamentalSolutionConvolution n f) {x | 2 * R + 2 < ‖x‖} := by
    refine ⟨(hsmooth.of_le (by simp)).contDiffOn, fun x hx ↦ ?_⟩
    have hx' : R < ‖x‖ := by
      have h : 2 * R + 2 < ‖x‖ := hx
      linarith [norm_nonneg x]
    have h := negative_laplacian_fundamentalSolutionConvolution (show 2 ≤ n by omega) f x
    rw [hsupp x hx'] at h
    linarith
  have hdecay := hharm.hasSymbolDecay (C := C) (d := 2 - n - 1) hsmooth.contDiffOn
    fun x hx ↦ by
      have h := hC x (le_of_lt hx)
      rwa [Real.norm_eq_abs] at h
  exact hdecay.mono (by omega)

end PoissonEquation
