/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.Poisson.PlanarFundamentalSolution
import PDE.Elliptic.PotentialTheory.FundamentalSolution.NewtonianDistribution
import PDE.FDeriv.Calculus

/-!
# Classical Poisson inversion in dimension at least two

For every compactly supported `C²` datum `f` on `ℝ^n`, `n ≥ 2`, the convolution `Φ ⋆ f` with the
fundamental solution is a classical `C²` solution of `-Δu = f`
(`fundamentalSolutionConvolution_isSolution`). This is Evans's §2.2.1, Theorem 1, in every
dimension at least two and under the same hypotheses on `f`: two continuous derivatives and
compact support.

## How it works

Evans moves both derivatives onto `f`, cuts a small ball `B(0, ε)` out of the integral, and
integrates by parts twice; the term on the small sphere tends to `-f(x)`. We use instead the pole
identity `Newtonian.integral_fundamentalSolution_mul_laplacian`, the distributional form of
`-ΔΦ = δ₀`, for the translated test function `y ↦ f(x + y)`. After
`laplacian_fundamentalSolutionConvolution` moves the Laplacian onto `f`, reflection of the
integration variable and evenness of the kernel (`fundamentalSolution_neg`) identify `Φ ⋆ Δf` at
`x` with the integral in the pole identity, which is `-f(x)`. The planar case is
`negative_laplacian_fundamentalSolutionConvolution_two`, proved the same way in
`PlanarFundamentalSolution` with the logarithmic pole identity.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.1(b), Theorem 1 (Solving Poisson's equation) and its
  proof, pp. 23-25, and the interpretation `-ΔΦ = δ₀`, p. 25.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (laplacian)

noncomputable section

namespace PoissonEquation

open MeasureTheory PotentialTheory TopologicalSpace
open scoped Distributions

/-- Convolution of the fundamental solution with a compactly supported `C²` datum
satisfies `-Δu = f` pointwise in every dimension at least two. -/
theorem negative_laplacian_fundamentalSolutionConvolution
    {n : ℕ} (hn : 2 ≤ n)
    (f : 𝓓^{2}((⊤ : Opens (ℝ^n)), ℝ)) (x : ℝ^n) :
    -laplacian (fundamentalSolutionConvolution n f) x = f x := by
  rcases eq_or_lt_of_le hn with rfl | hn
  · exact negative_laplacian_fundamentalSolutionConvolution_two f x
  have : Fact (0 < n) := ⟨by omega⟩
  let φ : 𝓓^{2}((⊤ : Opens (ℝ^n)), ℝ) :=
    { toFun := fun y ↦ f (x + y)
      contDiff' := f.contDiff.comp (contDiff_const.add contDiff_id)
      hasCompactSupport' := by
        simpa [Function.comp_def] using
          f.hasCompactSupport.comp_homeomorph (Homeomorph.addLeft x)
      tsupport_subset' := Set.subset_univ _ }
  have hφLaplacian (y : ℝ^n) :
      laplacian (φ : ℝ^n → ℝ) y = laplacian f (x + y) := by
    change laplacian (fun z : ℝ^n ↦ f (x + z)) y = laplacian f (x + y)
    exact PDE.laplacian_comp_add_left f x y f.contDiff.contDiffAt
  have hpole := Newtonian.integral_fundamentalSolution_mul_laplacian (by omega) φ
  have hconvolution :
      convolution (fundamentalSolution n) (fun y ↦ laplacian f y)
          (ContinuousLinearMap.mul ℝ ℝ) volume x = -f x := by
    rw [MeasureTheory.convolution_mul]
    calc
      (∫ y : ℝ^n, fundamentalSolution n y * laplacian f (x - y)) =
          ∫ y : ℝ^n,
            fundamentalSolution n (-y) * laplacian f (x - (-y)) := by
        symm
        exact MeasureTheory.integral_neg_eq_self
          (fun y : ℝ^n ↦
            fundamentalSolution n y * laplacian f (x - y)) volume
      _ = ∫ y : ℝ^n,
          fundamentalSolution n y * laplacian (φ : ℝ^n → ℝ) y := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y ↦ by
          change fundamentalSolution n (-y) * laplacian f (x - (-y)) =
            fundamentalSolution n y * laplacian (φ : ℝ^n → ℝ) y
          rw [fundamentalSolution_neg, sub_neg_eq_add, hφLaplacian]
      _ = -φ 0 := hpole
      _ = -f x := by
        change -f (x + 0) = -f x
        simp
  rw [laplacian_fundamentalSolutionConvolution, hconvolution, neg_neg]

/-- The fundamental-solution convolution is a classical `C²` solution of the
Poisson equation on all of `ℝ^n` for every `n ≥ 2` and compactly supported `C²` datum. -/
theorem fundamentalSolutionConvolution_isSolution
    {n : ℕ} (hn : 2 ≤ n)
    (f : 𝓓^{2}((⊤ : Opens (ℝ^n)), ℝ)) :
    ContDiff ℝ 2 (fundamentalSolutionConvolution n f) ∧
      ∀ x ∈ (poissonEquation n f).domain,
        (poissonEquation n f).residual
          (fundamentalSolutionConvolution n f) x = 0 := by
  have : Fact (0 < n) := ⟨by omega⟩
  refine ⟨contDiff_two_fundamentalSolutionConvolution n f, ?_⟩
  exact (poissonEquation_residual_zero_iff n f
      (fundamentalSolutionConvolution n f)).2
    (negative_laplacian_fundamentalSolutionConvolution hn f)

end PoissonEquation
