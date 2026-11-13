/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.Harmonic.DerivativeEstimates
public import PDE.Elliptic.Classical.Poisson.FundamentalSolution
import PDE.Elliptic.PotentialTheory.FundamentalSolution.LocalIntegrability
import PDE.FDeriv.Calculus

/-!
# Bounded Poisson solutions on Euclidean space

In dimension at least three, every bounded classical solution of `-Δu = f` with compactly
supported `C²` data `f` is the Newtonian potential `Φ ⋆ f` plus a constant
(`exists_eq_fundamentalSolutionConvolution_add_const`). This is Evans's §2.2.3, Theorem 9, for the
normalization `-ΔΦ = δ₀`.

## How it works

Evans notes that `Φ(x) → 0` as `|x| → ∞` when `n ≥ 3`, so that `Φ ⋆ f` is a bounded solution, and
applies Liouville's theorem to the difference of two solutions. We prove the boundedness of
`Φ ⋆ f` (`exists_bound_fundamentalSolutionConvolution`) by splitting the kernel at the unit
sphere. The part in the closed unit ball is integrable (`locallyIntegrable_fundamentalSolution`),
and the part outside is bounded (`norm_fundamentalSolution_le_of_one_le_norm`), so Mathlib's
Hölder convolution estimate `enorm_convolution_le` applies to the two pieces with exponents
`(1, ∞)` and `(∞, 1)`; the full kernel need not be globally integrable. Subtracting the potential
from a bounded classical solution leaves a bounded entire harmonic function, which is constant by
Liouville's theorem (`IsHarmonicPDE.eq_const_of_bounded`).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.3(d), Theorem 8 (Liouville's Theorem) and Theorem 9
  (Representation formula), p. 30, and the proof of Theorem 9, p. 31.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (laplacian)

open MeasureTheory PDE.Analysis PotentialTheory TopologicalSpace
open scoped Distributions ENNReal

namespace PotentialTheory

/-- Outside the unit ball the Newtonian kernel is bounded by its value at radius one. -/
theorem norm_fundamentalSolution_le_of_one_le_norm {n : ℕ} (hn : 3 ≤ n)
    {x : ℝ^n} (hx : 1 ≤ ‖x‖) :
    ‖fundamentalSolution n x‖ ≤ 1 / (((n : ℝ) - 2) * n * unitBallVolume n) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hnsub : 0 < (n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hc : 0 < ((n : ℝ) - 2) * n * unitBallVolume n :=
    mul_pos (mul_pos hnsub hnpos) (unitBallVolume_pos n)
  rw [fundamentalSolution_of_three_le hn, Real.norm_eq_abs,
    abs_of_nonneg (one_div_nonneg.mpr
      (mul_nonneg hc.le (pow_nonneg (norm_nonneg x) _)))]
  exact one_div_le_one_div_of_le hc (le_mul_of_one_le_right hc.le (one_le_pow₀ hx))

end PotentialTheory

namespace PoissonEquation

/-- Compactly supported `C²` Poisson data have a uniformly bounded Newtonian potential
in every dimension at least three. No bound on the potential is assumed. -/
theorem exists_bound_fundamentalSolutionConvolution {n : ℕ} (hn : 3 ≤ n)
    (f : 𝓓^{2}((⊤ : Opens (ℝ^n)), ℝ)) :
    ∃ M : ℝ, ∀ x, |fundamentalSolutionConvolution n f x| ≤ M := by
  classical
  have : Fact (0 < n) := ⟨by omega⟩
  let near : ℝ^n → ℝ :=
    (Metric.closedBall 0 1).indicator (fundamentalSolution n)
  let far : ℝ^n → ℝ :=
    (Metric.closedBall 0 1)ᶜ.indicator (fundamentalSolution n)
  let c : ℝ := 1 / (((n : ℝ) - 2) * n * unitBallVolume n)
  have hc : 0 ≤ c := one_div_nonneg.mpr (mul_nonneg (mul_nonneg
    (sub_nonneg.mpr (by exact_mod_cast (show 2 ≤ n by omega))) (by positivity))
      (unitBallVolume_pos n).le)
  have hΦ := locallyIntegrable_fundamentalSolution n
  have hnear : MemLp near 1 volume :=
    memLp_one_iff_integrable.mpr
      ((hΦ.integrableOn_isCompact (isCompact_closedBall 0 1)).integrable_indicator
        measurableSet_closedBall)
  have hfar : MemLp far ∞ volume := by
    refine memLp_top_of_bound (hΦ.aestronglyMeasurable.indicator
      measurableSet_closedBall.compl) c (.of_forall fun x ↦ ?_)
    by_cases hx : x ∈ Metric.closedBall (0 : ℝ^n) 1
    · simpa [far, hx] using hc
    · have hxnorm : 1 < ‖x‖ := by
        simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx
      simpa [far, hx, c] using norm_fundamentalSolution_le_of_one_le_norm hn hxnorm.le
  have hf₁ : MemLp (f : ℝ^n → ℝ) 1 volume :=
    memLp_one_iff_integrable.mpr (f.continuous.integrable_of_hasCompactSupport
      f.hasCompactSupport)
  have hfTop : MemLp (f : ℝ^n → ℝ) ∞ volume :=
    f.continuous.memLp_top_of_hasCompactSupport f.hasCompactSupport volume
  let L := ContinuousLinearMap.mul ℝ ℝ
  have hsplit : fundamentalSolution n = near + far := by
    funext x
    by_cases hx : x ∈ Metric.closedBall (0 : ℝ^n) 1 <;> simp [near, far, hx]
  let B : ℝ≥0∞ :=
    ‖L‖ₑ * eLpNorm near 1 volume * eLpNorm (f : ℝ^n → ℝ) ∞ volume +
      ‖L‖ₑ * eLpNorm far ∞ volume * eLpNorm (f : ℝ^n → ℝ) 1 volume
  have hB : B ≠ ∞ := by
    have := hnear.eLpNorm_ne_top
    have := hfar.eLpNorm_ne_top
    have := hf₁.eLpNorm_ne_top
    have := hfTop.eLpNorm_ne_top
    dsimp [B]
    finiteness
  refine ⟨B.toReal, fun x ↦ ?_⟩
  have hbound : ‖fundamentalSolutionConvolution n f x‖ₑ ≤ B := by
    change ‖convolution (fundamentalSolution n) (f : ℝ^n → ℝ) L volume x‖ₑ ≤ B
    rw [hsplit, ((ConvolutionExists.of_memLp_memLp L hnear hfTop) x).add_distrib
      ((ConvolutionExists.of_memLp_memLp L hfar hf₁) x)]
    exact (enorm_add_le _ _).trans (add_le_add
      (enorm_convolution_le L hnear.aestronglyMeasurable hfTop.aestronglyMeasurable x)
      (enorm_convolution_le L hfar.aestronglyMeasurable hf₁.aestronglyMeasurable x))
  simpa only [toReal_enorm, Real.norm_eq_abs] using ENNReal.toReal_mono hB hbound

/-- Every bounded classical solution of `-Δu = f` is the Newtonian potential plus
a constant, for compactly supported `C²` data in dimension at least three. -/
theorem exists_eq_fundamentalSolutionConvolution_add_const {n : ℕ} (hn : 3 ≤ n)
    (f : 𝓓^{2}((⊤ : Opens (ℝ^n)), ℝ)) {u : ℝ^n → ℝ}
    (hu : ContDiff ℝ 2 u) (hpoisson : ∀ x, -laplacian u x = f x)
    (hbounded : ∃ M : ℝ, ∀ x, |u x| ≤ M) :
    ∃ C : ℝ, ∀ x, u x = fundamentalSolutionConvolution n f x + C := by
  have : Fact (0 < n) := ⟨by omega⟩
  obtain ⟨M, hM⟩ := hbounded
  obtain ⟨N, hN⟩ := exists_bound_fundamentalSolutionConvolution hn f
  have hv := contDiff_two_fundamentalSolutionConvolution n f
  have hharmonic : LaplacianEquation.IsHarmonicPDE n
      (fun x ↦ u x - fundamentalSolutionConvolution n f x) Set.univ := by
    refine ⟨(hu.sub hv).contDiffOn, fun x _ ↦ ?_⟩
    rw [PDE.laplacian_sub u (fundamentalSolutionConvolution n f) x hu.contDiffAt hv.contDiffAt]
    linarith [hpoisson x, negative_laplacian_fundamentalSolutionConvolution
      (show 2 ≤ n by omega) f x]
  have hbound : ∀ x, |u x - fundamentalSolutionConvolution n f x| ≤ M + N :=
    fun x ↦ (abs_sub (u x) (fundamentalSolutionConvolution n f x)).trans
      (add_le_add (hM x) (hN x))
  refine ⟨u 0 - fundamentalSolutionConvolution n f 0, fun x ↦ ?_⟩
  linarith [hharmonic.eq_const_of_bounded hbound x]

end PoissonEquation
