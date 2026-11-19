/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.FirstOrder.RealSpectrum.Classical.Real
public import PDE.Analysis.Operator.ConstantCoefficient.FirstOrder.Real

/-!
# The classical Cauchy problem for real-spectrum systems

Evans, §7.3.3, Theorem 5: real fractional Sobolev data with `s > n/2 + m`
give a joint `C¹` solution of the full real constant-matrix system. Every
classical solution with the same initial data agrees on nonnegative times.

Existence uses the inverse Fourier construction. Uniqueness uses the
constant-coefficient Gaussian localization theorem and is independent of the
Sobolev and spectral hypotheses. The constructed solution satisfies the PDE
also on the initial time face; competitors need only be continuous there.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.3.3, Theorem 5.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace.Fractional
open scoped Sobolev Matrix.Norms.L2Operator

namespace PDE.Hyperbolic.FirstOrder

variable {n m : ℕ} {s : ℝ}

/-- The full real-spectrum Cauchy theorem. The single constructed solution
is jointly `C¹`, has the canonical original Sobolev initial data pointwise, and
is unique among all classical solutions on nonnegative times. The Sobolev
order is real; both zero dimensions are included. -/
theorem exists_unique_jointC1_realSpectrumSolution (B : Fin n → Matrix (Fin m) (Fin m) ℝ)
    (hB : ∀ ξ : ℝ^n, ∀ z ∈ spectrum ℂ (∑ j, ξ j • (B j).map Complex.ofReal), z.im = 0)
    (hs : (n : ℝ) < 2 * (s - m)) (f : Fin m → H^{s}(ℝ^n; ℝ)) :
    ∃ U : ℝ × ℝ^n → ℝ^m,
      ContDiff ℝ 1 U ∧
      (∀ p : ℝ × ℝ^n, fderiv ℝ U p (1, 0) + ∑ j,
        Matrix.toEuclideanCLM (𝕜 := ℝ) (B j)
          (fderiv ℝ U p (0, EuclideanSpace.single j 1)) = 0) ∧
      (∀ x, U (0, x) = realSpectrumInitialData hs f x) ∧
      ∀ V : ℝ × ℝ^n → ℝ^m,
        ContDiffOn ℝ 1 V (Ioi 0 ×ˢ univ) →
        ContinuousOn V (Ici 0 ×ˢ univ) →
        (∀ t > 0, ∀ x, fderiv ℝ V (t, x) (1, 0) + ∑ j,
          Matrix.toEuclideanCLM (𝕜 := ℝ) (B j)
            (fderiv ℝ V (t, x) (0, EuclideanSpace.single j 1)) = 0) →
        (∀ x, V (0, x) = realSpectrumInitialData hs f x) →
        EqOn V U (Ici 0 ×ˢ univ) := by
  obtain ⟨U, hU, heq, hi⟩ := exists_jointC1_realSpectrumSolution B hB hs f
  refine ⟨U, hU, heq, hi, fun V hV hVc hVe hVi p hp ↦ ?_⟩
  exact Analysis.eq_of_realMatrix_firstOrder B hp.1
    (hV.mono (fun q hq ↦ ⟨hq.1.1, hq.2⟩)) hU.contDiffOn
    (hVc.mono (fun q hq ↦ ⟨hq.1.1, hq.2⟩)) hU.continuous.continuousOn
    (fun x ↦ (hVi x).trans (hi x).symm) (fun t ht x ↦ hVe t ht.1 x) (fun t _ x ↦ heq (t, x)) p.2

/-- The same existence and unrestricted uniqueness theorem with any continuous
literal realization of the physical Sobolev initial data. Equality with the
canonical representative is derived from the almost-everywhere data identity. -/
theorem exists_unique_jointC1_realSpectrumSolution_of_ae_eq
    (B : Fin n → Matrix (Fin m) (Fin m) ℝ)
    (hB : ∀ ξ : ℝ^n,
      ∀ z ∈ spectrum ℂ (∑ j, ξ j • (B j).map Complex.ofReal), z.im = 0)
    (hs : (n : ℝ) < 2 * (s - m)) (f : Fin m → H^{s}(ℝ^n; ℝ))
    {v : ℝ^n → ℝ^m} (hv : Continuous v)
    (h : ∀ i, (fun x ↦ v x i) =ᵐ[volume]
      (HsSpaceReal.toL2FunCLM n
        (by
          have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
          linarith only [hs, hn, hm])
        (f i) : ℝ^n → ℝ)) :
    ∃ U : ℝ × ℝ^n → ℝ^m,
      ContDiff ℝ 1 U ∧
      (∀ p : ℝ × ℝ^n, fderiv ℝ U p (1, 0) + ∑ j,
        Matrix.toEuclideanCLM (𝕜 := ℝ) (B j)
          (fderiv ℝ U p (0, EuclideanSpace.single j 1)) = 0) ∧
      (∀ x, U (0, x) = v x) ∧
      ∀ V : ℝ × ℝ^n → ℝ^m,
        ContDiffOn ℝ 1 V (Ioi 0 ×ˢ univ) →
        ContinuousOn V (Ici 0 ×ˢ univ) →
        (∀ t > 0, ∀ x, fderiv ℝ V (t, x) (1, 0) + ∑ j,
          Matrix.toEuclideanCLM (𝕜 := ℝ) (B j)
            (fderiv ℝ V (t, x) (0, EuclideanSpace.single j 1)) = 0) →
        (∀ x, V (0, x) = v x) → EqOn V U (Ici 0 ×ˢ univ) := by
  have heq := realSpectrumInitialData_eq_of_ae_eq hs f hv h
  simpa only [heq] using exists_unique_jointC1_realSpectrumSolution B hB hs f

end PDE.Hyperbolic.FirstOrder
