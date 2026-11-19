/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.Radon.SignedRadius.Integrability
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Signed radial weights lose the value at the origin

In positive even dimension, an even compactly supported smooth bump with value one at
the origin has zero signed-radius backprojection at the origin: with the radial weight
`r^(n-1)` and radii over all of `ℝ`, the integrand is odd in `r`. So the signed weight
does not recover `f 0`; the absolute weight `|r|^(n-1)` of
`eq_integral_filtered_radonTransform` does. Joint absolute integrability justifies the
iterated integrals in this calculation.

The right side in `exists_signed_radius_backprojection_ne` is formula (32) of Evans, §4.3.2,
Theorem 5(i), at `x = 0`, with his normalization `1 / (2 (2π)^n)`, so that formula fails in
every positive even dimension; the substitution `r ↦ -r`, `ω ↦ -ω` in step 1 of his proof
produces the factor `(-1)^(n-1)`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.3.2, Theorem 5(i), (32), and step 1 of its proof,
  p. 199. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped SchwartzMap ContDiff

namespace PDE.Analysis.Fourier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- In every positive even dimension, some compactly supported smooth real function with
value one at the origin is not recovered there by the signed radial weight `r^(n-1)`: its
signed-radius backprojection at the origin differs from `f 0`. The joint integrability in
the statement makes these iterated integrals ordinary integrals. -/
theorem exists_signed_radius_backprojection_ne
    (hodd : Odd (Module.finrank ℝ E - 1)) :
    ∃ f : E → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ f 0 = 1 ∧
      Integrable (fun p : Metric.sphere (0 : E) 1 × ℝ ↦
        p.2 ^ (Module.finrank ℝ E - 1) •
          angularFourierRadonTransform (fun x ↦ (f x : ℂ)) (p.1 : E) p.2)
        ((volume : Measure E).toSphere.prod volume) ∧
      (f 0 : ℂ) ≠ (1 / (2 * (2 * Real.pi) ^ Module.finrank ℝ E) : ℝ) •
        (∫ r : ℝ, ∫ θ : Metric.sphere (0 : E) 1,
          r ^ (Module.finrank ℝ E - 1) •
            angularFourierRadonTransform (fun x ↦ (f x : ℂ)) (θ : E) r
          ∂(volume : Measure E).toSphere) := by
  let b : ContDiffBump (0 : E) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  let f : 𝓢(E, ℝ) := b.hasCompactSupport.toSchwartzMap b.contDiff
  let g : 𝓢(E, ℂ) := f.postcompCLM Complex.ofRealCLM
  have hg (x : E) : g x = (b x : ℂ) := rfl
  have heven : Function.Even (g : E → ℂ) := by
    intro x
    simp only [hg, b.neg]
  have hb : b 0 = 1 := b.one_of_mem_closedBall (by simp [b])
  refine ⟨b, b.contDiff, b.hasCompactSupport, hb, ?_, ?_⟩
  · exact g.integrable_signed_radius_angularFourierRadonTransform_of_even heven
  · have hz := g.integral_signed_radius_angularFourierRadonTransform_eq_zero heven hodd
    have hz' : (∫ r : ℝ, ∫ θ : Metric.sphere (0 : E) 1,
        r ^ (Module.finrank ℝ E - 1) •
          angularFourierRadonTransform (fun x ↦ (b x : ℂ)) (θ : E) r
        ∂(volume : Measure E).toSphere) = 0 := hz
    rw [hz', smul_zero, hb]
    exact one_ne_zero

end PDE.Analysis.Fourier
