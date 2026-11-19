/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Circle integrals under conjugate-linear maps

Let `L` be a continuous real-linear equivalence of a complex normed space that is
conjugate-linear, `L (c • x) = conj c • L x`. If `L (f z) = f (conj z)` on the circle `|z| = R`,
then `L` reverses the circle integral of `f` about the origin:

```text
L (∮ z in C(0, R), f z) = -∮ z in C(0, R), f z.
```

Conjugation reverses the orientation of the circle. The factor `(2 π i)⁻¹` also changes sign
under conjugation, so `L` fixes `(2 π i)⁻¹ ∮ z in C(0, R), f z`. Applied to the resolvent of an
operator that commutes with a conjugation, this shows that the Riesz projections of the operator
commute with the conjugation.
-/

@[expose] public noncomputable section

open Real MeasureTheory
open scoped ComplexConjugate

namespace PDE.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A conjugate-linear continuous equivalence that intertwines `f` with `f ∘ conj` on the circle
`|z| = R` reverses the circle integral of `f` about the origin. -/
theorem map_circleIntegral_conj {L : E ≃L[ℝ] E}
    (hL : ∀ (c : ℂ) (x : E), L (c • x) = conj c • L x)
    {f : ℂ → E} {R : ℝ} (hf : ∀ z ∈ Metric.sphere (0 : ℂ) |R|, L (f z) = f (conj z)) :
    L (∮ z in C(0, R), f z) = -∮ z in C(0, R), f z := by
  set g : ℝ → E := fun θ ↦ deriv (circleMap 0 R) θ • f (circleMap 0 R θ) with hg
  have hLg (θ : ℝ) : L (g θ) = -g (-θ) := by
    simp only [hg, hL, deriv_circleMap, map_mul, Complex.conj_I, conj_circleMap_zero,
      hf _ (circleMap_mem_sphere' 0 R θ), mul_neg, neg_smul]
  have hper : Function.Periodic g (2 * π) := fun θ ↦ by
    simp only [hg, deriv_circleMap, periodic_circleMap 0 R θ]
  have hI (φ : ℝ → E) :
      L (∫ θ in (0 : ℝ)..2 * π, φ θ) = ∫ θ in (0 : ℝ)..2 * π, L (φ θ) := by
    rw [intervalIntegral.integral_of_le two_pi_pos.le,
      intervalIntegral.integral_of_le two_pi_pos.le]
    exact (L.integral_comp_comm φ).symm
  change L (∫ θ in (0 : ℝ)..2 * π, g θ) = -∫ θ in (0 : ℝ)..2 * π, g θ
  rw [hI]
  simp_rw [hLg]
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_comp_neg (fun θ ↦ g θ)]
  congr 1
  simpa using hper.intervalIntegral_add_eq (-(2 * π)) 0

/-- A conjugate-linear continuous equivalence that intertwines `f` with `f ∘ conj` on the circle
`|z| = R` fixes `(2 π i)⁻¹ ∮ z in C(0, R), f z`. -/
theorem map_two_pi_I_inv_smul_circleIntegral_conj {L : E ≃L[ℝ] E}
    (hL : ∀ (c : ℂ) (x : E), L (c • x) = conj c • L x)
    {f : ℂ → E} {R : ℝ} (hf : ∀ z ∈ Metric.sphere (0 : ℂ) |R|, L (f z) = f (conj z)) :
    L ((2 * π * Complex.I : ℂ)⁻¹ • ∮ z in C(0, R), f z) =
      (2 * π * Complex.I : ℂ)⁻¹ • ∮ z in C(0, R), f z := by
  rw [hL, map_circleIntegral_conj hL hf, smul_neg, ← neg_smul]
  congr 1
  simp [Complex.conj_ofReal, map_ofNat]

end PDE.Analysis
