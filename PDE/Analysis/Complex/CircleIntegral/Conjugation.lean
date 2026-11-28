/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Circle integrals under conjugate-linear maps

Let `L` be a continuous real-linear equivalence of a complex normed space that is
conjugate-linear, `L (a • x) = conj a • L x`. If `L (f z) = g (conj z)` on the circle
`|z - c| = |R|`, then `L` carries the circle integral of `f` about `c` to minus the circle
integral of `g` about `conj c`:

```text
L (∮ z in C(c, R), f z) = -∮ z in C(conj c, R), g z.
```

Conjugation reverses the orientation of the circle. The factor `(2 π i)⁻¹` also changes sign
under conjugation, so for `g = f` and the centre `0` the map `L` fixes
`(2 π i)⁻¹ ∮ z in C(0, R), f z`. Applied to the resolvent of an operator that commutes with a
conjugation, this shows that the conjugation carries the Riesz projection on `C(c, R)` to the
one on `C(conj c, R)`. In particular, the Riesz projections on circles about `0` commute with
the conjugation.
-/

@[expose] public noncomputable section

open Real MeasureTheory
open scoped ComplexConjugate

namespace PDE.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Conjugation reverses circle integrals.** A conjugate-linear continuous equivalence `L`
with `L (f z) = g (conj z)` on the circle `C(c, R)` sends the circle integral of `f` on
`C(c, R)` to minus the circle integral of `g` on `C(conj c, R)`. -/
theorem map_circleIntegral_conj_center {L : E ≃L[ℝ] E}
    (hL : ∀ (a : ℂ) (x : E), L (a • x) = conj a • L x) {f g : ℂ → E} {c : ℂ} {R : ℝ}
    (hfg : ∀ z ∈ Metric.sphere c |R|, L (f z) = g (conj z)) :
    L (∮ z in C(c, R), f z) = -∮ z in C(conj c, R), g z := by
  set F : ℝ → E := fun θ ↦ deriv (circleMap c R) θ • f (circleMap c R θ) with hF
  set G : ℝ → E := fun θ ↦ deriv (circleMap (conj c) R) θ • g (circleMap (conj c) R θ) with hG
  have hLF (θ : ℝ) : L (F θ) = -G (-θ) := by
    simp only [hF, hG, hL, deriv_circleMap, map_mul, Complex.conj_I,
      hfg _ (circleMap_mem_sphere' c R θ), conj_circleMap, map_zero, mul_neg, neg_smul]
  have hper : Function.Periodic G (2 * π) := fun θ ↦ by
    simp only [hG, deriv_circleMap, periodic_circleMap (conj c) R θ, periodic_circleMap 0 R θ]
  have hI (φ : ℝ → E) :
      L (∫ θ in (0 : ℝ)..2 * π, φ θ) = ∫ θ in (0 : ℝ)..2 * π, L (φ θ) := by
    rw [intervalIntegral.integral_of_le two_pi_pos.le,
      intervalIntegral.integral_of_le two_pi_pos.le]
    exact (L.integral_comp_comm φ).symm
  change L (∫ θ in (0 : ℝ)..2 * π, F θ) = -∫ θ in (0 : ℝ)..2 * π, G θ
  rw [hI]
  simp_rw [hLF]
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_comp_neg (fun θ ↦ G θ)]
  congr 1
  simpa using hper.intervalIntegral_add_eq (-(2 * π)) 0

/-- A conjugate-linear continuous equivalence that intertwines `f` with `f ∘ conj` on the circle
`|z| = |R|` reverses the circle integral of `f` about the origin. This is
`map_circleIntegral_conj_center` for the centre `0` and `g = f`. -/
theorem map_circleIntegral_conj {L : E ≃L[ℝ] E}
    (hL : ∀ (c : ℂ) (x : E), L (c • x) = conj c • L x)
    {f : ℂ → E} {R : ℝ} (hf : ∀ z ∈ Metric.sphere (0 : ℂ) |R|, L (f z) = f (conj z)) :
    L (∮ z in C(0, R), f z) = -∮ z in C(0, R), f z := by
  simpa using map_circleIntegral_conj_center (c := 0) hL hf

/-- A conjugate-linear continuous equivalence that intertwines `f` with `f ∘ conj` on the circle
`|z| = |R|` fixes `(2 π i)⁻¹ ∮ z in C(0, R), f z`. -/
theorem map_two_pi_I_inv_smul_circleIntegral_conj {L : E ≃L[ℝ] E}
    (hL : ∀ (c : ℂ) (x : E), L (c • x) = conj c • L x)
    {f : ℂ → E} {R : ℝ} (hf : ∀ z ∈ Metric.sphere (0 : ℂ) |R|, L (f z) = f (conj z)) :
    L ((2 * π * Complex.I : ℂ)⁻¹ • ∮ z in C(0, R), f z) =
      (2 * π * Complex.I : ℂ)⁻¹ • ∮ z in C(0, R), f z := by
  rw [hL, map_circleIntegral_conj hL hf, smul_neg, ← neg_smul]
  congr 1
  simp [Complex.conj_ofReal, map_ofNat]

end PDE.Analysis
