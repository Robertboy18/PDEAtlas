/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.NavierStokes.Stationary.ConvectionStrain
import PDE.Analysis.MeasureTheory.Lp.RealL2
import PDE.Analysis.MeasureTheory.Lp.WeightedL2

/-!
# The convection form with one bounded factor

The convection form `b(u, v, w) = ∫ (u·∇)v·w` on `H¹(ℝ³)³` is bounded by `‖u‖₄ ‖∇v‖₂ ‖w‖₄`. When
one of the three factors `u`, `∇v`, `w` is bounded, the form is at most the bound of that factor
times the `L²` norms of the other two, with constant one. No field has to be divergence free.

## Main results

All for fields of `H¹(ℝ³)³` unless stated otherwise.

* `abs_convectionDensity_le` (all vectors and matrices of any finite size):
  `|∑ₖ ∑ᵢ aᵢ Mₖᵢ bₖ| ≤ |a| |M| |b|`, with the Frobenius norm of `M`.
* `memLp_sqrt_sum_gradientRepresentative_sq` (all dimensions): the pointwise Frobenius norm of
  the weak gradient is in `L²`, with norm `‖∇v‖₂`.
* `abs_convectionTrilinear_le_of_norm_le_left`: `|b(u, v, w)| ≤ S ‖∇v‖₂ ‖w‖₂` if `|u| ≤ S`.
* `abs_convectionTrilinear_le_of_gradient_le`: `|b(u, v, w)| ≤ L ‖u‖₂ ‖w‖₂` if `|∇v| ≤ L`.
* `abs_convectionTrilinear_le_of_norm_le_right`: `|b(u, v, w)| ≤ S ‖u‖₂ ‖∇v‖₂` if `|w| ≤ S`.

## How it works

At each point the density `∑ₖ ∑ᵢ uᵢ ∂ᵢvₖ wₖ` is at most `|u| |∇v| |w|` by the Cauchy–Schwarz
inequality, with the Frobenius norm of the matrix `∇v`. Bound one factor by its supremum and use
the Cauchy–Schwarz inequality in `L²` for the other two
(`MeasureTheory.abs_integral_mul_le_lpNorm_two_mul_lpNorm_two`). The `L²` norm of the pointwise
Frobenius norm of the weak gradient is `‖∇v‖₂` (`integral_sum_gradientRepresentative_sq`). The
first and the third bound add up to
`NavierStokes.Nonuniqueness.abs_eigenPerturbation_le_of_norm_le`.

## References

* T. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116, Section 4.4: the bound (4.52),
  `|λ_con| ≤ ‖v̄‖_∞ ‖∇U‖₂` in (4.54), and the first step of (4.58).
  <https://arxiv.org/abs/2509.25116>
-/

@[expose] public noncomputable section

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Sobolev SobolevSpace.WholeSpaceHilbert

namespace NavierStokes.Stationary

set_option linter.missingDocs true

/-- **Pointwise Cauchy–Schwarz inequality for the convection density**:
`|∑ₖ ∑ᵢ aᵢ Mₖᵢ bₖ| ≤ |a| (∑ₖᵢ Mₖᵢ²)^{1/2} |b|`, for vectors `a ∈ ℝⁿ`, `b ∈ ℝᵐ` and an `m × n`
matrix `M`. -/
theorem abs_convectionDensity_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : EuclideanSpace ℝ ι) (b : EuclideanSpace ℝ κ) (M : κ → ι → ℝ) :
    |∑ k, ∑ i, a i * M k i * b k| ≤ ‖a‖ * √(∑ k, ∑ i, M k i ^ 2) * ‖b‖ := by
  have hc (k : κ) : (∑ i, a i * M k i) ^ 2 ≤ (∑ i, a i ^ 2) * ∑ i, M k i ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hL : ∑ k, ∑ i, a i * M k i * b k = ∑ k, (∑ i, a i * M k i) * b k := by
    simp only [Finset.sum_mul]
  have h₁ : (∑ k, (∑ i, a i * M k i) * b k) ^ 2 ≤
      (∑ k, (∑ i, a i * M k i) ^ 2) * ∑ k, b k ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have h₂ : ∑ k, (∑ i, a i * M k i) ^ 2 ≤ (∑ i, a i ^ 2) * ∑ k, ∑ i, M k i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ ↦ hc k
  have hb : 0 ≤ ∑ k, b k ^ 2 := by positivity
  refine abs_le_of_sq_le_sq ?_ (by positivity)
  rw [hL, mul_pow, mul_pow, Real.sq_sqrt (by positivity), EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq]
  calc _ ≤ _ := h₁
    _ ≤ (∑ i, a i ^ 2) * (∑ k, ∑ i, M k i ^ 2) * ∑ k, b k ^ 2 := by gcongr
    _ = _ := by ring

/-- The pointwise Frobenius norm `(∑ₖᵢ (∂ᵢvₖ)²)^{1/2}` of the weak gradient of a field of
`H¹(ℝⁿ)ⁿ` is square integrable, and its `L²` norm is `‖∇v‖₂`. -/
theorem memLp_sqrt_sum_gradientRepresentative_sq {n : ℕ}
    (v : PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n))) :
    MemLp (fun x ↦ √(∑ k, ∑ i, gradientRepresentative v x k i ^ 2)) 2 volume ∧
      (eLpNorm (fun x ↦ √(∑ k, ∑ i, gradientRepresentative v x k i ^ 2)) 2 volume).toReal =
        ‖gradientCLM v‖ := by
  have hint : Integrable (fun x ↦ ∑ k, ∑ i, gradientRepresentative v x k i ^ 2) :=
    integrable_finsetSum _ fun k _ ↦ integrable_finsetSum _ fun i _ ↦
      (memLp_gradientRepresentative v k i).integrable_sq
  have hsq (x : ℝ^n) : √(∑ k, ∑ i, gradientRepresentative v x k i ^ 2) ^ 2 =
      ∑ k, ∑ i, gradientRepresentative v x k i ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun k _ ↦ Finset.sum_nonneg fun i _ ↦ sq_nonneg _)
  have hmem : MemLp (fun x ↦ √(∑ k, ∑ i, gradientRepresentative v x k i ^ 2)) 2 volume := by
    refine (memLp_two_iff_integrable_sq
      (Real.continuous_sqrt.comp_aestronglyMeasurable hint.aestronglyMeasurable)).mpr ?_
    simpa only [hsq] using hint
  refine ⟨hmem, (pow_left_inj₀ ENNReal.toReal_nonneg (norm_nonneg _) two_ne_zero).mp ?_⟩
  exact (integral_sq_eq_eLpNorm_toReal_sq hmem).symm.trans
    ((integral_congr_ae (Filter.Eventually.of_forall hsq)).trans
      (integral_sum_gradientRepresentative_sq v))

/-- An integrable function bounded almost everywhere by `S f g`, with `f`, `g` square
integrable, has integral at most `S ‖f‖₂ ‖g‖₂` in absolute value. -/
private theorem abs_integral_le_mul_of_ae_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F f g : α → ℝ} {S : ℝ} (hS : 0 ≤ S) (hF : Integrable F μ) (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ) (hle : ∀ᵐ x ∂μ, |F x| ≤ S * (f x * g x)) :
    |∫ x, F x ∂μ| ≤ S * ((eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal) := by
  calc |∫ x, F x ∂μ| ≤ ∫ x, |F x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, S * (f x * g x) ∂μ :=
        integral_mono_ae hF.abs ((hf.integrable_mul hg).const_mul S) hle
    _ = S * ∫ x, f x * g x ∂μ := integral_const_mul S _
    _ ≤ S * |∫ x, f x * g x ∂μ| := mul_le_mul_of_nonneg_left (le_abs_self _) hS
    _ ≤ _ := mul_le_mul_of_nonneg_left
        (by simpa only [toReal_eLpNorm] using abs_integral_mul_le_lpNorm_two_mul_lpNorm_two hf hg)
        hS

local notation "E" => PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))

/-- The `L²` norm of the length of a field of `H¹(ℝ³)³` is its mass norm. -/
private theorem toReal_eLpNorm_norm_representative (w : E) :
    (eLpNorm (fun x ↦ ‖representative w x‖) 2 volume).toReal = ‖massCLM w‖ := by
  rw [eLpNorm_norm _ (memLp_representative w).aestronglyMeasurable,
    toReal_eLpNorm_two_representative]

/-- **The convection form with a bounded advecting field.** If the representative of `u` has
length at most `S` almost everywhere, then `|b(u, v, w)| ≤ S ‖∇v‖₂ ‖w‖₂`. -/
theorem abs_convectionTrilinear_le_of_norm_le_left (u v w : E) {S : ℝ}
    (hS : ∀ᵐ x ∂volume, ‖representative u x‖ ≤ S) :
    |convectionTrilinear u v w| ≤ S * ‖gradientCLM v‖ * ‖massCLM w‖ := by
  have hS0 : 0 ≤ S := by
    obtain ⟨x, hx⟩ := hS.exists
    exact (norm_nonneg _).trans hx
  obtain ⟨hG, hN⟩ := memLp_sqrt_sum_gradientRepresentative_sq v
  have h := abs_integral_le_mul_of_ae_le hS0 (integrable_convectionDensity u v w) hG
    (memLp_representative w).norm (by
      filter_upwards [hS] with x hx
      calc _ ≤ ‖representative u x‖ * √(∑ k, ∑ i, gradientRepresentative v x k i ^ 2) *
            ‖representative w x‖ := abs_convectionDensity_le _ _ _
        _ ≤ S * √(∑ k, ∑ i, gradientRepresentative v x k i ^ 2) * ‖representative w x‖ := by
            gcongr
        _ = _ := by ring)
  rw [hN, toReal_eLpNorm_norm_representative] at h
  rw [convectionTrilinear_eq_integral]
  exact h.trans (le_of_eq (by ring))

/-- **The convection form with a bounded gradient.** If the weak gradient of `v` has Frobenius
norm at most `L` almost everywhere, then `|b(u, v, w)| ≤ L ‖u‖₂ ‖w‖₂`. -/
theorem abs_convectionTrilinear_le_of_gradient_le (u v w : E) {L : ℝ}
    (hL : ∀ᵐ x ∂volume, √(∑ k, ∑ i, gradientRepresentative v x k i ^ 2) ≤ L) :
    |convectionTrilinear u v w| ≤ L * ‖massCLM u‖ * ‖massCLM w‖ := by
  have hL0 : 0 ≤ L := by
    obtain ⟨x, hx⟩ := hL.exists
    exact (Real.sqrt_nonneg _).trans hx
  have h := abs_integral_le_mul_of_ae_le hL0 (integrable_convectionDensity u v w)
    (memLp_representative u).norm (memLp_representative w).norm (by
      filter_upwards [hL] with x hx
      calc _ ≤ ‖representative u x‖ * √(∑ k, ∑ i, gradientRepresentative v x k i ^ 2) *
            ‖representative w x‖ := abs_convectionDensity_le _ _ _
        _ ≤ ‖representative u x‖ * L * ‖representative w x‖ := by gcongr
        _ = _ := by ring)
  rw [toReal_eLpNorm_norm_representative, toReal_eLpNorm_norm_representative] at h
  rw [convectionTrilinear_eq_integral]
  exact h.trans (le_of_eq (by ring))

/-- **The convection form with a bounded test field.** If the representative of `w` has length
at most `S` almost everywhere, then `|b(u, v, w)| ≤ S ‖u‖₂ ‖∇v‖₂`. -/
theorem abs_convectionTrilinear_le_of_norm_le_right (u v w : E) {S : ℝ}
    (hS : ∀ᵐ x ∂volume, ‖representative w x‖ ≤ S) :
    |convectionTrilinear u v w| ≤ S * ‖massCLM u‖ * ‖gradientCLM v‖ := by
  have hS0 : 0 ≤ S := by
    obtain ⟨x, hx⟩ := hS.exists
    exact (norm_nonneg _).trans hx
  obtain ⟨hG, hN⟩ := memLp_sqrt_sum_gradientRepresentative_sq v
  have h := abs_integral_le_mul_of_ae_le hS0 (integrable_convectionDensity u v w)
    (memLp_representative u).norm hG (by
      filter_upwards [hS] with x hx
      calc _ ≤ ‖representative u x‖ * √(∑ k, ∑ i, gradientRepresentative v x k i ^ 2) *
            ‖representative w x‖ := abs_convectionDensity_le _ _ _
        _ ≤ ‖representative u x‖ * √(∑ k, ∑ i, gradientRepresentative v x k i ^ 2) * S := by
            gcongr
        _ = _ := by ring)
  rw [hN, toReal_eLpNorm_norm_representative] at h
  rw [convectionTrilinear_eq_integral]
  exact h.trans (le_of_eq (by ring))

end NavierStokes.Stationary
