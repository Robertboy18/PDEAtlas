/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Integrals of `g ∘ Φ` when `Φ` has a differentiable left inverse

A map `Φ` carries a function from one region to another, `g ↦ g ∘ Φ`. If `Φ` is continuous on a
measurable set `K` and has a left inverse `Ψ` on `K` whose derivative has norm at most `L` on
`Φ(K)`, then `∫_K g ∘ Φ ≤ Lⁿ ∫_{Φ(K)} g` for every `g ≥ 0`, in every finite-dimensional real
inner product space of dimension `n`. No Jacobian of `Φ` is computed. The extension of a
function from an annulus by reflection (`PDE.Analysis.annulusExtension`) bounds its reflected
pieces this way.

## Main results

* `abs_det_le_norm_pow`: `|det f| ≤ ‖f‖ⁿ` for every continuous linear map `f` of the space.
* `lintegral_comp_le_of_leftInverse`: `∫_K g ∘ Φ ≤ Lⁿ ∫_{Φ(K)} g`.

## How it works

The map `f` scales volume by `|det f|` (`Measure.addHaar_image_continuousLinearMap`) and sends
the unit ball into the ball of radius `‖f‖`, so `|det f| ≤ ‖f‖ⁿ`.
The left inverse makes `Φ` injective on `K`, so `Φ(K)` is measurable by the theorem of Lusin
and Souslin (`MeasurableSet.image_of_continuousOn_injOn`). The change of variables `y = Ψ(x)`
of Mathlib, `lintegral_image_eq_lintegral_abs_det_fderiv_mul`, writes `∫_K g(Φ y) dy` as
`∫_{Φ(K)} |det DΨ| g`, and the determinant bound finishes the proof.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace PDE.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The determinant of a continuous linear map on a space of dimension `n` is at most the `n`-th
power of its norm: the image of the unit ball lies in the ball of radius `‖f‖`. -/
theorem abs_det_le_norm_pow (f : E →L[ℝ] E) : |f.det| ≤ ‖f‖ ^ Module.finrank ℝ E := by
  have hsub : f '' closedBall 0 1 ⊆ closedBall 0 ‖f‖ := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_closedBall_zero_iff] at hx ⊢
    exact (f.le_opNorm x).trans (mul_le_of_le_one_right (norm_nonneg f) hx)
  have h2 := measure_mono (μ := (volume : Measure E)) hsub
  rw [Measure.addHaar_image_continuousLinearMap, Measure.addHaar_closedBall _ _ (norm_nonneg f),
    Measure.addHaar_closedBall _ _ zero_le_one, one_pow, ENNReal.ofReal_one, one_mul] at h2
  have hpos : (volume : Measure E) (ball 0 1) ≠ 0 := (measure_ball_pos _ _ one_pos).ne'
  have hfin : (volume : Measure E) (ball 0 1) ≠ ∞ := measure_ball_lt_top.ne
  rw [ENNReal.mul_le_mul_iff_left hpos hfin] at h2
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2

/-- **Integrals of `g ∘ Φ` when `Φ` has a differentiable left inverse.** If `Ψ (Φ y) = y` on the
measurable set `K`, `Φ` is continuous on `K`, and the derivative of `Ψ` has norm at most `L` on
`Φ(K)`, then `∫_K g(Φ y) dy ≤ Lⁿ ∫_{Φ(K)} g` for every `g ≥ 0`. -/
theorem lintegral_comp_le_of_leftInverse {K : Set E} (hK : MeasurableSet K) {Φ Ψ : E → E}
    {Ψ' : E → E →L[ℝ] E} (hΦ : ContinuousOn Φ K) (hinv : ∀ y ∈ K, Ψ (Φ y) = y)
    (hΨ : ∀ x ∈ Φ '' K, HasFDerivAt Ψ (Ψ' x) x) {L : ℝ} (hL : ∀ x ∈ Φ '' K, ‖Ψ' x‖ ≤ L)
    (g : E → ℝ≥0∞) :
    ∫⁻ y in K, g (Φ y) ≤ ENNReal.ofReal (L ^ Module.finrank ℝ E) * ∫⁻ x in Φ '' K, g x := by
  have hinj : InjOn Φ K := fun y hy z hz h ↦ by rw [← hinv y hy, ← hinv z hz, h]
  have hmeas : MeasurableSet (Φ '' K) := hK.image_of_continuousOn_injOn hΦ hinj
  have hinjΨ : InjOn Ψ (Φ '' K) := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ h
    rw [hinv y hy, hinv z hz] at h
    rw [h]
  have himage : Ψ '' (Φ '' K) = K := by
    ext y
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      rwa [hinv z hz]
    · exact fun hy ↦ ⟨Φ y, ⟨y, hy, rfl⟩, hinv y hy⟩
  have hcov := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hmeas
    (fun x hx ↦ (hΨ x hx).hasFDerivWithinAt) hinjΨ (fun y ↦ g (Φ y))
  rw [himage] at hcov
  rw [hcov, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' hmeas fun x hx ↦ ?_
  obtain ⟨y, hy, rfl⟩ := hx
  rw [hinv y hy]
  gcongr
  exact (abs_det_le_norm_pow _).trans
    (pow_le_pow_left₀ (norm_nonneg _) (hL _ ⟨y, hy, rfl⟩) _)

end PDE.Analysis
