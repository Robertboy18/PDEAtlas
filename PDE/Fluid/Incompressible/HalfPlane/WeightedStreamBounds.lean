/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.HalfPlane.OriginTaylor
import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.GradientBounds
import PDE.Elliptic.PotentialTheory.FundamentalSolution.PlanarSingularIntegral
import PDE.FDeriv.PartialDeriv.Energy

/-!
# Weighted bounds for the half-plane stream function (Part I, Lemma 6.5)

Let `f` be continuous with compact support, odd in `x₀` on the open upper half-plane, and

`|f(y)| (|y|^(-α) + |y|^β) ≤ M`  for `y₁ > 0`,

so that `|f(y)| ≤ M min(|y|^α, |y|^(-β))` (`abs_le_mul_min_rpow`). Let `φ = G[f]` be its
half-plane Green potential, the solution of `-Δφ = f` with `φ = 0` on the boundary given by the
odd extension `W` of `f` and the logarithmic kernel, Chen and Hou, Part I, (6.20)-(6.21); `φ` is
`C¹` with `∂ⱼφ(x) = ∫ gⱼ(x - y) W(y) dy`, and `W` is odd in both coordinates. We prove the
estimates of Chen and Hou, Part I, Lemma 6.5:

* (6.23a) for `α > 0`, `0 < β < 1`: `|∇φ(x)| ≤ C M min(|x|, |x|^(1-β))`
  (`exists_norm_fderiv_greenPotential_le`);
* (6.23b) for `0 < α < 2`: `|∇(φ - c_f x₀ x₁)(x)| ≤ C M |x|^(1+α)` and
  `|φ - c_f x₀ x₁| ≤ C M |x|^(2+α)` (`exists_greenPotential_sub_mixed_le`);
* (6.23c) for `α > 2`, `β > 0`: the same with `|x|³` and `|x|⁴`
  (`exists_greenPotential_sub_mixed_le_of_two_lt`);

with `C` depending only on the exponents and `c_f = ∂₀∂₁φ(0) = (4/π) ∫_{ℝ²₊₊} y₀ y₁ |y|⁻⁴ f(y) dy`
(`mixedCoefficient`, `mixedDeriv_greenPotential_zero`). All bounds hold on the whole plane.

Remarks on the statement.
* (6.23a) is stated for `0 < β < 1`, as in Part I; the near region uses `β < 2`. A bound of this
  form uniform in the support needs a bounded range of `β`: for `f = a(|y|) sin 2θ` with `a`
  supported in an annulus the exterior gradient is `J/(2r³)`, `J = ∫ a(s) s³ ds`, which is not
  `O(r^(1-β))` for `β > 4`.
* (6.23b) uses only `|f(y)| ≤ M |y|^α`; no decay exponent is needed. In the near region
  `|y| < 2|x|` the corrected gradient integral is at most `(3 + 1/α) M (2|x|)^α |x|`
  (`abs_setIntegral_compl_farRegion_le`).
* Part I states (6.23b) for `ω ∈ C^{1,γ}` and (6.23c) for `α ∈ (2, 3]` and `ω ∈ C^{2,γ}`. Our
  versions assume only continuity and compact support, and (6.23c) holds for every `α > 2`, with
  the explicit coefficient `c_f`.

## Main definitions

* `mixedCoefficient`: `c_f = (4/π) ∫_{ℝ²₊₊} y₀ y₁ |y|⁻⁴ f(y) dy`, the coefficient of `x₀ x₁` in the
  expansion of the Green potential at the origin.
* `farRegion`: the far region `{y | 2|x| ≤ |y|}`.

## Main results

* `abs_le_mul_min_rpow`: the weighted bound gives `|f(y)| ≤ M min(|y|^α, |y|^(-β))` on the open
  upper half-plane.
* `abs_partialDeriv_le_mul_norm`: `|∂ⱼφ(x)| ≤ (20/α + 20/β + 3) M |x|` for
  `|f(y)| ≤ M min(|y|^α, |y|^(-β), 1)`.
* `abs_partialDeriv_le_mul_rpow`: `|∂ⱼφ(x)| ≤ (20/β + 9) M |x|^(1-β)` for `x ≠ 0` and
  `|f(y)| ≤ M |y|^(-β)`, `0 < β < 1`.
* `exists_norm_fderiv_greenPotential_le`: (6.23a), `|∇φ(x)| ≤ C M min(|x|, |x|^(1-β))`.
* `exists_greenPotential_sub_mixed_le`: (6.23b) for `0 < α < 2`, with no condition on `β`.
* `exists_greenPotential_sub_mixed_le_of_two_lt`: (6.23c) for `α > 2` and `β > 0`.
* `abs_mixedCoefficient_le`: `|c_f| ≤ 4 (1/α + 1/β) M` under the weighted bound.
* `mixedDeriv_greenPotential_zero`: `c_f = ∂₀∂₁φ(0) = ∂₁∂₀φ(0)` for `α > 0`, `β > 0`.

## How it works

We follow the partition of the plane in the proof of (6.23a) in Part I and in its Appendix C.3.2,
into the far region `|y| ≥ 2|x|` (`farRegion`), where the four images of `y` are grouped on the
quadrant (`setIntegral_farRegion_eq`) and the symmetrized gradient kernel is `O(|x|/|y|²)`, or
`O(|x|³/|y|⁴)` after subtracting `(4/π) x_k K₁(y)`
(`IncompressibleFlow.abs_symmetrizedKernel_gradientKernel_one_sub_le`), and the near region
`|y| < 2|x|`, split at the disc `|y - x| < |x|/2` when the decay of `f` is used. The radial
integrals are those of `MeasureTheory.lintegral_ball_mul_rpow_sub_two` and
`MeasureTheory.lintegral_compl_ball_mul_rpow_sub_three`. For (6.23a) this gives the two bounds
`abs_partialDeriv_le_mul_norm` and `abs_partialDeriv_le_mul_rpow` of each partial derivative. For
(6.23b) and (6.23c) the gradient of `φ - c_f x₀ x₁` is the integral of `W` against the corrected
kernel (`partialDeriv_sub_mixedMonomial_eq`), bounded by `abs_integral_sub_le_of_lt_two` and, for
`|x| ≤ 1`, by `abs_integral_sub_le_of_two_lt`; for (6.23c) with `|x| > 1` the bound
`abs_partialDeriv_le_mul_norm` and `abs_mixedCoefficient_le` suffice. Since `φ` vanishes at the
origin, the mean value inequality (`abs_le_of_norm_fderiv_le`) turns each gradient bound into the
bound on the values.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 6.2, (6.20)-(6.21),
  pp. 97-98, Lemma 6.5 and the proof of (6.23a), pp. 98-99, (5.67), p. 78, and Appendix C.3.2,
  pp. 145-146.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

namespace IncompressibleFlow

open MeasureTheory Filter Topology Set Metric GreenFunction PotentialTheory.Planar SobolevSpace

set_option linter.missingDocs true

local notation "𝐑" => PDE.Common.coordinateReflection


/-- A function dominated on `S` by `g`, with `∫⁻_T g ≤ B` on a larger set `T`, has
`|∫_S F| ≤ B`. -/
theorem abs_setIntegral_le_of_lintegral_le {S T : Set (ℝ^2)} (hS : MeasurableSet S)
    (hST : S ⊆ T) {F g : ℝ^2 → ℝ} {B : ℝ} (hB : 0 ≤ B) (hle : ∀ y ∈ S, |F y| ≤ g y)
    (hg : ∫⁻ y in T, ENNReal.ofReal (g y) ≤ ENNReal.ofReal B) :
    |∫ y in S, F y| ≤ B := by
  have hS' : ∫⁻ y in S, ENNReal.ofReal (g y) ≤ ENNReal.ofReal B :=
    (lintegral_mono_set hST).trans hg
  have hne : ∫⁻ y in S, ENNReal.ofReal (g y) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hS'
  have h := norm_setIntegral_le_of_norm_le (μ := volume) hS
    (fun y hy ↦ by rw [Real.norm_eq_abs]; exact hle y hy) hne
  rw [Real.norm_eq_abs] at h
  exact h.trans (ENNReal.toReal_le_of_le_ofReal hB hS')

/-- A measurable function dominated on `S` by `g` with finite `∫⁻_T g`, `S ⊆ T`, is integrable
on `S`. -/
theorem integrableOn_of_abs_le_of_lintegral_le {S T : Set (ℝ^2)} (hS : MeasurableSet S)
    (hST : S ⊆ T) {F g : ℝ^2 → ℝ} {B : ℝ} (hF : AEStronglyMeasurable F (volume.restrict S))
    (hle : ∀ y ∈ S, |F y| ≤ g y)
    (hg : ∫⁻ y in T, ENNReal.ofReal (g y) ≤ ENNReal.ofReal B) :
    IntegrableOn F S := by
  have hS' : ∫⁻ y in S, ENNReal.ofReal (g y) ≤ ENNReal.ofReal B :=
    (lintegral_mono_set hST).trans hg
  exact integrableOn_of_norm_le_of_lintegral_ne_top hS hF
    (fun y hy ↦ by rw [Real.norm_eq_abs]; exact hle y hy)
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hS')

/-- `∫⁻_{|y|<ρ} c |y|^(γ-2) = c · 2π ρ^γ/γ` for `γ > 0`. -/
theorem lintegral_ball_zero_rpow {c ρ γ : ℝ} (hc : 0 ≤ c) (hρ : 0 ≤ ρ) (hγ : 0 < γ) :
    ∫⁻ y in ball (0 : ℝ^2) ρ, ENNReal.ofReal (c * ‖y‖ ^ (γ - 2)) =
      ENNReal.ofReal (c * (2 * Real.pi * ρ ^ γ / γ)) := by
  simpa using MeasureTheory.lintegral_ball_mul_rpow_sub_two (0 : ℝ^2) hc hρ hγ

/-- `∫⁻_{|y|≥ρ} c |y|^(γ-3) = c · 2π ρ^(γ-1)/(1-γ)` for `γ < 1`. -/
theorem lintegral_compl_ball_zero_rpow {c ρ γ : ℝ} (hc : 0 ≤ c) (hρ : 0 < ρ) (hγ : γ < 1) :
    ∫⁻ y in (ball (0 : ℝ^2) ρ)ᶜ, ENNReal.ofReal (c * ‖y‖ ^ (γ - 3)) =
      ENNReal.ofReal (c * (2 * Real.pi * ρ ^ (γ - 1) / (1 - γ))) := by
  simpa using MeasureTheory.lintegral_compl_ball_mul_rpow_sub_three (0 : ℝ^2) hc hρ hγ

/-- `∫⁻_{|y-x|<ρ} c |x - y|⁻¹ = c · 2πρ`. -/
theorem lintegral_ball_sub_inv {c ρ : ℝ} (hc : 0 ≤ c) (hρ : 0 ≤ ρ) (x : ℝ^2) :
    ∫⁻ y in ball x ρ, ENNReal.ofReal (c * ‖x - y‖ ^ ((1 : ℝ) - 2)) =
      ENNReal.ofReal (c * (2 * Real.pi * ρ)) := by
  simpa using MeasureTheory.lintegral_ball_mul_rpow_sub_two x hc hρ one_pos


/-- A function on `S` bounded by `c |y|^(γ-2)` inside the unit disc and by `c |y|^(δ-3)` outside
it, `γ > 0` and `δ < 1`, is integrable on `S`, with
`|∫_S F| ≤ c · 2π/γ + c · 2π/(1 - δ)`. -/
private theorem integrableOn_and_abs_setIntegral_le_split {S : Set (ℝ^2)}
    (hS : MeasurableSet S) {F : ℝ^2 → ℝ} (hF : AEStronglyMeasurable F) {c γ δ : ℝ} (hc : 0 ≤ c)
    (hγ : 0 < γ) (hδ : δ < 1) (h₁ : ∀ y ∈ S ∩ ball (0 : ℝ^2) 1, |F y| ≤ c * ‖y‖ ^ (γ - 2))
    (h₂ : ∀ y ∈ S \ ball (0 : ℝ^2) 1, |F y| ≤ c * ‖y‖ ^ (δ - 3)) :
    IntegrableOn F S ∧
      |∫ y in S, F y| ≤ c * (2 * Real.pi / γ) + c * (2 * Real.pi / (1 - δ)) := by
  have hB : MeasurableSet (ball (0 : ℝ^2) 1) := measurableSet_ball
  have hT₁ := (lintegral_ball_zero_rpow hc zero_le_one hγ).le
  have hT₂ := (lintegral_compl_ball_zero_rpow hc one_pos hδ).le
  simp only [Real.one_rpow, mul_one] at hT₁ hT₂
  have hI : IntegrableOn F S := by
    simpa only [inter_union_sdiff] using
      (integrableOn_of_abs_le_of_lintegral_le (hS.inter hB) inter_subset_right hF.restrict h₁
        hT₁).union (integrableOn_of_abs_le_of_lintegral_le (hS.diff hB) (fun y hy ↦ hy.2)
          hF.restrict h₂ hT₂)
  have hδ' : 0 < 1 - δ := by linarith
  refine ⟨hI, ?_⟩
  rw [← integral_inter_add_sdiff hB hI]
  exact (abs_add_le _ _).trans (add_le_add
    (abs_setIntegral_le_of_lintegral_le (hS.inter hB) inter_subset_right (by positivity) h₁ hT₁)
    (abs_setIntegral_le_of_lintegral_le (hS.diff hB) (fun y hy ↦ hy.2) (by positivity) h₂ hT₂))

/-! ### Pointwise consequences of the weighted bound -/

section Pointwise

variable {f : ℝ^2 → ℝ} {α β M : ℝ}

/-- The weighted bound of Lemma 6.5 forces `M ≥ 0`. -/
theorem nonneg_of_weighted_le (hM : ∀ y : ℝ^2, 0 < y 1 → |f y| * (‖y‖ ^ (-α) + ‖y‖ ^ β) ≤ M) :
    0 ≤ M := by
  have hy : ‖(EuclideanSpace.single (1 : Fin 2) (1 : ℝ) : ℝ^2)‖ = 1 := by
    rw [PiLp.norm_single, norm_one]
  have h := hM (EuclideanSpace.single 1 1) (by simp)
  rw [hy, Real.one_rpow, Real.one_rpow] at h
  linarith [abs_nonneg (f (EuclideanSpace.single 1 1))]

/-- The weighted bound gives `|f(y)| ≤ M |y|^α` on the open upper half-plane. -/
theorem abs_le_mul_rpow_of_weighted_le
    (hM : ∀ y : ℝ^2, 0 < y 1 → |f y| * (‖y‖ ^ (-α) + ‖y‖ ^ β) ≤ M) {y : ℝ^2} (hy : 0 < y 1) :
    |f y| ≤ M * ‖y‖ ^ α := by
  have hpos : 0 < ‖y‖ := by
    have : |y 1| ≤ ‖y‖ := by simpa using PiLp.norm_apply_le y 1
    rw [abs_of_pos hy] at this; linarith
  have ha : 0 < ‖y‖ ^ α := Real.rpow_pos_of_pos hpos α
  have hb : 0 ≤ ‖y‖ ^ β := (Real.rpow_pos_of_pos hpos β).le
  have h := hM y hy
  rw [Real.rpow_neg hpos.le] at h
  have h1 : |f y| * (‖y‖ ^ α)⁻¹ ≤ M := by
    have : |f y| * (‖y‖ ^ α)⁻¹ ≤ |f y| * ((‖y‖ ^ α)⁻¹ + ‖y‖ ^ β) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hb) (abs_nonneg _)
    linarith
  calc |f y| = |f y| * (‖y‖ ^ α)⁻¹ * ‖y‖ ^ α := by field_simp
    _ ≤ M * ‖y‖ ^ α := mul_le_mul_of_nonneg_right h1 ha.le

/-- The weighted bound gives `|f(y)| ≤ M |y|^(-β)` on the open upper half-plane. -/
theorem abs_le_mul_rpow_neg_of_weighted_le
    (hM : ∀ y : ℝ^2, 0 < y 1 → |f y| * (‖y‖ ^ (-α) + ‖y‖ ^ β) ≤ M) {y : ℝ^2} (hy : 0 < y 1) :
    |f y| ≤ M * ‖y‖ ^ (-β) := by
  have hpos : 0 < ‖y‖ := by
    have : |y 1| ≤ ‖y‖ := by simpa using PiLp.norm_apply_le y 1
    rw [abs_of_pos hy] at this; linarith
  have ha : 0 ≤ ‖y‖ ^ (-α) := (Real.rpow_pos_of_pos hpos _).le
  have hb : 0 < ‖y‖ ^ β := Real.rpow_pos_of_pos hpos β
  have h := hM y hy
  have h1 : |f y| * ‖y‖ ^ β ≤ M := by
    have : |f y| * ‖y‖ ^ β ≤ |f y| * (‖y‖ ^ (-α) + ‖y‖ ^ β) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_left ha) (abs_nonneg _)
    linarith
  rw [Real.rpow_neg hpos.le]
  calc |f y| = |f y| * ‖y‖ ^ β * (‖y‖ ^ β)⁻¹ := by field_simp
    _ ≤ M * (‖y‖ ^ β)⁻¹ := mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr hb.le)

/-- The weighted bound of Part I, Lemma 6.5: `|f(y)| (|y|^(-α) + |y|^β) ≤ M` on the open upper
half-plane gives `|f(y)| ≤ M min(|y|^α, |y|^(-β))` there. -/
theorem abs_le_mul_min_rpow
    (hM : ∀ y : ℝ^2, 0 < y 1 → |f y| * (‖y‖ ^ (-α) + ‖y‖ ^ β) ≤ M) {y : ℝ^2} (hy : 0 < y 1) :
    |f y| ≤ M * min (‖y‖ ^ α) (‖y‖ ^ (-β)) := by
  rw [mul_min_of_nonneg _ _ (nonneg_of_weighted_le hM)]
  exact le_min (abs_le_mul_rpow_of_weighted_le hM hy) (abs_le_mul_rpow_neg_of_weighted_le hM hy)

/-- A bound on the open upper half-plane by a nonnegative function invariant under the reflection
in the boundary bounds the odd extension on the whole plane. -/
theorem abs_oddHalfSpaceExtension_le_of_forall {g : ℝ^2 → ℝ}
    (hg : ∀ y : ℝ^2, 0 < y 1 → |f y| ≤ g y) (hgR : ∀ y, g (𝐑 1 y) = g y) (hg0 : ∀ y, 0 ≤ g y)
    (y : ℝ^2) : |oddHalfSpaceExtension f y| ≤ g y := by
  rcases lt_trichotomy (y 1) 0 with hy | hy | hy
  · have hyl : y ∈ HalfSpace.lower 2 := hy
    have hyu : y ∉ HalfSpace.upper 2 := fun h ↦ by
      have : (0 : ℝ) < y 1 := h
      linarith
    have h1 : 0 < (𝐑 1 y) 1 := by
      rw [PDE.Common.coordinateReflection_apply_same]; linarith
    simp only [oddHalfSpaceExtension, Pi.sub_apply, indicator_of_mem hyl,
      indicator_of_notMem hyu, zero_sub, abs_neg, reflect_two_eq_coordinateReflection_one]
    rw [← hgR y]
    exact hg _ h1
  · have hyl : y ∉ HalfSpace.lower 2 := fun h ↦ by
      have : y 1 < 0 := h
      linarith
    have hyu : y ∉ HalfSpace.upper 2 := fun h ↦ by
      have : (0 : ℝ) < y 1 := h
      linarith
    simp only [oddHalfSpaceExtension, Pi.sub_apply, indicator_of_notMem hyl,
      indicator_of_notMem hyu, sub_zero, abs_zero]
    exact hg0 y
  · have hyu : y ∈ HalfSpace.upper 2 := hy
    have hyl : y ∉ HalfSpace.lower 2 := fun h ↦ by
      have : y 1 < 0 := h
      linarith
    simp only [oddHalfSpaceExtension, Pi.sub_apply, indicator_of_mem hyu,
      indicator_of_notMem hyl, sub_zero]
    exact hg y hy

/-- The odd extension keeps a bound `|f(y)| ≤ M |y|^γ` from the open upper half-plane. -/
private theorem abs_oddHalfSpaceExtension_le_mul_rpow {γ : ℝ} (hM0 : 0 ≤ M)
    (h : ∀ y : ℝ^2, 0 < y 1 → |f y| ≤ M * ‖y‖ ^ γ) (y : ℝ^2) :
    |oddHalfSpaceExtension f y| ≤ M * ‖y‖ ^ γ :=
  abs_oddHalfSpaceExtension_le_of_forall h (fun y ↦ by rw [PDE.Common.norm_coordinateReflection])
    (fun y ↦ by positivity) y

end Pointwise

/-! ### The far region -/

section Far

/-- The far region `{y | 2|x| ≤ |y|}`. -/
def farRegion (x : ℝ^2) : Set (ℝ^2) := {y | 2 * ‖x‖ ≤ ‖y‖}

/-- The far region is measurable. -/
theorem measurableSet_farRegion (x : ℝ^2) : MeasurableSet (farRegion x) :=
  measurableSet_le measurable_const measurable_norm

/-- The far region is the complement of the open disc of radius `2|x|`. -/
theorem farRegion_eq_compl_ball (x : ℝ^2) : farRegion x = (ball (0 : ℝ^2) (2 * ‖x‖))ᶜ := by
  ext y; simp [farRegion]

/-- Folding the far region onto the quadrant. -/
theorem setIntegral_farRegion_eq (j : Fin 2) (ℓ : ℝ) {W : ℝ^2 → ℝ}
    (hW₀ : ∀ y, W (𝐑 0 y) = -W y) (hW₁ : ∀ y, W (𝐑 1 y) = -W y) (x : ℝ^2)
    (hF : Integrable fun y ↦
      (gradientKernel j (x - y) - ℓ / Real.pi * hessianKernel 0 1 y) * W y) :
    ∫ y in farRegion x, (gradientKernel j (x - y) - ℓ / Real.pi * hessianKernel 0 1 y) * W y =
      ∫ y in farRegion x ∩ quadrant,
        (symmetrizedKernel (gradientKernel j) x y - 4 * ℓ / Real.pi * hessianKernel 0 1 y) *
          W y := by
  have hA₀ : ∀ y, 𝐑 0 y ∈ farRegion x ↔ y ∈ farRegion x := fun y ↦ by
    simp only [farRegion, mem_ofPred_eq, PDE.Common.norm_coordinateReflection]
  have hA₁ : ∀ y, 𝐑 1 y ∈ farRegion x ↔ y ∈ farRegion x := fun y ↦ by
    simp only [farRegion, mem_ofPred_eq, PDE.Common.norm_coordinateReflection]
  rw [setIntegral_eq_setIntegral_inter_quadrant (measurableSet_farRegion x) hA₀ hA₁
    hF.integrableOn]
  refine setIntegral_congr_fun ((measurableSet_farRegion x).inter measurableSet_quadrant)
    fun y _ ↦ ?_
  have hneg : W (-y) = W y := by rw [← coordinateReflection_zero_one, hW₀, hW₁, neg_neg]
  simp only [hW₀, hW₁, hneg, hessianKernel_zero_one_coordinateReflection,
    hessianKernel_neg, symmetrizedKernel, sub_neg_eq_add]
  ring

/-- The far bound of the symmetrized gradient kernel without the linear term:
`|g_{js}(x, y)| ≤ (10/π) |x|/|y|²` for `2|x| ≤ |y|`. -/
theorem abs_symmetrizedKernel_le_of_sub_le {j k : Fin 2} {x y : ℝ^2} (hy : y ≠ 0)
    (hxy : 2 * ‖x‖ ≤ ‖y‖)
    (hker : |symmetrizedKernel (gradientKernel j) x y - 4 / Real.pi * x k * hessianKernel 0 1 y| ≤
      32 / Real.pi * ‖x‖ ^ 3 / ‖y‖ ^ 4) :
    |symmetrizedKernel (gradientKernel j) x y| ≤ 10 / Real.pi * ‖x‖ / ‖y‖ ^ 2 := by
  have hb : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hlin : |4 / Real.pi * x k * hessianKernel 0 1 y| ≤ 2 / Real.pi * ‖x‖ / ‖y‖ ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 / Real.pi)]
    calc 4 / Real.pi * |x k| * |hessianKernel 0 1 y| ≤ 4 / Real.pi * ‖x‖ * (1 / (2 * ‖y‖ ^ 2)) := by
          gcongr
          · simpa using PiLp.norm_apply_le x k
          · exact abs_hessianKernel_le 0 1 y
      _ = 2 / Real.pi * ‖x‖ / ‖y‖ ^ 2 := by field_simp; ring
  have hcub : 32 / Real.pi * ‖x‖ ^ 3 / ‖y‖ ^ 4 ≤ 8 / Real.pi * ‖x‖ / ‖y‖ ^ 2 :=
    calc 32 / Real.pi * ‖x‖ ^ 3 / ‖y‖ ^ 4 = 32 / Real.pi * ‖x‖ * ‖x‖ ^ 2 / ‖y‖ ^ 4 := by ring
      _ ≤ 32 / Real.pi * ‖x‖ * (‖y‖ ^ 2 / 4) / ‖y‖ ^ 4 := by gcongr; nlinarith [norm_nonneg x]
      _ = 8 / Real.pi * ‖x‖ / ‖y‖ ^ 2 := by field_simp; ring
  rw [show 10 / Real.pi * ‖x‖ / ‖y‖ ^ 2 =
    8 / Real.pi * ‖x‖ / ‖y‖ ^ 2 + 2 / Real.pi * ‖x‖ / ‖y‖ ^ 2 by ring]
  linarith [abs_sub_abs_le_abs_sub (symmetrizedKernel (gradientKernel j) x y)
    (4 / Real.pi * x k * hessianKernel 0 1 y)]

/-- The symmetrized gradient kernel is measurable in `y`. -/
theorem measurable_symmetrizedKernel_gradientKernel (j : Fin 2) (x : ℝ^2) :
    Measurable (symmetrizedKernel (gradientKernel j) x) := by
  have mg := measurable_gradientKernel j
  have hR (i : Fin 2) : Measurable (𝐑 i : ℝ^2 → ℝ^2) :=
    (PDE.Common.contDiff_coordinateReflection i 0).continuous.measurable
  unfold symmetrizedKernel
  exact (((mg.comp (measurable_const.sub measurable_id)).sub
    (mg.comp (measurable_const.sub (hR 0)))).sub (mg.comp (measurable_const.sub (hR 1)))).add
      (mg.comp (measurable_const.add measurable_id))

/-- Points of the open quadrant have positive norm. -/
theorem norm_pos_of_mem_quadrant {y : ℝ^2} (hy : y ∈ quadrant) : 0 < ‖y‖ :=
  norm_pos_iff.mpr (ne_zero_of_mem_quadrant hy)

/-- The near region lies in the disc `B(x, 3|x|)`. -/
private theorem compl_farRegion_subset_ball (x : ℝ^2) : (farRegion x)ᶜ ⊆ ball x (3 * ‖x‖) :=
  fun y hy ↦ by
    simp only [farRegion, mem_compl_iff, mem_ofPred_eq, not_le] at hy
    rw [mem_ball, dist_eq_norm]
    linarith [norm_sub_le y x]

/-- `|gⱼ(x - y) W(y)| ≤ B/(2π) |x - y|^(1-2)` when `|W(y)| ≤ B`. -/
private theorem abs_gradientKernel_mul_le {j : Fin 2} {x y : ℝ^2} {W : ℝ^2 → ℝ} {B : ℝ}
    (hB : |W y| ≤ B) :
    |gradientKernel j (x - y) * W y| ≤ B / (2 * Real.pi) * ‖x - y‖ ^ ((1 : ℝ) - 2) := by
  have hg := norm_gradientKernel_le j (x - y)
  rw [Real.norm_eq_abs] at hg
  rw [abs_mul, show (1 : ℝ) - 2 = -1 by norm_num]
  calc _ ≤ 1 / (2 * Real.pi) * ‖x - y‖ ^ (-1 : ℝ) * B :=
        mul_le_mul hg hB (abs_nonneg _) (by positivity)
    _ = _ := by ring

/-- The far bound of `gⱼₛ W` for `|W(y)| ≤ M |y|^γ`:
`|gⱼₛ(x, y) W(y)| ≤ (10/π) M |x| |y|^(γ-2)`. -/
private theorem abs_symmetrizedKernel_mul_le_rpow {j k : Fin 2} {x y : ℝ^2}
    (hy : y ∈ farRegion x ∩ quadrant)
    (hker : |symmetrizedKernel (gradientKernel j) x y - 4 / Real.pi * x k * hessianKernel 0 1 y| ≤
      32 / Real.pi * ‖x‖ ^ 3 / ‖y‖ ^ 4) {W : ℝ^2 → ℝ} {M γ : ℝ} (hW : |W y| ≤ M * ‖y‖ ^ γ) :
    |symmetrizedKernel (gradientKernel j) x y * W y| ≤
      10 * M * ‖x‖ / Real.pi * ‖y‖ ^ (γ - 2) := by
  rw [abs_mul, Real.rpow_sub (norm_pos_of_mem_quadrant hy.2), Real.rpow_two]
  calc _ ≤ 10 / Real.pi * ‖x‖ / ‖y‖ ^ 2 * (M * ‖y‖ ^ γ) :=
        mul_le_mul (abs_symmetrizedKernel_le_of_sub_le (ne_zero_of_mem_quadrant hy.2) hy.1 hker)
          hW (abs_nonneg _) (by positivity)
    _ = _ := by ring

/-- The far bound of the corrected kernel times `W` for `|W(y)| ≤ M |y|^γ`:
`|(gⱼₛ(x, y) - (4/π) x_k K₁(y)) W(y)| ≤ (32/π) M |x|³ |y|^(γ-4)`. -/
private theorem abs_correctedKernel_mul_le_rpow {j k : Fin 2} {x y : ℝ^2} (hy : y ∈ quadrant)
    (hker : |symmetrizedKernel (gradientKernel j) x y - 4 / Real.pi * x k * hessianKernel 0 1 y| ≤
      32 / Real.pi * ‖x‖ ^ 3 / ‖y‖ ^ 4) {W : ℝ^2 → ℝ} {M γ : ℝ} (hW : |W y| ≤ M * ‖y‖ ^ γ) :
    |(symmetrizedKernel (gradientKernel j) x y - 4 * x k / Real.pi * hessianKernel 0 1 y) * W y| ≤
      32 * M * ‖x‖ ^ 3 / Real.pi * ‖y‖ ^ (γ - 4) := by
  rw [show 4 / Real.pi * x k * hessianKernel 0 1 y = 4 * x k / Real.pi * hessianKernel 0 1 y by
    ring] at hker
  rw [abs_mul, Real.rpow_sub (norm_pos_of_mem_quadrant hy), Real.rpow_ofNat]
  calc _ ≤ 32 / Real.pi * ‖x‖ ^ 3 / ‖y‖ ^ 4 * (M * ‖y‖ ^ γ) :=
        mul_le_mul hker hW (abs_nonneg _) (by positivity)
    _ = _ := by ring

end Far

/-! ### The linear bound -/

section Estimates

variable {f : ℝ^2 → ℝ} (hf : Continuous f) (hc : HasCompactSupport f)
  (hodd : ∀ y : ℝ^2, 0 < y 1 → f (𝐑 0 y) = -f y)
include hf hc hodd

omit hf hc in
/-- The odd extension of an `x₀`-odd source is odd under `R₀`. -/
private theorem oddHalfSpaceExtension_reflect_zero_neg (y : ℝ^2) :
    oddHalfSpaceExtension f (𝐑 0 y) = -oddHalfSpaceExtension f y := by
  rw [oddHalfSpaceExtension_reflect_zero_eq_mul (ω := f) (c := -1)
    (fun y hy ↦ by rw [hodd y hy]; ring) y]
  ring

/-- `∂ⱼφ(x)` is the integral of `gⱼₛ W` over the far part of the quadrant plus the integral of
`gⱼ(x - ·) W` over the near region. -/
private theorem partialDeriv_eq_farRegion_add (j : Fin 2) (x : ℝ^2) :
    (∂[j] (halfSpaceGreenPotential f)) x =
      (∫ y in farRegion x ∩ quadrant,
        symmetrizedKernel (gradientKernel j) x y * oddHalfSpaceExtension f y) +
      ∫ y in (farRegion x)ᶜ, gradientKernel j (x - y) * oddHalfSpaceExtension f y := by
  have hFi := integrable_gradientKernel_sub_mul_oddHalfSpaceExtension hf hc j x
  have hfold := setIntegral_farRegion_eq j 0 (oddHalfSpaceExtension_reflect_zero_neg hodd)
    (oddHalfSpaceExtension_reflect_one f) x (by simpa using hFi)
  simp only [zero_div, zero_mul, sub_zero, mul_zero] at hfold
  rw [partialDeriv_halfSpaceGreenPotential_eq_integral hf hc j x,
    ← integral_add_compl (measurableSet_farRegion x) hFi, hfold]

/-- **The linear bound** `|∂ⱼφ(x)| ≤ (20/α + 20/β + 3) M |x|` for
`|f(y)| ≤ M min(|y|^α, |y|^(-β), 1)`: the far region split at `|y| = 1`, the near region by
`|f| ≤ M`. The far-field bound of the symmetrized kernel `gⱼₛ` with linear coefficient
`(4/π) x_k K₁` is the hypothesis `hker`. -/
theorem abs_partialDeriv_le_mul_norm {α β M : ℝ} (hα : 0 < α) (hβ : 0 < β) (hM0 : 0 ≤ M)
    (hpow : ∀ y : ℝ^2, 0 < y 1 → |f y| ≤ M * ‖y‖ ^ α)
    (hdec : ∀ y : ℝ^2, 0 < y 1 → |f y| ≤ M * ‖y‖ ^ (-β))
    (hbdd : ∀ y : ℝ^2, 0 < y 1 → |f y| ≤ M) (j k : Fin 2)
    (hker : ∀ x y : ℝ^2, y ≠ 0 → 2 * ‖x‖ ≤ ‖y‖ →
      |symmetrizedKernel (gradientKernel j) x y - 4 / Real.pi * x k * hessianKernel 0 1 y| ≤
        32 / Real.pi * ‖x‖ ^ 3 / ‖y‖ ^ 4) (x : ℝ^2) :
    |(∂[j] (halfSpaceGreenPotential f)) x| ≤ (20 / α + 20 / β + 3) * M * ‖x‖ := by
  have hpi : 0 < Real.pi := Real.pi_pos
  set W := oddHalfSpaceExtension f with hWdef
  rw [partialDeriv_eq_farRegion_add hf hc hodd j x]
  -- the far region, split at `|y| = 1`
  have hfar := (integrableOn_and_abs_setIntegral_le_split
    (F := fun y ↦ symmetrizedKernel (gradientKernel j) x y * W y)
    ((measurableSet_farRegion x).inter measurableSet_quadrant)
    ((measurable_symmetrizedKernel_gradientKernel j x).aestronglyMeasurable.mul
      (integrable_oddHalfSpaceExtension hf hc).aestronglyMeasurable)
    (by positivity : 0 ≤ 10 * M * ‖x‖ / Real.pi) hα (by linarith : 1 - β < 1)
    (fun y hy ↦ abs_symmetrizedKernel_mul_le_rpow hy.1
      (hker x y (ne_zero_of_mem_quadrant hy.1.2) hy.1.1)
      (abs_oddHalfSpaceExtension_le_mul_rpow hM0 hpow y))
    (fun y hy ↦ by
      rw [show (1 - β) - 3 = -β - 2 by ring]
      exact abs_symmetrizedKernel_mul_le_rpow hy.1
        (hker x y (ne_zero_of_mem_quadrant hy.1.2) hy.1.1)
        (abs_oddHalfSpaceExtension_le_mul_rpow hM0 hdec y))).2
  -- the near region
  have hnear := abs_setIntegral_le_of_lintegral_le (F := fun y ↦ gradientKernel j (x - y) * W y)
    (measurableSet_farRegion x).compl
    (compl_farRegion_subset_ball x) (by positivity)
    (fun y _ ↦ abs_gradientKernel_mul_le (abs_oddHalfSpaceExtension_le_of_forall hbdd
      (fun _ ↦ rfl) (fun _ ↦ hM0) y))
    (le_of_eq (lintegral_ball_sub_inv (by positivity) (by positivity) x))
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ 10 * M * ‖x‖ / Real.pi * (2 * Real.pi / α) +
          10 * M * ‖x‖ / Real.pi * (2 * Real.pi / (1 - (1 - β))) +
        M / (2 * Real.pi) * (2 * Real.pi * (3 * ‖x‖)) := add_le_add hfar hnear
    _ = (20 / α + 20 / β + 3) * M * ‖x‖ := by
        rw [show 1 - (1 - β) = β by ring]; field_simp; ring


/-- **The decaying bound** `|∂ⱼφ(x)| ≤ (20/β + 9) M |x|^(1-β)`, `x ≠ 0`, for
`|f(y)| ≤ M |y|^(-β)`, `0 < β < 1`: the far region, the disc `|y - x| < |x|/2` where
`|y| ≥ |x|/2`, and the rest of `|y| < 2|x|` where `|x - y| ≥ |x|/2`. -/
theorem abs_partialDeriv_le_mul_rpow {β M : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hM0 : 0 ≤ M)
    (hdec : ∀ y : ℝ^2, 0 < y 1 → |f y| ≤ M * ‖y‖ ^ (-β)) (j k : Fin 2)
    (hker : ∀ x y : ℝ^2, y ≠ 0 → 2 * ‖x‖ ≤ ‖y‖ →
      |symmetrizedKernel (gradientKernel j) x y - 4 / Real.pi * x k * hessianKernel 0 1 y| ≤
        32 / Real.pi * ‖x‖ ^ 3 / ‖y‖ ^ 4) {x : ℝ^2} (hx : x ≠ 0) :
    |(∂[j] (halfSpaceGreenPotential f)) x| ≤ (20 / β + 9) * M * ‖x‖ ^ (1 - β) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hxp : 0 < ‖x‖ := norm_pos_iff.mpr hx
  set W := oddHalfSpaceExtension f with hWdef
  have hWβ := abs_oddHalfSpaceExtension_le_mul_rpow hM0 hdec
  rw [partialDeriv_eq_farRegion_add hf hc hodd j x]
  -- far region
  set c := 10 * M * ‖x‖ / Real.pi with hcdef
  have hc0 : 0 ≤ c := by positivity
  have hA := measurableSet_farRegion x
  have hS := hA.inter measurableSet_quadrant
  have hfle : ∀ y ∈ farRegion x ∩ quadrant,
      |symmetrizedKernel (gradientKernel j) x y * W y| ≤ c * ‖y‖ ^ ((1 - β) - 3) := fun y hy ↦ by
    rw [show (1 - β) - 3 = -β - 2 by ring]
    exact abs_symmetrizedKernel_mul_le_rpow hy (hker x y (ne_zero_of_mem_quadrant hy.2) hy.1)
      (hWβ y)
  have hfar := abs_setIntegral_le_of_lintegral_le hS
    (inter_subset_left.trans (farRegion_eq_compl_ball x).le)
    (mul_nonneg hc0 (div_nonneg (by positivity) (by linarith))) hfle
    (le_of_eq (lintegral_compl_ball_zero_rpow hc0 (by positivity) (by linarith)))
  have hpow2 : (2 * ‖x‖) ^ ((1 - β) - 1) ≤ ‖x‖ ^ (-β) := by
    rw [show (1 - β) - 1 = -β by ring]
    exact Real.rpow_le_rpow_of_nonpos hxp (by linarith) (by linarith)
  have hfar' : |∫ y in farRegion x ∩ quadrant, symmetrizedKernel (gradientKernel j) x y * W y| ≤
      20 / β * M * ‖x‖ ^ (1 - β) := by
    refine hfar.trans ?_
    rw [show 1 - (1 - β) = β by ring, hcdef]
    have h1 : ‖x‖ ^ (1 - β) = ‖x‖ * ‖x‖ ^ (-β) := by
      rw [show 1 - β = 1 + -β by ring, Real.rpow_add hxp, Real.rpow_one]
    rw [h1]
    calc 10 * M * ‖x‖ / Real.pi * (2 * Real.pi * (2 * ‖x‖) ^ (1 - β - 1) / β) =
          20 / β * M * ‖x‖ * (2 * ‖x‖) ^ (1 - β - 1) := by field_simp; ring
      _ ≤ 20 / β * M * ‖x‖ * ‖x‖ ^ (-β) := by gcongr
      _ = 20 / β * M * (‖x‖ * ‖x‖ ^ (-β)) := by ring
  -- near region, split at the disc around `x`
  have hFc : IntegrableOn (fun y ↦ gradientKernel j (x - y) * W y) (farRegion x)ᶜ :=
    (integrable_gradientKernel_sub_mul_oddHalfSpaceExtension hf hc j x).integrableOn
  have hBx : MeasurableSet (ball x (‖x‖ / 2)) := measurableSet_ball
  rw [← integral_inter_add_sdiff hBx hFc]
  have hn1le : ∀ y ∈ (farRegion x)ᶜ ∩ ball x (‖x‖ / 2),
      |gradientKernel j (x - y) * W y| ≤
        M * (‖x‖ / 2) ^ (-β) / (2 * Real.pi) * ‖x - y‖ ^ ((1 : ℝ) - 2) := fun y hy ↦ by
    have hxy : ‖x - y‖ < ‖x‖ / 2 := by rw [← dist_eq_norm, dist_comm]; exact hy.2
    have hy2 : ‖x‖ / 2 ≤ ‖y‖ := by
      have := norm_sub_norm_le x (x - y); rw [sub_sub_cancel] at this; linarith
    exact abs_gradientKernel_mul_le ((hWβ y).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (by positivity) hy2 (by linarith)) hM0))
  have hnear1 := abs_setIntegral_le_of_lintegral_le (hA.compl.inter hBx) inter_subset_right
    (by positivity) hn1le (le_of_eq (lintegral_ball_sub_inv (by positivity) (by positivity) x))
  have hn2le : ∀ y ∈ (farRegion x)ᶜ \ ball x (‖x‖ / 2),
      |gradientKernel j (x - y) * W y| ≤ M / (Real.pi * ‖x‖) * ‖y‖ ^ ((2 - β) - 2) :=
    fun y hy ↦ by
      have hxy : ‖x‖ / 2 ≤ ‖x - y‖ := by
        have := hy.2; rw [mem_ball, dist_eq_norm, norm_sub_rev, not_lt] at this; exact this
      have hxy' : 0 < ‖x - y‖ := by linarith
      rw [abs_mul, show (2 - β) - 2 = -β by ring]
      have hg : |gradientKernel j (x - y)| ≤ 1 / (Real.pi * ‖x‖) := by
        refine (abs_gradientKernel_le j (x - y)).trans ?_
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      calc |gradientKernel j (x - y)| * |W y| ≤ 1 / (Real.pi * ‖x‖) * (M * ‖y‖ ^ (-β)) :=
            mul_le_mul hg (hWβ y) (abs_nonneg _) (by positivity)
        _ = M / (Real.pi * ‖x‖) * ‖y‖ ^ (-β) := by ring
  have hsub2 : (farRegion x)ᶜ \ ball x (‖x‖ / 2) ⊆ ball (0 : ℝ^2) (2 * ‖x‖) := fun y hy ↦ by
    have := hy.1
    rw [farRegion_eq_compl_ball, compl_compl] at this
    exact this
  have hnear2 := abs_setIntegral_le_of_lintegral_le (hA.compl.diff hBx) hsub2
    (mul_nonneg (by positivity) (div_nonneg (by positivity) (by linarith))) hn2le
    (le_of_eq (lintegral_ball_zero_rpow (by positivity) (by positivity) (by linarith)))
  have hnear2' : M / (Real.pi * ‖x‖) * (2 * Real.pi * (2 * ‖x‖) ^ (2 - β) / (2 - β)) ≤
      8 * M * ‖x‖ ^ (1 - β) := by
    have h2 : (2 * ‖x‖) ^ (2 - β) ≤ 4 * ‖x‖ ^ (2 - β) := by
      rw [Real.mul_rpow (by norm_num) hxp.le]
      have : (2 : ℝ) ^ (2 - β) ≤ 4 :=
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith : 2 - β ≤ 2)).trans_eq
          (by norm_num)
      gcongr
    have h3 : ‖x‖ ^ (2 - β) = ‖x‖ * ‖x‖ ^ (1 - β) := by
      rw [show 2 - β = 1 + (1 - β) by ring, Real.rpow_add hxp, Real.rpow_one]
    have h4 : 1 ≤ 2 - β := by linarith
    calc M / (Real.pi * ‖x‖) * (2 * Real.pi * (2 * ‖x‖) ^ (2 - β) / (2 - β)) ≤
          M / (Real.pi * ‖x‖) * (2 * Real.pi * (4 * ‖x‖ ^ (2 - β)) / 1) := by
          gcongr
      _ = 8 * M * ‖x‖ ^ (1 - β) := by rw [h3]; field_simp; ring
  have hnear1' : M * (‖x‖ / 2) ^ (-β) / (2 * Real.pi) * (2 * Real.pi * (‖x‖ / 2)) ≤
      M * ‖x‖ ^ (1 - β) := by
    have h1 : (‖x‖ / 2) ^ (-β) * (‖x‖ / 2) = (‖x‖ / 2) ^ (1 - β) := by
      rw [show 1 - β = -β + 1 by ring, Real.rpow_add (by positivity), Real.rpow_one]
    have h2 : (‖x‖ / 2) ^ (1 - β) ≤ ‖x‖ ^ (1 - β) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
    calc M * (‖x‖ / 2) ^ (-β) / (2 * Real.pi) * (2 * Real.pi * (‖x‖ / 2)) =
          M * ((‖x‖ / 2) ^ (-β) * (‖x‖ / 2)) := by field_simp
      _ ≤ M * ‖x‖ ^ (1 - β) := by rw [h1]; exact mul_le_mul_of_nonneg_left h2 hM0
  calc |(∫ y in farRegion x ∩ quadrant, symmetrizedKernel (gradientKernel j) x y * W y) +
        ((∫ y in (farRegion x)ᶜ ∩ ball x (‖x‖ / 2), gradientKernel j (x - y) * W y) +
          ∫ y in (farRegion x)ᶜ \ ball x (‖x‖ / 2), gradientKernel j (x - y) * W y)|
      ≤ |∫ y in farRegion x ∩ quadrant, symmetrizedKernel (gradientKernel j) x y * W y| +
        (|∫ y in (farRegion x)ᶜ ∩ ball x (‖x‖ / 2), gradientKernel j (x - y) * W y| +
          |∫ y in (farRegion x)ᶜ \ ball x (‖x‖ / 2), gradientKernel j (x - y) * W y|) :=
        (abs_add_le _ _).trans (add_le_add_right (abs_add_le _ _) _)
    _ ≤ 20 / β * M * ‖x‖ ^ (1 - β) + (M * ‖x‖ ^ (1 - β) + 8 * M * ‖x‖ ^ (1 - β)) :=
        add_le_add hfar' (add_le_add (hnear1.trans hnear1') (hnear2.trans hnear2'))
    _ = (20 / β + 9) * M * ‖x‖ ^ (1 - β) := by ring


omit hf hc hodd in
/-- `|K₁(y) W(y)| ≤ (M/2) |y|^(α-2)` when `|W(y)| ≤ M |y|^α`. -/
theorem abs_hessianKernel_mul_le {W : ℝ^2 → ℝ} {α M : ℝ} (hM0 : 0 ≤ M) {y : ℝ^2}
    (hW : |W y| ≤ M * ‖y‖ ^ α) : |hessianKernel 0 1 y * W y| ≤ M / 2 * ‖y‖ ^ (α - 2) := by
  by_cases hy : y = 0
  · have h0 : hessianKernel 0 1 (0 : ℝ^2) = 0 := by simp [hessianKernel]
    rw [hy, h0, zero_mul, abs_zero]; positivity
  have hp : 0 < ‖y‖ := norm_pos_iff.mpr hy
  rw [abs_mul, Real.rpow_sub hp, Real.rpow_two]
  calc |hessianKernel 0 1 y| * |W y| ≤ 1 / (2 * ‖y‖ ^ 2) * (M * ‖y‖ ^ α) :=
        mul_le_mul (abs_hessianKernel_le 0 1 y) hW (abs_nonneg _) (by positivity)
    _ = M / 2 * (‖y‖ ^ α / ‖y‖ ^ 2) := by field_simp

omit hodd in
/-- `K₁ W` is integrable when `|f(y)| ≤ M |y|^α`, `α > 0`. -/
theorem integrable_hessianKernel_mul_oddHalfSpaceExtension_of_le {α M : ℝ} (hα : 0 < α)
    (hM0 : 0 ≤ M) (hpow : ∀ y : ℝ^2, 0 < y 1 → |f y| ≤ M * ‖y‖ ^ α) :
    Integrable fun y ↦ hessianKernel 0 1 y * oddHalfSpaceExtension f y := by
  have hWα : ∀ y, |oddHalfSpaceExtension f y| ≤ M * ‖y‖ ^ α :=
    abs_oddHalfSpaceExtension_le_of_forall hpow
      (fun y ↦ by rw [PDE.Common.norm_coordinateReflection]) (fun y ↦ by positivity)
  have hWi := integrable_oddHalfSpaceExtension hf hc
  have hm : AEStronglyMeasurable (fun y ↦ hessianKernel 0 1 y * oddHalfSpaceExtension f y) :=
    (measurable_hessianKernel 0 1).aestronglyMeasurable.mul hWi.aestronglyMeasurable
  have hnear : IntegrableOn (fun y ↦ hessianKernel 0 1 y * oddHalfSpaceExtension f y)
      (ball (0 : ℝ^2) 1) :=
    integrableOn_of_abs_le_of_lintegral_le measurableSet_ball subset_rfl hm.restrict
      (fun y _ ↦ abs_hessianKernel_mul_le hM0 (hWα y))
      (le_of_eq (lintegral_ball_zero_rpow (by positivity) zero_le_one hα))
  have hfar : IntegrableOn (fun y ↦ hessianKernel 0 1 y * oddHalfSpaceExtension f y)
      (ball (0 : ℝ^2) 1)ᶜ := by
    refine hWi.integrableOn.bdd_mul (c := 1 / 2)
      (measurable_hessianKernel 0 1).aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_ball.compl] with y hy
    rw [mem_compl_iff, mem_ball, dist_zero_right, not_lt] at hy
    rw [Real.norm_eq_abs]
    refine (abs_hessianKernel_le 0 1 y).trans ?_
    rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]
    nlinarith
  have := hnear.union hfar
  rwa [union_compl_self, integrableOn_univ] at this

/-- The corrected gradient integral split into the folded far part and the near part. -/
private theorem integral_sub_eq_farRegion_add {α M : ℝ} (hα : 0 < α) (hM0 : 0 ≤ M)
    (hpow : ∀ y : ℝ^2, 0 < y 1 → |f y| ≤ M * ‖y‖ ^ α) (j k : Fin 2) (x : ℝ^2) :
    ∫ y, (gradientKernel j (x - y) - x k / Real.pi * hessianKernel 0 1 y) *
        oddHalfSpaceExtension f y =
      (∫ y in farRegion x ∩ quadrant,
        (symmetrizedKernel (gradientKernel j) x y - 4 * x k / Real.pi * hessianKernel 0 1 y) *
          oddHalfSpaceExtension f y) +
      ∫ y in (farRegion x)ᶜ, (gradientKernel j (x - y) - x k / Real.pi * hessianKernel 0 1 y) *
        oddHalfSpaceExtension f y := by
  have hF : Integrable fun y ↦ (gradientKernel j (x - y) - x k / Real.pi * hessianKernel 0 1 y) *
      oddHalfSpaceExtension f y :=
    ((integrable_gradientKernel_sub_mul_oddHalfSpaceExtension hf hc j x).sub
      ((integrable_hessianKernel_mul_oddHalfSpaceExtension_of_le hf hc hα hM0 hpow).const_mul
        (x k / Real.pi))).congr (.of_forall fun y ↦ by simp only [Pi.sub_apply]; ring)
  rw [← integral_add_compl (measurableSet_farRegion x) hF, setIntegral_farRegion_eq j (x k)
    (oddHalfSpaceExtension_reflect_zero_neg hodd) (oddHalfSpaceExtension_reflect_one f) x hF]

omit hodd in
/-- The near part `|y| < 2|x|` of the corrected gradient integral. -/
theorem abs_setIntegral_compl_farRegion_le {α M : ℝ} (hα : 0 < α) (hM0 : 0 ≤ M)
    (hpow : ∀ y : ℝ^2, 0 < y 1 → |f y| ≤ M * ‖y‖ ^ α) (j k : Fin 2) (x : ℝ^2) :
    |∫ y in (farRegion x)ᶜ, (gradientKernel j (x - y) - x k / Real.pi * hessianKernel 0 1 y) *
        oddHalfSpaceExtension f y| ≤ (3 + 1 / α) * M * (2 * ‖x‖) ^ α * ‖x‖ := by
  have hpi : 0 < Real.pi := Real.pi_pos
  set W := oddHalfSpaceExtension f with hWdef
  have hWα := abs_oddHalfSpaceExtension_le_mul_rpow hM0 hpow
  have hKint := integrable_hessianKernel_mul_oddHalfSpaceExtension_of_le hf hc hα hM0 hpow
  have hA := measurableSet_farRegion x
  have hsplit : ∫ y in (farRegion x)ᶜ,
      (gradientKernel j (x - y) - x k / Real.pi * hessianKernel 0 1 y) * W y =
      (∫ y in (farRegion x)ᶜ, gradientKernel j (x - y) * W y) -
        x k / Real.pi * ∫ y in (farRegion x)ᶜ, hessianKernel 0 1 y * W y := by
    rw [← integral_const_mul, ← integral_sub
      (integrable_gradientKernel_sub_mul_oddHalfSpaceExtension hf hc j x).integrableOn
      (hKint.integrableOn.const_mul _)]
    exact setIntegral_congr_fun hA.compl fun y _ ↦ by ring
  rw [hsplit]
  have hball : (farRegion x)ᶜ = ball (0 : ℝ^2) (2 * ‖x‖) := by
    rw [farRegion_eq_compl_ball, compl_compl]
  have hle2 : ∀ y ∈ (farRegion x)ᶜ, ‖y‖ ^ α ≤ (2 * ‖x‖) ^ α := fun y hy ↦ by
    rw [hball, mem_ball, dist_zero_right] at hy
    exact Real.rpow_le_rpow (norm_nonneg _) hy.le hα.le
  have h1 := abs_setIntegral_le_of_lintegral_le (F := fun y ↦ gradientKernel j (x - y) * W y)
    hA.compl (compl_farRegion_subset_ball x)
    (by positivity) (fun y hy ↦ abs_gradientKernel_mul_le
      ((hWα y).trans (mul_le_mul_of_nonneg_left (hle2 y hy) hM0)))
    (le_of_eq (lintegral_ball_sub_inv (by positivity) (by positivity) x))
  have h2 := abs_setIntegral_le_of_lintegral_le hA.compl hball.le (by positivity)
    (fun y _ ↦ abs_hessianKernel_mul_le hM0 (hWα y))
    (le_of_eq (lintegral_ball_zero_rpow (by positivity) (by positivity) hα))
  have hxk : |x k / Real.pi| ≤ ‖x‖ / Real.pi := by
    rw [abs_div, abs_of_pos hpi]
    exact div_le_div_of_nonneg_right (by simpa using PiLp.norm_apply_le x k) hpi.le
  calc _ ≤ |∫ y in (farRegion x)ᶜ, gradientKernel j (x - y) * W y| +
        |x k / Real.pi| * |∫ y in (farRegion x)ᶜ, hessianKernel 0 1 y * W y| := by
        rw [← abs_mul]; exact abs_sub _ _
    _ ≤ M * (2 * ‖x‖) ^ α / (2 * Real.pi) * (2 * Real.pi * (3 * ‖x‖)) +
        ‖x‖ / Real.pi * (M / 2 * (2 * Real.pi * (2 * ‖x‖) ^ α / α)) := by
        gcongr
    _ = (3 + 1 / α) * M * (2 * ‖x‖) ^ α * ‖x‖ := by field_simp


/-- **The bound of the corrected integral for `0 < α < 2`:**
`|∫ (gⱼ(x - y) - π⁻¹ x_k K₁(y)) W(y) dy| ≤ (64/(2-α) + 12 + 4/α) M |x|^(1+α)` for
`|f(y)| ≤ M |y|^α`. -/
theorem abs_integral_sub_le_of_lt_two {α M : ℝ} (hα : 0 < α) (hα2 : α < 2) (hM0 : 0 ≤ M)
    (hpow : ∀ y : ℝ^2, 0 < y 1 → |f y| ≤ M * ‖y‖ ^ α) (j k : Fin 2)
    (hker : ∀ x y : ℝ^2, y ≠ 0 → 2 * ‖x‖ ≤ ‖y‖ →
      |symmetrizedKernel (gradientKernel j) x y - 4 / Real.pi * x k * hessianKernel 0 1 y| ≤
        32 / Real.pi * ‖x‖ ^ 3 / ‖y‖ ^ 4) (x : ℝ^2) :
    |∫ y, (gradientKernel j (x - y) - x k / Real.pi * hessianKernel 0 1 y) *
        oddHalfSpaceExtension f y| ≤ (64 / (2 - α) + 12 + 4 / α) * M * ‖x‖ ^ (1 + α) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have h2α : 0 < 2 - α := by linarith
  have hnear := abs_setIntegral_compl_farRegion_le hf hc hα hM0 hpow j k x
  set W := oddHalfSpaceExtension f with hWdef
  rw [integral_sub_eq_farRegion_add hf hc hodd hα hM0 hpow j k x]
  set c := 32 * M * ‖x‖ ^ 3 / Real.pi with hcdef
  have hfle : ∀ y ∈ farRegion x ∩ quadrant,
      |(symmetrizedKernel (gradientKernel j) x y - 4 * x k / Real.pi * hessianKernel 0 1 y) *
        W y| ≤ c * ‖y‖ ^ ((α - 1) - 3) := fun y hy ↦ by
    rw [show (α - 1) - 3 = α - 4 by ring]
    exact abs_correctedKernel_mul_le_rpow hy.2 (hker x y (ne_zero_of_mem_quadrant hy.2) hy.1)
      (abs_oddHalfSpaceExtension_le_mul_rpow hM0 hpow y)
  rcases eq_or_ne x 0 with rfl | hx
  · rw [setIntegral_eq_zero_of_forall_eq_zero fun y hy ↦ abs_nonpos_iff.mp (by
      simpa [c] using hfle y hy), zero_add]
    refine hnear.trans ?_
    rw [norm_zero, mul_zero]
    exact mul_nonneg (mul_nonneg (by positivity) hM0) (by positivity)
  have hxp : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hc0 : 0 ≤ c := by positivity
  have hfar := abs_setIntegral_le_of_lintegral_le
    ((measurableSet_farRegion x).inter measurableSet_quadrant)
    (inter_subset_left.trans (farRegion_eq_compl_ball x).le)
    (mul_nonneg hc0 (div_nonneg (by positivity) (by linarith))) hfle
    (le_of_eq (lintegral_compl_ball_zero_rpow hc0 (by positivity) (by linarith)))
  have hfar' : c * (2 * Real.pi * (2 * ‖x‖) ^ ((α - 1) - 1) / (1 - (α - 1))) ≤
      64 / (2 - α) * M * ‖x‖ ^ (1 + α) := by
    rw [show (α - 1) - 1 = α - 2 by ring, show 1 - (α - 1) = 2 - α by ring, hcdef]
    have h1 : (2 * ‖x‖) ^ (α - 2) ≤ ‖x‖ ^ (α - 2) :=
      Real.rpow_le_rpow_of_nonpos hxp (by linarith) (by linarith)
    have h2 : ‖x‖ ^ (1 + α) = ‖x‖ ^ 3 * ‖x‖ ^ (α - 2) := by
      rw [show 1 + α = ((3 : ℕ) : ℝ) + (α - 2) by push_cast; ring, Real.rpow_add hxp,
        Real.rpow_natCast]
    rw [h2]
    calc 32 * M * ‖x‖ ^ 3 / Real.pi * (2 * Real.pi * (2 * ‖x‖) ^ (α - 2) / (2 - α)) =
          64 / (2 - α) * M * ‖x‖ ^ 3 * (2 * ‖x‖) ^ (α - 2) := by field_simp; ring
      _ ≤ 64 / (2 - α) * M * ‖x‖ ^ 3 * ‖x‖ ^ (α - 2) := by gcongr
      _ = _ := by ring
  have hnear' : (3 + 1 / α) * M * (2 * ‖x‖) ^ α * ‖x‖ ≤ (12 + 4 / α) * M * ‖x‖ ^ (1 + α) := by
    have h1 : (2 * ‖x‖) ^ α ≤ 4 * ‖x‖ ^ α := by
      rw [Real.mul_rpow (by norm_num) hxp.le]
      have : (2 : ℝ) ^ α ≤ 4 :=
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) hα2.le).trans_eq (by norm_num)
      gcongr
    have h2 : ‖x‖ ^ (1 + α) = ‖x‖ * ‖x‖ ^ α := by
      rw [Real.rpow_add hxp, Real.rpow_one]
    rw [h2]
    calc (3 + 1 / α) * M * (2 * ‖x‖) ^ α * ‖x‖ ≤ (3 + 1 / α) * M * (4 * ‖x‖ ^ α) * ‖x‖ := by
          gcongr
      _ = (12 + 4 / α) * M * (‖x‖ * ‖x‖ ^ α) := by ring
  calc _ ≤ |∫ y in farRegion x ∩ quadrant,
        (symmetrizedKernel (gradientKernel j) x y - 4 * x k / Real.pi * hessianKernel 0 1 y) *
          W y| + |∫ y in (farRegion x)ᶜ,
            (gradientKernel j (x - y) - x k / Real.pi * hessianKernel 0 1 y) * W y| :=
        abs_add_le _ _
    _ ≤ 64 / (2 - α) * M * ‖x‖ ^ (1 + α) + (12 + 4 / α) * M * ‖x‖ ^ (1 + α) :=
        add_le_add (hfar.trans hfar') (hnear.trans hnear')
    _ = _ := by ring

/-- **The bound of the corrected integral for `α > 2`, `|x| ≤ 1`:** the same integral is at most
`(64/(α-2) + 32 + 3·2^α + 2^α/α) M |x|³` for `|f(y)| ≤ M min(|y|^α, |y|^(-β))`. -/
theorem abs_integral_sub_le_of_two_lt {α β M : ℝ} (hα : 2 < α) (hβ : 0 < β) (hM0 : 0 ≤ M)
    (hpow : ∀ y : ℝ^2, 0 < y 1 → |f y| ≤ M * ‖y‖ ^ α)
    (hdec : ∀ y : ℝ^2, 0 < y 1 → |f y| ≤ M * ‖y‖ ^ (-β)) (j k : Fin 2)
    (hker : ∀ x y : ℝ^2, y ≠ 0 → 2 * ‖x‖ ≤ ‖y‖ →
      |symmetrizedKernel (gradientKernel j) x y - 4 / Real.pi * x k * hessianKernel 0 1 y| ≤
        32 / Real.pi * ‖x‖ ^ 3 / ‖y‖ ^ 4) {x : ℝ^2} (hx1 : ‖x‖ ≤ 1) :
    |∫ y, (gradientKernel j (x - y) - x k / Real.pi * hessianKernel 0 1 y) *
        oddHalfSpaceExtension f y| ≤
      (64 / (α - 2) + 32 + 3 * 2 ^ α + 2 ^ α / α) * M * ‖x‖ ^ 3 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hα0 : 0 < α := by linarith
  have hα2 : 0 < α - 2 := by linarith
  have hnear := abs_setIntegral_compl_farRegion_le hf hc hα0 hM0 hpow j k x
  set W := oddHalfSpaceExtension f with hWdef
  rw [integral_sub_eq_farRegion_add hf hc hodd hα0 hM0 hpow j k x]
  set c := 32 * M * ‖x‖ ^ 3 / Real.pi with hcdef
  have hc0 : 0 ≤ c := by positivity
  -- the far region, split at `|y| = 1`
  have hfar := (integrableOn_and_abs_setIntegral_le_split (F := fun y ↦
      (symmetrizedKernel (gradientKernel j) x y - 4 * x k / Real.pi * hessianKernel 0 1 y) * W y)
    ((measurableSet_farRegion x).inter measurableSet_quadrant)
    ((((measurable_symmetrizedKernel_gradientKernel j x).sub
      (measurable_const.mul (measurable_hessianKernel 0 1))).aestronglyMeasurable).mul
        (integrable_oddHalfSpaceExtension hf hc).aestronglyMeasurable) hc0 hα2
    (by linarith : -1 - β < 1)
    (fun y hy ↦ by
      rw [show (α - 2) - 2 = α - 4 by ring]
      exact abs_correctedKernel_mul_le_rpow hy.1.2
        (hker x y (ne_zero_of_mem_quadrant hy.1.2) hy.1.1)
        (abs_oddHalfSpaceExtension_le_mul_rpow hM0 hpow y))
    (fun y hy ↦ by
      rw [show (-1 - β) - 3 = -β - 4 by ring]
      exact abs_correctedKernel_mul_le_rpow hy.1.2
        (hker x y (ne_zero_of_mem_quadrant hy.1.2) hy.1.1)
        (abs_oddHalfSpaceExtension_le_mul_rpow hM0 hdec y))).2
  have hT : c * (2 * Real.pi / (1 - (-1 - β))) ≤ c * Real.pi := by
    refine mul_le_mul_of_nonneg_left ?_ hc0
    rw [div_le_iff₀ (by linarith)]
    nlinarith [Real.pi_pos]
  have hnear' : (3 + 1 / α) * M * (2 * ‖x‖) ^ α * ‖x‖ ≤
      (3 * 2 ^ α + 2 ^ α / α) * M * ‖x‖ ^ 3 := by
    have h1 : ‖x‖ ^ α ≤ ‖x‖ ^ 2 := by
      rw [← Real.rpow_two]
      exact Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg _) hx1 (by norm_num) hα.le
    rw [Real.mul_rpow (by norm_num) (norm_nonneg _)]
    calc (3 + 1 / α) * M * (2 ^ α * ‖x‖ ^ α) * ‖x‖ ≤ (3 + 1 / α) * M * (2 ^ α * ‖x‖ ^ 2) * ‖x‖ := by
          gcongr
      _ = (3 * 2 ^ α + 2 ^ α / α) * M * ‖x‖ ^ 3 := by field_simp
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ c * (2 * Real.pi / (α - 2)) + c * Real.pi + (3 * 2 ^ α + 2 ^ α / α) * M * ‖x‖ ^ 3 :=
        add_le_add (hfar.trans (add_le_add le_rfl hT)) (hnear.trans hnear')
    _ = (64 / (α - 2) + 32 + 3 * 2 ^ α + 2 ^ α / α) * M * ‖x‖ ^ 3 := by
        rw [hcdef]; field_simp; ring

end Estimates

/-! ### The coefficient of `x₀ x₁` -/

/-- The coefficient `c_f = (4/π) ∫_{ℝ²₊₊} y₀ y₁ |y|⁻⁴ f(y) dy` of `x₀ x₁` in the expansion of the
half-plane Green potential of `f` at the origin: `∂₀∂₁φ(0)` in Chen and Hou, Part I, Lemma 6.5,
(6.23b), `mixedDeriv_greenPotential_zero`. It is `-c_ω(f)`, minus the strain functional of
Part I (5.67). -/
def mixedCoefficient (f : ℝ^2 → ℝ) : ℝ :=
  4 / Real.pi * ∫ y in quadrant, hessianKernel 0 1 y * f y

/-- The monomial `c x₀ x₁` has derivative `c (x₁ dy₀ + x₀ dy₁)`. -/
theorem hasFDerivAt_mixedMonomial (c : ℝ) (x : ℝ^2) :
    HasFDerivAt (fun y : ℝ^2 ↦ c * (y 0 * y 1))
      (c • (x 1 • (EuclideanSpace.proj 0 : ℝ^2 →L[ℝ] ℝ) + x 0 • EuclideanSpace.proj 1)) x := by
  have h0 : HasFDerivAt (fun y : ℝ^2 ↦ y 0) (EuclideanSpace.proj 0 : ℝ^2 →L[ℝ] ℝ) x :=
    (EuclideanSpace.proj (0 : Fin 2) : ℝ^2 →L[ℝ] ℝ).hasFDerivAt
  have h1 : HasFDerivAt (fun y : ℝ^2 ↦ y 1) (EuclideanSpace.proj 1 : ℝ^2 →L[ℝ] ℝ) x :=
    (EuclideanSpace.proj (1 : Fin 2) : ℝ^2 →L[ℝ] ℝ).hasFDerivAt
  convert (h0.mul h1).const_mul c using 2
  rw [add_comm]

/-- `∂₀(c x₀ x₁) = c x₁`. -/
theorem partialDeriv_zero_mixedMonomial (c : ℝ) (x : ℝ^2) :
    (∂[(0 : Fin 2)] (fun y : ℝ^2 ↦ c * (y 0 * y 1))) x = c * x 1 := by
  change fderiv ℝ _ x _ = _
  rw [(hasFDerivAt_mixedMonomial c x).fderiv]
  simp

/-- `∂₁(c x₀ x₁) = c x₀`. -/
theorem partialDeriv_one_mixedMonomial (c : ℝ) (x : ℝ^2) :
    (∂[(1 : Fin 2)] (fun y : ℝ^2 ↦ c * (y 0 * y 1))) x = c * x 0 := by
  change fderiv ℝ _ x _ = _
  rw [(hasFDerivAt_mixedMonomial c x).fderiv]
  simp

section Coefficient

variable {f : ℝ^2 → ℝ} (hf : Continuous f) (hc : HasCompactSupport f)
include hf hc

/-- The integrand of `c_f` is integrable on the quadrant when `|f(y)| ≤ M |y|^α`, `α > 0`. -/
theorem integrableOn_hessianKernel_mul_quadrant_of_le {α M : ℝ} (hα : 0 < α) (hM0 : 0 ≤ M)
    (hpow : ∀ y : ℝ^2, 0 < y 1 → |f y| ≤ M * ‖y‖ ^ α) :
    IntegrableOn (fun y ↦ hessianKernel 0 1 y * f y) quadrant := by
  refine ((integrable_hessianKernel_mul_oddHalfSpaceExtension_of_le hf hc hα hM0
    hpow).integrableOn).congr_fun (fun y hy ↦ ?_) measurableSet_quadrant
  simp only
  rw [oddHalfSpaceExtension_eqOn f (show y ∈ HalfSpace.upper 2 from hy.2)]

/-- `c_f = π⁻¹ ∫ K₁ W` over the plane, `W` the odd extension (the quadrant fold). -/
theorem mixedCoefficient_eq_integral (hodd : ∀ y : ℝ^2, 0 < y 1 → f (𝐑 0 y) = -f y)
    {α M : ℝ} (hα : 0 < α) (hM0 : 0 ≤ M) (hpow : ∀ y : ℝ^2, 0 < y 1 → |f y| ≤ M * ‖y‖ ^ α) :
    mixedCoefficient f =
      1 / Real.pi * ∫ y, hessianKernel 0 1 y * oddHalfSpaceExtension f y := by
  rw [integral_eq_four_mul_setIntegral_quadrant
    (integrable_hessianKernel_mul_oddHalfSpaceExtension_of_le hf hc hα hM0 hpow)
    (fun y ↦ by
      rw [hessianKernel_zero_one_coordinateReflection, oddHalfSpaceExtension_reflect_zero_neg hodd]
      ring)
    (fun y ↦ by
      rw [hessianKernel_zero_one_coordinateReflection, oddHalfSpaceExtension_reflect_one]; ring)]
  have : ∫ y in quadrant, hessianKernel 0 1 y * oddHalfSpaceExtension f y =
      ∫ y in quadrant, hessianKernel 0 1 y * f y :=
    setIntegral_congr_fun measurableSet_quadrant fun y hy ↦ by
      rw [oddHalfSpaceExtension_eqOn f (show y ∈ HalfSpace.upper 2 from hy.2)]
  rw [this, mixedCoefficient]
  ring

omit hc in
/-- `|c_f| ≤ 4 (1/α + 1/β) M` under the weighted bound of Lemma 6.5. -/
theorem abs_mixedCoefficient_le {α β M : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hM : ∀ y : ℝ^2, 0 < y 1 → |f y| * (‖y‖ ^ (-α) + ‖y‖ ^ β) ≤ M) :
    |mixedCoefficient f| ≤ 4 * (1 / α + 1 / β) * M := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hM0 := nonneg_of_weighted_le hM
  have h := (integrableOn_and_abs_setIntegral_le_split (F := fun y ↦ hessianKernel 0 1 y * f y)
    measurableSet_quadrant
    ((measurable_hessianKernel 0 1).aestronglyMeasurable.mul hf.aestronglyMeasurable)
    (by positivity : 0 ≤ M / 2) hα (by linarith : 1 - β < 1)
    (fun y hy ↦ abs_hessianKernel_mul_le hM0 (abs_le_mul_rpow_of_weighted_le hM hy.1.2))
    (fun y hy ↦ by
      rw [show (1 - β) - 3 = -β - 2 by ring]
      exact abs_hessianKernel_mul_le hM0 (abs_le_mul_rpow_neg_of_weighted_le hM hy.1.2))).2
  rw [mixedCoefficient, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 / Real.pi)]
  calc _ ≤ 4 / Real.pi * (M / 2 * (2 * Real.pi / α) + M / 2 * (2 * Real.pi / (1 - (1 - β)))) := by
        gcongr
    _ = 4 * (1 / α + 1 / β) * M := by rw [show 1 - (1 - β) = β by ring]; field_simp

end Coefficient


/-! ### Lemma 6.5 -/

section Lemma

/-- The weighted bound gives `|f(y)| ≤ M` on the open upper half-plane. -/
theorem abs_le_of_weighted_le {f : ℝ^2 → ℝ} {α β M : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hM : ∀ y : ℝ^2, 0 < y 1 → |f y| * (‖y‖ ^ (-α) + ‖y‖ ^ β) ≤ M) {y : ℝ^2} (hy : 0 < y 1) :
    |f y| ≤ M := by
  have h := abs_le_mul_min_rpow hM hy
  have hM0 := nonneg_of_weighted_le hM
  have hmin : min (‖y‖ ^ α) (‖y‖ ^ (-β)) ≤ 1 := by
    rcases le_total ‖y‖ 1 with h1 | h1
    · exact (min_le_left _ _).trans (Real.rpow_le_one (norm_nonneg _) h1 hα)
    · exact (min_le_right _ _).trans (Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith))
  calc |f y| ≤ M * min (‖y‖ ^ α) (‖y‖ ^ (-β)) := h
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left hmin hM0
    _ = M := mul_one M

/-- The gradient of `φ = G[f] - c x₀ x₁` in terms of the corrected kernel. -/
theorem partialDeriv_sub_mixedMonomial_eq {f : ℝ^2 → ℝ} (hf : Continuous f)
    (hc : HasCompactSupport f) (hodd : ∀ y : ℝ^2, 0 < y 1 → f (𝐑 0 y) = -f y) {α M : ℝ}
    (hα : 0 < α) (hM0 : 0 ≤ M) (hpow : ∀ y : ℝ^2, 0 < y 1 → |f y| ≤ M * ‖y‖ ^ α)
    (j k : Fin 2) (x : ℝ^2)
    (hmono : (∂[j] (fun y : ℝ^2 ↦ mixedCoefficient f * (y 0 * y 1))) x =
      mixedCoefficient f * x k) :
    (∂[j] (fun y ↦ halfSpaceGreenPotential f y - mixedCoefficient f * (y 0 * y 1))) x =
      ∫ y, (gradientKernel j (x - y) - x k / Real.pi * hessianKernel 0 1 y) *
        oddHalfSpaceExtension f y := by
  have hφ := (contDiff_one_halfSpaceGreenPotential hf hc).differentiable one_ne_zero
  rw [PDE.partialDeriv_sub (hφ x) (hasFDerivAt_mixedMonomial _ x).differentiableAt, hmono,
    partialDeriv_halfSpaceGreenPotential_eq_integral hf hc j x,
    mixedCoefficient_eq_integral hf hc hodd hα hM0 hpow]
  have hgint := integrable_gradientKernel_sub_mul_oddHalfSpaceExtension hf hc j x
  have hKint := integrable_hessianKernel_mul_oddHalfSpaceExtension_of_le hf hc hα hM0 hpow
  rw [show 1 / Real.pi * (∫ y, hessianKernel 0 1 y * oddHalfSpaceExtension f y) * x k =
    x k / Real.pi * ∫ y, hessianKernel 0 1 y * oddHalfSpaceExtension f y by ring,
    ← integral_const_mul, ← integral_sub hgint (hKint.const_mul _)]
  congr 1
  funext y
  ring

/-- The mean value bound from the origin: if `ψ(0) = 0` and `‖Dψ‖ ≤ B` on the closed disc of
radius `|x|`, then `|ψ(x)| ≤ B |x|`. -/
theorem abs_le_of_norm_fderiv_le {ψ : ℝ^2 → ℝ} (hψ : Differentiable ℝ ψ) (h0 : ψ 0 = 0)
    {B : ℝ} {x : ℝ^2} (hB : ∀ z ∈ closedBall (0 : ℝ^2) ‖x‖, ‖fderiv ℝ ψ z‖ ≤ B) :
    |ψ x| ≤ B * ‖x‖ := by
  have hx : x ∈ closedBall (0 : ℝ^2) ‖x‖ := by simp
  have h := (convex_closedBall (0 : ℝ^2) ‖x‖).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ ↦ hψ z) hB (mem_closedBall_self (norm_nonneg x)) hx
  rwa [h0, sub_zero, sub_zero, Real.norm_eq_abs] at h

/-- **Chen and Hou, Part I, Lemma 6.5, (6.23a).** Let `f` be continuous with compact support and
odd in `x₀` on the open upper half-plane, with `|f(y)| (|y|^(-α) + |y|^β) ≤ M` there, `α > 0`,
`0 < β < 1`. Its half-plane Green potential `φ` (the solution of `-Δφ = f` with `φ = 0` on the
boundary, (6.20)) satisfies `|∇φ(x)| ≤ C M min(|x|, |x|^(1-β))` on the plane, with `C` depending
only on `α` and `β`. -/
theorem exists_norm_fderiv_greenPotential_le {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hβ1 : β < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ℝ^2 → ℝ) (M : ℝ), Continuous f → HasCompactSupport f →
      (∀ y : ℝ^2, 0 < y 1 → f (𝐑 0 y) = -f y) →
      (∀ y : ℝ^2, 0 < y 1 → |f y| * (‖y‖ ^ (-α) + ‖y‖ ^ β) ≤ M) →
      ∀ x : ℝ^2, ‖fderiv ℝ (halfSpaceGreenPotential f) x‖ ≤
        C * M * min ‖x‖ (‖x‖ ^ (1 - β)) := by
  set C₀ := max (20 / α + 20 / β + 3) (20 / β + 9) with hC₀
  have hC₀0 : 0 ≤ C₀ := le_max_of_le_right (by positivity)
  refine ⟨2 * C₀, by positivity, fun f M hf hc hodd hM x ↦ ?_⟩
  have hM0 := nonneg_of_weighted_le hM
  have hpow := fun (y : ℝ^2) (hy : 0 < y 1) ↦ abs_le_mul_rpow_of_weighted_le hM hy
  have hdec := fun (y : ℝ^2) (hy : 0 < y 1) ↦ abs_le_mul_rpow_neg_of_weighted_le hM hy
  have hbdd := fun (y : ℝ^2) (hy : 0 < y 1) ↦ abs_le_of_weighted_le hα.le hβ.le hM hy
  have hpart (j k : Fin 2) (hker : ∀ x y : ℝ^2, y ≠ 0 → 2 * ‖x‖ ≤ ‖y‖ →
      |symmetrizedKernel (gradientKernel j) x y - 4 / Real.pi * x k * hessianKernel 0 1 y| ≤
        32 / Real.pi * ‖x‖ ^ 3 / ‖y‖ ^ 4) :
      |(∂[j] (halfSpaceGreenPotential f)) x| ≤ C₀ * M * min ‖x‖ (‖x‖ ^ (1 - β)) := by
    have h1 := abs_partialDeriv_le_mul_norm hf hc hodd hα hβ hM0 hpow hdec hbdd j k hker x
    have h2 : |(∂[j] (halfSpaceGreenPotential f)) x| ≤ (20 / β + 9) * M * ‖x‖ ^ (1 - β) := by
      rcases eq_or_ne x 0 with rfl | hx
      · simpa [Real.zero_rpow (by linarith : 1 - β ≠ 0)] using h1
      · exact abs_partialDeriv_le_mul_rpow hf hc hodd hβ hβ1 hM0 hdec j k hker hx
    rw [mul_min_of_nonneg _ _ (by positivity)]
    refine le_min (h1.trans ?_) (h2.trans ?_)
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hM0)
        (norm_nonneg _)
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hM0)
        (by positivity)
  calc ‖fderiv ℝ (halfSpaceGreenPotential f) x‖ ≤
        |(∂[(0 : Fin 2)] (halfSpaceGreenPotential f)) x| +
          |(∂[(1 : Fin 2)] (halfSpaceGreenPotential f)) x| :=
        (PDE.norm_fderiv_le_sum_norm_partialDeriv _ x).trans_eq (Fin.sum_univ_two _)
    _ ≤ C₀ * M * min ‖x‖ (‖x‖ ^ (1 - β)) + C₀ * M * min ‖x‖ (‖x‖ ^ (1 - β)) :=
        add_le_add
          (hpart 0 1 fun x y hy hxy ↦ abs_symmetrizedKernel_gradientKernel_zero_sub_le hy hxy)
          (hpart 1 0 fun x y hy hxy ↦ abs_symmetrizedKernel_gradientKernel_one_sub_le hy hxy)
    _ = 2 * C₀ * M * min ‖x‖ (‖x‖ ^ (1 - β)) := by ring

/-- The gradient bound behind (6.23b) under the pointwise bound `|f(y)| ≤ M |y|^α`,
`0 < α < 2`. -/
theorem norm_fderiv_greenPotential_sub_le_of_lt_two {f : ℝ^2 → ℝ} (hf : Continuous f)
    (hc : HasCompactSupport f) (hodd : ∀ y : ℝ^2, 0 < y 1 → f (𝐑 0 y) = -f y) {α M : ℝ}
    (hα : 0 < α) (hα2 : α < 2) (hM0 : 0 ≤ M) (hpow : ∀ y : ℝ^2, 0 < y 1 → |f y| ≤ M * ‖y‖ ^ α)
    (x : ℝ^2) :
    ‖fderiv ℝ (fun y ↦ halfSpaceGreenPotential f y - mixedCoefficient f * (y 0 * y 1)) x‖ ≤
      2 * (64 / (2 - α) + 12 + 4 / α) * M * ‖x‖ ^ (1 + α) := by
  refine (PDE.norm_fderiv_le_sum_norm_partialDeriv _ x).trans ?_
  simp only [Fin.sum_univ_two, Real.norm_eq_abs]
  rw [partialDeriv_sub_mixedMonomial_eq hf hc hodd hα hM0 hpow 0 1 x
      (partialDeriv_zero_mixedMonomial _ x),
    partialDeriv_sub_mixedMonomial_eq hf hc hodd hα hM0 hpow 1 0 x
      (partialDeriv_one_mixedMonomial _ x)]
  have h0 := abs_integral_sub_le_of_lt_two hf hc hodd hα hα2 hM0 hpow 0 1
    (fun x y hy hxy ↦ abs_symmetrizedKernel_gradientKernel_zero_sub_le hy hxy) x
  have h1 := abs_integral_sub_le_of_lt_two hf hc hodd hα hα2 hM0 hpow 1 0
    (fun x y hy hxy ↦ abs_symmetrizedKernel_gradientKernel_one_sub_le hy hxy) x
  linarith

/-- **Chen and Hou, Part I, Lemma 6.5, (6.23b).** Under the hypotheses of (6.23a) with
`0 < α < 2` and any real `β`, with `c_f = mixedCoefficient f`:
`|∇(φ - c_f x₀ x₁)(x)| ≤ C M |x|^(1+α)` and `|φ(x) - c_f x₀ x₁| ≤ C M |x|^(2+α)` on the plane,
`C` depending only on `α`. The coefficient `c_f` is `∂₀∂₁φ(0)`
(`mixedDeriv_greenPotential_zero`). -/
theorem exists_greenPotential_sub_mixed_le {α β : ℝ} (hα : 0 < α) (hα2 : α < 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ℝ^2 → ℝ) (M : ℝ), Continuous f → HasCompactSupport f →
      (∀ y : ℝ^2, 0 < y 1 → f (𝐑 0 y) = -f y) →
      (∀ y : ℝ^2, 0 < y 1 → |f y| * (‖y‖ ^ (-α) + ‖y‖ ^ β) ≤ M) → ∀ x : ℝ^2,
        ‖fderiv ℝ (fun y ↦ halfSpaceGreenPotential f y - mixedCoefficient f * (y 0 * y 1)) x‖ ≤
            C * M * ‖x‖ ^ (1 + α) ∧
          |halfSpaceGreenPotential f x - mixedCoefficient f * (x 0 * x 1)| ≤
            C * M * ‖x‖ ^ (2 + α) := by
  have h2α : 0 < 2 - α := by linarith
  refine ⟨2 * (64 / (2 - α) + 12 + 4 / α), by positivity, fun f M hf hc hodd hM x ↦ ?_⟩
  have hM0 := nonneg_of_weighted_le hM
  have hpow := fun (y : ℝ^2) (hy : 0 < y 1) ↦ abs_le_mul_rpow_of_weighted_le hM hy
  have hgrad := norm_fderiv_greenPotential_sub_le_of_lt_two hf hc hodd hα hα2 hM0 hpow
  refine ⟨hgrad x, ?_⟩
  have hψ : Differentiable ℝ
      (fun y ↦ halfSpaceGreenPotential f y - mixedCoefficient f * (y 0 * y 1)) :=
    ((contDiff_one_halfSpaceGreenPotential hf hc).differentiable one_ne_zero).sub
      fun y ↦ (hasFDerivAt_mixedMonomial _ y).differentiableAt
  have h0 : halfSpaceGreenPotential f 0 - mixedCoefficient f * ((0 : ℝ^2) 0 * (0 : ℝ^2) 1) = 0 := by
    rw [halfSpaceGreenPotential_boundary f (by simp [HalfSpace.boundary])]
    simp
  have h := abs_le_of_norm_fderiv_le hψ h0 (x := x)
    (B := 2 * (64 / (2 - α) + 12 + 4 / α) * M * ‖x‖ ^ (1 + α)) fun z hz ↦ by
      refine (hgrad z).trans ?_
      have hz' : ‖z‖ ≤ ‖x‖ := by simpa using hz
      gcongr
  refine h.trans (le_of_eq ?_)
  rw [mul_assoc, ← Real.rpow_add_one' (norm_nonneg x) (by linarith)]
  ring_nf


/-- **Chen and Hou, Part I, Lemma 6.5, (6.23c).** Under the hypotheses of (6.23a) with `α > 2`
and `β > 0`: `|∇(φ - c_f x₀ x₁)(x)| ≤ C M |x|³` and `|φ(x) - c_f x₀ x₁| ≤ C M |x|⁴` on the plane,
`C` depending only on `α` and `β`. -/
theorem exists_greenPotential_sub_mixed_le_of_two_lt {α β : ℝ} (hα : 2 < α) (hβ : 0 < β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ℝ^2 → ℝ) (M : ℝ), Continuous f → HasCompactSupport f →
      (∀ y : ℝ^2, 0 < y 1 → f (𝐑 0 y) = -f y) →
      (∀ y : ℝ^2, 0 < y 1 → |f y| * (‖y‖ ^ (-α) + ‖y‖ ^ β) ≤ M) → ∀ x : ℝ^2,
        ‖fderiv ℝ (fun y ↦ halfSpaceGreenPotential f y - mixedCoefficient f * (y 0 * y 1)) x‖ ≤
            C * M * ‖x‖ ^ 3 ∧
          |halfSpaceGreenPotential f x - mixedCoefficient f * (x 0 * x 1)| ≤ C * M * ‖x‖ ^ 4 := by
  have hα0 : 0 < α := by linarith
  have hα2 : 0 < α - 2 := by linarith
  set C₀ := max (64 / (α - 2) + 32 + 3 * 2 ^ α + 2 ^ α / α)
    (20 / α + 20 / β + 3 + 4 * (1 / α + 1 / β)) with hC₀
  have hC₀0 : 0 ≤ C₀ := le_max_of_le_right (by positivity)
  refine ⟨2 * C₀, by positivity, fun f M hf hc hodd hM ↦ ?_⟩
  have hM0 := nonneg_of_weighted_le hM
  have hpow := fun (y : ℝ^2) (hy : 0 < y 1) ↦ abs_le_mul_rpow_of_weighted_le hM hy
  have hdec := fun (y : ℝ^2) (hy : 0 < y 1) ↦ abs_le_mul_rpow_neg_of_weighted_le hM hy
  have hbdd := fun (y : ℝ^2) (hy : 0 < y 1) ↦ abs_le_of_weighted_le hα0.le hβ.le hM hy
  have hcoef := abs_mixedCoefficient_le hf hα0 hβ hM
  have hφ := (contDiff_one_halfSpaceGreenPotential hf hc).differentiable one_ne_zero
  have hpart (j k : Fin 2) (hker : ∀ x y : ℝ^2, y ≠ 0 → 2 * ‖x‖ ≤ ‖y‖ →
      |symmetrizedKernel (gradientKernel j) x y - 4 / Real.pi * x k * hessianKernel 0 1 y| ≤
        32 / Real.pi * ‖x‖ ^ 3 / ‖y‖ ^ 4) (x : ℝ^2)
      (hmono : (∂[j] (fun y : ℝ^2 ↦ mixedCoefficient f * (y 0 * y 1))) x =
        mixedCoefficient f * x k) :
      |(∂[j] (fun y ↦ halfSpaceGreenPotential f y - mixedCoefficient f * (y 0 * y 1))) x| ≤
        C₀ * M * ‖x‖ ^ 3 := by
    rcases le_or_gt ‖x‖ 1 with hx1 | hx1
    · rw [partialDeriv_sub_mixedMonomial_eq hf hc hodd hα0 hM0 hpow j k x hmono]
      refine (abs_integral_sub_le_of_two_lt hf hc hodd hα hβ hM0 hpow hdec j k hker hx1).trans ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hM0)
        (by positivity)
    · rw [PDE.partialDeriv_sub (hφ x) (hasFDerivAt_mixedMonomial _ x).differentiableAt, hmono]
      have h1 := abs_partialDeriv_le_mul_norm hf hc hodd hα0 hβ hM0 hpow hdec hbdd j k hker x
      have hxk : |x k| ≤ ‖x‖ := by simpa using PiLp.norm_apply_le x k
      have h3 : ‖x‖ ≤ ‖x‖ ^ 3 := le_self_pow₀ hx1.le (by norm_num)
      calc |(∂[j] (halfSpaceGreenPotential f)) x - mixedCoefficient f * x k|
          ≤ |(∂[j] (halfSpaceGreenPotential f)) x| + |mixedCoefficient f| * |x k| := by
            rw [← abs_mul]; exact abs_sub _ _
        _ ≤ (20 / α + 20 / β + 3) * M * ‖x‖ + 4 * (1 / α + 1 / β) * M * ‖x‖ :=
            add_le_add h1 (mul_le_mul hcoef hxk (abs_nonneg _) (by positivity))
        _ = (20 / α + 20 / β + 3 + 4 * (1 / α + 1 / β)) * M * ‖x‖ := by ring
        _ ≤ C₀ * M * ‖x‖ ^ 3 := by gcongr; exact le_max_right _ _
  have hgrad : ∀ x : ℝ^2,
      ‖fderiv ℝ (fun y ↦ halfSpaceGreenPotential f y - mixedCoefficient f * (y 0 * y 1)) x‖ ≤
        2 * C₀ * M * ‖x‖ ^ 3 := fun x ↦ by
    refine (PDE.norm_fderiv_le_sum_norm_partialDeriv _ x).trans ?_
    simp only [Fin.sum_univ_two, Real.norm_eq_abs]
    have h0 := hpart 0 1 (fun x y hy hxy ↦ abs_symmetrizedKernel_gradientKernel_zero_sub_le hy hxy)
      x (partialDeriv_zero_mixedMonomial _ x)
    have h1 := hpart 1 0 (fun x y hy hxy ↦ abs_symmetrizedKernel_gradientKernel_one_sub_le hy hxy)
      x (partialDeriv_one_mixedMonomial _ x)
    linarith
  intro x
  refine ⟨hgrad x, ?_⟩
  have hψ : Differentiable ℝ
      (fun y ↦ halfSpaceGreenPotential f y - mixedCoefficient f * (y 0 * y 1)) :=
    hφ.sub fun y ↦ (hasFDerivAt_mixedMonomial _ y).differentiableAt
  have h0 : halfSpaceGreenPotential f 0 - mixedCoefficient f * ((0 : ℝ^2) 0 * (0 : ℝ^2) 1) = 0 := by
    rw [halfSpaceGreenPotential_boundary f (by simp [HalfSpace.boundary])]
    simp
  have h := abs_le_of_norm_fderiv_le hψ h0 (x := x) (B := 2 * C₀ * M * ‖x‖ ^ 3) fun z hz ↦ by
    refine (hgrad z).trans ?_
    have hz' : ‖z‖ ≤ ‖x‖ := by simpa using hz
    gcongr
  refine h.trans (le_of_eq ?_)
  ring

/-- The linear map `v ↦ c (v₁ dy₀ + v₀ dy₁)`, the second derivative of `c x₀ x₁`. -/
def mixedHessian (c : ℝ) : ℝ^2 →L[ℝ] ℝ^2 →L[ℝ] ℝ :=
  (EuclideanSpace.proj 1 : ℝ^2 →L[ℝ] ℝ).smulRight (c • (EuclideanSpace.proj 0 : ℝ^2 →L[ℝ] ℝ)) +
    (EuclideanSpace.proj 0 : ℝ^2 →L[ℝ] ℝ).smulRight (c • (EuclideanSpace.proj 1 : ℝ^2 →L[ℝ] ℝ))

/-- `mixedHessian c v w = c (v₁ w₀ + v₀ w₁)`. -/
theorem mixedHessian_apply_apply (c : ℝ) (v w : ℝ^2) :
    mixedHessian c v w = c * (v 1 * w 0 + v 0 * w 1) := by
  simp [mixedHessian]
  ring

/-- `mixedHessian c v` is the derivative of `c x₀ x₁` at `v`. -/
theorem mixedHessian_apply (c : ℝ) (v : ℝ^2) :
    mixedHessian c v = c • (v 1 • (EuclideanSpace.proj 0 : ℝ^2 →L[ℝ] ℝ) +
      v 0 • EuclideanSpace.proj 1) := by
  ext w
  rw [mixedHessian_apply_apply]
  simp
  ring

/-- **The coefficient is the mixed derivative at the origin.** Under the hypotheses of (6.23a)
with `α > 0`, `β > 0`, the derivative of `∇φ` at the origin exists and is the Hessian of
`c_f x₀ x₁`: the remainder bound (6.23b) at the exponent `min α 1` makes it `o(|x|)`. -/
theorem hasFDerivAt_fderiv_greenPotential_zero {f : ℝ^2 → ℝ} (hf : Continuous f)
    (hc : HasCompactSupport f) (hodd : ∀ y : ℝ^2, 0 < y 1 → f (𝐑 0 y) = -f y) {α β M : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hM : ∀ y : ℝ^2, 0 < y 1 → |f y| * (‖y‖ ^ (-α) + ‖y‖ ^ β) ≤ M) :
    HasFDerivAt (fderiv ℝ (halfSpaceGreenPotential f)) (mixedHessian (mixedCoefficient f)) 0 := by
  set a := min α 1 with ha
  have ha0 : 0 < a := lt_min hα one_pos
  have ha2 : a < 2 := (min_le_right _ _).trans_lt (by norm_num)
  have hM0 := nonneg_of_weighted_le hM
  have hpow : ∀ y : ℝ^2, 0 < y 1 → |f y| ≤ M * ‖y‖ ^ a := fun y hy ↦ by
    rcases le_total ‖y‖ 1 with h1 | h1
    · exact (abs_le_mul_rpow_of_weighted_le hM hy).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg _) h1 ha0.le (min_le_left _ _)) hM0)
    · calc |f y| ≤ M * ‖y‖ ^ (-β) := abs_le_mul_rpow_neg_of_weighted_le hM hy
        _ ≤ M * 1 := mul_le_mul_of_nonneg_left
          (Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)) hM0
        _ ≤ M * ‖y‖ ^ a := mul_le_mul_of_nonneg_left (Real.one_le_rpow h1 ha0.le) hM0
  set K := 2 * (64 / (2 - a) + 12 + 4 / a) * M with hK
  have hgrad := norm_fderiv_greenPotential_sub_le_of_lt_two hf hc hodd ha0 ha2 hM0 hpow
  have hφ := (contDiff_one_halfSpaceGreenPotential hf hc).differentiable one_ne_zero
  have heq : ∀ z : ℝ^2, fderiv ℝ (halfSpaceGreenPotential f) z =
      fderiv ℝ (fun y ↦ halfSpaceGreenPotential f y - mixedCoefficient f * (y 0 * y 1)) z +
        mixedHessian (mixedCoefficient f) z := fun z ↦ by
    rw [fderiv_fun_sub (hφ z) (hasFDerivAt_mixedMonomial _ z).differentiableAt,
      (hasFDerivAt_mixedMonomial _ z).fderiv, mixedHessian_apply]
    abel
  have hzero : fderiv ℝ (fun y ↦ halfSpaceGreenPotential f y -
      mixedCoefficient f * (y 0 * y 1)) 0 = 0 := by
    have h := hgrad 0
    rw [norm_zero, Real.zero_rpow (by linarith), mul_zero] at h
    exact norm_le_zero_iff.mp h
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have hsimp : (fun h : ℝ^2 ↦ fderiv ℝ (halfSpaceGreenPotential f) (0 + h) -
      fderiv ℝ (halfSpaceGreenPotential f) 0 - mixedHessian (mixedCoefficient f) h) =
      fun h ↦ fderiv ℝ (fun y ↦ halfSpaceGreenPotential f y -
        mixedCoefficient f * (y 0 * y 1)) h := by
    funext h
    rw [zero_add, heq h, heq 0, hzero, map_zero]
    abel
  rw [hsimp, Asymptotics.isLittleO_iff]
  intro ε hε
  have hcont : Continuous fun h : ℝ^2 ↦ K * ‖h‖ ^ a :=
    continuous_const.mul (continuous_norm.rpow_const fun _ ↦ Or.inr ha0.le)
  have hlim : Filter.Tendsto (fun h : ℝ^2 ↦ K * ‖h‖ ^ a) (𝓝 0) (𝓝 0) := by
    have := hcont.tendsto 0
    rwa [norm_zero, Real.zero_rpow ha0.ne', mul_zero] at this
  filter_upwards [hlim.eventually (Iic_mem_nhds hε)] with h hh
  have hh' : K * ‖h‖ ^ a ≤ ε := hh
  calc ‖fderiv ℝ (fun y ↦ halfSpaceGreenPotential f y - mixedCoefficient f * (y 0 * y 1)) h‖
      ≤ K * ‖h‖ ^ (1 + a) := hgrad h
    _ = K * ‖h‖ ^ a * ‖h‖ := by
        rw [Real.rpow_add' (norm_nonneg _) (by linarith), Real.rpow_one]; ring
    _ ≤ ε * ‖h‖ := mul_le_mul_of_nonneg_right hh' (norm_nonneg _)

/-- **`c_f = ∂₀∂₁φ(0) = ∂₁∂₀φ(0)`** for the half-plane Green potential `φ` of `f`, under the
hypotheses of (6.23a) with `α > 0`, `β > 0`. -/
theorem mixedDeriv_greenPotential_zero {f : ℝ^2 → ℝ} (hf : Continuous f)
    (hc : HasCompactSupport f) (hodd : ∀ y : ℝ^2, 0 < y 1 → f (𝐑 0 y) = -f y) {α β M : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hM : ∀ y : ℝ^2, 0 < y 1 → |f y| * (‖y‖ ^ (-α) + ‖y‖ ^ β) ≤ M) :
    (∂[(0 : Fin 2)] (∂[(1 : Fin 2)] (halfSpaceGreenPotential f))) 0 = mixedCoefficient f ∧
      (∂[(1 : Fin 2)] (∂[(0 : Fin 2)] (halfSpaceGreenPotential f))) 0 = mixedCoefficient f := by
  have hL := hasFDerivAt_fderiv_greenPotential_zero hf hc hodd hα hβ hM
  have h1 := hL.clm_apply (hasFDerivAt_const (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) 0)
  have h0 := hL.clm_apply (hasFDerivAt_const (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) 0)
  constructor
  · change fderiv ℝ (fun x ↦ fderiv ℝ (halfSpaceGreenPotential f) x
      (EuclideanSpace.single 1 1)) 0 (EuclideanSpace.single 0 1) = _
    rw [h1.fderiv]
    simp [mixedHessian_apply_apply]
  · change fderiv ℝ (fun x ↦ fderiv ℝ (halfSpaceGreenPotential f) x
      (EuclideanSpace.single 0 1)) 0 (EuclideanSpace.single 1 1) = _
    rw [h0.fderiv]
    simp [mixedHessian_apply_apply]

end Lemma

end IncompressibleFlow
