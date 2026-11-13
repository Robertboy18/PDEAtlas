/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.FundamentalSolution.PlanarSingularKernel
public import PDE.Analysis.MeasureTheory.Integral.PlanarRadialPower

/-!
# Hölder estimates of planar singular integrals

For a planar singular kernel `K` with constant `A` (`IsSingularKernel`) and an integrable
density `f` that is Hölder continuous on the whole plane,
`|f(y) - f(z)| ≤ M |y - z|^α` with `0 < α < 1`, the singular integral

`T f(x) = ∫_{|x-y|<1} K(x - y) (f(y) - f(x)) dy + ∫_{|x-y|≥1} K(x - y) f(y) dy`

is absolutely convergent, its radius `1` may be replaced by any `r > 0`, it is Hölder continuous
with exponent `α`, and it is bounded. For the Hessian kernels `T f(x)` is the disc-truncated
principal value.

The Hölder estimate is the classical one (Gilbarg and Trudinger, Chapter 4): with
`δ = |x - x'|` and `N = B(x, 2δ)`, the near parts are bounded by `∫_N |x - y|^(α-2)`, the far
part by the smoothness of `K` and `∫_{|x-y|≥2δ} δ |x - y|^(α-3)`, and the two constants
`f(x')∫ K` that appear cancel because
`∫_{|x-y|≥2δ} (K(x - y) - K(x' - y)) dy = P.V.∫_N K(x' - y) dy`.

## Main definitions

* `singularIntegral`: `T f(x)`, the singular integral truncated at radius `1`.

## Main results

* `singularIntegral_eq`: the radius `1` may be replaced by any `r > 0`.
* `integral_compl_ball_sub`: with `δ = |x - x'| > 0`,
  `∫_{|x-y|≥2δ} (K(x - y) - K(x' - y)) dy = ∫_{B(x,2δ) \ B(x',δ)} K(x' - y) dy`.
* `abs_singularIntegral_sub_le`: `|T f(x) - T f(x')| ≤ 10π/(α(1-α)) · A M |x - x'|^α`.
* `abs_singularIntegral_le`: `|T f(x)| ≤ A (2πM/α + ‖f‖₁)`.
* `abs_singularIntegral_le_log`: `|T f(x)| ≤ (2πA/α)(1 + B log(2 + M)) + A ‖f‖₁` when `|f| ≤ B`.
* `singularIntegral_sub`: `T` is linear on Hölder integrable densities.
* `hasPrincipalValueAt_singularIntegral`: for the Hessian kernels `T f(x)` is the disc-truncated
  principal value.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Classics in Mathematics, Springer, 2001, Chapter 4 (Poisson's Equation and the Newtonian
  Potential), pp. 51-72.
  <https://doi.org/10.1007/978-3-642-61798-0_4>
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology

namespace PotentialTheory.Planar

/-- The singular integral `∫_{|x-y|<1} K(x - y) (f(y) - f(x)) dy + ∫_{|x-y|≥1} K(x - y) f(y) dy`.
For a singular kernel and a Hölder density the radius `1` can be replaced by any `r > 0`
(`IsSingularKernel.singularIntegral_eq`). -/
def singularIntegral (K f : ℝ^2 → ℝ) (x : ℝ^2) : ℝ :=
  (∫ y in ball x 1, K (x - y) * (f y - f x)) + ∫ y in (ball x 1)ᶜ, K (x - y) * f y

section Helpers

/-- A measurable function dominated on `S` by `g` with `∫⁻_S g < ∞` is integrable on `S`. -/
theorem integrableOn_of_norm_le_of_lintegral_ne_top {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {S : Set X} {F g : X → ℝ}
    (hS : MeasurableSet S) (hF : AEStronglyMeasurable F (μ.restrict S))
    (hle : ∀ y ∈ S, ‖F y‖ ≤ g y) (hg : ∫⁻ y in S, ENNReal.ofReal (g y) ∂μ ≠ ⊤) :
    IntegrableOn F S μ := by
  refine ⟨hF, ?_⟩
  refine lt_of_le_of_lt (lintegral_mono_ae ?_) hg.lt_top
  filter_upwards [ae_restrict_mem hS] with y hy
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (hle y hy)

/-- A function dominated on `S` by `g` has integral at most `∫⁻_S g`. -/
theorem norm_setIntegral_le_of_norm_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {S : Set X} {F g : X → ℝ}
    (hS : MeasurableSet S) (hle : ∀ y ∈ S, ‖F y‖ ≤ g y)
    (hg : ∫⁻ y in S, ENNReal.ofReal (g y) ∂μ ≠ ⊤) :
    ‖∫ y in S, F y ∂μ‖ ≤ (∫⁻ y in S, ENNReal.ofReal (g y) ∂μ).toReal := by
  refine (norm_integral_le_lintegral_norm _).trans ?_
  refine ENNReal.toReal_mono hg (lintegral_mono_ae ?_)
  filter_upwards [ae_restrict_mem hS] with y hy
  exact ENNReal.ofReal_le_ofReal (hle y hy)

/-- A Hölder bound with a nonzero difference forces a nonnegative constant. -/
theorem nonneg_of_holder {f : ℝ^2 → ℝ} {M α : ℝ}
    (hM : ∀ y z, |f y - f z| ≤ M * ‖y - z‖ ^ α) : 0 ≤ M := by
  have h := hM !₂[1, 0] 0
  rw [sub_zero, ← Real.sqrt_sq (norm_nonneg _), norm_sq_vec] at h
  norm_num at h
  exact (abs_nonneg _).trans h

/-- Points outside `B(x, ρ)` are at distance at least `ρ` from `x`. -/
theorem le_norm_sub_of_mem_compl_ball {x y : ℝ^2} {ρ : ℝ} (hy : y ∈ (ball x ρ)ᶜ) :
    ρ ≤ ‖x - y‖ := by
  simpa [dist_eq_norm, norm_sub_rev y x] using hy

/-- The arithmetic of the three pieces of the Hölder estimate. -/
theorem holder_constant_le {δ α : ℝ} (hδ : 0 < δ) (hα : 0 < α) (hα1 : α < 1) :
    2 * Real.pi * (2 * δ) ^ α / α + 2 * Real.pi * (3 * δ) ^ α / α +
        3 / 2 * δ * (2 * Real.pi * (2 * δ) ^ (α - 1) / (1 - α)) ≤
      10 * Real.pi / (α * (1 - α)) * δ ^ α := by
  have h1α : 0 < 1 - α := by linarith
  have e2 : (2 * δ) ^ α = 2 ^ α * δ ^ α := Real.mul_rpow (by norm_num) hδ.le
  have e3 : (3 * δ) ^ α = 3 ^ α * δ ^ α := Real.mul_rpow (by norm_num) hδ.le
  have e2' : (2 * δ) ^ (α - 1) = 2 ^ (α - 1) * δ ^ (α - 1) := Real.mul_rpow (by norm_num) hδ.le
  have eδ : δ * δ ^ (α - 1) = δ ^ α := by
    rw [show α = 1 + (α - 1) by ring, Real.rpow_add hδ, Real.rpow_one]
    ring_nf
  have b2 : (2 : ℝ) ^ α ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hα1.le
  have b3 : (3 : ℝ) ^ α ≤ 3 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hα1.le
  have b2' : (2 : ℝ) ^ (α - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have ht : 0 < δ ^ α := Real.rpow_pos_of_pos hδ α
  set t := δ ^ α
  have hpi := Real.pi_pos
  calc 2 * Real.pi * (2 * δ) ^ α / α + 2 * Real.pi * (3 * δ) ^ α / α +
        3 / 2 * δ * (2 * Real.pi * (2 * δ) ^ (α - 1) / (1 - α))
      = t * (2 * Real.pi * 2 ^ α / α + 2 * Real.pi * 3 ^ α / α +
          3 * Real.pi * 2 ^ (α - 1) / (1 - α)) := by
        rw [e2, e3, e2', show 3 / 2 * δ * (2 * Real.pi * (2 ^ (α - 1) * δ ^ (α - 1)) / (1 - α)) =
          3 * Real.pi * 2 ^ (α - 1) * (δ * δ ^ (α - 1)) / (1 - α) by ring, eδ]
        ring
    _ ≤ t * (2 * Real.pi * 2 / α + 2 * Real.pi * 3 / α + 3 * Real.pi * 1 / (1 - α)) := by
        gcongr
    _ ≤ t * (10 * Real.pi / (α * (1 - α))) := by
        gcongr
        rw [div_add_div _ _ hα.ne' hα.ne', div_add_div _ _ (by positivity) h1α.ne',
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_pos hα h1α, mul_pos (mul_pos hα h1α) hpi]
    _ = 10 * Real.pi / (α * (1 - α)) * t := by ring

end Helpers

variable {K : ℝ^2 → ℝ} {A : ℝ} {f : ℝ^2 → ℝ} {M α : ℝ}

namespace IsSingularKernel

variable (hK : IsSingularKernel K A)
include hK

/-- The near integrand is bounded by `A M |x - y|^(α-2)`. -/
theorem norm_mul_sub_le (hM : ∀ y z, |f y - f z| ≤ M * ‖y - z‖ ^ α) (x y : ℝ^2) :
    ‖K (x - y) * (f y - f x)‖ ≤ A * M * ‖x - y‖ ^ (α - 2) := by
  have hA := hK.nonneg
  have hM0 := nonneg_of_holder hM
  rcases eq_or_ne x y with rfl | hxy
  · simp only [sub_self, mul_zero, norm_zero]
    positivity
  have hn : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  calc |K (x - y)| * |f y - f x| ≤ A / ‖x - y‖ ^ 2 * (M * ‖x - y‖ ^ α) := by
        gcongr
        · exact hK.abs_le _
        · rw [← norm_neg (x - y), neg_sub]; exact hM y x
    _ = A * M * ‖x - y‖ ^ (α - 2) := by
        rw [Real.rpow_sub hn, Real.rpow_two]; ring

/-- The near integrand is integrable on every measurable set inside a disc around `x`, with
`∫_S |K(x - y)| |f(y) - f(x)| dy ≤ A M · 2πr^α/α`. -/
theorem integrableOn_mul_sub (hα : 0 < α) (hf : AEStronglyMeasurable f)
    (hM : ∀ y z, |f y - f z| ≤ M * ‖y - z‖ ^ α) (x : ℝ^2) {S : Set (ℝ^2)}
    (hS : MeasurableSet S) {r : ℝ} (hr : 0 ≤ r) (hSr : S ⊆ ball x r) :
    IntegrableOn (fun y ↦ K (x - y) * (f y - f x)) S := by
  have hA := hK.nonneg
  have hM0 := nonneg_of_holder hM
  refine integrableOn_of_norm_le_of_lintegral_ne_top hS
    (((hK.measurable.comp (measurable_const.sub measurable_id)).aestronglyMeasurable.mul
      (hf.sub aestronglyMeasurable_const)).restrict)
    (fun y _ ↦ hK.norm_mul_sub_le hM x y) ?_
  refine ne_top_of_le_ne_top ?_ (lintegral_mono_set hSr)
  rw [lintegral_ball_mul_rpow_sub_two x (by positivity) hr hα]
  exact ENNReal.ofReal_ne_top

/-- The near part is at most `A M · 2πr^α/α` on every measurable set inside `B(x, r)`. -/
theorem abs_setIntegral_mul_sub_le (hα : 0 < α) (hM : ∀ y z, |f y - f z| ≤ M * ‖y - z‖ ^ α)
    (x : ℝ^2) {S : Set (ℝ^2)} (hS : MeasurableSet S) {r : ℝ} (hr : 0 ≤ r)
    (hSr : S ⊆ ball x r) :
    |∫ y in S, K (x - y) * (f y - f x)| ≤ A * M * (2 * Real.pi * r ^ α / α) := by
  have hA := hK.nonneg
  have hM0 := nonneg_of_holder hM
  have hball := lintegral_ball_mul_rpow_sub_two x (mul_nonneg hA hM0) hr hα
  have hfin : ∫⁻ y in S, ENNReal.ofReal (A * M * ‖x - y‖ ^ (α - 2)) ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [hball]; exact ENNReal.ofReal_ne_top) (lintegral_mono_set hSr)
  rw [← Real.norm_eq_abs]
  refine (norm_setIntegral_le_of_norm_le hS (fun y _ ↦ hK.norm_mul_sub_le hM x y) hfin).trans ?_
  rw [← ENNReal.toReal_ofReal (by positivity : 0 ≤ A * M * (2 * Real.pi * r ^ α / α)), ← hball]
  exact ENNReal.toReal_mono (by rw [hball]; exact ENNReal.ofReal_ne_top) (lintegral_mono_set hSr)

/-- Away from `x` the kernel is bounded, so `K(x - ·) f` is integrable for integrable `f`. -/
theorem integrableOn_mul_of_le (hf : Integrable f) (x : ℝ^2) {S : Set (ℝ^2)}
    (hS : MeasurableSet S) {r : ℝ} (hr : 0 < r) (hSr : ∀ y ∈ S, r ≤ ‖x - y‖) :
    IntegrableOn (fun y ↦ K (x - y) * f y) S := by
  refine Integrable.bdd_mul (c := A / r ^ 2) hf.integrableOn
    (hK.measurable.comp (measurable_const.sub measurable_id)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem hS] with y hy
  rw [Real.norm_eq_abs]
  exact hK.abs_le_of_le hr (hSr y hy)

/-- The far integrand is integrable outside every disc of positive radius around `x`. -/
theorem integrableOn_compl_ball (hf : Integrable f) (x : ℝ^2) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun y ↦ K (x - y) * f y) (ball x r)ᶜ :=
  hK.integrableOn_mul_of_le hf x measurableSet_ball.compl hr fun y hy ↦ by
    simpa [dist_eq_norm, norm_sub_rev y x] using hy

/-- The far part outside `B(x, r)` is at most `A ‖f‖₁ / r²`. -/
theorem abs_setIntegral_mul_le (hf : Integrable f) (x : ℝ^2) {S : Set (ℝ^2)}
    (hS : MeasurableSet S) {r : ℝ} (hr : 0 < r) (hSr : ∀ y ∈ S, r ≤ ‖x - y‖) :
    |∫ y in S, K (x - y) * f y| ≤ A / r ^ 2 * ∫ y, |f y| := by
  have hA := hK.nonneg
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans ?_
  calc ∫ y in S, ‖K (x - y) * f y‖ ≤ ∫ y in S, A / r ^ 2 * |f y| := by
        refine setIntegral_mono_on (hK.integrableOn_mul_of_le hf x hS hr hSr).norm
          (hf.abs.const_mul _).integrableOn hS fun y hy ↦ ?_
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hK.abs_le_of_le hr (hSr y hy)) (abs_nonneg _)
    _ ≤ ∫ y, A / r ^ 2 * |f y| :=
        setIntegral_le_integral (hf.abs.const_mul _) (Eventually.of_forall fun y ↦ by positivity)
    _ = A / r ^ 2 * ∫ y, |f y| := integral_const_mul _ _

/-- The disc complement splits at a larger radius. -/
theorem setIntegral_compl_ball_eq (hf : Integrable f) (x : ℝ^2) {r R : ℝ} (hr : 0 < r)
    (hrR : r ≤ R) :
    ∫ y in (ball x r)ᶜ, K (x - y) * f y =
      (∫ y in ball x R \ ball x r, K (x - y) * f y) + ∫ y in (ball x R)ᶜ, K (x - y) * f y := by
  have hsub : ball x r ⊆ ball x R := ball_subset_ball hrR
  have hann : MeasurableSet (ball x R \ ball x r) := measurableSet_ball.diff measurableSet_ball
  have hset : (ball x r)ᶜ = (ball x R \ ball x r) ∪ (ball x R)ᶜ := by
    ext y
    by_cases h : y ∈ ball x R
    · simp [h]
    · exact iff_of_true (fun h' ↦ h (hsub h')) (Or.inr h)
  rw [hset, setIntegral_union (Set.disjoint_left.mpr fun y (hy : y ∈ ball x R \ ball x r)
    (hy' : y ∈ (ball x R)ᶜ) ↦ hy' hy.1) measurableSet_ball.compl
    (hK.integrableOn_mul_of_le hf x hann hr fun y hy ↦ by
      simpa [dist_eq_norm, norm_sub_rev y x] using hy.2)
    (hK.integrableOn_compl_ball hf x (hr.trans_le hrR))]

/-- **Independence of the radius.** For a Hölder integrable density the singular integral
equals `∫_{B(x,r)} K(x - y)(f(y) - f(x)) dy + ∫_{|x-y|≥r} K(x - y) f(y) dy` for every `r > 0`. -/
theorem singularIntegral_eq (hα : 0 < α) (hf : Integrable f)
    (hM : ∀ y z, |f y - f z| ≤ M * ‖y - z‖ ^ α) (x : ℝ^2) {r : ℝ} (hr : 0 < r) :
    singularIntegral K f x =
      (∫ y in ball x r, K (x - y) * (f y - f x)) + ∫ y in (ball x r)ᶜ, K (x - y) * f y := by
  -- the expression at radius `s` does not change between `r ≤ R`
  have key : ∀ r R : ℝ, 0 < r → r ≤ R →
      (∫ y in ball x R, K (x - y) * (f y - f x)) + ∫ y in (ball x R)ᶜ, K (x - y) * f y =
        (∫ y in ball x r, K (x - y) * (f y - f x)) + ∫ y in (ball x r)ᶜ, K (x - y) * f y := by
    intro r R hr hrR
    have hsub : ball x r ⊆ ball x R := ball_subset_ball hrR
    have hann : MeasurableSet (ball x R \ ball x r) := measurableSet_ball.diff measurableSet_ball
    have hannr : ∀ y ∈ ball x R \ ball x r, r ≤ ‖x - y‖ := fun y hy ↦ by
      simpa [dist_eq_norm, norm_sub_rev y x] using hy.2
    have hg : ∀ S, MeasurableSet S → S ⊆ ball x R →
        IntegrableOn (fun y ↦ K (x - y) * (f y - f x)) S := fun S hS hSR ↦
      hK.integrableOn_mul_sub hα hf.aestronglyMeasurable hM x hS (by linarith) hSR
    have hk : IntegrableOn (fun y ↦ K (x - y) * f y) (ball x R \ ball x r) :=
      hK.integrableOn_mul_of_le hf x hann hr hannr
    have hK1 : IntegrableOn (fun y ↦ K (x - y)) (ball x R \ ball x r) :=
      hK.integrableOn_of_le x hann ((measure_mono sdiff_subset).trans_lt measure_ball_lt_top).ne
        hr hannr
    have h1 : ∫ y in ball x R, K (x - y) * (f y - f x) =
        (∫ y in ball x r, K (x - y) * (f y - f x)) +
          ∫ y in ball x R \ ball x r, K (x - y) * (f y - f x) := by
      rw [← setIntegral_union disjoint_sdiff_right hann (hg _ measurableSet_ball hsub)
        (hg _ hann sdiff_subset), union_sdiff_cancel hsub]
    have h3 : ∫ y in ball x R \ ball x r, K (x - y) * (f y - f x) =
        ∫ y in ball x R \ ball x r, K (x - y) * f y := by
      simp only [mul_sub]
      rw [integral_sub hk (hK1.mul_const _), integral_mul_const, hK.integral_annulus_sub x r R,
        zero_mul, sub_zero]
    rw [h1, hK.setIntegral_compl_ball_eq hf x hr hrR, h3]
    ring
  rcases le_total r 1 with h | h
  · exact key r 1 hr h
  · exact (key 1 r one_pos h).symm

omit hK in
/-- `δ / t³ = δ t^(0 - 3)` for `t > 0`. -/
private theorem div_pow_three_eq_rpow {c t : ℝ} (ht : 0 < t) :
    c / t ^ 3 = c * t ^ ((0 : ℝ) - 3) := by
  rw [zero_sub, Real.rpow_neg ht.le, show ((3 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast, div_eq_mul_inv]

/-- The kernel difference `K(x - y) - K(x' - y)` is bounded by `A |x - x'| / |x - y|³` once
`|x - y| ≥ 2 |x - x'|`. -/
theorem abs_sub_sub_le (x x' y : ℝ^2) (h : 2 * ‖x - x'‖ ≤ ‖x - y‖) :
    |K (x - y) - K (x' - y)| ≤ A * ‖x - x'‖ / ‖x - y‖ ^ 3 := by
  have h' : (x - y) - (x' - y) = x - x' := by abel
  have := hK.abs_sub_le (x - y) (x' - y) (by rw [h']; exact h)
  rwa [h'] at this

/-- **Far part with a Hölder factor.** On a measurable set `S` with `|x - y| ≥ 2 |x - x'|`
and `|y - p| ≤ c |x - y|` (`c ≥ 1`), the integrand `(K(x - y) - K(x' - y))(f(y) - f(p))` is
integrable with integral at most `c A M |x - x'| · 2π (2|x - x'|)^(α-1)/(1-α)`. -/
theorem integrableOn_sub_mul_sub_and_abs_le (hα : 0 < α) (hα1 : α < 1)
    (hfm : AEStronglyMeasurable f) (hM : ∀ y z, |f y - f z| ≤ M * ‖y - z‖ ^ α)
    {x x' p : ℝ^2} (hxx' : x ≠ x') {S : Set (ℝ^2)} (hS : MeasurableSet S)
    (hSx : ∀ y ∈ S, 2 * ‖x - x'‖ ≤ ‖x - y‖) {c : ℝ} (hc : 1 ≤ c)
    (hp : ∀ y ∈ S, ‖y - p‖ ≤ c * ‖x - y‖) :
    IntegrableOn (fun y ↦ (K (x - y) - K (x' - y)) * (f y - f p)) S ∧
      |∫ y in S, (K (x - y) - K (x' - y)) * (f y - f p)| ≤
        c * A * M * ‖x - x'‖ * (2 * Real.pi * (2 * ‖x - x'‖) ^ (α - 1) / (1 - α)) := by
  have hA := hK.nonneg
  have hM0 := nonneg_of_holder hM
  have hδ : 0 < ‖x - x'‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxx')
  set C := c * A * M * ‖x - x'‖ with hCdef
  have hC : 0 ≤ C := by positivity
  have hle : ∀ y ∈ S, ‖(K (x - y) - K (x' - y)) * (f y - f p)‖ ≤ C * ‖x - y‖ ^ (α - 3) := by
    intro y hy
    have h2 := hSx y hy
    have hn : 0 < ‖x - y‖ := by linarith
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have hfy : |f y - f p| ≤ c * M * ‖x - y‖ ^ α := calc
      _ ≤ M * (c * ‖x - y‖) ^ α := (hM y p).trans (by gcongr; exact hp y hy)
      _ ≤ M * (c * ‖x - y‖ ^ α) := by
        rw [Real.mul_rpow (by linarith) hn.le]
        gcongr
        exact (Real.rpow_le_rpow_of_exponent_le hc hα1.le).trans_eq (Real.rpow_one c)
      _ = c * M * ‖x - y‖ ^ α := by ring
    calc |K (x - y) - K (x' - y)| * |f y - f p|
        ≤ A * ‖x - x'‖ / ‖x - y‖ ^ 3 * (c * M * ‖x - y‖ ^ α) := by
          gcongr
          exact hK.abs_sub_sub_le x x' y h2
      _ = C * ‖x - y‖ ^ (α - 3) := by
          rw [Real.rpow_sub hn, show ((3 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          rw [hCdef]
          field_simp
  have hSsub : S ⊆ (ball x (2 * ‖x - x'‖))ᶜ := fun y hy hyb ↦ by
    have := hSx y hy
    rw [mem_ball, dist_eq_norm, norm_sub_rev] at hyb
    linarith
  have hval := lintegral_compl_ball_mul_rpow_sub_three x hC (by positivity : 0 < 2 * ‖x - x'‖)
    hα1
  have hfin : ∫⁻ y in S, ENNReal.ofReal (C * ‖x - y‖ ^ (α - 3)) ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [hval]; exact ENNReal.ofReal_ne_top) (lintegral_mono_set hSsub)
  refine ⟨integrableOn_of_norm_le_of_lintegral_ne_top hS ?_ hle hfin, ?_⟩
  · exact (((hK.measurable.comp (measurable_const.sub measurable_id)).sub
      (hK.measurable.comp (measurable_const.sub measurable_id))).aestronglyMeasurable.mul
      (hfm.sub aestronglyMeasurable_const)).restrict
  rw [← Real.norm_eq_abs]
  refine (norm_setIntegral_le_of_norm_le hS hle hfin).trans ?_
  rw [← ENNReal.toReal_ofReal (by positivity :
    0 ≤ C * (2 * Real.pi * (2 * ‖x - x'‖) ^ (α - 1) / (1 - α))), ← hval]
  exact ENNReal.toReal_mono (by rw [hval]; exact ENNReal.ofReal_ne_top)
    (lintegral_mono_set hSsub)

/-- The kernel difference is integrable outside `B(x, 2|x - x'|)`. -/
theorem integrableOn_compl_ball_sub {x x' : ℝ^2} (hxx' : x ≠ x') :
    IntegrableOn (fun y ↦ K (x - y) - K (x' - y)) (ball x (2 * ‖x - x'‖))ᶜ := by
  have hA := hK.nonneg
  have hδ : 0 < ‖x - x'‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxx')
  have hC : 0 ≤ A * ‖x - x'‖ := by positivity
  have hval := lintegral_compl_ball_mul_rpow_sub_three x hC (by positivity : 0 < 2 * ‖x - x'‖)
    (by norm_num : (0 : ℝ) < 1)
  refine integrableOn_of_norm_le_of_lintegral_ne_top measurableSet_ball.compl
    ((hK.measurable.comp (measurable_const.sub measurable_id)).sub
      (hK.measurable.comp (measurable_const.sub measurable_id))).aestronglyMeasurable.restrict
    (fun y hy ↦ ?_) (by rw [hval]; exact ENNReal.ofReal_ne_top)
  have h2 := le_norm_sub_of_mem_compl_ball hy
  have hn : 0 < ‖x - y‖ := by linarith
  rw [Real.norm_eq_abs, ← div_pow_three_eq_rpow hn]
  exact hK.abs_sub_sub_le x x' y h2

/-- **Total cancellation.** With `δ = |x - x'| > 0`,
`∫_{|x-y|≥2δ} (K(x - y) - K(x' - y)) dy = ∫_{B(x,2δ) \ B(x',δ)} K(x' - y) dy`, the principal
value of `K(x' - ·)` over `B(x, 2δ)`. -/
theorem integral_compl_ball_sub {x x' : ℝ^2} (hxx' : x ≠ x') :
    ∫ y in (ball x (2 * ‖x - x'‖))ᶜ, (K (x - y) - K (x' - y)) =
      ∫ y in ball x (2 * ‖x - x'‖) \ ball x' ‖x - x'‖, K (x' - y) := by
  have hA := hK.nonneg
  set δ := ‖x - x'‖ with hδdef
  have hδ : 0 < δ := norm_pos_iff.mpr (sub_ne_zero.mpr hxx')
  set N := ball x (2 * δ) with hNdef
  set F : ℝ^2 → ℝ := fun y ↦ K (x - y) - K (x' - y) with hFdef
  set c := ∫ y in N \ ball x' δ, K (x' - y) with hcdef
  have hm {a b : ℝ^2} {r s : ℝ} : MeasurableSet (ball a r \ ball b s) :=
    measurableSet_ball.diff measurableSet_ball
  have hx'x (y : ℝ^2) : ‖x - y‖ - δ ≤ ‖x' - y‖ := by
    have := norm_sub_le_norm_sub_add_norm_sub x x' y
    linarith
  have hB'R (R : ℝ) : ball x' (R - δ) ⊆ ball x R :=
    ball_subset_ball' (by rw [dist_comm, dist_eq_norm, ← hδdef]; linarith)
  have hB'N : ball x' δ ⊆ N :=
    ball_subset_ball' (by rw [dist_comm, dist_eq_norm, ← hδdef]; linarith)
  -- the error term on the crescent
  set e : ℝ → ℝ := fun R ↦ ∫ y in ball x R \ ball x' (R - δ), K (x' - y) with hedef
  have hval : ∀ R, 3 * δ ≤ R → ∫ y in ball x R \ N, F y = c - e R := by
    intro R hR
    have hNR : N ⊆ ball x R := ball_subset_ball (by linarith)
    have hK2 (S : Set (ℝ^2)) (hS : MeasurableSet S) (hSR : S ⊆ ball x R)
        (hSδ : ∀ y ∈ S, δ ≤ ‖x' - y‖) : IntegrableOn (fun y ↦ K (x' - y)) S :=
      hK.integrableOn_of_le x' hS ((measure_mono hSR).trans_lt measure_ball_lt_top).ne hδ hSδ
    have i1 : IntegrableOn (fun y ↦ K (x' - y)) (ball x R \ N) :=
      hK2 _ hm sdiff_subset fun y hy ↦ by linarith [le_norm_sub_of_mem_compl_ball hy.2, hx'x y]
    have hsplit1 : ∫ y in ball x R \ N, F y =
        (∫ y in ball x R \ N, K (x - y)) - ∫ y in ball x R \ N, K (x' - y) :=
      integral_sub (hK.integrableOn_of_le x hm
        ((measure_mono sdiff_subset).trans_lt measure_ball_lt_top).ne (by linarith)
        fun y hy ↦ le_norm_sub_of_mem_compl_ball hy.2) i1
    have hsplit2 : ∫ y in ball x R \ ball x' δ, K (x' - y) =
        (∫ y in ball x R \ N, K (x' - y)) + c := by
      rw [← sdiff_union_sdiff_cancel hNR hB'N, setIntegral_union
        (disjoint_sdiff_left.mono_right sdiff_subset) hm i1
        (hK2 (N \ ball x' δ) hm (sdiff_subset.trans hNR) fun y hy ↦
          le_norm_sub_of_mem_compl_ball hy.2)]
    have hsplit3 : ∫ y in ball x R \ ball x' δ, K (x' - y) = e R := by
      rw [← sdiff_union_sdiff_cancel (hB'R R) (ball_subset_ball (by linarith)), setIntegral_union
        (disjoint_sdiff_left.mono_right sdiff_subset) hm
        (hK2 _ hm sdiff_subset fun y hy ↦ by linarith [le_norm_sub_of_mem_compl_ball hy.2])
        (hK2 _ hm (sdiff_subset.trans (hB'R R)) fun y hy ↦ le_norm_sub_of_mem_compl_ball hy.2),
        hK.integral_annulus_sub x' δ (R - δ), add_zero]
    rw [hsplit1, hK.integral_annulus_sub x (2 * δ) R]
    linarith
  -- the integrals over `B(x,R) \ N` converge to the integral over `Nᶜ`
  have hFint : IntegrableOn F Nᶜ := hK.integrableOn_compl_ball_sub hxx'
  have hlim1 : Tendsto (fun R ↦ ∫ y in ball x R \ N, F y) atTop (𝓝 (∫ y in Nᶜ, F y)) := by
    simp_rw [fun R ↦ show ∫ y in ball x R \ N, F y = ∫ y in Nᶜ, (ball x R).indicator F y by
      rw [setIntegral_indicator measurableSet_ball, Set.sdiff_eq, inter_comm]]
    refine tendsto_integral_filter_of_dominated_convergence (fun y ↦ ‖F y‖)
      (Eventually.of_forall fun R ↦ (hFint.aestronglyMeasurable.indicator measurableSet_ball))
      (Eventually.of_forall fun R ↦ Eventually.of_forall fun y ↦ norm_indicator_le_norm_self _ _)
      hFint.norm (Eventually.of_forall fun y ↦ tendsto_const_nhds.congr' ?_)
    filter_upwards [eventually_gt_atTop (dist y x)] with R hR
    rw [indicator_of_mem (mem_ball.mpr hR)]
  -- the crescent error tends to zero
  have hlim2 : Tendsto e atTop (𝓝 0) := by
    have hbound : ∀ R, 3 * δ ≤ R → ‖e R‖ ≤ 9 / 2 * A * Real.pi * δ / R := by
      intro R hR
      have hRpos : 0 < R := by linarith
      have hRδ : 0 < R - δ := by linarith
      have h1 := norm_setIntegral_le_of_norm_le_const (f := fun y ↦ K (x' - y))
        (s := ball x R \ ball x' (R - δ)) (C := A / (R - δ) ^ 2) (μ := volume)
        ((measure_mono sdiff_subset).trans_lt (measure_ball_lt_top (x := x) (r := R)))
        fun y hy ↦ (Real.norm_eq_abs _).trans_le
          (hK.abs_le_of_le hRδ (le_norm_sub_of_mem_compl_ball hy.2))
      rw [measureReal_sdiff (hB'R R) measurableSet_ball measure_ball_lt_top.ne,
        measureReal_ball_two x hRpos.le, measureReal_ball_two x' hRδ.le] at h1
      refine h1.trans ?_
      have hsq : 4 * R ^ 2 / 9 ≤ (R - δ) ^ 2 := by nlinarith
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hRpos]
      have hπ := Real.pi_pos
      nlinarith [mul_nonneg hA hπ.le, mul_nonneg (mul_nonneg hA hπ.le) hδ.le,
        mul_nonneg (mul_nonneg hA hπ.le) (sq_nonneg δ)]
    exact squeeze_zero_norm' (eventually_atTop.2 ⟨3 * δ, hbound⟩)
      (tendsto_const_nhds.div_atTop tendsto_id)
  have hlim3 : Tendsto (fun R ↦ ∫ y in ball x R \ N, F y) atTop (𝓝 (c - 0)) :=
    (tendsto_const_nhds.sub hlim2).congr' (eventually_atTop.2 ⟨3 * δ, fun R hR ↦ (hval R hR).symm⟩)
  rw [sub_zero] at hlim3
  exact tendsto_nhds_unique hlim1 hlim3

/-- **Hölder continuity of planar singular integrals.** For a singular kernel with constant `A`
and an integrable density with `|f(y) - f(z)| ≤ M |y - z|^α`, `0 < α < 1`,
`|T f(x) - T f(x')| ≤ 10π/(α(1-α)) · A M |x - x'|^α`. -/
theorem abs_singularIntegral_sub_le (hα : 0 < α) (hα1 : α < 1) (hf : Integrable f)
    (hM : ∀ y z, |f y - f z| ≤ M * ‖y - z‖ ^ α) (x x' : ℝ^2) :
    |singularIntegral K f x - singularIntegral K f x'| ≤
      10 * Real.pi / (α * (1 - α)) * A * M * ‖x - x'‖ ^ α := by
  have hA := hK.nonneg
  have hM0 := nonneg_of_holder hM
  have hfm := hf.aestronglyMeasurable
  rcases eq_or_ne x x' with rfl | hxx'
  · rw [sub_self, abs_zero]
    have : 0 < α * (1 - α) := mul_pos hα (by linarith)
    positivity
  set δ := ‖x - x'‖ with hδdef
  have hδ : 0 < δ := norm_pos_iff.mpr (sub_ne_zero.mpr hxx')
  set N := ball x (2 * δ) with hNdef
  have hx'x (y : ℝ^2) : ‖x - y‖ - δ ≤ ‖x' - y‖ := by
    linarith [norm_sub_le_norm_sub_add_norm_sub x x' y]
  have hB'N : ball x' δ ⊆ N :=
    ball_subset_ball' (by rw [dist_comm, dist_eq_norm, ← hδdef]; linarith)
  have hN3 : N ⊆ ball x' (3 * δ) := ball_subset_ball' (by rw [dist_eq_norm, ← hδdef]; linarith)
  have hT := hK.singularIntegral_eq hα hf hM x (by linarith : (0 : ℝ) < 2 * δ)
  have hT' := hK.singularIntegral_eq hα hf hM x' hδ
  have hNm : MeasurableSet N := measurableSet_ball
  have hNδm : MeasurableSet (N \ ball x' δ) := measurableSet_ball.diff measurableSet_ball
  have hNδ : ∀ y ∈ N \ ball x' δ, δ ≤ ‖x' - y‖ := fun y hy ↦ le_norm_sub_of_mem_compl_ball hy.2
  have hNcδ : ∀ y ∈ Nᶜ, δ ≤ ‖x' - y‖ := fun y hy ↦ by
    linarith [le_norm_sub_of_mem_compl_ball hy, hx'x y]
  have hNfin : volume (N \ ball x' δ) ≠ ⊤ :=
    ((measure_mono sdiff_subset).trans_lt measure_ball_lt_top).ne
  -- integrability
  have i1 : IntegrableOn (fun y ↦ K (x' - y) * (f y - f x')) (ball x' δ) :=
    hK.integrableOn_mul_sub hα hfm hM x' measurableSet_ball hδ.le subset_rfl
  have i2 : IntegrableOn (fun y ↦ K (x' - y) * (f y - f x')) (N \ ball x' δ) :=
    hK.integrableOn_mul_sub hα hfm hM x' hNδm (by linarith) (sdiff_subset.trans hN3)
  have i3 : IntegrableOn (fun y ↦ K (x' - y)) (N \ ball x' δ) :=
    hK.integrableOn_of_le x' hNδm hNfin hδ hNδ
  have i4 : IntegrableOn (fun y ↦ K (x' - y) * f y) (N \ ball x' δ) :=
    hK.integrableOn_mul_of_le hf x' hNδm hδ hNδ
  have i5 : IntegrableOn (fun y ↦ K (x' - y) * f y) Nᶜ :=
    hK.integrableOn_mul_of_le hf x' hNm.compl hδ hNcδ
  have i6 : IntegrableOn (fun y ↦ K (x - y) * f y) Nᶜ :=
    hK.integrableOn_compl_ball hf x (by linarith)
  have hfar := hK.integrableOn_sub_mul_sub_and_abs_le (p := x') hα hα1 hfm hM hxx' hNm.compl
    (fun y hy ↦ le_norm_sub_of_mem_compl_ball hy) (le_refl (3 / 2 : ℝ) |>.trans' (by norm_num))
    (fun y hy ↦ by
      linarith [le_norm_sub_of_mem_compl_ball hy, norm_sub_le_norm_sub_add_norm_sub y x x',
        norm_sub_rev y x])
  have i8 : IntegrableOn (fun y ↦ K (x - y) - K (x' - y)) Nᶜ := hK.integrableOn_compl_ball_sub hxx'
  -- the decomposition
  set c := ∫ y in N \ ball x' δ, K (x' - y) with hcdef
  have e1 : ∫ y in (ball x' δ)ᶜ, K (x' - y) * f y =
      (∫ y in N \ ball x' δ, K (x' - y) * f y) + ∫ y in Nᶜ, K (x' - y) * f y := by
    have hset : (ball x' δ)ᶜ = (N \ ball x' δ) ∪ Nᶜ := by
      ext y
      have := @hB'N y
      simp only [mem_compl_iff, mem_union, Set.mem_sdiff]
      tauto
    rw [hset, setIntegral_union (disjoint_compl_right.mono_left sdiff_subset) hNm.compl i4 i5]
  have e2 : ∫ y in N \ ball x' δ, K (x' - y) * f y =
      (∫ y in N \ ball x' δ, K (x' - y) * (f y - f x')) + f x' * c := by
    rw [show (fun y ↦ K (x' - y) * f y) =
        fun y ↦ K (x' - y) * (f y - f x') + K (x' - y) * f x' by funext y; ring,
      integral_add i2 (i3.mul_const _), integral_mul_const, hcdef, mul_comm]
  have e3 : ∫ y in N, K (x' - y) * (f y - f x') =
      (∫ y in ball x' δ, K (x' - y) * (f y - f x')) +
        ∫ y in N \ ball x' δ, K (x' - y) * (f y - f x') := by
    rw [← setIntegral_union disjoint_sdiff_right hNδm i1 i2, union_sdiff_cancel hB'N]
  have e4 : (∫ y in Nᶜ, K (x - y) * f y) - ∫ y in Nᶜ, K (x' - y) * f y =
      (∫ y in Nᶜ, (K (x - y) - K (x' - y)) * (f y - f x')) +
        f x' * ∫ y in Nᶜ, (K (x - y) - K (x' - y)) := by
    rw [← integral_sub i6 i5, ← integral_const_mul, ← integral_add hfar.1 (i8.const_mul _)]
    congr 1 with y
    ring
  have e5 : ∫ y in Nᶜ, (K (x - y) - K (x' - y)) = c := hK.integral_compl_ball_sub hxx'
  have hdec : singularIntegral K f x - singularIntegral K f x' =
      (∫ y in N, K (x - y) * (f y - f x)) - (∫ y in N, K (x' - y) * (f y - f x')) +
        ∫ y in Nᶜ, (K (x - y) - K (x' - y)) * (f y - f x') := by
    rw [hT, hT', e1, e2, e3]
    rw [e5] at e4
    linarith
  -- the bounds
  have b1 := hK.abs_setIntegral_mul_sub_le hα hM x hNm (by linarith : (0 : ℝ) ≤ 2 * δ) subset_rfl
  have b2 := hK.abs_setIntegral_mul_sub_le hα hM x' hNm (by linarith : (0 : ℝ) ≤ 3 * δ) hN3
  have b3 := hfar.2
  rw [hdec]
  refine (abs_add_le _ _).trans ((add_le_add (abs_sub _ _) le_rfl).trans ?_)
  have hsum := holder_constant_le hδ hα hα1
  calc |∫ y in N, K (x - y) * (f y - f x)| + |∫ y in N, K (x' - y) * (f y - f x')| +
        |∫ y in Nᶜ, (K (x - y) - K (x' - y)) * (f y - f x')|
      ≤ A * M * (2 * Real.pi * (2 * δ) ^ α / α) + A * M * (2 * Real.pi * (3 * δ) ^ α / α) +
          3 / 2 * A * M * δ * (2 * Real.pi * (2 * δ) ^ (α - 1) / (1 - α)) := by
        gcongr
    _ = A * M * (2 * Real.pi * (2 * δ) ^ α / α + 2 * Real.pi * (3 * δ) ^ α / α +
          3 / 2 * δ * (2 * Real.pi * (2 * δ) ^ (α - 1) / (1 - α))) := by ring
    _ ≤ A * M * (10 * Real.pi / (α * (1 - α)) * δ ^ α) := by gcongr
    _ = 10 * Real.pi / (α * (1 - α)) * A * M * δ ^ α := by ring

/-- **Size of planar singular integrals.** `|T f(x)| ≤ A (2πM/α + ‖f‖₁)`. -/
theorem abs_singularIntegral_le (hα : 0 < α) (hf : Integrable f)
    (hM : ∀ y z, |f y - f z| ≤ M * ‖y - z‖ ^ α) (x : ℝ^2) :
    |singularIntegral K f x| ≤ A * (2 * Real.pi * M / α + ∫ y, |f y|) := by
  have b1 := hK.abs_setIntegral_mul_sub_le hα hM x measurableSet_ball zero_le_one subset_rfl
  have b2 := hK.abs_setIntegral_mul_le hf x measurableSet_ball.compl one_pos
    fun y hy ↦ le_norm_sub_of_mem_compl_ball hy
  rw [Real.one_rpow, one_pow, div_one] at *
  refine (abs_add_le _ _).trans ((add_le_add b1 b2).trans (le_of_eq ?_))
  ring

/-- **Logarithmic size bound of planar singular integrals.** For `|f| ≤ B`,
`|T f(x)| ≤ (2πA/α)(1 + B log(2 + M)) + A ‖f‖₁`. The Hölder constant enters only through the
logarithm. -/
theorem abs_singularIntegral_le_log (hα : 0 < α) (hf : Integrable f)
    (hM : ∀ y z, |f y - f z| ≤ M * ‖y - z‖ ^ α) {B : ℝ} (hB : ∀ y, |f y| ≤ B) (x : ℝ^2) :
    |singularIntegral K f x| ≤
      2 * Real.pi * A / α * (1 + B * Real.log (2 + M)) + A * ∫ y, |f y| := by
  have hA := hK.nonneg
  have hM0 := nonneg_of_holder hM
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hL : 0 ≤ ∫ y, |f y| := integral_nonneg fun y ↦ abs_nonneg _
  have hlog2 : 0 ≤ Real.log (2 + M) := Real.log_nonneg (by linarith)
  -- the estimate at any radius `r ∈ (0, 1]`
  have key : ∀ r : ℝ, 0 < r → r ≤ 1 → |singularIntegral K f x| ≤
      A * M * (2 * Real.pi * r ^ α / α) + A * B * (2 * Real.pi * Real.log (1 / r)) +
        A * ∫ y, |f y| := by
    intro r hr hr1
    rw [hK.singularIntegral_eq hα hf hM x hr, hK.setIntegral_compl_ball_eq hf x hr hr1]
    have b1 := hK.abs_setIntegral_mul_sub_le hα hM x measurableSet_ball hr.le subset_rfl
    have b3 := hK.abs_setIntegral_mul_le hf x measurableSet_ball.compl one_pos
      fun y hy ↦ le_norm_sub_of_mem_compl_ball hy
    rw [one_pow, div_one] at b3
    have hann : MeasurableSet (ball x 1 \ ball x r) := measurableSet_ball.diff measurableSet_ball
    have hval := lintegral_annulus_mul_inv_sq x (mul_nonneg hA hB0) hr hr1
    have hle : ∀ y ∈ ball x 1 \ ball x r, ‖K (x - y) * f y‖ ≤ A * B * (‖x - y‖ ^ 2)⁻¹ := by
      intro y hy
      have hn : 0 < ‖x - y‖ := hr.trans_le (le_norm_sub_of_mem_compl_ball hy.2)
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact (mul_le_mul (hK.abs_le _) (hB y) (abs_nonneg _) (by positivity)).trans_eq (by ring)
    have b2 := norm_setIntegral_le_of_norm_le hann hle (by rw [hval]; exact ENNReal.ofReal_ne_top)
    rw [hval, ENNReal.toReal_ofReal (by
      have : 0 ≤ Real.log (1 / r) := Real.log_nonneg (by rw [le_div_iff₀ hr]; linarith)
      positivity), Real.norm_eq_abs] at b2
    refine (abs_add_le _ _).trans (add_le_add b1 ((abs_add_le _ _).trans (add_le_add b2 b3)))
      |>.trans (le_of_eq ?_)
    ring
  rcases le_or_gt M 1 with hM1 | hM1
  · refine (key 1 one_pos le_rfl).trans ?_
    rw [Real.one_rpow, mul_one, div_one, Real.log_one, mul_zero, mul_zero, add_zero]
    have h1 : A * M * (2 * Real.pi / α) ≤ 2 * Real.pi * A / α := by
      rw [show 2 * Real.pi * A / α = A * 1 * (2 * Real.pi / α) by ring]
      gcongr
    have h2 : 0 ≤ 2 * Real.pi * A / α * (B * Real.log (2 + M)) := by positivity
    rw [mul_add, mul_one]
    linarith
  · -- choose `r = M^(-1/α)`, so that `M r^α = 1`
    set r := M ^ (-1 / α) with hrdef
    have hMpos : 0 < M := by linarith
    have hr : 0 < r := Real.rpow_pos_of_pos hMpos _
    have hr1 : r ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hM1.le
      (div_nonpos_of_nonpos_of_nonneg (by norm_num) hα.le)
    have hrα : M * r ^ α = 1 := by
      rw [hrdef, ← Real.rpow_mul hMpos.le, show -1 / α * α = -1 by field_simp,
        Real.rpow_neg_one, mul_inv_cancel₀ hMpos.ne']
    have hlog : Real.log (1 / r) = Real.log M / α := by
      rw [one_div, Real.log_inv, hrdef, Real.log_rpow hMpos]
      ring
    refine (key r hr hr1).trans ?_
    rw [hlog]
    have hlogM : Real.log M ≤ Real.log (2 + M) := Real.log_le_log hMpos (by linarith)
    have h1 : A * M * (2 * Real.pi * r ^ α / α) = 2 * Real.pi * A / α := by
      rw [show A * M * (2 * Real.pi * r ^ α / α) = 2 * Real.pi * A / α * (M * r ^ α) by ring,
        hrα, mul_one]
    have h2 : A * B * (2 * Real.pi * (Real.log M / α)) ≤
        2 * Real.pi * A / α * (B * Real.log (2 + M)) := by
      rw [show A * B * (2 * Real.pi * (Real.log M / α)) =
        2 * Real.pi * A / α * (B * Real.log M) by ring]
      gcongr
    rw [h1]
    nlinarith

/-- The singular integral is linear on Hölder integrable densities. -/
theorem singularIntegral_sub {g : ℝ^2 → ℝ} {Mg : ℝ} (hα : 0 < α)
    (hf : Integrable f) (hg : Integrable g)
    (hM : ∀ y z, |f y - f z| ≤ M * ‖y - z‖ ^ α) (hMg : ∀ y z, |g y - g z| ≤ Mg * ‖y - z‖ ^ α)
    (x : ℝ^2) :
    singularIntegral K (f - g) x = singularIntegral K f x - singularIntegral K g x := by
  unfold singularIntegral
  have h1 := hK.integrableOn_mul_sub hα hf.aestronglyMeasurable hM x measurableSet_ball
    zero_le_one subset_rfl
  have h2 := hK.integrableOn_mul_sub hα hg.aestronglyMeasurable hMg x measurableSet_ball
    zero_le_one subset_rfl
  have h3 := hK.integrableOn_compl_ball hf x one_pos
  have h4 := hK.integrableOn_compl_ball hg x one_pos
  have e1 : ∫ y in ball x 1, K (x - y) * ((f - g) y - (f - g) x) =
      (∫ y in ball x 1, K (x - y) * (f y - f x)) - ∫ y in ball x 1, K (x - y) * (g y - g x) := by
    rw [← integral_sub h1 h2]
    congr 1; funext y; simp only [Pi.sub_apply]; ring
  have e2 : ∫ y in (ball x 1)ᶜ, K (x - y) * (f - g) y =
      (∫ y in (ball x 1)ᶜ, K (x - y) * f y) - ∫ y in (ball x 1)ᶜ, K (x - y) * g y := by
    rw [← integral_sub h3 h4]
    congr 1; funext y; simp only [Pi.sub_apply]; ring
  rw [e1, e2]
  ring

end IsSingularKernel

/-- For the Hessian kernels the singular integral of a Hölder integrable density is the
disc-truncated principal value. -/
theorem hasPrincipalValueAt_singularIntegral (i j : Fin 2) (hα : 0 < α) (hf : Integrable f)
    (hM : ∀ y z, |f y - f z| ≤ M * ‖y - z‖ ^ α) (x : ℝ^2) :
    PDE.Analysis.HasPrincipalValueAt univ (fun x y ↦ hessianKernel i j (x - y)) f x
      (singularIntegral (hessianKernel i j) f x) := by
  have hK := isSingularKernel_hessianKernel i j
  have h := hasPrincipalValueAt_hessianKernel_of_holder i j MeasurableSet.univ one_pos hα
    (subset_univ _) hf.aestronglyMeasurable (fun y _ ↦ by
      rw [← norm_neg (x - y), neg_sub]; exact hM y x)
    (by rw [← compl_eq_univ_sdiff]; exact hK.integrableOn_compl_ball hf x one_pos)
  rwa [← compl_eq_univ_sdiff] at h

end PotentialTheory.Planar
