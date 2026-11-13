/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.FundamentalSolution.PlanarPrincipalValue
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.QuadrantSymmetrization
import PDE.Analysis.Integration.Rectangle.MixedPrimitive
import PDE.Analysis.InnerProductSpace.Euclidean.Coordinates

/-!
# The principal value of `K₂` at the corner of a rectangle

Lemma B.1 of Chen and Hou I (Appendix B.1). Let `Q = cornerRectangle a b` be the rectangle with
corners `0` and `(a, b)`, `a, b ≠ 0`, in any of the four quadrants, let `K₂ = hessianKernel 0 0`,
and let `f` be Hölder continuous at `0` on `Q`. With
`L = ∫_Q K₂ (f - f(0)) + ((1/2) arctan(|a|/|b|) - π/8) f(0)`, removing the corner square
`|y₀|, |y₁| < ε` (the principal value of Lemma B.1) or the disc `|y| < ε` gives the
principal value `L`, while removing the strip `|y₀| < ε` gives `L + (π/8) f(0)` and removing the
strip `|y₁| < ε` gives `L - (π/8) f(0)`.

The square and the disc agree because the region between them is invariant under the coordinate
swap, which reverses the sign of `K₂`. The strips are not swap invariant: `K₂ < 0` in the strip
`|y₀| < ε` away from the corner and `K₂ > 0` in the strip `|y₁| < ε`.

The proof subtracts `f(0)`, whose remainder is absolutely integrable, and computes the integrals
of `K₂` over rectangles with `∂_{y₁}(y₁ / (2|y|²)) = K₂`; for example the corner strip
`[0, ε) × [ε, b]` contributes `(1/2)(arctan(ε/b) - π/4)`. The reflections of either coordinate
preserve `K₂`, which reduces the constants to the first quadrant.

## Main definitions

* `cornerRectangle`: the rectangle with opposite corners `0` and `(a, b)`.

## Main results

* `integral_rectangle_hessianKernel_zero_zero`: for a rectangle `[s₀,s₁]×[t₀,t₁]` of the first
  quadrant avoiding the origin, `∫ K₂` is a sum of four arctangents `(1/2) arctan(sᵢ/tⱼ)`.
* `tendsto_setIntegral_hessianKernel_cornerRectangle`: the square truncations tend to `L`.
* `hasPrincipalValueAt_hessianKernel_cornerRectangle`: the disc-truncated principal value exists
  and equals `L`.
* `tendsto_setIntegral_hessianKernel_cornerRectangle_strip_zero`: the strip truncations
  `|y₀| ≥ ε` tend to `L + (π/8) f(0)`.
* `tendsto_setIntegral_hessianKernel_cornerRectangle_strip_one`: the strip truncations
  `|y₁| ≥ ε` tend to `L - (π/8) f(0)`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Appendix B.1, Lemma B.1.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace PotentialTheory.Planar

/-- The coordinate `y ↦ y k` of the plane is measurable. -/
private theorem measurable_coord (k : Fin 2) : Measurable fun y : ℝ^2 ↦ y k :=
  (EuclideanSpace.proj k).continuous.measurable

/-- The function `y ↦ |y k|` is measurable. -/
private theorem measurable_abs_coord (k : Fin 2) : Measurable fun y : ℝ^2 ↦ |y k| :=
  continuous_abs.measurable.comp (measurable_coord k)

/-- A Hessian kernel is integrable on a bounded measurable set staying away from the pole. -/
private theorem integrableOn_hessianKernel_of_le (i j : Fin 2) {T : Set (ℝ^2)}
    (hT : MeasurableSet T) {ε R : ℝ} (hε : 0 < ε) (hTR : T ⊆ Metric.closedBall 0 R)
    (hTε : ∀ y ∈ T, ε ≤ ‖y‖) : IntegrableOn (hessianKernel i j) T := by
  refine Measure.integrableOn_of_bounded (M := 1 / (2 * ε ^ 2))
    ((measure_mono hTR).trans_lt measure_closedBall_lt_top).ne
    (measurable_hessianKernel i j).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem hT] with y hy
  rw [Real.norm_eq_abs]
  refine (abs_hessianKernel_le i j y).trans ?_
  have := hTε y hy
  gcongr

/-- The inner integral: `∫_{t₀}^{t₁} K₂(p, q) dq = t₁/(2(p² + t₁²)) - t₀/(2(p² + t₀²))`. -/
private theorem integral_inner_hessianKernel {p t₀ t₁ : ℝ} (hp : p ≠ 0 ∨ 0 < t₀)
    (ht : t₀ ≤ t₁) :
    ∫ q in Icc t₀ t₁, (p ^ 2 - q ^ 2) / (2 * (p ^ 2 + q ^ 2) ^ 2) =
      t₁ / (2 * (p ^ 2 + t₁ ^ 2)) - t₀ / (2 * (p ^ 2 + t₀ ^ 2)) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht]
  have hpos : ∀ q ∈ uIcc t₀ t₁, 0 < p ^ 2 + q ^ 2 := by
    intro q hq
    rw [uIcc_of_le ht] at hq
    rcases hp with hp | hp
    · have := pow_pos (abs_pos.mpr hp) 2; rw [sq_abs] at this; positivity
    · have : 0 < q := lt_of_lt_of_le hp hq.1; positivity
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro q hq'
    have hq := hpos q hq'
    have h := ((hasDerivAt_id q).div (((hasDerivAt_pow 2 q).const_add (p ^ 2)).const_mul 2)
      (by positivity))
    convert h using 1
    · funext r; simp
    · simp only [id, Nat.cast_ofNat]; field_simp; ring
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro q hq; have := hpos q hq; positivity

/-- The outer integral: `∫_{s₀}^{s₁} t/(2(p² + t²)) dp = (1/2)(arctan(s₁/t) - arctan(s₀/t))`. -/
private theorem integral_outer_hessianKernel {s₀ s₁ t : ℝ} (ht : 0 < t) (hs : s₀ ≤ s₁) :
    ∫ p in Icc s₀ s₁, t / (2 * (p ^ 2 + t ^ 2)) =
      (Real.arctan (s₁ / t) - Real.arctan (s₀ / t)) / 2 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs]
  have hpos : ∀ p : ℝ, 0 < p ^ 2 + t ^ 2 := fun p ↦ by positivity
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun p ↦ Real.arctan (p / t) / 2) (f' := fun p ↦ t / (2 * (p ^ 2 + t ^ 2)))
    (a := s₀) (b := s₁) (fun p _ ↦ by
      have h := ((Real.hasDerivAt_arctan (p / t)).comp p
        ((hasDerivAt_id p).div_const t)).div_const 2
      convert h using 1
      · simp only [id, Function.comp_apply]
      · field_simp
        ring)
    (by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.div continuous_const.continuousOn (by fun_prop)
      intro p _; have := hpos p; positivity)
  rw [h]
  ring

/-- **`K₂` over a rectangle in the first quadrant.** Let `s` and `t` agree almost everywhere
with `[s₀, s₁]` and `[t₀, t₁]` and lie inside them, where `0 ≤ s₀ ≤ s₁`, `0 ≤ t₀ ≤ t₁`,
`0 < t₁` and `(s₀, t₀) ≠ 0`. Then
`∫_{s × t} K₂ = (1/2)(arctan(s₁/t₁) - arctan(s₀/t₁) - arctan(s₁/t₀) + arctan(s₀/t₀))`,
with `arctan(s/0) = 0`. -/
private theorem setIntegral_rectangle_hessianKernel {s t : Set ℝ} {s₀ s₁ t₀ t₁ : ℝ}
    (hsm : MeasurableSet s) (hss : s ⊆ Icc s₀ s₁) (hsae : s =ᵐ[volume] Icc s₀ s₁)
    (htm : MeasurableSet t) (hts : t ⊆ Icc t₀ t₁) (htae : t =ᵐ[volume] Icc t₀ t₁)
    (hs₀ : 0 ≤ s₀) (hs : s₀ ≤ s₁) (ht₀ : 0 ≤ t₀) (ht : t₀ ≤ t₁) (ht₁ : 0 < t₁)
    (hpos : 0 < s₀ ∨ 0 < t₀) :
    ∫ y in {y : ℝ^2 | y 0 ∈ s ∧ y 1 ∈ t}, hessianKernel 0 0 y =
      (Real.arctan (s₁ / t₁) - Real.arctan (s₀ / t₁)) / 2 -
        (Real.arctan (s₁ / t₀) - Real.arctan (s₀ / t₀)) / 2 := by
  set R := {y : ℝ^2 | y 0 ∈ s ∧ y 1 ∈ t}
  set ρ := max s₀ t₀
  have hρ : 0 < ρ := lt_max_iff.2 hpos
  have hRm : MeasurableSet R := (measurable_coord 0 hsm).inter (measurable_coord 1 htm)
  have hRb : R ⊆ Metric.closedBall (0 : ℝ^2) (s₁ + t₁) := by
    intro y hy
    rw [Metric.mem_closedBall, dist_zero_right]
    have h0 := hss hy.1; have h1 := hts hy.2
    have : ‖y‖ ^ 2 ≤ (s₁ + t₁) ^ 2 := by
      rw [EuclideanSpace.norm_sq_fin_two]; nlinarith [h0.1, h0.2, h1.1, h1.2]
    nlinarith [norm_nonneg y]
  have hR : IntegrableOn (hessianKernel 0 0) R := by
    refine integrableOn_hessianKernel_of_le 0 0 hRm hρ hRb fun y hy ↦ max_le ?_ ?_
    · exact (hss hy.1).1.trans ((le_abs_self _).trans (EuclideanSpace.abs_apply_le_norm y 0))
    · exact (hts hy.2).1.trans ((le_abs_self _).trans (EuclideanSpace.abs_apply_le_norm y 1))
  rw [PDE.Analysis.setIntegral_coordinateProduct hR]
  simp only [hessianKernel_zero_zero_toLp]
  rw [setIntegral_congr_set hsae]
  have hinner : ∀ᵐ p ∂(volume.restrict (Icc s₀ s₁)),
      ∫ q in t, (p ^ 2 - q ^ 2) / (2 * (p ^ 2 + q ^ 2) ^ 2) =
        t₁ / (2 * (p ^ 2 + t₁ ^ 2)) - t₀ / (2 * (p ^ 2 + t₀ ^ 2)) := by
    filter_upwards [ae_restrict_of_ae (Measure.ae_ne volume (0 : ℝ))] with p hp
    rw [setIntegral_congr_set htae]
    exact integral_inner_hessianKernel (Or.inl hp) ht
  rw [integral_congr_ae hinner]
  have hI {c : ℝ} (hc : 0 < c) :
      IntegrableOn (fun p : ℝ ↦ c / (2 * (p ^ 2 + c ^ 2))) (Icc s₀ s₁) :=
    (continuous_const.continuousOn.div (by fun_prop) fun p _ ↦ by positivity).integrableOn_Icc
  rcases eq_or_lt_of_le ht₀ with h0 | h0
  · subst h0
    simp only [zero_div, sub_zero, Real.arctan_zero, div_zero]
    rw [integral_outer_hessianKernel ht₁ hs]
  · rw [integral_sub (hI ht₁) (hI h0), integral_outer_hessianKernel ht₁ hs,
      integral_outer_hessianKernel h0 hs]

/-- **`K₂` over a rectangle in the first quadrant.** For `0 ≤ s₀ ≤ s₁`, `0 ≤ t₀ ≤ t₁`,
`0 < t₁` and `(s₀, t₀) ≠ 0`:
`∫_{[s₀,s₁]×[t₀,t₁]} K₂ = (1/2)(arctan(s₁/t₁) - arctan(s₀/t₁) - arctan(s₁/t₀) + arctan(s₀/t₀))`,
with `arctan(s/0) = 0`. -/
theorem integral_rectangle_hessianKernel_zero_zero {s₀ s₁ t₀ t₁ : ℝ} (hs₀ : 0 ≤ s₀)
    (hs : s₀ ≤ s₁) (ht₀ : 0 ≤ t₀) (ht : t₀ ≤ t₁) (ht₁ : 0 < t₁) (hpos : 0 < s₀ ∨ 0 < t₀) :
    ∫ y in {y : ℝ^2 | y 0 ∈ Icc s₀ s₁ ∧ y 1 ∈ Icc t₀ t₁}, hessianKernel 0 0 y =
      (Real.arctan (s₁ / t₁) - Real.arctan (s₀ / t₁)) / 2 -
        (Real.arctan (s₁ / t₀) - Real.arctan (s₀ / t₀)) / 2 :=
  setIntegral_rectangle_hessianKernel measurableSet_Icc subset_rfl EventuallyEq.rfl
    measurableSet_Icc subset_rfl EventuallyEq.rfl hs₀ hs ht₀ ht ht₁ hpos

/-! ### The corner rectangle -/

/-- The rectangle with opposite corners `0` and `(a, b)`; the signs of `a` and `b` select the
quadrant. -/
def cornerRectangle (a b : ℝ) : Set (ℝ^2) := {y | y 0 ∈ uIcc 0 a ∧ y 1 ∈ uIcc 0 b}

/-- The corner rectangle with corners `0` and `(a, b)` is measurable. -/
theorem measurableSet_cornerRectangle (a b : ℝ) : MeasurableSet (cornerRectangle a b) :=
  (measurable_coord 0 measurableSet_uIcc).inter (measurable_coord 1 measurableSet_uIcc)

/-- For `a, b > 0` the corner rectangle is `[0, a] × [0, b]`. -/
private theorem cornerRectangle_of_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    cornerRectangle a b = {y | y 0 ∈ Icc 0 a ∧ y 1 ∈ Icc 0 b} := by
  simp only [cornerRectangle, uIcc_of_le ha.le, uIcc_of_le hb.le]

/-- A point `x` between `0` and `a` satisfies `|x| ≤ |a|`. -/
private theorem abs_le_abs_of_mem_uIcc {x a : ℝ} (h : x ∈ uIcc 0 a) : |x| ≤ |a| := by
  rw [mem_uIcc] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact abs_le.mpr ⟨by linarith [neg_abs_le a, abs_nonneg a], h2.trans (le_abs_self a)⟩
  · exact abs_le.mpr ⟨(neg_abs_le a).trans h1, by linarith [abs_nonneg a]⟩

/-- The corner rectangle with corners `0` and `(a, b)` lies in the closed disc of radius
`|a| + |b|`. -/
private theorem cornerRectangle_subset_closedBall (a b : ℝ) :
    cornerRectangle a b ⊆ Metric.closedBall 0 (|a| + |b|) := by
  intro y hy
  rw [Metric.mem_closedBall, dist_zero_right]
  have h0 := abs_le_abs_of_mem_uIcc hy.1
  have h1 := abs_le_abs_of_mem_uIcc hy.2
  have : ‖y‖ ^ 2 ≤ (|a| + |b|) ^ 2 := by
    rw [EuclideanSpace.norm_sq_fin_two, ← sq_abs (y 0), ← sq_abs (y 1)]
    nlinarith [abs_nonneg (y 0), abs_nonneg (y 1)]
  nlinarith [norm_nonneg y, abs_nonneg a, abs_nonneg b]

/-- `K₂` is integrable on the part of a corner rectangle lying in a measurable set `P` on which
`|y| ≥ ε > 0`. -/
private theorem integrableOn_hessianKernel_cornerRectangle_inter {P : Set (ℝ^2)}
    (hP : MeasurableSet P) {ε : ℝ} (hε : 0 < ε) (hPε : ∀ y ∈ P, ε ≤ ‖y‖) (a b : ℝ) :
    IntegrableOn (hessianKernel 0 0) (cornerRectangle a b ∩ P) :=
  integrableOn_hessianKernel_of_le 0 0 ((measurableSet_cornerRectangle a b).inter hP) hε
    (inter_subset_left.trans (cornerRectangle_subset_closedBall a b)) fun y hy ↦ hPε y hy.2

/-- The subtracted integrand `K₂ (f - f(0))` is integrable on the corner rectangle. -/
private theorem integrableOn_hessianKernel_mul_sub {a b M α : ℝ} {f : ℝ^2 → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (cornerRectangle a b))) (hα : 0 < α)
    (hhol : ∀ y ∈ cornerRectangle a b, |f y - f 0| ≤ M * ‖y‖ ^ α) :
    IntegrableOn (fun y ↦ hessianKernel 0 0 y * (f y - f 0)) (cornerRectangle a b) := by
  have hpow : IntegrableOn (fun z : ℝ^2 ↦ |M| / 2 * ‖z‖ ^ (α - 2))
      (Metric.ball 0 (|a| + |b| + 1)) := by
    apply integrableOn_ball_of_norm_le_rpow (C := |M| / 2) (α := 2 - α) (by simp)
      (by simp; linarith)
    · filter_upwards with z
      rw [Real.norm_eq_abs, abs_mul, abs_div, abs_two, abs_abs, abs_of_nonneg (Real.rpow_nonneg
        (norm_nonneg z) _), show α - 2 = -(2 - α) by ring]
    · exact (measurable_const.mul (measurable_norm.pow_const _)).aestronglyMeasurable
  have hsub : cornerRectangle a b ⊆ Metric.ball 0 (|a| + |b| + 1) :=
    (cornerRectangle_subset_closedBall a b).trans (Metric.closedBall_subset_ball (by linarith))
  refine (hpow.mono_set hsub).mono'
    ((measurable_hessianKernel 0 0).aestronglyMeasurable.mul
      (hf.sub aestronglyMeasurable_const)) ?_
  filter_upwards [ae_restrict_mem (measurableSet_cornerRectangle a b)] with y hy
  by_cases hy0 : y = 0
  · rw [hy0, sub_self, mul_zero, norm_zero]
    positivity
  have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  rw [Real.norm_eq_abs, abs_mul]
  calc |hessianKernel 0 0 y| * |f y - f 0| ≤ 1 / (2 * ‖y‖ ^ 2) * (|M| * ‖y‖ ^ α) :=
        mul_le_mul (abs_hessianKernel_le 0 0 y)
          ((hhol y hy).trans (mul_le_mul_of_nonneg_right (le_abs_self M) (by positivity)))
          (abs_nonneg _) (by positivity)
    _ = |M| / 2 * ‖y‖ ^ (α - 2) := by
        rw [Real.rpow_sub hn, Real.rpow_two]; field_simp

/-- Dominated convergence for an exhaustion of `Q` by measurable subsets. -/
private theorem tendsto_setIntegral_of_ae_eventually_mem {Q : Set (ℝ^2)} {g : ℝ^2 → ℝ}
    (hg : IntegrableOn g Q) {T : ℝ → Set (ℝ^2)} (hTm : ∀ ε, MeasurableSet (T ε))
    (hTQ : ∀ ε, T ε ⊆ Q) (hmem : ∀ᵐ y ∂(volume.restrict Q), ∀ᶠ ε in 𝓝[>] (0 : ℝ), y ∈ T ε) :
    Tendsto (fun ε ↦ ∫ y in T ε, g y) (𝓝[>] 0) (𝓝 (∫ y in Q, g y)) := by
  have h : ∀ ε, ∫ y in T ε, g y = ∫ y in Q, (T ε).indicator g y := fun ε ↦ by
    rw [setIntegral_indicator (hTm ε), inter_eq_right.mpr (hTQ ε)]
  simp_rw [h]
  refine tendsto_integral_filter_of_dominated_convergence (fun y ↦ ‖g y‖)
    (Eventually.of_forall fun ε ↦ hg.aestronglyMeasurable.indicator (hTm ε))
    (Eventually.of_forall fun ε ↦ ae_of_all _ fun y ↦ norm_indicator_le_norm_self g y)
    hg.norm ?_
  filter_upwards [hmem] with y hy
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hy] with ε hε
  rw [indicator_of_mem hε]

/-- The truncated integrals of `K₂ f` converge to `∫_Q K₂ (f - f(0)) + c f(0)` when the
truncated integrals of `K₂` converge to `c`. -/
private theorem tendsto_setIntegral_hessianKernel_mul {Q : Set (ℝ^2)} {f : ℝ^2 → ℝ}
    (hg : IntegrableOn (fun y ↦ hessianKernel 0 0 y * (f y - f 0)) Q) {T : ℝ → Set (ℝ^2)}
    (hTm : ∀ ε, MeasurableSet (T ε)) (hTQ : ∀ ε, T ε ⊆ Q)
    (hmem : ∀ᵐ y ∂(volume.restrict Q), ∀ᶠ ε in 𝓝[>] (0 : ℝ), y ∈ T ε)
    (hK : ∀ᶠ ε in 𝓝[>] (0 : ℝ), IntegrableOn (hessianKernel 0 0) (T ε)) {c : ℝ}
    (hc : Tendsto (fun ε ↦ ∫ y in T ε, hessianKernel 0 0 y) (𝓝[>] 0) (𝓝 c)) :
    Tendsto (fun ε ↦ ∫ y in T ε, hessianKernel 0 0 y * f y) (𝓝[>] 0)
      (𝓝 ((∫ y in Q, hessianKernel 0 0 y * (f y - f 0)) + c * f 0)) := by
  refine ((tendsto_setIntegral_of_ae_eventually_mem hg hTm hTQ hmem).add
    (hc.mul_const (f 0))).congr' ?_
  filter_upwards [hK] with ε hε
  rw [← integral_mul_const, ← integral_add (hg.mono_set (hTQ ε)) (hε.mul_const _)]
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  simp only
  ring

/-! ### Symmetries of the truncations -/

local notation "𝐑" => PDE.Common.coordinateReflection

/-- A coordinate reflection preserves the absolute value of every coordinate. -/
private theorem abs_coordinateReflection_apply (k i : Fin 2) (y : ℝ^2) : |𝐑 k y i| = |y i| := by
  by_cases h : i = k
  · subst h; rw [PDE.Common.coordinateReflection_apply_same, abs_neg]
  · rw [PDE.Common.coordinateReflection_apply_of_ne k i h]

/-- `-x` lies between `0` and `a` if and only if `x` lies between `0` and `-a`. -/
private theorem neg_mem_uIcc_zero {x a : ℝ} : -x ∈ uIcc 0 a ↔ x ∈ uIcc 0 (-a) := by
  rw [mem_uIcc, mem_uIcc]
  constructor <;> rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
  all_goals first
    | exact Or.inl ⟨by linarith, by linarith⟩
    | exact Or.inr ⟨by linarith, by linarith⟩

/-- The reflection `y₀ ↦ -y₀` maps the corner rectangle of `(a, b)` to that of `(-a, b)`. -/
private theorem preimage_reflection_cornerRectangle_zero (a b : ℝ) :
    𝐑 0 ⁻¹' cornerRectangle a b = cornerRectangle (-a) b := by
  ext y
  simp only [cornerRectangle, mem_preimage, mem_ofPred_eq,
    PDE.Common.coordinateReflection_apply_same,
    PDE.Common.coordinateReflection_apply_of_ne (n := 2) 0 1 (by decide), neg_mem_uIcc_zero]

/-- The reflection `y₁ ↦ -y₁` maps the corner rectangle of `(a, b)` to that of `(a, -b)`. -/
private theorem preimage_reflection_cornerRectangle_one (a b : ℝ) :
    𝐑 1 ⁻¹' cornerRectangle a b = cornerRectangle a (-b) := by
  ext y
  simp only [cornerRectangle, mem_preimage, mem_ofPred_eq,
    PDE.Common.coordinateReflection_apply_same,
    PDE.Common.coordinateReflection_apply_of_ne (n := 2) 1 0 (by decide), neg_mem_uIcc_zero]

/-- Integrals of `K₂` over a corner rectangle cut by a reflection invariant set depend only on
`|a|` and `|b|`. -/
private theorem setIntegral_hessianKernel_cornerRectangle_abs {P : Set (ℝ^2)}
    (hP : ∀ k y, 𝐑 k y ∈ P ↔ y ∈ P) (a b : ℝ) :
    ∫ y in cornerRectangle a b ∩ P, hessianKernel 0 0 y =
      ∫ y in cornerRectangle |a| |b| ∩ P, hessianKernel 0 0 y := by
  have h0 : ∀ a b, ∫ y in cornerRectangle a b ∩ P, hessianKernel 0 0 y =
      ∫ y in cornerRectangle (-a) b ∩ P, hessianKernel 0 0 y := by
    intro a b
    rw [← GreenFunction.setIntegral_preimage_coordinateReflection 0 (cornerRectangle a b ∩ P)
        (hessianKernel 0 0),
      preimage_inter, preimage_reflection_cornerRectangle_zero, show 𝐑 0 ⁻¹' P = P from
        Set.ext (hP 0)]
    simp only [hessianKernel_zero_zero_coordinateReflection]
  have h1 : ∀ a b, ∫ y in cornerRectangle a b ∩ P, hessianKernel 0 0 y =
      ∫ y in cornerRectangle a (-b) ∩ P, hessianKernel 0 0 y := by
    intro a b
    rw [← GreenFunction.setIntegral_preimage_coordinateReflection 1 (cornerRectangle a b ∩ P)
        (hessianKernel 0 0),
      preimage_inter, preimage_reflection_cornerRectangle_one, show 𝐑 1 ⁻¹' P = P from
        Set.ext (hP 1)]
    simp only [hessianKernel_zero_zero_coordinateReflection]
  rcases le_or_gt 0 a with ha | ha <;> rcases le_or_gt 0 b with hb | hb
  · rw [abs_of_nonneg ha, abs_of_nonneg hb]
  · rw [abs_of_nonneg ha, abs_of_neg hb, h1]
  · rw [abs_of_neg ha, abs_of_nonneg hb, h0]
  · rw [abs_of_neg ha, abs_of_neg hb, h0, h1]

/-- An integral of `K₂` over a set invariant under the coordinate swap vanishes. -/
private theorem setIntegral_hessianKernel_eq_zero_of_swap {S : Set (ℝ^2)}
    (hS : ∀ y, LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin 2) 1) y ∈ S ↔
      y ∈ S) :
    ∫ y in S, hessianKernel 0 0 y = 0 := by
  have h := (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    (Equiv.swap (0 : Fin 2) 1)).measurePreserving.setIntegral_preimage_emb
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      (Equiv.swap (0 : Fin 2) 1)).toMeasurableEquiv.measurableEmbedding (hessianKernel 0 0) S
  rw [show (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin 2) 1)) ⁻¹' S = S from
    Set.ext hS] at h
  simp only [hessianKernel_zero_zero_swap, integral_neg] at h
  linarith

/-! ### The constant parts -/

section Positive

variable {a b ε : ℝ}

/-- For `0 < ε ≤ a` and `b > 0`, the integral of `K₂` over `[0, a] × [0, b]` outside the strip
`|y₀| < ε` is `(arctan(a/b) - arctan(ε/b)) / 2`. -/
private theorem integral_strip_zero (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε) (hεa : ε ≤ a) :
    ∫ y in cornerRectangle a b ∩ {y | ε ≤ |y 0|}, hessianKernel 0 0 y =
      (Real.arctan (a / b) - Real.arctan (ε / b)) / 2 := by
  have hset : cornerRectangle a b ∩ {y | ε ≤ |y 0|} =
      {y : ℝ^2 | y 0 ∈ Icc ε a ∧ y 1 ∈ Icc 0 b} := by
    ext y
    simp only [cornerRectangle_of_pos ha hb, mem_inter_iff, mem_ofPred_eq, mem_Icc]
    constructor
    · rintro ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩
      rw [abs_of_nonneg h0] at h3
      exact ⟨⟨h3, h1⟩, h2⟩
    · rintro ⟨⟨h0, h1⟩, h2⟩
      exact ⟨⟨⟨by linarith, h1⟩, h2⟩, by rw [abs_of_nonneg (by linarith)]; exact h0⟩
  rw [hset, integral_rectangle_hessianKernel_zero_zero hε.le hεa le_rfl hb.le hb (Or.inl hε)]
  simp only [div_zero, Real.arctan_zero, sub_self, zero_div, sub_zero]

/-- For `0 < ε ≤ b` and `a > 0`, the integral of `K₂` over `[0, a] × [0, b]` outside the strip
`|y₁| < ε` is `(arctan(a/b) - arctan(a/ε)) / 2`. -/
private theorem integral_strip_one (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε) (hεb : ε ≤ b) :
    ∫ y in cornerRectangle a b ∩ {y | ε ≤ |y 1|}, hessianKernel 0 0 y =
      (Real.arctan (a / b) - Real.arctan (a / ε)) / 2 := by
  have hset : cornerRectangle a b ∩ {y | ε ≤ |y 1|} =
      {y : ℝ^2 | y 0 ∈ Icc 0 a ∧ y 1 ∈ Icc ε b} := by
    ext y
    simp only [cornerRectangle_of_pos ha hb, mem_inter_iff, mem_ofPred_eq, mem_Icc]
    constructor
    · rintro ⟨⟨h0, ⟨h1, h2⟩⟩, h3⟩
      rw [abs_of_nonneg h1] at h3
      exact ⟨h0, ⟨h3, h2⟩⟩
    · rintro ⟨h0, ⟨h1, h2⟩⟩
      exact ⟨⟨h0, ⟨by linarith, h2⟩⟩, by rw [abs_of_nonneg (by linarith)]; exact h1⟩
  rw [hset, integral_rectangle_hessianKernel_zero_zero le_rfl ha.le hε.le hεb hb (Or.inr hε)]
  simp only [zero_div, Real.arctan_zero, sub_zero]
  ring

/-- For `0 < ε ≤ a, b`, the integral of `K₂` over `[0, a] × [0, b]` outside the corner square
`|y₀|, |y₁| < ε` is `arctan(a/b)/2 - π/8`. -/
private theorem integral_square (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε) (hεa : ε ≤ a)
    (hεb : ε ≤ b) :
    ∫ y in cornerRectangle a b ∩ {y | ε ≤ |y 0| ∨ ε ≤ |y 1|}, hessianKernel 0 0 y =
      Real.arctan (a / b) / 2 - Real.pi / 8 := by
  set A := {y : ℝ^2 | y 0 ∈ Icc ε a ∧ y 1 ∈ Icc 0 b}
  set C := {y : ℝ^2 | y 0 ∈ Ico 0 ε ∧ y 1 ∈ Icc ε b}
  have hset : cornerRectangle a b ∩ {y | ε ≤ |y 0| ∨ ε ≤ |y 1|} = A ∪ C := by
    ext y
    simp only [cornerRectangle_of_pos ha hb, mem_inter_iff, mem_ofPred_eq, mem_union, mem_Icc,
      mem_Ico, A, C]
    constructor
    · rintro ⟨⟨⟨h0, h1⟩, ⟨h2, h3⟩⟩, h4⟩
      rw [abs_of_nonneg h0, abs_of_nonneg h2] at h4
      by_cases h : ε ≤ y 0
      · exact Or.inl ⟨⟨h, h1⟩, ⟨h2, h3⟩⟩
      · exact Or.inr ⟨⟨h0, not_le.mp h⟩, ⟨h4.resolve_left h, h3⟩⟩
    · rintro (⟨⟨h0, h1⟩, ⟨h2, h3⟩⟩ | ⟨⟨h0, h1⟩, ⟨h2, h3⟩⟩)
      · exact ⟨⟨⟨by linarith, h1⟩, ⟨h2, h3⟩⟩,
          Or.inl (by rw [abs_of_nonneg (by linarith)]; exact h0)⟩
      · exact ⟨⟨⟨h0, by linarith⟩, ⟨by linarith, h3⟩⟩,
          Or.inr (by rw [abs_of_nonneg (by linarith)]; exact h2)⟩
  have hsub : A ∪ C ⊆ cornerRectangle a b ∩ {y | ε ≤ |y 0| ∨ ε ≤ |y 1|} := hset.ge
  have hint : IntegrableOn (hessianKernel 0 0) (A ∪ C) := by
    refine (integrableOn_hessianKernel_cornerRectangle_inter ?_ hε ?_ a b).mono_set hsub
    · exact measurableSet_le measurable_const (measurable_abs_coord 0) |>.union
        (measurableSet_le measurable_const (measurable_abs_coord 1))
    · exact fun y hy ↦ hy.elim (·.trans (EuclideanSpace.abs_apply_le_norm y 0))
        (·.trans (EuclideanSpace.abs_apply_le_norm y 1))
  have hdisj : Disjoint A C :=
    Set.disjoint_left.mpr fun y hA hC ↦ (hC.1.2.trans_le hA.1.1).false
  have hCm : MeasurableSet C := (measurable_coord 0 measurableSet_Ico).inter
    (measurable_coord 1 measurableSet_Icc)
  rw [hset, setIntegral_union hdisj hCm (hint.mono_set subset_union_left)
    (hint.mono_set subset_union_right),
    integral_rectangle_hessianKernel_zero_zero hε.le hεa le_rfl hb.le hb (Or.inl hε),
    setIntegral_rectangle_hessianKernel measurableSet_Ico Ico_subset_Icc_self Ico_ae_eq_Icc
      measurableSet_Icc subset_rfl EventuallyEq.rfl le_rfl hε.le hε.le hεb hb (Or.inr hε),
    div_self hε.ne', Real.arctan_one]
  simp only [div_zero, Real.arctan_zero, zero_div, sub_zero]
  ring

/-- For `0 < ε < min a b`, the integral of `K₂` over `[0, a] × [0, b]` outside the disc `|y| ≤ ε` is
also `arctan(a/b)/2 - π/8`. -/
private theorem integral_disc (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε) (hεm : ε < min a b) :
    ∫ y in cornerRectangle a b ∩ {y | ε < ‖0 - y‖}, hessianKernel 0 0 y =
      Real.arctan (a / b) / 2 - Real.pi / 8 := by
  set m := min a b
  have hm : 0 < m := lt_min ha hb
  set Sq := cornerRectangle m m with hSqdef
  have hSqm : MeasurableSet Sq := measurableSet_cornerRectangle m m
  have hSq : Sq ⊆ cornerRectangle a b := by
    intro y hy
    rw [hSqdef, cornerRectangle_of_pos hm hm] at hy
    rw [cornerRectangle_of_pos ha hb]
    exact ⟨⟨hy.1.1, hy.1.2.trans (min_le_left _ _)⟩, ⟨hy.2.1, hy.2.2.trans (min_le_right _ _)⟩⟩
  -- outside the small square both truncations keep everything
  have hout : ∀ y ∈ cornerRectangle a b \ Sq, m < |y 0| ∨ m < |y 1| := by
    rintro y ⟨hy, hyS⟩
    rw [cornerRectangle_of_pos ha hb] at hy
    rw [abs_of_nonneg hy.1.1, abs_of_nonneg hy.2.1]
    by_contra h
    simp only [not_or, not_lt] at h
    exact hyS (by rw [hSqdef, cornerRectangle_of_pos hm hm]; exact ⟨⟨hy.1.1, h.1⟩, ⟨hy.2.1, h.2⟩⟩)
  have hdiff : ∀ {P : Set (ℝ^2)}, (∀ y ∈ cornerRectangle a b \ Sq, y ∈ P) →
      (cornerRectangle a b ∩ P) \ Sq = cornerRectangle a b \ Sq := fun hP ↦
    Set.ext fun y ↦ ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, hP y h⟩, h.2⟩⟩
  have hinter : ∀ {P : Set (ℝ^2)}, (cornerRectangle a b ∩ P) ∩ Sq = P ∩ Sq :=
    Set.ext fun y ↦ ⟨fun h ↦ ⟨h.1.2, h.2⟩, fun h ↦ ⟨⟨hSq h.2, h.1⟩, h.2⟩⟩
  have hSqswap : ∀ y, LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin 2) 1) y ∈ Sq ↔
      y ∈ Sq := by
    intro y
    obtain ⟨h0, h1⟩ := coordinateSwap_apply y
    simp only [Sq, cornerRectangle, mem_ofPred_eq, h0, h1]
    exact and_comm
  have hDm : MeasurableSet {y : ℝ^2 | ε < ‖0 - y‖} :=
    measurableSet_lt measurable_const (measurable_const.sub measurable_id).norm
  have hSm : MeasurableSet {y : ℝ^2 | ε ≤ |y 0| ∨ ε ≤ |y 1|} :=
    (measurableSet_le measurable_const (measurable_abs_coord 0)).union
      (measurableSet_le measurable_const (measurable_abs_coord 1))
  have hDint := integrableOn_hessianKernel_cornerRectangle_inter hDm hε
    (fun y (hy : ε < ‖0 - y‖) ↦ by rw [zero_sub, norm_neg] at hy; exact hy.le) a b
  have hSint := integrableOn_hessianKernel_cornerRectangle_inter hSm hε (fun y hy ↦
    hy.elim (·.trans (EuclideanSpace.abs_apply_le_norm y 0))
      (·.trans (EuclideanSpace.abs_apply_le_norm y 1))) a b
  have hD : ∫ y in cornerRectangle a b ∩ {y | ε < ‖0 - y‖}, hessianKernel 0 0 y =
      ∫ y in cornerRectangle a b \ Sq, hessianKernel 0 0 y := by
    rw [← integral_inter_add_sdiff hSqm hDint, hinter,
      setIntegral_hessianKernel_eq_zero_of_swap, zero_add, hdiff]
    · intro y hy
      simp only [mem_ofPred_eq, zero_sub, norm_neg]
      rcases hout y hy with h | h <;>
        linarith [EuclideanSpace.abs_apply_le_norm y 0, EuclideanSpace.abs_apply_le_norm y 1]
    · intro y
      simp only [mem_inter_iff, mem_ofPred_eq, zero_sub, norm_neg, LinearIsometryEquiv.norm_map,
        hSqswap]
  have hS : ∫ y in cornerRectangle a b ∩ {y | ε ≤ |y 0| ∨ ε ≤ |y 1|}, hessianKernel 0 0 y =
      ∫ y in cornerRectangle a b \ Sq, hessianKernel 0 0 y := by
    rw [← integral_inter_add_sdiff hSqm hSint, hinter,
      setIntegral_hessianKernel_eq_zero_of_swap, zero_add, hdiff]
    · exact fun y hy ↦ (hout y hy).imp (fun h ↦ by linarith) fun h ↦ by linarith
    · intro y
      obtain ⟨h0, h1⟩ := coordinateSwap_apply y
      simp only [mem_inter_iff, mem_ofPred_eq, h0, h1, hSqswap]
      rw [or_comm]
  rw [hD, ← hS, integral_square ha hb hε (hεm.le.trans (min_le_left _ _))
    (hεm.le.trans (min_le_right _ _))]

end Positive

/-! ### The truncations -/

/-- Almost every point of the plane has nonzero coordinate `y k`. -/
private theorem ae_coordinate_ne_zero (k : Fin 2) : ∀ᵐ y : ℝ^2, y k ≠ 0 := by
  rw [ae_iff]
  simpa using GreenFunction.volume_coordinate_eq_zero k

/-- The complement `{ε ≤ |y k|}` of a coordinate strip is measurable. -/
private theorem measurableSet_strip (k : Fin 2) (ε : ℝ) :
    MeasurableSet {y : ℝ^2 | ε ≤ |y k|} :=
  measurableSet_le measurable_const (measurable_abs_coord k)

/-- The complement `{ε ≤ |y₀|} ∪ {ε ≤ |y₁|}` of the corner square is measurable. -/
private theorem measurableSet_square (ε : ℝ) :
    MeasurableSet {y : ℝ^2 | ε ≤ |y 0| ∨ ε ≤ |y 1|} :=
  (measurableSet_strip 0 ε).union (measurableSet_strip 1 ε)

/-- The complement `{ε < |y|}` of the closed disc is measurable. -/
private theorem measurableSet_disc (ε : ℝ) : MeasurableSet {y : ℝ^2 | ε < ‖0 - y‖} :=
  measurableSet_lt measurable_const (measurable_const.sub measurable_id).norm

/-- The set `{ε ≤ |y k|}` is invariant under each coordinate reflection. -/
private theorem reflect_strip (k : Fin 2) (ε : ℝ) (i : Fin 2) (y : ℝ^2) :
    𝐑 i y ∈ {y : ℝ^2 | ε ≤ |y k|} ↔ y ∈ {y : ℝ^2 | ε ≤ |y k|} := by
  simp only [mem_ofPred_eq, abs_coordinateReflection_apply]

/-- The set `{ε ≤ |y₀|} ∪ {ε ≤ |y₁|}` is invariant under each coordinate reflection. -/
private theorem reflect_square (ε : ℝ) (i : Fin 2) (y : ℝ^2) :
    𝐑 i y ∈ {y : ℝ^2 | ε ≤ |y 0| ∨ ε ≤ |y 1|} ↔ y ∈ {y : ℝ^2 | ε ≤ |y 0| ∨ ε ≤ |y 1|} := by
  simp only [mem_ofPred_eq, abs_coordinateReflection_apply]

/-- The set `{ε < |y|}` is invariant under each coordinate reflection. -/
private theorem reflect_disc (ε : ℝ) (i : Fin 2) (y : ℝ^2) :
    𝐑 i y ∈ {y : ℝ^2 | ε < ‖0 - y‖} ↔ y ∈ {y : ℝ^2 | ε < ‖0 - y‖} := by
  simp only [mem_ofPred_eq, zero_sub, norm_neg, PDE.Common.norm_coordinateReflection]

/-! ### Lemma B.1 -/

variable {a b M α : ℝ} {f : ℝ^2 → ℝ}

/-- **Lemma B.1, square truncation.** For `a, b ≠ 0` and `f` Hölder continuous at `0` on the
corner rectangle `Q` (`|f(y) - f(0)| ≤ M |y|^α`, `α > 0`), the integrals of `K₂ f` over `Q`
without the corner square `|y₀|, |y₁| < ε` converge to
`∫_Q K₂ (f - f(0)) + ((1/2) arctan(|a|/|b|) - π/8) f(0)`. -/
theorem tendsto_setIntegral_hessianKernel_cornerRectangle (ha : a ≠ 0) (hb : b ≠ 0)
    (hf : AEStronglyMeasurable f (volume.restrict (cornerRectangle a b))) (hα : 0 < α)
    (hhol : ∀ y ∈ cornerRectangle a b, |f y - f 0| ≤ M * ‖y‖ ^ α) :
    Tendsto (fun ε ↦ ∫ y in cornerRectangle a b ∩ {y | ε ≤ |y 0| ∨ ε ≤ |y 1|},
        hessianKernel 0 0 y * f y) (𝓝[>] 0)
      (𝓝 ((∫ y in cornerRectangle a b, hessianKernel 0 0 y * (f y - f 0)) +
        (Real.arctan (|a| / |b|) / 2 - Real.pi / 8) * f 0)) := by
  have ha' := abs_pos.mpr ha
  have hb' := abs_pos.mpr hb
  refine tendsto_setIntegral_hessianKernel_mul (integrableOn_hessianKernel_mul_sub hf hα hhol)
    (fun ε ↦ (measurableSet_cornerRectangle a b).inter (measurableSet_square ε))
    (fun ε ↦ inter_subset_left) ?_ ?_ ?_
  · filter_upwards [ae_restrict_of_ae (ae_coordinate_ne_zero 0),
      ae_restrict_mem (measurableSet_cornerRectangle a b)] with y hy hyQ
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds
      (eventually_le_nhds (abs_pos.mpr hy))] with ε hε
    exact ⟨hyQ, Or.inl hε⟩
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    refine integrableOn_hessianKernel_cornerRectangle_inter (measurableSet_square ε) hε ?_ a b
    rintro y (h | h)
    · exact h.trans (EuclideanSpace.abs_apply_le_norm y 0)
    · exact h.trans (EuclideanSpace.abs_apply_le_norm y 1)
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
      (eventually_le_nhds (lt_min ha' hb'))] with ε (hε : 0 < ε) hεm
    rw [setIntegral_hessianKernel_cornerRectangle_abs (reflect_square ε),
      integral_square ha' hb' hε (hεm.trans (min_le_left _ _)) (hεm.trans (min_le_right _ _))]

/-- **Lemma B.1, strip `|y₀| ≥ ε`.** Under the measurability and Hölder hypotheses of
`tendsto_setIntegral_hessianKernel_cornerRectangle`, with the rectangle possibly degenerate,
removing the strip `|y₀| < ε` gives the limit `∫_Q K₂ (f - f(0)) + (1/2) arctan(|a|/|b|) f(0)`.
For `a ≠ 0` and `b ≠ 0` this is the principal value plus `(π/8) f(0)`. -/
theorem tendsto_setIntegral_hessianKernel_cornerRectangle_strip_zero
    (hf : AEStronglyMeasurable f (volume.restrict (cornerRectangle a b))) (hα : 0 < α)
    (hhol : ∀ y ∈ cornerRectangle a b, |f y - f 0| ≤ M * ‖y‖ ^ α) :
    Tendsto (fun ε ↦ ∫ y in cornerRectangle a b ∩ {y | ε ≤ |y 0|}, hessianKernel 0 0 y * f y)
      (𝓝[>] 0)
      (𝓝 ((∫ y in cornerRectangle a b, hessianKernel 0 0 y * (f y - f 0)) +
        (Real.arctan (|a| / |b|) / 2 - Real.pi / 8) * f 0 + Real.pi / 8 * f 0)) := by
  by_cases hab : a = 0 ∨ b = 0
  · -- a degenerate rectangle is null and the constant vanishes
    have hnull : volume (cornerRectangle a b) = 0 := by
      rcases hab with rfl | rfl
      · exact measure_mono_null (fun y hy ↦ by simpa using hy.1)
          (GreenFunction.volume_coordinate_eq_zero 0)
      · exact measure_mono_null (fun y hy ↦ by simpa using hy.2)
          (GreenFunction.volume_coordinate_eq_zero 1)
    have hμ : volume.restrict (cornerRectangle a b) = 0 := Measure.restrict_eq_zero.mpr hnull
    have hμ' (ε : ℝ) : volume.restrict (cornerRectangle a b ∩ {y | ε ≤ |y 0|}) = 0 :=
      Measure.restrict_eq_zero.mpr (measure_mono_null inter_subset_left hnull)
    simp only [hμ, hμ', integral_zero_measure, zero_add]
    convert tendsto_const_nhds using 2
    rcases hab with rfl | rfl <;> simp
  push Not at hab
  obtain ⟨ha, hb⟩ := hab
  have ha' := abs_pos.mpr ha
  have hb' := abs_pos.mpr hb
  have hlim : Tendsto (fun ε : ℝ ↦ (Real.arctan (|a| / |b|) - Real.arctan (ε / |b|)) / 2)
      (𝓝[>] 0) (𝓝 (Real.arctan (|a| / |b|) / 2)) := by
    have hc : Continuous fun ε : ℝ ↦ (Real.arctan (|a| / |b|) - Real.arctan (ε / |b|)) / 2 :=
      (continuous_const.sub (Real.continuous_arctan.comp (continuous_id.div_const _))).div_const 2
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have h := tendsto_setIntegral_hessianKernel_mul (integrableOn_hessianKernel_mul_sub hf hα hhol)
    (fun ε ↦ (measurableSet_cornerRectangle a b).inter (measurableSet_strip 0 ε))
    (fun ε ↦ inter_subset_left) ?_ ?_ (hlim.congr' ?_)
  · convert h using 2
    ring
  · filter_upwards [ae_restrict_of_ae (ae_coordinate_ne_zero 0),
      ae_restrict_mem (measurableSet_cornerRectangle a b)] with y hy hyQ
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds
      (eventually_le_nhds (abs_pos.mpr hy))] with ε hε
    exact ⟨hyQ, hε⟩
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact integrableOn_hessianKernel_cornerRectangle_inter (measurableSet_strip 0 ε) hε
      (fun y h ↦ h.trans (EuclideanSpace.abs_apply_le_norm y 0)) a b
  · filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
      (eventually_le_nhds ha')] with ε (hε : 0 < ε) hεa
    rw [setIntegral_hessianKernel_cornerRectangle_abs (reflect_strip 0 ε),
      integral_strip_zero ha' hb' hε hεa]

/-- **Lemma B.1, strip `|y₁| ≥ ε`.** Under the hypotheses of
`tendsto_setIntegral_hessianKernel_cornerRectangle`, removing the strip `|y₁| < ε` gives the
principal value minus `(π/8) f(0)`. -/
theorem tendsto_setIntegral_hessianKernel_cornerRectangle_strip_one (ha : a ≠ 0) (hb : b ≠ 0)
    (hf : AEStronglyMeasurable f (volume.restrict (cornerRectangle a b))) (hα : 0 < α)
    (hhol : ∀ y ∈ cornerRectangle a b, |f y - f 0| ≤ M * ‖y‖ ^ α) :
    Tendsto (fun ε ↦ ∫ y in cornerRectangle a b ∩ {y | ε ≤ |y 1|}, hessianKernel 0 0 y * f y)
      (𝓝[>] 0)
      (𝓝 ((∫ y in cornerRectangle a b, hessianKernel 0 0 y * (f y - f 0)) +
        (Real.arctan (|a| / |b|) / 2 - Real.pi / 8) * f 0 - Real.pi / 8 * f 0)) := by
  have ha' := abs_pos.mpr ha
  have hb' := abs_pos.mpr hb
  have hlim : Tendsto (fun ε : ℝ ↦ (Real.arctan (|a| / |b|) - Real.arctan (|a| / ε)) / 2)
      (𝓝[>] 0) (𝓝 ((Real.arctan (|a| / |b|) - Real.pi / 2) / 2)) := by
    have h1 : Tendsto (fun ε : ℝ ↦ |a| / ε) (𝓝[>] 0) atTop := by
      simp_rw [div_eq_mul_inv]
      exact Tendsto.const_mul_atTop ha' tendsto_inv_nhdsGT_zero
    have h2 : Tendsto (fun ε : ℝ ↦ Real.arctan (|a| / ε)) (𝓝[>] 0) (𝓝 (Real.pi / 2)) :=
      (Real.tendsto_arctan_atTop.comp h1).mono_right nhdsWithin_le_nhds
    exact (tendsto_const_nhds.sub h2).div_const 2
  have h := tendsto_setIntegral_hessianKernel_mul (integrableOn_hessianKernel_mul_sub hf hα hhol)
    (fun ε ↦ (measurableSet_cornerRectangle a b).inter (measurableSet_strip 1 ε))
    (fun ε ↦ inter_subset_left) ?_ ?_ (hlim.congr' ?_)
  · convert h using 2
    ring
  · filter_upwards [ae_restrict_of_ae (ae_coordinate_ne_zero 1),
      ae_restrict_mem (measurableSet_cornerRectangle a b)] with y hy hyQ
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds
      (eventually_le_nhds (abs_pos.mpr hy))] with ε hε
    exact ⟨hyQ, hε⟩
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact integrableOn_hessianKernel_cornerRectangle_inter (measurableSet_strip 1 ε) hε
      (fun y h ↦ h.trans (EuclideanSpace.abs_apply_le_norm y 1)) a b
  · filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
      (eventually_le_nhds hb')] with ε (hε : 0 < ε) hεb
    rw [setIntegral_hessianKernel_cornerRectangle_abs (reflect_strip 1 ε),
      integral_strip_one ha' hb' hε hεb]

/-- **Lemma B.1, disc truncation.** Under the hypotheses of
`tendsto_setIntegral_hessianKernel_cornerRectangle`, the disc-truncated principal value of
`∫_Q K₂ f` at the corner exists and equals the square-truncated one. -/
theorem hasPrincipalValueAt_hessianKernel_cornerRectangle (ha : a ≠ 0) (hb : b ≠ 0)
    (hf : AEStronglyMeasurable f (volume.restrict (cornerRectangle a b))) (hα : 0 < α)
    (hhol : ∀ y ∈ cornerRectangle a b, |f y - f 0| ≤ M * ‖y‖ ^ α) :
    PDE.Analysis.HasPrincipalValueAt (cornerRectangle a b)
      (fun x y ↦ hessianKernel 0 0 (x - y)) f 0
      ((∫ y in cornerRectangle a b, hessianKernel 0 0 y * (f y - f 0)) +
        (Real.arctan (|a| / |b|) / 2 - Real.pi / 8) * f 0) := by
  have ha' := abs_pos.mpr ha
  have hb' := abs_pos.mpr hb
  have hg := integrableOn_hessianKernel_mul_sub hf hα hhol
  have hdisc : ∀ ε, 0 < ε → ∀ y ∈ {y : ℝ^2 | ε < ‖0 - y‖}, ε ≤ ‖y‖ :=
    fun ε _ y (hy : ε < ‖0 - y‖) ↦ by simpa using hy.le
  refine ⟨?_, ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    have hK := integrableOn_hessianKernel_cornerRectangle_inter (measurableSet_disc ε) hε
      (hdisc ε hε) a b
    refine ((hg.mono_set inter_subset_left).add (hK.mul_const (f 0))).congr_fun
      (fun y _ ↦ ?_) ((measurableSet_cornerRectangle a b).inter (measurableSet_disc ε))
    change hessianKernel 0 0 y * (f y - f 0) + hessianKernel 0 0 y * f 0 =
      hessianKernel 0 0 (0 - y) * f y
    rw [zero_sub, hessianKernel_neg]
    ring
  · have h := tendsto_setIntegral_hessianKernel_mul hg
      (fun ε ↦ (measurableSet_cornerRectangle a b).inter (measurableSet_disc ε))
      (fun ε ↦ inter_subset_left) ?_ ?_ (c := Real.arctan (|a| / |b|) / 2 - Real.pi / 8)
      (tendsto_const_nhds.congr' ?_)
    · refine h.congr' (Eventually.of_forall fun ε ↦ ?_)
      simp only [PDE.Analysis.principalValueTruncation, zero_sub, hessianKernel_neg]
    · filter_upwards [ae_restrict_of_ae (ae_coordinate_ne_zero 0),
        ae_restrict_mem (measurableSet_cornerRectangle a b)] with y hy hyQ
      have hn : 0 < ‖0 - y‖ := by
        simpa using (abs_pos.mpr hy).trans_le (EuclideanSpace.abs_apply_le_norm y 0)
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hn)]
        with ε hε
      exact ⟨hyQ, hε⟩
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      exact integrableOn_hessianKernel_cornerRectangle_inter (measurableSet_disc ε) hε
        (hdisc ε hε) a b
    · filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
        (eventually_lt_nhds (lt_min ha' hb'))] with ε (hε : 0 < ε) hεm
      rw [setIntegral_hessianKernel_cornerRectangle_abs (reflect_disc ε),
        integral_disc ha' hb' hε hεm]

end PotentialTheory.Planar
