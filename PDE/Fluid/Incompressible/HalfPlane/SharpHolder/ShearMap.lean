/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Scalar.DepressedCubic
public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.ShearKernel

/-!
# The vertical transport map of the horizontal Hölder estimates of `u_y` and `v_x`

For fixed `y₁ > 0`, `y₁ ≠ 1`, the vertical transport map `T(y₁, y₂)` of Chen and Hou, Part I,
(B.17) and (B.66), pairs `y₂ > 0` with the point on the other side of the sign threshold
`s_c(y₁)` at which the primitive `Ψ(t) = (1/2)(t/((y₁ + 1)² + t²) - t/((y₁ - 1)² + t²))` of
`Δ(y₁, ·)` takes the same value. Clearing denominators, `Ψ(T) = Ψ(y₂)` with `T ≠ y₂` is the cubic
(B.66)

`T³ + T² y₂ + T (y₂² + 2 + 2 y₁²) - (y₁² - 1)² / y₂ = 0`

(`shearCubic`), whose linear coefficient is positive, so it has exactly one real root, given by
Cardano's formula (`shearMap`).

## Main results

* `shearCubic_shearMap`, `eq_shearMap_of_shearCubic_eq_zero`, `shearMap_pos`: `T` is the unique
  real root, and it is positive for `y₁² ≠ 1`.
* `shearPotential_shearMap`: `Ψ(T) = Ψ(y₂)`, the mass equation (B.17).
* `shearMap_shearThreshold`: `s_c(y₁)` is the fixed point.
* Part II, Supplement, Lemma 5.5: `strictAntiOn_shearMap_right` (`T` decreases in `y₂`),
  `antitoneOn_shearMap_left` (`T` decreases in `y₁ ∈ (0, 1]`) and `monotoneOn_shearMap_left`
  (`T` increases in `y₁ ≥ 1`).
* `measurable_shearMap`: joint measurability.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Appendix B.1.2, (B.17) and (B.18),
  p. 132, and Appendix B.3, (B.62) and (B.66), pp. 141-142.
  <https://arxiv.org/abs/2210.07191v4>
* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Supplementary material II,
  Section 5.4, Lemma 5.5, p. 12.
  <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public section

noncomputable section

open Set Filter PDE.Analysis.Scalar
open scoped Topology

namespace IncompressibleFlow.SharpHolder

/-- The cubic (B.66) of Chen and Hou, Part I, in the variable `T`:
`T³ + T² y₂ + T (y₂² + 2 + 2 y₁²) - (y₁² - 1)² / y₂`. -/
def shearCubic (y₁ y₂ T : ℝ) : ℝ :=
  T ^ 3 + T ^ 2 * y₂ + T * (y₂ ^ 2 + 2 + 2 * y₁ ^ 2) - (y₁ ^ 2 - 1) ^ 2 / y₂

/-- The coefficient `p = (2/3) y₂² + 2 + 2 y₁²` of the depressed form of (B.66). -/
def shearMapCoeffP (y₁ y₂ : ℝ) : ℝ :=
  2 / 3 * y₂ ^ 2 + 2 + 2 * y₁ ^ 2

/-- The coefficient `q = -((y₁² - 1)² / y₂ + y₂³/27 + (y₂/3)((2/3) y₂² + 2 + 2 y₁²))` of the
depressed form of (B.66). -/
def shearMapCoeffQ (y₁ y₂ : ℝ) : ℝ :=
  -((y₁ ^ 2 - 1) ^ 2 / y₂ + y₂ ^ 3 / 27 + y₂ / 3 * (2 / 3 * y₂ ^ 2 + 2 + 2 * y₁ ^ 2))

/-- The vertical transport map `T(y₁, y₂)` of Chen and Hou, Part I, (B.66), by Cardano's
formula: `T = W - y₂/3` with `W` the real root of `W³ + p W + q`. -/
def shearMap (y₁ y₂ : ℝ) : ℝ :=
  cardanoRoot (shearMapCoeffP y₁ y₂) (shearMapCoeffQ y₁ y₂) - y₂ / 3

/-- The primitive `Ψ(t) = (1/2)(t/((y₁ + 1)² + t²) - t/((y₁ - 1)² + t²))` of `Δ(y₁, ·)`. -/
def shearPotential (y₁ t : ℝ) : ℝ :=
  (t / ((y₁ + 1) ^ 2 + t ^ 2) - t / ((y₁ - 1) ^ 2 + t ^ 2)) / 2

/-- The depressed form of (B.66): `P(T) = W³ + p W + q` with `W = T + y₂/3`. -/
theorem shearCubic_eq_depressed {y₂ : ℝ} (y₁ T : ℝ) :
    shearCubic y₁ y₂ T = (T + y₂ / 3) ^ 3 + shearMapCoeffP y₁ y₂ * (T + y₂ / 3) +
      shearMapCoeffQ y₁ y₂ := by
  rcases eq_or_ne y₂ 0 with rfl | h
  · simp only [shearCubic, shearMapCoeffP, shearMapCoeffQ, div_zero]
    ring
  simp only [shearCubic, shearMapCoeffP, shearMapCoeffQ]
  field_simp
  ring

/-- The linear coefficient `p` of the depressed form is positive. -/
theorem shearMapCoeffP_pos (y₁ y₂ : ℝ) : 0 < shearMapCoeffP y₁ y₂ := by
  unfold shearMapCoeffP
  positivity

/-- The discriminant `q² + 4p³/27` of the depressed cubic is nonnegative and
`-q + (q² + 4p³/27)^{1/2} > 0`, so Cardano's formula applies. -/
private theorem shearMap_cardano (y₁ y₂ : ℝ) :
    0 ≤ shearMapCoeffQ y₁ y₂ ^ 2 + 4 * shearMapCoeffP y₁ y₂ ^ 3 / 27 ∧
      0 < -shearMapCoeffQ y₁ y₂ +
        Real.sqrt (shearMapCoeffQ y₁ y₂ ^ 2 + 4 * shearMapCoeffP y₁ y₂ ^ 3 / 27) := by
  have hp := shearMapCoeffP_pos y₁ y₂
  set q := shearMapCoeffQ y₁ y₂
  set p := shearMapCoeffP y₁ y₂
  have hp3 : 0 < 4 * p ^ 3 / 27 := by positivity
  refine ⟨by positivity, ?_⟩
  have : |q| < Real.sqrt (q ^ 2 + 4 * p ^ 3 / 27) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)
  linarith [neg_abs_le q, le_abs_self q]

/-- `T(y₁, y₂)` is a root of (B.66). -/
theorem shearCubic_shearMap {y₂ : ℝ} (y₁ : ℝ) :
    shearCubic y₁ y₂ (shearMap y₁ y₂) = 0 := by
  obtain ⟨hD, hr⟩ := shearMap_cardano y₁ y₂
  rw [shearCubic_eq_depressed, shearMap, sub_add_cancel]
  exact cardanoRoot_cubic_eq_zero hD hr

/-- Every real root of (B.66) is `T(y₁, y₂)`: the linear coefficient is positive. -/
theorem eq_shearMap_of_shearCubic_eq_zero {y₂ T : ℝ} {y₁ : ℝ}
    (hT : shearCubic y₁ y₂ T = 0) : T = shearMap y₁ y₂ := by
  have hr := shearCubic_shearMap (y₂ := y₂) y₁
  rw [shearCubic_eq_depressed] at hr hT
  have hdisc : 0 < 4 * shearMapCoeffP y₁ y₂ ^ 3 + 27 * shearMapCoeffQ y₁ y₂ ^ 2 := by
    have := shearMapCoeffP_pos y₁ y₂
    positivity
  have := eq_of_cubic_eq_zero_of_discr_pos hdisc hT hr
  linarith

/-- For `y₂ > 0`, (B.66) is increasing in `T ≥ 0`. -/
theorem shearCubic_strictMonoOn {y₁ y₂ : ℝ} (h : 0 < y₂) :
    StrictMonoOn (shearCubic y₁ y₂) (Ici 0) := by
  intro s hs t ht hst
  have hs0 : 0 ≤ s := hs
  simp only [shearCubic]
  have h1 : s ^ 3 < t ^ 3 := pow_lt_pow_left₀ hst hs0 (by norm_num)
  have h2 : s ^ 2 * y₂ ≤ t ^ 2 * y₂ :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs0 hst.le 2) h.le
  have h3 : s * (y₂ ^ 2 + 2 + 2 * y₁ ^ 2) ≤ t * (y₂ ^ 2 + 2 + 2 * y₁ ^ 2) := by nlinarith
  linarith

/-- `T(y₁, y₂) > 0` for `y₂ > 0` and `y₁² ≠ 1`. -/
theorem shearMap_pos {y₁ y₂ : ℝ} (h : 0 < y₂) (h₁ : y₁ ^ 2 ≠ 1) : 0 < shearMap y₁ y₂ := by
  have hc : 0 < (y₁ ^ 2 - 1) ^ 2 / y₂ := div_pos (by positivity) h
  set R := 1 + (y₁ ^ 2 - 1) ^ 2 / y₂
  have hR : 0 ≤ R := by positivity
  have hcont : ContinuousOn (shearCubic y₁ y₂) (Icc 0 R) := by
    unfold shearCubic
    fun_prop
  have h0 : shearCubic y₁ y₂ 0 < 0 := by
    simp only [shearCubic]
    linarith
  have hRpos : 0 ≤ shearCubic y₁ y₂ R := by
    simp only [shearCubic]
    have hR1 : 1 ≤ R := by simp only [R]; linarith
    nlinarith [mul_nonneg hR (sq_nonneg R), mul_nonneg (sq_nonneg R) h.le,
      mul_nonneg hR (by positivity : (0 : ℝ) ≤ y₂ ^ 2 + 2 * y₁ ^ 2)]
  obtain ⟨T, hT, hroot⟩ := intermediate_value_Icc hR hcont ⟨h0.le, hRpos⟩
  rw [← eq_shearMap_of_shearCubic_eq_zero hroot]
  rcases eq_or_lt_of_le hT.1 with h' | h'
  · rw [← h'] at hroot
    exact absurd hroot h0.ne
  · exact h'

/-- `Ψ(T) - Ψ(y₂) = -2 y₁ y₂ (y₂ - T) P(T) / ∏` with `P` the cubic (B.66). -/
theorem shearPotential_sub_eq (y₁ : ℝ) {y₂ : ℝ} (h : y₂ ≠ 0) (T : ℝ)
    (h₁ : (y₁ + 1) ^ 2 + T ^ 2 ≠ 0) (h₂ : (y₁ - 1) ^ 2 + T ^ 2 ≠ 0)
    :
    shearPotential y₁ T - shearPotential y₁ y₂ =
      -2 * y₁ * y₂ * (y₂ - T) * shearCubic y₁ y₂ T /
        (((y₁ + 1) ^ 2 + T ^ 2) * ((y₁ - 1) ^ 2 + T ^ 2) *
          ((y₁ + 1) ^ 2 + y₂ ^ 2) * ((y₁ - 1) ^ 2 + y₂ ^ 2)) := by
  have h₄ : (y₁ - 1) ^ 2 + y₂ ^ 2 ≠ 0 := by positivity
  have h₃ : (y₁ + 1) ^ 2 + y₂ ^ 2 ≠ 0 := by positivity
  simp only [shearPotential, shearCubic]
  field_simp
  ring

/-- The mass equation of the vertical transport map: `Ψ(T(y₁, y₂)) = Ψ(y₂)` for `y₂ > 0` and
`y₁² ≠ 1` (at `y₁ = ± 1` the kernel `Δ(y₁, ·)` is not integrable at `0`). -/
theorem shearPotential_shearMap {y₁ y₂ : ℝ} (h : 0 < y₂) (h₁ : y₁ ^ 2 ≠ 1) :
    shearPotential y₁ (shearMap y₁ y₂) = shearPotential y₁ y₂ := by
  have hT := shearMap_pos h h₁
  have := shearPotential_sub_eq y₁ h.ne' (shearMap y₁ y₂) (by positivity) (by positivity)
   
  rw [shearCubic_shearMap, mul_zero, zero_div] at this
  linarith

/-- `T(y₁, y₂) ≥ 0` for `y₂ > 0`; at `y₁² = 1` the root is `0`. -/
theorem shearMap_nonneg {y₁ y₂ : ℝ} (h : 0 < y₂) : 0 ≤ shearMap y₁ y₂ := by
  by_cases h₁ : y₁ ^ 2 = 1
  · refine le_of_eq (eq_shearMap_of_shearCubic_eq_zero ?_)
    simp [shearCubic, h₁]
  · exact (shearMap_pos h h₁).le

/-- Comparing two cubics at a common nonnegative point: if `P_{y'}(T(y)) ≥ 0`, then
`T(y') ≤ T(y)`. -/
private theorem shearMap_le_shearMap_of_shearCubic_nonneg {y₁ y₁' y₂ y₂' : ℝ} (h : 0 < y₂)
    (h' : 0 < y₂') (hc : 0 ≤ shearCubic y₁' y₂' (shearMap y₁ y₂)) :
    shearMap y₁' y₂' ≤ shearMap y₁ y₂ := by
  by_contra hlt
  push Not at hlt
  have := shearCubic_strictMonoOn (y₁ := y₁') h' (show shearMap y₁ y₂ ∈ Ici 0 from
    shearMap_nonneg h) (show shearMap y₁' y₂' ∈ Ici 0 from shearMap_nonneg h') hlt
  rw [shearCubic_shearMap] at this
  linarith

/-- `T(y₁, ·)` is strictly decreasing on `(0, ∞)` for `y₁² ≠ 1`, Part II, Supplement,
Lemma 5.5. -/
theorem strictAntiOn_shearMap_right {y₁ : ℝ} (h₁ : y₁ ^ 2 ≠ 1) :
    StrictAntiOn (fun y₂ ↦ shearMap y₁ y₂) (Ioi 0) := by
  intro y₂ hy₂ y₂' hy₂' hlt
  have h : 0 < y₂ := hy₂
  have h' : 0 < y₂' := hy₂'
  change shearMap y₁ y₂' < shearMap y₁ y₂
  have hT := shearMap_pos h h₁
  set T := shearMap y₁ y₂
  have hroot := shearCubic_shearMap (y₂ := y₂) y₁
  have hc : 0 < shearCubic y₁ y₂' T := by
    have hdiff : shearCubic y₁ y₂' T - shearCubic y₁ y₂ T = T ^ 2 * (y₂' - y₂) +
        T * (y₂' ^ 2 - y₂ ^ 2) + (y₁ ^ 2 - 1) ^ 2 * (1 / y₂ - 1 / y₂') := by
      simp only [shearCubic]
      ring
    have h1 : 0 < T ^ 2 * (y₂' - y₂) := mul_pos (by positivity) (by linarith)
    have h2 : 0 ≤ T * (y₂' ^ 2 - y₂ ^ 2) := mul_nonneg hT.le (by nlinarith)
    have h3 : 0 ≤ (y₁ ^ 2 - 1) ^ 2 * (1 / y₂ - 1 / y₂') :=
      mul_nonneg (sq_nonneg _) (sub_nonneg.2 (one_div_le_one_div_of_le h hlt.le))
    linarith
  rcases (shearMap_le_shearMap_of_shearCubic_nonneg h h' hc.le).lt_or_eq with hlt' | heq
  · exact hlt'
  · exfalso
    have := shearCubic_shearMap (y₂ := y₂') y₁
    rw [heq] at this
    linarith

/-- `T(·, y₂)` decreases on `[0, 1]`, Part II, Supplement, Lemma 5.5. -/
theorem antitoneOn_shearMap_left {y₂ : ℝ} (h : 0 < y₂) :
    AntitoneOn (fun y₁ ↦ shearMap y₁ y₂) (Icc 0 1) := by
  intro y₁ hy₁ y₁' hy₁' hle
  change shearMap y₁' y₂ ≤ shearMap y₁ y₂
  refine shearMap_le_shearMap_of_shearCubic_nonneg h h ?_
  have hT := shearMap_nonneg (y₁ := y₁) h
  have hroot := shearCubic_shearMap (y₂ := y₂) y₁
  have hdiff : shearCubic y₁' y₂ (shearMap y₁ y₂) - shearCubic y₁ y₂ (shearMap y₁ y₂) =
      (y₁' ^ 2 - y₁ ^ 2) * (2 * shearMap y₁ y₂ + (2 - y₁' ^ 2 - y₁ ^ 2) / y₂) := by
    simp only [shearCubic]
    field_simp
    ring
  have h1 : 0 ≤ y₁' ^ 2 - y₁ ^ 2 := by nlinarith [hy₁.1, hy₁'.1]
  have h2 : 0 ≤ 2 - y₁' ^ 2 - y₁ ^ 2 := by nlinarith [hy₁.1, hy₁'.1, hy₁.2, hy₁'.2]
  have : 0 ≤ (y₁' ^ 2 - y₁ ^ 2) * (2 * shearMap y₁ y₂ + (2 - y₁' ^ 2 - y₁ ^ 2) / y₂) :=
    mul_nonneg h1 (by positivity)
  linarith

/-- For `y₁ > 1`, `y₁² - 1 > T y₂`: from `(y₁² - 1)² = y₂ (T³ + T² y₂ + T (…)) > (T y₂)²`. -/
theorem mul_shearMap_lt {y₁ y₂ : ℝ} (h₁ : 1 < y₁) :
    shearMap y₁ y₂ * y₂ < y₁ ^ 2 - 1 := by
  have hpos : 0 < y₁ ^ 2 - 1 := by nlinarith
  rcases eq_or_ne y₂ 0 with rfl | h
  · simpa using hpos
  have hroot := shearCubic_shearMap (y₂ := y₂) y₁
  set T := shearMap y₁ y₂
  simp only [shearCubic] at hroot
  have he : (y₁ ^ 2 - 1) ^ 2 =
      (T * y₂) * (T ^ 2 + T * y₂ + y₂ ^ 2 + 2 + 2 * y₁ ^ 2) := by
    field_simp at hroot
    linarith
  have hF : 0 < T ^ 2 + T * y₂ + y₂ ^ 2 + 2 + 2 * y₁ ^ 2 := by
    nlinarith [sq_nonneg (T + y₂ / 2), sq_nonneg y₂]
  have hu : 0 < T * y₂ := by
    by_contra hu
    push Not at hu
    nlinarith [mul_nonpos_iff.mpr (Or.inr ⟨hu, hF.le⟩), pow_pos hpos 2]
  have hFu : 0 < T ^ 2 + y₂ ^ 2 + 2 + 2 * y₁ ^ 2 := by positivity
  have hgt : (T * y₂) ^ 2 < (y₁ ^ 2 - 1) ^ 2 := by
    rw [he]
    nlinarith [mul_pos hu hFu]
  nlinarith

/-- `T(·, y₂)` increases on `[1, ∞)`, Part II, Supplement, Lemma 5.5. -/
theorem monotoneOn_shearMap_left {y₂ : ℝ} (h : 0 < y₂) :
    MonotoneOn (fun y₁ ↦ shearMap y₁ y₂) (Ici 1) := by
  intro y₁ hy₁ y₁' hy₁' hle
  change shearMap y₁ y₂ ≤ shearMap y₁' y₂
  rcases eq_or_lt_of_le (show (1 : ℝ) ≤ y₁ from hy₁) with h1 | h1
  · have : shearMap y₁ y₂ = 0 := by
      refine (eq_shearMap_of_shearCubic_eq_zero ?_).symm
      simp [shearCubic, ← h1]
    rw [this]
    exact shearMap_nonneg h
  · rcases eq_or_lt_of_le hle with heq | hlt
    · rw [heq]
    by_contra hgt
    push Not at hgt
    -- `P_{y₁'}(T(y₁)) < 0`, so the root `T(y₁')` lies above `T(y₁)`
    have hT := mul_shearMap_lt (y₂ := y₂) h1
    have hroot := shearCubic_shearMap (y₂ := y₂) y₁
    have hdiff : shearCubic y₁' y₂ (shearMap y₁ y₂) - shearCubic y₁ y₂ (shearMap y₁ y₂) =
        (y₁' ^ 2 - y₁ ^ 2) * (2 * shearMap y₁ y₂ - (y₁' ^ 2 + y₁ ^ 2 - 2) / y₂) := by
      simp only [shearCubic]
      field_simp
      ring
    have hneg : 2 * shearMap y₁ y₂ - (y₁' ^ 2 + y₁ ^ 2 - 2) / y₂ < 0 := by
      rw [sub_neg, lt_div_iff₀ h]
      nlinarith
    have hpos : 0 < y₁' ^ 2 - y₁ ^ 2 := by nlinarith
    have hc : shearCubic y₁' y₂ (shearMap y₁ y₂) < 0 := by nlinarith
    have := shearCubic_strictMonoOn (y₁ := y₁') h (show shearMap y₁' y₂ ∈ Ici 0 from
      shearMap_nonneg h) (show shearMap y₁ y₂ ∈ Ici 0 from shearMap_nonneg h) hgt
    rw [shearCubic_shearMap] at this
    linarith

/-- `s_c(y₁) > 0` for `y₁² ≠ 1`. -/
theorem shearThreshold_pos {y₁ : ℝ} (h₁ : y₁ ^ 2 ≠ 1) : 0 < shearThreshold y₁ := by
  refine Real.sqrt_pos.2 (div_pos ?_ (by norm_num))
  have hlt : (y₁ ^ 2 + 1) / 2 < Real.sqrt (y₁ ^ 4 - y₁ ^ 2 + 1) := by
    refine Real.lt_sqrt_of_sq_lt ?_
    have : 0 < (y₁ ^ 2 - 1) ^ 2 := by positivity
    nlinarith
  linarith

/-- `y₂ P(y₂) = -Q(y₁, y₂)`: the diagonal of (B.66) is the sign quartic. -/
theorem mul_shearCubic_self {y₂ : ℝ} (h : y₂ ≠ 0) (y₁ : ℝ) :
    y₂ * shearCubic y₁ y₂ y₂ = -shearQuartic y₁ y₂ := by
  simp only [shearCubic, shearQuartic]
  field_simp
  ring

/-- The sign threshold is the fixed point: `T(y₁, s_c(y₁)) = s_c(y₁)` for `y₁² ≠ 1`. -/
theorem shearMap_shearThreshold {y₁ : ℝ} (h₁ : y₁ ^ 2 ≠ 1) :
    shearMap y₁ (shearThreshold y₁) = shearThreshold y₁ := by
  have hs := shearThreshold_pos h₁
  refine (eq_shearMap_of_shearCubic_eq_zero ?_).symm
  have := mul_shearCubic_self hs.ne' y₁
  rw [shearQuartic_eq_threshold, sub_self, mul_zero, zero_mul, neg_zero] at this
  exact (mul_eq_zero.1 this).resolve_left hs.ne'

/-- `Ψ' = Δ(y₁, ·)` off the poles. -/
theorem hasDerivAt_shearPotential {y₁ t : ℝ} (h₁ : (y₁ + 1) ^ 2 + t ^ 2 ≠ 0)
    (h₂ : (y₁ - 1) ^ 2 + t ^ 2 ≠ 0) :
    HasDerivAt (shearPotential y₁) (shearDifference y₁ t) t := by
  have hd : ∀ c : ℝ, c ^ 2 + t ^ 2 ≠ 0 →
      HasDerivAt (fun t ↦ t / (c ^ 2 + t ^ 2)) (2 * shearDensity c t) t := fun c hc ↦ by
    have hg : HasDerivAt (fun t ↦ c ^ 2 + t ^ 2) (2 * t) t := by
      simpa using (hasDerivAt_pow 2 t).const_add (c ^ 2)
    refine ((hasDerivAt_id t).div hg hc).congr_deriv ?_
    rw [shearDensity_eq, id]
    field_simp
    ring
  refine (((hd (y₁ + 1) h₁).sub (hd (y₁ - 1) h₂)).div_const 2).congr_deriv ?_
  rw [shearDifference]
  ring

/-- `Ψ` is strictly decreasing on `[0, s_c(y₁)]` for `y₁ > 0`, `y₁² ≠ 1`. -/
theorem strictAntiOn_shearPotential {y₁ : ℝ} (h₀ : 0 < y₁) (h₁ : y₁ ^ 2 ≠ 1) :
    StrictAntiOn (shearPotential y₁) (Icc 0 (shearThreshold y₁)) := by
  have hne : ∀ t : ℝ, 0 < t → (y₁ - 1) ^ 2 + t ^ 2 ≠ 0 := fun t ht ↦ by positivity
  have hy1 : y₁ ≠ 1 := fun h ↦ h₁ (by rw [h]; norm_num)
  have hpole : ∀ t : ℝ, 0 ≤ t → (y₁ - 1) ^ 2 + t ^ 2 ≠ 0 := fun t ht ↦ by
    rcases eq_or_lt_of_le ht with h | h
    · rw [← h]
      have : y₁ - 1 ≠ 0 := sub_ne_zero.2 hy1
      positivity
    · exact hne t h
  have hcont : ContinuousOn (shearPotential y₁) (Icc 0 (shearThreshold y₁)) := fun t ht ↦
    (hasDerivAt_shearPotential (by positivity) (hpole t ht.1)).continuousAt.continuousWithinAt
  refine strictAntiOn_of_deriv_neg (convex_Icc _ _) hcont fun t ht ↦ ?_
  rw [interior_Icc] at ht
  rw [(hasDerivAt_shearPotential (by positivity) (hne t ht.1)).deriv]
  refine (shearDifference_neg_iff h₀ (hne t ht.1)).2 ?_
  rw [abs_of_pos ht.1]
  exact ht.2

/-- `Ψ` is strictly increasing on `[s_c(y₁), ∞)` for `y₁ > 0`, `y₁² ≠ 1`. -/
theorem strictMonoOn_shearPotential {y₁ : ℝ} (h₀ : 0 < y₁) (h₁ : y₁ ^ 2 ≠ 1) :
    StrictMonoOn (shearPotential y₁) (Ici (shearThreshold y₁)) := by
  have hs := shearThreshold_pos h₁
  have hne : ∀ t : ℝ, 0 < t → (y₁ - 1) ^ 2 + t ^ 2 ≠ 0 := fun t ht ↦ by positivity
  refine strictMonoOn_of_deriv_pos (convex_Ici _)
    (fun t ht ↦ (hasDerivAt_shearPotential (by positivity)
      (hne t (hs.trans_le ht))).continuousAt.continuousWithinAt) fun t ht ↦ ?_
  rw [interior_Ici] at ht
  have ht0 : 0 < t := hs.trans ht
  rw [(hasDerivAt_shearPotential (by positivity) (hne t ht0)).deriv]
  refine (shearDifference_pos_iff h₀ (hne t ht0)).2 ?_
  rw [abs_of_pos ht0]
  exact ht

/-- `T(y₁, y₂) = y₂` only at the threshold. -/
theorem eq_shearThreshold_of_shearMap_eq {y₁ y₂ : ℝ} (h : 0 < y₂)
    (heq : shearMap y₁ y₂ = y₂) : y₂ = shearThreshold y₁ := by
  have hroot := shearCubic_shearMap (y₂ := y₂) y₁
  rw [heq] at hroot
  have := mul_shearCubic_self h.ne' y₁
  rw [hroot, mul_zero] at this
  have hQ : shearQuartic y₁ y₂ = 0 := by linarith
  rw [shearQuartic_eq_threshold] at hQ
  have ha : 0 < y₂ ^ 2 - (-(y₁ ^ 2 + 1) - 2 * Real.sqrt (y₁ ^ 4 - y₁ ^ 2 + 1)) / 3 := by
    have := Real.sqrt_nonneg (y₁ ^ 4 - y₁ ^ 2 + 1)
    nlinarith [sq_nonneg y₂, sq_nonneg y₁]
  have h2 : y₂ ^ 2 = shearThreshold y₁ ^ 2 := by
    rcases mul_eq_zero.1 hQ with h' | h'
    · rcases mul_eq_zero.1 h' with h'' | h''
      · norm_num at h''
      · linarith
    · linarith
  exact (pow_left_inj₀ h.le (Real.sqrt_nonneg _) two_ne_zero).1 h2

/-- Below the threshold the vertical transport map lands above it, Part I, (B.18): for
`0 < y₂ < s_c(y₁)`, `T(y₁, y₂) > s_c(y₁)`. -/
theorem shearThreshold_lt_shearMap {y₁ y₂ : ℝ} (h₀ : 0 < y₁) (h₁ : y₁ ^ 2 ≠ 1) (h : 0 < y₂)
    (hlt : y₂ < shearThreshold y₁) : shearThreshold y₁ < shearMap y₁ y₂ := by
  have hT := shearMap_pos h h₁
  by_contra hle
  push Not at hle
  have heq : shearMap y₁ y₂ = y₂ := (strictAntiOn_shearPotential h₀ h₁).injOn ⟨hT.le, hle⟩
    ⟨h.le, hlt.le⟩ (shearPotential_shearMap h h₁)
  exact absurd (eq_shearThreshold_of_shearMap_eq h heq) hlt.ne

/-- Above the threshold the vertical transport map lands below it, Part I, (B.18): for
`y₂ > s_c(y₁)`, `T(y₁, y₂) < s_c(y₁)`. -/
theorem shearMap_lt_shearThreshold {y₁ y₂ : ℝ} (h₀ : 0 < y₁) (h₁ : y₁ ^ 2 ≠ 1)
    (hlt : shearThreshold y₁ < y₂) : shearMap y₁ y₂ < shearThreshold y₁ := by
  have h : 0 < y₂ := (shearThreshold_pos h₁).trans hlt
  by_contra hle
  push Not at hle
  have heq : shearMap y₁ y₂ = y₂ := (strictMonoOn_shearPotential h₀ h₁).injOn
    (show shearThreshold y₁ ≤ shearMap y₁ y₂ from hle)
    (show shearThreshold y₁ ≤ y₂ from hlt.le) (shearPotential_shearMap h h₁)
  exact absurd (eq_shearThreshold_of_shearMap_eq h heq) hlt.ne'

/-- The vertical transport map is jointly measurable. -/
theorem measurable_shearMap : Measurable fun y : ℝ × ℝ ↦ shearMap y.1 y.2 := by
  have hP : Measurable fun y : ℝ × ℝ ↦ shearMapCoeffP y.1 y.2 := by
    unfold shearMapCoeffP
    fun_prop
  have hQ : Measurable fun y : ℝ × ℝ ↦ shearMapCoeffQ y.1 y.2 := by
    unfold shearMapCoeffQ
    fun_prop
  exact (measurable_cardanoRoot.comp (hP.prodMk hQ)).sub (measurable_snd.div_const 3)

end IncompressibleFlow.SharpHolder
