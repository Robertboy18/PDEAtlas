/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.ShearMap

/-!
# The horizontal transport map of the vertical Hölder estimates of `u_y` and `v_x`

In the `C_y^{1/2}` estimates of `u_y` and `v_x` (Chen and Hou, Part I, Appendix B.2) the
kernel `Δ(y₁, y₂) = K₂(y₁ + 1, y₂) - K₂(y₁ - 1, y₂)` is transported along horizontal lines. The
map `𝖳(y₁, y₂) ≥ 0` solving `∫_{y₁}^{𝖳} Δ(s, y₂) ds = 0` (Part I, (B.48)) is explicit (Part I,
(B.67)):

`𝖳² = (y₁² + 2 y₂² + y₁² y₂² + 3 y₂⁴ - 1) / (y₁² - y₂² - 1)
    = (1 + y₂²)(y₁² + 3 y₂² - 1) / (y₁² - y₂² - 1)`

(`horizontalShearMap`). With the primitive `X(t) = (1/2)((t - 1)/((t - 1)² + y₂²) -
(t + 1)/((t + 1)² + y₂²))` of `Δ(·, y₂)` (`horizontalShearPotential`), `X(𝖳) - X(y₁)` vanishes:
`horizontalShearPotential_horizontalShearMap`.

## Main results

Part II, Supplement, Lemma 5.7:
* on `D₁ = {0 < y₂, 3 y₂² < 1, 0 ≤ y₁ < h_c^-(y₂)}`: `h_c^-(y₂) < 𝖳 < 1`
  (`lowerShearThreshold_lt_horizontalShearMap`, `horizontalShearMap_lt_one`), and `𝖳` decreases
  in `y₁` and in `y₂`;
* on `D₂ = {0 < y₂, y₁ > h_c^+(y₂)}`: `1 < 𝖳 < h_c^+(y₂)` (`one_lt_horizontalShearMap`,
  `horizontalShearMap_lt_upperShearThreshold`), and `𝖳` decreases in `y₁` and increases in `y₂`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Appendix B.2.1, (B.48), p. 138, and
  Appendix B.3.2, (B.67), p. 142.
  <https://arxiv.org/abs/2210.07191v4>
* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Supplementary material II,
  Section 5.5.1, Lemma 5.7, p. 23.
  <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public section

noncomputable section

open Set

namespace IncompressibleFlow.SharpHolder

/-- The horizontal transport map `𝖳(y₁, y₂) = ((y₁² + 2 y₂² + y₁² y₂² + 3 y₂⁴ - 1) /
(y₁² - y₂² - 1))^{1/2}` of Chen and Hou, Part I, (B.67). -/
def horizontalShearMap (y₁ y₂ : ℝ) : ℝ :=
  Real.sqrt ((y₁ ^ 2 + 2 * y₂ ^ 2 + y₁ ^ 2 * y₂ ^ 2 + 3 * y₂ ^ 4 - 1) / (y₁ ^ 2 - y₂ ^ 2 - 1))

/-- The primitive `X(t) = (1/2)((t - 1)/((t - 1)² + y₂²) - (t + 1)/((t + 1)² + y₂²))` of
`Δ(·, y₂)`. -/
def horizontalShearPotential (y₂ t : ℝ) : ℝ :=
  ((t - 1) / ((t - 1) ^ 2 + y₂ ^ 2) - (t + 1) / ((t + 1) ^ 2 + y₂ ^ 2)) / 2

/-- The radicand of (B.67) in factored form: `(1 + y₂²)(y₁² + 3 y₂² - 1) / (y₁² - y₂² - 1)`. -/
theorem horizontalShearMap_radicand (y₁ y₂ : ℝ) :
    (y₁ ^ 2 + 2 * y₂ ^ 2 + y₁ ^ 2 * y₂ ^ 2 + 3 * y₂ ^ 4 - 1) / (y₁ ^ 2 - y₂ ^ 2 - 1) =
      (1 + y₂ ^ 2) * (y₁ ^ 2 + 3 * y₂ ^ 2 - 1) / (y₁ ^ 2 - y₂ ^ 2 - 1) := by
  congr 1
  ring

/-- `X' = Δ(·, y₂)` for `y₂ ≠ 0`. -/
theorem hasDerivAt_horizontalShearPotential {y₂ : ℝ} (h : y₂ ≠ 0) (t : ℝ) :
    HasDerivAt (horizontalShearPotential y₂) (shearDifference t y₂) t := by
  have hd : ∀ c : ℝ, HasDerivAt (fun t ↦ (t + c) / ((t + c) ^ 2 + y₂ ^ 2))
      (-2 * shearDensity (t + c) y₂) t := fun c ↦ by
    have hne : (t + c) ^ 2 + y₂ ^ 2 ≠ 0 := by positivity
    have hg : HasDerivAt (fun t ↦ (t + c) ^ 2 + y₂ ^ 2) (2 * (t + c)) t := by
      have := ((hasDerivAt_id t).add_const c).pow 2
      simpa using this.add_const (y₂ ^ 2)
    refine (((hasDerivAt_id t).add_const c).div hg hne).congr_deriv ?_
    rw [shearDensity_eq, id]
    field_simp
    ring
  have h₁ := hd (-1)
  have h₂ := hd 1
  simp only [← sub_eq_add_neg] at h₁
  refine ((h₁.sub h₂).div_const 2).congr_deriv ?_
  rw [shearDifference]
  ring

/-- On `{y₁² ≠ y₂² + 1}`, `𝖳² (y₁² - y₂² - 1) = y₁² + 2 y₂² + y₁² y₂² + 3 y₂⁴ - 1` when the
radicand is nonnegative. -/
theorem horizontalShearMap_sq {y₁ y₂ : ℝ}
    (h : 0 ≤ (y₁ ^ 2 + 2 * y₂ ^ 2 + y₁ ^ 2 * y₂ ^ 2 + 3 * y₂ ^ 4 - 1) / (y₁ ^ 2 - y₂ ^ 2 - 1)) :
    horizontalShearMap y₁ y₂ ^ 2 =
      (y₁ ^ 2 + 2 * y₂ ^ 2 + y₁ ^ 2 * y₂ ^ 2 + 3 * y₂ ^ 4 - 1) / (y₁ ^ 2 - y₂ ^ 2 - 1) :=
  Real.sq_sqrt h

/-- `X(𝖳) - X(y₁)` factors through (B.67): it is a multiple of
`(y₁² + 2 y₂² + y₁² y₂² + 3 y₂⁴ - 1) - 𝖳² (y₁² - y₂² - 1)`. -/
theorem horizontalShearPotential_sub_eq {y₂ : ℝ} (h : y₂ ≠ 0) (y₁ T : ℝ) :
    horizontalShearPotential y₂ T - horizontalShearPotential y₂ y₁ =
      (T - y₁) * (T + y₁) *
        ((y₁ ^ 2 + 2 * y₂ ^ 2 + y₁ ^ 2 * y₂ ^ 2 + 3 * y₂ ^ 4 - 1) -
          T ^ 2 * (y₁ ^ 2 - y₂ ^ 2 - 1)) /
        (((T - 1) ^ 2 + y₂ ^ 2) * ((T + 1) ^ 2 + y₂ ^ 2) * ((y₁ - 1) ^ 2 + y₂ ^ 2) *
          ((y₁ + 1) ^ 2 + y₂ ^ 2)) := by
  have a₁ : (T - 1) ^ 2 + y₂ ^ 2 ≠ 0 := by positivity
  have a₂ : (T + 1) ^ 2 + y₂ ^ 2 ≠ 0 := by positivity
  have a₃ : (y₁ - 1) ^ 2 + y₂ ^ 2 ≠ 0 := by positivity
  have a₄ : (y₁ + 1) ^ 2 + y₂ ^ 2 ≠ 0 := by positivity
  simp only [horizontalShearPotential]
  field_simp
  ring

/-- The mass equation (B.48) for the map (B.67): `X(𝖳(y₁, y₂)) = X(y₁)` where the radicand is
nonnegative and `y₁² ≠ y₂² + 1`. -/
theorem horizontalShearPotential_horizontalShearMap {y₁ y₂ : ℝ} (h : y₂ ≠ 0)
    (hQ : y₁ ^ 2 - y₂ ^ 2 - 1 ≠ 0)
    (hP : 0 ≤ (y₁ ^ 2 + 2 * y₂ ^ 2 + y₁ ^ 2 * y₂ ^ 2 + 3 * y₂ ^ 4 - 1) / (y₁ ^ 2 - y₂ ^ 2 - 1)) :
    horizontalShearPotential y₂ (horizontalShearMap y₁ y₂) = horizontalShearPotential y₂ y₁ := by
  have := horizontalShearPotential_sub_eq h y₁ (horizontalShearMap y₁ y₂)
  rw [horizontalShearMap_sq hP, div_mul_cancel₀ _ hQ, sub_self, mul_zero, zero_div] at this
  linarith

/-! ### Part II, Supplement, Lemma 5.7 -/

/-- The radicand of (B.67) as `(1 + y₂²) + 4 y₂² (1 + y₂²) / (y₁² - 1 - y₂²)`. -/
theorem horizontalShearMap_radicand_eq {y₁ y₂ : ℝ} (h : y₁ ^ 2 - y₂ ^ 2 - 1 ≠ 0) :
    (y₁ ^ 2 + 2 * y₂ ^ 2 + y₁ ^ 2 * y₂ ^ 2 + 3 * y₂ ^ 4 - 1) / (y₁ ^ 2 - y₂ ^ 2 - 1) =
      (1 + y₂ ^ 2) + 4 * y₂ ^ 2 * (1 + y₂ ^ 2) / (y₁ ^ 2 - y₂ ^ 2 - 1) := by
  field_simp
  ring

/-- `4 y₂² (1 + y₂²) / (2 y₂ s) = 2 y₂ s` with `s = (y₂² + 1)^{1/2}`: the squares
`u± = y₂² + 1 ± 2 y₂ s` of `h_c^±` are the fixed points of the radicand. -/
private theorem div_two_mul_sqrt_sq_add_one_eq {y₂ : ℝ} (hy₂ : 0 < y₂) :
    4 * y₂ ^ 2 * (1 + y₂ ^ 2) / (2 * y₂ * Real.sqrt (y₂ ^ 2 + 1)) =
      2 * y₂ * Real.sqrt (y₂ ^ 2 + 1) := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ y₂ ^ 2 + 1 by positivity)
  have hs0 : 0 < Real.sqrt (y₂ ^ 2 + 1) := Real.sqrt_pos.2 (by positivity)
  rw [div_eq_iff (by positivity)]
  linear_combination (-(4 : ℝ) * y₂ ^ 2) * hs

/-- The radicand of (B.67) as a function of `u = y₁²` and `v = y₂²`. -/
private def radicand (u v : ℝ) : ℝ := (1 + v) * (u + 3 * v - 1) / (u - v - 1)

/-- `𝖳(y₁, y₂) = R(y₁², y₂²)^{1/2}` with the radicand `R` of (B.67). -/
private theorem horizontalShearMap_eq_radicand (y₁ y₂ : ℝ) :
    horizontalShearMap y₁ y₂ = Real.sqrt (radicand (y₁ ^ 2) (y₂ ^ 2)) := by
  rw [horizontalShearMap, horizontalShearMap_radicand, radicand]

/-- Off the pole `u = v + 1`, `R(u, v) = (1 + v) + 4 v (1 + v) / (u - v - 1)`. -/
private theorem radicand_eq {u v : ℝ} (h : u - v - 1 ≠ 0) :
    radicand u v = (1 + v) + 4 * v * (1 + v) / (u - v - 1) := by
  rw [radicand]
  field_simp
  ring

/-- `R(v) - R(w) = (v - w) E / (D(v) D(w))` with
`E = (u - 1)(u + 3 + 3 (v + w)) - 3 v w`. -/
private theorem radicand_sub {u v w : ℝ} (hv : u - v - 1 ≠ 0) (hw : u - w - 1 ≠ 0) :
    radicand u v - radicand u w =
      (v - w) * ((u - 1) * (u + 3 + 3 * (v + w)) - 3 * v * w) / ((u - v - 1) * (u - w - 1)) := by
  rw [radicand, radicand]
  field_simp
  ring

/-- The domain `D₁ = {0 < y₂, 3 y₂² < 1, 0 ≤ y₁ < h_c^-(y₂)}` of the inner region gives
`y₁² < h_c^-(y₂)² < y₂² + 1` and `y₁² < 1`. -/
private theorem lower_domain {y₁ y₂ : ℝ} (hy₂ : 0 < y₂) (h3 : 3 * y₂ ^ 2 < 1) (hy₁ : 0 ≤ y₁)
    (hlt : y₁ < lowerShearThreshold y₂) :
    y₁ ^ 2 < y₂ ^ 2 + 1 - 2 * y₂ * Real.sqrt (y₂ ^ 2 + 1) ∧ y₁ ^ 2 < 1 := by
  have hsq := lowerShearThreshold_sq h3.le
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ y₂ ^ 2 + 1 by positivity)
  have hs0 : 0 < Real.sqrt (y₂ ^ 2 + 1) := Real.sqrt_pos.2 (by positivity)
  have h1 : y₁ ^ 2 < lowerShearThreshold y₂ ^ 2 := by
    have := Real.sqrt_nonneg (y₂ ^ 2 + 1 - 2 * y₂ * Real.sqrt (y₂ ^ 2 + 1))
    nlinarith [lowerShearThreshold]
  rw [hsq] at h1
  refine ⟨h1, ?_⟩
  have : y₂ ^ 2 ≤ 2 * y₂ * Real.sqrt (y₂ ^ 2 + 1) := by
    have : y₂ ≤ Real.sqrt (y₂ ^ 2 + 1) := Real.le_sqrt_of_sq_le (by linarith)
    nlinarith
  linarith

/-- On `D₁`, `h_c^-(y₂) < 𝖳(y₁, y₂)`, Part II, Supplement, Lemma 5.7. -/
theorem lowerShearThreshold_lt_horizontalShearMap {y₁ y₂ : ℝ} (hy₂ : 0 < y₂)
    (h3 : 3 * y₂ ^ 2 < 1) (hy₁ : 0 ≤ y₁) (hlt : y₁ < lowerShearThreshold y₂) :
    lowerShearThreshold y₂ < horizontalShearMap y₁ y₂ := by
  obtain ⟨hu, -⟩ := lower_domain hy₂ h3 hy₁ hlt
  have hs0 : 0 < Real.sqrt (y₂ ^ 2 + 1) := Real.sqrt_pos.2 (by positivity)
  have hneg : y₁ ^ 2 - y₂ ^ 2 - 1 < -(2 * y₂ * Real.sqrt (y₂ ^ 2 + 1)) := by linarith
  have hb : -(2 * y₂ * Real.sqrt (y₂ ^ 2 + 1)) < 0 := by
    have := mul_pos (mul_pos two_pos hy₂) hs0
    linarith
  have hR : y₂ ^ 2 + 1 - 2 * y₂ * Real.sqrt (y₂ ^ 2 + 1) < radicand (y₁ ^ 2) (y₂ ^ 2) := by
    rw [radicand_eq (by linarith)]
    have hinv : 1 / -(2 * y₂ * Real.sqrt (y₂ ^ 2 + 1)) < 1 / (y₁ ^ 2 - y₂ ^ 2 - 1) :=
      one_div_lt_one_div_of_neg_of_lt (by linarith) hneg
    have hpos : 0 < 4 * y₂ ^ 2 * (1 + y₂ ^ 2) := by positivity
    have := mul_lt_mul_of_pos_left hinv hpos
    rw [mul_one_div, mul_one_div, div_neg, div_two_mul_sqrt_sq_add_one_eq hy₂] at this
    linarith
  rw [horizontalShearMap_eq_radicand, lowerShearThreshold]
  exact Real.sqrt_lt_sqrt (by
    have := lowerShearThreshold_sq h3.le
    nlinarith [sq_nonneg (lowerShearThreshold y₂)]) hR

/-- On `D₁`, `𝖳(y₁, y₂) < 1`, Part II, Supplement, Lemma 5.7. -/
theorem horizontalShearMap_lt_one {y₁ y₂ : ℝ} (hy₂ : 0 < y₂) (h3 : 3 * y₂ ^ 2 < 1)
    (hy₁ : 0 ≤ y₁) (hlt : y₁ < lowerShearThreshold y₂) : horizontalShearMap y₁ y₂ < 1 := by
  obtain ⟨hu', hu⟩ := lower_domain hy₂ h3 hy₁ hlt
  have hv := pow_pos hy₂ 2
  have hP : y₁ ^ 2 + 3 * y₂ ^ 2 - 1 ≤ 0 := by
    have : 2 * y₂ ≤ Real.sqrt (y₂ ^ 2 + 1) := Real.le_sqrt_of_sq_le (by nlinarith)
    nlinarith
  rw [horizontalShearMap_eq_radicand, ← Real.sqrt_one]
  refine Real.sqrt_lt_sqrt ?_ ?_
  · rw [radicand]
    exact div_nonneg_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (by positivity) hP) (by linarith)
  · rw [radicand, div_lt_one_of_neg (by linarith)]
    nlinarith [sq_nonneg y₁]

/-- The region `D₁` of Part II, Supplement, Lemma 5.7. -/
def lowerShearDomain : Set (ℝ × ℝ) :=
  {y | 0 ≤ y.1 ∧ 0 < y.2 ∧ 3 * y.2 ^ 2 < 1 ∧ y.1 < lowerShearThreshold y.2}

/-- The region `D₂` of Part II, Supplement, Lemma 5.7. -/
def upperShearDomain : Set (ℝ × ℝ) :=
  {y | 0 < y.2 ∧ upperShearThreshold y.2 < y.1}

/-- On `D₂`, `y₁² > h_c^+(y₂)² = y₂² + 1 + 2 y₂ (y₂² + 1)^{1/2}`. -/
private theorem upper_domain {y₁ y₂ : ℝ} (hy₂ : 0 < y₂) (hlt : upperShearThreshold y₂ < y₁) :
    y₂ ^ 2 + 1 + 2 * y₂ * Real.sqrt (y₂ ^ 2 + 1) < y₁ ^ 2 := by
  have h0 : 0 ≤ upperShearThreshold y₂ := Real.sqrt_nonneg _
  have := mul_self_lt_mul_self h0 hlt
  rw [← upperShearThreshold_sq hy₂.le]
  nlinarith

/-- On `D₁`, `𝖳` decreases in `y₁`, Part II, Supplement, Lemma 5.7. -/
theorem antitoneOn_horizontalShearMap_left {y₂ : ℝ} :
    AntitoneOn (fun y₁ ↦ horizontalShearMap y₁ y₂) {y₁ | (y₁, y₂) ∈ lowerShearDomain} := by
  intro y₁ hy₁ y₁' hy₁' hle
  obtain ⟨h₀, hy₂, h3, hlt⟩ := hy₁
  obtain ⟨h₀', -, -, hlt'⟩ := hy₁'
  dsimp only at h₀ hy₂ h3 hlt h₀' hlt'
  obtain ⟨-, hu⟩ := lower_domain hy₂ h3 h₀ hlt
  obtain ⟨-, hu'⟩ := lower_domain hy₂ h3 h₀' hlt'
  have hv := pow_pos hy₂ 2
  simp only [horizontalShearMap_eq_radicand]
  refine Real.sqrt_le_sqrt ?_
  rw [radicand_eq (by linarith), radicand_eq (by linarith)]
  have hsq : y₁ ^ 2 ≤ y₁' ^ 2 := by nlinarith
  have hinv : 1 / (y₁' ^ 2 - y₂ ^ 2 - 1) ≤ 1 / (y₁ ^ 2 - y₂ ^ 2 - 1) :=
    one_div_le_one_div_of_neg_of_le (by linarith) (by linarith)
  have := mul_le_mul_of_nonneg_left hinv (by positivity : (0 : ℝ) ≤ 4 * y₂ ^ 2 * (1 + y₂ ^ 2))
  rw [mul_one_div, mul_one_div] at this
  linarith

/-- On `D₁`, `𝖳` decreases in `y₂`, Part II, Supplement, Lemma 5.7. -/
theorem antitoneOn_horizontalShearMap_right {y₁ : ℝ} :
    AntitoneOn (fun y₂ ↦ horizontalShearMap y₁ y₂) {y₂ | (y₁, y₂) ∈ lowerShearDomain} := by
  intro y₂ hy₂ y₂' hy₂' hle
  obtain ⟨h₀, hy₂0, h3, hlt⟩ := hy₂
  obtain ⟨-, hy₂0', h3', hlt'⟩ := hy₂'
  dsimp only at h₀ hy₂0 h3 hlt hy₂0' h3' hlt'
  obtain ⟨-, hu⟩ := lower_domain hy₂0 h3 h₀ hlt
  have hv := pow_pos hy₂0 2
  have hv' := pow_pos hy₂0' 2
  simp only [horizontalShearMap_eq_radicand]
  refine Real.sqrt_le_sqrt ?_
  have hsub := radicand_sub (u := y₁ ^ 2) (v := y₂ ^ 2) (w := y₂' ^ 2) (by linarith) (by linarith)
  have hE : (y₁ ^ 2 - 1) * (y₁ ^ 2 + 3 + 3 * (y₂ ^ 2 + y₂' ^ 2)) - 3 * y₂ ^ 2 * y₂' ^ 2 < 0 := by
    have : 0 < y₁ ^ 2 + 3 + 3 * (y₂ ^ 2 + y₂' ^ 2) := by positivity
    nlinarith [mul_pos hv hv']
  have hvw : y₂ ^ 2 - y₂' ^ 2 ≤ 0 := by nlinarith
  have hD : 0 < (y₁ ^ 2 - y₂ ^ 2 - 1) * (y₁ ^ 2 - y₂' ^ 2 - 1) :=
    mul_pos_of_neg_of_neg (by linarith) (by linarith)
  have : 0 ≤ radicand (y₁ ^ 2) (y₂ ^ 2) - radicand (y₁ ^ 2) (y₂' ^ 2) := by
    rw [hsub]
    exact div_nonneg (mul_nonneg_of_nonpos_of_nonpos hvw hE.le) hD.le
  linarith

/-- On `D₂`, `1 < 𝖳(y₁, y₂)`, Part II, Supplement, Lemma 5.7. -/
theorem one_lt_horizontalShearMap {y₁ y₂ : ℝ} (hy : (y₁, y₂) ∈ upperShearDomain) :
    1 < horizontalShearMap y₁ y₂ := by
  obtain ⟨hy₂, hlt⟩ := hy
  dsimp only at hy₂ hlt
  have hs0 : 0 < Real.sqrt (y₂ ^ 2 + 1) := Real.sqrt_pos.2 (by positivity)
  have hsq := upperShearThreshold_sq hy₂.le
  have hu := upper_domain hy₂ hlt
  have hv := pow_pos hy₂ 2
  have hd : 0 < y₁ ^ 2 - y₂ ^ 2 - 1 := by nlinarith [mul_pos hy₂ hs0]
  rw [horizontalShearMap_eq_radicand, ← Real.sqrt_one]
  refine Real.sqrt_lt_sqrt zero_le_one ?_
  rw [radicand_eq hd.ne']
  have : 0 < 4 * y₂ ^ 2 * (1 + y₂ ^ 2) / (y₁ ^ 2 - y₂ ^ 2 - 1) := by positivity
  linarith

/-- On `D₂`, `𝖳(y₁, y₂) < h_c^+(y₂)`, Part II, Supplement, Lemma 5.7. -/
theorem horizontalShearMap_lt_upperShearThreshold {y₁ y₂ : ℝ}
    (hy : (y₁, y₂) ∈ upperShearDomain) : horizontalShearMap y₁ y₂ < upperShearThreshold y₂ := by
  obtain ⟨hy₂, hlt⟩ := hy
  dsimp only at hy₂ hlt
  have hs0 : 0 < Real.sqrt (y₂ ^ 2 + 1) := Real.sqrt_pos.2 (by positivity)
  have hsq := upperShearThreshold_sq hy₂.le
  have hu := upper_domain hy₂ hlt
  have hb : 0 < 2 * y₂ * Real.sqrt (y₂ ^ 2 + 1) := by positivity
  have hd : 2 * y₂ * Real.sqrt (y₂ ^ 2 + 1) < y₁ ^ 2 - y₂ ^ 2 - 1 := by linarith
  rw [horizontalShearMap_eq_radicand, upperShearThreshold]
  refine Real.sqrt_lt_sqrt ?_ ?_
  · rw [radicand_eq (by linarith)]
    have : 0 < 4 * y₂ ^ 2 * (1 + y₂ ^ 2) / (y₁ ^ 2 - y₂ ^ 2 - 1) := by
      have := pow_pos hy₂ 2
      have : 0 < y₁ ^ 2 - y₂ ^ 2 - 1 := by linarith
      positivity
    nlinarith [sq_nonneg y₂]
  · rw [radicand_eq (by linarith)]
    have hinv : 1 / (y₁ ^ 2 - y₂ ^ 2 - 1) < 1 / (2 * y₂ * Real.sqrt (y₂ ^ 2 + 1)) :=
      one_div_lt_one_div_of_lt hb hd
    have hpos : 0 < 4 * y₂ ^ 2 * (1 + y₂ ^ 2) := by positivity
    have := mul_lt_mul_of_pos_left hinv hpos
    rw [mul_one_div, mul_one_div, div_two_mul_sqrt_sq_add_one_eq hy₂] at this
    linarith

/-- On `D₂`, `𝖳` decreases in `y₁`, Part II, Supplement, Lemma 5.7. -/
theorem antitoneOn_horizontalShearMap_left_upper {y₂ : ℝ} :
    AntitoneOn (fun y₁ ↦ horizontalShearMap y₁ y₂) {y₁ | (y₁, y₂) ∈ upperShearDomain} := by
  intro y₁ hy₁ y₁' hy₁' hle
  have hpos : ∀ y : ℝ, (y, y₂) ∈ upperShearDomain → 0 < y ^ 2 - y₂ ^ 2 - 1 := fun y hy ↦ by
    obtain ⟨hy₂, hlt⟩ := hy
    dsimp only at hy₂ hlt
    have hs0 : 0 < Real.sqrt (y₂ ^ 2 + 1) := Real.sqrt_pos.2 (by positivity)
    have := upper_domain hy₂ hlt
    nlinarith [mul_pos hy₂ hs0]
  have hp := hpos y₁ hy₁
  have hp' := hpos y₁' hy₁'
  have hy₂ : 0 < y₂ := hy₁.1
  have h0 : 0 ≤ y₁ := (Real.sqrt_nonneg _).trans (show upperShearThreshold y₂ < y₁ from hy₁.2).le
  simp only [horizontalShearMap_eq_radicand]
  refine Real.sqrt_le_sqrt ?_
  rw [radicand_eq hp.ne', radicand_eq hp'.ne']
  have hinv : 1 / (y₁' ^ 2 - y₂ ^ 2 - 1) ≤ 1 / (y₁ ^ 2 - y₂ ^ 2 - 1) :=
    one_div_le_one_div_of_le hp (by nlinarith)
  have := mul_le_mul_of_nonneg_left hinv (by positivity : (0 : ℝ) ≤ 4 * y₂ ^ 2 * (1 + y₂ ^ 2))
  rw [mul_one_div, mul_one_div] at this
  linarith

/-- On `D₂`, `𝖳` increases in `y₂`, Part II, Supplement, Lemma 5.7. -/
theorem monotoneOn_horizontalShearMap_right_upper {y₁ : ℝ} :
    MonotoneOn (fun y₂ ↦ horizontalShearMap y₁ y₂) {y₂ | (y₁, y₂) ∈ upperShearDomain} := by
  intro y₂ hy₂ y₂' hy₂' hle
  have hpos : ∀ y : ℝ, (y₁, y) ∈ upperShearDomain → 0 < y₁ ^ 2 - y ^ 2 - 1 := fun y hy ↦ by
    obtain ⟨hy0, hlt⟩ := hy
    dsimp only at hy0 hlt
    have hs0 : 0 < Real.sqrt (y ^ 2 + 1) := Real.sqrt_pos.2 (by positivity)
    have := upper_domain hy0 hlt
    nlinarith [mul_pos hy0 hs0]
  have hp := hpos y₂ hy₂
  have hp' := hpos y₂' hy₂'
  have hv := pow_pos (show (0 : ℝ) < y₂ from hy₂.1) 2
  have hv' := pow_pos (show (0 : ℝ) < y₂' from hy₂'.1) 2
  simp only [horizontalShearMap_eq_radicand]
  refine Real.sqrt_le_sqrt ?_
  have hsub := radicand_sub (u := y₁ ^ 2) (v := y₂ ^ 2) (w := y₂' ^ 2) hp.ne' hp'.ne'
  have hE : 0 < (y₁ ^ 2 - 1) * (y₁ ^ 2 + 3 + 3 * (y₂ ^ 2 + y₂' ^ 2)) - 3 * y₂ ^ 2 * y₂' ^ 2 := by
    nlinarith [mul_pos hv hv']
  have hvw : y₂ ^ 2 - y₂' ^ 2 ≤ 0 := by
    have h1 : (0 : ℝ) < y₂ := hy₂.1
    nlinarith
  have : radicand (y₁ ^ 2) (y₂ ^ 2) - radicand (y₁ ^ 2) (y₂' ^ 2) ≤ 0 := by
    rw [hsub]
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hvw hE.le)
      (mul_pos hp hp').le
  linarith

end IncompressibleFlow.SharpHolder
