/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Scalar.DepressedCubic
public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.StrainKernel

/-!
# The transport map of the horizontal Hölder estimate of the strain

For `s₂ ≠ 0` and `s₁ > 0` the transport map `T(s₁, s₂)` of Chen and Hou, Part I, Section 3.3,
pairs `s₁` with the point on the other side of the threshold `f(s₂)` at which the primitive `Φ`
of the kernel `Δ(·, s₂)` takes the same value, so that `∫_T^{s₁} Δ(t, s₂) dt = 0`. Clearing
denominators, `Φ(T) = Φ(s₁)` with `T ≠ s₁` is the cubic (3.14)

`-1 - 8 T s₁ + 16 T s₁ (T² + T s₁ + s₁²) - 8 s₂² (1 - 4 s₁ T + 2 s₂²) = 0`

(`strainSymmetricCubic`, symmetric in `T` and `s₁`), which is `16 s₁` times the monic cubic
(B.63) `T³ + T² s₁ + T (s₁² - 1/2 + 2 s₂²) - (4 s₂² + 1)² / (16 s₁)` (`strainCubic`). Its
discriminant is negative (`strainCubic_discr_pos`), so it has exactly one real root, given by
Cardano's formula (B.65); this is the definition of `strainMap`.

## Main results

* `strainCubic_strainMap`, `eq_strainMap_of_strainCubic_eq_zero`: `T` is the unique real root of
  (B.63).
* `strainPotential_strainMap`: `Φ(T(s₁)) = Φ(s₁)`, the mass equation (3.13) of the paper.
* `strainMap_pos`, `strainThreshold_lt_strainMap`, `strainMap_lt_strainThreshold`,
  `strainMap_strainThreshold`: `T` maps `(0, f)` into `(f, ∞)` and `(f, ∞)` into `(0, f)`, with
  the fixed point `f`.
* `strainMap_strainMap`: `T` is an involution.
* Part II, Supplement, Lemma 5.3: `strainMap_mul_le` (`4 s₁ T ≤ 4 s₂² + 1`),
  `three_fourths_le_strainMap` (`T² + T s₁ + s₁² + 2 s₂² ≥ 3/4`), `strictAntiOn_strainMap`
  (`T` decreases in `s₁`) and `monotoneOn_strainMap_right` (`T` increases in `s₂ > 0`).
* `measurable_strainMap`: joint measurability in `(s₁, s₂)`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 3.3.1, (3.13) and (3.14),
  p. 32, and Appendix B.3.2, (B.63)-(B.65), pp. 141-142.
  <https://arxiv.org/abs/2210.07191v4>
* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Supplementary material II,
  Section 5.3, Lemma 5.3, p. 8.
  <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public section

noncomputable section

open Set Filter PDE.Analysis.Scalar
open scoped Topology

namespace IncompressibleFlow.SharpHolder

/-- The cubic (3.14) of Chen and Hou, Part I, symmetric in `T` and `s₁`:
`-1 - 8 T s₁ + 16 T s₁ (T² + T s₁ + s₁²) - 8 s₂² (1 - 4 s₁ T + 2 s₂²)`. -/
def strainSymmetricCubic (s₁ s₂ T : ℝ) : ℝ :=
  -1 - 8 * T * s₁ + 16 * T * s₁ * (T ^ 2 + T * s₁ + s₁ ^ 2) -
    8 * s₂ ^ 2 * (1 - 4 * s₁ * T + 2 * s₂ ^ 2)

/-- The monic cubic (B.63) of Chen and Hou, Part I, in the variable `T`:
`T³ + T² s₁ + T (s₁² - 1/2 + 2 s₂²) - (4 s₂² + 1)² / (16 s₁)`. -/
def strainCubic (s₁ s₂ T : ℝ) : ℝ :=
  T ^ 3 + T ^ 2 * s₁ + T * (s₁ ^ 2 - 1 / 2 + 2 * s₂ ^ 2) - (4 * s₂ ^ 2 + 1) ^ 2 / (16 * s₁)

/-- The coefficient `p = (2/3) s₁² - 1/2 + 2 s₂²` of the depressed form of (B.63). -/
def strainMapCoeffP (s₁ s₂ : ℝ) : ℝ :=
  2 / 3 * s₁ ^ 2 - 1 / 2 + 2 * s₂ ^ 2

/-- The coefficient `q = -((4 s₂² + 1)² / (16 s₁) + (7/27) s₁³ + (s₁/3)(2 s₂² - 1/2))` of the
depressed form of (B.63). -/
def strainMapCoeffQ (s₁ s₂ : ℝ) : ℝ :=
  -((4 * s₂ ^ 2 + 1) ^ 2 / (16 * s₁) + 7 / 27 * s₁ ^ 3 + s₁ / 3 * (2 * s₂ ^ 2 - 1 / 2))

/-- The transport map `T(s₁, s₂)` of Chen and Hou, Part I, (3.14), by Cardano's formula (B.65):
`T = Z - s₁/3` with `Z` the real root of `Z³ + p Z + q`. -/
def strainMap (s₁ s₂ : ℝ) : ℝ :=
  cardanoRoot (strainMapCoeffP s₁ s₂) (strainMapCoeffQ s₁ s₂) - s₁ / 3

/-- The cubic (3.14) is symmetric in `T` and `s₁`. -/
theorem strainSymmetricCubic_comm (s₁ s₂ T : ℝ) :
    strainSymmetricCubic s₁ s₂ T = strainSymmetricCubic T s₂ s₁ := by
  simp only [strainSymmetricCubic]
  ring

/-- (3.14) is `16 s₁` times (B.63). -/
theorem strainSymmetricCubic_eq {s₁ : ℝ} (h : s₁ ≠ 0) (s₂ T : ℝ) :
    strainSymmetricCubic s₁ s₂ T = 16 * s₁ * strainCubic s₁ s₂ T := by
  simp only [strainSymmetricCubic, strainCubic]
  field_simp
  ring

/-- The diagonal of (3.14) is `-16 Δ₁`, so `T = s₁` solves it only at the threshold. -/
theorem strainSymmetricCubic_self (s₁ s₂ : ℝ) :
    strainSymmetricCubic s₁ s₂ s₁ = -16 * strainQuartic s₁ s₂ := by
  simp only [strainSymmetricCubic, strainQuartic]
  ring

/-- The depressed form: `T³ + … = Z³ + p Z + q` with `Z = T + s₁/3`. -/
theorem strainCubic_eq_depressed {s₁ : ℝ} (h : s₁ ≠ 0) (s₂ T : ℝ) :
    strainCubic s₁ s₂ T = (T + s₁ / 3) ^ 3 + strainMapCoeffP s₁ s₂ * (T + s₁ / 3) +
      strainMapCoeffQ s₁ s₂ := by
  simp only [strainCubic, strainMapCoeffP, strainMapCoeffQ]
  field_simp
  ring

/-- `-q > 0` for `s₁ > 0`. -/
theorem strainMapCoeffQ_neg {s₁ : ℝ} (h : 0 < s₁) (s₂ : ℝ) : strainMapCoeffQ s₁ s₂ < 0 := by
  have e : -strainMapCoeffQ s₁ s₂ =
      (7 / 27 * s₁ ^ 4 - s₁ ^ 2 / 6 + 1 / 16) / s₁ +
        s₂ ^ 2 * (4 * s₁ ^ 2 + 6 * s₂ ^ 2 + 3) / (6 * s₁) := by
    simp only [strainMapCoeffQ]
    field_simp
    ring
  have h₁ : 0 < 7 / 27 * s₁ ^ 4 - s₁ ^ 2 / 6 + 1 / 16 := by nlinarith [sq_nonneg (s₁ ^ 2 - 9 / 28)]
  have : 0 < -strainMapCoeffQ s₁ s₂ := by
    rw [e]
    have : 0 ≤ s₂ ^ 2 * (4 * s₁ ^ 2 + 6 * s₂ ^ 2 + 3) / (6 * s₁) := by positivity
    have : 0 < (7 / 27 * s₁ ^ 4 - s₁ ^ 2 / 6 + 1 / 16) / s₁ := by positivity
    linarith
  linarith

/-- The discriminant of (B.63) is negative: `4 p³ + 27 q² > 0` for `s₁ > 0`, `s₂ ≠ 0`. -/
theorem strainCubic_discr_pos {s₁ s₂ : ℝ} (h₁ : 0 < s₁) (h₂ : s₂ ≠ 0) :
    0 < 4 * strainMapCoeffP s₁ s₂ ^ 3 + 27 * strainMapCoeffQ s₁ s₂ ^ 2 := by
  set p₀ := strainMapCoeffP s₁ 0
  set q₀ := strainMapCoeffQ s₁ 0
  have hp : strainMapCoeffP s₁ s₂ = p₀ + 2 * s₂ ^ 2 := by
    simp only [p₀, strainMapCoeffP]
    ring
  have hq : strainMapCoeffQ s₁ s₂ = q₀ - s₂ ^ 2 * (4 * s₁ ^ 2 + 6 * s₂ ^ 2 + 3) / (6 * s₁) := by
    simp only [q₀, strainMapCoeffQ]
    field_simp
    ring
  have h0 : 4 * p₀ ^ 3 + 27 * q₀ ^ 2 =
      (1 - 4 * s₁ ^ 2) ^ 2 * (27 - 56 * s₁ ^ 2 + 48 * s₁ ^ 4) / (256 * s₁ ^ 2) := by
    simp only [p₀, q₀, strainMapCoeffP, strainMapCoeffQ]
    field_simp
    ring
  have h0' : 0 ≤ 4 * p₀ ^ 3 + 27 * q₀ ^ 2 := by
    rw [h0]
    have : 0 ≤ 27 - 56 * s₁ ^ 2 + 48 * s₁ ^ 4 := by nlinarith [sq_nonneg (s₁ ^ 2 - 7 / 12)]
    positivity
  have hq₀ : q₀ < 0 := strainMapCoeffQ_neg h₁ 0
  have hδ : 0 ≤ s₂ ^ 2 * (4 * s₁ ^ 2 + 6 * s₂ ^ 2 + 3) / (6 * s₁) := by positivity
  have hs : 0 < s₂ ^ 2 := by positivity
  rw [hp, hq]
  set δ := s₂ ^ 2 * (4 * s₁ ^ 2 + 6 * s₂ ^ 2 + 3) / (6 * s₁)
  have hcube : p₀ ^ 3 < (p₀ + 2 * s₂ ^ 2) ^ 3 := by
    have : p₀ < p₀ + 2 * s₂ ^ 2 := by linarith
    exact (Odd.strictMono_pow (by decide : Odd 3)) this
  have hsq : q₀ ^ 2 ≤ (q₀ - δ) ^ 2 := by nlinarith
  linarith

/-- For `s₁ > 0` and `s₂ ≠ 0`, the discriminant `q² + 4p³/27` of the depressed cubic is
nonnegative and `-q + (q² + 4p³/27)^{1/2} > 0`, so Cardano's formula applies. -/
private theorem strainMap_cardano {s₁ s₂ : ℝ} (h₁ : 0 < s₁) (h₂ : s₂ ≠ 0) :
    0 ≤ strainMapCoeffQ s₁ s₂ ^ 2 + 4 * strainMapCoeffP s₁ s₂ ^ 3 / 27 ∧
      0 < -strainMapCoeffQ s₁ s₂ +
        Real.sqrt (strainMapCoeffQ s₁ s₂ ^ 2 + 4 * strainMapCoeffP s₁ s₂ ^ 3 / 27) := by
  have hd := strainCubic_discr_pos h₁ h₂
  have hq := strainMapCoeffQ_neg h₁ s₂
  refine ⟨by linarith, ?_⟩
  have := Real.sqrt_nonneg (strainMapCoeffQ s₁ s₂ ^ 2 + 4 * strainMapCoeffP s₁ s₂ ^ 3 / 27)
  linarith

/-- `T(s₁, s₂)` is a root of (B.63). -/
theorem strainCubic_strainMap {s₁ s₂ : ℝ} (h₁ : 0 < s₁) (h₂ : s₂ ≠ 0) :
    strainCubic s₁ s₂ (strainMap s₁ s₂) = 0 := by
  obtain ⟨hD, hr⟩ := strainMap_cardano h₁ h₂
  rw [strainCubic_eq_depressed h₁.ne', strainMap, sub_add_cancel]
  exact cardanoRoot_cubic_eq_zero hD hr

/-- Every real root of (B.63) is `T(s₁, s₂)`. -/
theorem eq_strainMap_of_strainCubic_eq_zero {s₁ s₂ T : ℝ} (h₁ : 0 < s₁) (h₂ : s₂ ≠ 0)
    (hT : strainCubic s₁ s₂ T = 0) : T = strainMap s₁ s₂ := by
  have h := strainCubic_strainMap h₁ h₂
  rw [strainCubic_eq_depressed h₁.ne'] at h hT
  have := eq_of_cubic_eq_zero_of_discr_pos (strainCubic_discr_pos h₁ h₂) hT h
  linarith

/-- `T(s₁, s₂)` solves the symmetric cubic (3.14). -/
theorem strainSymmetricCubic_strainMap {s₁ s₂ : ℝ} (h₁ : 0 < s₁) (h₂ : s₂ ≠ 0) :
    strainSymmetricCubic s₁ s₂ (strainMap s₁ s₂) = 0 := by
  rw [strainSymmetricCubic_eq h₁.ne', strainCubic_strainMap h₁ h₂, mul_zero]

/-- `Φ(T) - Φ(s₁) = -s₂ (T - s₁) P(T, s₁) / (16 ∏)`, with `P` the cubic (3.14): a root of
(3.14) has the same primitive value as `s₁`. -/
theorem strainPotential_sub_eq (s₁ s₂ T : ℝ) (h₂ : s₂ ≠ 0) :
    strainPotential s₂ T - strainPotential s₂ s₁ =
      -s₂ * (T - s₁) * strainSymmetricCubic s₁ s₂ T /
        (16 * (((T - 1 / 2) ^ 2 + s₂ ^ 2) * ((T + 1 / 2) ^ 2 + s₂ ^ 2) *
          ((s₁ - 1 / 2) ^ 2 + s₂ ^ 2) * ((s₁ + 1 / 2) ^ 2 + s₂ ^ 2))) := by
  have a₁ : (T - 1 / 2) ^ 2 + s₂ ^ 2 ≠ 0 := by positivity
  have a₂ : (T + 1 / 2) ^ 2 + s₂ ^ 2 ≠ 0 := by positivity
  have a₃ : (s₁ - 1 / 2) ^ 2 + s₂ ^ 2 ≠ 0 := by positivity
  have a₄ : (s₁ + 1 / 2) ^ 2 + s₂ ^ 2 ≠ 0 := by positivity
  rw [strainPotential_eq, strainPotential_eq]
  simp only [strainSymmetricCubic]
  field_simp
  ring

/-- The mass equation of the transport map: `Φ(T(s₁, s₂)) = Φ(s₁)`, that is
`∫_{T}^{s₁} Δ(t, s₂) dt = 0`. -/
theorem strainPotential_strainMap {s₁ s₂ : ℝ} (h₁ : 0 < s₁) (h₂ : s₂ ≠ 0) :
    strainPotential s₂ (strainMap s₁ s₂) = strainPotential s₂ s₁ := by
  have := strainPotential_sub_eq s₁ s₂ (strainMap s₁ s₂) h₂
  rw [strainSymmetricCubic_strainMap h₁ h₂, mul_zero, zero_div] at this
  linarith

/-- For `s₁ > 0` the cubic (B.63) is positive at every `R ≥ 2 + 2 (4 s₂² + 1)²/(16 s₁)`. -/
private theorem strainCubic_pos_of_large {s₁ s₂ R : ℝ} (h₁ : 0 < s₁)
    (hR : 2 + 2 * ((4 * s₂ ^ 2 + 1) ^ 2 / (16 * s₁)) ≤ R) : 0 < strainCubic s₁ s₂ R := by
  set c := (4 * s₂ ^ 2 + 1) ^ 2 / (16 * s₁)
  have hc : 0 ≤ c := by positivity
  have hR2 : 2 ≤ R := by linarith
  simp only [strainCubic]
  have h3 : 4 * R ≤ R ^ 3 := by
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ R) (by linarith : (0 : ℝ) ≤ R - 2))
      (by linarith : (0 : ℝ) ≤ R + 2)]
  have : 0 ≤ R ^ 2 * s₁ := by positivity
  have : 0 ≤ R * (s₁ ^ 2 + 2 * s₂ ^ 2) := by positivity
  nlinarith

/-- `T(s₁, s₂) > 0` for `s₁ > 0`. -/
theorem strainMap_pos {s₁ s₂ : ℝ} (h₁ : 0 < s₁) (h₂ : s₂ ≠ 0) : 0 < strainMap s₁ s₂ := by
  set R := 2 + 2 * ((4 * s₂ ^ 2 + 1) ^ 2 / (16 * s₁))
  have hR : 0 ≤ R := by positivity
  have hcont : ContinuousOn (strainCubic s₁ s₂) (Icc 0 R) := by
    unfold strainCubic
    fun_prop
  have h0 : strainCubic s₁ s₂ 0 < 0 := by
    simp only [strainCubic]
    have : 0 < (4 * s₂ ^ 2 + 1) ^ 2 / (16 * s₁) := by positivity
    linarith
  obtain ⟨T, hT, hroot⟩ := intermediate_value_Icc hR hcont
    ⟨h0.le, (strainCubic_pos_of_large h₁ le_rfl).le⟩
  have heq := eq_strainMap_of_strainCubic_eq_zero h₁ h₂ hroot
  rcases eq_or_lt_of_le hT.1 with h | h
  · rw [← h] at hroot
    exact absurd hroot h0.ne
  · rw [← heq]
    exact h

/-- A root of the symmetric cubic (3.14) at `T = s₁` sits at the threshold. -/
theorem eq_strainThreshold_of_strainQuartic {s₁ s₂ : ℝ} (h₁ : 0 ≤ s₁)
    (h : strainQuartic s₁ s₂ = 0) : s₁ = strainThreshold s₂ := by
  rcases lt_trichotomy s₁ (strainThreshold s₂) with hlt | heq | hgt
  · exact absurd h ((strainQuartic_pos_iff h₁ s₂).2 hlt).ne'
  · exact heq
  · exact absurd h ((strainQuartic_neg_iff h₁ s₂).2 hgt).ne

/-- The threshold is the fixed point of the transport map. -/
theorem strainMap_strainThreshold {s₂ : ℝ} (h₂ : s₂ ≠ 0) :
    strainMap (strainThreshold s₂) s₂ = strainThreshold s₂ := by
  have hf := strainThreshold_pos s₂
  refine (eq_strainMap_of_strainCubic_eq_zero hf h₂ ?_).symm
  have := strainSymmetricCubic_self (strainThreshold s₂) s₂
  rw [strainQuartic_strainThreshold, mul_zero, strainSymmetricCubic_eq hf.ne'] at this
  exact (mul_eq_zero.1 this).resolve_left (by positivity)

/-- `T(s₁, s₂) = s₁` only at the threshold. -/
theorem eq_strainThreshold_of_strainMap_eq {s₁ s₂ : ℝ} (h₁ : 0 < s₁) (h₂ : s₂ ≠ 0)
    (h : strainMap s₁ s₂ = s₁) : s₁ = strainThreshold s₂ := by
  refine eq_strainThreshold_of_strainQuartic h₁.le ?_
  have := strainSymmetricCubic_strainMap h₁ h₂
  rw [h, strainSymmetricCubic_self] at this
  linarith

/-- Below the threshold the transport map lands above it: `T(s₁, s₂) > f(s₂)` for
`0 < s₁ < f(s₂)`. -/
theorem strainThreshold_lt_strainMap {s₁ s₂ : ℝ} (h₁ : 0 < s₁) (h₂ : 0 < s₂)
    (h : s₁ < strainThreshold s₂) : strainThreshold s₂ < strainMap s₁ s₂ := by
  have hT := strainMap_pos h₁ h₂.ne'
  by_contra hle
  push Not at hle
  have hinj := (strictMonoOn_strainPotential h₂).injOn
  have heq : strainMap s₁ s₂ = s₁ :=
    hinj ⟨hT.le, hle⟩ ⟨h₁.le, h.le⟩ (strainPotential_strainMap h₁ h₂.ne')
  exact absurd (eq_strainThreshold_of_strainMap_eq h₁ h₂.ne' heq) h.ne

/-- Above the threshold the transport map lands below it: `0 < T(s₁, s₂) < f(s₂)` for
`s₁ > f(s₂)`. -/
theorem strainMap_lt_strainThreshold {s₁ s₂ : ℝ} (h₂ : 0 < s₂) (h : strainThreshold s₂ < s₁) :
    strainMap s₁ s₂ < strainThreshold s₂ := by
  have h₁ : 0 < s₁ := (strainThreshold_pos s₂).trans h
  by_contra hle
  push Not at hle
  have hinj := (strictAntiOn_strainPotential h₂).injOn
  have heq : strainMap s₁ s₂ = s₁ :=
    hinj (show strainThreshold s₂ ≤ strainMap s₁ s₂ from hle)
      (show strainThreshold s₂ ≤ s₁ from h.le) (strainPotential_strainMap h₁ h₂.ne')
  exact absurd (eq_strainThreshold_of_strainMap_eq h₁ h₂.ne' heq) h.ne'

/-- The transport map is an involution: `T(T(s₁, s₂), s₂) = s₁` for `s₁ > 0`. -/
theorem strainMap_strainMap {s₁ s₂ : ℝ} (h₁ : 0 < s₁) (h₂ : s₂ ≠ 0) :
    strainMap (strainMap s₁ s₂) s₂ = s₁ := by
  have hT := strainMap_pos h₁ h₂
  refine (eq_strainMap_of_strainCubic_eq_zero hT h₂ ?_).symm
  have := strainSymmetricCubic_strainMap h₁ h₂
  rw [strainSymmetricCubic_comm, strainSymmetricCubic_eq hT.ne'] at this
  exact (mul_eq_zero.1 this).resolve_left (by positivity)

/-! ### Part II, Supplement, Lemma 5.3 -/

/-- `4 s₁ T(s₁, s₂) ≤ 4 s₂² + 1`, the first inequality of Part II, Supplement, Lemma 5.3. -/
theorem strainMap_mul_le {s₁ s₂ : ℝ} (h₁ : 0 < s₁) (h₂ : s₂ ≠ 0) :
    4 * s₁ * strainMap s₁ s₂ ≤ 4 * s₂ ^ 2 + 1 := by
  have hT := strainMap_pos h₁ h₂
  have hc := strainSymmetricCubic_strainMap h₁ h₂
  set T := strainMap s₁ s₂
  simp only [strainSymmetricCubic] at hc
  set P := 4 * s₁ * T
  set Q := 4 * s₂ ^ 2 + 1
  have hP : 0 < P := by positivity
  have hQ : 1 ≤ Q := by nlinarith [sq_nonneg s₂]
  have hkey : 3 * P ^ 2 + 2 * P * Q - 4 * P ≤ Q ^ 2 := by
    have : 3 * T * s₁ ≤ T ^ 2 + T * s₁ + s₁ ^ 2 := by nlinarith [sq_nonneg (T - s₁)]
    simp only [P, Q]
    nlinarith [mul_pos hT h₁]
  by_contra hlt
  push Not at hlt
  have hP1 : 1 < P := lt_of_le_of_lt hQ hlt
  nlinarith

/-- `T² + T s₁ + s₁² + 2 s₂² ≥ 3/4`, the second inequality of Part II, Supplement, Lemma 5.3. -/
theorem three_fourths_le_strainMap {s₁ s₂ : ℝ} (h₁ : 0 < s₁) (h₂ : s₂ ≠ 0) :
    3 / 4 ≤ strainMap s₁ s₂ ^ 2 + strainMap s₁ s₂ * s₁ + s₁ ^ 2 + 2 * s₂ ^ 2 := by
  have hT := strainMap_pos h₁ h₂
  have hle := strainMap_mul_le h₁ h₂
  have hc := strainSymmetricCubic_strainMap h₁ h₂
  set T := strainMap s₁ s₂
  simp only [strainSymmetricCubic] at hc
  have hTs : 0 < T * s₁ := mul_pos hT h₁
  have hQ : 4 * s₁ * T ≤ (4 * s₂ ^ 2 + 1) ^ 2 := by
    have : 1 ≤ 4 * s₂ ^ 2 + 1 := by nlinarith [sq_nonneg s₂]
    nlinarith
  have : 16 * (T * s₁) * (T ^ 2 + T * s₁ + s₁ ^ 2 + 2 * s₂ ^ 2) =
      (4 * s₂ ^ 2 + 1) ^ 2 + 8 * (T * s₁) := by linarith
  nlinarith

/-- `T(·, s₂)` is strictly decreasing on `(0, ∞)` for `s₂ > 0`, Part II, Supplement,
Lemma 5.3. -/
theorem strictAntiOn_strainMap {s₂ : ℝ} (h₂ : 0 < s₂) :
    StrictAntiOn (fun s₁ ↦ strainMap s₁ s₂) (Ioi 0) := by
  intro s hs s' hs' hss'
  have hs0 : 0 < s := hs
  have hs0' : 0 < s' := hs'
  set f := strainThreshold s₂
  have hmono := strictMonoOn_strainPotential h₂
  have hanti := strictAntiOn_strainPotential h₂
  have hT := strainMap_pos hs0 h₂.ne'
  have hT' := strainMap_pos hs0' h₂.ne'
  have hΦ := strainPotential_strainMap hs0 h₂.ne'
  have hΦ' := strainPotential_strainMap hs0' h₂.ne'
  change strainMap s' s₂ < strainMap s s₂
  rcases lt_or_ge s f with hsf | hsf
  · have hTs : f < strainMap s s₂ := strainThreshold_lt_strainMap hs0 h₂ hsf
    rcases lt_or_ge s' f with hs'f | hs'f
    · have hTs' : f < strainMap s' s₂ := strainThreshold_lt_strainMap hs0' h₂ hs'f
      have hlt : strainPotential s₂ s < strainPotential s₂ s' :=
        hmono ⟨hs0.le, hsf.le⟩ ⟨hs0'.le, hs'f.le⟩ hss'
      rw [← hΦ, ← hΦ'] at hlt
      by_contra hge
      push Not at hge
      rcases eq_or_lt_of_le hge with h | h
      · rw [h] at hlt
        exact lt_irrefl _ hlt
      · exact absurd (hanti (show strainMap s s₂ ∈ Ici f from hTs.le)
          (show strainMap s' s₂ ∈ Ici f from hTs'.le) h) (not_lt.2 hlt.le)
    · rcases eq_or_lt_of_le hs'f with h | h
      · rw [← h, strainMap_strainThreshold h₂.ne']
        exact hTs
      · exact (strainMap_lt_strainThreshold h₂ h).trans hTs
  · have hs'f : f < s' := lt_of_le_of_lt hsf hss'
    have hTs' : strainMap s' s₂ < f := strainMap_lt_strainThreshold h₂ hs'f
    rcases eq_or_lt_of_le hsf with h | h
    · rw [← h, strainMap_strainThreshold h₂.ne']
      exact hTs'
    · have hTs : strainMap s s₂ < f := strainMap_lt_strainThreshold h₂ h
      have hlt : strainPotential s₂ s' < strainPotential s₂ s :=
        hanti (show f ≤ s from h.le) (show f ≤ s' from hs'f.le) hss'
      rw [← hΦ, ← hΦ'] at hlt
      exact (StrictMonoOn.lt_iff_lt hmono ⟨hT'.le, hTs'.le⟩ ⟨hT.le, hTs.le⟩).1 hlt

/-- Beyond its root the cubic (B.63) is positive. -/
theorem strainCubic_pos_of_lt {s₁ s₂ t : ℝ} (h₁ : 0 < s₁) (h₂ : s₂ ≠ 0)
    (ht : strainMap s₁ s₂ < t) : 0 < strainCubic s₁ s₂ t := by
  by_contra hle
  push Not at hle
  rcases le_or_gt (2 + 2 * ((4 * s₂ ^ 2 + 1) ^ 2 / (16 * s₁))) t with hR | hR
  · exact absurd hle (not_le.2 (strainCubic_pos_of_large h₁ hR))
  · have hcont : ContinuousOn (strainCubic s₁ s₂)
        (Icc t (2 + 2 * ((4 * s₂ ^ 2 + 1) ^ 2 / (16 * s₁)))) := by
      unfold strainCubic
      fun_prop
    obtain ⟨u, hu, hroot⟩ := intermediate_value_Icc hR.le hcont
      ⟨hle, (strainCubic_pos_of_large h₁ le_rfl).le⟩
    have := eq_strainMap_of_strainCubic_eq_zero h₁ h₂ hroot
    linarith [hu.1]

/-- `T(s₁, ·)` increases in `s₂ > 0`, Part II, Supplement, Lemma 5.3. -/
theorem monotoneOn_strainMap_right {s₁ : ℝ} (h₁ : 0 < s₁) :
    MonotoneOn (fun s₂ ↦ strainMap s₁ s₂) (Ioi 0) := by
  intro σ hσ σ' hσ' hσσ'
  have hσ0 : 0 < σ := hσ
  have hσ0' : 0 < σ' := hσ'
  change strainMap s₁ σ ≤ strainMap s₁ σ'
  by_contra hlt
  push Not at hlt
  have hpos := strainCubic_pos_of_lt h₁ hσ0'.ne' hlt
  have hroot := strainCubic_strainMap h₁ hσ0.ne'
  have hle := strainMap_mul_le h₁ hσ0.ne'
  set T := strainMap s₁ σ
  have hdiff : strainCubic s₁ σ' T - strainCubic s₁ σ T =
      (σ' ^ 2 - σ ^ 2) / (2 * s₁) * (4 * s₁ * T - (2 * σ ^ 2 + 2 * σ' ^ 2 + 1)) := by
    simp only [strainCubic]
    field_simp
    ring
  have hsq : σ ^ 2 ≤ σ' ^ 2 := by nlinarith
  have : (σ' ^ 2 - σ ^ 2) / (2 * s₁) * (4 * s₁ * T - (2 * σ ^ 2 + 2 * σ' ^ 2 + 1)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  linarith

/-- The transport map is jointly measurable in `(s₁, s₂)`. -/
theorem measurable_strainMap : Measurable fun s : ℝ × ℝ ↦ strainMap s.1 s.2 := by
  have hP : Measurable fun s : ℝ × ℝ ↦ strainMapCoeffP s.1 s.2 := by
    unfold strainMapCoeffP
    fun_prop
  have hQ : Measurable fun s : ℝ × ℝ ↦ strainMapCoeffQ s.1 s.2 := by
    unfold strainMapCoeffQ
    fun_prop
  exact (measurable_cardanoRoot.comp (hP.prodMk hQ)).sub (measurable_fst.div_const 3)

/-- The transport map is measurable in `s₁`. -/
theorem measurable_strainMap_left (s₂ : ℝ) : Measurable fun s₁ ↦ strainMap s₁ s₂ := by
  have h : Measurable fun s₁ : ℝ ↦ ((s₁, s₂) : ℝ × ℝ) := measurable_id.prodMk measurable_const
  have := measurable_strainMap.comp h
  simpa only [Function.comp_def] using this

/-- The transport map is continuous in `s₂` for `s₁ > 0`, including at the axis `s₂ = 0`. -/
theorem continuousAt_strainMap_right {s₁ : ℝ} (h₁ : 0 < s₁) (s₂ : ℝ) :
    ContinuousAt (fun σ ↦ strainMap s₁ σ) s₂ := by
  have hq := strainMapCoeffQ_neg h₁ s₂
  have hbase : 0 < -strainMapCoeffQ s₁ s₂ +
      Real.sqrt (strainMapCoeffQ s₁ s₂ ^ 2 + 4 * strainMapCoeffP s₁ s₂ ^ 3 / 27) := by
    have := Real.sqrt_nonneg (strainMapCoeffQ s₁ s₂ ^ 2 + 4 * strainMapCoeffP s₁ s₂ ^ 3 / 27)
    linarith
  have hPQ : Continuous fun σ : ℝ ↦ (strainMapCoeffP s₁ σ, strainMapCoeffQ s₁ σ) := by
    unfold strainMapCoeffP strainMapCoeffQ
    fun_prop
  exact ((continuousAt_cardanoRoot hbase).comp
    (f := fun σ : ℝ ↦ (strainMapCoeffP s₁ σ, strainMapCoeffQ s₁ σ)) (x := s₂)
    hPQ.continuousAt).sub continuousAt_const

/-- The axis value is a lower bound: `T(s₁, 0) ≤ T(s₁, s₂)` for `s₁ > 0`, `s₂ > 0`, by continuity
at the axis and Part II, Supplement, Lemma 5.3. -/
theorem strainMap_zero_le {s₁ s₂ : ℝ} (h₁ : 0 < s₁) (h₂ : 0 < s₂) :
    strainMap s₁ 0 ≤ strainMap s₁ s₂ := by
  have ht : Tendsto (fun σ ↦ strainMap s₁ σ) (𝓝[>] 0) (𝓝 (strainMap s₁ 0)) :=
    (continuousAt_strainMap_right h₁ 0).tendsto.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsGT h₂] with σ hσ
  exact monotoneOn_strainMap_right h₁ hσ.1 h₂ hσ.2.le

/-- `T(s₁, ·)` increases on `[0, ∞)` for `s₁ > 0`, Part II, Supplement, Lemma 5.3, including the
axis. -/
theorem monotoneOn_strainMap_right_Ici {s₁ : ℝ} (h₁ : 0 < s₁) :
    MonotoneOn (fun s₂ ↦ strainMap s₁ s₂) (Ici 0) := by
  intro σ hσ σ' hσ' hle
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ σ from hσ) with h | h
  · subst h
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ σ' from hσ') with h' | h'
    · rw [← h']
    · exact strainMap_zero_le h₁ h'
  · exact monotoneOn_strainMap_right h₁ h (h.trans_le hle) hle

/-- On the axis, `T(·, 0)` decreases on `(0, ∞)`, as the limit of `T(·, s₂)` for `s₂ → 0⁺`. -/
theorem antitoneOn_strainMap_zero : AntitoneOn (fun s₁ ↦ strainMap s₁ 0) (Ioi 0) := by
  intro s hs s' hs' hle
  have hs0 : 0 < s := hs
  have hs0' : 0 < s' := hs'
  change strainMap s' 0 ≤ strainMap s 0
  refine le_of_tendsto_of_tendsto (b := 𝓝[>] (0 : ℝ))
    ((continuousAt_strainMap_right hs0' 0).tendsto.mono_left nhdsWithin_le_nhds)
    ((continuousAt_strainMap_right hs0 0).tendsto.mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  rcases eq_or_lt_of_le hle with h | h
  · rw [h]
  · exact (strictAntiOn_strainMap hσ hs hs' h).le

end IncompressibleFlow.SharpHolder
