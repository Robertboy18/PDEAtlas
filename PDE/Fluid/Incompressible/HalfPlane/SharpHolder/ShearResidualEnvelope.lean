/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.ShearHolderTails

/-!
# The residual envelope of the horizontal estimate of `v_x`

With `g_A(y) = A/(y² + A²)` and `μ_A(p) = g_A(p - 1) - g_A(p + 1)`, the column mass satisfies
`Δ_{1D}(p) ≤ 0` for `p ≥ 0` (`shearMass_nonpos`) and `Δ_{1D}(p) = -μ_A(p)` for `0 ≤ p ≤ B - 1`
(`abs_shearMass_eq`).

On `[1/9, 9]` the weights `2 |p - 1|^{1/2} + d(p)` and `(2p)^{1/2} + √2` agree, and
`∫_{1/9}^9 |Δ_{1D}| ≤ π`, so that `√2 |π + P(1/9)| + √2 ∫_{1/9}^9 |Δ_{1D}| = √2 π`.

## Main definitions

* `shearMassDensity`: `μ_A(p) = g_A(p - 1) - g_A(p + 1)`.
* `shearLineWeight`: the weight `d(p) = (2p)^{1/2} + √2 - 2 |p - 1|^{1/2}`.
* `shearLineDefect`: the line defect `D_c(A) = ∫_{1/9}^{c} d μ_A`.
* `shearOuterMassBelow`: the mass of `|Δ|` over the heights in `(h, B]`.

## Main results

* `shearMass_nonpos`, `abs_shearMass_eq`: `Δ_{1D} ≤ 0` on `p ≥ 0`, and `|Δ_{1D}| = μ_A` inside
  the boxes.
* `shearLineWeight_nonneg`: `d ≥ 0` on `[1/9, 9]`.
* `shearInnerMassCost_add_shearLineCost_le`:
  `S_{in,x}(B, A) + S_{1D}(B, A) + D_c(A) ≤ √2 π + X(A)` for `B ≥ 4`, `c ≤ 9` and `c ≤ B - 1`.
* `shearMassDensity_le`, `shearLineDefect_le`: `(l/A)³ μ_l ≤ μ_A` on `p ≥ 0` for `0 < l ≤ A`,
  hence `(l/A)³ D_c(l) ≤ D_c(A)`.
* `shearOuterCost_le_mass_below`: `S_out(B, h) ≤ 2 (2h)^{1/2} ∫_h^B ∫_{p > 0} |Δ|`.
* `shearOuterMassBelow_le`: the mass below `B` is at most `W(h)`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Appendix B.1, (B.14), p. 132, and
  (B.39), p. 136.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace IncompressibleFlow.SharpHolder

/-- `μ_A(p) = g_A(p - 1) - g_A(p + 1)`, `g_A(y) = A/(y² + A²)`. -/
def shearMassDensity (A p : ℝ) : ℝ := A / ((p - 1) ^ 2 + A ^ 2) - A / ((p + 1) ^ 2 + A ^ 2)

/-- The weight `d(p) = (2p)^{1/2} + √2 - 2 |p - 1|^{1/2}` of the line defect. -/
def shearLineWeight (p : ℝ) : ℝ := (2 * p) ^ (1 / 2 : ℝ) + Real.sqrt 2 - 2 * |p - 1| ^ (1 / 2 : ℝ)

/-- The line defect `D_c(A) = ∫_{1/9}^{c} d(p) μ_A(p) dp`. -/
def shearLineDefect (c A : ℝ) : ℝ≥0∞ :=
  ∫⁻ p in Ioc (1 / 9) c, ENNReal.ofReal (shearLineWeight p * shearMassDensity A p)

/-- The mass of `|Δ|` over the heights in `(h, B]`. -/
def shearOuterMassBelow (h B : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioc h B, ∫⁻ p in Ioi 0, ‖shearDifference p t‖ₑ

/-! ### The weight and the density -/

/-- `d ≥ 0` on `[1/9, 9]`: with `s = √p`, `(√2 (s + 1))² = 2 (s + 1)² ≥ 4 |s² - 1|` for
`1/3 ≤ s ≤ 3`. -/
theorem shearLineWeight_nonneg {p : ℝ} (h₁ : 1 / 9 ≤ p) (h₂ : p ≤ 9) : 0 ≤ shearLineWeight p := by
  have hp : 0 ≤ p := by linarith
  have hs0 := Real.sqrt_nonneg p
  have hss : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp
  have hs₁ : 1 / 3 ≤ Real.sqrt p := by nlinarith
  have hs₂ : Real.sqrt p ≤ 3 := by nlinarith
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hcc : Real.sqrt |p - 1| ^ 2 = |p - 1| := Real.sq_sqrt (abs_nonneg _)
  have hq : 4 * |p - 1| ≤ 2 * (Real.sqrt p + 1) ^ 2 := by
    have hlo : -((Real.sqrt p + 1) ^ 2 / 2) ≤ p - 1 := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ Real.sqrt p + 1)
        (by linarith : 0 ≤ 3 * Real.sqrt p - 1)]
    have hhi : p - 1 ≤ (Real.sqrt p + 1) ^ 2 / 2 := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ Real.sqrt p + 1)
        (by linarith : 0 ≤ 3 - Real.sqrt p)]
    linarith [abs_le.2 ⟨hlo, hhi⟩]
  rw [shearLineWeight, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_mul (by norm_num) p,
    sub_nonneg]
  have key : (2 * Real.sqrt |p - 1|) ^ 2 ≤ (Real.sqrt 2 * Real.sqrt p + Real.sqrt 2) ^ 2 := by
    rw [show (Real.sqrt 2 * Real.sqrt p + Real.sqrt 2) ^ 2 =
      Real.sqrt 2 ^ 2 * (Real.sqrt p + 1) ^ 2 by ring, h2, mul_pow, hcc]
    linarith
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 key

/-- `μ_A ≥ 0` on `p ≥ 0`: `(p + 1)² ≥ (p - 1)²`. -/
theorem shearMassDensity_nonneg {A p : ℝ} (hA : 0 < A) (hp : 0 ≤ p) : 0 ≤ shearMassDensity A p :=
  sub_nonneg.2 (div_le_div_of_nonneg_left hA.le (by positivity) (by nlinarith))

/-- `μ_A(p) = 4Ap/(((p - 1)² + A²)((p + 1)² + A²))`. -/
theorem shearMassDensity_eq {A : ℝ} (hA : 0 < A) (p : ℝ) :
    shearMassDensity A p = 4 * A * p / (((p - 1) ^ 2 + A ^ 2) * ((p + 1) ^ 2 + A ^ 2)) := by
  rw [shearMassDensity, div_sub_div _ _ (by positivity) (by positivity)]
  congr 1
  ring

/-- `Δ_{1D} ≤ 0` on `p ≥ 0`: the box at `p - 1` contains the one at `p + 1`, and
`g_A(p + 1) ≤ g_A(p - 1)`. -/
theorem shearMass_nonpos {B A p : ℝ} (hA : 0 < A) (hp : 0 ≤ p) : shearMass B A p ≤ 0 := by
  have hg₁ : 0 ≤ A / ((p + 1) ^ 2 + A ^ 2) := by positivity
  have hg := shearMassDensity_nonneg hA hp
  rw [shearMassDensity] at hg
  have hle : |p - 1| ≤ |p + 1| := by
    rw [abs_of_nonneg (by linarith : 0 ≤ p + 1)]
    exact abs_le.2 ⟨by linarith, by linarith⟩
  rw [shearMass]
  split_ifs with h₁ h₂
  · linarith
  · exact absurd (hle.trans h₁) h₂
  · linarith [show 0 ≤ A / ((p - 1) ^ 2 + A ^ 2) by positivity]
  · simp

/-- Inside the boxes, `|Δ_{1D}| = μ_A` on `p ≥ 0`. -/
theorem abs_shearMass_eq {B A p : ℝ} (hA : 0 < A) (hp : 0 ≤ p) (hpB : p + 1 ≤ B) :
    |shearMass B A p| = shearMassDensity A p := by
  have h₁ : |p + 1| ≤ B := by rwa [abs_of_nonneg (by linarith)]
  have h₂ : |p - 1| ≤ B := abs_le.2 ⟨by linarith, by linarith⟩
  rw [shearMass, ite_eq_left h₁, ite_eq_left h₂, abs_sub_comm]
  exact abs_of_nonneg (shearMassDensity_nonneg hA hp)

/-- `|Δ_{1D}| ≤ g_A(p - 1)` on `p ≥ 0`. -/
theorem abs_shearMass_le_of_nonneg {B A p : ℝ} (hA : 0 < A) (hp : 0 ≤ p) :
    |shearMass B A p| ≤ A / ((p - 1) ^ 2 + A ^ 2) := by
  have hg₁ : 0 ≤ A / ((p + 1) ^ 2 + A ^ 2) := by positivity
  have hg₂ : 0 ≤ A / ((p - 1) ^ 2 + A ^ 2) := by positivity
  rw [abs_of_nonpos (shearMass_nonpos hA hp), shearMass]
  split_ifs <;> linarith

/-- `(l/A)³ μ_l ≤ μ_A` on `p ≥ 0` for `0 < l ≤ A`: `(y² + l²)/(y² + A²) ≥ l²/A²`. -/
theorem shearMassDensity_le {l A p : ℝ} (hl : 0 < l) (hlA : l ≤ A) (hp : 0 ≤ p) :
    (l / A) ^ 3 * shearMassDensity l p ≤ shearMassDensity A p := by
  have hA : 0 < A := hl.trans_le hlA
  have hsq : l ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ hl.le hlA 2
  have h₁ : l ^ 2 * ((p - 1) ^ 2 + A ^ 2) ≤ A ^ 2 * ((p - 1) ^ 2 + l ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_right hsq (sq_nonneg (p - 1))]
  have h₂ : l ^ 2 * ((p + 1) ^ 2 + A ^ 2) ≤ A ^ 2 * ((p + 1) ^ 2 + l ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_right hsq (sq_nonneg (p + 1))]
  rw [shearMassDensity_eq hl, shearMassDensity_eq hA, div_pow, div_mul_div_comm,
    div_le_div_iff₀ (by positivity) (by positivity)]
  calc l ^ 3 * (4 * l * p) * (((p - 1) ^ 2 + A ^ 2) * ((p + 1) ^ 2 + A ^ 2))
      = 4 * p * (l ^ 2 * ((p - 1) ^ 2 + A ^ 2) * (l ^ 2 * ((p + 1) ^ 2 + A ^ 2))) := by ring
    _ ≤ 4 * p * (A ^ 2 * ((p - 1) ^ 2 + l ^ 2) * (A ^ 2 * ((p + 1) ^ 2 + l ^ 2))) := by
        gcongr
    _ = 4 * A * p * (A ^ 3 * (((p - 1) ^ 2 + l ^ 2) * ((p + 1) ^ 2 + l ^ 2))) := by ring

/-! ### The line defect -/

/-- `(l/A)³ D_c(l) ≤ D_c(A)` for `0 < l ≤ A` and `c ≤ 9`. -/
theorem shearLineDefect_le {c l A : ℝ} (hc : c ≤ 9) (hl : 0 < l) (hlA : l ≤ A) :
    ENNReal.ofReal ((l / A) ^ 3) * shearLineDefect c l ≤ shearLineDefect c A := by
  rw [shearLineDefect, shearLineDefect, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' measurableSet_Ioc fun p hp ↦ ?_
  have hd := shearLineWeight_nonneg hp.1.le (hp.2.trans hc)
  have hp0 : 0 ≤ p := by linarith [hp.1]
  rw [← ENNReal.ofReal_mul (pow_pos (div_pos hl (hl.trans_le hlA)) 3).le]
  refine ENNReal.ofReal_le_ofReal ?_
  calc (l / A) ^ 3 * (shearLineWeight p * shearMassDensity l p)
      = shearLineWeight p * ((l / A) ^ 3 * shearMassDensity l p) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (shearMassDensity_le hl hlA hp0) hd

/-- `∫_a^b g_A(p - e) dp = arctan ((b - e)/A) - arctan ((a - e)/A) ≤ π` for `a ≤ b`. -/
theorem lintegral_Ioc_div_sq_add_sq_le {A a b : ℝ} (hA : 0 < A) (hab : a ≤ b) (e : ℝ) :
    ∫⁻ p in Ioc a b, ENNReal.ofReal (A / ((p - e) ^ 2 + A ^ 2)) ≤ ENNReal.ofReal Real.pi := by
  rw [lintegral_Ioc_ofReal_deriv (g := fun p ↦ Real.arctan ((p - e) / A)) hab
    (by fun_prop) (fun p _ ↦ ?_) (fun p _ ↦ by positivity)]
  · refine ENNReal.ofReal_le_ofReal ?_
    linarith [Real.arctan_lt_pi_div_two ((b - e) / A),
      Real.neg_pi_div_two_lt_arctan ((a - e) / A)]
  · refine (((hasDerivAt_id' p).sub_const e).div_const A).arctan.congr_deriv ?_
    field_simp
    ring

/-- **The residual line cost** (Chen and Hou, Part I, (B.39)): for `B ≥ 4`, `A > 0`, `c ≤ 9`
and `c ≤ B - 1`, `S_{in,x}(B, A) + S_{1D}(B, A) + D_c(A) ≤ √2 π + X(A)`. -/
theorem shearInnerMassCost_add_shearLineCost_le {B A c : ℝ} (hB : 4 ≤ B) (hA : 0 < A)
    (hc : c ≤ 9) (hcB : c ≤ B - 1) :
    shearInnerMassCost B A + shearLineCost B A + shearLineDefect c A ≤
      ENNReal.ofReal (Real.sqrt 2 * Real.pi) + shearMassEnvelope A := by
  have hmeas := measurable_shearMass B A
  -- the mass cost over `(0, 1/9]`, `(1/9, 9]` and `(9, ∞)`
  have hcost : shearMassCost B A =
      (∫⁻ p in Ioc 0 (1 / 9), ENNReal.ofReal ((2 * p) ^ (1 / 2 : ℝ) * |shearMass B A p|)) +
      (∫⁻ p in Ioc (1 / 9) 9, ENNReal.ofReal ((2 * p) ^ (1 / 2 : ℝ) * |shearMass B A p|)) +
      shearInnerMassCost B A := by
    rw [shearMassCost, shearInnerMassCost, ← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 9),
      lintegral_union measurableSet_Ioi Ioc_disjoint_Ioi_same,
      ← Ioc_union_Ioc_eq_Ioc (by norm_num : (0 : ℝ) ≤ 1 / 9) (by norm_num : (1 / 9 : ℝ) ≤ 9),
      lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl)]
  have hline : shearLineCost B A =
      2 * (∫⁻ p in Ioc (1 / 9) 9, ENNReal.ofReal (|shearMass B A p| * |p - 1| ^ (1 / 2 : ℝ))) +
      (∫⁻ p in Ioc 0 (1 / 9), ENNReal.ofReal ((2 * p) ^ (1 / 2 : ℝ) * |shearMass B A p|)) +
      ENNReal.ofReal (Real.sqrt 2 * |Real.pi + ∫ p in Ioc (1 / 9) 9, shearMass B A p|) := by
    simp only [shearLineCost, mul_comm |shearMass B A _|]
  -- the defect is at most its integral over `(1/9, 9]`
  have hdef : shearLineDefect c A ≤
      ∫⁻ p in Ioc (1 / 9) 9, ENNReal.ofReal (shearLineWeight p * |shearMass B A p|) := by
    rw [shearLineDefect]
    refine (setLIntegral_congr_fun measurableSet_Ioc fun p hp ↦ ?_).trans_le
      (lintegral_mono_set (Ioc_subset_Ioc_right hc))
    rw [abs_shearMass_eq hA (by linarith [hp.1]) (by linarith [hp.2])]
  -- on `(1/9, 9]`, `2 |p - 1|^{1/2} + d(p) = (2p)^{1/2} + √2`
  have hsplit :
      2 * (∫⁻ p in Ioc (1 / 9) 9, ENNReal.ofReal (|shearMass B A p| * |p - 1| ^ (1 / 2 : ℝ))) +
        ∫⁻ p in Ioc (1 / 9) 9, ENNReal.ofReal (shearLineWeight p * |shearMass B A p|) =
      (∫⁻ p in Ioc (1 / 9) 9, ENNReal.ofReal ((2 * p) ^ (1 / 2 : ℝ) * |shearMass B A p|)) +
        ENNReal.ofReal (Real.sqrt 2) * ∫⁻ p in Ioc (1 / 9) 9, ENNReal.ofReal |shearMass B A p| := by
    rw [← lintegral_const_mul' _ _ (by norm_num), ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_add_left (by fun_prop), ← lintegral_add_left (by fun_prop)]
    refine setLIntegral_congr_fun measurableSet_Ioc fun p hp ↦ ?_
    have hd := shearLineWeight_nonneg hp.1.le hp.2
    rw [show (2 : ℝ≥0∞) * ENNReal.ofReal (|shearMass B A p| * |p - 1| ^ (1 / 2 : ℝ)) =
        ENNReal.ofReal (2 * (|shearMass B A p| * |p - 1| ^ (1 / 2 : ℝ))) by
      rw [ENNReal.ofReal_mul (p := 2) (by norm_num), ENNReal.ofReal_ofNat],
      ← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
      ← ENNReal.ofReal_add (by positivity) (mul_nonneg hd (abs_nonneg _)),
      ← ENNReal.ofReal_add (mul_nonneg (Real.rpow_nonneg (by linarith [hp.1]) _) (abs_nonneg _))
        (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))]
    congr 1
    simp only [shearLineWeight]
    ring
  -- the mass over `(1/9, 9]` is at most `π`
  have hi : IntegrableOn (shearMass B A) (Ioc (1 / 9 : ℝ) 9) := by
    simpa using integrableOn_shearMass_mul (B := B) hA (φ := fun _ ↦ 1) continuousOn_const
      (show volume (Ioc (1 / 9 : ℝ) 9) ≠ ⊤ by simp)
  have hM : ∫⁻ p in Ioc (1 / 9) 9, ENNReal.ofReal |shearMass B A p| =
      ENNReal.ofReal (∫ p in Ioc (1 / 9) 9, |shearMass B A p|) :=
    (ofReal_integral_eq_lintegral_ofReal hi.abs (Eventually.of_forall fun p ↦ abs_nonneg _)).symm
  have hP : ∫ p in Ioc (1 / 9) 9, shearMass B A p = -∫ p in Ioc (1 / 9) 9, |shearMass B A p| := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioc fun p hp ↦ ?_
    rw [abs_of_nonpos (shearMass_nonpos hA (by linarith [hp.1])), neg_neg]
  have hπ : ∫ p in Ioc (1 / 9) 9, |shearMass B A p| ≤ Real.pi := by
    refine (ENNReal.ofReal_le_ofReal_iff Real.pi_pos.le).1 ?_
    rw [← hM]
    refine le_trans (setLIntegral_mono' measurableSet_Ioc fun p hp ↦
      ENNReal.ofReal_le_ofReal (abs_shearMass_le_of_nonneg hA (by linarith [hp.1])))
      (lintegral_Ioc_div_sq_add_sq_le hA (by norm_num) 1)
  have hlast : ENNReal.ofReal (Real.sqrt 2) *
        (∫⁻ p in Ioc (1 / 9) 9, ENNReal.ofReal |shearMass B A p|) +
      ENNReal.ofReal (Real.sqrt 2 * |Real.pi + ∫ p in Ioc (1 / 9) 9, shearMass B A p|) =
      ENNReal.ofReal (Real.sqrt 2 * Real.pi) := by
    have h0 : 0 ≤ ∫ p in Ioc (1 / 9) 9, |shearMass B A p| :=
      setIntegral_nonneg measurableSet_Ioc fun p _ ↦ abs_nonneg _
    rw [hM, hP, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _), ← sub_eq_add_neg,
      abs_of_nonneg (sub_nonneg.2 hπ), ← ENNReal.ofReal_add (by positivity)
        (mul_nonneg (Real.sqrt_nonneg _) (sub_nonneg.2 hπ))]
    congr 1
    ring
  calc shearInnerMassCost B A + shearLineCost B A + shearLineDefect c A
      ≤ shearInnerMassCost B A + shearLineCost B A +
          ∫⁻ p in Ioc (1 / 9) 9, ENNReal.ofReal (shearLineWeight p * |shearMass B A p|) := by
        gcongr
    _ = shearInnerMassCost B A +
          (∫⁻ p in Ioc 0 (1 / 9), ENNReal.ofReal ((2 * p) ^ (1 / 2 : ℝ) * |shearMass B A p|)) +
          ENNReal.ofReal (Real.sqrt 2 * |Real.pi + ∫ p in Ioc (1 / 9) 9, shearMass B A p|) +
          (2 * (∫⁻ p in Ioc (1 / 9) 9,
              ENNReal.ofReal (|shearMass B A p| * |p - 1| ^ (1 / 2 : ℝ))) +
            ∫⁻ p in Ioc (1 / 9) 9, ENNReal.ofReal (shearLineWeight p * |shearMass B A p|)) := by
        rw [hline]
        ring
    _ = (ENNReal.ofReal (Real.sqrt 2) *
            (∫⁻ p in Ioc (1 / 9) 9, ENNReal.ofReal |shearMass B A p|) +
          ENNReal.ofReal (Real.sqrt 2 * |Real.pi + ∫ p in Ioc (1 / 9) 9, shearMass B A p|)) +
          shearMassCost B A := by
        rw [hsplit, hcost]
        ring
    _ ≤ _ := by
        rw [hlast]
        gcongr
        exact shearMassCost_le_envelope hB hA

/-! ### The outer cost -/

/-- `S_out(B, h) ≤ 2 (2h)^{1/2} ∫_h^B ∫_{p > 0} |Δ|`. -/
theorem shearOuterCost_le_mass_below {B h : ℝ} (hB : 4 ≤ B) (hh : 0 < h) :
    shearOuterCost B h ≤ ENNReal.ofReal (2 * (2 * h) ^ (1 / 2 : ℝ)) * shearOuterMassBelow h B := by
  have hswap := lintegral_lintegral_swap (μ := volume.restrict (Ioi (0 : ℝ)))
    (ν := volume.restrict (Ioc h B)) (f := fun p t ↦ ‖localShearDifference B p t‖ₑ)
    (measurable_localShearDifference B).enorm.aemeasurable
  rw [shearOuterCost, shearOuterMassBelow, hswap, ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_ofNat]
  gcongr _ * ?_
  exact setLIntegral_mono' measurableSet_Ioc fun t ht ↦
    lintegral_enorm_localShearDifference_le (by linarith) (hh.trans ht.1) ht.2

/-- The mass below `B` is at most the mass `W(h)` above `h`. -/
theorem shearOuterMassBelow_le (h B : ℝ) : shearOuterMassBelow h B ≤ shearOuterMass h :=
  lintegral_mono_set Ioc_subset_Ioi_self

end IncompressibleFlow.SharpHolder
