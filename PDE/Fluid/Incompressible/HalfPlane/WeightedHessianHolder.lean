/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.HalfPlane.WeightedHessian

/-!
# Local Hölder increments of the Hessian of the quadrant potential

For a Hölder vorticity with `|f(y)| ≤ M min(|y|^a, |y|^(-b))` and local Hölder constant
`M min(|x|^γ, |x|^ε)` on `B(x, |x|/2)`, the Hessian of the grouped stream function
`Ψ = quadrantPotential f` has local increments, near the origin and away from it, behind Chen and
Hou, Part I, Lemma 6.12.

Multiplied by the Hölder weight `ψ₁ ≍ min(|x|^(-γ), |x|^(-ε))` these give the `C^{1/2}` bound of
Lemma 6.12 for nearby points; points far apart are handled by the pointwise bounds of Lemma 6.11.

## Main results

* `exists_abs_hessian_sub_quartic_sub_le`: near the origin, for `|x| ≤ 1`, `32 |x - z| ≤ |x|`,
  `2 < a < 4` and `γ ≤ a - α`,
  `|(∂ₗ∂ₖΨ - d ∂ₖ∂ₗG)(x) - (∂ₗ∂ₖΨ - d ∂ₖ∂ₗG)(z)| ≤ C M |x|^γ |x - z|^α`, `d = quarticCoefficient f`.
* `exists_abs_hessian_sub_le_of_one_le`: away from the origin, for `|x| ≥ 1`,
  `|x - z| ≤ |x|^(-ε/α)/32` and `ε ≥ 0`, `|∂ₗ∂ₖΨ(x) - ∂ₗ∂ₖΨ(z)| ≤ C M |x|^ε |x - z|^α`.

## How it works

Both proofs use the two-point form of the engine, `exists_abs_hessian_sub_far_sub_le`, which
compares the increment of the Hessian between `x` and `z` with that of the far potential of
`farSource R f`, with `R = 8|x|`. Near the origin the local radius is `δ = |x|/16`, and the integral
of `|f(y)|/|x - y|³` over the middle region `δ ≤ |x - y|`, `|y| ≤ 2R` is bounded crudely by
`lintegral_middleRegion_le`. The far part is then the increment of the fourth-order expansion
(`GreenFunction.IsQuadrantFarDensity.abs_hessian_expansion_sub_le`, with
`integral_abs_farSource_div_pow_six_le`), and the change of the quartic term is controlled by the
near moment `abs_quarticCoefficient_sub_farSource_le` and `abs_quarticHessian_sub_le`. Away from the
origin the radius is `δ = |x|^(-ε/α)/16`, the middle integral is bounded directly, and the far part
is the Lipschitz bound `GreenFunction.IsQuadrantFarDensity.abs_hessian_sub_le` with
`integral_abs_farSource_div_pow_three_le`. In both cases the inequality `t ≤ t^α ρ^(1-α)` for
`0 ≤ t ≤ ρ` (`le_rpow_mul_rpow_of_le`) turns the Lipschitz factors `|x - z|` into the Hölder factor
`|x - z|^α`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 6.3.3, Lemma 6.11 and (6.58),
  p. 107, Lemma 6.12, p. 108, and Appendix C.3.3, pp. 146-148.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric GreenFunction PotentialTheory PotentialTheory.Planar
open SobolevSpace SobolevSpace.Approximation
open scoped Topology

namespace IncompressibleFlow

variable {α a b γ ε : ℝ}

/-- For `0 ≤ t ≤ ρ` and `α ≤ 1`, `t ≤ t^α ρ^(1-α)`. -/
theorem le_rpow_mul_rpow_of_le {t ρ : ℝ} (ht : 0 ≤ t) (htρ : t ≤ ρ) (hα1 : α ≤ 1) :
    t ≤ t ^ α * ρ ^ (1 - α) := by
  calc t = t ^ α * t ^ (1 - α) := by
        rw [← Real.rpow_add' ht (by norm_num : α + (1 - α) ≠ 0), add_sub_cancel, Real.rpow_one]
    _ ≤ t ^ α * ρ ^ (1 - α) := by
        gcongr

/-- **The local increment near the origin** (Part I, Lemma 6.12). For a Hölder vorticity with
`|f(y)| ≤ M min(|y|^a, |y|^(-b))`, `2 < a < 4`, `b > 0`, and local Hölder constant
`M min(|x|^γ, |x|^ε)` on `B(x, |x|/2)` with `γ ≤ a - α`: for `x, z` in the open upper half-plane
with `|x| ≤ 1` and `32 |x - z| ≤ |x|`,
`|(∂ₗ∂ₖΨ(x) - d ∂ₖ∂ₗG(x)) - (∂ₗ∂ₖΨ(z) - d ∂ₖ∂ₗG(z))| ≤ C M |x|^γ |x - z|^α`,
`d = quarticCoefficient f`. -/
theorem exists_abs_hessian_sub_quartic_sub_le (hα : 0 < α) (hα1 : α < 1) (ha : 2 < a)
    (ha4 : a < 4) (hb : 0 < b) (hγa : γ ≤ a - α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ⦃f : ℝ^2 → ℝ⦄ ⦃M : ℝ⦄, IsHolderVorticity α f →
      (∀ y : ℝ^2, 0 ≤ y 1 → |f y| ≤ M * min (‖y‖ ^ a) (‖y‖ ^ (-b))) →
      (∀ x : ℝ^2, x ≠ 0 → ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 → ‖x - y‖ ≤ ‖x‖ / 2 →
        ‖x - z‖ ≤ ‖x‖ / 2 → |f y - f z| ≤ M * min (‖x‖ ^ γ) (‖x‖ ^ ε) * ‖y - z‖ ^ α) →
      ∀ x z : ℝ^2, 0 < x 1 → 0 < z 1 → ‖x‖ ≤ 1 → 32 * ‖x - z‖ ≤ ‖x‖ → ∀ k l : Fin 2,
        |((∂[l] (∂[k] (quadrantPotential f))) x - quarticCoefficient f * quarticHessian k l x) -
            ((∂[l] (∂[k] (quadrantPotential f))) z -
              quarticCoefficient f * quarticHessian k l z)| ≤
          C * M * ‖x‖ ^ γ * ‖x - z‖ ^ α := by
  obtain ⟨C₂, hC₂, hE⟩ := exists_abs_hessian_sub_far_sub_le hα hα1
  have ha0 : 0 < a := by linarith
  have ha2 : 0 < a - 2 := by linarith
  have h4a : 0 < 4 - a := by linarith
  set KI : ℝ := 4194304 * Real.pi * 16 ^ a
  set KB : ℝ := 2944 / (9 * Real.pi) * 8 * (2 * Real.pi * 8 ^ (a - 4) / (4 - a))
  set KC : ℝ := 192 * 16 ^ (a - 2) / (a - 2)
  have hKI : 0 ≤ KI := by positivity
  have hKB : 0 ≤ KB := by positivity
  have hKC : 0 ≤ KC := by positivity
  refine ⟨C₂ * (1 + 2 ^ a * 16 ^ α) + C₂ * KI + KB + KC, by positivity, ?_⟩
  intro f M hf hS hH x z hx hz hx1 hxz k l
  have hM := nonneg_of_abs_le_min hS
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  set r := ‖x‖ with hr_def
  have hr : 0 < r := norm_pos_iff.mpr hx0
  set t := ‖x - z‖ with ht_def
  have ht : 0 ≤ t := norm_nonneg _
  set δ := r / 16 with hδ_def
  set R := 8 * r with hR_def
  have hδ : 0 < δ := by positivity
  have hR : 0 < R := by positivity
  have hzr : ‖z‖ ≤ 2 * r := by linarith [norm_le_norm_add_norm_sub' z x, norm_sub_rev z x]
  set F := farSource R f
  have hfar := hf.isQuadrantFarDensity_farSource hR
  -- the engine
  have hB : ∀ y, 0 ≤ y 1 → ‖x - y‖ ≤ 2 * δ → |f y| ≤ M * (2 * r) ^ a := fun y hy hxy ↦ by
    refine (abs_le_mul_rpow_of_le_min hS hy).trans (mul_le_mul_of_nonneg_left ?_ hM)
    exact Real.rpow_le_rpow (norm_nonneg _)
      (by linarith [norm_le_norm_add_norm_sub' y x, norm_sub_rev y x]) ha0.le
  have hL : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → ‖x - y‖ ≤ 2 * δ → ‖x - z‖ ≤ 2 * δ →
      |f y - f z| ≤ M * min (r ^ γ) (r ^ ε) * ‖y - z‖ ^ α := fun y z hy hz hxy hxz ↦
    hH x hx0 y z hy hz (by linarith) (by linarith)
  have hI := lintegral_middleRegion_le hS ha0.le (x := x) hδ hR 3
  have h1 := hE hf hx hδ (by linarith) hB hL (by positivity) hI hz (by linarith) k l
  -- the far part
  have h2 := hfar.abs_hessian_expansion_sub_le k l (x := x) (z := z) (by linarith)
    (by linarith)
  have h2' := integral_abs_farSource_div_pow_six_le hS ha4 hR
  -- the near moment
  have h3 := abs_quarticCoefficient_sub_farSource_le hS hf ha hb hR
  have hQ := abs_quarticHessian_sub_le k l x z
  -- arithmetic
  set w := M * r ^ γ * t ^ α
  have hw : 0 ≤ w := by positivity
  have htr : t ≤ r := by linarith
  have hkey : M * r ^ (a - 1) * t ≤ w := by
    have h := le_rpow_mul_rpow_of_le ht htr hα1.le
    have e : r ^ (a - 1) * r ^ (1 - α) = r ^ (a - α) := by
      rw [← Real.rpow_add hr]; congr 1; ring
    have hγ' : r ^ (a - α) ≤ r ^ γ := Real.rpow_le_rpow_of_exponent_ge hr hx1 hγa
    calc M * r ^ (a - 1) * t ≤ M * r ^ (a - 1) * (t ^ α * r ^ (1 - α)) := by gcongr
      _ = M * r ^ (a - α) * t ^ α := by rw [← e]; ring
      _ ≤ w := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hγ' hM) (by positivity)
  have hmax : max ‖x‖ ‖z‖ ≤ 2 * r := max_le (by linarith) hzr
  have hT1 : C₂ * (M * min (r ^ γ) (r ^ ε) + M * (2 * r) ^ a * δ ^ (-α)) * t ^ α +
      C₂ * t * (16 * Real.pi * M * (2 * R) ^ a * R ^ 2 / δ ^ 3) ≤
        C₂ * ((1 + 2 ^ a * 16 ^ α) * w) + C₂ * (KI * w) := by
    have hLw : M * min (r ^ γ) (r ^ ε) * t ^ α ≤ w :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (min_le_left _ _) hM)
        (by positivity)
    have hBw : M * (2 * r) ^ a * δ ^ (-α) * t ^ α ≤ 2 ^ a * 16 ^ α * w := by
      have e : (2 * r) ^ a * δ ^ (-α) = 2 ^ a * 16 ^ α * r ^ (a - α) := by
        rw [Real.mul_rpow (by norm_num) hr.le, show δ = r * 16⁻¹ by simp only [δ]; ring,
          Real.mul_rpow hr.le (by norm_num), Real.inv_rpow (by norm_num),
          Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 16), inv_inv, sub_eq_add_neg,
          Real.rpow_add hr]
        ring
      have hγ' : r ^ (a - α) ≤ r ^ γ := Real.rpow_le_rpow_of_exponent_ge hr hx1 hγa
      calc M * (2 * r) ^ a * δ ^ (-α) * t ^ α = 2 ^ a * 16 ^ α * (M * r ^ (a - α) * t ^ α) := by
            rw [mul_assoc M, e]; ring
        _ ≤ 2 ^ a * 16 ^ α * w := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hγ' hM) (by positivity))
            (by positivity)
    have hIw : t * (16 * Real.pi * M * (2 * R) ^ a * R ^ 2 / δ ^ 3) ≤ KI * w := by
      have e : 16 * Real.pi * M * (2 * R) ^ a * R ^ 2 / δ ^ 3 = KI * (M * r ^ (a - 1)) := by
        rw [show 2 * R = 16 * r by simp only [R]; ring, Real.mul_rpow (by norm_num) hr.le,
          Real.rpow_sub hr, Real.rpow_one]
        simp only [KI, R, δ]
        field_simp
        ring
      rw [e]
      calc t * (KI * (M * r ^ (a - 1))) = KI * (M * r ^ (a - 1) * t) := by ring
        _ ≤ KI * w := mul_le_mul_of_nonneg_left hkey hKI
    have := mul_le_mul_of_nonneg_left (add_le_add hLw hBw) hC₂
    have := mul_le_mul_of_nonneg_left hIw hC₂
    nlinarith
  have hT2 : 2944 / (9 * Real.pi) * max ‖x‖ ‖z‖ ^ 3 * t *
      ∫ y in quadrant, |F y| / ‖y‖ ^ 6 ≤ KB * w := by
    calc 2944 / (9 * Real.pi) * max ‖x‖ ‖z‖ ^ 3 * t * ∫ y in quadrant, |F y| / ‖y‖ ^ 6
        ≤ 2944 / (9 * Real.pi) * (2 * r) ^ 3 * t *
            (M * (2 * Real.pi * R ^ (a - 4) / (4 - a))) := by
          gcongr
      _ = KB * (M * r ^ (a - 1) * t) := by
          rw [show R ^ (a - 4) = 8 ^ (a - 4) * r ^ (a - 4) from
            Real.mul_rpow (by norm_num) hr.le]
          have e : r ^ (a - 4) * r ^ 3 = r ^ (a - 1) := by
            rw [← Real.rpow_natCast, ← Real.rpow_add hr]; congr 1; push_cast; ring
          simp only [KB]
          rw [← e]
          field_simp
          ring
      _ ≤ KB * w := mul_le_mul_of_nonneg_left hkey hKB
  have hT3 : |quarticCoefficient f - quarticCoefficient F| *
      |quarticHessian k l x - quarticHessian k l z| ≤ KC * w := by
    calc |quarticCoefficient f - quarticCoefficient F| *
          |quarticHessian k l x - quarticHessian k l z|
        ≤ 48 * M * (2 * R) ^ (a - 2) / (a - 2) * (2 * (2 * r) * t) := by
          refine mul_le_mul h3 (hQ.trans ?_) (abs_nonneg _) (by positivity)
          gcongr
      _ = KC * (M * r ^ (a - 1) * t) := by
          rw [show 2 * R = 16 * r by simp only [R]; ring, Real.mul_rpow (by norm_num) hr.le]
          have e : r ^ (a - 2) * r = r ^ (a - 1) := by
            rw [← Real.rpow_add_one hr.ne']; congr 1; ring
          simp only [KC]
          rw [← e]
          field_simp
          ring
      _ ≤ KC * w := mul_le_mul_of_nonneg_left hkey hKC
  have hsplit : ((∂[l] (∂[k] (quadrantPotential f))) x - quarticCoefficient f *
        quarticHessian k l x) - ((∂[l] (∂[k] (quadrantPotential f))) z -
          quarticCoefficient f * quarticHessian k l z) =
      (((∂[l] (∂[k] (quadrantPotential f))) x - (∂[l] (∂[k] (quadrantPotential F))) x) -
        ((∂[l] (∂[k] (quadrantPotential f))) z - (∂[l] (∂[k] (quadrantPotential F))) z)) +
      (((∂[l] (∂[k] (quadrantPotential F))) x - quarticCoefficient F * quarticHessian k l x) -
        ((∂[l] (∂[k] (quadrantPotential F))) z - quarticCoefficient F * quarticHessian k l z)) -
      (quarticCoefficient f - quarticCoefficient F) *
        (quarticHessian k l x - quarticHessian k l z) := by ring
  rw [hsplit]
  have hC : (C₂ * (1 + 2 ^ a * 16 ^ α) + C₂ * KI + KB + KC) * M * r ^ γ * t ^ α =
      C₂ * ((1 + 2 ^ a * 16 ^ α) * w) + C₂ * (KI * w) + KB * w + KC * w := by
    simp only [w]; ring
  rw [hC]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul]
  refine add_le_add ((abs_add_le _ _).trans (add_le_add (h1.trans hT1) (h2.trans hT2))) hT3

/-- **The local increment away from the origin** (Part I, Lemma 6.12). For a Hölder vorticity
with `|f(y)| ≤ M min(|y|^a, |y|^(-b))`, `a ≥ 0`, `b > 0`, and local Hölder constant
`M min(|x|^γ, |x|^ε)` on `B(x, |x|/2)` with `ε ≥ 0`: for `x, z` in the open upper half-plane with
`|x| ≥ 1` and `|x - z| ≤ |x|^(-ε/α)/32`,
`|∂ₗ∂ₖΨ(x) - ∂ₗ∂ₖΨ(z)| ≤ C M |x|^ε |x - z|^α`. -/
theorem exists_abs_hessian_sub_le_of_one_le (hα : 0 < α) (hα1 : α < 1) (ha : 0 ≤ a)
    (hb : 0 < b) (hε : 0 ≤ ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ⦃f : ℝ^2 → ℝ⦄ ⦃M : ℝ⦄, IsHolderVorticity α f →
      (∀ y : ℝ^2, 0 ≤ y 1 → |f y| ≤ M * min (‖y‖ ^ a) (‖y‖ ^ (-b))) →
      (∀ x : ℝ^2, x ≠ 0 → ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 → ‖x - y‖ ≤ ‖x‖ / 2 →
        ‖x - z‖ ≤ ‖x‖ / 2 → |f y - f z| ≤ M * min (‖x‖ ^ γ) (‖x‖ ^ ε) * ‖y - z‖ ^ α) →
      ∀ x z : ℝ^2, 0 < x 1 → 0 < z 1 → 1 ≤ ‖x‖ → ‖x - z‖ ≤ ‖x‖ ^ (-(ε / α)) / 32 →
        ∀ k l : Fin 2,
          |(∂[l] (∂[k] (quadrantPotential f))) x - (∂[l] (∂[k] (quadrantPotential f))) z| ≤
            C * M * ‖x‖ ^ ε * ‖x - z‖ ^ α := by
  obtain ⟨C₂, hC₂, hE⟩ := exists_abs_hessian_sub_far_sub_le hα hα1
  refine ⟨C₂ * (1 + 16 ^ α) + C₂ * (2 * Real.pi * 16 ^ α) + 2 * Real.pi, by positivity, ?_⟩
  intro f M hf hS hH x z hx hz hx1 hxz k l
  have hM := nonneg_of_abs_le_min hS
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  set r := ‖x‖ with hr_def
  have hr : 0 < r := by linarith
  set t := ‖x - z‖ with ht_def
  have ht : 0 ≤ t := norm_nonneg _
  set s := r ^ (-(ε / α)) with hs_def
  have hs : 0 < s := by positivity
  have hs1 : s ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hx1 (neg_nonpos.2 (div_nonneg hε hα.le))
  set δ := s / 16 with hδ_def
  set R := 8 * r with hR_def
  have hδ : 0 < δ := by positivity
  have hR : 0 < R := by positivity
  have htδ : 2 * t ≤ δ := by simp only [δ]; linarith
  have hzr : ‖z‖ ≤ 2 * r := by linarith [norm_le_norm_add_norm_sub' z x, norm_sub_rev z x]
  set F := farSource R f
  have hfar := hf.isQuadrantFarDensity_farSource hR
  have hB : ∀ y, 0 ≤ y 1 → ‖x - y‖ ≤ 2 * δ → |f y| ≤ M := fun y hy _ ↦
    abs_le_of_le_min hS ha hb.le hy
  have hL : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → ‖x - y‖ ≤ 2 * δ → ‖x - z‖ ≤ 2 * δ →
      |f y - f z| ≤ M * min (r ^ γ) (r ^ ε) * ‖y - z‖ ^ α := fun y z hy hz hxy hxz ↦
    hH x hx0 y z hy hz (by linarith) (by linarith)
  -- the cubic intermediate integral
  set I := M * (2 * Real.pi * δ ^ ((0 : ℝ) - 1) / (1 - 0))
  have hI : ∫⁻ y in {y : ℝ^2 | 0 < y 1 ∧ δ ≤ ‖x - y‖ ∧ ‖y‖ ≤ 2 * R},
      ENNReal.ofReal (|f y| / ‖x - y‖ ^ 3) ≤ ENNReal.ofReal I := by
    calc ∫⁻ y in {y : ℝ^2 | 0 < y 1 ∧ δ ≤ ‖x - y‖ ∧ ‖y‖ ≤ 2 * R},
          ENNReal.ofReal (|f y| / ‖x - y‖ ^ 3)
        ≤ ∫⁻ y in {y : ℝ^2 | 0 < y 1 ∧ δ ≤ ‖x - y‖ ∧ ‖y‖ ≤ 2 * R},
            ENNReal.ofReal (M * ‖x - y‖ ^ ((0 : ℝ) - 3)) := by
          refine setLIntegral_mono' (measurableSet_middleRegion x δ R) fun y hy ↦ ?_
          refine ENNReal.ofReal_le_ofReal ?_
          have hxy : 0 < ‖x - y‖ := lt_of_lt_of_le hδ hy.2.1
          rw [zero_sub, Real.rpow_neg hxy.le, ← div_eq_mul_inv]
          norm_cast
          gcongr
          exact abs_le_of_le_min hS ha hb.le hy.1.le
      _ ≤ ∫⁻ y in (ball x δ)ᶜ, ENNReal.ofReal (M * ‖x - y‖ ^ ((0 : ℝ) - 3)) := by
          refine lintegral_mono_set fun y hy ↦ ?_
          rw [mem_compl_iff, mem_ball, dist_comm, dist_eq_norm, not_lt]
          exact hy.2.1
      _ = ENNReal.ofReal I := lintegral_compl_ball_mul_rpow_sub_three x hM hδ (by norm_num)
  have h1 := hE hf hx hδ (by linarith) hB hL (by positivity) hI hz htδ k l
  have h2 := hfar.abs_hessian_sub_le k l (x := x) (z := z) (by linarith) (by linarith)
  have h2' := integral_abs_farSource_div_pow_three_le hS ha hb.le hR
  -- arithmetic
  set w := M * r ^ ε * t ^ α
  have hw : 0 ≤ w := by positivity
  have hrε : 1 ≤ r ^ ε := Real.one_le_rpow hx1 hε
  have hsα : s ^ (-α) = r ^ ε := by
    rw [hs_def, ← Real.rpow_mul hr.le, neg_mul_neg, div_mul_cancel₀ ε hα.ne']
  have hδα : δ ^ (-α) = 16 ^ α * r ^ ε := by
    rw [show δ = s * 16⁻¹ by simp only [δ]; ring, Real.mul_rpow hs.le (by norm_num), hsα,
      Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 16), inv_inv]
    ring
  have hT1 : C₂ * (M * min (r ^ γ) (r ^ ε) + M * δ ^ (-α)) * t ^ α + C₂ * t * I ≤
      C₂ * ((1 + 16 ^ α) * w) + C₂ * (2 * Real.pi * 16 ^ α * w) := by
    have hLw : (M * min (r ^ γ) (r ^ ε) + M * δ ^ (-α)) * t ^ α ≤ (1 + 16 ^ α) * w := by
      rw [hδα]
      have := mul_le_mul_of_nonneg_left (min_le_right (r ^ γ) (r ^ ε)) hM
      have h0 : 0 ≤ t ^ α := by positivity
      calc (M * min (r ^ γ) (r ^ ε) + M * (16 ^ α * r ^ ε)) * t ^ α
          ≤ (M * r ^ ε + M * (16 ^ α * r ^ ε)) * t ^ α := by gcongr
        _ = (1 + 16 ^ α) * w := by simp only [w]; ring
    have hIw : t * I ≤ 2 * Real.pi * 16 ^ α * w := by
      have htd : t ≤ t ^ α * δ ^ (1 - α) := le_rpow_mul_rpow_of_le ht (by linarith) hα1.le
      have e : δ ^ (1 - α) * δ ^ ((0 : ℝ) - 1) = δ ^ (-α) := by
        rw [← Real.rpow_add hδ]; congr 1; ring
      calc t * I ≤ t ^ α * δ ^ (1 - α) * I := by gcongr
        _ = 2 * Real.pi * M * t ^ α * (δ ^ (1 - α) * δ ^ ((0 : ℝ) - 1)) := by
            simp only [I]; ring
        _ = 2 * Real.pi * 16 ^ α * w := by rw [e, hδα]; simp only [w]; ring
    have := mul_le_mul_of_nonneg_left hLw hC₂
    have := mul_le_mul_of_nonneg_left hIw hC₂
    nlinarith
  have hT2 : 8 * t * ∫ y in quadrant, |F y| / ‖y‖ ^ 3 ≤ 2 * Real.pi * w := by
    have ht1 : t ≤ 1 := by linarith
    have htα : t ≤ t ^ α := by
      simpa using Real.rpow_le_rpow_of_exponent_ge' ht ht1 hα.le hα1.le
    calc 8 * t * ∫ y in quadrant, |F y| / ‖y‖ ^ 3 ≤ 8 * t * (M * (2 * Real.pi / R)) := by gcongr
      _ = 2 * Real.pi * M * t / r := by simp only [R]; field_simp
      _ ≤ 2 * Real.pi * M * t := div_le_self (by positivity) hx1
      _ ≤ 2 * Real.pi * (M * r ^ ε * t ^ α) := by
          have hMt : M * t ≤ M * r ^ ε * t ^ α := by
            calc M * t ≤ M * t ^ α := mul_le_mul_of_nonneg_left htα hM
              _ = M * 1 * t ^ α := by ring
              _ ≤ M * r ^ ε * t ^ α := by gcongr
          rw [mul_assoc (2 * Real.pi)]
          exact mul_le_mul_of_nonneg_left hMt (by positivity)
  have hsplit : (∂[l] (∂[k] (quadrantPotential f))) x - (∂[l] (∂[k] (quadrantPotential f))) z =
      (((∂[l] (∂[k] (quadrantPotential f))) x - (∂[l] (∂[k] (quadrantPotential F))) x) -
        ((∂[l] (∂[k] (quadrantPotential f))) z - (∂[l] (∂[k] (quadrantPotential F))) z)) +
      ((∂[l] (∂[k] (quadrantPotential F))) x - (∂[l] (∂[k] (quadrantPotential F))) z) := by ring
  rw [hsplit]
  have hC : (C₂ * (1 + 16 ^ α) + C₂ * (2 * Real.pi * 16 ^ α) + 2 * Real.pi) * M * r ^ ε *
      t ^ α = C₂ * ((1 + 16 ^ α) * w) + C₂ * (2 * Real.pi * 16 ^ α * w) + 2 * Real.pi * w := by
    simp only [w]; ring
  rw [hC]
  refine (abs_add_le _ _).trans (add_le_add ?_ (h2.trans hT2))
  exact h1.trans (by rw [mul_assoc C₂ t I]; linarith [hT1])

end IncompressibleFlow
