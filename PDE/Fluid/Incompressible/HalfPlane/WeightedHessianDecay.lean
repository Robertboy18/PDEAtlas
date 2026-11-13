/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.HalfPlane.WeightedHessian

/-!
# Decay of the Hessian of the quadrant potential and the second estimate of Lemma 6.11

For a Hölder vorticity with `|f(y)| ≤ M min(|y|^a, |y|^(-b))`, `0 < b ≤ 1`, and local Hölder
constant `M min(|x|^γ, |x|^ε)` on `B(x, |x|/2)`, `ε ≥ 0`, the Hessian of the grouped stream
function `Ψ` decays for `|x| ≥ 1`; with the estimate near the origin this gives the second estimate
of Part I, Lemma 6.11, and the interior limit of the Hessian at the origin.

For `|x| ≥ 1` the local radius of the decomposition is `δ = |x|^(-κ)/16`,
`κ = (ε + b/2)/α`. Then the local Hölder term `δ^α M |x|^ε` is `≲ M |x|^(-b/2)`, and the
intermediate annulus `δ ≤ |x - y| ≤ |x|/2` contributes `M |x|^(-b) log(|x|/δ) ≲ M |x|^(-b/2)`.
This is the shrinking singular region of Part I, footnote 93, with the exponent chosen from `α`
and the growth `ε` of the local Hölder constant.

## Main results

* `exists_abs_hessian_le_of_one_le`: `|∂ₗ∂ₖΨ(x)| ≤ C M |x|^(-b/2)` for `|x| ≥ 1`, the decay
  (6.59a) of Chen and Hou, Part I.
* `exists_abs_hessian_sub_mixed_le`: the second estimate of Part I, Lemma 6.11,
  `|∂ₗ∂ₖ(Ψ - c x₀x₁)(x)| ≤ C M min(|x|², 1)`, for `2 < a < 4` and `γ + α ≥ 2`.
* `tendsto_hessian_quadrantPotential`: `∂ₗ∂ₖΨ(x) → c (1 - δₖₗ)` as `x → 0` in the open upper
  half-plane, so the interior limit of the mixed derivative at the origin is `c`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 6.3.3, Lemma 6.11, p. 107,
  (6.59a) and footnote 93, p. 108.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric GreenFunction PotentialTheory PotentialTheory.Planar
open SobolevSpace SobolevSpace.Approximation
open scoped Topology

namespace IncompressibleFlow

variable {α a b γ ε : ℝ}

/-- For `0 < s ≤ t` and `b ≥ 0`, `t^(-b) ≤ s^(-b)`. -/
private theorem rpow_neg_le_of_le {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (hb : 0 ≤ b) :
    t ^ (-b) ≤ s ^ (-b) :=
  Real.rpow_le_rpow_of_nonpos hs hst (neg_nonpos.mpr hb)

/-- `(r/2)^(-b) = 2^b r^(-b)`. -/
private theorem div_two_rpow_neg {r : ℝ} (hr : 0 ≤ r) (b : ℝ) :
    (r / 2) ^ (-b) = 2 ^ b * r ^ (-b) := by
  rw [Real.div_rpow hr (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) b]
  field_simp

/-- For `r ≥ 1`, `r^(-b) ≤ r^(-b/2)` when `b ≥ 0`. -/
private theorem rpow_neg_le_rpow_neg_half {r : ℝ} (hr : 1 ≤ r) (hb : 0 ≤ b) :
    r ^ (-b) ≤ r ^ (-(b / 2)) :=
  Real.rpow_le_rpow_of_exponent_le hr (by linarith)

/-- **Decay of the Hessian** (Part I, (6.59a)). For a Hölder vorticity with
`|f(y)| ≤ M min(|y|^a, |y|^(-b))`, `0 < b ≤ 1`, and local Hölder constant `M min(|x|^γ, |x|^ε)` on
`B(x, |x|/2)`, `ε ≥ 0`, the Hessian of the grouped stream function satisfies
`|∂ₗ∂ₖΨ(x)| ≤ C M |x|^(-b/2)` for `|x| ≥ 1` in the open upper half-plane. -/
theorem exists_abs_hessian_le_of_one_le (hα : 0 < α) (hα1 : α < 1) (hb : 0 < b) (hb1 : b ≤ 1)
    (hε : 0 ≤ ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ⦃f : ℝ^2 → ℝ⦄ ⦃M : ℝ⦄, IsHolderVorticity α f →
      (∀ y : ℝ^2, 0 ≤ y 1 → |f y| ≤ M * min (‖y‖ ^ a) (‖y‖ ^ (-b))) →
      (∀ x : ℝ^2, x ≠ 0 → ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 → ‖x - y‖ ≤ ‖x‖ / 2 →
        ‖x - z‖ ≤ ‖x‖ / 2 → |f y - f z| ≤ M * min (‖x‖ ^ γ) (‖x‖ ^ ε) * ‖y - z‖ ^ α) →
      ∀ x : ℝ^2, 0 < x 1 → 1 ≤ ‖x‖ → ∀ k l : Fin 2,
        |(∂[l] (∂[k] (quadrantPotential f))) x| ≤ C * M * ‖x‖ ^ (-(b / 2)) := by
  obtain ⟨C₁, hC₁, hE⟩ := exists_abs_hessian_sub_far_le hα hα1
  set κ := (ε + b / 2) / α with hκ_def
  have hκ : 0 ≤ κ := by positivity
  have h2b : 0 < 2 - b := by linarith
  set K₁ : ℝ := 2 ^ b * (2 * Real.pi) * (Real.log 8 + (1 + κ) * (2 / b))
  set K₂ : ℝ := 8 * Real.pi * 9 ^ (2 - b) / (2 - b)
  have hK₁ : 0 ≤ K₁ := by
    have : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
    positivity
  have hK₂ : 0 ≤ K₂ := by positivity
  refine ⟨C₁ * (2 ^ b + 1) + C₁ * (K₁ + K₂) + 4 * Real.pi / b, by positivity, ?_⟩
  intro f M hf hS hH x hx hx1 k l
  have hM := nonneg_of_abs_le_min hS
  have hx0 : x ≠ 0 := fun h ↦ by rw [h] at hx; simp at hx
  set r := ‖x‖ with hr_def
  have hr : 0 < r := by linarith
  set δ := r ^ (-κ) / 16 with hδ_def
  set R := 4 * r with hR_def
  have hrκ : r ^ (-κ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
  have hδ : 0 < δ := by positivity
  have hδr : δ ≤ r / 16 := by
    simp only [δ]; linarith
  have hR : 0 < R := by positivity
  set F := farSource R f
  have hfar := hf.isQuadrantFarDensity_farSource hR
  set w := M * r ^ (-(b / 2))
  have hw : 0 ≤ w := by positivity
  -- local bound
  set B := M * (2 ^ b * r ^ (-b))
  have hB' : ∀ y, 0 ≤ y 1 → ‖x - y‖ ≤ r / 2 → |f y| ≤ B := fun y hy hxy ↦ by
    have hry : r / 2 ≤ ‖y‖ := by
      have := norm_le_norm_add_norm_sub' x y
      linarith
    refine (abs_le_mul_rpow_neg_of_le_min hS hy).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hM
    rw [← div_two_rpow_neg hr.le]
    exact rpow_neg_le_of_le (by positivity) hry hb.le
  have hB : ∀ y, 0 ≤ y 1 → ‖x - y‖ ≤ 2 * δ → |f y| ≤ B := fun y hy hxy ↦
    hB' y hy (by linarith)
  have hL : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → ‖x - y‖ ≤ 2 * δ → ‖x - z‖ ≤ 2 * δ →
      |f y - f z| ≤ M * min (r ^ γ) (r ^ ε) * ‖y - z‖ ^ α := fun y z hy hz hxy hxz ↦
    hH x hx0 y z hy hz (by linarith) (by linarith)
  -- the intermediate integral
  set p₁ := M * (2 ^ b * r ^ (-b)) * (2 * Real.pi * Real.log (r / 2 / δ))
  set p₂ := 4 * M / r ^ 2 * (2 * Real.pi * (9 * r) ^ (2 - b) / (2 - b))
  have hlog : 0 ≤ Real.log (r / 2 / δ) := Real.log_nonneg ((le_div_iff₀ hδ).2 (by linarith))
  have hp₁ : 0 ≤ p₁ := by positivity
  have hp₂ : 0 ≤ p₂ := by positivity
  have hI : ∫⁻ y in {y : ℝ^2 | 0 < y 1 ∧ δ ≤ ‖x - y‖ ∧ ‖y‖ ≤ 2 * R},
      ENNReal.ofReal (|f y| / ‖x - y‖ ^ 2) ≤ ENNReal.ofReal (p₁ + p₂) := by
    set S := {y : ℝ^2 | 0 < y 1 ∧ δ ≤ ‖x - y‖ ∧ ‖y‖ ≤ 2 * R}
    have hSm : MeasurableSet S := measurableSet_middleRegion x δ R
    refine (setLIntegral_le_inter_add_diff S (ball x (r / 2)) _).trans ?_
    rw [ENNReal.ofReal_add hp₁ hp₂]
    refine add_le_add ?_ ?_
    · calc ∫⁻ y in S ∩ ball x (r / 2), ENNReal.ofReal (|f y| / ‖x - y‖ ^ 2)
          ≤ ∫⁻ y in S ∩ ball x (r / 2),
              ENNReal.ofReal (M * (2 ^ b * r ^ (-b)) * (‖x - y‖ ^ 2)⁻¹) := by
            refine setLIntegral_mono' (hSm.inter measurableSet_ball) fun y hy ↦ ?_
            refine ENNReal.ofReal_le_ofReal ?_
            rw [div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_right (hB' y hy.1.1.le (mem_ball_iff_norm'.1 hy.2).le)
              (by positivity)
        _ ≤ ∫⁻ y in ball x (r / 2) \ ball x δ,
              ENNReal.ofReal (M * (2 ^ b * r ^ (-b)) * (‖x - y‖ ^ 2)⁻¹) :=
            lintegral_mono_set fun y hy ↦
              ⟨hy.2, fun h ↦ (mem_ball_iff_norm'.1 h).not_ge hy.1.2.1⟩
        _ = ENNReal.ofReal p₁ :=
            lintegral_annulus_mul_inv_sq x (by positivity) hδ (by linarith)
    · refine setLIntegral_le_of_le_ball (hSm.inter measurableSet_ball.compl) (by positivity)
        (by positivity : 0 ≤ 9 * r) h2b (fun y hy ↦ mem_ball_zero_iff.2 (by linarith [hy.1.2.2]))
        fun y hy ↦ ?_
      · have hxy : r / 2 ≤ ‖x - y‖ := not_lt.1 fun h ↦ hy.2 (mem_ball_iff_norm'.2 h)
        have hxy0 : 0 < ‖x - y‖ := by linarith
        calc |f y| / ‖x - y‖ ^ 2 ≤ M * ‖y‖ ^ (-b) / (r / 2) ^ 2 := by
              gcongr
              exact abs_le_mul_rpow_neg_of_le_min hS hy.1.1.le
          _ = 4 * M / r ^ 2 * ‖y‖ ^ ((2 - b) - 2) := by
              rw [show 2 - b - 2 = -b by ring]; field_simp; ring
  have h1 := hE hf hx hδ (by linarith) hB hL (by positivity) hI k l
  have h2 := hfar.abs_hessian_le k l (x := x) (by linarith)
  have h2' := integral_abs_farSource_div_sq_le hS hb hR
  -- the bounds by `w = M r^(-b/2)`
  have hrb := rpow_neg_le_rpow_neg_half hx1 hb.le
  have hMw : M * r ^ (-b) ≤ w := mul_le_mul_of_nonneg_left hrb hM
  have hBw : B ≤ 2 ^ b * w := by
    simp only [B, w]
    have := mul_le_mul_of_nonneg_left hrb (by positivity : (0 : ℝ) ≤ M * 2 ^ b)
    linarith
  have hLw : δ ^ α * (M * min (r ^ γ) (r ^ ε)) ≤ w := by
    have hδα : δ ^ α ≤ r ^ (-(ε + b / 2)) := by
      calc δ ^ α ≤ (r ^ (-κ)) ^ α :=
            Real.rpow_le_rpow hδ.le (by simp only [δ]; linarith [Real.rpow_nonneg hr.le (-κ)])
              hα.le
        _ = r ^ (-(ε + b / 2)) := by
            rw [← Real.rpow_mul hr.le]; congr 1; simp only [κ]; field_simp
    calc δ ^ α * (M * min (r ^ γ) (r ^ ε)) ≤ r ^ (-(ε + b / 2)) * (M * r ^ ε) := by
          gcongr; exact min_le_right _ _
      _ = w := by
          simp only [w]
          rw [mul_left_comm, ← Real.rpow_add hr]; congr 2; ring
  have hp₁w : p₁ ≤ K₁ * w := by
    have hr8 : r / 2 / δ = 8 * r ^ (1 + κ) := by
      simp only [δ]
      rw [Real.rpow_add hr, Real.rpow_one, Real.rpow_neg hr.le]
      have : 0 < r ^ κ := by positivity
      field_simp
      ring
    have hlr : Real.log r ≤ 2 / b * r ^ (b / 2) :=
      (Real.log_le_rpow_div hr.le (by positivity : 0 < b / 2)).trans_eq (by field_simp)
    have hl : Real.log (r / 2 / δ) ≤ Real.log 8 + (1 + κ) * (2 / b * r ^ (b / 2)) := by
      rw [hr8, Real.log_mul (by norm_num) (by positivity), Real.log_rpow hr]
      gcongr
    have e : r ^ (-b) * r ^ (b / 2) = r ^ (-(b / 2)) := by
      rw [← Real.rpow_add hr]; congr 1; ring
    have h8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
    calc p₁ ≤ M * (2 ^ b * r ^ (-b)) *
          (2 * Real.pi * (Real.log 8 + (1 + κ) * (2 / b * r ^ (b / 2)))) := by
          simp only [p₁]; gcongr
      _ = M * 2 ^ b * (2 * Real.pi) *
          (r ^ (-b) * Real.log 8 + (1 + κ) * (2 / b) * (r ^ (-b) * r ^ (b / 2))) := by ring
      _ ≤ M * 2 ^ b * (2 * Real.pi) *
          (r ^ (-(b / 2)) * Real.log 8 + (1 + κ) * (2 / b) * r ^ (-(b / 2))) := by
          rw [e]; gcongr
      _ = K₁ * w := by simp only [K₁, w]; ring
  have hp₂w : p₂ ≤ K₂ * w := by
    have e : (9 * r) ^ (2 - b) / r ^ 2 = 9 ^ (2 - b) * r ^ (-b) := by
      rw [Real.mul_rpow (by norm_num) hr.le, mul_div_assoc, ← Real.rpow_sub_natCast hr.ne']
      congr 2; push_cast; ring
    calc p₂ = 8 * Real.pi * M / (2 - b) * ((9 * r) ^ (2 - b) / r ^ 2) := by
          simp only [p₂]; ring
      _ = K₂ * (M * r ^ (-b)) := by rw [e]; simp only [K₂]; ring
      _ ≤ K₂ * w := mul_le_mul_of_nonneg_left hMw hK₂
  have hFw : 2 * (M * (2 * Real.pi * R ^ (-b) / b)) ≤ 4 * Real.pi / b * w := by
    have hR' : R ^ (-b) ≤ r ^ (-b) := rpow_neg_le_of_le hr (by simp only [R]; linarith) hb.le
    calc 2 * (M * (2 * Real.pi * R ^ (-b) / b)) ≤ 2 * (M * (2 * Real.pi * r ^ (-b) / b)) := by
          gcongr
      _ = 4 * Real.pi / b * (M * r ^ (-b)) := by ring
      _ ≤ 4 * Real.pi / b * w := mul_le_mul_of_nonneg_left hMw (by positivity)
  have htri := abs_sub_abs_le_abs_sub ((∂[l] (∂[k] (quadrantPotential f))) x)
    ((∂[l] (∂[k] (quadrantPotential F))) x)
  have h2w : |(∂[l] (∂[k] (quadrantPotential F))) x| ≤ 4 * Real.pi / b * w :=
    h2.trans ((mul_le_mul_of_nonneg_left h2' (by norm_num)).trans hFw)
  have hC : (C₁ * (2 ^ b + 1) + C₁ * (K₁ + K₂) + 4 * Real.pi / b) * M * r ^ (-(b / 2)) =
      C₁ * (2 ^ b * w + w) + C₁ * (K₁ * w + K₂ * w) + 4 * Real.pi / b * w := by
    simp only [w]; ring
  rw [hC]
  have hloc : C₁ * (B + δ ^ α * (M * min (r ^ γ) (r ^ ε))) ≤ C₁ * (2 ^ b * w + w) :=
    mul_le_mul_of_nonneg_left (add_le_add hBw hLw) hC₁
  have hmid : C₁ * (p₁ + p₂) ≤ C₁ * (K₁ * w + K₂ * w) :=
    mul_le_mul_of_nonneg_left (add_le_add hp₁w hp₂w) hC₁
  linarith

/-- **Part I, Lemma 6.11, the second estimate.** For a Hölder vorticity with
`|f(y)| ≤ M min(|y|^a, |y|^(-b))`, `2 < a < 4`, `0 < b ≤ 1`, and local Hölder constant
`M min(|x|^γ, |x|^ε)` on `B(x, |x|/2)`, `γ + α ≥ 2`, `ε ≥ 0`, the Hessian of the grouped stream
function satisfies `|∂ₗ∂ₖΨ(x) - c mₖₗ| ≤ C M min(|x|², 1)` in the open upper half-plane,
`c = mixedCoefficient f`, `mₖₗ = 1 - δₖₗ`. -/
theorem exists_abs_hessian_sub_mixed_le (hα : 0 < α) (hα1 : α < 1) (ha : 2 < a) (ha4 : a < 4)
    (hb : 0 < b) (hb1 : b ≤ 1) (hγα : 2 ≤ γ + α) (hε : 0 ≤ ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ⦃f : ℝ^2 → ℝ⦄ ⦃M : ℝ⦄, IsHolderVorticity α f →
      (∀ y : ℝ^2, 0 ≤ y 1 → |f y| ≤ M * min (‖y‖ ^ a) (‖y‖ ^ (-b))) →
      (∀ x : ℝ^2, x ≠ 0 → ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 → ‖x - y‖ ≤ ‖x‖ / 2 →
        ‖x - z‖ ≤ ‖x‖ / 2 → |f y - f z| ≤ M * min (‖x‖ ^ γ) (‖x‖ ^ ε) * ‖y - z‖ ^ α) →
      ∀ x : ℝ^2, 0 < x 1 → ∀ k l : Fin 2,
        |(∂[l] (∂[k] (quadrantPotential f))) x - mixedCoefficient f * (if k = l then 0 else 1)| ≤
          C * M * min (‖x‖ ^ 2) 1 := by
  obtain ⟨C₁, hC₁, hW₁⟩ := exists_abs_hessian_sub_expansion_le (ε := ε) (γ := γ) hα hα1 ha ha4 hb
  obtain ⟨C₃, hC₃, hW₃⟩ := exists_abs_hessian_le_of_one_le (a := a) (γ := γ) hα hα1 hb hb1 hε
  have ha0 : 0 < a := by linarith
  set Kd : ℝ := 48 * (1 / (a - 2) + 1 / (2 + b))
  set Kc : ℝ := 4 * (1 / a + 1 / b)
  have ha2 : 0 < a - 2 := by linarith
  have hKd : 0 ≤ Kd := by positivity
  have hKc : 0 ≤ Kc := by positivity
  refine ⟨2 * C₁ + Kd + C₃ + Kc, by positivity, ?_⟩
  intro f M hf hS hH x hx k l
  have hM := nonneg_of_abs_le_min hS
  have hx0 : x ≠ 0 := fun h ↦ by rw [h] at hx; simp at hx
  set r := ‖x‖ with hr_def
  have hr : 0 < r := norm_pos_iff.mpr hx0
  have hm : |(if k = l then (0 : ℝ) else 1)| ≤ 1 := by split_ifs <;> simp
  set H := (∂[l] (∂[k] (quadrantPotential f))) x
  set m := mixedCoefficient f * (if k = l then (0 : ℝ) else 1)
  rcases le_total r 1 with hr1 | hr1
  · have h1 := hW₁ hf hS hH x hx hr1 k l
    have hd := abs_quarticCoefficient_le_of_le_min hS ha hb
    have hQ := abs_quarticHessian_le k l x
    have hra : r ^ a ≤ r ^ 2 := by
      rw [← Real.rpow_two]; exact Real.rpow_le_rpow_of_exponent_ge hr hr1 ha.le
    have hrγ : r ^ (γ + α) ≤ r ^ 2 := by
      rw [← Real.rpow_two]; exact Real.rpow_le_rpow_of_exponent_ge hr hr1 hγα
    have hmin : min (r ^ 2) 1 = r ^ 2 := min_eq_left (pow_le_one₀ hr.le hr1)
    rw [hmin]
    have htri := abs_sub_le H (m + quarticCoefficient f * quarticHessian k l x) m
    rw [add_sub_cancel_left, abs_mul] at htri
    have h2 : |quarticCoefficient f| * |quarticHessian k l x| ≤ Kd * M * r ^ 2 :=
      mul_le_mul hd hQ (abs_nonneg _) (by positivity)
    have h3 : C₁ * M * (r ^ a + r ^ (γ + α)) ≤ 2 * C₁ * M * r ^ 2 := by
      have := mul_le_mul_of_nonneg_left (add_le_add hra hrγ) (mul_nonneg hC₁ hM)
      linarith
    have h4 : 0 ≤ (C₃ + Kc) * M * r ^ 2 := by positivity
    nlinarith [htri, h1, h2, h3, h4]
  · have h3 := hW₃ hf hS hH x hx hr1 k l
    have hc := abs_mixedCoefficient_le_of_le_min hS ha0 hb
    have hmin : min (r ^ 2) 1 = 1 := min_eq_right (one_le_pow₀ hr1)
    rw [hmin, mul_one]
    have hrb : r ^ (-(b / 2)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hr1 (by linarith)
    have htri : |H - m| ≤ |H| + |mixedCoefficient f| :=
      (abs_sub H m).trans (add_le_add le_rfl
        ((abs_mul _ _).trans_le (mul_le_of_le_one_right (abs_nonneg _) hm)))
    have h3' : C₃ * M * r ^ (-(b / 2)) ≤ C₃ * M := mul_le_of_le_one_right (by positivity) hrb
    have h5 : 0 ≤ (2 * C₁ + Kd) * M := by positivity
    nlinarith [htri, h3, hc, h3', h5]

/-- **The interior limit at the origin.** Under the hypotheses of
`exists_abs_hessian_sub_expansion_le` with `γ ≥ 0`, the Hessian of the grouped stream function
tends to `c mₖₗ`, `c = mixedCoefficient f`, as `x → 0` in the open upper half-plane. In
particular the mixed derivative `∂₀∂₁Ψ` has the interior limit `c` at the origin (the quantity
`Ψ_xy(0)` of Part I, Lemma 6.11). -/
theorem tendsto_hessian_quadrantPotential (hα : 0 < α) (hα1 : α < 1) (ha : 2 < a) (ha4 : a < 4)
    (hb : 0 < b) (hγ : 0 ≤ γ) {f : ℝ^2 → ℝ} {M : ℝ} (hf : IsHolderVorticity α f)
    (hS : ∀ y : ℝ^2, 0 ≤ y 1 → |f y| ≤ M * min (‖y‖ ^ a) (‖y‖ ^ (-b)))
    (hH : ∀ x : ℝ^2, x ≠ 0 → ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 → ‖x - y‖ ≤ ‖x‖ / 2 →
      ‖x - z‖ ≤ ‖x‖ / 2 → |f y - f z| ≤ M * min (‖x‖ ^ γ) (‖x‖ ^ ε) * ‖y - z‖ ^ α)
    (k l : Fin 2) :
    Tendsto (fun x ↦ (∂[l] (∂[k] (quadrantPotential f))) x) (𝓝[{x : ℝ^2 | 0 < x 1}] 0)
      (𝓝 (mixedCoefficient f * (if k = l then 0 else 1))) := by
  obtain ⟨C, hC, hW⟩ := exists_abs_hessian_sub_expansion_le (ε := ε) (γ := γ) hα hα1 ha ha4 hb
  have ha0 : 0 < a := by linarith
  have hγα : 0 < γ + α := by linarith
  set d := quarticCoefficient f
  set g : ℝ^2 → ℝ := fun x ↦ C * M * (‖x‖ ^ a + ‖x‖ ^ (γ + α)) + |d| * ‖x‖ ^ 2
  have hg : Continuous g :=
    ((continuous_const.mul ((continuous_norm.rpow_const fun _ ↦ Or.inr ha0.le).add
      (continuous_norm.rpow_const fun _ ↦ Or.inr hγα.le))).add
      (continuous_const.mul (continuous_norm.pow 2)))
  have hg0 : g 0 = 0 := by
    simp [g, Real.zero_rpow ha0.ne', Real.zero_rpow hγα.ne']
  have hgt : Tendsto g (𝓝[{x : ℝ^2 | 0 < x 1}] 0) (𝓝 0) := by
    rw [← hg0]; exact (hg.tendsto 0).mono_left nhdsWithin_le_nhds
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hgt
  have hball : ∀ᶠ x in 𝓝[{x : ℝ^2 | 0 < x 1}] (0 : ℝ^2), x ∈ ball (0 : ℝ^2) 1 :=
    mem_nhdsWithin_of_mem_nhds (ball_mem_nhds 0 one_pos)
  filter_upwards [hball, self_mem_nhdsWithin] with x hx1 hx
  rw [mem_ball_zero_iff] at hx1
  rw [Real.norm_eq_abs]
  have h1 := hW hf hS hH x hx hx1.le k l
  have hQ := abs_quarticHessian_le k l x
  have htri := abs_sub_le ((∂[l] (∂[k] (quadrantPotential f))) x)
    (mixedCoefficient f * (if k = l then 0 else 1) + d * quarticHessian k l x)
    (mixedCoefficient f * (if k = l then 0 else 1))
  rw [add_sub_cancel_left, abs_mul] at htri
  exact htri.trans (add_le_add h1 (mul_le_mul_of_nonneg_left hQ (abs_nonneg _)))

end IncompressibleFlow
