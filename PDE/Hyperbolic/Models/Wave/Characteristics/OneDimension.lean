/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.PartialDeriv.Regularity
public import PDE.Hyperbolic.Models.Wave.Operator
import CAS.ExactTactic

/-!
# Characteristic bounds for one-dimensional waves

The derivatives `u_t + u_x` and `u_t - u_x` have characteristic derivative
equal to the wave operator. A forcing bound and initial first-jet bound
therefore control both first derivatives and displacement on a truncated backward
triangle.
-/

@[expose] public noncomputable section

open PDE Set Filter
open scoped Topology

namespace WaveEquation

/-- The two null derivatives have derivative equal to the wave operator
along the oppositely directed characteristics. -/
theorem hasDerivAt_nullDerivative_characteristic {u : ℝ^2 → ℝ} {p : ℝ^2} {ε t : ℝ} (hε : ε ^ 2 = 1)
    (hu : ContDiffAt ℝ 2 u (p + t • (EuclideanSpace.single 0 1 - ε • EuclideanSpace.single 1 1))) :
    HasDerivAt
      (fun s ↦ (∂[0] u) (p + s •
        (EuclideanSpace.single 0 1 - ε • EuclideanSpace.single 1 1)) +
        ε * (∂[1] u) (p + s •
        (EuclideanSpace.single 0 1 - ε • EuclideanSpace.single 1 1)))
      (waveOperator u (p + t •
        (EuclideanSpace.single 0 1 - ε • EuclideanSpace.single 1 1))) t := by
  let v : ℝ^2 := EuclideanSpace.single 0 1 - ε • EuclideanSpace.single 1 1
  have hd : HasDerivAt (fun s : ℝ ↦ p + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add p
  have h₀ := ((hu.partialDeriv 0 (k := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt.comp_hasDerivAt t hd
  have h₁ := ((hu.partialDeriv 1 (k := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt.comp_hasDerivAt t hd
  convert h₀.add (h₁.const_mul ε) using 1
  · rfl
  · rw [fderiv_apply_eq_sum_partialDeriv_mul, fderiv_apply_eq_sum_partialDeriv_mul]
    simp only [Fin.sum_univ_two, v, PiLp.sub_apply, PiLp.smul_apply,
      PiLp.single_apply, smul_eq_mul, ite_true, ite_false,
      Fin.zero_ne_one, mul_zero, sub_zero, mul_one]
    rw [partialDeriv_partialDeriv_comm_at 0 1 hu]
    simp only [waveOperator, Fin.sum_univ_one, Fin.succ_zero_eq_one]
    cas using hε

/-- A bound on the wave operator bounds the change of either null derivative
on a characteristic segment. -/
theorem norm_nullDerivative_sub_le_of_waveOperator_le {u : ℝ^2 → ℝ} {p : ℝ^2} {ε a b C : ℝ}
    (hε : ε ^ 2 = 1) (hab : a ≤ b)
    (hu : ∀ t ∈ Icc a b,
      ContDiffAt ℝ 2 u (p + t • (EuclideanSpace.single 0 1 - ε • EuclideanSpace.single 1 1)))
    (hb : ∀ t ∈ Ico a b,
      ‖waveOperator u (p + t • (EuclideanSpace.single 0 1 - ε • EuclideanSpace.single 1 1))‖ ≤ C) :
    ‖((∂[0] u) (p + b •
        (EuclideanSpace.single 0 1 - ε • EuclideanSpace.single 1 1)) +
        ε * (∂[1] u) (p + b •
        (EuclideanSpace.single 0 1 - ε • EuclideanSpace.single 1 1))) -
      ((∂[0] u) (p + a •
        (EuclideanSpace.single 0 1 - ε • EuclideanSpace.single 1 1)) +
        ε * (∂[1] u) (p + a •
        (EuclideanSpace.single 0 1 - ε • EuclideanSpace.single 1 1)))‖ ≤ C * (b - a) :=
  norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t ht ↦ (hasDerivAt_nullDerivative_characteristic hε (hu t ht)).hasDerivWithinAt)
    hb b ⟨hab, le_rfl⟩

/-- Initial null-derivative bounds propagate into a truncated backward triangle
under a bound on the forcing there. The top cap may precede the vertex. -/
theorem norm_nullDerivative_le_on_triangle {u : ℝ^2 → ℝ} {a τ T c B F ε : ℝ} (hε : ε ^ 2 = 1)
    (hu : ∀ p : ℝ^2, p 0 ∈ Icc a τ → |p 1 - c| ≤ T - p 0 → ContDiffAt ℝ 2 u p)
    (hF : ∀ p : ℝ^2, p 0 ∈ Icc a τ → |p 1 - c| ≤ T - p 0 → ‖waveOperator u p‖ ≤ F)
    (hB : ∀ p : ℝ^2, p 0 = a → |p 1 - c| ≤ T - a → ‖(∂[0] u) p + ε * (∂[1] u) p‖ ≤ B) {q : ℝ^2}
    (hq : q 0 ∈ Icc a τ) (hqc : |q 1 - c| ≤ T - q 0) :
    ‖(∂[0] u) q + ε * (∂[1] u) q‖ ≤ B + F * (q 0 - a) := by
  let v : ℝ^2 := EuclideanSpace.single 0 1 - ε • EuclideanSpace.single 1 1
  let p := q - q 0 • v
  have hv0 : v 0 = 1 := by simp [v]
  have hv1 : v 1 = -ε := by simp [v]
  have hp0 (s : ℝ) : (p + s • v) 0 = s := by
    simp [p, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, hv0]
  have hp1 (s : ℝ) : (p + s • v) 1 = q 1 + ε * (q 0 - s) := by
    simp only [p, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, hv1]
    cas
  have hεabs : |ε| = 1 := by nlinarith [sq_abs ε, abs_nonneg ε]
  have hpath (s : ℝ) (hs : s ∈ Icc a (q 0)) :
      |(p + s • v) 1 - c| ≤ T - (p + s • v) 0 := by
    rw [hp0, hp1]
    calc
      _ = |(q 1 - c) + ε * (q 0 - s)| := by congr 1; cas
      _ ≤ |q 1 - c| + |ε * (q 0 - s)| := abs_add_le _ _
      _ = |q 1 - c| + (q 0 - s) := by
        rw [abs_mul, hεabs, abs_of_nonneg (sub_nonneg.mpr hs.2), one_mul]
      _ ≤ T - s := by linarith
  have htop : p + q 0 • v = q := sub_add_cancel _ _
  have he := norm_nullDerivative_sub_le_of_waveOperator_le hε hq.1
    (fun s hs ↦ hu _ (by rw [hp0]; exact ⟨hs.1, hs.2.trans hq.2⟩) (hpath s hs))
    (fun s hs ↦ hF _ (by rw [hp0]; exact ⟨hs.1, hs.2.le.trans hq.2⟩) (hpath s ⟨hs.1, hs.2.le⟩))
  change ‖((∂[0] u) (p + q 0 • v) + ε * (∂[1] u) (p + q 0 • v)) -
    ((∂[0] u) (p + a • v) + ε * (∂[1] u) (p + a • v))‖ ≤ _ at he
  rw [htop] at he
  have hinitial := hB (p + a • v) (hp0 a)
    (by simpa only [hp0] using hpath a ⟨le_rfl, hq.1⟩)
  calc
    _ ≤ ‖((∂[0] u) q + ε * (∂[1] u) q) - ((∂[0] u) (p + a • v) + ε * (∂[1] u) (p + a • v))‖ +
          ‖(∂[0] u) (p + a • v) + ε * (∂[1] u) (p + a • v)‖ := norm_le_norm_sub_add _ _
    _ ≤ B + F * (q 0 - a) := by linarith

/-- The two characteristic estimates bound both first derivatives in a
truncated backward triangle. -/
theorem norm_partialDeriv_le_on_triangle {u : ℝ^2 → ℝ} {a τ T c B F : ℝ} (hFnonneg : 0 ≤ F)
    (hu : ∀ p : ℝ^2, p 0 ∈ Icc a τ → |p 1 - c| ≤ T - p 0 → ContDiffAt ℝ 2 u p)
    (hF : ∀ p : ℝ^2, p 0 ∈ Icc a τ → |p 1 - c| ≤ T - p 0 → ‖waveOperator u p‖ ≤ F)
    (hB : ∀ p : ℝ^2, p 0 = a → |p 1 - c| ≤ T - a → ∀ ε : ℝ, ε ^ 2 = 1 →
      ‖(∂[0] u) p + ε * (∂[1] u) p‖ ≤ B)
    {q : ℝ^2} (hq : q 0 ∈ Icc a τ) (hqc : |q 1 - c| ≤ T - q 0) (i : Fin 2) :
    ‖(∂[i] u) q‖ ≤ B + F * (τ - a) := by
  have hp := norm_nullDerivative_le_on_triangle (by norm_num : (1 : ℝ) ^ 2 = 1)
    hu hF (fun p hp hc ↦ hB p hp hc 1 (by norm_num)) hq hqc
  have hm := norm_nullDerivative_le_on_triangle (by norm_num : (-1 : ℝ) ^ 2 = 1)
    hu hF (fun p hp hc ↦ hB p hp hc (-1) (by norm_num)) hq hqc
  simp only [Real.norm_eq_abs, one_mul, neg_one_mul, abs_le] at hp hm
  simp only [Real.norm_eq_abs, abs_le]
  have hle : F * (q 0 - a) ≤ F * (τ - a) :=
    mul_le_mul_of_nonneg_left (sub_le_sub_right hq.2 a) hFnonneg
  fin_cases i
  · change -(B + F * (τ - a)) ≤ (∂[0] u) q ∧ (∂[0] u) q ≤ B + F * (τ - a)
    constructor <;> linarith [hp.1, hp.2, hm.1, hm.2]
  · change -(B + F * (τ - a)) ≤ (∂[1] u) q ∧ (∂[1] u) q ≤ B + F * (τ - a)
    constructor <;> linarith [hp.1, hp.2, hm.1, hm.2]

/-- A bounded forcing on the preceding triangle controls displacement from the
initial slice, using the time derivative and characteristic estimates. -/
theorem norm_sub_initial_le_on_triangle {u : ℝ^2 → ℝ} {a τ T c B F : ℝ} (hFnonneg : 0 ≤ F)
    (hu : ∀ p : ℝ^2, p 0 ∈ Icc a τ → |p 1 - c| ≤ T - p 0 → ContDiffAt ℝ 2 u p)
    (hF : ∀ p : ℝ^2, p 0 ∈ Icc a τ → |p 1 - c| ≤ T - p 0 → ‖waveOperator u p‖ ≤ F)
    (hB : ∀ p : ℝ^2, p 0 = a → |p 1 - c| ≤ T - a → ∀ ε : ℝ, ε ^ 2 = 1 →
      ‖(∂[0] u) p + ε * (∂[1] u) p‖ ≤ B)
    {q : ℝ^2} (hq : q 0 ∈ Icc a τ) (hqc : |q 1 - c| ≤ T - q 0) :
    ‖u q - u (q + (a - q 0) • EuclideanSpace.single 0 1)‖ ≤ (B + F * (τ - a)) * (q 0 - a) := by
  let γ := fun s : ℝ ↦ q + (s - q 0) • EuclideanSpace.single 0 (1 : ℝ)
  have hg0 (s : ℝ) : γ s 0 = s := by simp [γ]
  have hg1 (s : ℝ) : γ s 1 = q 1 := by simp [γ]
  have hmem (s : ℝ) (hs : s ∈ Icc a (q 0)) : γ s 0 ∈ Icc a τ := by
    rw [hg0]; exact ⟨hs.1, hs.2.trans hq.2⟩
  have hcone (s : ℝ) (hs : s ∈ Icc a (q 0)) : |γ s 1 - c| ≤ T - γ s 0 := by
    rw [hg0, hg1]; linarith [hs.2]
  have hd (s : ℝ) (hs : s ∈ Icc a (q 0)) :
      HasDerivAt (fun r ↦ u (γ r)) ((∂[0] u) (γ s)) s := by
    have hγ : HasDerivAt γ (EuclideanSpace.single 0 1) s := by
      simpa [γ] using (((hasDerivAt_id s).sub_const (q 0)).smul_const
        (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))).const_add q
    exact ((hu _ (hmem s hs) (hcone s hs)).differentiableAt (by norm_num)).hasFDerivAt
      |>.comp_hasDerivAt s hγ
  have he := norm_image_sub_le_of_norm_deriv_le_segment' (fun s hs ↦ (hd s hs).hasDerivWithinAt)
    (fun s hs ↦ norm_partialDeriv_le_on_triangle hFnonneg hu hF hB
      (hmem s ⟨hs.1, hs.2.le⟩) (hcone s ⟨hs.1, hs.2.le⟩) 0) (q 0) ⟨hq.1, le_rfl⟩
  simpa [γ] using he

end WaveEquation
