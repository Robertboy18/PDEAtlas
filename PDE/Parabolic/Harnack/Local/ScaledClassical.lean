/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Harnack.Local.Classical
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Classical Harnack comparison at arbitrary interior scales

Parabolic dilation transports the specified spatial and temporal derivatives
and the equation. The comparison constant is uniform for scales at
most one and for every positive margin beyond the later comparison time.
-/

@[expose] public noncomputable section

namespace ParabolicHarnack

open PDE.Analysis ParabolicMaximum Set Metric
open scoped RealInnerProductSpace

variable {n : ℕ}

/-- The C²,¹ comparison on a translated cylinder. Neither the scale nor
the remaining future time margin enters the constant. -/
theorem exists_scaled_comparison_of_space_time_derivatives
    {α τ B K : ℝ} (hα : 0 < α) (hτ : 0 ≤ τ) (hB : 0 ≤ B) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ) (d : ℝ^n → ℝ → ℝ^n)
        (c : ℝ^n → ℝ → ℝ) (z : ℝ^n) (s r T : ℝ),
        0 < r → r ≤ 1 → s + 64 * r ^ 2 < T →
        let D := ball z (13 * r) ×ˢ Ioo (s - 2 * r ^ 2) T
        ContinuousOn (Function.uncurry a) D →
        (∀ p ∈ D, (a p.1 p.2).PosSemidef) →
        (∀ p ∈ D, ∀ w : ℝ^n,
          α * ‖w‖ ^ 2 ≤ ⟪w, (a p.1 p.2).toEuclideanLin w⟫) →
        (∀ p ∈ D, (a p.1 p.2).trace ≤ τ) →
        (∀ p ∈ D, ‖d p.1 p.2‖ ≤ B) →
        (∀ p ∈ D, |c p.1 p.2| ≤ K) →
        ∀ (u : ℝ^n → ℝ → ℝ)
          (Dx : ℝ^n × ℝ → ℝ^n →L[ℝ] ℝ) (Dt : ℝ^n × ℝ → ℝ)
          (Dxx : ℝ^n × ℝ → ℝ^n →L[ℝ] ℝ^n →L[ℝ] ℝ),
          ContinuousOn Dx D → ContinuousOn Dt D → ContinuousOn Dxx D →
          (∀ p ∈ D, HasFDerivAt (fun x ↦ u x p.2) (Dx p) p.1) →
          (∀ p ∈ D, HasFDerivAt (fun x ↦ Dx (x, p.2)) (Dxx p) p.1) →
          (∀ p ∈ D, HasDerivAt (u p.1) (Dt p) p.2) →
          (∀ p ∈ D, 0 ≤ u p.1 p.2) →
          (∀ p ∈ D, matrixParabolicOperator a d c u p.1 p.2 = 0) →
          ∀ x ∈ closedBall z (r / 2), ∀ t ∈ Icc (s - r ^ 2 / 2) s,
            ∀ y ∈ closedBall z r, u x t ≤ C * u y (s + 64 * r ^ 2) := by
  obtain ⟨C, hC, hlocal⟩ :=
    exists_local_comparison_of_space_time_derivatives (n := n) hα hτ hB hK
  refine ⟨C, hC, ?_⟩
  intro a d c z s r T hr hr₁ hT D hacont ha hell htrace hdrift hpotential
    u Dx Dt Dxx hDx hDt hDxx hd hdd ht hnonneg hsol x hx t hxt y hy
  have hr₂ : 0 < r ^ 2 := sq_pos_of_pos hr
  have hr₂₁ : r ^ 2 ≤ 1 := by nlinarith
  let b := (T - s) / r ^ 2
  have hb : 64 < b := (lt_div_iff₀ hr₂).mpr (by linarith)
  let Φ : ℝ^n × ℝ → ℝ^n × ℝ := fun p ↦ (z + r • p.1, s + r ^ 2 * p.2)
  have hΦ : Continuous Φ := by dsimp only [Φ]; fun_prop
  have hdist (v : ℝ^n) : dist (z + r • v) z = r * ‖v‖ := by
    simp [dist_eq_norm, norm_smul, abs_of_pos hr]
  have hmaps : MapsTo Φ (ball (0 : ℝ^n) 13 ×ˢ Ioo (-2 : ℝ) b) D := fun p hp ↦
    ⟨show dist (z + r • p.1) z < 13 * r by
        rw [hdist, mul_comm 13 r]; exact mul_lt_mul_of_pos_left (by simpa using hp.1) hr,
      show s - 2 * r ^ 2 < s + r ^ 2 * p.2 by linarith [mul_lt_mul_of_pos_left hp.2.1 hr₂],
      show s + r ^ 2 * p.2 < T by linarith [(lt_div_iff₀ hr₂).mp hp.2.2]⟩
  let a' := fun v q ↦ a (Φ (v, q)).1 (Φ (v, q)).2
  let d' := fun v q ↦ r • d (Φ (v, q)).1 (Φ (v, q)).2
  let c' := fun v q ↦ r ^ 2 * c (Φ (v, q)).1 (Φ (v, q)).2
  let v := fun w q ↦ u (Φ (w, q)).1 (Φ (w, q)).2
  let Dx' := fun p ↦ r • Dx (Φ p)
  let Dt' := fun p ↦ r ^ 2 * Dt (Φ p)
  let Dxx' := fun p ↦ r ^ 2 • Dxx (Φ p)
  have hd' (p : ℝ^n × ℝ) (hp : p ∈ ball (0 : ℝ^n) 13 ×ˢ Ioo (-2 : ℝ) b) :
      HasFDerivAt (fun w ↦ v w p.2) (Dx' p) p.1 :=
    hasFDerivAt_comp_const_add_smul (hd (Φ p) (hmaps hp))
  have hdd' (p : ℝ^n × ℝ) (hp : p ∈ ball (0 : ℝ^n) 13 ×ˢ Ioo (-2 : ℝ) b) :
      HasFDerivAt (fun w ↦ Dx' (w, p.2)) (Dxx' p) p.1 := by
    simpa only [Dx', Dxx', Φ, Pi.smul_def, smul_smul, pow_two] using
      (hasFDerivAt_comp_const_add_smul (hdd (Φ p) (hmaps hp))).const_smul r
  have ht' (p : ℝ^n × ℝ) (hp : p ∈ ball (0 : ℝ^n) 13 ×ˢ Ioo (-2 : ℝ) b) :
      HasDerivAt (v p.1) (Dt' p) p.2 := by
    simpa only [Dt', v, Φ, Function.comp_def, id_eq, mul_one, mul_comm] using
      (ht (Φ p) (hmaps hp)).comp p.2
        (((hasDerivAt_id p.2).const_mul (r ^ 2)).const_add s)
  let x' := r⁻¹ • (x - z)
  let y' := r⁻¹ • (y - z)
  let t' := (t - s) / r ^ 2
  have hxx : z + r • x' = x := by simp [x', smul_smul, hr.ne']
  have hyy : z + r • y' = y := by simp [y', smul_smul, hr.ne']
  have htt : s + r ^ 2 * t' = t := by simp only [t', mul_div_cancel₀ _ hr₂.ne', add_sub_cancel]
  have hx' : x' ∈ closedBall (0 : ℝ^n) (1 / 2) := by
    rw [mem_closedBall, dist_zero_right]
    have hbnd : r * ‖x'‖ ≤ r / 2 := by
      simpa only [mem_closedBall, ← hxx, hdist] using hx
    nlinarith
  have hy' : y' ∈ closedBall (0 : ℝ^n) 1 := by
    rw [mem_closedBall, dist_zero_right]
    have hbnd : r * ‖y'‖ ≤ r := by simpa only [mem_closedBall, ← hyy, hdist] using hy
    nlinarith
  have htmem : t' ∈ Icc (-1 / 2 : ℝ) 0 := ⟨(le_div_iff₀ hr₂).mpr (by linarith [hxt.1]),
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hxt.2) hr₂.le⟩
  have hcompare := hlocal b hb a' d' c' (hacont.comp hΦ.continuousOn hmaps)
    (fun p hp ↦ ha _ (hmaps hp)) (fun p hp ↦ hell _ (hmaps hp))
    (fun p hp ↦ htrace _ (hmaps hp))
    (fun p hp ↦ by
      change ‖r • d (Φ p).1 (Φ p).2‖ ≤ B
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      exact (mul_le_mul_of_nonneg_left (hdrift _ (hmaps hp)) hr.le).trans
        (mul_le_of_le_one_left hB hr₁))
    (fun p hp ↦ by
      change |r ^ 2 * c (Φ p).1 (Φ p).2| ≤ K
      rw [abs_mul, abs_of_nonneg hr₂.le]
      exact (mul_le_mul_of_nonneg_left (hpotential _ (hmaps hp)) hr₂.le).trans
        (mul_le_of_le_one_left hK hr₂₁))
    v Dx' Dt' Dxx'
    ((hDx.comp hΦ.continuousOn hmaps).const_smul r)
    (continuousOn_const.mul (hDt.comp hΦ.continuousOn hmaps))
    ((hDxx.comp hΦ.continuousOn hmaps).const_smul (r ^ 2))
    hd' hdd' ht' (fun p hp ↦ hnonneg _ (hmaps hp))
    (fun p hp ↦ by
      change matrixParabolicOperator
        (fun w q ↦ a (z + r • w) (s + r ^ 2 * q))
        (fun w q ↦ r • d (z + r • w) (s + r ^ 2 * q))
        (fun w q ↦ r ^ 2 * c (z + r • w) (s + r ^ 2 * q))
        (fun w q ↦ u (z + r • w) (s + r ^ 2 * q)) p.1 p.2 = 0
      rw [matrixParabolicOperator_comp_space_time_dilation, hsol _ (hmaps hp), mul_zero])
    x' hx' t' htmem y' hy'
  simpa only [v, Φ, hxx, hyy, htt, mul_comm (r ^ 2) 64] using hcompare

end ParabolicHarnack
