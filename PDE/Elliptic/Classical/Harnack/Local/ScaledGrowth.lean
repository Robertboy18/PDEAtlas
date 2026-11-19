/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.AffineVolume
public import PDE.Elliptic.Classical.Harnack.Local.Growth
public import PDE.Elliptic.Classical.Harnack.Local.Scaling

/-!
# Localized contact growth on translated balls

The constants in the contact estimate are uniform under translation and
dilations of radius at most one. Normalizing the solution by a positive level
gives the estimate at every level. The factor `rⁿ` records the exact volume
change, so it can later be compared with the volume of a cube of side `2r`.
-/

@[expose] public section

noncomputable section

namespace EllipticHarnack

open PDE.Analysis EllipticMaximum Set Metric MeasureTheory
open scoped RealInnerProductSpace ENNReal

variable {n : ℕ}

/-- Uniform localized low-level mass at every center, scale at most one, and
positive normalization level. -/
theorem exists_scaled_sublevel_measure_bound
    {R ρ α τ B : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (hα : 0 < α)
    (hB : 0 ≤ B) :
    ∃ M D : ℝ, 2 ≤ M ∧ 0 < D ∧
      ∀ (a : ℝ^n → Matrix (Fin n) (Fin n) ℝ) (b : ℝ^n → ℝ^n)
        (z : ℝ^n) (r : ℝ), 0 < r → r ≤ 1 →
        (∀ x ∈ ball z (r * R), (a x).PosSemidef) →
        (∀ x ∈ ball z (r * R), ∀ v : ℝ^n,
          α * ‖v‖ ^ 2 ≤ ⟪v, (a x).toEuclideanLin v⟫) →
        (∀ x ∈ ball z (r * R), (a x).trace ≤ τ) →
        (∀ x ∈ ball z (r * R), ‖b x‖ ≤ B) →
        ∀ u : ℝ^n → ℝ, ContinuousOn u (closedBall z (r * R)) →
        (∀ x ∈ ball z (r * R), ContDiffAt ℝ 2 u x) →
        (∀ x ∈ closedBall z (r * R), 0 ≤ u x) →
        (∀ x ∈ ball z (r * R), 0 ≤ matrixOperator a b (fun _ ↦ 0) u x) →
        ∀ t : ℝ, 0 < t → ∀ x₀ ∈ closedBall z (r * (R / 2)), u x₀ ≤ t →
          r ^ n * volume.real (closedBall (0 : ℝ^n) (R / 2)) ≤
            D * volume.real (ball z (r * ρ) ∩ {x | u x ≤ M * t}) := by
  obtain ⟨M, D, _, hD, hbound⟩ :=
    exists_localized_sublevel_measure_bound (n := n) hR hρ hα
  refine ⟨max 2 M, D, le_max_left _ _, hD, ?_⟩
  intro a b z r hr hr₁ ha hell htrace hdrift u hu hreg hnonneg hsuper t ht x₀ hx₀ hsmall
  let Φ : ℝ^n → ℝ^n := fun y ↦ z + r • y
  have hΦ : ContDiff ℝ 2 Φ := contDiff_const.add (contDiff_id.const_smul r)
  have hdist (y : ℝ^n) : dist (Φ y) z = r * ‖y‖ := by
    simp [Φ, dist_eq_norm, norm_smul, abs_of_pos hr]
  have hmaps : MapsTo Φ (closedBall 0 R) (closedBall z (r * R)) := fun y hy ↦ by
    rw [mem_closedBall, hdist]
    exact mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.1 hy) hr.le
  have hmapsOpen : MapsTo Φ (ball 0 R) (ball z (r * R)) := fun y hy ↦ by
    rw [mem_ball, hdist]
    exact mul_lt_mul_of_pos_left (mem_ball_zero_iff.1 hy) hr
  let a' := fun y ↦ a (Φ y)
  let b' := fun y ↦ r • b (Φ y)
  let v := fun y ↦ t⁻¹ * u (Φ y)
  have hvreg : ∀ y ∈ ball (0 : ℝ^n) R, ContDiffAt ℝ 2 v y :=
    fun y hy ↦ contDiffAt_const.mul ((hreg (Φ y) (hmapsOpen hy)).comp y hΦ.contDiffAt)
  have hv : ContinuousOn v (closedBall 0 R) :=
    (hu.comp hΦ.continuous.continuousOn hmaps).const_mul _
  have hvsuper : ∀ y ∈ ball (0 : ℝ^n) R, 0 ≤ matrixOperator a' b' (fun _ ↦ 0) v y := by
    intro y hy
    have hd := ((hreg (Φ y) (hmapsOpen hy)).comp y hΦ.contDiffAt).differentiableAt
      (by norm_num)
    change 0 ≤ matrixOperator a' b' (fun _ ↦ 0) (fun y ↦ t⁻¹ * (u ∘ Φ) y) y
    rw [matrixOperator_const_mul a' b' (fun _ ↦ 0) hd t⁻¹]
    have hscale := matrixOperator_comp_const_add_smul a b (fun _ ↦ 0) u z y r
    simp only [mul_zero] at hscale
    change matrixOperator a' b' (fun _ ↦ 0) (u ∘ Φ) y =
      r ^ 2 * matrixOperator a b (fun _ ↦ 0) u (Φ y) at hscale
    rw [hscale]
    exact mul_nonneg (inv_nonneg.mpr ht.le)
      (mul_nonneg (sq_nonneg r) (hsuper (Φ y) (hmapsOpen hy)))
  let y₀ := r⁻¹ • (x₀ - z)
  have hΦy₀ : Φ y₀ = x₀ := by simp [Φ, y₀, smul_smul, hr.ne']
  have hy₀ : y₀ ∈ closedBall (0 : ℝ^n) (R / 2) := by
    rw [mem_closedBall, ← hΦy₀, hdist] at hx₀
    exact mem_closedBall_zero_iff.2 ((mul_le_mul_iff_right₀ hr).mp hx₀)
  have h :=
    hbound a' b' (fun y hy ↦ ha _ (hmapsOpen hy))
      (fun y hy ↦ hell _ (hmapsOpen hy)) (fun y hy ↦ htrace _ (hmapsOpen hy))
      (fun y hy ↦ by
        change ‖r • b (Φ y)‖ ≤ B
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
        exact (mul_le_mul_of_nonneg_left (hdrift _ (hmapsOpen hy)) hr.le).trans
          (mul_le_of_le_one_left hB hr₁))
      v hv hvreg
      (fun y hy ↦ mul_nonneg (inv_nonneg.mpr ht.le) (hnonneg _ (hmaps hy)))
      hvsuper y₀ hy₀ (by
        change t⁻¹ * u (Φ y₀) ≤ 1
        rw [hΦy₀, inv_mul_eq_div]
        exact (div_le_one ht).mpr hsmall)
  let S := ball (0 : ℝ^n) ρ ∩ {y | v y ≤ M}
  have hfinite : volume S ≠ ∞ :=
    (measure_mono inter_subset_left |>.trans_lt measure_ball_lt_top).ne
  have hreal : volume.real (closedBall (0 : ℝ^n) (R / 2)) ≤ D * volume.real S := by
    have h' := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite) h
    simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_ofReal hD.le] using h'
  have hsubset : Φ '' S ⊆ ball z (r * ρ) ∩ {x | u x ≤ max 2 M * t} := by
    rintro _ ⟨y, hy, rfl⟩
    constructor
    · rw [mem_ball, hdist]
      exact mul_lt_mul_of_pos_left (mem_ball_zero_iff.1 hy.1) hr
    · have hlow : t⁻¹ * u (Φ y) ≤ M := hy.2
      rw [inv_mul_eq_div] at hlow
      exact ((div_le_iff₀ ht).mp hlow).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) ht.le)
  have hmeasure : r ^ n * volume.real S ≤
      volume.real (ball z (r * ρ) ∩ {x | u x ≤ max 2 M * t}) := by
    rw [← volume_real_image_const_add_smul z hr.le]
    exact measureReal_mono hsubset
      (measure_mono inter_subset_left |>.trans_lt measure_ball_lt_top).ne
  calc _ ≤ r ^ n * (D * volume.real S) := by gcongr
    _ = D * (r ^ n * volume.real S) := by ring
    _ ≤ _ := by gcongr

end EllipticHarnack
