/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.MaximumPrinciple.MatrixStrong
import CAS.ExactTactic

/-!
# Gaussian barriers for localization of contact measure

The Gaussian barrier has a uniformly negative residual outside any fixed inner
ball when its decay parameter is sufficiently large. The estimates use only
ellipticity, the principal trace bound, and the drift bound. Coefficients are
never differentiated.
-/

@[expose] public section

noncomputable section

namespace EllipticHarnack

open PDE.Analysis EllipticMaximum Metric Set
open scoped RealInnerProductSpace

variable {n : ℕ}

/-- The Gaussian residual in the matrix operator. The principal factors
are obtained from positive semidefiniteness, with no regularity of the factors. -/
theorem matrixOperator_radialBarrier
    (a : ℝ^n → Matrix (Fin n) (Fin n) ℝ) (b : ℝ^n → ℝ^n)
    (z : ℝ^n) (R t : ℝ) {x : ℝ^n} (ha : (a x).PosSemidef) :
    matrixOperator a b (fun _ ↦ 0) (radialBarrier z R t) x =
      Real.exp (-t * ‖x - z‖ ^ 2) *
        (2 * t * (a x).trace - 4 * t ^ 2 * ⟪x - z, (a x).toEuclideanLin (x - z)⟫ -
          2 * t * ⟪x - z, b x⟫) := by
  obtain ⟨σ, hσ⟩ := exists_factors_of_posSemidef ha
  rw [matrixOperator_eq_factoredOperator a (fun _ ↦ σ) b (fun _ ↦ 0)
    (contDiff_radialBarrier z R t).contDiffAt hσ, factoredOperator_radialBarrier]
  rw [sum_norm_sq_eq_matrix_trace (a x) σ hσ,
    sum_inner_sq_eq_matrix_quadratic (a x) σ hσ, ← inner_toEuclideanLin_self]
  simp only [zero_mul, add_zero, Matrix.trace, Matrix.diag_apply]

/-- A Gaussian barrier has a uniform upper residual bound throughout the ball. -/
theorem matrixOperator_radialBarrier_le
    (a : ℝ^n → Matrix (Fin n) (Fin n) ℝ) (b : ℝ^n → ℝ^n)
    {R t τ B : ℝ} (ht : 0 < t) (hτ : 0 ≤ τ) (hB : 0 ≤ B)
    {x : ℝ^n} (hx : ‖x‖ ≤ R) (ha : (a x).PosSemidef)
    (hquadratic : 0 ≤ ⟪x, (a x).toEuclideanLin x⟫)
    (htrace : (a x).trace ≤ τ) (hdrift : ‖b x‖ ≤ B) :
    matrixOperator a b (fun _ ↦ 0) (radialBarrier 0 R t) x ≤
      2 * t * (τ + R * B) := by
  have hR : 0 ≤ R := (norm_nonneg _).trans hx
  have hinner : -(R * B) ≤ ⟪x, b x⟫ := by
    have habs := (abs_real_inner_le_norm x (b x)).trans
      (mul_le_mul hx hdrift (norm_nonneg _) hR)
    linarith [neg_abs_le ⟪x, b x⟫]
  have hbase : 2 * t * (a x).trace -
      4 * t ^ 2 * ⟪x, (a x).toEuclideanLin x⟫ - 2 * t * ⟪x, b x⟫ ≤
        2 * t * (τ + R * B) := by
    have h1 := mul_le_mul_of_nonneg_left htrace (show 0 ≤ 2 * t by positivity)
    have h2 := mul_le_mul_of_nonneg_left hinner (show 0 ≤ 2 * t by positivity)
    have h3 := mul_nonneg (sq_nonneg t) hquadratic
    nlinarith
  rw [matrixOperator_radialBarrier a b 0 R t ha, sub_zero]
  calc
    _ ≤ Real.exp (-t * ‖x‖ ^ 2) * (2 * t * (τ + R * B)) :=
      mul_le_mul_of_nonneg_left hbase (Real.exp_nonneg _)
    _ ≤ 1 * (2 * t * (τ + R * B)) :=
      mul_le_mul_of_nonneg_right
        (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ‖x‖])) (by positivity)
    _ = _ := one_mul _

/-- A sufficiently steep Gaussian has a strictly negative residual, uniformly
on the closed annulus from `ρ` to `R`. -/
theorem matrixOperator_radialBarrier_le_neg
    (a : ℝ^n → Matrix (Fin n) (Fin n) ℝ) (b : ℝ^n → ℝ^n)
    {R ρ t α τ B : ℝ} (ht : 0 < t) (hα : 0 < α) (hρ : 0 < ρ)
    (hsteep : τ + R * B + 1 ≤ 2 * t * α * ρ ^ 2)
    {x : ℝ^n} (hxinner : ρ ≤ ‖x‖) (hxouter : ‖x‖ ≤ R)
    (ha : (a x).PosSemidef)
    (hell : α * ‖x‖ ^ 2 ≤ ⟪x, (a x).toEuclideanLin x⟫)
    (htrace : (a x).trace ≤ τ) (hdrift : ‖b x‖ ≤ B) :
    matrixOperator a b (fun _ ↦ 0) (radialBarrier 0 R t) x ≤
      -(2 * t * Real.exp (-t * R ^ 2)) := by
  have hR : 0 ≤ R := (norm_nonneg _).trans hxouter
  have hinner : -(R * B) ≤ ⟪x, b x⟫ := by
    have habs := (abs_real_inner_le_norm x (b x)).trans
      (mul_le_mul hxouter hdrift (norm_nonneg _) hR)
    linarith [neg_abs_le ⟪x, b x⟫]
  have hsq := (sq_le_sq₀ hρ.le (norm_nonneg _)).mpr hxinner
  have hq : α * ρ ^ 2 ≤ ⟪x, (a x).toEuclideanLin x⟫ :=
    (mul_le_mul_of_nonneg_left hsq hα.le).trans hell
  have hbase : 2 * t * (a x).trace -
      4 * t ^ 2 * ⟪x, (a x).toEuclideanLin x⟫ - 2 * t * ⟪x, b x⟫ ≤ -(2 * t) := by
    have h1 := mul_le_mul_of_nonneg_left htrace (show 0 ≤ 2 * t by positivity)
    have h2 := mul_le_mul_of_nonneg_left hinner (show 0 ≤ 2 * t by positivity)
    have h3 := mul_le_mul_of_nonneg_left hq (show 0 ≤ 4 * t ^ 2 by positivity)
    have h4 := mul_le_mul_of_nonneg_left hsteep (show 0 ≤ 2 * t by positivity)
    nlinarith
  have hexp : Real.exp (-t * R ^ 2) ≤ Real.exp (-t * ‖x‖ ^ 2) := by
    apply Real.exp_le_exp.mpr
    have hsqouter := (sq_le_sq₀ (norm_nonneg _) hR).mpr hxouter
    nlinarith
  rw [matrixOperator_radialBarrier a b 0 R t ha, sub_zero]
  calc
    _ ≤ Real.exp (-t * ‖x‖ ^ 2) * -(2 * t) :=
      mul_le_mul_of_nonneg_left hbase (Real.exp_nonneg _)
    _ ≤ Real.exp (-t * R ^ 2) * -(2 * t) :=
      mul_le_mul_of_nonpos_right hexp (by linarith)
    _ = _ := by cas

/-- A normalized Gaussian and a positive aperture force lower contacts into
the prescribed inner ball. Every constant is chosen from coefficient bounds
and radii, before any supersolution is given. -/
theorem exists_barrier_for_contact_localization
    {R ρ α τ B : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (hα : 0 < α)
    (hτ : 0 ≤ τ) (hB : 0 ≤ B) :
    ∃ (φ : ℝ^n → ℝ) (M F κ : ℝ),
      ContDiff ℝ 2 φ ∧ 0 < M ∧ 0 ≤ F ∧ 0 < κ ∧ κ * R ^ 2 ≤ 1 ∧
      (∀ x, φ x ≤ M) ∧
      (∀ x ∈ closedBall (0 : ℝ^n) (R / 2), 2 ≤ φ x) ∧
      (∀ x ∈ sphere (0 : ℝ^n) R, φ x = 0) ∧
      ∀ (a : ℝ^n → Matrix (Fin n) (Fin n) ℝ) (b : ℝ^n → ℝ^n),
        (∀ x ∈ ball (0 : ℝ^n) R, (a x).PosSemidef) →
        (∀ x ∈ ball (0 : ℝ^n) R, ∀ v : ℝ^n,
          α * ‖v‖ ^ 2 ≤ ⟪v, (a x).toEuclideanLin v⟫) →
        (∀ x ∈ ball (0 : ℝ^n) R, (a x).trace ≤ τ) →
        (∀ x ∈ ball (0 : ℝ^n) R, ‖b x‖ ≤ B) →
        (∀ x ∈ ball (0 : ℝ^n) R, matrixOperator a b (fun _ ↦ 0) φ x ≤ F) ∧
        (∀ x ∈ ball (0 : ℝ^n) R, ρ ≤ ‖x‖ →
          matrixOperator a b (fun _ ↦ 0) φ x < -(κ * (τ + B * (2 * R)))) := by
  let t := 1 + (τ + R * B + 1) / (2 * α * ρ ^ 2)
  have hden : 0 < 2 * α * ρ ^ 2 := by positivity
  have ht : 0 < t := by dsimp [t]; positivity
  have htcalc : (t - 1) * (2 * α * ρ ^ 2) = τ + R * B + 1 := by
    dsimp [t]
    rw [add_sub_cancel_left, div_mul_cancel₀ _ hden.ne']
  have hsteep : τ + R * B + 1 ≤ 2 * t * α * ρ ^ 2 := by nlinarith
  let d := Real.exp (-t * (R / 2) ^ 2) - Real.exp (-t * R ^ 2)
  have hd : 0 < d :=
    sub_pos.mpr (Real.exp_lt_exp.mpr (by nlinarith [mul_pos ht (sq_pos_of_pos hR)]))
  let M := 2 / d
  have hM : 0 < M := by dsimp [M]; positivity
  let φ := fun x : ℝ^n ↦ M * radialBarrier 0 R t x
  have hφ : ContDiff ℝ 2 φ := contDiff_const.mul (contDiff_radialBarrier 0 R t)
  have hres (a : ℝ^n → Matrix (Fin n) (Fin n) ℝ) (b : ℝ^n → ℝ^n)
      (x : ℝ^n) : matrixOperator a b (fun _ ↦ 0) φ x =
      M * matrixOperator a b (fun _ ↦ 0) (radialBarrier 0 R t) x :=
    matrixOperator_const_mul a b (fun _ ↦ 0)
      ((contDiff_radialBarrier 0 R t).differentiable (by norm_num) x) M
  let F := M * (2 * t * (τ + R * B))
  have hF : 0 ≤ F := by dsimp [F]; positivity
  let η := M * (2 * t * Real.exp (-t * R ^ 2))
  have hη : 0 < η := by dsimp [η]; positivity
  let T := τ + B * (2 * R)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  let κ := min (1 / (R ^ 2 + 1)) (η / (T + 1))
  have hκ : 0 < κ := lt_min (by positivity) (by positivity)
  have hκR : κ * (R ^ 2 + 1) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < R ^ 2 + 1)).mp (min_le_left _ _)
  have hκT : κ * (T + 1) ≤ η :=
    (le_div_iff₀ (by positivity : 0 < T + 1)).mp (min_le_right _ _)
  have hκsmall : κ * T < η := by nlinarith
  refine ⟨φ, M, F, κ, hφ, hM, hF, hκ, by nlinarith, fun x ↦ ?_, ?_, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_left (radialBarrier_le_one 0 R ht.le x) hM.le).trans_eq
      (mul_one M)
  · intro x hx
    have hxnorm : ‖x‖ ≤ R / 2 := by simpa using hx
    have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ R / 2)).mpr hxnorm
    have hexp : Real.exp (-t * (R / 2) ^ 2) ≤ Real.exp (-t * ‖x‖ ^ 2) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hbarrier : d ≤ radialBarrier (0 : ℝ^n) R t x := by
      dsimp [d, radialBarrier]
      simpa only [sub_zero] using sub_le_sub_right hexp (Real.exp (-t * R ^ 2))
    have hMd : M * d = 2 := by dsimp [M]; exact div_mul_cancel₀ _ hd.ne'
    exact hMd.symm.le.trans (mul_le_mul_of_nonneg_left hbarrier hM.le)
  · intro x hx
    simp only [φ, radialBarrier_eq_zero (by simpa only [mem_sphere, dist_eq_norm] using hx),
      mul_zero]
  · intro a b ha hell htrace hdrift
    constructor
    · intro x hx
      have hxnorm : ‖x‖ ≤ R := (show ‖x‖ < R by simpa using hx).le
      rw [hres]
      apply mul_le_mul_of_nonneg_left _ hM.le
      exact matrixOperator_radialBarrier_le a b ht hτ hB hxnorm (ha x hx)
        ((mul_nonneg hα.le (sq_nonneg ‖x‖)).trans (hell x hx x))
        (htrace x hx) (hdrift x hx)
    · intro x hx hxinner
      have hneg := matrixOperator_radialBarrier_le_neg a b ht hα hρ hsteep hxinner
        (show ‖x‖ < R by simpa using hx).le (ha x hx) (hell x hx x) (htrace x hx) (hdrift x hx)
      rw [hres]
      exact ((mul_le_mul_of_nonneg_left hneg hM.le).trans_eq (mul_neg _ _)).trans_lt
        (neg_lt_neg hκsmall)

end EllipticHarnack
