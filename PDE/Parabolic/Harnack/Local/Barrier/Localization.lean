/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Harnack.Local.Barrier.Expanding
import CAS.ExactTactic

/-!
# A barrier whose forcing lies in an earlier inner cylinder

An expanding polynomial bump starts from zero and reaches the half ball at the
top time. Its positive forcing is confined to an initial inner cylinder.
Subtracting a small linear function of time makes the residual strictly
negative elsewhere. All constants are chosen from geometry and coefficient
bounds before a supersolution is supplied.
-/

@[expose] public noncomputable section

namespace ParabolicHarnack

open PDE.Analysis ParabolicMaximum Set Metric
open scoped RealInnerProductSpace

variable {n : ℕ}

/-- The chosen expanding radius stays inside the outer ball up to time `b`,
and inside the inner ball up to the positive localization time `ε`. -/
private theorem localization_scale_bounds
    {R ρ b : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (hb : 0 < b) :
    let r := min (ρ / 4) (R / 4)
    let v := R ^ 2 / (2 * b)
    let ε := min (b / 4) ((ρ ^ 2 - r ^ 2) / (2 * v))
    0 < r ∧ 0 < v ∧ v * b = R ^ 2 / 2 ∧
      0 < ε ∧ ε ≤ b / 4 ∧ r ^ 2 + v * ε ≤ ρ ^ 2 ∧
      ∀ t ≤ b, r ^ 2 + v * t ≤ R ^ 2 := by
  dsimp only
  let r := min (ρ / 4) (R / 4)
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hrρ : r ≤ ρ / 4 := min_le_left _ _
  have hrR : r ≤ R / 4 := min_le_right _ _
  have hrρsq : r ^ 2 < ρ ^ 2 :=
    pow_lt_pow_left₀ (hrρ.trans_lt (by linarith)) hr.le two_ne_zero
  have hrRsq : r ^ 2 ≤ R ^ 2 / 16 := (pow_le_pow_left₀ hr.le hrR 2).trans_eq (by ring)
  let v := R ^ 2 / (2 * b)
  have hv : 0 < v := by dsimp [v]; positivity
  have hvb : v * b = R ^ 2 / 2 := by dsimp [v]; cas
  let ε := min (b / 4) ((ρ ^ 2 - r ^ 2) / (2 * v))
  have hε : 0 < ε := lt_min (by positivity) (div_pos (sub_pos.mpr hrρsq) (by positivity))
  refine ⟨hr, hv, hvb, hε, min_le_left _ _, ?_, ?_⟩
  · have hsmall := (le_div_iff₀ (show 0 < 2 * v by positivity)).mp (min_le_right _ _ :
      ε ≤ (ρ ^ 2 - r ^ 2) / (2 * v))
    change r ^ 2 + v * ε ≤ ρ ^ 2
    linarith [mul_pos hv hε]
  · intro t ht
    change r ^ 2 + v * t ≤ R ^ 2
    linarith [mul_le_mul_of_nonneg_left ht hv.le, sq_nonneg R]

/-- A global C² barrier for localized parabolic contacts, with a positive
residual margin. The forcing cylinder ends before one quarter of the reference
time. No coefficient regularity is required for these pointwise bounds. -/
theorem exists_barrier_for_contact_localization
    {R ρ b θ τ B : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (hb : 0 < b)
    (hθ : 0 < θ) (hτ : 0 ≤ τ) (hB : 0 ≤ B) :
    ∃ (φ : ℝ^n → ℝ → ℝ) (M F κ ε σ : ℝ),
      ContDiff ℝ 2 (Function.uncurry φ) ∧ 0 < M ∧ 0 ≤ F ∧
      0 < κ ∧ κ * R ^ 2 ≤ 1 ∧ 0 < ε ∧ ε ≤ b / 4 ∧ 0 < σ ∧
      (∀ x t, t ∈ Icc 0 b → φ x t ≤ M) ∧
      (∀ x ∈ closedBall (0 : ℝ^n) (R / 2), 2 ≤ φ x b) ∧
      (∀ x, φ x 0 = 0) ∧
      (∀ x ∈ sphere (0 : ℝ^n) R, ∀ t ∈ Icc 0 b, φ x t ≤ 0) ∧
      ∀ (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ) (d : ℝ^n → ℝ → ℝ^n),
        (∀ p ∈ ball (0 : ℝ^n) R ×ˢ Ioc 0 b, (a p.1 p.2).PosSemidef) →
        (∀ p ∈ ball (0 : ℝ^n) R ×ˢ Ioc 0 b, ∀ z : ℝ^n,
          θ * ‖z‖ ^ 2 ≤ ⟪z, (a p.1 p.2).toEuclideanLin z⟫) →
        (∀ p ∈ ball (0 : ℝ^n) R ×ˢ Ioc 0 b, (a p.1 p.2).trace ≤ τ) →
        (∀ p ∈ ball (0 : ℝ^n) R ×ˢ Ioc 0 b, ‖d p.1 p.2‖ ≤ B) →
        (∀ p ∈ ball (0 : ℝ^n) R ×ˢ Ioc 0 b,
          matrixParabolicOperator a d (fun _ _ ↦ 0) φ p.1 p.2 ≤ F) ∧
        (∀ p ∈ ball (0 : ℝ^n) R ×ˢ Ioc 0 b, p ∉ ball (0 : ℝ^n) ρ ×ˢ Ioc 0 ε →
          matrixParabolicOperator a d (fun _ _ ↦ 0) φ p.1 p.2 <
            -(κ * (τ + B * (2 * R) + 1) + σ)) := by
  let r := min (ρ / 4) (R / 4)
  let v := R ^ 2 / (2 * b)
  let ε := min (b / 4) ((ρ ^ 2 - r ^ 2) / (2 * v))
  obtain ⟨hr, hv, hvb, hε, hεb, hεradius, hradius⟩ := localization_scale_bounds hR hρ hb
  let K := 3 * v + 6 * (τ + R * B)
  let δ := ε⁻¹ + (K + 24 * θ) ^ 2 / (4 * (24 * θ) * r ^ 2)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  let Ψ := expandingPolynomialBump (0 : ℝ^n) r v δ
  have hΨ : ContDiff ℝ 2 (Function.uncurry Ψ) :=
    contDiff_expandingPolynomialBump 0 r v δ
  have hΨspace (t : ℝ) : ContDiff ℝ 2 (fun x ↦ Ψ x t) :=
    hΨ.comp (contDiff_id.prodMk contDiff_const)
  have hΨtime (x : ℝ^n) (t : ℝ) : DifferentiableAt ℝ (Ψ x) t :=
    (hasDerivAt_expandingPolynomialBump 0 r v δ x t).differentiableAt
  let A := 3 / (b * Real.exp (-δ * b) * (R ^ 2 / 4) ^ 3)
  have hA : 0 < A := by dsimp [A]; positivity
  have hAnorm : A * (b * Real.exp (-δ * b) * (R ^ 2 / 4) ^ 3) = 3 :=
    div_mul_cancel₀ _ (ne_of_gt (by positivity))
  let φ := fun x t ↦ A * Ψ x t - t / b
  have hφ : ContDiff ℝ 2 (Function.uncurry φ) :=
    (contDiff_const.mul hΨ).sub (contDiff_snd.div_const b)
  let M := A * (b * R ^ 6) + 1
  let F := A * (R ^ 6 + b * K * R ^ 4)
  have hM : 0 < M := by dsimp [M]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  let T := τ + B * (2 * R) + 1
  have hT : 0 ≤ T := by dsimp [T]; positivity
  let κ := min (1 / (R ^ 2 + 1)) (b⁻¹ / (T + 1))
  have hκ : 0 < κ := lt_min (by positivity) (by positivity)
  have hκR : κ * (R ^ 2 + 1) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < R ^ 2 + 1)).mp (min_le_left _ _)
  have hκT : κ * (T + 1) ≤ b⁻¹ :=
    (le_div_iff₀ (by positivity : 0 < T + 1)).mp (min_le_right _ _)
  have hstrict : κ * T < b⁻¹ := by linarith
  let σ := (b⁻¹ - κ * T) / 2
  have hσ : 0 < σ := by dsimp [σ]; linarith
  have hmargin : κ * T + σ < b⁻¹ := by dsimp [σ]; linarith
  have hres (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ) (d : ℝ^n → ℝ → ℝ^n)
      (x : ℝ^n) (t : ℝ) :
      matrixParabolicOperator a d (fun _ _ ↦ 0) φ x t =
        A * matrixParabolicOperator a d (fun _ _ ↦ 0) Ψ x t - b⁻¹ := by
    have htime : HasDerivAt (fun s : ℝ ↦ s / b) b⁻¹ t := by cas
    change matrixParabolicOperator a d (fun _ _ ↦ 0) (fun y s ↦ A * Ψ y s - s / b)
      x t = _
    rw [matrixParabolicOperator_sub a d (fun _ _ ↦ 0)
      (contDiff_const.mul (hΨspace t)).contDiffAt contDiffAt_const
      ((hΨtime x t).const_mul A) htime.differentiableAt,
      matrixParabolicOperator_const_mul a d (fun _ _ ↦ 0)
        ((hΨspace t).differentiable (by norm_num) x) (hΨtime x t) A]
    simp only [matrixParabolicOperator, htime.deriv,
      EllipticMaximum.matrixOperator_const, zero_mul, add_zero]
  refine ⟨φ, M, F, κ, ε, σ, hφ, hM, hF, hκ, by linarith, hε, hεb, hσ,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro x t ht
    have := mul_le_mul_of_nonneg_left
      (expandingPolynomialBump_le (0 : ℝ^n) x hδ ht.1 ht.2 (hradius t ht.2)) hA.le
    dsimp only [φ, M]
    linarith [div_nonneg ht.1 hb.le]
  · intro x hx
    have hxnorm : ‖x‖ ≤ R / 2 := by simpa using hx
    have hxsq : ‖x‖ ^ 2 ≤ R ^ 2 / 4 :=
      (pow_le_pow_left₀ (norm_nonneg x) hxnorm 2).trans_eq (by ring)
    have hgap : R ^ 2 / 4 ≤ r ^ 2 + v * b - ‖x‖ ^ 2 := by linarith [sq_nonneg r]
    have hcube : (R ^ 2 / 4) ^ 3 ≤ (r ^ 2 + v * b - ‖x‖ ^ 2)⁺ ^ 3 :=
      pow_le_pow_left₀ (by positivity) (hgap.trans le_sup_left) _
    have hψlower : b * Real.exp (-δ * b) * (R ^ 2 / 4) ^ 3 ≤ Ψ x b := by
      simpa only [Ψ, expandingPolynomialBump, sub_zero] using
        mul_le_mul_of_nonneg_left hcube (by positivity : 0 ≤ b * Real.exp (-δ * b))
    have hscaled := mul_le_mul_of_nonneg_left hψlower hA.le
    dsimp [φ]
    rw [div_self hb.ne']
    linarith
  · intro x
    simp [φ, Ψ, expandingPolynomialBump]
  · intro x hx t ht
    have hnorm : ‖x - (0 : ℝ^n)‖ = R := by simpa only [mem_sphere, dist_eq_norm] using hx
    have hzero : Ψ x t = 0 := expandingPolynomialBump_eq_zero 0 x (hnorm ▸ hradius t ht.2)
    simpa only [φ, hzero, mul_zero, zero_sub, neg_nonpos] using div_nonneg ht.1 hb.le
  · intro a d ha hell htrace hdrift
    constructor
    · intro p hp
      have hbase := matrixParabolicOperator_expandingPolynomialBump_le a d (0 : ℝ^n)
        p.1 hR.le hv.le hδ hτ hB hp.2.1.le hp.2.2 (hradius p.2 hp.2.2) (ha p hp)
        ((mul_nonneg hθ.le (sq_nonneg _)).trans (hell p hp (p.1 - 0)))
        (htrace p hp) (hdrift p hp)
      rw [hres]
      exact (sub_le_self _ (inv_nonneg.mpr hb.le)).trans
        (mul_le_mul_of_nonneg_left hbase hA.le)
    · intro p hp houtside
      have hbase : matrixParabolicOperator a d (fun _ _ ↦ 0) Ψ p.1 p.2 ≤ 0 := by
        by_cases hlate : ε ≤ p.2
        · exact matrixParabolicOperator_expandingPolynomialBump_nonpos a d (0 : ℝ^n)
            p.1 hr hR.le hv.le hθ hε hlate (hradius p.2 hp.2.2) le_rfl
            (ha p hp) (hell p hp) (htrace p hp) (hdrift p hp)
        · have hx : p.1 ∉ ball (0 : ℝ^n) ρ :=
            fun hx ↦ houtside ⟨hx, hp.2.1, (lt_of_not_ge hlate).le⟩
          have hxnorm : ρ ≤ ‖p.1 - (0 : ℝ^n)‖ := by
            simpa only [mem_ball, dist_eq_norm, not_lt] using hx
          have := mul_le_mul_of_nonneg_left (lt_of_not_ge hlate).le hv.le
          have := (sq_le_sq₀ hρ.le (norm_nonneg _)).mpr hxnorm
          exact (matrixParabolicOperator_expandingPolynomialBump_eq_zero a d 0 p.1
            (by linarith) (ha p hp)).le
      rw [hres]
      linarith [mul_nonpos_of_nonneg_of_nonpos hA.le hbase]

end ParabolicHarnack
