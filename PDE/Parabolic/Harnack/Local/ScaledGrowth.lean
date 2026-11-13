/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.AffineVolume.Product
public import PDE.Parabolic.Harnack.Local.Growth
public import PDE.Parabolic.Harnack.Local.Scaling

/-!
# Localized growth at arbitrary parabolic scales

Translation, spatial dilation by `r`, temporal dilation by `r²`, and division
by a positive level transport the contact estimate. The exact volume factor
is `r^(n + 2)`. Coefficient bounds determine every constant before the center,
scale, coefficients, supersolution, and normalization level.
-/

@[expose] public noncomputable section

namespace ParabolicHarnack

open PDE.Analysis ParabolicMaximum Set Metric MeasureTheory
open scoped RealInnerProductSpace ENNReal

variable {n : ℕ}

/-- The smooth local growth estimate on translated cylinders of scale at most
one. The inhomogeneous allowance has its natural parabolic scaling. -/
theorem exists_scaled_sublevel_measure_bound
    {R ρ α τ B b : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (hα : 0 < α)
    (hB : 0 ≤ B) (hb : 0 < b) (hshort : b < R ^ 2 / 8) :
    ∃ M D ε σ : ℝ, 2 ≤ M ∧ 0 < D ∧ 0 < ε ∧ ε ≤ b / 4 ∧ 0 < σ ∧
      ∀ (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ) (d : ℝ^n → ℝ → ℝ^n)
        (z : ℝ^n) (s r : ℝ), 0 < r → r ≤ 1 →
        (∀ p ∈ ball z (r * R) ×ˢ Ioc s (s + r ^ 2 * b), (a p.1 p.2).PosSemidef) →
        (∀ p ∈ ball z (r * R) ×ˢ Ioc s (s + r ^ 2 * b), ∀ v : ℝ^n,
          α * ‖v‖ ^ 2 ≤ ⟪v, (a p.1 p.2).toEuclideanLin v⟫) →
        (∀ p ∈ ball z (r * R) ×ˢ Ioc s (s + r ^ 2 * b), (a p.1 p.2).trace ≤ τ) →
        (∀ p ∈ ball z (r * R) ×ˢ Ioc s (s + r ^ 2 * b), ‖d p.1 p.2‖ ≤ B) →
        ∀ (u : ℝ^n → ℝ → ℝ) (ℓ : ℝ), 0 < ℓ →
          (∀ p ∈ closedBall z (r * R) ×ˢ Icc s (s + r ^ 2 * b),
            ContDiffAt ℝ 2 (Function.uncurry u) p) →
          (∀ p ∈ closedBall z (r * R) ×ˢ Icc s (s + r ^ 2 * b), 0 ≤ u p.1 p.2) →
          (∀ p ∈ ball z (r * R) ×ˢ Ioc s (s + r ^ 2 * b),
            -σ * ℓ ≤ r ^ 2 * matrixParabolicOperator a d (fun _ _ ↦ 0) u p.1 p.2) →
          ∀ x₀ ∈ closedBall z (r * (R / 2)), u x₀ (s + r ^ 2 * b) ≤ ℓ →
            r ^ (n + 2) *
                volume.real (closedBall (0 : ℝ^n) (R / 2) ×ˢ Icc (b / 4) (b / 2)) ≤
              D * volume.real ((ball z (r * ρ) ×ˢ Ioc s (s + r ^ 2 * ε)) ∩
                {p | u p.1 p.2 ≤ M * ℓ}) := by
  obtain ⟨M, D, ε, σ, _, hD, hε, hεb, hσ, hgrowth⟩ :=
    exists_localized_sublevel_measure_bound (n := n) hR hρ hα hb hshort
  refine ⟨max 2 M, D, ε, σ, le_max_left _ _, hD, hε, hεb, hσ, ?_⟩
  intro a d z s r hr hr₁ ha hell htrace hdrift u ℓ hℓ hreg hnonneg hsuper x₀ hx₀ hsmall
  let Φ : ℝ^n × ℝ → ℝ^n × ℝ := fun p ↦ (z + r • p.1, s + r ^ 2 * p.2)
  have hΦ : ContDiff ℝ 2 Φ := by dsimp only [Φ]; fun_prop
  have hdist (x : ℝ^n) : dist (z + r • x) z = r * ‖x‖ := by
    simp [dist_eq_norm, norm_smul, abs_of_pos hr]
  have hmaps :
      MapsTo Φ (closedBall 0 R ×ˢ Icc 0 b)
        (closedBall z (r * R) ×ˢ Icc s (s + r ^ 2 * b)) := fun p hp ↦
    ⟨show dist (z + r • p.1) z ≤ r * R by
        rw [hdist]; exact mul_le_mul_of_nonneg_left (by simpa using hp.1) hr.le,
      le_add_of_nonneg_right (mul_nonneg (sq_nonneg r) hp.2.1),
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hp.2.2 (sq_nonneg r))⟩
  have hmapsOpen :
      MapsTo Φ (ball 0 R ×ˢ Ioc 0 b)
        (ball z (r * R) ×ˢ Ioc s (s + r ^ 2 * b)) := fun p hp ↦
    ⟨show dist (z + r • p.1) z < r * R by
        rw [hdist]; exact mul_lt_mul_of_pos_left (by simpa using hp.1) hr,
      lt_add_of_pos_right _ (mul_pos (sq_pos_of_pos hr) hp.2.1),
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hp.2.2 (sq_nonneg r))⟩
  let a' := fun x t ↦ a (Φ (x, t)).1 (Φ (x, t)).2
  let d' := fun x t ↦ r • d (Φ (x, t)).1 (Φ (x, t)).2
  let v := fun x t ↦ ℓ⁻¹ * u (Φ (x, t)).1 (Φ (x, t)).2
  have hvreg (p : ℝ^n × ℝ) (hp : p ∈ closedBall 0 R ×ˢ Icc 0 b) :
      ContDiffAt ℝ 2 (Function.uncurry v) p :=
    contDiffAt_const.mul ((hreg (Φ p) (hmaps hp)).comp p hΦ.contDiffAt)
  have hvsuper (p : ℝ^n × ℝ) (hp : p ∈ ball (0 : ℝ^n) R ×ˢ Ioc 0 b) :
      -σ ≤ matrixParabolicOperator a' d' (fun _ _ ↦ 0) v p.1 p.2 := by
    have hclosed : p ∈ closedBall (0 : ℝ^n) R ×ˢ Icc 0 b :=
      ⟨ball_subset_closedBall hp.1, hp.2.1.le, hp.2.2⟩
    have huΦ := (hreg (Φ p) (hmaps hclosed)).comp p hΦ.contDiffAt
    have hspace := (huΦ.comp p.1 (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt
      (by norm_num)
    have htime := (huΦ.comp p.2 (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt
      (by norm_num)
    change -σ ≤ matrixParabolicOperator a' d' (fun _ _ ↦ 0)
      (fun x t ↦ ℓ⁻¹ * u (Φ (x, t)).1 (Φ (x, t)).2) p.1 p.2
    rw [matrixParabolicOperator_const_mul a' d' (fun _ _ ↦ 0) hspace htime]
    have hscale := matrixParabolicOperator_comp_space_time_dilation a d (fun _ _ ↦ 0)
      u z p.1 s p.2 r
    simp only [mul_zero] at hscale
    change matrixParabolicOperator a' d' (fun _ _ ↦ 0)
      (fun x t ↦ u (Φ (x, t)).1 (Φ (x, t)).2) p.1 p.2 =
        r ^ 2 * matrixParabolicOperator a d (fun _ _ ↦ 0) u (Φ p).1 (Φ p).2 at hscale
    rw [hscale, inv_mul_eq_div]
    exact (le_div_iff₀ hℓ).mpr (hsuper (Φ p) (hmapsOpen hp))
  let y₀ := r⁻¹ • (x₀ - z)
  have hΦy₀ : z + r • y₀ = x₀ := by simp [y₀, smul_smul, hr.ne']
  have hy₀ : y₀ ∈ closedBall (0 : ℝ^n) (R / 2) := by
    rw [mem_closedBall, ← hΦy₀, hdist] at hx₀
    rw [mem_closedBall, dist_zero_right]
    exact (mul_le_mul_iff_right₀ hr).mp hx₀
  have h := hgrowth a' d'
    (fun p hp ↦ ha _ (hmapsOpen hp))
    (fun p hp ↦ hell _ (hmapsOpen hp))
    (fun p hp ↦ htrace _ (hmapsOpen hp))
    (fun p hp ↦ by
      change ‖r • d (Φ p).1 (Φ p).2‖ ≤ B
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      exact (mul_le_mul_of_nonneg_left (hdrift _ (hmapsOpen hp)) hr.le).trans
        (mul_le_of_le_one_left hB hr₁))
    v hvreg (fun p hp ↦ mul_nonneg (inv_nonneg.mpr hℓ.le) (hnonneg _ (hmaps hp)))
    hvsuper y₀ hy₀ (by
      change ℓ⁻¹ * u (z + r • y₀) (s + r ^ 2 * b) ≤ 1
      rw [hΦy₀, inv_mul_eq_div]
      exact (div_le_one hℓ).mpr hsmall)
  let S := (ball (0 : ℝ^n) ρ ×ˢ Ioc 0 ε) ∩ {p | v p.1 p.2 ≤ M}
  have hfinite : volume S ≠ ∞ :=
    ((isBounded_ball.prod (isBounded_Ioc _ _)).subset inter_subset_left).measure_lt_top.ne
  have hreal :
      volume.real (closedBall (0 : ℝ^n) (R / 2) ×ˢ Icc (b / 4) (b / 2)) ≤
        D * volume.real S := by
    have h' := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite) h
    simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_ofReal hD.le] using h'
  have hsubset : Φ '' S ⊆
      (ball z (r * ρ) ×ˢ Ioc s (s + r ^ 2 * ε)) ∩
        {p | u p.1 p.2 ≤ max 2 M * ℓ} := by
    rintro _ ⟨p, hp, rfl⟩
    refine ⟨⟨show dist (z + r • p.1) z < r * ρ by
        rw [hdist]; exact mul_lt_mul_of_pos_left (by simpa using hp.1.1) hr,
      lt_add_of_pos_right _ (mul_pos (sq_pos_of_pos hr) hp.1.2.1),
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hp.1.2.2 (sq_nonneg r))⟩, ?_⟩
    have hlow : ℓ⁻¹ * u (Φ p).1 (Φ p).2 ≤ M := hp.2
    rw [inv_mul_eq_div] at hlow
    exact ((div_le_iff₀ hℓ).mp hlow).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hℓ.le)
  have hmeasure : r ^ (n + 2) * volume.real S ≤
      volume.real ((ball z (r * ρ) ×ˢ Ioc s (s + r ^ 2 * ε)) ∩
        {p | u p.1 p.2 ≤ max 2 M * ℓ}) := by
    rw [← volume_real_image_space_time_dilation z s hr.le]
    exact measureReal_mono hsubset
      ((isBounded_ball.prod (isBounded_Ioc _ _)).subset inter_subset_left).measure_lt_top.ne
  calc _ ≤ r ^ (n + 2) * (D * volume.real S) := by gcongr
    _ = D * (r ^ (n + 2) * volume.real S) := by ring
    _ ≤ _ := by gcongr

end ParabolicHarnack
