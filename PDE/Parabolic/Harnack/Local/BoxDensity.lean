/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Geometry.SpaceTime.Boxes
public import PDE.Analysis.MeasureTheory.Covering.SublevelComplement
public import PDE.Parabolic.Harnack.Local.ScaledGrowth

/-!
# A low-level fraction in parabolic boxes

The local contact estimate supplies a sublevel set in the inscribed spatial
ball during the first short time interval. Identifying that interval with
the time side of a coordinate box gives a fixed fraction of its volume.
Both volumes scale by `r^(n + 2)`, so the fraction is independent of scale.
-/

@[expose] public noncomputable section

namespace ParabolicHarnack

open PDE.Analysis ParabolicMaximum BoxIntegral Set Metric MeasureTheory
open scoped RealInnerProductSpace ENNReal

variable {n : ℕ}

/-- A small value on the later ball forces a uniform sublevel fraction in the
earlier parabolic box. The coefficient bounds determine the constants before
the box, coefficients, supersolution, and level are supplied. -/
theorem exists_box_sublevel_fraction
    {R α τ B b : ℝ} (hR : 0 < R) (hα : 0 < α)
    (hB : 0 ≤ B) (hb : 0 < b) (hshort : b < R ^ 2 / 8) :
    ∃ M η ε σ : ℝ, 2 ≤ M ∧ 0 < η ∧ η ≤ 1 / 2 ∧
      0 < ε ∧ ε ≤ b / 4 ∧ 0 < σ ∧
      ∀ (I : Box (Fin (n + 1))) (j : Fin (n + 1)) (r : ℝ),
        0 < r → r ≤ 1 →
        (∀ i, (I.face j).upper i - (I.face j).lower i = 2 * r) →
        I.upper j - I.lower j = ε * r ^ 2 →
        ∀ (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ) (d : ℝ^n → ℝ → ℝ^n),
          let z := euclideanBoxCenter (I.face j)
          let s := I.lower j
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
              η * volume.real (I : Set (Fin (n + 1) → ℝ)) ≤
                (volume.restrict {x : Fin (n + 1) → ℝ |
                  u (WithLp.toLp 2 (fun i ↦ x (j.succAbove i))) (x j) ≤ M * ℓ}).real I := by
  obtain ⟨M, D, ε, σ, hM, hD, hε, hεb, hσ, hgrowth⟩ :=
    exists_scaled_sublevel_measure_bound (n := n) hR zero_lt_one hα hB hb hshort
  let A := volume.real (closedBall (0 : ℝ^n) (R / 2) ×ˢ Icc (b / 4) (b / 2))
  have hA : 0 < A := by
    apply ENNReal.toReal_pos
    · rw [Measure.volume_eq_prod, Measure.prod_prod]
      exact mul_ne_zero (measure_closedBall_pos volume 0 (half_pos hR)).ne'
        (by rw [Real.volume_Icc]; exact (ENNReal.ofReal_pos.mpr (by linarith)).ne')
    · exact ((isCompact_closedBall (0 : ℝ^n) (R / 2)).prod isCompact_Icc).measure_lt_top.ne
  let η := min (1 / 2) (A / (D * (2 ^ n * ε)))
  have hden : 0 < D * (2 ^ n * ε) := mul_pos hD (mul_pos (by positivity) hε)
  have hη : 0 < η := lt_min (by norm_num) (div_pos hA hden)
  refine ⟨M, η, ε, σ, hM, hη, min_le_left _ _, hε, hεb, hσ, ?_⟩
  intro I j r hr hr₁ hside htime a d
  dsimp only
  intro ha hell htrace hdrift u ℓ hℓ hreg hnonneg hsuper x₀ hx₀ hsmall
  let z := euclideanBoxCenter (I.face j)
  let s := I.lower j
  have h := hgrowth a d z s r hr hr₁ ha hell htrace hdrift u ℓ hℓ
    hreg hnonneg hsuper x₀ hx₀ hsmall
  simp only [mul_one] at h
  let S := (I : Set (Fin (n + 1) → ℝ)) ∩
    {x | u (WithLp.toLp 2 (fun i ↦ x (j.succAbove i))) (x j) ≤ M * ℓ}
  have htime' : s + r ^ 2 * ε = I.upper j := by dsimp [s]; nlinarith [htime]
  have hsubset :
      ((ball z r ×ˢ Ioc s (s + r ^ 2 * ε)) ∩ {p | u p.1 p.2 ≤ M * ℓ}) ⊆
        (fun p : ℝ^n × ℝ ↦ j.insertNth p.2 (WithLp.ofLp p.1)) ⁻¹' S := by
    intro p hp
    refine ⟨?_, ?_⟩
    · apply ball_prod_Ioc_subset_insertNth_ofLp_box I j hside
      simpa only [htime'] using hp.1
    · simpa only [mem_ofPred_eq, Fin.insertNth_apply_succAbove, Fin.insertNth_apply_same,
        WithLp.toLp_ofLp] using hp.2
  have hvolume :
      volume.real ((ball z r ×ˢ Ioc s (s + r ^ 2 * ε)) ∩ {p | u p.1 p.2 ≤ M * ℓ}) ≤
        volume.real S := by
    have hfinite : volume S ≠ ∞ :=
      (measure_mono inter_subset_left |>.trans_lt (I.measure_coe_lt_top volume)).ne
    have hpre := volume_preimage_insertNth_ofLp j S
    rw [← hpre] at hfinite
    simpa only [measureReal_def, hpre] using measureReal_mono hsubset hfinite
  have hmass : r ^ (n + 2) * A ≤ D * volume.real S :=
    h.trans (mul_le_mul_of_nonneg_left hvolume hD.le)
  have hηbound : η * (D * (2 ^ n * ε)) ≤ A :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  have hscaled : D * (η * ((2 * r) ^ n * (ε * r ^ 2))) ≤ r ^ (n + 2) * A := by
    calc
      _ = r ^ (n + 2) * (η * (D * (2 ^ n * ε))) := by rw [pow_add, mul_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hηbound (pow_nonneg hr.le _)
  rw [volume_real_box_space_time_of_side I j hside htime,
    measureReal_restrict_apply I.measurableSet_coe]
  exact (mul_le_mul_iff_right₀ hD).mp (hscaled.trans hmass)

/-- A dense high superlevel in an early box forces a pointwise lower bound
throughout the later ball. A small negative residual is still permitted. -/
theorem exists_box_superlevel_growth
    {R α τ B b : ℝ} (hRbox : (n : ℝ) + 1 ≤ R) (hα : 0 < α)
    (hB : 0 ≤ B) (hb : 0 < b) (hshort : b < R ^ 2 / 8) :
    ∃ M δ ε σ : ℝ, 2 ≤ M ∧ 0 < δ ∧ δ < 1 ∧
      0 < ε ∧ ε ≤ b / 4 ∧ 0 < σ ∧
      ∀ (I : Box (Fin (n + 1))) (j : Fin (n + 1)) (r : ℝ),
        0 < r → r ≤ 1 →
        (∀ i, (I.face j).upper i - (I.face j).lower i = 2 * r) →
        I.upper j - I.lower j = ε * r ^ 2 →
        ∀ (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ) (d : ℝ^n → ℝ → ℝ^n),
          let z := euclideanBoxCenter (I.face j)
          let s := I.lower j
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
            δ * volume.real (I : Set (Fin (n + 1) → ℝ)) <
              (volume.restrict {x : Fin (n + 1) → ℝ |
                M * ℓ < u (WithLp.toLp 2 (fun i ↦ x (j.succAbove i))) (x j)}).real I →
            ∀ x₀ ∈ closedBall z (r * (R / 2)), ℓ < u x₀ (s + r ^ 2 * b) := by
  have hR : 0 < R := by linarith
  obtain ⟨M, η, ε, σ, hM, hη, hηhalf, hε, hεb, hσ, hdensity⟩ :=
    exists_box_sublevel_fraction (n := n) hR hα hB hb hshort
  refine ⟨M, 1 - η, ε, σ, hM, by linarith, by linarith, hε, hεb, hσ, ?_⟩
  intro I j r hr hr₁ hside htime a d
  dsimp only
  intro ha hell htrace hdrift u ℓ hℓ hreg hnonneg hsuper hdense x₀ hx₀
  by_contra hnot
  have hlo := hdensity I j r hr hr₁ hside htime a d ha hell htrace hdrift
    u ℓ hℓ hreg hnonneg hsuper x₀ hx₀ (le_of_not_gt hnot)
  have hdecode : Continuous (fun x : Fin (n + 1) → ℝ ↦
      (WithLp.toLp 2 (fun i ↦ x (j.succAbove i)), x j)) :=
    ((PiLp.continuous_toLp 2 (fun _ : Fin n ↦ ℝ)).comp
      (continuous_pi fun i ↦ continuous_apply (j.succAbove i))).prodMk
        (continuous_apply j)
  have hvcont : ContinuousOn
      (fun x : Fin (n + 1) → ℝ ↦
        u (WithLp.toLp 2 (fun i ↦ x (j.succAbove i))) (x j)) I.Icc :=
    ContinuousOn.comp
      (fun p hp ↦ (hreg p hp).continuousAt.continuousWithinAt) hdecode.continuousOn
      (mapsTo_box_space_time_cylinder I j hr.le hRbox (by linarith only [hεb, hb])
        hside htime)
  exact (not_lt_of_ge
    (measure_restrict_superlevel_le_of_sublevel volume I hvcont (M * ℓ) η hlo)) hdense

end ParabolicHarnack
