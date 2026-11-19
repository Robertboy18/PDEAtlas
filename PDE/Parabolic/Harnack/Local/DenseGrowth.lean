/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Harnack.Local.BoxDensity
public import PDE.Parabolic.MaximumPrinciple.Barrier.StationaryComparison
import CAS.ExactTactic

/-!
# Persistence of dense-box growth

A dense early superlevel gives a lower bound on the later half-ball by the
contact estimate. Stationary comparison retains a fixed fraction on its
inner half for any prescribed additional number of parabolic time units.
The density and initial time scale are chosen before the retention duration.
-/

@[expose] public noncomputable section

namespace ParabolicHarnack

open PDE.Analysis ParabolicMaximum BoxIntegral Set Metric MeasureTheory
open scoped RealInnerProductSpace ENNReal

variable {n : ℕ}

/-- A dense early box forces a lower bound on a later closed cylinder.
The density threshold and early time scale do not depend on the length of
that later cylinder; the required level ratio may depend on it. -/
theorem exists_box_persistent_growth
    {R α τ B : ℝ} (hRbox : (n : ℝ) + 1 ≤ R)
    (hα : 0 < α) (hτ : 0 ≤ τ) (hB : 0 ≤ B) (hshort : 1 < R ^ 2 / 8) :
    ∃ δ ε : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < ε ∧ ε ≤ 1 / 4 ∧
      ∀ H : ℝ, 0 < H → ∃ M : ℝ, 2 ≤ M ∧
        ∀ (K : Box (Fin (n + 1))) (j : Fin (n + 1)) (r : ℝ),
          0 < r → r ≤ 1 →
          (∀ i, (K.face j).upper i - (K.face j).lower i = 2 * r) →
          K.upper j - K.lower j = ε * r ^ 2 →
          ∀ (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ) (d : ℝ^n → ℝ → ℝ^n),
            let z := euclideanBoxCenter (K.face j)
            let s := K.lower j
            (∀ p ∈ ball z (r * R) ×ˢ Ioc s (s + r ^ 2 * (1 + H)),
              (a p.1 p.2).PosSemidef) →
            (∀ p ∈ ball z (r * R) ×ˢ Ioc s (s + r ^ 2 * (1 + H)), ∀ v : ℝ^n,
              α * ‖v‖ ^ 2 ≤ ⟪v, (a p.1 p.2).toEuclideanLin v⟫) →
            (∀ p ∈ ball z (r * R) ×ˢ Ioc s (s + r ^ 2 * (1 + H)),
              (a p.1 p.2).trace ≤ τ) →
            (∀ p ∈ ball z (r * R) ×ˢ Ioc s (s + r ^ 2 * (1 + H)), ‖d p.1 p.2‖ ≤ B) →
            ∀ (u : ℝ^n → ℝ → ℝ) (ℓ : ℝ), 0 < ℓ →
              (∀ p ∈ closedBall z (r * R) ×ˢ Icc s (s + r ^ 2 * (1 + H)),
                ContDiffAt ℝ 2 (Function.uncurry u) p) →
              (∀ p ∈ closedBall z (r * R) ×ˢ Icc s (s + r ^ 2 * (1 + H)),
                0 ≤ u p.1 p.2) →
              (∀ p ∈ ball z (r * R) ×ˢ Ioc s (s + r ^ 2 * (1 + H)),
                0 ≤ matrixParabolicOperator a d (fun _ _ ↦ 0) u p.1 p.2) →
              δ * volume.real (K : Set (Fin (n + 1) → ℝ)) <
                (volume.restrict {x : Fin (n + 1) → ℝ |
                  M * ℓ < u (WithLp.toLp 2 (fun i ↦ x (j.succAbove i))) (x j)}).real K →
              ∀ q ∈ Icc (s + r ^ 2) ((s + r ^ 2) + r ^ 2 * H),
                ∀ x ∈ closedBall z (r * (R / 2) / 2), ℓ < u x q := by
  have hR : 0 < R := by linarith
  obtain ⟨M₀, δ, ε, σ, hM₀, hδ, hδ₁, hε, hεquarter, hσ, hdensity⟩ :=
    exists_box_superlevel_growth (n := n) hRbox hα hB zero_lt_one hshort
  refine ⟨δ, ε, hδ, hδ₁, hε, hεquarter, fun H hH ↦ ?_⟩
  obtain ⟨γ, hγ, hretain⟩ :=
    exists_uniform_stationary_halfBall_fraction (n := n) (half_pos hR) hH hα hτ hB
  let M := max 2 (2 * M₀ / γ)
  refine ⟨M, le_max_left _ _, ?_⟩
  intro K j r hr hr₁ hside htime a d
  dsimp only
  intro ha hell htrace hdrift u ℓ hℓ hreg hnonneg hsuper hdense
  let z := euclideanBoxCenter (K.face j)
  let s := K.lower j
  let v := fun x : Fin (n + 1) → ℝ ↦
    u (WithLp.toLp 2 (fun i ↦ x (j.succAbove i))) (x j)
  let L := 2 * ℓ / γ
  have hL : 0 < L := div_pos (mul_pos (by norm_num) hℓ) hγ
  have hr₂ : 0 < r ^ 2 := sq_pos_of_pos hr
  have hshortClosed : closedBall z (r * R) ×ˢ Icc s (s + r ^ 2 * 1) ⊆
      closedBall z (r * R) ×ˢ Icc s (s + r ^ 2 * (1 + H)) := fun p hp ↦
    ⟨hp.1, hp.2.1, hp.2.2.trans (by nlinarith only [hH, hr₂])⟩
  have hshortOpen : ball z (r * R) ×ˢ Ioc s (s + r ^ 2 * 1) ⊆
      ball z (r * R) ×ˢ Ioc s (s + r ^ 2 * (1 + H)) := fun p hp ↦
    ⟨hp.1, hp.2.1, hp.2.2.trans (by nlinarith only [hH, hr₂])⟩
  have hinitial : ∀ x₀ ∈ closedBall z (r * (R / 2)), L ≤ u x₀ (s + r ^ 2) := by
    have hlevel : M₀ * L ≤ M * ℓ := calc
      _ = (2 * M₀ / γ) * ℓ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hℓ.le
    have hmono :
        (volume.restrict {x | M * ℓ < v x}).real K ≤
          (volume.restrict {x | M₀ * L < v x}).real K := by
      rw [measureReal_restrict_apply K.measurableSet_coe,
        measureReal_restrict_apply K.measurableSet_coe]
      exact measureReal_mono (fun _ hx ↦ ⟨hx.1, hlevel.trans_lt hx.2⟩)
        (measure_mono inter_subset_left |>.trans_lt (K.measure_coe_lt_top volume)).ne
    have hgrowth := hdensity K j r hr hr₁ hside htime a d
      (fun p hp ↦ ha p (hshortOpen hp)) (fun p hp ↦ hell p (hshortOpen hp))
      (fun p hp ↦ htrace p (hshortOpen hp)) (fun p hp ↦ hdrift p (hshortOpen hp))
      u L hL (fun p hp ↦ hreg p (hshortClosed hp))
      (fun p hp ↦ hnonneg p (hshortClosed hp))
      (fun p hp ↦ (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hσ.le) hL.le).trans
        (mul_nonneg hr₂.le (hsuper p (hshortOpen hp)))) (hdense.trans_le hmono)
    intro x₀ hx₀
    simpa only [mul_one] using (hgrowth x₀ hx₀).le
  have hradius : 2 * (r * (R / 2)) = r * R := by ring
  have hend : (s + r ^ 2) + r ^ 2 * H = s + r ^ 2 * (1 + H) := by ring
  have hstationaryOpen (x : ℝ^n) (hx : x ∈ ball z (2 * (r * (R / 2))))
      (q : ℝ) (hq : q ∈ Ioo (s + r ^ 2) ((s + r ^ 2) + r ^ 2 * H)) :
      (x, q) ∈ ball z (r * R) ×ˢ Ioc s (s + r ^ 2 * (1 + H)) :=
    ⟨by simpa only [hradius] using hx,
      (lt_add_of_pos_right s hr₂).trans hq.1, by simpa only [hend] using hq.2.le⟩
  have hstationaryClosed : closedBall z (2 * (r * (R / 2))) ×ˢ
      Icc (s + r ^ 2) ((s + r ^ 2) + r ^ 2 * H) ⊆
        closedBall z (r * R) ×ˢ Icc s (s + r ^ 2 * (1 + H)) := fun p hp ↦
    ⟨by simpa only [hradius] using hp.1, (le_add_of_nonneg_right hr₂.le).trans hp.2.1,
      by simpa only [hend] using hp.2.2⟩
  have hregOpen (x : ℝ^n) (hx : x ∈ ball z (2 * (r * (R / 2))))
      (q : ℝ) (hq : q ∈ Ioo (s + r ^ 2) ((s + r ^ 2) + r ^ 2 * H)) :=
    hreg (x, q) (hstationaryClosed ⟨ball_subset_closedBall hx, hq.1.le, hq.2.le⟩)
  have hlower : ∀ q ∈ Icc (s + r ^ 2) ((s + r ^ 2) + r ^ 2 * H),
      ∀ x ∈ closedBall z (r * (R / 2) / 2), γ * L ≤ u x q :=
    hretain z (s + r ^ 2) r hr hr₁ a d (fun x hx q hq ↦ ha (x, q) (hstationaryOpen x hx q hq))
      (fun x hx q hq ↦ hell (x, q) (hstationaryOpen x hx q hq))
      (fun x hx q hq ↦ htrace (x, q) (hstationaryOpen x hx q hq))
      (fun x hx q hq ↦ hdrift (x, q) (hstationaryOpen x hx q hq)) u L hL.le
      (fun p hp ↦ (hreg p (hstationaryClosed hp)).continuousAt.continuousWithinAt)
      (fun x hx q hq ↦ (hregOpen x hx q hq).comp x (contDiffAt_id.prodMk contDiffAt_const))
      (fun x hx q hq ↦ ((hregOpen x hx q hq).comp q
        (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by norm_num))
      (fun x hx q hq ↦ hsuper (x, q) (hstationaryOpen x hx q hq))
      (fun x hx q hq ↦ hnonneg (x, q) (hstationaryClosed ⟨hx, hq⟩)) hinitial
  have hγL : γ * L = 2 * ℓ := by
    dsimp only [L]
    clear * - γ ℓ hγ
    cas using hγ.ne'
  exact fun q hq x hx ↦ by linarith [hlower q hq x hx]

end ParabolicHarnack
