/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.SpaceTime.Regularity
public import PDE.Analysis.Calculus.SpaceTime.Averaging.Regularity
public import PDE.Parabolic.Harnack.Local.Residual
public import PDE.Parabolic.MaximumPrinciple.MatrixOperator.Averaging
import CAS.ExactTactic

/-!
# Local Harnack comparison for C²,¹ fields

Forward time averages have joint C² regularity and approximate the parabolic
residual uniformly on the comparison cylinder. The comparison with a residual
error passes to the original field as the averaging width tends to zero.
Only the original first time derivative and first two spatial derivatives
occur in the hypotheses.
-/

@[expose] public noncomputable section

namespace ParabolicHarnack

open PDE.Analysis ParabolicMaximum MeasureTheory Set Metric
open scoped RealInnerProductSpace Interval

variable {n : ℕ}

/-- The local comparison for C²,¹ data with a signed potential.
The principal coefficient is continuous, while drift and potential need only
the displayed bounds. The constant precedes all coefficients and field data,
and is independent of the positive time margin beyond the comparison time. -/
theorem exists_local_comparison_of_space_time_derivatives
    {α τ B K : ℝ} (hα : 0 < α) (hτ : 0 ≤ τ) (hB : 0 ≤ B) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ b : ℝ, 64 < b →
      ∀ (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ) (d : ℝ^n → ℝ → ℝ^n)
        (c : ℝ^n → ℝ → ℝ),
        let D := ball (0 : ℝ^n) 13 ×ˢ Ioo (-2) b
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
          ∀ x ∈ closedBall (0 : ℝ^n) (1 / 2), ∀ t ∈ Icc (-1 / 2) 0,
            ∀ y ∈ closedBall (0 : ℝ^n) 1, u x t ≤ C * u y 64 := by
  obtain ⟨C, hC, hcompare⟩ := exists_local_comparison_with_residual (n := n) hα hτ hB hK
  refine ⟨C, hC, ?_⟩
  intro b hb a d c D hacont ha hell htrace hdrift hpotential u Dx Dt Dxx
    hDx hDt hDxx hd hdd ht hnonneg hsol x hx t hxt y hy
  let σ := (b - 64) / 2
  have hσ : 0 < σ := div_pos (sub_pos.mpr hb) (by norm_num)
  have hσb : 64 + 2 * σ = b := by dsimp only [σ]; cas
  let Q := closedBall (0 : ℝ^n) 12 ×ˢ Icc (-1 : ℝ) 64
  let S := closedBall (0 : ℝ^n) 12 ×ˢ Icc (-1 : ℝ) (64 + σ)
  have hS : IsCompact S := (isCompact_closedBall _ _).prod isCompact_Icc
  have hSD : S ⊆ D := fun p hp ↦ ⟨closedBall_subset_ball (by norm_num : (12 : ℝ) < 13) hp.1,
    (by norm_num : (-2 : ℝ) < -1).trans_le hp.2.1, hp.2.2.trans_lt (by linarith)⟩
  have hQS : Q ⊆ S :=
    prod_mono Subset.rfl (Icc_subset_Icc le_rfl (le_add_of_nonneg_right hσ.le))
  have hQD : Q ⊆ D := hQS.trans hSD
  have huone : ContDiffOn ℝ 1 (Function.uncurry u) D := by
    simpa only [isOpen_Ioo.interior_eq] using
      (contDiffOn_one_of_space_time_derivatives isOpen_ball hDx hDt hd
        (fun p hp ↦ (ht p hp).hasDerivWithinAt))
  have hsumcont : ContinuousOn
      (fun p : ℝ^n × ℝ ↦ ∑ i : Fin n, ∑ j : Fin n, |a p.1 p.2 i j|) S :=
    continuousOn_finsetSum _ fun i _ ↦ continuousOn_finsetSum _ fun j _ ↦
      (continuousOn_pi.mp (continuousOn_pi.mp (hacont.mono hSD) i) j).abs
  obtain ⟨A, hA⟩ := hS.exists_bound_of_continuousOn hsumcont
  have hAbound (p : ℝ^n × ℝ) (hp : p ∈ S) :
      (∑ i : Fin n, ∑ j : Fin n, |a p.1 p.2 i j|) ≤ max A 0 :=
    (Real.le_norm_self _).trans ((hA p hp).trans (le_max_left _ _))
  have hpointx : (x, t) ∈ Q :=
    ⟨closedBall_subset_closedBall (by norm_num : (1 / 2 : ℝ) ≤ 12) hx,
      ⟨(by norm_num : (-1 : ℝ) ≤ -1 / 2).trans hxt.1, hxt.2.trans (by norm_num)⟩⟩
  have hpointy : (y, (64 : ℝ)) ∈ Q :=
    ⟨closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 12) hy, by norm_num⟩
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  let η := ε / (2 * C + 1)
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨δr, hδr, hres⟩ := exists_timeAverage_residual_sub_le
    isOpen_ball isOpen_Ioo hS hSD a d c (le_max_right A 0) hB hK hAbound
    (fun p hp ↦ hdrift p (hSD hp)) (fun p hp ↦ hpotential p (hSD hp))
    huone.continuousOn hDx hDt hDxx hd hdd ht hη
  obtain ⟨δu, hδu, hvalue⟩ := exists_timeAverage_norm_sub_le
    (f := Function.uncurry u) hS (huone.continuousOn.mono hSD) hη
  obtain ⟨h, hh, hsmall⟩ := exists_between (lt_min (lt_min hδr hδu) hσ)
  obtain ⟨⟨hr, hval⟩, hhσ⟩ : (h < δr ∧ h < δu) ∧ h < σ := by simpa only [lt_min_iff] using hsmall
  have hsegment (r : ℝ) (hrJ : r ∈ Ioo (-2 : ℝ) (64 + σ)) :
      uIcc r (r + h) ⊆ Ioo (-2 : ℝ) b := by
    rw [uIcc_of_le (le_add_of_nonneg_right hh.le)]
    exact fun s hs ↦ ⟨hrJ.1.trans_le hs.1, hs.2.trans_lt (by linarith [hrJ.2])⟩
  have hQJ (p : ℝ^n × ℝ) (hp : p ∈ Q) :
      p ∈ ball (0 : ℝ^n) 13 ×ˢ Ioo (-2 : ℝ) (64 + σ) :=
    ⟨(hQD hp).1, ⟨(hQD hp).2.1, hp.2.2.trans_lt (lt_add_of_pos_right _ hσ)⟩⟩
  have hwindow (p : ℝ^n × ℝ) (hp : p ∈ Q) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      (p.1, p.2 + h * s) ∈ S := by
    refine ⟨hp.1, ⟨hp.2.1.trans (le_add_of_nonneg_right (mul_nonneg hh.le hs.1)), ?_⟩⟩
    linarith [mul_le_of_le_one_right hh.le hs.2, hp.2.2]
  let v : ℝ^n → ℝ → ℝ := fun z r ↦ ∫ s in (0 : ℝ)..1, u z (r + h * s)
  have hvreg : ∀ p ∈ Q, ContDiffAt ℝ 2 (Function.uncurry v) p := fun p hp ↦
    (contDiffOn_two_timeAverage isOpen_ball isOpen_Ioo isOpen_Ioo hh huone hDx hDxx hd hdd
      hsegment).contDiffAt ((isOpen_ball.prod isOpen_Ioo).mem_nhds (hQJ p hp))
  have hvnonneg : ∀ p ∈ Q, 0 ≤ v p.1 p.2 := fun p hp ↦
    intervalIntegral.integral_nonneg zero_le_one
      fun s hs ↦ hnonneg (p.1, p.2 + h * s) (hSD (hwindow p hp s hs))
  have hvres : ∀ p ∈ Q, |matrixParabolicOperator a d c v p.1 p.2| ≤ η := fun p hp ↦ by
    simpa only [hsol p (hQD hp), sub_zero] using
      hres h hh hr p (hQS hp) (hsegment p.2 (hQJ p hp).2) (hwindow p hp)
  have havalue (p : ℝ^n × ℝ) (hp : p ∈ Q) :
      |v p.1 p.2 - u p.1 p.2| ≤ η := by
    simpa only [Real.norm_eq_abs, Function.uncurry, v] using
      hvalue p (hQS hp) h (by rwa [abs_of_pos hh]) (hwindow p hp)
  have hlocal := hcompare a d c (fun p hp ↦ ha p (hQD hp))
    (fun p hp ↦ hell p (hQD hp)) (fun p hp ↦ htrace p (hQD hp))
    (fun p hp ↦ hdrift p (hQD hp)) (fun p hp ↦ hpotential p (hQD hp))
    v η hη hvreg hvnonneg hvres x hx t hxt y hy
  have hvx := (abs_le.mp (havalue (x, t) hpointx)).1
  have hvy := (abs_le.mp (havalue (y, 64) hpointy)).2
  have hlast : (2 * C + 1) * η = ε := mul_div_cancel₀ ε (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left hvy hC.le]

end ParabolicHarnack
