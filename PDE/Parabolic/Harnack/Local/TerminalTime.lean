/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Harnack.Local.ScaledClassical
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Local Harnack comparison through the terminal time

The earlier comparison interval leaves room to move the later time from below
without changing the radius or the constant. Continuity through the terminal
time therefore suffices; the equation and derivative identities are used only
in the open time interval.
-/

@[expose] public noncomputable section

namespace ParabolicHarnack

open PDE.Analysis ParabolicMaximum Set Metric Filter
open scoped RealInnerProductSpace Topology

variable {n : ℕ}

/-- A forward local comparison valid up to the terminal time. The time lag is
`(129 / 2) r²`, and all differentiation takes place strictly before `T`. -/
theorem exists_forward_comparison_of_space_time_derivatives
    {α τ B K : ℝ} (hα : 0 < α) (hτ : 0 ≤ τ) (hB : 0 ≤ B) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ) (d : ℝ^n → ℝ → ℝ^n)
        (c : ℝ^n → ℝ → ℝ) (U : Set (ℝ^n)) (ℓ T : ℝ),
        let D := U ×ˢ Ioo ℓ T
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
          ContinuousOn (Function.uncurry u) (U ×ˢ Ioc ℓ T) →
          ContinuousOn Dx D → ContinuousOn Dt D → ContinuousOn Dxx D →
          (∀ p ∈ D, HasFDerivAt (fun x ↦ u x p.2) (Dx p) p.1) →
          (∀ p ∈ D, HasFDerivAt (fun x ↦ Dx (x, p.2)) (Dxx p) p.1) →
          (∀ p ∈ D, HasDerivAt (u p.1) (Dt p) p.2) →
          (∀ p ∈ D, 0 ≤ u p.1 p.2) →
          (∀ p ∈ D, matrixParabolicOperator a d c u p.1 p.2 = 0) →
          ∀ (x y : ℝ^n) (r s : ℝ), 0 < r → r ≤ 1 →
            ball x (13 * r) ⊆ U → dist x y ≤ r → ℓ < s - 2 * r ^ 2 →
            s + (129 / 2) * r ^ 2 ≤ T →
            u x s ≤ C * u y (s + (129 / 2) * r ^ 2) := by
  obtain ⟨C, hC, hscaled⟩ :=
    exists_scaled_comparison_of_space_time_derivatives (n := n) hα hτ hB hK
  refine ⟨C, hC, ?_⟩
  intro a d c U ℓ T D hacont ha hell htrace hdrift hpotential u Dx Dt Dxx
    hu hDx hDt hDxx hd hdd ht hnonneg hsol x y r s hr hr₁ hball hxy hstart hend
  have hr₂ : 0 < r ^ 2 := sq_pos_of_pos hr
  let q := s + (129 / 2) * r ^ 2
  have hq : ℓ < q := by dsimp only [q]; linarith
  have hyU : y ∈ U := by
    apply hball
    rw [mem_ball, dist_comm]
    exact hxy.trans_lt (by linarith)
  have hycont : ContinuousWithinAt (u y) (Ioc ℓ T) q := by
    have h := hu.comp (f := fun t : ℝ ↦ (y, t))
      (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht ↦ ⟨hyU, ht⟩)
    exact h q ⟨hq, hend⟩
  have htend : Tendsto (fun v : ℝ ↦ C * u y v) (𝓝[<] q) (𝓝 (C * u y q)) :=
    tendsto_const_nhds.mul
      (hycont.mono_of_mem_nhdsWithin (Ioc_mem_nhdsLT_of_mem ⟨hq, hend⟩))
  apply ge_of_tendsto htend
  filter_upwards [Ioo_mem_nhdsLT (show q - r ^ 2 / 2 < q by linarith)] with v hv
  let w := v - 64 * r ^ 2
  have hwv : w + 64 * r ^ 2 = v := sub_add_cancel _ _
  have hvT : v < T := hv.2.trans_le hend
  have htime : s ∈ Icc (w - r ^ 2 / 2) w := by
    have hvlo := hv.1
    have hvhi := hv.2
    dsimp only [q] at hvlo hvhi
    dsimp only [w]
    constructor <;> linarith
  have hsub : ball x (13 * r) ×ˢ Ioo (w - 2 * r ^ 2) T ⊆ D := by
    intro p hp
    refine ⟨hball hp.1, ?_, hp.2.2⟩
    have hlo := hp.2.1
    linarith [htime.2]
  have hcompare := hscaled a d c x w r T hr hr₁ (by rwa [hwv])
    (hacont.mono hsub) (fun p hp ↦ ha p (hsub hp))
    (fun p hp ↦ hell p (hsub hp)) (fun p hp ↦ htrace p (hsub hp))
    (fun p hp ↦ hdrift p (hsub hp)) (fun p hp ↦ hpotential p (hsub hp))
    u Dx Dt Dxx (hDx.mono hsub) (hDt.mono hsub) (hDxx.mono hsub)
    (fun p hp ↦ hd p (hsub hp)) (fun p hp ↦ hdd p (hsub hp))
    (fun p hp ↦ ht p (hsub hp)) (fun p hp ↦ hnonneg p (hsub hp))
    (fun p hp ↦ hsol p (hsub hp)) x (mem_closedBall_self (by positivity)) s htime y
    (by simpa only [mem_closedBall, dist_comm] using hxy)
  simpa only [hwv] using hcompare

end ParabolicHarnack
