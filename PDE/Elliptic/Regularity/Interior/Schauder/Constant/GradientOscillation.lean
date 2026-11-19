/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.Schauder.Constant.BallOscillation
import PDE.Elliptic.Regularity.Interior.Schauder.Campanato.BallEnergy
import PDE.Elliptic.Regularity.Coefficients.Restriction

/-!
# Quadratic gradient oscillation for constant coefficient comparisons

Interior H² regularity and differentiation construct homogeneous weak
equations for the gradient coordinates. Applying scalar oscillation decay to
those equations gives quadratic gradient oscillation from raw H¹ data.
The outer gradient energy can be centred at any constant.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric SobolevSpace
open PDE.Elliptic.Regularity.Campanato
open scoped NNReal Sobolev ENNReal

namespace SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)]

/-- The weak gradient of a constant coefficient H¹ solution has
quadratic mean oscillation decay, uniformly in the matrix and the ball. -/
theorem exists_gradient_oscillation_of_constant_coefficients
    {q : ℝ≥0∞} (hq2 : 2 < q)
    (hq : q ≤ (if 2 < n then Inequalities.pStar n 2 else 4 : ℝ≥0)) {α Λ : ℝ}
    (hα : 0 < α) (hΛ : 0 ≤ Λ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (z : ℝ^n) (R : ℝ), 0 < R →
      ∀ (A : Fin n → Fin n → DerivLp n ∞ (ball z R))
        (a : Fin n → Fin n → ℝ),
        (∀ i j, (A i j : ℝ^n → ℝ) =ᵐ[domainMeasure n (ball z R)]
          fun _ ↦ a i j) →
        (∀ i j, ‖A i j‖ ≤ Λ) → AEUniformlyElliptic A α →
      ∀ (u : H¹(ball z R)), IsInteriorWeakDivergenceSolution A 0 u →
      ∀ (i : Fin n) (c r : ℝ), 0 < r → r ≤ R / 8 →
        (⨍ x in ball z r, ‖wkpCoordinateCLM (singleDerivIndex n i) u x -
          ⨍ y in ball z r, wkpCoordinateCLM (singleDerivIndex n i) u y‖ ^ 2) ≤
          C * (r / R) ^ 2 *
            ⨍ x in ball z R, ‖wkpCoordinateCLM (singleDerivIndex n i) u x - c‖ ^ 2 := by
  obtain ⟨D, hD, hdecay⟩ :=
    exists_ball_oscillation_of_constant_coefficients hq2 hq hα hΛ
  refine ⟨4 * D * (2 : ℝ) ^ n, by positivity, ?_⟩
  intro z R hR A a hrep hAΛ hA u hu i c r hr hrR
  have hhalf : 0 < R / 2 := by positivity
  have hsub : closure (ball z (R / 2)) ⊆ ball z R :=
    closure_ball_subset_closedBall.trans (closedBall_subset_ball (by linarith))
  let hinner := subset_closure.trans hsub
  obtain ⟨W, hW, hlinear⟩ := exists_interior_gradient_solutions_of_constant_coefficients
    A a hrep hA u hu isOpen_ball isBounded_ball.isCompact_closure hsub
  let B (j k : Fin n) : DerivLp n ∞ (ball z (R / 2)) :=
    restrictDerivLp hinner (A j k)
  have hb (j k : Fin n) : (B j k : ℝ^n → ℝ)
      =ᵐ[domainMeasure n (ball z (R / 2))] fun _ ↦ a j k :=
    (restrictDerivLp_apply_ae hinner (A j k)).trans
      ((hrep j k).filter_mono (ae_mono (domainMeasure_le hinner)))
  have hbase : wkpBaseCoordinateCLM (∂[i] W) =
      wkpCoordinateCLM (singleDerivIndex n i)
        (lowerOrderCLM (by omega : 1 ≤ 2) W) := by
    simp only [wkpBaseCoordinateCLM_apply, partialDerivCLM, derivativeWordCLM_apply,
      derivativeWordIndex_baseIndex, wkpCoordinateCLM_apply, lowerOrderCLM_apply,
      DerivIndex.castOrder_singleDerivIndex]
    rfl
  have hbaseAE : (wkpBaseCoordinateCLM (∂[i] W) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n (ball z (R / 2))]
        wkpCoordinateCLM (singleDerivIndex n i) u := by
    rw [hbase, hW]
    exact restrictCLM_apply_ae isOpen_ball.measurableSet hinner u (singleDerivIndex n i)
  have hsmallAE := hbaseAE.filter_mono (ae_mono (domainMeasure_le
    (ball_subset_ball (show r ≤ R / 2 by linarith))))
  have hosc :
      (⨍ x in ball z r, ‖wkpBaseCoordinateCLM (∂[i] W) x -
        ⨍ y in ball z r, wkpBaseCoordinateCLM (∂[i] W) y‖ ^ 2) =
      ⨍ x in ball z r, ‖wkpCoordinateCLM (singleDerivIndex n i) u x -
        ⨍ y in ball z r, wkpCoordinateCLM (singleDerivIndex n i) u y‖ ^ 2 := by
    rw [average_congr hsmallAE]
    exact average_congr (hsmallAE.fun_comp fun t ↦
      ‖t - ⨍ y in ball z r, wkpCoordinateCLM (singleDerivIndex n i) u y‖ ^ 2)
  have h := hdecay z (R / 2) hhalf B a hb
    (fun j k ↦ (norm_restrictDerivLp_le hinner (A j k)).trans (hAΛ j k))
    (hA.restrict hinner) (∂[i] W) (hlinear i) c r hr (by linarith)
  have henergy :
      (⨍ x in ball z (R / 2), ‖wkpBaseCoordinateCLM (∂[i] W) x - c‖ ^ 2) =
        ⨍ x in ball z (R / 2),
          ‖wkpCoordinateCLM (singleDerivIndex n i) u x - c‖ ^ 2 :=
    average_congr (hbaseAE.fun_comp fun t ↦ ‖t - c‖ ^ 2)
  rw [hosc, henergy] at h
  have : IsFiniteMeasure (volume.restrict (ball z R)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have houter := setAverage_norm_sq_le_of_radius_le hhalf (by linarith : R / 2 ≤ R)
    ((Lp.memLp (wkpCoordinateCLM (singleDerivIndex n i) u)).sub (memLp_const c))
  simp only [Pi.sub_apply, show R / (R / 2) = 2 by field_simp] at houter
  calc
    _ ≤ _ := h
    _ ≤ D * (r / (R / 2)) ^ 2 * ((2 : ℝ) ^ n *
        ⨍ x in ball z R, ‖wkpCoordinateCLM (singleDerivIndex n i) u x - c‖ ^ 2) :=
      by gcongr
    _ = _ := by ring

end SobolevSpace.GraphSpace
