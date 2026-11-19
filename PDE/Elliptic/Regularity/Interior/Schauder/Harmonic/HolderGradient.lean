/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.Schauder.Harmonic.MeanSquareEstimate
import PDE.Elliptic.Regularity.Interior.Schauder.Campanato.MeanSquare
import PDE.Elliptic.Regularity.Interior.Schauder.Campanato.Quadratic

/-!
# Hölder gradients of weak Poisson solutions

The quantitative mean-square estimate supplies the Campanato hypothesis for
each weak gradient coordinate. Zero extension as an `L²` function permits use
of the representative theorem. Open and closed ball averages agree
because Euclidean spheres have zero volume.

Thus Hölder divergence forcing gives a Hölder gradient representative from
an `H¹` weak solution, with no gradient continuity or boundedness seed.
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set
open scoped Sobolev InnerProductSpace NNReal

namespace SobolevSpace.GraphSpace

open PDE.Elliptic.Regularity.Campanato

variable {n : ℕ} [Fact (0 < n)]

/-- Interior gradient Hölder regularity for a weak Poisson solution.
For every `0 < γ < 1`, Hölder divergence forcing of exponent `γ` yields a
representative of the same exponent for each weak gradient coordinate. -/
theorem exists_holder_gradient_of_dirichlet_eq_divergence
    {Ω : Set ℝ^n} (hΩ : IsOpen Ω) (U : H¹(Ω))
    (F : Fin n → DerivLp n 2 Ω) (f : Fin n → ℝ^n → ℝ) {M γ : ℝ≥0}
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hf : ∀ j, HolderOnWith M γ (f j) Ω)
    (hF : ∀ j, (F j : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] f j)
    (hweak : ∀ t : H¹₀(Ω),
      (∑ j, ⟪wkpCoordinateCLM (singleDerivIndex n j) U, derivCoordCLM j t⟫_ℝ) =
        ∑ j, ⟪F j, derivCoordCLM j t⟫_ℝ)
    {z : ℝ^n} {R : ℝ} (hR : 0 < R) (hsub : ball z R ⊆ Ω) (i : Fin n) :
    ∃ (g : ℝ^n → ℝ) (K : ℝ≥0), Continuous g ∧
      HolderOnWith K γ g (ball z (R / 32)) ∧
      g =ᵐ[volume.restrict (ball z (R / 32))]
        wkpCoordinateCLM (singleDerivIndex n i) U := by
  classical
  let : NeZero n := ⟨(Fact.out : 0 < n).ne'⟩
  obtain ⟨C, hC, hestimate⟩ := exists_meanSquare_gradient_estimate (n := n) hγ1
  let v : ℝ^n → ℝ := Ω.indicator (wkpCoordinateCLM (singleDerivIndex n i) U)
  have hv : MemLp v 2 volume :=
    (memLp_indicator_iff_restrict hΩ.measurableSet.nullMeasurableSet).mpr (Lp.memLp _)
  have hrep {x : ℝ^n} {s : ℝ} (hxs : ball x s ⊆ Ω) :
      v =ᵐ[volume.restrict (ball x s)] wkpCoordinateCLM (singleDerivIndex n i) U :=
    (ae_restrict_mem isOpen_ball.measurableSet).mono
      (fun y hy ↦ indicator_of_mem (hxs hy) _)
  have hav {x : ℝ^n} {s : ℝ} (hxs : ball x s ⊆ Ω) :
      (⨍ y in ball x s, ‖v y - ⨍ w in ball x s, v w‖ ^ 2) =
      ⨍ y in ball x s, ‖wkpCoordinateCLM (singleDerivIndex n i) U y -
        ⨍ w in ball x s, wkpCoordinateCLM (singleDerivIndex n i) U w‖ ^ 2 := by
    rw [average_congr (hrep hxs)]
    exact average_congr ((hrep hxs).fun_comp (fun t ↦ ‖t -
      ⨍ w in ball x s, wkpCoordinateCLM (singleDerivIndex n i) U w‖ ^ 2))
  let ρ := R / 4
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  let I := ∫ y, ‖v y‖ ^ 2
  have hI : 0 ≤ I := integral_nonneg (fun _ ↦ sq_nonneg _)
  let E := (volume.real (ball z ρ))⁻¹ * I + (M * ρ ^ (γ : ℝ)) ^ 2
  have hE : 0 ≤ E := by dsimp [E]; positivity
  let P := C / ρ ^ (2 * (γ : ℝ)) * E
  have hP : 0 ≤ P := by dsimp [P]; positivity
  let N : ℝ≥0 := ⟨Real.sqrt P, Real.sqrt_nonneg _⟩
  have hN : (N : ℝ) ^ 2 = P := Real.sq_sqrt hP
  have hcamp (x : ℝ^n) (hx : x ∈ ball z ρ) (s : ℝ) (hs : 0 < s) (hsρ : s ≤ ρ) :
      (⨍ y in closedBall x s, ‖v y - ⨍ w in closedBall x s, v w‖ ^ 2) ≤
        (N * s ^ (γ : ℝ)) ^ 2 := by
    have hxsub : ball x ρ ⊆ Ω :=
      (ball_subset_ball' (by linarith [mem_ball.mp hx, show ρ = R / 4 from rfl])).trans hsub
    have hxsmall : ball x s ⊆ Ω := (ball_subset_ball hsρ).trans hxsub
    have hdec := hestimate hΩ U F f M hf hF hweak x ρ hρ hxsub s hs hsρ i
    rw [← hav hxsmall, ← hav hxsub] at hdec
    have hmin := setAverage_norm_sub_average_sq_le (s := ball x ρ)
      (hv.mono_measure Measure.restrict_le_self) 0
    simp only [sub_zero] at hmin
    have hvol : volume.real (ball x ρ) = volume.real (ball z ρ) := by
      rw [Measure.addHaar_real_ball_center volume x, Measure.addHaar_real_ball_center volume z]
    have hmean : (⨍ y in ball x ρ, ‖v y‖ ^ 2) ≤ (volume.real (ball z ρ))⁻¹ * I := by
      rw [setAverage_eq, smul_eq_mul, hvol]
      exact mul_le_mul_of_nonneg_left
        (setIntegral_le_integral hv.norm.integrable_sq
          (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _))
        (inv_nonneg.mpr measureReal_nonneg)
    have houter := hmin.trans hmean
    have hballs : closedBall x s =ᵐ[volume] ball x s :=
      (ae_eq_of_subset_of_measure_ge ball_subset_closedBall
        (Measure.addHaar_closedBall_eq_addHaar_ball volume x s).le
        isOpen_ball.measurableSet.nullMeasurableSet measure_closedBall_lt_top.ne).symm
    simp_rw [setAverage_congr hballs]
    calc
      _ ≤ C * (s / ρ) ^ (2 * (γ : ℝ)) *
          ((volume.real (ball z ρ))⁻¹ * I + (M * ρ ^ (γ : ℝ)) ^ 2) :=
        hdec.trans (mul_le_mul_of_nonneg_left
          (add_le_add houter le_rfl) (by positivity))
      _ = _ := by
        have hp := Real.rpow_mul_natCast hs.le (γ : ℝ) 2
        norm_num only [Nat.cast_ofNat] at hp
        rw [mul_pow (N : ℝ) (s ^ (γ : ℝ)), hN, ← hp,
          mul_comm (γ : ℝ) 2, Real.div_rpow hs.le hρ.le]
        dsimp only [P, E]
        ring
  obtain ⟨K, _, hholder⟩ := exists_holderOnWith_representative_of_meanSquare (n := n) hγ0
  obtain ⟨g, hg, hgHolder, hgAE⟩ := hholder v N
    (fun _ _ ↦ hv.mono_measure Measure.restrict_le_self) z ρ hρ hcamp
  have heq : ρ / 8 = R / 32 := by dsimp only [ρ]; ring
  rw [heq] at hgHolder hgAE
  refine ⟨g, K * N, hg, hgHolder, hgAE.trans ?_⟩
  exact hrep ((ball_subset_ball (by linarith : R / 32 ≤ R)).trans hsub)

end SobolevSpace.GraphSpace
