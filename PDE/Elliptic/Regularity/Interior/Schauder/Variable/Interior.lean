/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.Schauder.Variable.HolderGradient
public import PDE.Elliptic.Regularity.Interior.Schauder.Variable.BoundedGradient
import PDE.Elliptic.Regularity.Interior.Schauder.Campanato.MeanSquare
import PDE.Elliptic.Regularity.Interior.Schauder.Campanato.Bounds
import PDE.Elliptic.Regularity.Interior.Schauder.Campanato.Quadratic
import PDE.Analysis.MeasureTheory.Lp.Continuous

/-!
# Interior Schauder regularity for weak divergence equations

For general scalar uniformly elliptic coefficients of Hölder exponent
`0 < γ < 1`, an H¹ solution with Hölder divergence forcing has a locally
Hölder gradient of the same exponent. The first perturbative gain derives
continuous gradient representatives. Their compact local bound then supplies
the full oscillation estimate, so no extra gradient regularity is an input.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric SobolevSpace
open PDE.Elliptic.Regularity.Campanato
open scoped Sobolev ENNReal NNReal InnerProductSpace

namespace SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)]

/-- Interior divergence-form Schauder regularity from an H¹ weak
solution. The derived gradient representatives have the same Hölder exponent
as the coefficients and forcing. Neither gradient boundedness nor continuity
is assumed. -/
theorem exists_holder_gradient_of_holder_coefficients_same_exponent
    {q : ℝ≥0∞} (hq2 : 2 < q)
    (hq : q ≤ (if 2 < n then Inequalities.pStar n 2 else 4 : ℝ≥0)) {α Λ : ℝ}
    (hα : 0 < α) (hΛ : 0 ≤ Λ) {Ω : Set ℝ^n} (hΩ : IsOpen Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (A : Fin n → Fin n → ℝ^n → ℝ) {K M γ : ℝ≥0}
    (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hA : ∀ i j, HolderOnWith K γ (A i j) Ω)
    (hrep : ∀ i j, (a i j : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] A i j)
    (hAbound : ∀ x ∈ Ω, ∀ i j, ‖A i j x‖ ≤ Λ)
    (hell : ∀ x ∈ Ω, ∀ ξ : Fin n → ℝ,
      α * ∑ i, ξ i * ξ i ≤ ∑ i, ∑ j, A i j x * ξ j * ξ i)
    (u : H¹(Ω)) (F : Fin n → DerivLp n 2 Ω) (f : Fin n → ℝ^n → ℝ)
    (hf : ∀ i, HolderOnWith M γ (f i) Ω)
    (hF : ∀ i, (F i : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] f i)
    (hu : ∀ v : H¹₀(Ω),
      interiorVariableCoeffForm (multiplicationCoefficientOperator a) u v =
        ∑ i, ⟪F i, derivCoordCLM i v⟫_ℝ)
    {z : ℝ^n} {R : ℝ} (hR : 0 < R) (hsub : ball z R ⊆ Ω) :
    ∃ r : ℝ, 0 < r ∧ r ≤ R / 32 ∧
      ∀ i : Fin n, ∃ (g : ℝ^n → ℝ) (N : ℝ≥0), Continuous g ∧
        HolderOnWith N γ g (ball z r) ∧
        g =ᵐ[volume.restrict (ball z r)] wkpCoordinateCLM (singleDerivIndex n i) u := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0, Fact.out⟩⟩
  obtain ⟨ρ, hρ, hρR, hfirst⟩ := exists_holder_gradient_of_holder_coefficients
    hq2 hq hα hΛ hΩ a A hγ0 hγ1 hA hrep hAbound hell u F f hf hF hu hR hsub
  choose g N hg hgh hga using hfirst
  obtain ⟨P, hP⟩ := (isCompact_closedBall z (ρ / 2)).exists_bound_of_continuousOn
    (continuous_pi hg).continuousOn
  let B := max 0 P
  have hB : 0 ≤ B := le_max_left _ _
  have hbound (j : Fin n) (x : ℝ^n) (hx : x ∈ closedBall z (ρ / 2)) :
      ‖g j x‖ ≤ B :=
    (norm_le_pi_norm (fun k ↦ g k x) j).trans ((hP x hx).trans (le_max_right _ _))
  obtain ⟨C, hC, hestimate⟩ := exists_meanSquare_gradient_estimate_of_bounded_gradient
    hq2 hq hα hΛ hB (K := K) (M := M) hγ1
  let σ := ρ / 4
  have hσ : 0 < σ := by dsimp [σ]; positivity
  let Q := C / σ ^ (2 * (γ : ℝ)) * (B ^ 2 + σ ^ (2 * (γ : ℝ)))
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  let T : ℝ≥0 := ⟨Real.sqrt Q, Real.sqrt_nonneg _⟩
  have hT : (T : ℝ) ^ 2 = Q := Real.sq_sqrt hQ
  have hρΩ : ball z ρ ⊆ Ω := (ball_subset_ball (by linarith : ρ ≤ R)).trans hsub
  refine ⟨σ / 8, by positivity, by dsimp [σ]; linarith, ?_⟩
  intro i
  have hmem (s : Set ℝ^n) (hs : IsCompact s) : MemLp (g i) 2 (volume.restrict s) :=
    (hg i).continuousOn.memLp_of_subset_isCompact hs hs.measurableSet Subset.rfl
  have hav {x : ℝ^n} {s : ℝ} (hxs : ball x s ⊆ ball z ρ) :
      (⨍ y in ball x s, ‖g i y - ⨍ w in ball x s, g i w‖ ^ 2) =
      ⨍ y in ball x s, ‖wkpCoordinateCLM (singleDerivIndex n i) u y -
        ⨍ w in ball x s, wkpCoordinateCLM (singleDerivIndex n i) u w‖ ^ 2 := by
    have hr := (hga i).filter_mono (ae_mono (Measure.restrict_mono hxs le_rfl))
    rw [average_congr hr]
    exact average_congr (hr.fun_comp (fun t ↦ ‖t -
      ⨍ w in ball x s, wkpCoordinateCLM (singleDerivIndex n i) u w‖ ^ 2))
  have hcamp (x : ℝ^n) (hx : x ∈ ball z σ) (s : ℝ) (hs : 0 < s) (hsσ : s ≤ σ) :
      (⨍ y in closedBall x s, ‖g i y - ⨍ w in closedBall x s, g i w‖ ^ 2) ≤
        (T * s ^ (γ : ℝ)) ^ 2 := by
    have hxclosed : ball x σ ⊆ closedBall z (ρ / 2) := by
      refine (ball_subset_ball' ?_).trans ball_subset_closedBall
      have hx' := mem_ball.mp hx
      dsimp only [σ] at hx' ⊢
      linarith
    have hxρ : ball x σ ⊆ ball z ρ :=
      hxclosed.trans (closedBall_subset_ball (by linarith))
    have hxΩ : x ∈ Ω := (hxρ.trans hρΩ) (mem_ball_self hσ)
    have hxbound (j : Fin n) : ∀ᵐ y ∂volume.restrict (ball x σ),
        ‖wkpCoordinateCLM (singleDerivIndex n j) u y‖ ≤ B := by
      filter_upwards [(hga j).filter_mono
        (ae_mono (Measure.restrict_mono hxρ le_rfl)),
        ae_restrict_mem isOpen_ball.measurableSet] with y hy hymem
      rw [← hy]
      exact hbound j y (hxclosed hymem)
    have hd := hestimate hΩ a A hA hrep u F f hf hF hu x σ hσ (hxρ.trans hρΩ)
      (hAbound x hxΩ) (hell x hxΩ) hxbound s hs hsσ i
    rw [← hav ((ball_subset_ball hsσ).trans hxρ), ← hav hxρ] at hd
    have hmemBall : MemLp (g i) 2 (volume.restrict (ball x σ)) :=
      (hmem _ (isCompact_closedBall x σ)).mono_measure
        (Measure.restrict_mono ball_subset_closedBall le_rfl)
    have hm := setAverage_norm_sub_average_sq_le hmemBall 0
    simp only [sub_zero] at hm
    have hb : (⨍ y in ball x σ, ‖g i y‖ ^ 2) ≤ B ^ 2 := by
      apply setAverage_le_of_ae_bound (measure_ball_pos volume x hσ).ne'
        measure_ball_lt_top.ne hmemBall.norm.integrable_sq
      filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with y hy
      exact pow_le_pow_left₀ (norm_nonneg _) (hbound i y (hxclosed hy)) 2
    have hballs : closedBall x s =ᵐ[volume] ball x s :=
      (ae_eq_of_subset_of_measure_ge ball_subset_closedBall
        (Measure.addHaar_closedBall_eq_addHaar_ball volume x s).le
        isOpen_ball.measurableSet.nullMeasurableSet measure_closedBall_lt_top.ne).symm
    simp_rw [setAverage_congr hballs]
    calc
      _ ≤ C * (s / σ) ^ (2 * (γ : ℝ)) * (B ^ 2 + σ ^ (2 * (γ : ℝ))) :=
        hd.trans (mul_le_mul_of_nonneg_left (add_le_add (hm.trans hb) le_rfl)
          (by positivity))
      _ = _ := by
        have hp := Real.rpow_mul_natCast hs.le (γ : ℝ) 2
        norm_num only [Nat.cast_ofNat] at hp
        rw [mul_pow (T : ℝ), hT, ← hp, mul_comm (γ : ℝ) 2,
          Real.div_rpow hs.le hσ.le]
        dsimp only [Q]
        ring
  obtain ⟨L, _, hholder⟩ := exists_holderOnWith_representative_of_meanSquare (n := n) hγ0
  obtain ⟨v, hv, hvh, hva⟩ := hholder (g i) T hmem z σ hσ hcamp
  refine ⟨v, L * T, hv, hvh, hva.trans ?_⟩
  exact (hga i).filter_mono (ae_mono (Measure.restrict_mono
    (ball_subset_ball (by dsimp only [σ]; linarith : σ / 8 ≤ ρ)) le_rfl))

end SobolevSpace.GraphSpace
