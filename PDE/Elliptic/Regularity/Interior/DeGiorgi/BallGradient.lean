/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.DeGiorgi.SuperlevelMeasure
import PDE.Elliptic.Regularity.Interior.DeGiorgi.Cutoffs
import PDE.Elliptic.Regularity.Interior.DeGiorgi.BallGeometry
import PDE.Elliptic.Regularity.Coefficients.Restriction

/-!
# Superlevel gradient energy on interior balls

The truncated weak equation controls the original weak gradient on the
superlevel set of a smaller ball. Both the cutoff and the ball's extension
atlas are constructed. The estimate is uniform in the centre, radii and
truncation level and holds in every positive dimension.

This is the Caccioppoli estimate used with level separation in the De Giorgi
oscillation argument for scalar measurable uniformly elliptic equations.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric TopologicalSpace
open scoped Sobolev ENNReal Distributions

namespace SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)]

/-- The superlevel gradient on an interior ball is controlled by the
tail energy on a larger ball. No regularity beyond H¹ is imposed on the
solution, and the coefficients are only essentially bounded and elliptic. -/
theorem exists_superlevel_ball_gradient_sq_le
    {α Λ : ℝ} (hα : 0 < α) (hΛ : 0 ≤ Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : Set ℝ^n),
      ∀ (a : Fin n → Fin n → DerivLp n ∞ W),
        (∀ i j, ‖a i j‖ ≤ Λ) → AEUniformlyElliptic a α →
      ∀ (u : H¹(W)), IsInteriorWeakDivergenceSolution a 0 u →
      ∀ (z : ℝ^n) (r R k : ℝ), 0 < r → r < R → ball z R ⊆ W →
        (∑ i, ∫ x in ball z r ∩ {x | k < wkpBaseCoordinateCLM u x},
          wkpCoordinateCLM (singleDerivIndex n i) u x ^ 2) ≤
        C / (R - r) ^ 2 *
          ∫ x in ball z R, max (wkpBaseCoordinateCLM u x - k) 0 ^ 2 := by
  obtain ⟨D, hD, hcut⟩ :=
    PDE.Elliptic.Regularity.DeGiorgi.exists_ball_cutoffs_with_derivative_bound (n := n)
  let C := 4 * ((n : ℝ) * n * Λ * D) ^ 2 / α ^ 2 + 1
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro W a haΛ ha u hu z r R k hr hrR hball
  let := Classical.choice (Boundary.nonempty_c1ExtensionAtlas_ball z (hr.trans hrR))
  let V : H¹(ball z R) := restrictCLM isOpen_ball.measurableSet hball u
  let b (i j : Fin n) : DerivLp n ∞ (ball z R) := restrictDerivLp hball (a i j)
  have hbΛ (i j : Fin n) : ‖b i j‖ ≤ Λ :=
    (norm_restrictDerivLp_le hball (a i j)).trans (haΛ i j)
  have hV : IsInteriorWeakDivergenceSolution b 0 V := by
    simpa only [map_zero] using hu.restrict isOpen_ball hball
  obtain ⟨η, hη, hone, _, hηD⟩ := hcut z r R hr hrR
  have hηnorm := norm_partialTestFunctionLpTop_le_of_fderiv_bound
    (V := ball z R) η (div_nonneg hD.le (sub_pos.mpr hrR).le) hηD
  let μ := domainMeasure n (ball z R)
  let U : H¹(ball z R) := V - wkpConstant k
  let T := lipschitzCompositionOn isOpen_ball Lp.lipschitzWith_pos_part U
  let q : DerivLp n ∞ (ball z R) := testFunctionLpTop η
  have hUbase : (wkpBaseCoordinateCLM U : ℝ^n → ℝ) =ᵐ[μ]
      fun x ↦ wkpBaseCoordinateCLM u x - k := by
    change (wkpBaseCoordinateCLM (V - wkpConstant k) : ℝ^n → ℝ) =ᵐ[μ] _
    rw [map_sub]
    filter_upwards [Lp.coeFn_sub (wkpBaseCoordinateCLM V)
      (wkpBaseCoordinateCLM (wkpConstant k)),
      wkpConstant_base_ae (n := n) (p := 2) (Ω := ball z R) k,
      restrictCLM_apply_ae isOpen_ball.measurableSet hball u (baseIndex n 1)]
      with x hx hk hvx
    exact hx.trans (congrArg₂ (· - ·) hvx hk)
  have hUderiv (i : Fin n) :
      (wkpCoordinateCLM (singleDerivIndex n i) U : ℝ^n → ℝ) =ᵐ[μ]
        wkpCoordinateCLM (singleDerivIndex n i) u := by
    change (wkpCoordinateCLM (singleDerivIndex n i)
      (V - wkpConstant k) : ℝ^n → ℝ) =ᵐ[μ] _
    rw [map_sub]
    filter_upwards [Lp.coeFn_sub (wkpCoordinateCLM (singleDerivIndex n i) V)
      (wkpCoordinateCLM (singleDerivIndex n i) (wkpConstant k)),
      wkpConstant_deriv_ae (n := n) (p := 2) (Ω := ball z R) k i,
      restrictCLM_apply_ae isOpen_ball.measurableSet hball u (singleDerivIndex n i)]
      with x hx hk hvx
    exact hx.trans ((congrArg₂ (· - ·) hvx hk).trans (sub_zero _))
  have hTbase : (wkpBaseCoordinateCLM T : ℝ^n → ℝ) =ᵐ[μ]
      fun x ↦ max (wkpBaseCoordinateCLM u x - k) 0 :=
    (lipschitzCompositionOn_base_ae isOpen_ball Lp.lipschitzWith_pos_part U).trans
      (hUbase.fun_comp (fun t : ℝ ↦ max t 0))
  let E := ball z r ∩ {x | k < wkpBaseCoordinateCLM u x}
  have hE : MeasurableSet E := measurableSet_ball.inter
    (measurableSet_lt measurable_const (Lp.stronglyMeasurable _).measurable)
  have hER : E ⊆ ball z R := fun x hx ↦ ball_subset_ball hrR.le hx.1
  have hmeasure : μ.restrict E = volume.restrict E := by
    change (volume.restrict (ball z R)).restrict E = _
    rw [Measure.restrict_restrict hE, inter_eq_left.mpr hER]
  have hcoord (i : Fin n) :
      (∫ x in E, wkpCoordinateCLM (singleDerivIndex n i) u x ^ 2) ≤
        ‖(q • wkpCoordinateCLM (singleDerivIndex n i) T : DerivLp n 2 (ball z R))‖ ^ 2 := by
    let p : DerivLp n 2 (ball z R) := q • wkpCoordinateCLM (singleDerivIndex n i) T
    have hrep : ∀ᵐ x ∂μ, x ∈ E → p x = wkpCoordinateCLM (singleDerivIndex n i) u x := by
      filter_upwards [Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) q
        (wkpCoordinateCLM (singleDerivIndex n i) T),
        testFunctionLpTop_apply_ae (Ω := ball z R) η,
        lipschitzCompositionOn_posPart_derivative_ae U i,
        hUbase, hUderiv i] with x hp hqx htx hux hdx
      intro hx
      have hpos : 0 < wkpBaseCoordinateCLM U x := by rw [hux]; exact sub_pos.mpr hx.2
      change p x = q x * wkpCoordinateCLM (singleDerivIndex n i) T x at hp
      change wkpCoordinateCLM (singleDerivIndex n i) T x =
        (if 0 < wkpBaseCoordinateCLM U x then
          wkpCoordinateCLM (singleDerivIndex n i) U x else 0) at htx
      rw [hp, hqx, hone x (ball_subset_closedBall hx.1), htx, ite_eq_left hpos, hdx, one_mul]
    calc
      _ = ∫ x in E, p x ^ 2 ∂μ := by
        rw [← hmeasure]
        apply integral_congr_ae
        filter_upwards [hrep.filter_mono (ae_mono Measure.restrict_le_self),
          ae_restrict_mem hE] with x hx hxE
        exact congrArg (fun t : ℝ ↦ t ^ 2) (hx hxE).symm
      _ ≤ ∫ x, p x ^ 2 ∂μ :=
        setIntegral_le_integral (Lp.memLp p).integrable_sq
          (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)
      _ = _ := (Lp.norm_sq_eq_integral_sq p).symm
  have hsum : (∑ i, ∑ j, ‖b i j‖ * ‖partialTestFunctionLpTop (Ω := ball z R) η i‖) ≤
      ((n : ℝ) * n * Λ * D) / (R - r) :=
    (Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦
      mul_le_mul (hbΛ i j) (hηnorm i) (norm_nonneg _) hΛ).trans_eq
        (by simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]; ring)
  have hzero : ∀ᵐ x ∂μ, ‖(0 : DerivLp n 2 (ball z R)) x‖ ≤ (0 : ℝ) :=
    (Lp.coeFn_zero ℝ 2 μ).mono fun x hx ↦ by rw [hx, Pi.zero_apply, norm_zero]
  have he := hV.superlevel_cutoff_gradient_sq_le_measure b (ha.restrict hball)
    0 V (M := 0) le_rfl hzero k η hη
  change α ^ 2 * ∑ i, ‖(q • wkpCoordinateCLM (singleDerivIndex n i) T :
    DerivLp n 2 (ball z R))‖ ^ 2 ≤ _ at he
  simp only [mul_zero, zero_mul, add_zero] at he
  have hnorm : ‖wkpBaseCoordinateCLM T‖ ^ 2 =
      ∫ x in ball z R, max (wkpBaseCoordinateCLM u x - k) 0 ^ 2 := by
    rw [Lp.norm_sq_eq_integral_sq]
    exact integral_congr_ae (hTbase.fun_comp (fun t : ℝ ↦ t ^ 2))
  have hs := pow_le_pow_left₀ (Finset.sum_nonneg fun i _ ↦
    Finset.sum_nonneg fun j _ ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _)) hsum 2
  have he' := he.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hs (by norm_num)) (sq_nonneg _))
  calc
    _ ≤ ∑ i, ‖(q • wkpCoordinateCLM (singleDerivIndex n i) T :
        DerivLp n 2 (ball z R))‖ ^ 2 := Finset.sum_le_sum fun i _ ↦ hcoord i
    _ ≤ (4 * (((n : ℝ) * n * Λ * D) / (R - r)) ^ 2 *
        ‖wkpBaseCoordinateCLM T‖ ^ 2) / α ^ 2 :=
      (le_div_iff₀ (sq_pos_of_pos hα)).mpr (by rw [mul_comm]; exact he')
    _ = (4 * ((n : ℝ) * n * Λ * D) ^ 2 / α ^ 2) / (R - r) ^ 2 *
        ∫ x in ball z R, max (wkpBaseCoordinateCLM u x - k) 0 ^ 2 := by
      rw [div_pow, hnorm]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (sq_nonneg _))
      (integral_nonneg fun _ ↦ sq_nonneg _)

end SobolevSpace.GraphSpace
