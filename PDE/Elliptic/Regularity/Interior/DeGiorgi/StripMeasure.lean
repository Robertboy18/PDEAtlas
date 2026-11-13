/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.DeGiorgi.BallGradient
import PDE.Elliptic.Regularity.Interior.DeGiorgi.StripEnergy
import PDE.Elliptic.Regularity.Interior.DeGiorgi.BallGeometry

/-!
# Strip-measure control for weak elliptic solutions

An upper bound and a positive measure of the lower half of a solution force
its successive upper level sets to shrink. Caccioppoli controls the strip
energy by the square of the distance to the upper bound. This factor cancels
the squared distance between consecutive levels in the separation estimate.

The theorem is stated on the unit and double balls, the normalization used
in the De Giorgi oscillation argument. The H¹ state satisfies the
homogeneous weak equation with measurable uniformly elliptic coefficients.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric
open scoped Sobolev ENNReal

namespace SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)]

/-- If a weak solution is at most one on the double ball and its nonpositive
set has measure at least `m` on the unit ball, the squared measure above
`(1+k)/2` is controlled by the measure between `k` and `(1+k)/2`, uniformly
for `0 ≤ k < 1`. This is the strip estimate for the second De Giorgi lemma. -/
theorem exists_upper_level_measure_sq_le_strip_measure
    {α Λ m : ℝ} (hα : 0 < α) (hΛ : 0 ≤ Λ) (hm : 0 < m) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : Fin n → Fin n → DerivLp n ∞ (ball (0 : ℝ^n) 2)),
        (∀ i j, ‖a i j‖ ≤ Λ) → AEUniformlyElliptic a α →
      ∀ (u : H¹(ball (0 : ℝ^n) 2)), IsInteriorWeakDivergenceSolution a 0 u →
        (∀ᵐ x ∂volume.restrict (ball (0 : ℝ^n) 2), wkpBaseCoordinateCLM u x ≤ 1) →
        m ≤ (volume.restrict (ball (0 : ℝ^n) 1)).real
          {x | wkpBaseCoordinateCLM u x ≤ 0} →
      ∀ k : ℝ, 0 ≤ k → k < 1 →
        (volume.restrict (ball (0 : ℝ^n) 1)).real
          {x | (1 + k) / 2 ≤ wkpBaseCoordinateCLM u x} ^ 2 ≤
        C * (volume.restrict (ball (0 : ℝ^n) 1)).real
          {x | k < wkpBaseCoordinateCLM u x ∧ wkpBaseCoordinateCLM u x < (1 + k) / 2} := by
  let := Classical.choice (Boundary.nonempty_c1ExtensionAtlas_ball (0 : ℝ^n) zero_lt_one)
  obtain ⟨P, hP, hsep⟩ := exists_level_separation_sq_le_strip_energy
    ((convex_ball (0 : ℝ^n) 1).isConnected (nonempty_ball.mpr zero_lt_one))
  obtain ⟨G, hG, hgrad⟩ := exists_superlevel_ball_gradient_sq_le (n := n) hα hΛ
  let μ := volume.restrict (ball (0 : ℝ^n) 1)
  let ν := volume.restrict (ball (0 : ℝ^n) 2)
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  refine ⟨4 * P * G * ν.real univ / m ^ 2 + 1, by positivity, ?_⟩
  intro a haΛ ha u hu hupper hlower k hk hk1
  have h12 : ball (0 : ℝ^n) 1 ⊆ ball 0 2 := ball_subset_ball (by norm_num)
  let U : H¹(ball (0 : ℝ^n) 1) := restrictCLM isOpen_ball.measurableSet h12 u
  have hbase : (wkpBaseCoordinateCLM U : ℝ^n → ℝ) =ᵐ[μ] wkpBaseCoordinateCLM u :=
    restrictCLM_apply_ae isOpen_ball.measurableSet h12 u (baseIndex n 1)
  let b := (1 + k) / 2
  let E := {x | k < wkpBaseCoordinateCLM u x ∧ wkpBaseCoordinateCLM u x < b}
  have hsets : {x | k < wkpBaseCoordinateCLM U x ∧ wkpBaseCoordinateCLM U x < b} =ᵐ[μ] E :=
    hbase.fun_comp fun t : ℝ ↦ k < t ∧ t < b
  have henergy (i : Fin n) :
      (∫ x in {x | k < wkpBaseCoordinateCLM U x ∧ wkpBaseCoordinateCLM U x < b},
        wkpCoordinateCLM (singleDerivIndex n i) U x ^ 2 ∂μ) =
      ∫ x in E, wkpCoordinateCLM (singleDerivIndex n i) u x ^ 2 ∂μ :=
    (setIntegral_congr_set hsets).trans (integral_congr_ae
      (((restrictCLM_apply_ae isOpen_ball.measurableSet h12 u (singleDerivIndex n i)).filter_mono
        (ae_mono Measure.restrict_le_self)).fun_comp (fun t : ℝ ↦ t ^ 2)))
  have hs := hsep U k b (by dsimp only [b]; linarith)
  change (b - k) ^ 2 * μ.real _ ^ 2 * μ.real _ ^ 2 ≤
    P * (∑ i, ∫ x in _, wkpCoordinateCLM (singleDerivIndex n i) U x ^ 2 ∂μ) * μ.real _ at hs
  have hlevel (p : ℝ → Prop) : μ.real {x | p (wkpBaseCoordinateCLM U x)} =
      μ.real {x | p (wkpBaseCoordinateCLM u x)} := measureReal_congr (hbase.fun_comp p)
  rw [hlevel (· ≤ k), hlevel (b ≤ ·), measureReal_congr hsets] at hs
  simp_rw [henergy] at hs
  have htail : (∫ x, max (wkpBaseCoordinateCLM u x - k) 0 ^ 2 ∂ν) ≤
      (1 - k) ^ 2 * ν.real univ := by
    have ht : MemLp (fun x ↦ max (wkpBaseCoordinateCLM u x - k) 0) 2 ν :=
      ((Lp.memLp (wkpBaseCoordinateCLM u)).sub (memLp_const k)).pos_part
    calc
      _ ≤ ∫ _x, (1 - k) ^ 2 ∂ν := by
        apply integral_mono_ae ht.integrable_sq (integrable_const _)
        filter_upwards [hupper] with x hx
        apply pow_le_pow_left₀ (le_max_right _ _) _ 2
        exact max_le (sub_le_sub_right hx k) (sub_nonneg.mpr hk1.le)
      _ = _ := by simp only [integral_const, smul_eq_mul]; ring
  have hg := hgrad (ball (0 : ℝ^n) 2) a haΛ ha u hu 0 1 2 k
    zero_lt_one (by norm_num) (Subset.rfl)
  norm_num only [sub_self, sub_zero, show (2 : ℝ) - 1 = 1 by norm_num,
    one_pow, div_one] at hg
  have hstripEnergy :
      (∑ i, ∫ x in E, wkpCoordinateCLM (singleDerivIndex n i) u x ^ 2 ∂μ) ≤
        G * ((1 - k) ^ 2 * ν.real univ) := by
    refine (Finset.sum_le_sum fun i _ ↦ ?_).trans
      (hg.trans (mul_le_mul_of_nonneg_left htail hG.le))
    rw [inter_comm, ← Measure.restrict_restrict
      (measurableSet_lt measurable_const (Lp.stronglyMeasurable _).measurable)]
    exact setIntegral_mono_set
      ((Lp.memLp _).mono_measure (domainMeasure_le h12)).integrable_sq.integrableOn
      (.of_forall fun _ ↦ sq_nonneg _) (.of_forall fun _ hx ↦ hx.1)
  have hstart :
      (b - k) ^ 2 * m ^ 2 * μ.real {x | b ≤ wkpBaseCoordinateCLM u x} ^ 2 ≤
        P * (G * ((1 - k) ^ 2 * ν.real univ)) * μ.real E := by
    calc
      _ ≤ (b - k) ^ 2 * μ.real {x | wkpBaseCoordinateCLM u x ≤ k} ^ 2 *
          μ.real {x | b ≤ wkpBaseCoordinateCLM u x} ^ 2 := by
        gcongr
        exact hlower.trans (measureReal_mono fun _ hx ↦ hx.trans hk)
      _ ≤ _ := hs.trans (by gcongr)
  have hbound : μ.real {x | b ≤ wkpBaseCoordinateCLM u x} ^ 2 ≤
      (4 * P * G * ν.real univ / m ^ 2) * μ.real E := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    refine le_of_mul_le_mul_left ?_ (pow_pos (sub_pos.mpr hk1) 2)
    dsimp only [b] at hstart
    nlinarith only [hstart]
  exact hbound.trans (mul_le_mul_of_nonneg_right
    (le_add_of_nonneg_right zero_le_one) measureReal_nonneg)

end SobolevSpace.GraphSpace
