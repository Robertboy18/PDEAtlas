/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.InitialValue
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import PDE.Parabolic.Heat.Kernel.Integrability
import CAS.ExactTactic

/-!
# The heat kernel as an approximate identity

Gaussian tail control and locally uniform convergence of the heat-kernel evolution to continuous
initial data as `t → 0⁺`. This is part (iii) of Evans's §2.3.1(b), Theorem 1, the initial trace. The
data hypotheses `hg_cont : Continuous g` and `hg_bdd : ∃ M, ∀ x, |g x| ≤ M` are his
`g ∈ C(ℝ^n) ∩ L^∞(ℝ^n)`.

## How it works

Evans proves `u(x, t) → g(x⁰)` as `(x, t) → (x⁰, 0)` by splitting the integral at a ball around `x⁰`
and sending the tail `∫_{‖y - x⁰‖ ≥ δ} Γ(x - y, t) dy` to zero after the substitution
`z = (y - x⁰)/√t`. Our proof of `initialValueSolution_locally_uniform_initial_trace` uses the same
split. The tail is handled by scaling: `heatKernel_tail_scaling` turns `∫_{‖z‖ ≥ η} Γ(z, t)` into a
fixed Gaussian integral over `‖w‖ ≥ η / √t`, and `gaussian_profile_tail_tendsto_zero` sends that to
zero along integer radii with Mathlib's `tendsto_setIntegral_of_antitone`. Gaussian integrability is
supplied by `integrable_exp_neg_mul_sq_norm_sub_left` from `Kernel/Integrability.lean`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.1(b), Theorem 1 (Solution of initial-value problem) and
  step 2 of its proof, (11), pp. 47-48.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace HeatEquation

open scoped Pointwise
open MeasureTheory PDE.Common

variable {n : ℕ}

private theorem heatKernel_tail_scaling (η t : ℝ) (ht : 0 < t) :
    (∫ z in {z : ℝ^n | η ≤ ‖z‖}, fundamentalSolutionHeat (n := n) z t) =
      (4 * Real.pi) ^ (-(n : ℝ) / 2) *
        ∫ w in {w : ℝ^n | η / Real.sqrt t ≤ ‖w‖},
          Real.exp (-(‖w‖ ^ 2 / 4)) := by
  have hr : 0 < √t := Real.sqrt_pos.2 ht
  have hs : √t • {w : ℝ^n | η / √t ≤ ‖w‖} = {z | η ≤ ‖z‖} := by
    ext z
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hr.ne', Set.mem_ofPred_eq, Set.mem_ofPred_eq, norm_smul,
      norm_inv, Real.norm_of_nonneg hr.le, inv_mul_eq_div, div_le_div_iff_of_pos_right hr]
  have hf (w : ℝ^n) : Real.exp (-(‖√t • w‖ ^ 2 / (4 * t))) = Real.exp (-(‖w‖ ^ 2 / 4)) := by
    rw [norm_smul, Real.norm_of_nonneg hr.le, mul_pow, Real.sq_sqrt ht.le]
    field_simp
  have hscale := Measure.setIntegral_comp_smul_of_pos (μ := volume)
    (fun z : ℝ^n ↦ Real.exp (-(‖z‖ ^ 2 / (4 * t)))) {w : ℝ^n | η / √t ≤ ‖w‖} hr
  simp only [hf, hs, finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul] at hscale
  have hpref : (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * √t ^ n = (4 * Real.pi) ^ (-(n : ℝ) / 2) := by
    cas
  simp only [fundamentalSolutionHeat, ht.not_ge, ↓reduceIte]
  rw [integral_const_mul, hscale, ← hpref, mul_assoc _ (√t ^ n),
    mul_inv_cancel_left₀ (pow_ne_zero _ hr.ne')]

/-! ### Heat kernel tail control -/

/-- The Gaussian profile `w ↦ exp (-‖w‖ ^ 2 / 4)` is integrable on `ℝ^n`. -/
private theorem integrable_gaussianProfile :
    Integrable fun w : ℝ^n ↦ Real.exp (-(‖w‖ ^ 2 / 4)) := by
  simpa [div_eq_mul_inv, neg_mul, mul_comm] using
    integrable_exp_neg_mul_sq_norm_sub_left (n := n) 0 (1 / 4) (by norm_num)

/-- Tail integral of the fixed Gaussian profile goes to `0` as the radius goes to `∞`
(along `ℕ`). -/
private theorem gaussian_profile_tail_tendsto_zero :
    Filter.Tendsto
      (fun r : ℕ ↦
        ∫ w in {w : ℝ^n | (r : ℝ) ≤ ‖w‖},
          Real.exp (-(‖w‖ ^ 2 / 4)))
      Filter.atTop (nhds (0 : ℝ)) := by
  have hinter : ⋂ r : ℕ, {w : ℝ^n | (r : ℝ) ≤ ‖w‖} = ∅ :=
    Set.eq_empty_of_forall_notMem fun w hw ↦ by
      obtain ⟨N, hN⟩ := exists_nat_gt ‖w‖
      exact (Set.mem_iInter.1 hw N).not_gt hN
  simpa [hinter] using tendsto_setIntegral_of_antitone (μ := (volume : Measure (ℝ^n)))
    (fun r : ℕ ↦ measurableSet_le measurable_const measurable_norm)
    (fun i j hij w hw ↦ (Nat.cast_le.2 hij).trans hw) ⟨0, integrable_gaussianProfile.integrableOn⟩

/-- For any fixed `η > 0`, the heat kernel tail `∫_{‖z‖≥η} Γ(z,t)` can be made arbitrarily small
as `t → 0+`. -/
private theorem heatKernel_tail_small (η : ℝ) (hη : 0 < η) :
    ∀ ε : ℝ, ε > 0 →
      ∃ δ : ℝ, δ > 0 ∧
        ∀ t : ℝ, (0 < t ∧ t < δ) →
          (∫ z in {z : ℝ^n | η ≤ ‖z‖}, fundamentalSolutionHeat (n := n) z t) <
            ε := by
  intro ε hε
  have hC : 0 < (4 * Real.pi) ^ (-(n : ℝ) / 2) := by positivity
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    ((gaussian_profile_tail_tendsto_zero (n := n)).eventually (gt_mem_nhds (div_pos hε hC)))
  refine ⟨(η / (N + 1)) ^ 2, by positivity, fun t ⟨ht0, htδ⟩ ↦ ?_⟩
  have hsqrt : √t * (N + 1) < η :=
    (lt_div_iff₀ (by positivity)).1 ((Real.sqrt_lt' (by positivity)).2 htδ)
  have hNt : ((N + 1 : ℕ) : ℝ) ≤ η / √t := by
    rw [le_div_iff₀ (Real.sqrt_pos.2 ht0)]
    push_cast
    linarith
  rw [heatKernel_tail_scaling η t ht0]
  calc _ ≤ (4 * Real.pi) ^ (-(n : ℝ) / 2) *
        ∫ w in {w : ℝ^n | ((N + 1 : ℕ) : ℝ) ≤ ‖w‖}, Real.exp (-(‖w‖ ^ 2 / 4)) := by
        exact mul_le_mul_of_nonneg_left (setIntegral_mono_set
          integrable_gaussianProfile.integrableOn (.of_forall fun w ↦ (Real.exp_pos _).le)
          (.of_forall fun w hw ↦ hNt.trans hw)) hC.le
    _ < (4 * Real.pi) ^ (-(n : ℝ) / 2) * (ε / (4 * Real.pi) ^ (-(n : ℝ) / 2)) := by
        gcongr
        exact hN (N + 1) (by omega)
    _ = ε := mul_div_cancel₀ ε hC.ne'

private theorem heatKernel_tail_translate (x : ℝ^n) (η t : ℝ) :
    (∫ y in {y : ℝ^n | η ≤ ‖x - y‖},
        fundamentalSolutionHeat (n := n) (x - y) t) =
      (∫ z in {z : ℝ^n | η ≤ ‖z‖}, fundamentalSolutionHeat (n := n) z t) := by
  exact (Measure.measurePreserving_sub_left volume x).setIntegral_preimage_emb
    (MeasurableEquiv.subLeft x).measurableEmbedding (fundamentalSolutionHeat · t) {z | η ≤ ‖z‖}

/-- The convolution solution converges locally uniformly to the initial data as `t → 0+`. -/
theorem initialValueSolution_locally_uniform_initial_trace (g : ℝ^n → ℝ)
    (x₀ : ℝ^n)
    (hg_cont : Continuous g) (hg_bdd : ∃ M, ∀ x, |g x| ≤ M)
    (ε : ℝ) (hε : ε > 0) :
    ∃ δ : ℝ, δ > 0 ∧
      ∀ (x : ℝ^n) (t : ℝ),
        ‖x - x₀‖ < δ → (0 < t ∧ t < δ) →
          |initialValueSolution (n := n) g x t - g x₀| < ε := by
  classical
  obtain ⟨M, hM⟩ := hg_bdd
  let M0 : ℝ := max M 1
  have hM0 (y : ℝ^n) : |g y| ≤ M0 := (hM y).trans (le_max_left _ _)
  have hM0_pos : 0 < M0 := lt_max_of_lt_right one_pos
  obtain ⟨η, hη_pos, hη⟩ :=
    Metric.continuousAt_iff.mp (hg_cont.continuousAt (x := x₀)) (ε / 2) (by positivity)
  obtain ⟨δt, hδt_pos, hδt⟩ :=
    heatKernel_tail_small (n := n) (η / 2) (by positivity) (ε / (4 * M0)) (by positivity)
  refine ⟨min (η / 2) δt, lt_min (by positivity) hδt_pos, fun x t hx ht ↦ ?_⟩
  have hxη : ‖x - x₀‖ < η / 2 := hx.trans_le (min_le_left _ _)
  let Γx : ℝ^n → ℝ := fun y ↦ fundamentalSolutionHeat (n := n) (x - y) t
  have hΓx_nonneg (y : ℝ^n) : 0 ≤ Γx y := (fundamentalSolutionHeat_pos _ t ht.1).le
  have hΓx_int : Integrable Γx :=
    (fundamentalSolutionHeat_integrable (n := n) t ht.1).comp_sub_left x
  have hΓx_one : ∫ y, Γx y = 1 :=
    (integral_sub_left_eq_self (fun z ↦ fundamentalSolutionHeat (n := n) z t) volume x).trans
      (fundamentalSolutionHeat_integral t ht.1)
  have hgsub (y : ℝ^n) : |g y - g x₀| ≤ 2 * M0 := by
    linarith [abs_sub (g y) (g x₀), hM0 y, hM0 x₀]
  have hint {f : ℝ^n → ℝ} (hf : Continuous f) (hfc : ∀ y, |f y| ≤ 2 * M0) :
      Integrable fun y ↦ Γx y * f y :=
    hΓx_int.mul_bdd hf.aestronglyMeasurable (.of_forall hfc)
  have hcont : Continuous fun y ↦ g y - g x₀ := by fun_prop
  have habsInt : Integrable fun y ↦ Γx y * |g y - g x₀| :=
    hint hcont.abs fun y ↦ (abs_abs _).trans_le (hgsub y)
  have hA : MeasurableSet (Metric.ball x₀ η) := measurableSet_ball
  have hnear : ∫ y in Metric.ball x₀ η, Γx y * |g y - g x₀| ≤ ε / 2 := calc
    _ ≤ ∫ y in Metric.ball x₀ η, Γx y * (ε / 2) :=
      setIntegral_mono_on habsInt.integrableOn (hΓx_int.mul_const _).integrableOn hA fun y hy ↦
          mul_le_mul_of_nonneg_left (hη hy).le (hΓx_nonneg y)
    _ ≤ ∫ y, Γx y * (ε / 2) := setIntegral_le_integral (hΓx_int.mul_const _)
      (.of_forall fun y ↦ mul_nonneg (hΓx_nonneg y) (by positivity))
    _ = ε / 2 := by rw [integral_mul_const, hΓx_one, one_mul]
  have hfar : ∫ y in (Metric.ball x₀ η)ᶜ, Γx y * |g y - g x₀| < ε / 2 := calc
    _ ≤ ∫ y in {y | η / 2 ≤ ‖x - y‖}, Γx y * (2 * M0) := by
      refine (setIntegral_mono_on habsInt.integrableOn (hΓx_int.mul_const _).integrableOn hA.compl
        fun y _ ↦
          mul_le_mul_of_nonneg_left (hgsub y) (hΓx_nonneg y)).trans
        (setIntegral_mono_set (hΓx_int.mul_const _).integrableOn
          (.of_forall fun y ↦ mul_nonneg (hΓx_nonneg y) (by positivity))
          (.of_forall fun y hy ↦ ?_))
      simp only [Set.mem_compl_iff, Metric.mem_ball, not_lt, dist_eq_norm] at hy
      change η / 2 ≤ ‖x - y‖
      linarith [norm_sub_le_norm_sub_add_norm_sub y x x₀, norm_sub_rev y x]
    _ = (∫ z in {z : ℝ^n | η / 2 ≤ ‖z‖}, fundamentalSolutionHeat z t) * (2 * M0) := by
      rw [integral_mul_const]
      exact congrArg (· * (2 * M0)) (heatKernel_tail_translate x (η / 2) t)
    _ < ε / (4 * M0) * (2 * M0) := mul_lt_mul_of_pos_right
      (hδt t ⟨ht.1, ht.2.trans_le (min_le_right _ _)⟩) (by positivity)
    _ = ε / 2 := by field_simp; ring
  have hdiff : initialValueSolution g x t - g x₀ = ∫ y, Γx y * (g y - g x₀) := by
    simp only [mul_sub]
    rw [integral_sub (hint hg_cont fun y ↦ (hM0 y).trans (by linarith))
      (hΓx_int.mul_const _), integral_mul_const, hΓx_one, one_mul, initialValueSolution,
      ite_eq_right (not_le_of_gt ht.1)]
  calc |initialValueSolution g x t - g x₀|
      ≤ ∫ y, Γx y * |g y - g x₀| := by
        rw [hdiff, ← Real.norm_eq_abs]
        refine norm_integral_le_of_norm_le habsInt (.of_forall fun y ↦ ?_)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hΓx_nonneg y)]
    _ = (∫ y in Metric.ball x₀ η, Γx y * |g y - g x₀|) +
        ∫ y in (Metric.ball x₀ η)ᶜ, Γx y * |g y - g x₀| :=
      (integral_add_compl hA habsInt).symm
    _ < ε := by linarith

end HeatEquation
