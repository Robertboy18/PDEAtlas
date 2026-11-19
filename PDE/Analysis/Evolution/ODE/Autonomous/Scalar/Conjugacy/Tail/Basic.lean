/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Autonomous.Scalar.Conjugacy
import CAS.ExactTactic

/-!
# Backward trajectories in a scalar inverse chart

Let `H = scalarConjugacy c b`, with `b` continuous and `c + s b(s) > 0` on
`(-r, r)`, and let `K` be a smooth right inverse of `H` on a ball around zero. Then
`t ↦ K(e^{ct} H(s₀))` solves `u' = c u + u² b(u)` for every `t ≤ 0`, so a smooth
inverse transports the exponential contraction of `y' = c y` to the nonlinear flow.
The trajectory and its derivative tend to `0` as `t → -∞`. Only continuity of
`b` is used once `K` is given.
-/

@[expose] public section

open Filter Metric Set
open scoped ContDiff Topology

namespace PDE.Analysis.Evolution.Scalar

/-- Let `K` be a smooth right inverse of `H = scalarConjugacy c b` on `ball 0 η` with
values in `(-r, r)` and `K 0 = 0`, and let `K (H s₀) = s₀` with `H s₀ ∈ ball 0 η`.
Then `u t = K (e^{ct} H s₀)` has `u 0 = s₀`, and for every `t ≤ 0` it lies in
`(-r, r)` between `0` and `s₀`, is smooth at `t` and solves `u' = c u + u² b(u)`.
Both `u` and `u'` tend to `0` as `t → -∞`. -/
theorem scalarConjugacy_backward_tail_of_inverse
    {c r η s₀ : ℝ} {b K : ℝ → ℝ} (hr : 0 < r) (hη : 0 < η)
    (hb : ContinuousOn b (Ioo (-r) r))
    (hden : ∀ s ∈ Ioo (-r) r, 0 < c + s * b s)
    (hK : ContDiffOn ℝ ∞ K (ball 0 η)) (hKzero : K 0 = 0)
    (hsource : MapsTo K (ball 0 η) (Ioo (-r) r))
    (hright : ∀ y ∈ ball 0 η, scalarConjugacy c b (K y) = y)
    (hleft : K (scalarConjugacy c b s₀) = s₀)
    (hs₀ : scalarConjugacy c b s₀ ∈ ball 0 η) :
    let u : ℝ → ℝ := fun t ↦ K (Real.exp (c * t) * scalarConjugacy c b s₀)
    u 0 = s₀ ∧
    (∀ t ≤ 0,
      Real.exp (c * t) * scalarConjugacy c b s₀ ∈ ball 0 η ∧
      u t ∈ Ioo (-r) r ∧ u t ∈ uIcc 0 s₀ ∧
      ContDiffAt ℝ ∞ u t ∧ HasDerivAt u (c * u t + (u t) ^ 2 * b (u t)) t) ∧
    Tendsto u atBot (𝓝 0) ∧ Tendsto (deriv u) atBot (𝓝 0) := by
  have hzero : (0 : ℝ) ∈ Ioo (-r) r := ⟨neg_lt_zero.mpr hr, hr⟩
  have hc : 0 < c := by simpa using hden 0 hzero
  have hsInterval : s₀ ∈ Ioo (-r) r := by
    simpa only [hleft] using hsource hs₀
  let Y : ℝ → ℝ := fun t ↦ Real.exp (c * t) * scalarConjugacy c b s₀
  let u : ℝ → ℝ := fun t ↦ K (Y t)
  change u 0 = s₀ ∧
    (∀ t ≤ 0, Y t ∈ ball 0 η ∧ u t ∈ Ioo (-r) r ∧ u t ∈ uIcc 0 s₀ ∧
      ContDiffAt ℝ ∞ u t ∧ HasDerivAt u (c * u t + (u t) ^ 2 * b (u t)) t) ∧
    Tendsto u atBot (𝓝 0) ∧ Tendsto (deriv u) atBot (𝓝 0)
  have hexp_le (t : ℝ) (ht : t ≤ 0) : Real.exp (c * t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hc.le ht)
  have hYtarget (t : ℝ) (ht : t ≤ 0) : Y t ∈ ball 0 η := by
    rw [mem_ball, Real.dist_eq, sub_zero, abs_mul, Real.abs_exp]
    exact (mul_le_of_le_one_left (abs_nonneg _) (hexp_le t ht)).trans_lt
      (by simpa only [mem_ball, Real.dist_eq, sub_zero] using hs₀)
  have huInterval (t : ℝ) (ht : t ≤ 0) : u t ∈ Ioo (-r) r :=
    hsource (hYtarget t ht)
  have hidentity (t : ℝ) (ht : t ≤ 0) : scalarConjugacy c b (u t) = Y t :=
    hright (Y t) (hYtarget t ht)
  have hu0 : u 0 = s₀ := by
    simpa only [u, Y, mul_zero, Real.exp_zero, one_mul] using hleft
  have hYsmooth : ContDiff ℝ ∞ Y :=
    (contDiff_const.mul contDiff_id).exp.mul contDiff_const
  have husmooth (t : ℝ) (ht : t ≤ 0) : ContDiffAt ℝ ∞ u t :=
    (hK.contDiffAt (isOpen_ball.mem_nhds (hYtarget t ht))).comp t hYsmooth.contDiffAt
  have huderiv (t : ℝ) (ht : t ≤ 0) :
      HasDerivAt u (c * u t + (u t) ^ 2 * b (u t)) t := by
    have hdu : DifferentiableAt ℝ u t := (husmooth t ht).differentiableAt (by simp)
    have hHu : HasDerivAt (scalarConjugacy c b)
        (deriv (scalarConjugacy c b) (u t)) (u t) :=
      (hasDerivAt_scalarConjugacy hb hden (huInterval t ht)).differentiableAt.hasDerivAt
    -- The open target gives the identity on both sides of time zero.
    have hnear : (fun τ ↦ scalarConjugacy c b (u τ)) =ᶠ[𝓝 t] Y := by
      filter_upwards [hYsmooth.continuous.continuousAt.preimage_mem_nhds
        (isOpen_ball.mem_nhds (hYtarget t ht))] with τ hτ using hright (Y τ) hτ
    have hYderiv : HasDerivAt Y (c * Y t) t := by
      dsimp only [Y]
      generalize scalarConjugacy c b s₀ = B
      cas
    have hproduct : deriv (scalarConjugacy c b) (u t) * deriv u t = c * Y t :=
      ((hHu.comp t hdu.hasDerivAt).congr_of_eventuallyEq hnear.symm).unique hYderiv
    have htransport : c * Y t =
        deriv (scalarConjugacy c b) (u t) * (c * u t + (u t) ^ 2 * b (u t)) := by
      rw [← hidentity t ht]
      exact (deriv_scalarConjugacy_mul_eq hb hden (huInterval t ht)).symm
    apply hdu.hasDerivAt.congr_deriv
    exact mul_left_cancel₀
      (ne_of_gt (deriv_scalarConjugacy_pos hb hden (huInterval t ht)))
      (hproduct.trans htransport)
  -- `H (u t) = e^{ct} H s₀` lies between `H 0 = 0` and `H s₀`, and `H` is strictly monotone.
  have hurange (t : ℝ) (ht : t ≤ 0) : u t ∈ uIcc 0 s₀ := by
    have hmono := strictMonoOn_scalarConjugacy hb hden
    have he := Real.exp_pos (c * t)
    have hle := hexp_le t ht
    rcases le_total 0 s₀ with hs | hs
    · have hH := hmono.monotoneOn hzero hsInterval hs
      rw [scalarConjugacy_zero] at hH
      refine mem_uIcc_of_le ((hmono.le_iff_le hzero (huInterval t ht)).mp ?_)
        ((hmono.le_iff_le (huInterval t ht) hsInterval).mp ?_) <;>
        simp only [hidentity t ht, scalarConjugacy_zero]
      exacts [mul_nonneg he.le hH, mul_le_of_le_one_left hH hle]
    · have hH := hmono.monotoneOn hsInterval hzero hs
      rw [scalarConjugacy_zero] at hH
      refine mem_uIcc_of_ge ((hmono.le_iff_le hsInterval (huInterval t ht)).mp ?_)
        ((hmono.le_iff_le (huInterval t ht) hzero).mp ?_) <;>
        simp only [hidentity t ht, scalarConjugacy_zero]
      exacts [le_mul_of_le_one_left hH hle, mul_nonpos_of_nonneg_of_nonpos he.le hH]
  have hYlimit : Tendsto Y atBot (𝓝 0) := by
    have hexp : Tendsto (fun t : ℝ ↦ Real.exp (c * t)) atBot (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (Tendsto.const_mul_atBot hc tendsto_id)
    simpa only [zero_mul] using hexp.mul_const (scalarConjugacy c b s₀)
  have hKlimit : Tendsto K (𝓝 0) (𝓝 0) := by
    simpa only [hKzero] using
      (hK.contDiffAt (isOpen_ball.mem_nhds (mem_ball_self hη))).continuousAt.tendsto
  have hulimit : Tendsto u atBot (𝓝 0) := hKlimit.comp hYlimit
  have hb0 : ContinuousAt b (0 : ℝ) :=
    (hb 0 hzero).continuousAt (isOpen_Ioo.mem_nhds hzero)
  have hfield : ContinuousAt (fun s : ℝ ↦ c * s + s ^ 2 * b s) 0 :=
    (continuousAt_const.mul continuousAt_id).add ((continuousAt_id.pow 2).mul hb0)
  have hfieldLimit : Tendsto (fun t ↦ c * u t + (u t) ^ 2 * b (u t)) atBot (𝓝 0) := by
    simpa [Function.comp_def] using hfield.tendsto.comp hulimit
  have hderivLimit : Tendsto (deriv u) atBot (𝓝 0) := by
    apply hfieldLimit.congr'
    filter_upwards [eventually_le_atBot (0 : ℝ)] with t ht
    exact (huderiv t ht).deriv.symm
  exact ⟨hu0, fun t ht ↦ ⟨hYtarget t ht, huInterval t ht, hurange t ht,
    husmooth t ht, huderiv t ht⟩, hulimit, hderivLimit⟩

end PDE.Analysis.Evolution.Scalar
