/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Control.Value
public import PDE.Analysis.Evolution.Time.LocalChainRule
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# C¹ tests along controlled trajectories

The curve `(X(s), -s)` follows physical time in the response and reversed time
in the initial-value problem. Its velocity is `(f(X(s), α(s)), -1)` almost
everywhere. Integrating the chain rule identifies the test increment exactly.

Uniform speed and state Lipschitz bounds also control the change of this
test rate uniformly over all control values. Compactness of the control
space is unnecessary.

The increment identity is the chain-rule step (32) and (39) in Evans's proof of Theorem 2,
§10.3.3, and the uniform control of the rate gives the margin (35) for all controls at once.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §10.3.3, proof of Theorem 2, equations (32), (35) and
  (39).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory Set TopologicalSpace
open scoped Topology

namespace HamiltonJacobi

open PDE.Analysis.Evolution

section Rate

variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The rate of a local C¹ test, including running cost, changes continuously
in spacetime uniformly over controls. Bounded speed controls the varying
derivative, while state Lipschitz bounds control the fixed derivative term. -/
theorem eventually_control_test_rate (f : E → A → E) (h : E → A → ℝ) (K M L : NNReal)
    (hK : ∀ v, LipschitzWith K (fun x ↦ f x v)) (hM : ∀ x v, ‖f x v‖ ≤ (M : ℝ))
    (hL : ∀ v, LipschitzWith L (fun x ↦ h x v)) {φ : E × ℝ → ℝ} {z : E × ℝ}
    (hφ : ContDiffAt ℝ 1 φ z) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ w in 𝓝 z, ∀ v,
      |(fderiv ℝ φ w (f w.1 v, -1) + h w.1 v) - (fderiv ℝ φ z (f z.1 v, -1) + h z.1 v)| < ε := by
  obtain ⟨U, hUz, hφU⟩ := hφ.contDiffOn le_rfl (by simp)
  obtain ⟨V, hVU, hV, hzV⟩ := mem_nhds_iff.mp hUz
  have hD : ContinuousAt (fderiv ℝ φ) z :=
    ((hφU.mono hVU).continuousOn_fderiv_of_isOpen hV le_rfl).continuousAt (hV.mem_nhds hzV)
  let D := fderiv ℝ φ z
  let q : E × ℝ → ℝ := fun w ↦ ‖fderiv ℝ φ w - D‖ * ((M : ℝ) + 1) +
      (‖D‖ * (K : ℝ) + (L : ℝ)) * dist w z
  have hq : ContinuousAt q z := ((hD.sub continuousAt_const).norm.mul continuousAt_const).add
      (continuousAt_const.mul (continuousAt_id.dist continuousAt_const))
  have hqz : q z = 0 := by simp only [q, D, sub_self, norm_zero, dist_self, zero_mul,
    mul_zero, add_zero]
  have he : ∀ᶠ w in 𝓝 z, q w < ε := hq.eventually (gt_mem_nhds (by simpa [hqz] using hε))
  filter_upwards [he] with w hw
  intro v
  have hdist : ‖w.1 - z.1‖ ≤ dist w z := by
    rw [← dist_eq_norm, Prod.dist_eq]
    exact le_max_left _ _
  have hv : ‖(f w.1 v, (-1 : ℝ))‖ ≤ (M : ℝ) + 1 := by
    rw [Prod.norm_mk, norm_neg, norm_one]
    exact max_le ((hM w.1 v).trans (le_add_of_nonneg_right zero_le_one))
      (le_add_of_nonneg_left M.property)
  have hf : ‖f w.1 v - f z.1 v‖ ≤ (K : ℝ) * dist w z := by
    have hl : ‖f w.1 v - f z.1 v‖ ≤ (K : ℝ) * ‖w.1 - z.1‖ := by
      simpa only [dist_eq_norm] using (hK v).dist_le_mul w.1 z.1
    exact hl.trans (mul_le_mul_of_nonneg_left hdist K.property)
  have hh : |h w.1 v - h z.1 v| ≤ (L : ℝ) * dist w z := by
    have hl : |h w.1 v - h z.1 v| ≤ (L : ℝ) * ‖w.1 - z.1‖ := by
      simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs] using (hL v).dist_le_mul w.1 z.1
    exact hl.trans (mul_le_mul_of_nonneg_left hdist L.property)
  apply lt_of_le_of_lt _ hw
  calc
    |(fderiv ℝ φ w (f w.1 v, -1) + h w.1 v) - (D (f z.1 v, -1) + h z.1 v)| =
        |(fderiv ℝ φ w - D) (f w.1 v, -1) +
          D (f w.1 v - f z.1 v, 0) + (h w.1 v - h z.1 v)| := by
      have hp : (f w.1 v - f z.1 v, (0 : ℝ)) =
          (f w.1 v, (-1 : ℝ)) - (f z.1 v, -1) := by ext <;> simp
      rw [hp, map_sub, sub_apply]
      congr 1
      ring
    _ ≤ ‖fderiv ℝ φ w - D‖ * ((M : ℝ) + 1) +
        ‖D‖ * ((K : ℝ) * dist w z) + (L : ℝ) * dist w z := by
      apply (abs_add_le _ _).trans
      apply add_le_add _ hh
      apply (abs_add_le _ _).trans
      apply add_le_add
      · exact ((fderiv ℝ φ w - D).le_opNorm _).trans (mul_le_mul_of_nonneg_left hv (norm_nonneg _))
      · have hp : ‖(f w.1 v - f z.1 v, (0 : ℝ))‖ = ‖f w.1 v - f z.1 v‖ := by
          simp only [Prod.norm_mk, norm_zero, max_eq_left (norm_nonneg _)]
        exact (D.le_opNorm _).trans (by
          rw [hp]
          exact mul_le_mul_of_nonneg_left hf (norm_nonneg D))
    _ = q w := by dsimp only [q]; ring

end Rate

section Trajectory

variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [TopologicalSpace A] [PseudoMetrizableSpace A] [MeasurableSpace A] [BorelSpace A]

variable (f : E → A → E) (hf : Continuous (fun p : E × A ↦ f p.1 p.2))
  (K M : NNReal) (hK : ∀ v, LipschitzWith K (fun x ↦ f x v))
  (hM : ∀ x v, ‖f x v‖ ≤ (M : ℝ))

local notation "X" => controlResponse f hf K M hK hM

/-- The a.e. spacetime velocity is strongly measurable and uniformly bounded. -/
private theorem integrable_reverse_velocity {a b : ℝ} (hab : a ≤ b) (α : ControlOn A a b) (x : E) :
    IntegrableOn (fun s ↦ (f (X hab α x s) (α.1 s), (-1 : ℝ))) (Icc a b) volume := by
  have hX := control_response_lipschitz f hf K M hK hM hab α x
  apply IntegrableOn.of_bound measure_Icc_lt_top ((hf.comp_aestronglyMeasurable
      (hX.continuous.aestronglyMeasurable.prodMk α.2)).prodMk
        aestronglyMeasurable_const) ((M : ℝ) + 1)
  refine Eventually.of_forall fun s ↦ ?_
  rw [Prod.norm_mk, norm_neg, norm_one]
  exact max_le ((hM _ _).trans (le_add_of_nonneg_right zero_le_one))
    (le_add_of_nonneg_left M.property)

/-- The reversed spacetime trajectory travels at speed at most `M+1`,
uniformly over measurable controls. -/
theorem dist_control_response_reverse_le {a b : ℝ} (hab : a ≤ b)
    (α : ControlOn A a b) (x : E) {s : ℝ} (hs : a ≤ s) :
    dist (X hab α x s, -s) (x, -a) ≤ ((M : ℝ) + 1) * (s - a) := by
  have hx := (control_response_lipschitz f hf K M hK hM hab α x).dist_le_mul s a
  rw [control_response_initial, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hs)] at hx
  rw [Prod.dist_eq, dist_neg_neg, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hs)]
  apply max_le
  · exact hx.trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right zero_le_one) (sub_nonneg.mpr hs))
  · calc
      s - a ≤ (M : ℝ) * (s - a) + (s - a) :=
        le_add_of_nonneg_left (mul_nonneg M.property (sub_nonneg.mpr hs))
      _ = ((M : ℝ) + 1) * (s - a) := by ring

/-- Every sufficiently short response remains in a prescribed spacetime
neighborhood of its starting point. The same time interval works for all
controls because their speeds share the bound `M`. -/
theorem exists_short_control_response_reverse_mem {a : ℝ} (ha : a < 0) (x : E)
    {U : Set (E × ℝ)} (hU : U ∈ 𝓝 (x, -a)) :
    ∃ c, ∃ hac : a < c, c < 0 ∧ ∀ α : ControlOn A a c, ∀ s ∈ Icc a c, (X hac.le α x s, -s) ∈ U := by
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp hU
  have hMpos : 0 < (M : ℝ) + 1 := by positivity
  obtain ⟨c, hac, hc⟩ := exists_between (lt_min ha (lt_add_of_pos_right a (div_pos hr hMpos)))
  obtain ⟨hc0, hcr⟩ := lt_min_iff.mp hc
  refine ⟨c, hac, hc0, fun α s hs ↦ ?_⟩
  apply hrU
  change dist (X hac.le α x s, -s) (x, -a) < r
  have hca : c - a < r / ((M : ℝ) + 1) := by linarith only [hcr]
  have hr' : ((M : ℝ) + 1) * (c - a) < r := by
    simpa only [mul_comm] using (lt_div_iff₀ hMpos).mp hca
  exact (dist_control_response_reverse_le f hf K M hK hM hac.le α x hs.1).trans_lt
    ((mul_le_mul_of_nonneg_left (sub_le_sub_right hs.2 a) hMpos.le).trans_lt hr')

/-- The rate of a C¹ test plus running cost is integrable along every response
whose reversed spacetime image stays in the test's open C¹ domain. -/
theorem intervalIntegrable_control_test_rate (h : E → A → ℝ)
    (hh : Measurable (fun p : E × A ↦ h p.1 p.2)) (C : NNReal) (hC : ∀ x v, |h x v| ≤ (C : ℝ))
    {a b : ℝ} (hab : a ≤ b) (α : ControlOn A a b) (x : E) {φ : E × ℝ → ℝ} {U : Set (E × ℝ)}
    (hU : IsOpen U) (hφ : ContDiffOn ℝ 1 φ U) (himage : ∀ s ∈ Icc a b, (X hab α x s, -s) ∈ U) :
    IntervalIntegrable (fun s ↦ fderiv ℝ φ (X hab α x s, -s) (f (X hab α x s) (α.1 s), -1) +
      h (X hab α x s) (α.1 s)) volume a b := by
  have hX := control_response_lipschitz f hf K M hK hM hab α x
  have hZ : Continuous (fun s ↦ (X hab α x s, -s)) := hX.continuous.prodMk continuous_id.neg
  have hi := integrableOn_fderiv_comp_apply hZ.continuousOn
    (integrable_reverse_velocity f hf K M hK hM hab α x) hU hφ himage
  exact ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 hi).add
    (intervalIntegrable_control_runningCost f hf K M hK hM h hh C hC hab α x)

/-- The integral of the local C¹ test rate equals the test's endpoint
increment plus running cost. The differential equation is used only a.e.;
the bounded Borel cost and speed bound give integrability. -/
theorem control_response_test_increment (h : E → A → ℝ)
    (hh : Measurable (fun p : E × A ↦ h p.1 p.2)) (C : NNReal) (hC : ∀ x v, |h x v| ≤ (C : ℝ))
    {a b : ℝ} (hab : a ≤ b) (α : ControlOn A a b) (x : E) {φ : E × ℝ → ℝ} {U : Set (E × ℝ)}
    (hU : IsOpen U) (hφ : ContDiffOn ℝ 1 φ U) (himage : ∀ s ∈ Icc a b, (X hab α x s, -s) ∈ U) :
    ∫ s in a..b, fderiv ℝ φ (X hab α x s, -s) (f (X hab α x s) (α.1 s), -1) +
      h (X hab α x s) (α.1 s) =
      controlRunningCost f hf K M hK hM h hab α x + φ (X hab α x b, -b) - φ (x, -a) := by
  let Z : ℝ → E × ℝ := fun s ↦ (X hab α x s, -s)
  let v : ℝ → E × ℝ := fun s ↦ (f (X hab α x s) (α.1 s), -1)
  have hX := control_response_lipschitz f hf K M hK hM hab α x
  have hZ : LipschitzWith (max M 1) Z := hX.prodMk LipschitzWith.id.neg
  have hv : IntegrableOn v (Icc a b) volume := integrable_reverse_velocity f hf K M hK hM hab α x
  have hd : ∀ᵐ s ∂volume.restrict (Ioc a b), HasDerivAt Z (v s) s := by
    filter_upwards [control_response_hasDerivAt_ae f hf K M hK hM hab α x] with s hs
    exact hs.prodMk (hasDerivAt_id s).neg
  have hac : AbsolutelyContinuousOnInterval Z a b :=
    hZ.lipschitzOnWith.absolutelyContinuousOnInterval
  have hchain :=
    PDE.Analysis.Evolution.AbsolutelyContinuousOnInterval.intervalIntegral_fderiv_comp_apply
      hab hac hv hd hU hφ himage
  have hi : IntervalIntegrable (fun s ↦ fderiv ℝ φ (Z s) (v s)) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2
      (integrableOn_fderiv_comp_apply hZ.continuous.continuousOn hv hU hφ himage)
  rw [intervalIntegral.integral_add hi
    (intervalIntegrable_control_runningCost f hf K M hK hM h hh C hC hab α x)]
  rw [hchain]
  simp only [Z, control_response_initial, controlRunningCost]
  ring

end Trajectory

end HamiltonJacobi
