/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.Kruzhkov.Weak
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Two-state estimates for the scalar Kružkov flux

The Kružkov flux is symmetric in its two states. A bound on `f'` gives the same
Lipschitz bound in each state, including across their coincidence set. We prove
this by applying the mean value theorem to the smooth entropy fluxes and
passing to their limits.

These estimates control the entropy and flux terms when two state functions
approach their limits in local `L¹`, and are used to pass from the doubled
entropy inequality to its diagonal. They are the Lipschitz continuity of `(a, b) ↦ |a - b|`
and `(a, b) ↦ sgn(a - b)(F(a) - F(b))` that Evans, §11.4.3, uses to let `ε → 0` in (47), in
step 3 of the proof of Theorem 3.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.4.3, proof of Theorem 3, step 3, equation (47).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology NNReal

namespace PDE.Hyperbolic.ConservationLaw.Scalar

/-- Interchanging the two states leaves the Kružkov flux unchanged. -/
theorem kruzhkovFlux_comm (flux : ℝ → ℝ) (k r : ℝ) :
    kruzhkovFlux flux k r = kruzhkovFlux flux r k := by
  unfold kruzhkovFlux
  rw [show k - r = -(r - k) from (neg_sub _ _).symm,
    show flux k - flux r = -(flux r - flux k) from (neg_sub _ _).symm, Real.sign_neg, neg_mul_neg]

/-- A derivative bound for the physical flux also bounds the two-state entropy flux. -/
theorem norm_kruzhkovFlux_le_mul {flux : ℝ → ℝ} (hf : ContDiff ℝ 1 flux) {a b C k r : ℝ}
    (hC : ∀ s ∈ Icc a b, ‖deriv flux s‖ ≤ C) (hk : k ∈ Icc a b) (hr : r ∈ Icc a b) :
    ‖kruzhkovFlux flux k r‖ ≤ C * ‖r - k‖ :=
  (norm_kruzhkovFlux_le flux k r).trans ((convex_Icc a b).norm_image_sub_le_of_norm_deriv_le
      (fun s _ ↦ hf.differentiable_one s) hC hk hr)

/-- The entropy flux is Lipschitz in the second state even when the states cross.
The entropy center `k` need not belong to the state interval. -/
theorem norm_kruzhkovFlux_sub_right_le {flux : ℝ → ℝ} (hf : ContDiff ℝ 1 flux) {a b C r s : ℝ}
    (hC : ∀ z ∈ Icc a b, ‖deriv flux z‖ ≤ C) (k : ℝ) (hr : r ∈ Icc a b) (hs : s ∈ Icc a b) :
    ‖kruzhkovFlux flux k r - kruzhkovFlux flux k s‖ ≤ C * ‖r - s‖ := by
  have hlim := ((Kruzhkov.tendsto_smoothEntropyFlux hf k r).sub
      (Kruzhkov.tendsto_smoothEntropyFlux hf k s)).norm
  apply le_of_tendsto hlim
  refine Eventually.of_forall fun n ↦ ?_
  apply (convex_Icc a b).norm_image_sub_le_of_norm_deriv_le
    (fun z _ ↦ (Kruzhkov.hasDerivAt_smoothEntropyFlux hf n k z).differentiableAt)
    (fun z hz ↦ ?_) hs hr
  rw [(Kruzhkov.hasDerivAt_smoothEntropyFlux hf n k z).deriv, norm_mul]
  exact (mul_le_mul_of_nonneg_right (Kruzhkov.norm_smoothSign_le n k z)
    (norm_nonneg _)).trans (by simpa only [one_mul] using hC z hz)

/-- The two-state flux changes by at most the sum of the changes in its two states,
times a bound on the physical characteristic speed. -/
theorem norm_kruzhkovFlux_sub_le {flux : ℝ → ℝ} (hf : ContDiff ℝ 1 flux)
    {a b C k r l s : ℝ} (hC : ∀ z ∈ Icc a b, ‖deriv flux z‖ ≤ C)
    (hk : k ∈ Icc a b) (hr : r ∈ Icc a b) (hl : l ∈ Icc a b) (hs : s ∈ Icc a b) :
    ‖kruzhkovFlux flux k r - kruzhkovFlux flux l s‖ ≤ C * (‖k - l‖ + ‖r - s‖) := by
  have hfirst :
      ‖kruzhkovFlux flux k r - kruzhkovFlux flux l r‖ ≤ C * ‖k - l‖ := by
    rw [kruzhkovFlux_comm flux k r, kruzhkovFlux_comm flux l r]
    exact norm_kruzhkovFlux_sub_right_le hf hC r hk hl
  calc
    _ ≤ ‖kruzhkovFlux flux k r - kruzhkovFlux flux l r‖ +
        ‖kruzhkovFlux flux l r - kruzhkovFlux flux l s‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ C * ‖k - l‖ + C * ‖r - s‖ :=
      add_le_add hfirst (norm_kruzhkovFlux_sub_right_le hf hC l hr hs)
    _ = _ := (mul_add _ _ _).symm

/-- The two-state absolute-value entropy has the corresponding bound with constant one. -/
theorem norm_abs_sub_sub_abs_sub_le (k r l s : ℝ) :
    ‖|r - k| - |s - l|‖ ≤ ‖k - l‖ + ‖r - s‖ := by
  calc
    _ ≤ ‖(r - k) - (s - l)‖ := by
      simpa only [Real.norm_eq_abs] using abs_norm_sub_norm_le (r - k) (s - l)
    _ = ‖(r - s) - (k - l)‖ := by congr 1; abel
    _ ≤ ‖r - s‖ + ‖k - l‖ := norm_sub_le _ _
    _ = _ := add_comm _ _

/-- The two-state entropy flux is measurable for every measurable physical flux. -/
theorem measurable_kruzhkovFlux {flux : ℝ → ℝ} (hf : Measurable flux) :
    Measurable (fun p : ℝ × ℝ ↦ kruzhkovFlux flux p.1 p.2) := by
  have hsign : Measurable Real.sign := by
    unfold Real.sign
    exact Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
      (Measurable.ite (measurableSet_lt measurable_const measurable_id)
        measurable_const measurable_const)
  exact (hsign.comp (measurable_snd.sub measurable_fst)).mul
    ((hf.comp measurable_snd).sub (hf.comp measurable_fst))

/-- On a bounded state rectangle the two-state flux is Lipschitz.
The factor two converts the sum of the state errors to the product's maximum norm. -/
theorem lipschitzOnWith_kruzhkovFlux {flux : ℝ → ℝ} (hf : ContDiff ℝ 1 flux)
    {a b : ℝ} {C : ℝ≥0} (hC : ∀ z ∈ Icc a b, ‖deriv flux z‖ ≤ C) :
    LipschitzOnWith (2 * C) (fun p : ℝ × ℝ ↦ kruzhkovFlux flux p.1 p.2) (Icc a b ×ˢ Icc a b) := by
  refine LipschitzOnWith.of_dist_le_mul fun p hp q hq ↦ ?_
  rw [dist_eq_norm, dist_eq_norm]
  apply (norm_kruzhkovFlux_sub_le hf hC hp.1 hp.2 hq.1 hq.2).trans
  have hfst : ‖p.1 - q.1‖ ≤ ‖p - q‖ := norm_fst_le (p - q)
  have hsnd : ‖p.2 - q.2‖ ≤ ‖p - q‖ := norm_snd_le (p - q)
  simp only [NNReal.coe_mul, NNReal.coe_ofNat]
  nlinarith [C.coe_nonneg]

/-- A `C¹` flux supplies a finite Lipschitz constant on each bounded state rectangle. -/
theorem exists_lipschitzOnWith_kruzhkovFlux {flux : ℝ → ℝ} (hf : ContDiff ℝ 1 flux) (a b : ℝ) :
    ∃ C : ℝ≥0, LipschitzOnWith C (fun p : ℝ × ℝ ↦ kruzhkovFlux flux p.1 p.2)
      (Icc a b ×ˢ Icc a b) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.image hf.continuous_deriv_one).isBounded.exists_norm_le
    (s := deriv flux '' Icc a b)
  let D : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  refine ⟨2 * D, lipschitzOnWith_kruzhkovFlux hf fun z hz ↦ ?_⟩
  exact (hC _ ⟨z, hz, rfl⟩).trans (le_max_left C 0)

section L1

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Bounded measurable state pairs with integrable difference have integrable flux difference.
The state functions themselves need not be globally integrable. -/
theorem integrable_kruzhkovFlux_sub {flux : ℝ → ℝ} (hf : ContDiff ℝ 1 flux) {a b : ℝ}
    {w z : α → ℝ × ℝ} (hw : AEStronglyMeasurable w μ) (hz : AEStronglyMeasurable z μ)
    (hmem : ∀ᵐ x ∂μ, w x ∈ Icc a b ×ˢ Icc a b ∧ z x ∈ Icc a b ×ˢ Icc a b)
    (herr : Integrable (fun x ↦ w x - z x) μ) :
    Integrable (fun x ↦ kruzhkovFlux flux (w x).1 (w x).2 -
      kruzhkovFlux flux (z x).1 (z x).2) μ := by
  obtain ⟨C, hC⟩ := exists_lipschitzOnWith_kruzhkovFlux hf a b
  have hmeas := measurable_kruzhkovFlux hf.continuous.measurable
  apply (herr.norm.const_mul (C : ℝ)).mono'
    ((hmeas.comp_aemeasurable hw.aemeasurable).aestronglyMeasurable.sub
      (hmeas.comp_aemeasurable hz.aemeasurable).aestronglyMeasurable)
  filter_upwards [hmem] with x hx
  simpa only [dist_eq_norm, Pi.sub_apply, Function.comp_apply] using
    hC.dist_le_mul (w x) hx.1 (z x) hx.2

/-- Strong `L¹` convergence of bounded paired states implies strong `L¹` convergence of
their Kružkov fluxes. Applying this with a restricted measure gives the local version
needed in diagonal limits. Integrability of the state errors prevents a vacuous
convergence assertion involving totalized integrals. -/
theorem tendsto_integral_norm_kruzhkovFlux_sub {flux : ℝ → ℝ} (hf : ContDiff ℝ 1 flux) {a b : ℝ}
    {w : ℕ → α → ℝ × ℝ} {z : α → ℝ × ℝ} (hw : ∀ n, AEStronglyMeasurable (w n) μ)
    (hz : AEStronglyMeasurable z μ)
    (hmem : ∀ n, ∀ᵐ x ∂μ, w n x ∈ Icc a b ×ˢ Icc a b ∧ z x ∈ Icc a b ×ˢ Icc a b)
    (herr : ∀ n, Integrable (fun x ↦ w n x - z x) μ)
    (hlim : Tendsto (fun n ↦ ∫ x, ‖w n x - z x‖ ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ x, ‖kruzhkovFlux flux (w n x).1 (w n x).2 -
      kruzhkovFlux flux (z x).1 (z x).2‖ ∂μ) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := exists_lipschitzOnWith_kruzhkovFlux hf a b
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [mul_zero] using hlim.const_mul (C : ℝ))
    (fun n ↦ integral_nonneg fun x ↦ norm_nonneg _) (fun n ↦ ?_)
  calc
    _ ≤ ∫ x, (C : ℝ) * ‖w n x - z x‖ ∂μ := by
      apply integral_mono_ae (integrable_kruzhkovFlux_sub hf (hw n) hz (hmem n) (herr n)).norm
        ((herr n).norm.const_mul (C : ℝ))
      filter_upwards [hmem n] with x hx
      simpa only [dist_eq_norm] using hC.dist_le_mul (w n x) hx.1 (z x) hx.2
    _ = _ := integral_const_mul _ _

end L1

end PDE.Hyperbolic.ConservationLaw.Scalar
