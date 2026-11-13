/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.Entropy
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Basic.Real.Sign
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

/-!
# Smooth approximations of the scalar Kružkov entropy pair

The increasing smooth functions `arctan (n * (r - k)) / (π / 2)` approximate
`sign (r - k)` and have absolute value at most one. Their primitives give convex
entropies; integrating their product with `f'` gives compatible entropy fluxes.
Interval dominated convergence and the fundamental theorem of calculus identify
the limits as `|r - k|` and `sign (r - k) * (f r - f k)`.

The pairs make explicit the approximation in step 1 of the proof of Theorem 3 in Evans,
§11.4.3: there smooth convex `β_k` with `β_k(z) → |z|` and `β_k' → sgn` give, in the limit, the
inequality (41) for the pair `|u - α|`, `sgn(u - α)(F(u) - F(α))`. Our limits are pointwise, and
the pairs follow the `C¹` entropy-pair convention of this library.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.4.3, step 1 of the proof of Theorem 3, equations
  (39)-(41).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology Interval ContDiff

namespace PDE.Hyperbolic.ConservationLaw.Scalar.Kruzhkov

/-- A smooth increasing approximation to `sign (r - k)`. -/
def smoothSign (n : ℕ) (k r : ℝ) : ℝ :=
  Real.arctan ((n : ℝ) * (r - k)) / (Real.pi / 2)

/-- The regularized sign is smooth at every state, including `r = k`. -/
theorem contDiff_smoothSign (n : ℕ) (k : ℝ) :
    ContDiff ℝ ∞ (smoothSign n k) := by
  unfold smoothSign
  exact (Real.contDiff_arctan.comp
    (contDiff_const.mul (contDiff_id.sub contDiff_const))).div_const _

/-- The regularized sign is increasing. -/
theorem monotone_smoothSign (n : ℕ) (k : ℝ) : Monotone (smoothSign n k) :=
  fun x y hxy ↦ div_le_div_of_nonneg_right
    (Real.arctan_mono (mul_le_mul_of_nonneg_left (sub_le_sub_right hxy k) (by positivity)))
    (le_of_lt (half_pos Real.pi_pos))

/-- All regularized signs are bounded by one, uniformly in the regularization. -/
theorem norm_smoothSign_le (n : ℕ) (k r : ℝ) : ‖smoothSign n k r‖ ≤ 1 := by
  rw [Real.norm_eq_abs, smoothSign, abs_div, abs_of_pos (half_pos Real.pi_pos)]
  exact (div_le_one (half_pos Real.pi_pos)).2 (abs_le.mpr ⟨(Real.neg_pi_div_two_lt_arctan _).le,
      (Real.arctan_lt_pi_div_two _).le⟩)

/-- The regularized signs converge at every state; their value at the center is zero. -/
theorem tendsto_smoothSign (k r : ℝ) :
    Tendsto (fun n : ℕ ↦ smoothSign n k r) atTop (𝓝 (Real.sign (r - k))) := by
  rcases lt_trichotomy r k with h | rfl | h
  · have ht : Tendsto (fun n : ℕ ↦ (n : ℝ) * (r - k)) atTop atBot :=
      tendsto_natCast_atTop_atTop.atTop_mul_const_of_neg (sub_neg.mpr h)
    have ha := (Real.tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp ht
    simpa [smoothSign, Real.sign_of_neg (sub_neg.mpr h), Real.pi_ne_zero] using
      ha.div_const (Real.pi / 2)
  · simp [smoothSign]
  · have ht : Tendsto (fun n : ℕ ↦ (n : ℝ) * (r - k)) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_const (sub_pos.mpr h)
    have ha := (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp ht
    simpa [smoothSign, Real.sign_of_pos (sub_pos.mpr h), Real.pi_ne_zero] using
      ha.div_const (Real.pi / 2)

/-- The smooth convex entropy is normalized to vanish at `k`. -/
def smoothEntropy (n : ℕ) (k r : ℝ) : ℝ :=
  ∫ s in k..r, smoothSign n k s

/-- The compatible flux is normalized to vanish at `k`. -/
def smoothEntropyFlux (flux : ℝ → ℝ) (n : ℕ) (k r : ℝ) : ℝ :=
  ∫ s in k..r, smoothSign n k s * deriv flux s

/-- FTC identifies the derivative of the regularized entropy. -/
theorem hasDerivAt_smoothEntropy (n : ℕ) (k r : ℝ) :
    HasDerivAt (smoothEntropy n k) (smoothSign n k r) r := by
  have hc := (contDiff_smoothSign n k).continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

/-- The entropy regularizations are smooth. -/
theorem contDiff_smoothEntropy (n : ℕ) (k : ℝ) :
    ContDiff ℝ ∞ (smoothEntropy n k) := by
  rw [contDiff_infty_iff_deriv]
  exact ⟨fun r ↦ (hasDerivAt_smoothEntropy n k r).differentiableAt,
    by simpa only [funext (fun r ↦ (hasDerivAt_smoothEntropy n k r).deriv)] using
      contDiff_smoothSign n k⟩

/-- Monotonicity of the regularized sign proves convexity of its primitive. -/
theorem convexOn_smoothEntropy (n : ℕ) (k : ℝ) :
    ConvexOn ℝ univ (smoothEntropy n k) := by
  apply MonotoneOn.convexOn_of_deriv convex_univ
    (contDiff_smoothEntropy n k).continuous.continuousOn
    (fun r _ ↦ (hasDerivAt_smoothEntropy n k r).differentiableAt.differentiableWithinAt)
  simpa only [funext (fun r ↦ (hasDerivAt_smoothEntropy n k r).deriv)] using
    (monotone_smoothSign n k).monotoneOn (interior univ)

/-- FTC gives compatibility between the entropy derivative and the flux derivative. -/
theorem hasDerivAt_smoothEntropyFlux {flux : ℝ → ℝ} (hf : ContDiff ℝ 1 flux) (n : ℕ) (k r : ℝ) :
    HasDerivAt (smoothEntropyFlux flux n k) (smoothSign n k r * deriv flux r) r := by
  have hc := (contDiff_smoothSign n k).continuous.mul hf.continuous_deriv_one
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

/-- A `C¹` physical flux gives `C¹` regularized entropy fluxes. -/
theorem contDiff_smoothEntropyFlux {flux : ℝ → ℝ} (hf : ContDiff ℝ 1 flux)
    (n : ℕ) (k : ℝ) : ContDiff ℝ 1 (smoothEntropyFlux flux n k) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun r ↦ (hasDerivAt_smoothEntropyFlux hf n k r).differentiableAt, ?_⟩
  rw [show deriv (smoothEntropyFlux flux n k) = (fun r ↦ smoothSign n k r * deriv flux r) from
      funext (fun r ↦ (hasDerivAt_smoothEntropyFlux hf n k r).deriv)]
  exact (contDiff_smoothSign n k).continuous.mul hf.continuous_deriv_one

/-- The regularizations use the scalar entropy-pair structure. -/
def smoothEntropyPair {flux : ℝ → ℝ} (hf : ContDiff ℝ 1 flux) (n : ℕ) (k : ℝ) :
    EntropyPair (deriv flux) where
  η := smoothEntropy n k
  q := smoothEntropyFlux flux n k
  eta_contDiff := (contDiff_smoothEntropy n k).of_le (by simp)
  entropyFlux_contDiff := contDiff_smoothEntropyFlux hf n k
  hq r := by
    rw [(hasDerivAt_smoothEntropy n k r).deriv,
      (hasDerivAt_smoothEntropyFlux hf n k r).deriv]

private theorem sign_eq_on_interval (k r : ℝ) :
    ∀ᵐ s : ℝ, s ∈ Ι k r → Real.sign (s - k) = Real.sign (r - k) := by
  filter_upwards [volume.ae_ne k] with s hsk hs
  rcases lt_trichotomy r k with h | rfl | h
  · rw [uIoc_of_ge h.le] at hs
    rw [Real.sign_of_neg (sub_neg.mpr (lt_of_le_of_ne hs.2 hsk)), Real.sign_of_neg (sub_neg.mpr h)]
  · simp at hs
  · rw [uIoc_of_le h.le] at hs
    rw [Real.sign_of_pos (sub_pos.mpr hs.1), Real.sign_of_pos (sub_pos.mpr h)]

/-- Dominated convergence for a continuously weighted regularized sign.
The sign is constant almost everywhere on the oriented interval from `k` to `r`. -/
theorem tendsto_integral_smoothSign_mul {g : ℝ → ℝ} (hg : Continuous g) (k r : ℝ) :
    Tendsto (fun n : ℕ ↦ ∫ s in k..r, smoothSign n k s * g s) atTop
      (𝓝 (Real.sign (r - k) * ∫ s in k..r, g s)) := by
  have ht := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (a := k) (b := r) (μ := volume) (l := atTop) (F := fun n s ↦ smoothSign n k s * g s)
    (f := fun s ↦ Real.sign (r - k) * g s) (fun s ↦ ‖g s‖) (Eventually.of_forall fun n ↦
      ((contDiff_smoothSign n k).continuous.mul hg).aestronglyMeasurable.restrict)
    (Eventually.of_forall fun n ↦ Eventually.of_forall fun s _ ↦ by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (norm_smoothSign_le n k s)
        (norm_nonneg _)).trans_eq (one_mul _)) (hg.norm.intervalIntegrable k r)
    (by
      filter_upwards [sign_eq_on_interval k r] with s hs hsr
      simpa only [hs hsr] using (tendsto_smoothSign k s).mul_const (g s))
  simpa only [intervalIntegral.integral_const_mul] using ht

/-- The regularized entropies converge to the absolute-value entropy. -/
theorem tendsto_smoothEntropy (k r : ℝ) :
    Tendsto (fun n : ℕ ↦ smoothEntropy n k r) atTop (𝓝 |r - k|) := by
  have ht := tendsto_integral_smoothSign_mul (g := fun _ ↦ (1 : ℝ)) continuous_const k r
  have heq : Real.sign (r - k) * (r - k) = |r - k| := by
    rcases lt_trichotomy r k with h | rfl | h
    · rw [Real.sign_of_neg (sub_neg.mpr h), neg_one_mul, abs_of_neg (sub_neg.mpr h)]
    · simp
    · rw [Real.sign_of_pos (sub_pos.mpr h), one_mul, abs_of_pos (sub_pos.mpr h)]
  simpa [smoothEntropy, heq] using ht

/-- FTC identifies the limiting flux; flux convergence is proved from `C¹` regularity. -/
theorem tendsto_smoothEntropyFlux {flux : ℝ → ℝ} (hf : ContDiff ℝ 1 flux) (k r : ℝ) :
    Tendsto (fun n : ℕ ↦ smoothEntropyFlux flux n k r) atTop
      (𝓝 (Real.sign (r - k) * (flux r - flux k))) := by
  have ht := tendsto_integral_smoothSign_mul hf.continuous_deriv_one k r
  rwa [intervalIntegral.integral_deriv_of_contDiffOn_uIcc hf.contDiffOn] at ht

/-- Uniform linear growth of the regularized entropies. -/
theorem norm_smoothEntropy_le (n : ℕ) (k r : ℝ) :
    ‖smoothEntropy n k r‖ ≤ |r - k| := by
  unfold smoothEntropy
  simpa only [one_mul] using (intervalIntegral.norm_integral_le_of_norm_le_const
      (a := k) (b := r) fun s _ ↦ norm_smoothSign_le n k s)

/-- A bound on the physical flux derivative bounds every regularized entropy flux. -/
theorem norm_smoothEntropyFlux_le {flux : ℝ → ℝ} (n : ℕ) (k r C : ℝ)
    (hC : ∀ s ∈ uIcc k r, ‖deriv flux s‖ ≤ C) :
    ‖smoothEntropyFlux flux n k r‖ ≤ C * |r - k| := by
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun s hs ↦ ?_
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right (norm_smoothSign_le n k s) (norm_nonneg _)).trans
    (by simpa only [one_mul] using hC s (uIoc_subset_uIcc hs))

/-- On every bounded state interval, both regularized coefficients have a common bound
independent of the regularization index. -/
theorem exists_bound_smoothEntropyPair {flux : ℝ → ℝ} (hf : ContDiff ℝ 1 flux) (k M : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, ∀ r : ℝ, ‖r‖ ≤ M → ‖smoothEntropy n k r‖ ≤ B ∧
      ‖smoothEntropyFlux flux n k r‖ ≤ B := by
  let R := max M |k|
  obtain ⟨C, hC⟩ := (isCompact_Icc.image hf.continuous_deriv_one).isBounded.exists_norm_le
    (s := deriv flux '' Icc (-R) R)
  let D := max C 0
  let A := max M 0 + |k|
  refine ⟨max A (D * A), le_max_of_le_left (by positivity), fun n r hr ↦ ?_⟩
  have hrk : |r - k| ≤ A := by
    apply (abs_sub r k).trans
    dsimp [A]
    gcongr
    exact (show |r| ≤ M from hr).trans (le_max_left M 0)
  refine ⟨(norm_smoothEntropy_le n k r).trans (hrk.trans (le_max_left _ _)), ?_⟩
  apply (norm_smoothEntropyFlux_le n k r D ?_).trans
    ((mul_le_mul_of_nonneg_left hrk (le_max_right C 0)).trans (le_max_right _ _))
  intro s hs
  have hkR : k ∈ Icc (-R) R := abs_le.mp (le_max_right M |k|)
  have hrR : r ∈ Icc (-R) R := abs_le.mp ((show |r| ≤ M from hr).trans (le_max_left M |k|))
  exact (hC _ ⟨s, uIcc_subset_Icc hkR hrR hs, rfl⟩).trans (le_max_left C 0)

end PDE.Hyperbolic.ConservationLaw.Scalar.Kruzhkov
