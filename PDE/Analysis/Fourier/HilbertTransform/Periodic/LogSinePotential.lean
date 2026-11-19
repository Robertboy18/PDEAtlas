/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Algebra.Group.EvenFunction
public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.ContinuousOn
import PDE.Analysis.Calculus.Periodic
import CAS.ExactTactic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Integrability.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# The periodic log-sine potential

The log-sine potential of a function `f` on the circle of length `L` is

`logSinePotential L f x = (1 / π) ∫₀ᴸ f (y) log |sin (π (x - y) / L)| dy`.

It is the periodic counterpart of the logarithmic potential `(1 / π) ∫ f (y) log |x - y| dy` of
the Hilbert transform on the line (`PDE.Analysis.Fourier.HilbertTransform.LogPotential`): for
`L > 0` and `f` of class `C¹` and of period `L`, its derivative is the potential of `f'`
(`hasDerivAt_logSinePotential`), and the Fourier coefficients of that derivative are `-i sgn n`
times those of `f`, the multiplier of the periodic Hilbert transform
(`PDE.Analysis.Fourier.HilbertTransform.Periodic.Multiplier`). Choi, Hou, Kiselev, Luo, Šverák
and Yao take this potential of the vorticity as the velocity of the Hou–Luo model on the circle,
their (4.1).

The results of this file follow from the definition alone. The principal value formula
`(1 / L) p.v. ∫₀ᴸ f (y) cot (π (x - y) / L) dy` for the derivative is not proved here.

## The kernel

* `periodic_log_abs_sin`: `z ↦ log |sin (π z / L)|` has period `L`, for every real `L`.
* `abs_mul_log_abs_sin_le`: `log |sin z| ≤ 0`, in the form `|a log |sin z|| ≤ -M log |sin z|` for
  `|a| ≤ M`.
* `intervalIntegrable_log_abs_sin`: `y ↦ log |sin (π (c - y) / L)|` is interval integrable on
  every interval, for all real `L` and `c`, by Mathlib's `MeromorphicOn.intervalIntegrable_log`;
  `intervalIntegrable_log_abs_sin_zero` is the kernel `z ↦ log |sin (π z / L)|` itself.
* `intervalIntegrable_mul_log_abs_sin`, `intervalIntegrable_comp_sub_mul_log_abs_sin`: so are
  the products of the kernel with a continuous function, in the two forms
  `f (y) log |sin (π (x - y) / L)|` and `f (x - z) log |sin (π z / L)|`.

## The potential

Here `u = logSinePotential L f`. The algebraic identities hold for every real `L`; continuity
and the derivative are stated for `L > 0`.

* `logSinePotential_eq_integral_sub`: the convolution form
  `u (x) = (1 / π) ∫₀ᴸ f (x - z) log |sin (π z / L)| dz`, for every `f` of period `L`.
* `logSinePotential_sub`: the potential of `f - g` is the difference of the potentials, for
  continuous `f` and `g`.
* `periodic_logSinePotential`: `u` has period `L`, for every `f`.
* `continuous_logSinePotential`: `u` is continuous, for `L > 0` and every continuous `f` of
  period `L`. `continuousOn_logSinePotential`: for `L > 0` and a field `F` that is continuous on
  `ℝ × K`, with `K` a compact set of parameters, and of period `L` in its real variable,
  `(x, t) ↦ logSinePotential L (F · t) x` is continuous on `ℝ × K`.
* `hasDerivAt_logSinePotential`: if `L > 0` and `f` is `C¹` of period `L` then `u` is
  differentiable and `u'` is the potential of `f'`, which is continuous
  (`continuous_logSinePotential_deriv`).
* `logSinePotential_neg_comp_neg`: the potential of `y ↦ -f (-y)` is `x ↦ -u (-x)`, for every
  `f` of period `L`. `odd_logSinePotential`: if moreover `f` is odd then `u` is odd.
* `logSinePotential_eq_integral_half`: if `f` is odd, continuous and of period `L` then
  `u (x) = (1 / π) ∫₀^{L/2} f (y) (log |sin (π (x - y) / L)| - log |sin (π (x + y) / L)|) dy`.
  This is the second line of the display (4.4) of the paper.

## How it works

Continuity and the derivative come from the convolution form, by dominated convergence
(`intervalIntegral.continuousWithinAt_of_dominated_interval`) and differentiation under the
integral (`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`). The integrable
bound is `-M log |sin (π z / L)|`, where `M` bounds the field: a field that is continuous on
`ℝ × K` and periodic in its real variable is bounded there (`exists_norm_le_of_periodic`). The
convolution form and the reflection are changes of variables in an integral over a period
(`Function.Periodic.intervalIntegral_add_eq`), so they need no continuity of `f`.

## References

* K. Choi, T. Y. Hou, A. Kiselev, G. Luo, V. Šverák, and Y. Yao, "On the finite-time blowup of a
  one-dimensional model for the three-dimensional axisymmetric Euler equations", *Comm. Pure
  Appl. Math.* 70 (2017), no. 11, 2218-2243; numbering of arXiv:1407.4776v2, Section 4: the
  velocity (4.1) and the representation (4.4) in the proof of Lemma 4.1.
  <https://doi.org/10.1002/cpa.21697> <https://arxiv.org/abs/1407.4776v2>
-/

@[expose] public noncomputable section

open Set Real MeasureTheory Function

namespace PDE.Analysis

/-- The periodic log-sine potential `(1 / π) ∫₀ᴸ f (y) log |sin (π (x - y) / L)| dy` of a function
`f` on the circle of length `L`. It is the velocity (4.1) of Choi, Hou, Kiselev, Luo, Šverák and
Yao. For `L > 0` and `f` of class `C¹` and of period `L`, its derivative is the periodic Hilbert
transform of `f`, in the sense of `fourierCoeffOn_logSinePotential_deriv`. -/
def logSinePotential (L : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  π⁻¹ * ∫ y in (0 : ℝ)..L, f y * log |sin (π * (x - y) / L)|

variable {L : ℝ} {f g : ℝ → ℝ}

/-! ### The kernel -/

/-- The kernel `z ↦ log |sin (π z / L)|` has period `L`, for every `L`. -/
theorem periodic_log_abs_sin (L : ℝ) : Periodic (fun z ↦ log |sin (π * z / L)|) L := by
  rcases eq_or_ne L 0 with rfl | hL
  · exact periodic_with_period_zero _
  · intro z
    have h : π * (z + L) / L = π * z / L + π := by cas using [hL]
    simp only [h, sin_add_pi, abs_neg]

/-- For `|a| ≤ M`, `|a log |sin z|| ≤ -M log |sin z|`: the kernel `log |sin z|` is nonpositive. -/
theorem abs_mul_log_abs_sin_le {a M : ℝ} (ha : |a| ≤ M) (z : ℝ) :
    |a * log (|sin z|)| ≤ -M * log |sin z| := by
  have h : log |sin z| ≤ 0 := log_nonpos (abs_nonneg _) (abs_sin_le_one _)
  rw [abs_mul, abs_of_nonpos h]
  cas using [mul_le_mul_of_nonneg_right ha (neg_nonneg.mpr h)]

/-- The kernel `y ↦ log |sin (π (c - y) / L)|` is interval integrable on every interval, for
every `L` and `c`, by Mathlib's `MeromorphicOn.intervalIntegrable_log`. -/
theorem intervalIntegrable_log_abs_sin (L c a b : ℝ) :
    IntervalIntegrable (fun y ↦ log |sin (π * (c - y) / L)|) volume a b := by
  have h : MeromorphicOn (fun y : ℝ ↦ sin (π * (c - y) / L)) (uIcc a b) :=
    fun y _ ↦ AnalyticAt.meromorphicAt (by fun_prop)
  simpa only [comp_def, log_abs] using h.intervalIntegrable_log

/-- The kernel `z ↦ log |sin (π z / L)|` is interval integrable on every interval, for every `L`:
the case `c = 0` of `intervalIntegrable_log_abs_sin`, after the reflection `z ↦ -z`. -/
theorem intervalIntegrable_log_abs_sin_zero (L a b : ℝ) :
    IntervalIntegrable (fun z ↦ log |sin (π * z / L)|) volume a b := by
  simpa only [zero_sub, mul_neg, neg_div, Real.sin_neg, abs_neg] using
    intervalIntegrable_log_abs_sin L 0 a b

/-- The product of a continuous function and the kernel `y ↦ log |sin (π (x - y) / L)|` is
interval integrable on every interval. -/
theorem intervalIntegrable_mul_log_abs_sin (hf : Continuous f) (L x a b : ℝ) :
    IntervalIntegrable (fun y ↦ f y * log |sin (π * (x - y) / L)|) volume a b :=
  (intervalIntegrable_log_abs_sin L x a b).continuousOn_mul hf.continuousOn

/-- For continuous `f`, the integrand `z ↦ f (x - z) log |sin (π z / L)|` of the convolution
form of the log-sine potential is interval integrable on every interval. -/
theorem intervalIntegrable_comp_sub_mul_log_abs_sin (hf : Continuous f) (L x a b : ℝ) :
    IntervalIntegrable (fun z ↦ f (x - z) * log |sin (π * z / L)|) volume a b := by
  simpa only [sub_sub_cancel] using
    (intervalIntegrable_mul_log_abs_sin hf L x (x - a) (x - b)).comp_sub_left x

/-! ### The potential -/

/-- The convolution form of the log-sine potential of a function `f` of period `L`:
`u (x) = (1 / π) ∫₀ᴸ f (x - z) log |sin (π z / L)| dz`. -/
theorem logSinePotential_eq_integral_sub (hper : f.Periodic L) (x : ℝ) :
    logSinePotential L f x = π⁻¹ * ∫ z in (0 : ℝ)..L, f (x - z) * log |sin (π * z / L)| := by
  have hG : Periodic (fun z ↦ f (x - z) * log |sin (π * z / L)|) L :=
    (hper.const_sub x).mul (periodic_log_abs_sin L)
  have h1 := intervalIntegral.integral_comp_sub_left (a := 0) (b := L)
    (fun z ↦ f (x - z) * log |sin (π * z / L)|) x
  have h2 := hG.intervalIntegral_add_eq (x - L) 0
  simp only [sub_sub_cancel, sub_zero] at h1
  simp only [sub_add_cancel, zero_add] at h2
  rw [logSinePotential, h1, h2]

/-- The log-sine potential of a difference of continuous functions is the difference of the
potentials. -/
theorem logSinePotential_sub (hf : Continuous f) (hg : Continuous g) (L x : ℝ) :
    logSinePotential L (fun y ↦ f y - g y) x = logSinePotential L f x - logSinePotential L g x := by
  simp only [logSinePotential, sub_mul]
  rw [intervalIntegral.integral_sub (intervalIntegrable_mul_log_abs_sin hf L x 0 L)
    (intervalIntegrable_mul_log_abs_sin hg L x 0 L), mul_sub]

/-- The log-sine potential has period `L`, for every function. -/
theorem periodic_logSinePotential (L : ℝ) (f : ℝ → ℝ) : (logSinePotential L f).Periodic L :=
  fun x ↦ by
    have h (y : ℝ) : log |sin (π * (x + L - y) / L)| = log |sin (π * (x - y) / L)| := by
      rw [add_sub_right_comm]
      exact periodic_log_abs_sin L (x - y)
    simp only [logSinePotential, h]

/-- For `L > 0` and a field `F` that is continuous on `ℝ × K`, with `K` a compact set of
parameters, and of period `L` in its real variable, the log-sine potential
`(x, t) ↦ logSinePotential L (F · t) x` is continuous on `ℝ × K`. -/
theorem continuousOn_logSinePotential (hL : 0 < L) {Y : Type*} [TopologicalSpace Y]
    [FirstCountableTopology Y] {F : ℝ → Y → ℝ} {K : Set Y} (hK : IsCompact K)
    (hF : ContinuousOn (uncurry F) (univ ×ˢ K)) (hper : ∀ t ∈ K, (F · t).Periodic L) :
    ContinuousOn (fun p : ℝ × Y ↦ logSinePotential L (F · p.2) p.1) (univ ×ˢ K) := by
  have hslice (t : Y) (ht : t ∈ K) : Continuous (F · t) :=
    hF.comp_continuous (Continuous.prodMk_left t) fun y ↦ ⟨mem_univ y, ht⟩
  obtain ⟨M, hbound⟩ := exists_norm_le_of_periodic hL.ne' hK hF hper
  have hint : ContinuousOn
      (fun p : ℝ × Y ↦ ∫ z in (0 : ℝ)..L, F (p.1 - z) p.2 * log |sin (π * z / L)|)
      (univ ×ˢ K) := fun p hp ↦
    intervalIntegral.continuousWithinAt_of_dominated_interval
      (bound := fun z ↦ -M * log |sin (π * z / L)|)
      (eventually_mem_nhdsWithin.mono fun q hq ↦
        (intervalIntegrable_comp_sub_mul_log_abs_sin (hslice q.2 hq.2) L q.1 0
          L).aestronglyMeasurable_restrict_uIoc)
      (eventually_mem_nhdsWithin.mono fun q hq ↦ Filter.Eventually.of_forall fun z _ ↦
        abs_mul_log_abs_sin_le (hbound (q.1 - z) q.2 hq.2) (π * z / L))
      (intervalIntegrable_comp_sub_mul_log_abs_sin (f := fun _ ↦ -M) continuous_const L 0 0 L)
      (Filter.Eventually.of_forall fun z _ ↦ by
        have hc : ContinuousOn (fun q : ℝ × Y ↦ F (q.1 - z) q.2) (univ ×ˢ K) :=
          hF.comp (f := fun q : ℝ × Y ↦ (q.1 - z, q.2)) (by fun_prop)
            fun q hq ↦ ⟨mem_univ _, hq.2⟩
        exact (hc.mul continuousOn_const) p hp)
  exact (continuousOn_const.mul hint).congr fun p hp ↦
    logSinePotential_eq_integral_sub (hper p.2 hp.2) p.1

/-- The log-sine potential of a continuous function of period `L > 0` is continuous. -/
theorem continuous_logSinePotential (hL : 0 < L) (hf : Continuous f) (hper : f.Periodic L) :
    Continuous (logSinePotential L f) := by
  have h : ContinuousOn (fun p : ℝ × ℝ ↦ logSinePotential L f p.1) (univ ×ˢ Icc (0 : ℝ) 0) :=
    continuousOn_logSinePotential hL (F := fun y _ ↦ f y) isCompact_Icc
      (hf.comp continuous_fst).continuousOn fun _ _ ↦ hper
  exact h.comp_continuous (f := fun x ↦ (x, (0 : ℝ))) (by fun_prop)
    fun x ↦ ⟨mem_univ x, left_mem_Icc.mpr le_rfl⟩

/-- The log-sine potential of a `C¹` function `f` of period `L > 0` is differentiable, and its
derivative is the potential of `f'`. -/
theorem hasDerivAt_logSinePotential (hL : 0 < L) (hf : ContDiff ℝ 1 f) (hper : f.Periodic L)
    (x : ℝ) : HasDerivAt (logSinePotential L f) (logSinePotential L (deriv f) x) x := by
  have hf' : Continuous (deriv f) := hf.continuous_deriv_one
  have hper' : (deriv f).Periodic L := hper.deriv
  obtain ⟨M, hM⟩ := (hper'.isBounded_of_continuous hL.ne' hf').exists_norm_le
  have key : HasDerivAt (fun y ↦ ∫ z in (0 : ℝ)..L, f (y - z) * log |sin (π * z / L)|)
      (∫ z in (0 : ℝ)..L, deriv f (x - z) * log |sin (π * z / L)|) x :=
    (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun y z : ℝ ↦ f (y - z) * log |sin (π * z / L)|)
      (F' := fun y z : ℝ ↦ deriv f (y - z) * log |sin (π * z / L)|)
      (bound := fun z ↦ -M * log |sin (π * z / L)|) (s := univ) Filter.univ_mem
      (Filter.Eventually.of_forall fun y ↦
        (intervalIntegrable_comp_sub_mul_log_abs_sin hf.continuous L y 0
          L).aestronglyMeasurable_restrict_uIoc)
      (intervalIntegrable_comp_sub_mul_log_abs_sin hf.continuous L x 0 L)
      (intervalIntegrable_comp_sub_mul_log_abs_sin hf' L x 0
        L).aestronglyMeasurable_restrict_uIoc
      (Filter.Eventually.of_forall fun z _ y _ ↦
        abs_mul_log_abs_sin_le (hM _ (mem_range_self (y - z))) (π * z / L))
      (intervalIntegrable_comp_sub_mul_log_abs_sin (f := fun _ ↦ -M) continuous_const L 0 0 L)
      (Filter.Eventually.of_forall fun z _ y _ ↦
        ((hf.differentiable one_ne_zero (y - z)).hasDerivAt.comp_sub_const y z).mul_const _)).2
  rw [logSinePotential_eq_integral_sub hper' x]
  exact (key.const_mul π⁻¹).congr_of_eventuallyEq
    (Filter.Eventually.of_forall (logSinePotential_eq_integral_sub hper))

/-- The derivative `logSinePotential L (deriv f)` of the log-sine potential of a `C¹` function
`f` of period `L > 0` is continuous. -/
theorem continuous_logSinePotential_deriv (hL : 0 < L) (hf : ContDiff ℝ 1 f)
    (hper : f.Periodic L) : Continuous (logSinePotential L (deriv f)) :=
  continuous_logSinePotential hL hf.continuous_deriv_one hper.deriv

/-- The log-sine potential of the reflected function `y ↦ -f (-y)` at `x` is `-u (-x)`, for `f`
of period `L`. -/
theorem logSinePotential_neg_comp_neg (hper : f.Periodic L) (x : ℝ) :
    logSinePotential L (fun y ↦ -f (-y)) x = -logSinePotential L f (-x) := by
  have hk (y : ℝ) : log |sin (π * (x - y) / L)| = log |sin (π * (-x - -y) / L)| := by
    rw [show π * (-x - -y) / L = -(π * (x - y) / L) by cas, sin_neg, abs_neg]
  have hG : Periodic (fun y ↦ f y * log |sin (π * (-x - y) / L)|) L :=
    hper.mul ((periodic_log_abs_sin L).const_sub (-x))
  have h1 := intervalIntegral.integral_comp_neg (a := 0) (b := L)
    (fun y ↦ f y * log |sin (π * (-x - y) / L)|)
  have h2 := hG.intervalIntegral_add_eq (-L) 0
  simp only [neg_zero] at h1
  simp only [neg_add_cancel, zero_add] at h2
  calc logSinePotential L (fun y ↦ -f (-y)) x
      = π⁻¹ * ∫ y in (0 : ℝ)..L, -(f (-y) * log |sin (π * (-x - -y) / L)|) := by
        simp only [logSinePotential, neg_mul, hk]
    _ = -logSinePotential L f (-x) := by
        rw [intervalIntegral.integral_neg, h1, h2, mul_neg, logSinePotential]

/-- The log-sine potential of an odd function of period `L` is odd. -/
theorem odd_logSinePotential (hper : f.Periodic L) (hodd : f.Odd) :
    (logSinePotential L f).Odd := fun x ↦ by
  have h := logSinePotential_neg_comp_neg hper x
  rw [show (fun y ↦ -f (-y)) = f from funext fun y ↦ by rw [hodd y, neg_neg]] at h
  rw [h, neg_neg]

/-- **The half-period formula.** For `f` odd, continuous and of period `L`,
`u (x) = (1 / π) ∫₀^{L/2} f (y) (log |sin (π (x - y) / L)| - log |sin (π (x + y) / L)|) dy`:
the second line of the display (4.4) of Choi, Hou, Kiselev, Luo, Šverák and Yao. -/
theorem logSinePotential_eq_integral_half (hf : Continuous f) (hper : f.Periodic L)
    (hodd : f.Odd) (x : ℝ) :
    logSinePotential L f x = π⁻¹ * ∫ y in (0 : ℝ)..(L / 2),
      f y * (log |sin (π * (x - y) / L)| - log |sin (π * (x + y) / L)|) := by
  have hg := intervalIntegrable_mul_log_abs_sin hf L x
  have hk (y : ℝ) : log |sin (π * (x + y - L) / L)| = log |sin (π * (x + y) / L)| :=
    (periodic_log_abs_sin L).sub_eq (x + y)
  have hrefl (y : ℝ) : f (L - y) * log |sin (π * (x - (L - y)) / L)| =
      -(f y * log |sin (π * (x + y) / L)|) := by
    rw [hper.sub_eq', hodd y, sub_sub_eq_add_sub, hk, neg_mul]
  have h1 := intervalIntegral.integral_comp_sub_left (a := 0) (b := L / 2)
    (fun y ↦ f y * log |sin (π * (x - y) / L)|) L
  have h2 : IntervalIntegrable (fun y ↦ -(f y * log |sin (π * (x + y) / L)|)) volume 0
      (L / 2) := by
    simpa only [sub_self, sub_half, hrefl] using (hg L (L / 2)).comp_sub_left L
  simp only [hrefl, sub_half, sub_zero] at h1
  rw [logSinePotential,
    ← intervalIntegral.integral_add_adjacent_intervals (hg 0 (L / 2)) (hg (L / 2) L), ← h1,
    ← intervalIntegral.integral_add (hg 0 (L / 2)) h2]
  simp only [← sub_eq_add_neg, ← mul_sub]

end PDE.Analysis
