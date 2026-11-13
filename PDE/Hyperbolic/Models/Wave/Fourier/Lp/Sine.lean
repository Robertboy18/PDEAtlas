/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.Modulation
public import PDE.Analysis.MeasureTheory.Lp.TimeDerivative.Dominated
public import PDE.Hyperbolic.Models.Wave.Fourier.Schwartz.Kernel

/-!
# Sine propagation on Lebesgue spaces

The measurable-frequency sine multiplier defines a bounded operator without a
singularity at frequency zero. At every finite exponent its strong time derivative
is the cosine multiplier, controlled by the norm of the input. This gives a
Lipschitz time trajectory. Real multiplication is self-adjoint on complex L2.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace WaveEquation.Fourier

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NormedSpace ℝ E] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The sine propagator for a measurable frequency, with no singularity at zero. -/
noncomputable def sinePropagator {ω : α → ℝ} (hω : Measurable ω) (t : ℝ) :
    Lp E p μ →L[ℝ] Lp E p μ :=
  t • Lp.modulationCLM Real.continuous_sinc Real.abs_sinc_le_one hω t

/-- Its quotient representative is the pointwise sine kernel multiplier. -/
theorem sinePropagator_coeFn {ω : α → ℝ} (hω : Measurable ω) (t : ℝ) (u : Lp E p μ) :
    sinePropagator hω t u =ᵐ[μ] fun x ↦ sineKernel (ω x) t • u x := by
  filter_upwards [Lp.coeFn_smul t
    (Lp.modulationCLM Real.continuous_sinc Real.abs_sinc_le_one hω t u),
    Lp.modulationCLM_coeFn Real.continuous_sinc Real.abs_sinc_le_one hω t u] with x hx hm
  change (t • Lp.modulationCLM Real.continuous_sinc Real.abs_sinc_le_one hω t u : Lp E p μ) x = _
  rw [hx, Pi.smul_apply, hm, smul_smul]
  rfl

/-- The sine propagator has norm at most absolute time. -/
theorem norm_sinePropagator_apply_le {ω : α → ℝ} (hω : Measurable ω)
    (t : ℝ) (u : Lp E p μ) : ‖sinePropagator hω t u‖ ≤ |t| * ‖u‖ := by
  change ‖t • Lp.modulationCLM Real.continuous_sinc Real.abs_sinc_le_one hω t u‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left
    (Lp.norm_modulationCLM_apply_le Real.continuous_sinc Real.abs_sinc_le_one hω t u) (abs_nonneg t)

/-- The sine propagator starts with zero displacement. -/
@[simp] theorem sinePropagator_zero {ω : α → ℝ} (hω : Measurable ω) :
    sinePropagator (E := E) (p := p) (μ := μ) hω 0 = 0 := by
  refine ContinuousLinearMap.ext fun u ↦ ?_
  change (0 : ℝ) • (Lp.modulationCLM Real.continuous_sinc Real.abs_sinc_le_one hω 0 u) = 0
  exact zero_smul ℝ _

/-- The strong time derivative of the sine propagator is the cosine
multiplier. A single Lp bound controls the derivative at every frequency and time. -/
theorem hasDerivAt_sinePropagator_apply (hp : p ≠ ∞) {ω : α → ℝ}
    (hω : Measurable ω) (u : Lp E p μ) (t : ℝ) :
    HasDerivAt (fun s ↦ sinePropagator hω s u)
      (Lp.modulationCLM Real.continuous_cos Real.abs_cos_le_one hω t u) t := by
  have hu (s : ℝ) : MemLp (fun x ↦ sineKernel (ω x) s • u x) p μ :=
    (memLp_congr_ae (sinePropagator_coeFn hω s u)).mp (Lp.memLp _)
  have hv (s : ℝ) : MemLp (fun x ↦ Real.cos (ω x * s) • u x) p μ := (memLp_congr_ae
      (Lp.modulationCLM_coeFn Real.continuous_cos Real.abs_cos_le_one hω s u)).mp (Lp.memLp _)
  have he (s : ℝ) : (hu s).toLp (fun x ↦ sineKernel (ω x) s • u x) = sinePropagator hω s u :=
    Lp.ext ((hu s).coeFn_toLp.trans (sinePropagator_coeFn hω s u).symm)
  have hc : (hv t).toLp (fun x ↦ Real.cos (ω x * t) • u x) =
      Lp.modulationCLM Real.continuous_cos Real.abs_cos_le_one hω t u :=
    Lp.ext ((hv t).coeFn_toLp.trans
      (Lp.modulationCLM_coeFn Real.continuous_cos Real.abs_cos_le_one hω t u).symm)
  have hd := hasDerivAt_toLp_of_memLp_bound hp hu (hv t) (Lp.memLp u).norm
    (s := Set.univ) (t₀ := t) (Filter.univ_mem) (convex_univ : Convex ℝ (Set.univ : Set ℝ))
    (.of_forall fun x s _ ↦ (hasDerivAt_sineKernel (ω x) s).smul_const (u x))
    (.of_forall fun x s _ ↦ by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one _))
  simpa only [he, hc] using hd

/-- At finite exponents the sine propagator is strongly continuous. -/
theorem continuous_sinePropagator_apply (hp : p ≠ ∞) {ω : α → ℝ}
    (hω : Measurable ω) (u : Lp E p μ) :
    Continuous (fun t ↦ sinePropagator hω t u) :=
  continuous_iff_continuousAt.mpr fun t ↦ (hasDerivAt_sinePropagator_apply hp hω u t).continuousAt

/-- The sine propagator is Lipschitz in time on every fixed Lp datum. -/
theorem lipschitzWith_sinePropagator_apply (hp : p ≠ ∞) {ω : α → ℝ}
    (hω : Measurable ω) (u : Lp E p μ) :
    LipschitzWith ‖u‖₊ (fun t ↦ sinePropagator hω t u) := by
  apply lipschitzOnWith_univ.mp
  apply convex_univ.lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun t _ ↦ (hasDerivAt_sinePropagator_apply hp hω u t).hasDerivWithinAt)
  intro t _
  exact_mod_cast Lp.norm_modulationCLM_apply_le Real.continuous_cos Real.abs_cos_le_one hω t u

/-- Real sine multiplication is self-adjoint on complex L2. -/
theorem inner_sinePropagator_left {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    {ω : α → ℝ} (hω : Measurable ω) (t : ℝ) (u v : Lp F 2 μ) :
    inner ℂ (sinePropagator hω t u) v = inner ℂ u (sinePropagator hω t v) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [sinePropagator_coeFn hω t u, sinePropagator_coeFn hω t v] with x hu hv
  rw [hu, hv, inner_smul_left_eq_smul, inner_smul_right_eq_smul]

end WaveEquation.Fourier
