/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Trace.GeneralOrder.NormalKernel
import PDE.Analysis.MeasureTheory.LpNorm

/-!
# Integration against the general-order normal kernel

The unit norm proved in `NormalKernel` gives absolute convergence and the
sharp Cauchy–Schwarz bound for integration against the kernel. These estimates
will identify the bounded Hilbert adjoint with a fiber integral.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal InnerProductSpace

namespace SobolevSpace.Fractional.Trace.GeneralOrder

theorem integrable_normalKernel_smul {s : ℝ} (hs : 1 / 2 < s)
    (a : ℝ≥0) (ha : a ≠ 0) {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    Integrable (fun t ↦ normalKernel s a t • f t) volume :=
  memLp_one_iff_integrable.1 ((memLp_normalKernel hs a ha).smul hf)

theorem norm_integral_normalKernel_smul_le {s : ℝ} (hs : 1 / 2 < s)
    (a : ℝ≥0) (ha : a ≠ 0) {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    ‖∫ t, normalKernel s a t • f t‖ ≤ ‖hf.toLp f‖ := by
  let hk : MemLp (fun t ↦ (normalKernel s a t : ℂ)) 2 volume :=
    (memLp_normalKernel hs a ha).ofReal
  let k := hk.toLp (fun t ↦ (normalKernel s a t : ℂ))
  have hk_norm : ‖k‖ = 1 := by
    rw [show ‖k‖ = ‖(memLp_normalKernel hs a ha).toLp (normalKernel s a)‖ by
      simp only [k, Lp.norm_toLp]
      congr 1
      exact eLpNorm_congr_norm_ae hk.aestronglyMeasurable
        (measurable_normalKernel s a).aestronglyMeasurable
        (Filter.Eventually.of_forall fun t ↦ Complex.norm_real _)]
    exact norm_normalKernel_toLp hs a ha
  have heq : (∫ t, normalKernel s a t • f t) = ⟪k, hf.toLp f⟫_ℂ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hk.coeFn_toLp, hf.coeFn_toLp] with t h1 h2
    change normalKernel s a t • f t = ⟪k t, hf.toLp f t⟫_ℂ
    rw [h1, h2]
    simp [RCLike.inner_apply, Complex.real_smul, mul_comm]
  rw [heq]
  simpa only [hk_norm, one_mul] using norm_inner_le_norm k (hf.toLp f)

/-- The squared estimate needed for Fubini on product-frequency space. -/
theorem norm_integral_normalKernel_smul_sq_le {s : ℝ} (hs : 1 / 2 < s)
    (a : ℝ≥0) (ha : a ≠ 0) {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    ‖∫ t, normalKernel s a t • f t‖ ^ 2 ≤ ∫ t, ‖f t‖ ^ 2 := by
  calc
    _ ≤ ‖hf.toLp f‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _)
        (norm_integral_normalKernel_smul_le hs a ha hf) 2
    _ = _ := by
      rw [Lp.norm_sq_eq_integral_norm_sq]
      exact integral_congr_ae (hf.coeFn_toLp.fun_comp (fun z : ℂ ↦ ‖z‖ ^ 2))

end SobolevSpace.Fractional.Trace.GeneralOrder
