/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.WeakNormal

/-!
# The weak normal trace of an H¹ harmonic function

The general weak normal trace with zero Laplacian gives the normal trace of a
weakly harmonic function. Its norm is at most the L² gradient norm, with
constant one in the quotient Hilbert trace norm.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped Sobolev InnerProductSpace

namespace SobolevSpace.Trace.C1

open GraphSpace

variable {m : ℕ} {Ω : Set ℝ^(m + 1)}
variable [Boundary.C1ExtensionAtlas (m + 1) Ω]
variable (u : H¹(Ω))
variable (hu : ∀ v : H¹₀(Ω),
  (∑ i, inner ℝ (wkpCoordinateCLM (singleDerivIndex (m + 1) i) u)
    (derivCoordCLM i v)) = 0)

/-- The outward weak normal derivative of a weakly harmonic H¹ function,
as a continuous functional on the quotient Hilbert trace space. -/
def weakHarmonicNormalTrace : HilbertTraceSpace (Ω := Ω) →L[ℝ] ℝ :=
  weakNormalTrace u 0 (fun v ↦ by simpa only [inner_zero_left, neg_zero] using hu v)

/-- Evaluation on the trace of any H¹ lifting is its gradient energy pairing. -/
@[simp]
theorem weakHarmonicNormalTrace_traceClass (v : H¹(Ω)) :
    weakHarmonicNormalTrace u hu (traceClass v) = inner ℝ (∇ u) (∇ v) := by
  simp only [weakHarmonicNormalTrace, weakNormalTrace_traceClass, inner_zero_left, zero_add]

/-- Evaluated at the trace class of `v`, the weak normal trace of `u` is
`∑ᵢ ⟪∂ᵢu, ∂ᵢv⟫`, written in scalar coordinates. -/
theorem weakHarmonicNormalTrace_traceClass_eq_sum (v : H¹(Ω)) :
    weakHarmonicNormalTrace u hu (traceClass v) =
      ∑ i, inner ℝ (wkpCoordinateCLM (singleDerivIndex (m + 1) i) u)
        (wkpCoordinateCLM (singleDerivIndex (m + 1) i) v) := by
  rw [weakHarmonicNormalTrace_traceClass, inner_wkpGradientCLM_eq_sum]

include hu in
/-- The gradient pairing depends only on the geometric boundary trace of the lifting. -/
theorem inner_gradient_eq_of_trace_eq {v w : H¹(Ω)} (hvw : trace v = trace w) :
    inner ℝ (∇ u) (∇ v) = inner ℝ (∇ u) (∇ w) := by
  simpa only [inner_zero_left, zero_add] using
    weak_laplacian_pairing_eq_of_trace_eq u 0
      (fun t ↦ by simpa only [inner_zero_left, neg_zero] using hu t) hvw

/-- The normal trace is uniquely determined by its evaluations on H¹ liftings. -/
theorem eq_weakHarmonicNormalTrace (L : HilbertTraceSpace (Ω := Ω) →L[ℝ] ℝ)
    (hL : ∀ v : H¹(Ω), L (traceClass v) = inner ℝ (∇ u) (∇ v)) :
    L = weakHarmonicNormalTrace u hu := by
  apply eq_weakNormalTrace
  simpa only [inner_zero_left, zero_add] using hL

/-- The quotient norm controls the normal trace, with the gradient norm as constant. -/
theorem norm_weakHarmonicNormalTrace_apply_le (q : HilbertTraceSpace (Ω := Ω)) :
    ‖weakHarmonicNormalTrace u hu q‖ ≤ ‖∇ u‖ * ‖q‖ := by
  simpa only [weakHarmonicNormalTrace, norm_zero, zero_add] using norm_weakNormalTrace_apply_le u 0
    (fun v ↦ by simpa only [inner_zero_left, neg_zero] using hu v) q

/-- The operator norm of the weak harmonic normal trace is at most the gradient norm. -/
theorem norm_weakHarmonicNormalTrace_le : ‖weakHarmonicNormalTrace u hu‖ ≤ ‖∇ u‖ := by
  simpa only [weakHarmonicNormalTrace, norm_zero, zero_add] using norm_weakNormalTrace_le u 0
    (fun v ↦ by simpa only [inner_zero_left, neg_zero] using hu v)

/-- The full H¹ norm also bounds the weak harmonic normal trace. -/
theorem norm_weakHarmonicNormalTrace_le_norm : ‖weakHarmonicNormalTrace u hu‖ ≤ ‖u‖ :=
  (norm_weakHarmonicNormalTrace_le u hu).trans (norm_wkpGradientCLM_apply_le u)

/-- Pairing a harmonic function's trace with its normal trace gives its Dirichlet energy. -/
theorem weakHarmonicNormalTrace_self :
    weakHarmonicNormalTrace u hu (traceClass u) = ‖∇ u‖ ^ 2 := by
  rw [weakHarmonicNormalTrace_traceClass, real_inner_self_eq_norm_sq]

end SobolevSpace.Trace.C1
