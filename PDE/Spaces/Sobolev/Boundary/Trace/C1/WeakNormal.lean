/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.TraceSpace
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.ZeroTrace
public import PDE.Spaces.Sobolev.Variational.Spaces.ZeroBoundaryCoordinates

/-!
# Weak normal traces on the quotient Hilbert trace space

If the weak Laplacian of an H¹ function is an L² function, its Green pairing
vanishes on H¹₀. The geometric trace kernel is exactly H¹₀, so Mathlib's
`liftQL` descends this pairing to the quotient Hilbert trace space. The quotient
norm gives the bound `‖Λ‖ ≤ ‖f‖₂ + ‖∇u‖₂`.

The result is a continuous linear functional on the trace space.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped Sobolev InnerProductSpace

namespace SobolevSpace.GraphSpace

/-- The L² pairing of weak gradients is the sum of the scalar derivative pairings. -/
theorem inner_wkpGradientCLM_eq_sum {n : ℕ} {Ω : Set ℝ^n} (u v : H¹(Ω)) :
    inner ℝ (∇ u) (∇ v) =
      ∑ i, inner ℝ (wkpCoordinateCLM (singleDerivIndex n i) u)
        (wkpCoordinateCLM (singleDerivIndex n i) v) := by
  simpa only [wkpGradientCLM, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_pi'] using
    Lp.inner_euclideanTuple
      (fun i ↦ wkpCoordinateCLM (singleDerivIndex n i) u)
      (fun i ↦ wkpCoordinateCLM (singleDerivIndex n i) v)

end SobolevSpace.GraphSpace

namespace SobolevSpace.Trace.C1

open GraphSpace ContinuousLinearMap.KernelQuotient

variable {m : ℕ} {Ω : Set ℝ^(m + 1)}
variable [Boundary.C1ExtensionAtlas (m + 1) Ω]
variable (u : H¹(Ω)) (f : DerivLp (m + 1) 2 Ω)
variable (huf : ∀ v : H¹₀(Ω),
  (∑ i, inner ℝ (wkpCoordinateCLM (singleDerivIndex (m + 1) i) u)
    (derivCoordCLM i v)) = -inner ℝ f (baseCoordCLM v))

/-- The outward weak normal derivative when the weak Laplacian of `u` is `f`,
as a continuous functional on the quotient Hilbert trace space. -/
def weakNormalTrace : HilbertTraceSpace (Ω := Ω) →L[ℝ] ℝ :=
  (trace (Ω := Ω)).ker.liftQL
    (((innerSL ℝ f).comp wkpBaseCoordinateCLM) +
      ((innerSL ℝ (∇ u)).comp wkpGradientCLM)) (by
    intro v hv
    let t : H¹₀(Ω) := ⟨v, (trace_eq_zero_iff_mem_H10 v).mp hv⟩
    change inner ℝ f (baseCoordCLM t) + inner ℝ (∇ u) (∇ (t : H¹(Ω))) = 0
    rw [inner_wkpGradientCLM_eq_sum]
    change inner ℝ f (baseCoordCLM t) +
      (∑ i, inner ℝ (wkpCoordinateCLM (singleDerivIndex (m + 1) i) u)
        (derivCoordCLM i t)) = 0
    rw [huf t, add_neg_cancel])

/-- Evaluation on an H¹ lifting is the volume Green pairing. -/
@[simp]
theorem weakNormalTrace_traceClass (v : H¹(Ω)) :
    weakNormalTrace u f huf (traceClass v) =
      inner ℝ f (wkpBaseCoordinateCLM v) + inner ℝ (∇ u) (∇ v) :=
  rfl

include huf in
/-- The weak Green pairing depends only on the geometric boundary trace. -/
theorem weak_laplacian_pairing_eq_of_trace_eq {v w : H¹(Ω)}
    (hvw : trace v = trace w) :
    inner ℝ f (wkpBaseCoordinateCLM v) + inner ℝ (∇ u) (∇ v) =
      inner ℝ f (wkpBaseCoordinateCLM w) + inner ℝ (∇ u) (∇ w) := by
  have hq : traceClass v = traceClass w := by
    change Submodule.Quotient.mk v = (Submodule.Quotient.mk w : HilbertTraceSpace (Ω := Ω))
    rw [Submodule.Quotient.eq]
    change trace (v - w) = 0
    rw [map_sub, hvw, sub_self]
  simpa only [weakNormalTrace_traceClass] using congrArg (weakNormalTrace u f huf) hq

/-- Evaluations on H¹ liftings uniquely determine the weak normal trace. -/
theorem eq_weakNormalTrace (L : HilbertTraceSpace (Ω := Ω) →L[ℝ] ℝ)
    (hL : ∀ v : H¹(Ω), L (traceClass v) =
      inner ℝ f (wkpBaseCoordinateCLM v) + inner ℝ (∇ u) (∇ v)) :
    L = weakNormalTrace u f huf := by
  ext q
  obtain ⟨v, rfl⟩ := (trace (Ω := Ω)).ker.mkQ_surjective q
  exact hL v

/-- The quotient norm bounds the normal trace using its L² Laplacian and gradient. -/
theorem norm_weakNormalTrace_apply_le (q : HilbertTraceSpace (Ω := Ω)) :
    ‖weakNormalTrace u f huf q‖ ≤ (‖f‖ + ‖∇ u‖) * ‖q‖ := by
  have hq := congrArg (weakNormalTrace u f huf)
    (mk_representative (trace (Ω := Ω)) q)
  change inner ℝ f (wkpBaseCoordinateCLM (representative (trace (Ω := Ω)) q)) +
    inner ℝ (∇ u) (∇ (representative (trace (Ω := Ω)) q)) =
      weakNormalTrace u f huf q at hq
  rw [← hq]
  calc
    ‖inner ℝ f (wkpBaseCoordinateCLM (representative (trace (Ω := Ω)) q)) +
        inner ℝ (∇ u) (∇ (representative (trace (Ω := Ω)) q))‖ ≤
        ‖inner ℝ f (wkpBaseCoordinateCLM (representative (trace (Ω := Ω)) q))‖ +
          ‖inner ℝ (∇ u) (∇ (representative (trace (Ω := Ω)) q))‖ := norm_add_le _ _
    _ ≤ ‖f‖ * ‖wkpBaseCoordinateCLM (representative (trace (Ω := Ω)) q)‖ +
        ‖∇ u‖ * ‖∇ (representative (trace (Ω := Ω)) q)‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ ‖f‖ * ‖representative (trace (Ω := Ω)) q‖ +
        ‖∇ u‖ * ‖representative (trace (Ω := Ω)) q‖ :=
      add_le_add
        (mul_le_mul_of_nonneg_left (wkpBaseCoordinateCLM_norm_le _) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (norm_wkpGradientCLM_apply_le _) (norm_nonneg _))
    _ = (‖f‖ + ‖∇ u‖) * ‖q‖ := by rw [norm_representative, add_mul]

/-- The operator norm is bounded by the L² Laplacian and gradient norms. -/
theorem norm_weakNormalTrace_le : ‖weakNormalTrace u f huf‖ ≤ ‖f‖ + ‖∇ u‖ := by
  -- Keep the quotient norm fixed when taking the infimum of its pointwise bounds.
  change sInf {C : ℝ | 0 ≤ C ∧ ∀ q : HilbertTraceSpace (m := m) (Ω := Ω),
    ‖weakNormalTrace u f huf q‖ ≤ C * ‖q‖} ≤ ‖f‖ + ‖∇ u‖
  exact csInf_le ⟨0, fun _ h ↦ h.1⟩
    ⟨add_nonneg (norm_nonneg _) (norm_nonneg _), norm_weakNormalTrace_apply_le u f huf⟩

end SobolevSpace.Trace.C1
