/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import PDE.Analysis.MeasureTheory.StronglyMeasurable.Evaluation

/-!
# Bounded measurable operator families on `Lp`

A uniformly bounded family of continuous linear maps acts on `Lp` functions over
an arbitrary measure space. Strong measurability is required only on each fixed
vector, rather than in the operator-norm topology. The exponent can be finite or infinite.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

/-- An essentially bounded operator family preserves `MemLp` if each of its
evaluations on a fixed vector is strongly measurable. -/
theorem MemLp.operatorFamily
    {𝕜 α E F : Type*} [NontriviallyNormedField 𝕜] [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {μ : Measure α} {p : ℝ≥0∞} {u : α → E} (hu : MemLp u p μ)
    (R : α → E →L[𝕜] F)
    (hR : ∀ v, AEStronglyMeasurable (fun x ↦ R x v) μ)
    (M : ℝ) (hbound : ∀ᵐ x ∂μ, ‖R x‖ ≤ M) :
    MemLp (fun x ↦ R x (u x)) p μ := by
  apply MemLp.of_le_mul (c := M) hu
    (hu.aestronglyMeasurable.eval_of_continuous hR (fun x ↦ (R x).continuous))
  filter_upwards [hbound] with x hx
  exact ((R x).le_opNorm (u x)).trans
    (mul_le_mul_of_nonneg_right hx (norm_nonneg _))

end MeasureTheory
