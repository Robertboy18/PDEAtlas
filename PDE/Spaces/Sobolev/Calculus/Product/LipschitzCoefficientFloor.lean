/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Product.LipschitzCoefficient

/-!
# A lower floor for a Lipschitz Sobolev coefficient

Clipping a bounded Lipschitz representative from below gives a W¹,∞
coefficient with that floor. Its weak derivatives come from the
Lipschitz representative construction; classical differentiability of the
clipped function is unnecessary.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal Sobolev

namespace SobolevSpace.GraphSpace

variable {n : ℕ}

/-- Clipping a bounded Lipschitz function below at `c` gives a W¹,∞ graph
whose base row is the clipped function and has the prescribed global floor. -/
theorem exists_w1Top_max_const
    (f : ℝ^n → ℝ) {C : NNReal} (hf : LipschitzWith C f)
    (hfLp : MemLp f ∞ (domainMeasure n univ)) (c : ℝ) :
    ∃ A : W^{1,∞}(ℝ^n),
      baseRepresentative A =ᵐ[domainMeasure n univ] (fun x ↦ max c (f x)) ∧
      ∀ᵐ x ∂domainMeasure n univ, c ≤ baseRepresentative A x := by
  have hgLp : MemLp (fun x ↦ max c (f x)) ∞ (domainMeasure n univ) :=
    (memLp_top_const c).sup hfLp
  let F : DerivLp n ∞ univ := hgLp.toLp (fun x ↦ max c (f x))
  let A := w1TopOfLipschitzRepresentative MeasurableSet.univ F
    (fun x ↦ max c (f x)) C (hf.const_max c) hgLp.coeFn_toLp
  have hA : baseRepresentative A =ᵐ[domainMeasure n univ] (fun x ↦ max c (f x)) :=
    (w1TopOfLipschitzRepresentative_base_ae MeasurableSet.univ F
      (fun x ↦ max c (f x)) C (hf.const_max c) hgLp.coeFn_toLp).trans hgLp.coeFn_toLp
  refine ⟨A, hA, ?_⟩
  filter_upwards [hA] with x hx
  exact hx ▸ le_max_left c (f x)

end SobolevSpace.GraphSpace
