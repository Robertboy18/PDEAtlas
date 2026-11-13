/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.EuclideanCoordinates
public import PDE.Spaces.Sobolev.GraphSpace.Operators.OrderRestriction

/-!
# Vector-valued weak gradients at every Sobolev exponent

The scalar derivative coordinates assemble into one Euclidean-valued `Lᵖ` field.
Coordinatewise almost-everywhere agreement identifies the gradient independently of
chosen representatives. Its norm is comparable to the sum of coordinate norms.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory
open scoped ENNReal Sobolev

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set (ℝ^n)}

local notation "μ" => domainMeasure n Ω

/-- The weak gradient as an `Lᵖ` vector field. Its Euclidean coordinates are the
first weak partial derivatives. The exponent may be finite or infinite. -/
noncomputable def wkpGradientCLM : W^{1,p}(Ω) →L[ℝ] Lp (ℝ^n) p μ :=
  (Lp.euclideanTuple (n := n) (p := p)).comp
    (ContinuousLinearMap.pi fun i : Fin n ↦
      wkpCoordinateCLM (n := n) (m := 1) (p := p) (Ω := Ω) (singleDerivIndex n i))

/-- The weak gradient of a scalar Sobolev function, as an `Lp` vector.
Pointwise identities refer to representatives and hold almost everywhere.
Use `open scoped Sobolev` and write `∇ u`. If Mathlib's `Gradient` scope is
also open, a weak `Lp` result type can disambiguate coercions to functions.
For `u : H¹₀(Ω)`, write `∇ (u : H¹(Ω))` to name the ambient space. -/
scoped[Sobolev] notation "∇" => SobolevSpace.GraphSpace.wkpGradientCLM

/-- Almost everywhere, each coordinate of the vector-valued weak gradient
agrees with the corresponding scalar derivative coordinate. The exceptional
null set can be chosen simultaneously for all directions. -/
theorem wkpGradientCLM_apply_ae (u : W^{1,p}(Ω)) :
    ∀ᵐ x ∂μ, ∀ i : Fin n,
      (∇ u x) i =
        (u : WkpAmbientOn n 1 p Ω) (singleDerivIndex (n := n) i) x := by
  simpa only [wkpGradientCLM, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_pi',
    wkpCoordinateCLM_apply] using Lp.euclideanTuple_apply_ae
      (fun i ↦ (u : WkpAmbientOn n 1 p Ω) (singleDerivIndex n i))

/-- Each weak partial derivative is bounded by the vector-valued gradient in `Lᵖ`. -/
theorem norm_derivCoordinate_le_wkpGradientCLM (u : W^{1,p}(Ω)) (i : Fin n) :
    ‖(u : WkpAmbientOn n 1 p Ω) (singleDerivIndex n i)‖ ≤ ‖∇ u‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [wkpGradientCLM_apply_ae u] with x hx
  rw [← hx i]
  exact PiLp.norm_apply_le _ i

/-- The gradient norm is at most the sum of the norms of its scalar coordinates. -/
theorem wkpGradientCLM_norm_le_sum (u : W^{1,p}(Ω)) :
    ‖∇ u‖ ≤
      ∑ i : Fin n, ‖(u : WkpAmbientOn n 1 p Ω) (singleDerivIndex n i)‖ := by
  simpa only [wkpGradientCLM, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_pi',
    wkpCoordinateCLM_apply] using Lp.norm_euclideanTuple_le
      (fun i ↦ (u : WkpAmbientOn n 1 p Ω) (singleDerivIndex n i))

/-- A dimension-dependent bound for the gradient with the full Sobolev graph norm.
At exponent two the sharper contractive bound follows from the squared-norm identity. -/
theorem wkpGradientCLM_norm_le (u : W^{1,p}(Ω)) :
    ‖∇ u‖ ≤ n * ‖u‖ := by
  apply (wkpGradientCLM_norm_le_sum u).trans
  calc
    ∑ i : Fin n, ‖(u : WkpAmbientOn n 1 p Ω) (singleDerivIndex n i)‖
        ≤ ∑ _i : Fin n, ‖u‖ :=
      Finset.sum_le_sum fun i _ ↦ wkpCoordinateCLM_norm_le (singleDerivIndex n i) u
    _ = n * ‖u‖ := by simp

end SobolevSpace.GraphSpace
