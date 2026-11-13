/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.PeriodicAveraging.Torus

/-!
# Differentiation along periodic coordinate flows

The derivative of a continuous periodic function has zero integral whenever that
derivative is continuous. The statement allows Banach-valued functions and only
requires differentiation along the chosen coordinate.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace PDE.Analysis.PeriodicAveraging

/-- A continuous derivative along a periodic coordinate flow has zero mean. -/
theorem integral_coordinate_derivative_eq_zero {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u g : C(UnitAddTorus (Fin n), E)) (i : Fin n)
    (hd : ∀ (x : UnitAddTorus (Fin n)) (t : ℝ),
      HasDerivAt (fun s ↦ u (x + coordinateShift i s))
        (g (x + coordinateShift i t)) t) :
    (∫ x, g x ∂cellMeasure n) = 0 := by
  let F : ℝ → UnitAddTorus (Fin n) → E := fun t x ↦ u (x + coordinateShift i t)
  let F' : ℝ → UnitAddTorus (Fin n) → E := fun t x ↦ g (x + coordinateShift i t)
  have hFc (t : ℝ) : Continuous (F t) := u.continuous.comp (continuous_id.add continuous_const)
  have hGc (t : ℝ) : Continuous (F' t) := g.continuous.comp (continuous_id.add continuous_const)
  have hdiff := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := cellMeasure n) (x₀ := (0 : ℝ)) (s := univ) (F := F) (F' := F')
    (bound := fun _ ↦ ‖g‖) (univ_mem : univ ∈ 𝓝 (0 : ℝ))
    (Eventually.of_forall fun t ↦ (hFc t).aestronglyMeasurable)
    ((hFc 0).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hGc 0).aestronglyMeasurable
    (Eventually.of_forall fun x t _ ↦ g.norm_coe_le_norm (x + coordinateShift i t))
    (integrable_const ‖g‖) (Eventually.of_forall fun x t _ ↦ hd x t)
  have hconstant : (fun t ↦ ∫ x, F t x ∂cellMeasure n) =
      fun _ : ℝ ↦ ∫ x, u x ∂cellMeasure n :=
    funext fun t ↦ integral_add_right_eq_self u (coordinateShift i t)
  have hzero : HasDerivAt (fun t ↦ ∫ x, F t x ∂cellMeasure n) 0 0 := by
    rw [hconstant]
    exact hasDerivAt_const _ _
  simpa [F'] using hdiff.2.unique hzero

/-- Periodic integration by parts has no boundary term. -/
theorem integral_mul_coordinate_derivative {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (u du v dv : C(UnitAddTorus (Fin n), 𝕜)) (i : Fin n)
    (hu : ∀ x t, HasDerivAt (fun s ↦ u (x + coordinateShift i s))
      (du (x + coordinateShift i t)) t)
    (hv : ∀ x t, HasDerivAt (fun s ↦ v (x + coordinateShift i s))
      (dv (x + coordinateShift i t)) t) :
    (∫ x, u x * dv x ∂cellMeasure n) = -(∫ x, du x * v x ∂cellMeasure n) := by
  have hz := integral_coordinate_derivative_eq_zero (u * v) (du * v + u * dv) i
    (fun x t ↦ (hu x t).mul (hv x t))
  have hint (w : C(UnitAddTorus (Fin n), 𝕜)) : Integrable w (cellMeasure n) :=
    w.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change (∫ x, du x * v x + u x * dv x ∂cellMeasure n) = 0 at hz
  have h₁ : Integrable (fun x ↦ du x * v x) (cellMeasure n) := hint (du * v)
  have h₂ : Integrable (fun x ↦ u x * dv x) (cellMeasure n) := hint (u * dv)
  rw [integral_add h₁ h₂] at hz
  exact eq_neg_of_add_eq_zero_right hz

end PDE.Analysis.PeriodicAveraging
