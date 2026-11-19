/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import PDE.Common.Euclidean

/-!
# Mean of a periodic gradient

Translation invariance of normalized Haar measure makes the integral of a periodic
function constant along each coordinate flow. Differentiation under the integral,
justified by compactness and continuity of the gradient, gives zero mean derivative.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace PDE.Analysis.PeriodicAveraging

/-- The normalized product Haar measure on the unit torus. -/
def cellMeasure (n : ℕ) : Measure (UnitAddTorus (Fin n)) :=
  Measure.pi (fun _ : Fin n ↦ AddCircle.haarAddCircle)

/-- The periodic cell has unit measure. -/
instance cellMeasure_probability (n : ℕ) : IsProbabilityMeasure (cellMeasure n) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n ↦ AddCircle.haarAddCircle)))

/-- Translation preserves the periodic cell measure. -/
instance cellMeasure_addInvariant (n : ℕ) : (cellMeasure n).IsAddRightInvariant :=
  inferInstanceAs ((Measure.pi (fun _ : Fin n ↦ AddCircle.haarAddCircle)).IsAddRightInvariant)

/-- Translation in one coordinate of the unit torus. -/
def coordinateShift {n : ℕ} (i : Fin n) (t : ℝ) : UnitAddTorus (Fin n) :=
  Pi.single i (t : UnitAddCircle)

/-- Translation by zero fixes each coordinate. -/
@[simp] theorem coordinateShift_zero {n : ℕ} (i : Fin n) : coordinateShift i 0 = 0 := by
  simp [coordinateShift]

/-- The integral of each coordinate derivative of a periodic potential is zero. -/
theorem integral_gradient_coordinate_eq_zero {n : ℕ}
    (u : C(UnitAddTorus (Fin n), ℝ)) (g : C(UnitAddTorus (Fin n), ℝ^n))
    (hd : ∀ (x : UnitAddTorus (Fin n)) (i : Fin n) (t : ℝ),
      HasDerivAt (fun s ↦ u (x + coordinateShift i s))
        (g (x + coordinateShift i t) i) t) (i : Fin n) :
    (∫ x, g x i ∂cellMeasure n) = 0 := by
  let F : ℝ → UnitAddTorus (Fin n) → ℝ := fun t x ↦ u (x + coordinateShift i t)
  let F' : ℝ → UnitAddTorus (Fin n) → ℝ := fun t x ↦ g (x + coordinateShift i t) i
  have hFc (t : ℝ) : Continuous (F t) := u.continuous.comp (continuous_id.add continuous_const)
  have hGc (t : ℝ) : Continuous (F' t) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp
      (g.continuous.comp (continuous_id.add continuous_const))
  have hFint : Integrable (F 0) (cellMeasure n) :=
    (hFc 0).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hbound : ∀ᵐ x ∂cellMeasure n, ∀ t ∈ (univ : Set ℝ), ‖F' t x‖ ≤ ‖g‖ := by
    exact Eventually.of_forall fun x t _ ↦
      (PiLp.norm_apply_le (g (x + coordinateShift i t)) i).trans (g.norm_coe_le_norm _)
  have hdiff := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := cellMeasure n) (x₀ := (0 : ℝ)) (s := univ) (F := F) (F' := F')
    (bound := fun _ ↦ ‖g‖) (univ_mem : univ ∈ 𝓝 (0 : ℝ))
    (Eventually.of_forall fun t ↦ (hFc t).aestronglyMeasurable) hFint
    (hGc 0).aestronglyMeasurable hbound (integrable_const ‖g‖)
    (Eventually.of_forall fun x t _ ↦ hd x i t)
  have hconstant : (fun t ↦ ∫ x, F t x ∂cellMeasure n) =
      fun _ : ℝ ↦ ∫ x, u x ∂cellMeasure n :=
    funext fun t ↦ integral_add_right_eq_self u (coordinateShift i t)
  have hzero : HasDerivAt (fun t ↦ ∫ x, F t x ∂cellMeasure n) 0 0 := by
    rw [hconstant]
    exact hasDerivAt_const _ _
  simpa [F'] using hdiff.2.unique hzero

end PDE.Analysis.PeriodicAveraging
