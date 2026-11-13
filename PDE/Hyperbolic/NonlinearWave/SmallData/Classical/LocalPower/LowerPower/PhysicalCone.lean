/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.LocalPower.ConeSolution

/-!
# Restricting an integral solution to its physical cones

A continuous solution of Kirchhoff's integral equation restricts to a
solution of the normalized equation on every compact backward cone.
The restrictions depend continuously on the vertex in the uniform norm.
These facts apply directly to the constructed C¹ solution.
-/

@[expose] public noncomputable section

open Set MeasureTheory BoundedContinuousFunction PDE.Analysis
open scoped unitInterval

namespace WaveEquation.SmallData.Classical.LocalPower.LowerPower

/-- The physical cone parametrization is jointly continuous in its vertex
and normalized cone point. -/
theorem continuous_physicalPoint :
    Continuous (fun z : (ℝ × ℝ^3) × Cone ↦ physicalPoint z.1 z.2) :=
  (continuous_fst.fst.mul (continuous_subtype_val.fst.comp continuous_snd)).prodMk
    (continuous_fst.snd.add
      (continuous_fst.fst.smul (continuous_subtype_val.snd.comp continuous_snd)))

/-- Physical evaluation respects the affine cone restrictions. -/
theorem physicalPoint_descend (q : ℝ × ℝ^3) (r s : Cone) :
    physicalPoint q (descend r s) = physicalPoint (physicalPoint q r) s := by
  apply Prod.ext
  · exact (mul_assoc _ _ _).symm
  · change q.2 + q.1 • (coneSpace r + coneTime r • coneSpace s) =
      q.2 + q.1 • coneSpace r + (q.1 * coneTime r) • coneSpace s
    rw [smul_add, smul_smul, add_assoc]

/-- A continuous spacetime field restricted to a compact physical cone,
with the uniform norm on cone fields. -/
def physicalCone {T : ℝ} {v : ℝ × ℝ^3 → ℝ}
    (hv : ContinuousOn v {q | |q.1| < T})
    (q : {q : ℝ × ℝ^3 | |q.1| < T}) : Cone →ᵇ ℝ :=
  mkOfCompact ⟨fun r ↦ v (physicalPoint q.1 r),
    hv.comp_continuous
      (continuous_physicalPoint.comp (continuous_const.prodMk continuous_id))
      (fun r ↦ (abs_physicalPoint_time_le q.1 r).trans_lt q.2)⟩

/-- Evaluation of a physical cone field is literal spacetime evaluation. -/
@[simp] theorem physicalCone_apply {T : ℝ} {v : ℝ × ℝ^3 → ℝ}
    (hv : ContinuousOn v {q | |q.1| < T})
    (q : {q : ℝ × ℝ^3 | |q.1| < T}) (r : Cone) :
    physicalCone hv q r = v (physicalPoint q.1 r) := rfl

/-- Compactness of the normalized cone upgrades joint continuity to
continuity in its uniform function-space norm. -/
theorem continuous_physicalCone {T : ℝ} {v : ℝ × ℝ^3 → ℝ}
    (hv : ContinuousOn v {q | |q.1| < T}) : Continuous (physicalCone hv) := by
  let F : {q : ℝ × ℝ^3 | |q.1| < T} → C(Cone, ℝ) := fun q ↦ (physicalCone hv q).toContinuousMap
  have hF : Continuous F := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact hv.comp_continuous (continuous_physicalPoint.comp
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd))
      (fun z ↦ (abs_physicalPoint_time_le z.1.1 z.2).trans_lt z.1.2)
  exact (ContinuousMap.isometryEquivBoundedOfCompact Cone ℝ).continuous.comp hF

/-- A spacetime integral equation gives the normalized equation on the
whole physical cone, including all its smaller cones. -/
theorem physicalCone_eq_of_integral_eq {T : ℝ} {v : ℝ × ℝ^3 → ℝ}
    (hv : ContinuousOn v {q | |q.1| < T}) (f : C(ℝ, ℝ)) (g : C(ℝ^3, ℝ))
    (heq : ∀ q : ℝ × ℝ^3, |q.1| < T → v q = q.1 * unitSphereAverage 3 g q.2 q.1 + q.1 ^ 2 * ∫ s : I,
      (1 - (s : ℝ)) * ((∫ ω : Direction, f (v (q.1 * (s : ℝ), q.2 + q.1 •
      ((1 - (s : ℝ)) • (ω : ℝ^3)))) ∂((volume : Measure (ℝ^3)).toSphere)) / unitSphereArea 3))
    (q : {q : ℝ × ℝ^3 | |q.1| < T}) :
    physicalCone hv q = freeField g q.1 +
      q.1.1 ^ 2 • duhamelOperator (composeCompact f (physicalCone hv q)) := by
  ext r
  have hr := heq (physicalPoint q.1 r) ((abs_physicalPoint_time_le q.1 r).trans_lt q.2)
  rw [physicalCone_apply, hr]
  simp only [BoundedContinuousFunction.add_apply, BoundedContinuousFunction.smul_apply,
    freeField_apply, duhamelOperator_apply, composeCompact_apply, physicalCone_apply,
    physicalPoint_descend, smul_eq_mul]
  change (q.1.1 * coneTime r) * unitSphereAverage 3 g
      (q.1.2 + q.1.1 • coneSpace r) (q.1.1 * coneTime r) + (q.1.1 * coneTime r) ^ 2 * _ = _
  congr 1
  simp only [physicalPoint, rim, coneTime, coneSpace, mul_pow, mul_assoc]

end WaveEquation.SmallData.Classical.LocalPower.LowerPower
