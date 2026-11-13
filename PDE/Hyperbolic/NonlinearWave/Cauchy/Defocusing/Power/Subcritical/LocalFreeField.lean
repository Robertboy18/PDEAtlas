/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Kirchhoff.Family
public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.LocalPower.ConeSolution

/-!
# Full Cauchy data on normalized backward cones

Restriction of a physical field to a normalized cone preserves finite
regularity in the time and center parameters. Applying this to the
Kirchhoff field supplies arbitrary displacement and velocity, together with
both initial traces. Only C² displacement and C¹ velocity are needed here.
-/

@[expose] public noncomputable section

open Set BoundedContinuousFunction PDE.Analysis PDE.Common WaveEquation
open WaveEquation.SmallData.Classical.LocalPower

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- The inclusion of the compact normalized cone as a bounded continuous map. -/
def coneCoordinates : Cone →ᵇ (ℝ × ℝ^3) :=
  mkOfCompact ⟨Subtype.val, continuous_subtype_val⟩

/-- A physical field evaluated simultaneously at every point of a backward cone. -/
def coneField (H : C(ℝ × ℝ^3, ℝ)) (p : ℝ × ℝ^3) : Cone →ᵇ ℝ :=
  composeCompact H (constCLM Cone ℝ (ℝ × ℝ^3) (0, p.2) + p.1 • coneCoordinates)

/-- The cone field is literal evaluation at the associated physical point. -/
@[simp] theorem coneField_apply (H : C(ℝ × ℝ^3, ℝ)) (p : ℝ × ℝ^3) (q : Cone) :
    coneField H p q = H (physicalPoint p q) := by
  simp only [coneField, composeCompact_apply, BoundedContinuousFunction.add_apply,
    constCLM_apply, const_apply, BoundedContinuousFunction.smul_apply,
    coneCoordinates, mkOfCompact_apply]
  congr 1
  ext <;> simp [physicalPoint, coneTime, coneSpace]

/-- Restricting a physical field to a subcone changes only its time and center. -/
theorem restrictCone_coneField (H : C(ℝ × ℝ^3, ℝ)) (p : ℝ × ℝ^3) (q : Cone) :
    restrictCone q (coneField H p) = coneField H (physicalPoint p q) := by
  ext r
  simp only [restrictCone_apply, coneField_apply]
  congr 1
  ext <;> simp [physicalPoint, coneTime_descend, coneSpace_descend,
    mul_assoc, smul_add, smul_smul, add_assoc]

/-- Joint finite regularity survives restriction to the compact cone in the
uniform function-space norm. -/
theorem contDiff_coneField {k : ℕ} {H : ℝ × ℝ^3 → ℝ} (hH : ContDiff ℝ k H) :
    ContDiff ℝ k (coneField ⟨H, hH.continuous⟩) := by
  apply (contDiff_composeCompact hH).comp
  exact ((constCLM Cone ℝ (ℝ × ℝ^3)).contDiff.comp
    (contDiff_const.prodMk contDiff_snd)).add (contDiff_fst.smul contDiff_const)

/-- A physical bound on a forward strip bounds every cone field in that strip. -/
theorem norm_coneField_le {H : C(ℝ × ℝ^3, ℝ)} {B S : ℝ}
    (hB : 0 ≤ B) (hbound : ∀ p : ℝ × ℝ^3, p.1 ∈ Icc 0 S → |H p| ≤ B)
    {p : ℝ × ℝ^3} (hp : p.1 ∈ Icc 0 S) : ‖coneField H p‖ ≤ B := by
  refine (BoundedContinuousFunction.norm_le hB).mpr fun q ↦ ?_
  rw [coneField_apply, Real.norm_eq_abs]
  apply hbound
  exact ⟨mul_nonneg hp.1 (coneTime_mem q).1,
    (mul_le_mul_of_nonneg_left (coneTime_mem q).2 hp.1).trans (by simpa using hp.2)⟩


end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
