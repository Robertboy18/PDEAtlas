/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Topology.MetricSpace.Contracting

/-!
# A bounded perturbation of a smoothing operator

The Green operator may gain the regularity lost by a bounded transport map.
If the product of their bounds is less than one, the perturbed forced
equation has a unique solution for every forcing, with an explicit norm bound.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.Evolution

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A smoothing map and a bounded derivative-loss perturbation give a unique
forced solution when their operator bounds have product less than one. -/
theorem existsUnique_boundedPerturbation [CompleteSpace E]
    (G : F →L[ℝ] E) (T : E →L[ℝ] F) {g b : ℝ}
    (hg : 0 ≤ g) (hb : 0 ≤ b) (hG : ‖G‖ ≤ g) (hT : ‖T‖ ≤ b)
    (hsmall : g * b < 1) (f : F) :
    ∃! u : E, u = G (f - T u) := by
  let Φ : E → E := fun u ↦ G (f - T u)
  let q : NNReal := ⟨g * b, mul_nonneg hg hb⟩
  have hΦ : ContractingWith q Φ := by
    refine ⟨hsmall, LipschitzWith.of_dist_le_mul fun u v ↦ ?_⟩
    simp only [dist_eq_norm]
    change ‖G (f - T u) - G (f - T v)‖ ≤ (g * b) * ‖u - v‖
    have heq : G (f - T u) - G (f - T v) = -G (T (u - v)) := by
      simp only [map_sub]
      abel
    rw [heq, norm_neg]
    exact (G.le_of_opNorm_le hG _).trans
      ((mul_le_mul_of_nonneg_left (T.le_of_opNorm_le hT _) hg).trans_eq
        (mul_assoc _ _ _).symm)
  refine ⟨hΦ.fixedPoint Φ, hΦ.fixedPoint_isFixedPt.eq.symm, ?_⟩
  intro u hu
  exact hΦ.fixedPoint_unique hu.symm

/-- Every solution obeys the resolvent bound, with the full distance from one. -/
theorem norm_boundedPerturbation_le
    (G : F →L[ℝ] E) (T : E →L[ℝ] F) {g b : ℝ}
    (hg : 0 ≤ g) (hG : ‖G‖ ≤ g) (hT : ‖T‖ ≤ b)
    (hsmall : g * b < 1) {f : F} {u : E} (hu : u = G (f - T u)) :
    ‖u‖ ≤ g * ‖f‖ / (1 - g * b) := by
  have hbound : ‖u‖ ≤ g * ‖f‖ + g * b * ‖u‖ := by
    calc
      ‖u‖ = ‖G (f - T u)‖ := congrArg norm hu
      _ ≤ g * ‖f - T u‖ := G.le_of_opNorm_le hG _
      _ ≤ g * (‖f‖ + ‖T u‖) := mul_le_mul_of_nonneg_left (norm_sub_le _ _) hg
      _ ≤ g * (‖f‖ + b * ‖u‖) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl (T.le_of_opNorm_le hT u)) hg
      _ = _ := by ring
  apply (le_div_iff₀ (sub_pos.mpr hsmall)).mpr
  nlinarith

/-- A perturbation budget at most one half costs at most a factor of two. -/
theorem norm_boundedPerturbation_le_twice
    (G : F →L[ℝ] E) (T : E →L[ℝ] F) {g b : ℝ}
    (hg : 0 ≤ g) (hG : ‖G‖ ≤ g) (hT : ‖T‖ ≤ b)
    (hsmall : g * b ≤ 1 / 2) {f : F} {u : E} (hu : u = G (f - T u)) :
    ‖u‖ ≤ 2 * g * ‖f‖ := by
  have h := norm_boundedPerturbation_le G T hg hG hT (by linarith) hu
  have hgap : 0 < 1 - g * b := by linarith
  have hmul := (le_div_iff₀ hgap).mp h
  nlinarith [mul_nonneg (by linarith : 0 ≤ 1 / 2 - g * b) (norm_nonneg u)]

end PDE.Analysis.Evolution
