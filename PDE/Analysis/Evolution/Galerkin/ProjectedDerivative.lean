/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Galerkin.TrialProjection

/-!
# Dual estimates for projected equations

Pivot orthogonality and energy stability control the ambient dual derivative
without an inverse-mass-matrix constant. The argument is pointwise and applies
to both classical and almost-everywhere Galerkin equations.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.Evolution.StableTrialProjection

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {T : GelfandTriple (V := V) (H := H)} {S : Submodule ℝ V} {K : NNReal}

/-- If `⟪ι du, ι v⟫_H + B(u, v) = ℓ(v)` for all `v ∈ S`, then for every `v ∈ V`,
`energyToDual du (v) = ℓ(P v) - B(u, P v)`, where `P` is the energy projection. -/
theorem energyToDual_apply_eq_projected
    (P : StableTrialProjection T S K) {u du : S}
    {B : V →L[ℝ] StrongDual ℝ V} {ell : StrongDual ℝ V}
    (heq : ∀ v : S, inner ℝ (T.inclusion (du : V)) (T.inclusion (v : V)) +
      B (u : V) (v : V) = ell (v : V)) (v : V) :
    T.energyToDual (du : V) v =
      ell (P.energyProjection v : V) - B (u : V) (P.energyProjection v : V) := by
  have hdecomp : T.inclusion v =
      T.inclusion (P.energyProjection v : V) +
        (T.inclusion v - T.inclusion (P.energyProjection v : V)) := by
    abel
  have horth : inner ℝ
      (T.inclusion (du : V))
      (T.inclusion v - T.inclusion (P.energyProjection v : V)) = 0 := by
    simpa only [StableTrialProjection.energyProjection_apply] using
      P.pivotOrthogonal du (T.inclusion v)
  rw [GelfandTriple.energyToDual_apply, hdecomp, inner_add_right, horth, add_zero]
  linarith [heq (P.energyProjection v)]

/-- Under the same equation, `‖energyToDual du‖_{V*} ≤ K (‖ℓ‖ + ‖B‖ ‖u‖_V)`, with `K` the
energy bound of the projection. -/
theorem norm_energyToDual_le_of_projected_equation
    (P : StableTrialProjection T S K) {u du : S}
    {B : V →L[ℝ] StrongDual ℝ V} {ell : StrongDual ℝ V}
    (heq : ∀ v : S, inner ℝ (T.inclusion (du : V)) (T.inclusion (v : V)) +
      B (u : V) (v : V) = ell (v : V)) :
    ‖T.energyToDual (du : V)‖ ≤ (K : ℝ) * (‖ell‖ + ‖B‖ * ‖(u : V)‖) := by
  apply ContinuousLinearMap.opNorm_le_bound _
  · exact mul_nonneg K.coe_nonneg
      (add_nonneg (norm_nonneg (ell))
        (mul_nonneg (norm_nonneg (B)) (norm_nonneg (u : V))))
  · intro v
    rw [P.energyToDual_apply_eq_projected heq v]
    calc
      ‖ell (P.energyProjection v : V) -
          B (u : V) (P.energyProjection v : V)‖
          ≤ ‖ell (P.energyProjection v : V)‖ +
            ‖B (u : V) (P.energyProjection v : V)‖ := norm_sub_le _ _
      _ ≤ ‖ell‖ * ‖P.energyProjection v‖ +
            (‖B‖ * ‖(u : V)‖) * ‖P.energyProjection v‖ := by
          apply add_le_add
          · exact (ell).le_opNorm _
          · exact ((B (u : V)).le_opNorm (P.energyProjection v : V)).trans
              (mul_le_mul_of_nonneg_right ((B).le_opNorm (u : V))
                (norm_nonneg _))
      _ = (‖ell‖ + ‖B‖ * ‖(u : V)‖) * ‖P.energyProjection v‖ := by
          ring
      _ ≤ (‖ell‖ + ‖B‖ * ‖(u : V)‖) * ((K : ℝ) * ‖v‖) :=
          mul_le_mul_of_nonneg_left (P.norm_le v)
            (add_nonneg (norm_nonneg _)
              (mul_nonneg (norm_nonneg (B)) (norm_nonneg (u : V))))
      _ = ((K : ℝ) * (‖ell‖ + ‖B‖ * ‖(u : V)‖)) *
          ‖v‖ := by
          ring

end PDE.Analysis.Evolution.StableTrialProjection
