/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.HigherOrderRegularity
public import PDE.Spaces.Sobolev.Evolution.HigherOrder.WholeSpaceTriple

/-!
# Pairing a mollified L² field against H¹

Integration by parts moves the H¹ derivatives onto the smoothed test state.
The identity is valid for arbitrary H¹ and L² inputs, by density of H² in H¹.
It avoids a scale-dependent H¹ estimate on the forcing.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Approximation

open GraphSpace
open scoped ENNReal InnerProductSpace Sobolev

variable {n : ℕ}

/-- The operator `1 - Δ` commutes with the graph mollifier. -/
theorem identitySubLaplacianCLM_mollifierHkCLM
    (μ : Mollifier n) {δ : ℝ} (hδ : 0 < δ) (U : W^{2,2}(ℝ^n)) :
    identitySubLaplacianCLM n (mollifierHkCLM μ hδ U) =
      mollifierRowCLM μ hδ (identitySubLaplacianCLM n U) := by
  simp [identitySubLaplacianCLM, sub_apply, sum_apply]

/-- The H¹ pairing with smoothed L² forcing equals an L² pairing with
`(1 - Δ) Jδ U`, for every H¹ state `U`. -/
theorem inner_mollifierSmoothingCLM_one {δ : ℝ} (hδ : 0 < δ)
    (U : W^{1,2}(ℝ^n)) (F : DerivLp n 2 Set.univ) :
    ⟪U, mollifierSmoothingCLM 1 (standardMollifier n) hδ F⟫_ℝ =
      ⟪identitySubLaplacianCLM n
        (mollifierSmoothingCLM 2 (standardMollifier n) hδ
          (wkpBaseCoordinateCLM U)), F⟫_ℝ := by
  have hd := denseRange_lowerOrderCLM (n := n) (show 1 ≤ 2 by omega)
    (p := 2) (by norm_num)
  refine hd.induction_on (p := fun W ↦
    ⟪W, mollifierSmoothingCLM 1 (standardMollifier n) hδ F⟫_ℝ =
      ⟪identitySubLaplacianCLM n
        (mollifierSmoothingCLM 2 (standardMollifier n) hδ
          (wkpBaseCoordinateCLM W)), F⟫_ℝ) U ?_ ?_
  · exact isClosed_eq
      (continuous_id.inner continuous_const)
      (((identitySubLaplacianCLM n).continuous.comp
        ((mollifierSmoothingCLM 2 (standardMollifier n) hδ).continuous.comp
          wkpBaseCoordinateCLM.continuous)).inner continuous_const)
  · intro V
    rw [← lowerOrderCLM_mollifierSmoothingCLM (show 1 ≤ 2 by omega)]
    rw [real_inner_comm, inner_lowerOrder_eq_identitySubLaplacian,
      mollifierSmoothingCLM_base, inner_standardMollifierRowCLM_left,
      real_inner_comm, ← identitySubLaplacianCLM_mollifierHkCLM,
      ← mollifierSmoothingCLM_baseCoordinate]
    rfl

end SobolevSpace.Approximation
