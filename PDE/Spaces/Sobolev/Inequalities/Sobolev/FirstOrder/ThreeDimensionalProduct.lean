/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.IntegralPower
public import PDE.Spaces.Sobolev.Inequalities.Sobolev.HigherOrder.ContinuousEmbedding
public import PDE.Spaces.Sobolev.Inequalities.Sobolev.HigherOrder.Global
import PDE.Analysis.MeasureTheory.Lp.Products
import PDE.Spaces.Sobolev.Inequalities.Ladyzhenskaya.WholeSpace

/-!
# Products of three-dimensional `H¹` functions

Hölder's inequality and the energy form `‖u‖₄ ≤ ½ ‖u‖_{H¹}` of Ladyzhenskaya's inequality give
`‖u v‖₂ ≤ ¼ ‖u‖_{H¹} ‖v‖_{H¹}` for `u, v ∈ H¹(ℝ³)`. The `L⁶` bound of `H¹(ℝ³)`, with the sharp
constant, is `eLpNorm_six_le_ofReal_mul_norm`.
-/

@[expose] public noncomputable section

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace Set
open scoped ENNReal NNReal Sobolev

namespace SobolevSpace.Inequalities

/-- The product of two three-dimensional `H¹` functions is square integrable, with
`‖u v‖₂ ≤ ‖u‖₄ ‖v‖₄ ≤ ¼ ‖u‖_{H¹} ‖v‖_{H¹}` by Hölder's inequality and Ladyzhenskaya's
inequality. -/
theorem eLpNorm_mul_le_H1 (U V : H¹(ℝ^3)) :
    eLpNorm (fun x ↦ baseRepresentative U x * baseRepresentative V x) 2 volume ≤
      ENNReal.ofReal (1 / 4 * ‖U‖ * ‖V‖) := by
  have hfour (W : H¹(ℝ^3)) :
      eLpNorm (baseRepresentative W) 4 volume ≤ ENNReal.ofReal (‖W‖ / 2) := by
    rw [ENNReal.le_ofReal_iff_toReal_le (memLp_four_H1 W).eLpNorm_ne_top (by positivity),
      ← norm_l4EmbeddingThree_apply]
    exact norm_l4EmbeddingThree_apply_le W
  calc eLpNorm (fun x ↦ baseRepresentative U x * baseRepresentative V x) 2 volume
      = eLpNorm (baseRepresentative U • baseRepresentative V) 2 volume := rfl
    _ ≤ eLpNorm (baseRepresentative U) 4 volume * eLpNorm (baseRepresentative V) 4 volume :=
        eLpNorm_smul_le_mul_eLpNorm_of_pos (by norm_num)
    _ ≤ ENNReal.ofReal (‖U‖ / 2) * ENNReal.ofReal (‖V‖ / 2) := by
        gcongr
        · exact hfour U
        · exact hfour V
    _ = ENNReal.ofReal (1 / 4 * ‖U‖ * ‖V‖) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        ring_nf

/-- The product of two three-dimensional `H¹` functions is square integrable, with
`‖u v‖₂ ≤ C ‖u‖_{H¹} ‖v‖_{H¹}`; `eLpNorm_mul_le_H1` gives `C = 1/4`. -/
theorem exists_eLpNorm_mul_le_H1 : ∃ C : ℝ, 0 ≤ C ∧ ∀ U V : H¹(ℝ^3),
    eLpNorm (fun x ↦ baseRepresentative U x * baseRepresentative V x) 2 volume ≤
      ENNReal.ofReal (C * ‖U‖ * ‖V‖) :=
  ⟨1 / 4, by norm_num, eLpNorm_mul_le_H1⟩

end SobolevSpace.Inequalities
