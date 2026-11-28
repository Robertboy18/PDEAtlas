/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.WeakDerivative
import PDE.Analysis.MeasureTheory.LpNorm

/-!
# Forward differences of functions in the class of a Sobolev element

The bound `‖D_h U‖_p ≤ ‖∂ₗU‖_p` of `norm_differenceQuotientLp_base_le_deriv_of_ne_top` is about
the `Lᵖ` class of a member `U` of `W^{1,p}(ℝⁿ)`. Here it is stated for a function `f` in that
class and its forward difference `D_h f = h⁻¹ (f(· + h eₗ) - f)`, for every finite `p`,
every direction `l` and every `h ≠ 0`. The forward difference of a representative is a
representative of the `Lᵖ` difference quotient (`differenceQuotientLp_apply_ae`), and it
depends only on the class of the function (`forwardDifference_congr_ae`). Hou, Wang and Yang use
the bound in this form for the difference quotients in the proof of their Proposition 3.

## Main results

* `forwardDifference_congr_ae`: forward differences of functions that agree almost everywhere
  agree almost everywhere.
* `lpNorm_forwardDifference_le`: `‖D_h f‖_p ≤ ‖∂ₗU‖_p` for every `f` in the class of `U`.

## References

* T. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116, the difference quotients in the
  proof of Proposition 3. <https://arxiv.org/abs/2509.25116>
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal Sobolev

namespace SobolevSpace.GraphSpace.DifferenceQuotient

variable {n : ℕ}

/-- Forward differences of functions that agree almost everywhere agree almost everywhere. -/
theorem forwardDifference_congr_ae {f g : ℝ^n → ℝ} (hfg : f =ᵐ[volume] g) (l : Fin n)
    (h : ℝ) : forwardDifference l h f =ᵐ[volume] forwardDifference l h g := by
  have hτ : (fun y ↦ f (y + coordinateStep l h)) =ᵐ[volume]
      fun y ↦ g (y + coordinateStep l h) :=
    (measurePreserving_add_right volume (coordinateStep l h)).quasiMeasurePreserving.ae_eq_comp
      hfg
  filter_upwards [hτ, hfg] with y h1 h2
  simp only [forwardDifference, h1, h2]

/-- **The difference quotient bound for functions**: if `f` is in the class of
`U ∈ W^{1,p}(ℝⁿ)` with `p` finite and `h ≠ 0`, then `‖D_h f‖_p ≤ ‖∂ₗU‖_p` for the forward
difference in the direction `eₗ`. -/
theorem lpNorm_forwardDifference_le {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (U : W^{1,p}(ℝ^n)) {f : ℝ^n → ℝ} (hf : baseRepresentative U =ᵐ[volume] f) (l : Fin n)
    {h : ℝ} (hh : h ≠ 0) :
    lpNorm (forwardDifference l h f) p volume ≤
      ‖wkpCoordinateCLM (singleDerivIndex n l) U‖ := by
  have h1 := differenceQuotientLp_apply_ae p l h (wkpBaseCoordinateCLM U)
  have h2 : (differenceQuotientLp p l h (wkpBaseCoordinateCLM U) : ℝ^n → ℝ) =ᵐ[volume]
      forwardDifference l h f := h1.trans (forwardDifference_congr_ae hf l h)
  have h3 := Lp.lpNorm_eq_norm_of_ae_eq (differenceQuotientLp p l h (wkpBaseCoordinateCLM U))
    (by simpa only [domainMeasure, Measure.restrict_univ] using h2)
  simp only [domainMeasure, Measure.restrict_univ] at h3
  rw [h3]
  exact norm_differenceQuotientLp_base_le_deriv_of_ne_top p hp l hh U

end SobolevSpace.GraphSpace.DifferenceQuotient
