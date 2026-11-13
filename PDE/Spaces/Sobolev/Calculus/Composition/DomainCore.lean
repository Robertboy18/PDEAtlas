/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.GraphSpace.Operator.Basic
import PDE.Spaces.Sobolev.Approximation.Density.Global

/-!
# Finite-measure domain composition: constants and restriction

We restrict a given extension back to its domain, restore constants, and
record coordinate formulas for sums.

The extension-based constructions in `Composition.DomainTruncation` and
`Composition.FiniteProduct.Domain` extend `u ∈ W^{1,p}(Ω)` to `ℝ^n`,
apply the whole-space theorem to the
centered map `x ↦ F x - F 0`, restrict back to `Ω`, and add the constant
`F 0`. The last step needs `Ω` to have finite measure, so that constants lie
in `Lᵖ(Ω)` and hence in `W^{1,p}(Ω)` with vanishing derivative coordinates.
The lemmas here keep the almost-everywhere coordinate formulas together.
The arbitrary-open-domain Lipschitz chain rule instead uses the local cutoff
argument in `Composition.OpenDomainLipschitz`.

## Main results

* `restrictExtension`, `restrictExtension_eq`: restricting a global extension of `U` back to
  `Ω` gives back `U`.
* `coordinate_add_ae`: coordinates of a sum add almost everywhere.
* `restrictAndRestoreConstant` with its `_base_ae` and `_derivative_ae` lemmas: restrict a
  global element to `Ω` and add a constant, tracking every coordinate.
* `extension_coordinate_ae`: every coordinate of an extension of `U` agrees a.e. on `Ω` with
  the corresponding coordinate of `U`, not only the base coordinate demanded by the
  extension interface.
-/

@[expose] public section

noncomputable section

set_option linter.missingDocs true

namespace SobolevSpace.GraphSpace

/-- Recenter a scalar map so that it fixes zero. -/
abbrev centered (F : ℝ → ℝ) : ℝ → ℝ :=
  fun x ↦ F x - F 0

/-- Recentering preserves the Lipschitz constant. -/
theorem centered_lipschitzWith {F : ℝ → ℝ} {C : NNReal} (hF : LipschitzWith C F) :
    LipschitzWith C (centered F) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  simpa [centered, dist_sub_right] using hF.dist_le_mul x y

end SobolevSpace.GraphSpace

namespace SobolevSpace.GraphSpace.DomainComposition

open MeasureTheory Set ENNReal
open scoped Sobolev

variable {n : ℕ} {p : ℝ≥0∞}
    {Ω : Set (ℝ^n)} [IsFiniteMeasure (domainMeasure n Ω)]

variable [Fact (1 ≤ p)]

/-- Restrict a supplied global extension back to its source domain. -/
noncomputable def restrictExtension
    (hΩ : IsOpen Ω) (E : Extension.GraphSpace.Operator n 1 p Ω)
    (U : W^{1,p}(Ω)) :
    W^{1,p}(Ω) :=
  restrictCLM hΩ.measurableSet (subset_univ Ω)
    (E.toContinuousLinearMap U)

omit [IsFiniteMeasure (domainMeasure n Ω)] in
/-- Restricting an extension back to its source domain recovers the original
Sobolev element. -/
theorem restrictExtension_eq
    (hΩ : IsOpen Ω) (E : Extension.GraphSpace.Operator n 1 p Ω)
    (U : W^{1,p}(Ω)) :
    restrictExtension hΩ E U = U := by
  apply WkpSpaceOn.ext_of_base_ae hΩ
  exact
    (restrictCLM_apply_ae
      (n := n) (k := 1) (p := p)
      hΩ.measurableSet (subset_univ Ω)
      (E.toContinuousLinearMap U) (baseIndex n 1)).trans
      (E.agree_ae U)

omit [IsFiniteMeasure (domainMeasure n Ω)] [Fact (1 ≤ p)] in
/-- Coordinates of a sum of Sobolev graph-space elements add pointwise
almost everywhere. -/
theorem coordinate_add_ae
    (V W : W^{1,p}(Ω)) (a : DerivIndex n 1) :
    ((((V + W : W^{1,p}(Ω)) : WkpAmbientOn n 1 p Ω) a :
        DerivLp n p Ω) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω]
        fun x ↦
          (((V : WkpAmbientOn n 1 p Ω) a :
            DerivLp n p Ω) : ℝ^n → ℝ) x +
          (((W : WkpAmbientOn n 1 p Ω) a :
            DerivLp n p Ω) : ℝ^n → ℝ) x := by
  have hcoord :
      (((V + W : W^{1,p}(Ω)) : WkpAmbientOn n 1 p Ω) a :
          DerivLp n p Ω) =
        ((V : WkpAmbientOn n 1 p Ω) a : DerivLp n p Ω) +
          ((W : WkpAmbientOn n 1 p Ω) a : DerivLp n p Ω) := rfl
  rw [hcoord]
  exact MeasureTheory.Lp.coeFn_add _ _

/-- Restrict a global first-order Sobolev element to an open finite-measure
domain and then restore a constant. This is the common domain-level
construction behind centered smooth composition, Lipschitz composition, and
interval truncation. -/
noncomputable def restrictAndRestoreConstant
    (hΩ : IsOpen Ω) (V : W^{1,p}(ℝ^n)) (c : ℝ) :
    W^{1,p}(Ω) :=
  restrictCLM hΩ.measurableSet (subset_univ Ω) V + wkpConstant c

/-- The base coordinate of `restrictAndRestoreConstant` is the restricted
global base coordinate plus the restored constant. -/
theorem restrictAndRestoreConstant_base_ae
    (hΩ : IsOpen Ω) (V : W^{1,p}(ℝ^n)) (c : ℝ) :
    ((((restrictAndRestoreConstant hΩ V c :
        WkpAmbientOn n 1 p Ω) (baseIndex n 1) : DerivLp n p Ω) :
      ℝ^n → ℝ))
      =ᵐ[domainMeasure n Ω] fun x ↦
        (((V : WkpAmbientOn n 1 p Set.univ)
          (baseIndex n 1) : DerivLp n p Set.univ) : ℝ^n → ℝ) x + c := by
  let R : W^{1,p}(Ω) :=
    restrictCLM hΩ.measurableSet (subset_univ Ω) V
  let C : W^{1,p}(Ω) := wkpConstant c
  have hadd := coordinate_add_ae R C (baseIndex n 1)
  have hrestrict :=
    restrictCLM_apply_ae
      (n := n) (k := 1) (p := p)
      hΩ.measurableSet (subset_univ Ω) V (baseIndex n 1)
  have hconst : ((C : WkpAmbientOn n 1 p Ω) (baseIndex n 1) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] fun _ ↦ c :=
    wkpConstant_base_ae (n := n) (p := p) (Ω := Ω) c
  filter_upwards [hadd, hrestrict, hconst] with x hxadd hxrestrict hxconst
  change
    ((((restrictAndRestoreConstant hΩ V c :
      WkpAmbientOn n 1 p Ω) (baseIndex n 1) :
        DerivLp n p Ω) : ℝ^n → ℝ) x) = _
  change
    (((((R + C : W^{1,p}(Ω)) : WkpAmbientOn n 1 p Ω)
      (baseIndex n 1) : DerivLp n p Ω) : ℝ^n → ℝ) x) = _
  rw [hxadd, hxrestrict, hxconst]

/-- Restoring a constant does not change first derivative coordinates. -/
theorem restrictAndRestoreConstant_derivative_ae
    (hΩ : IsOpen Ω) (V : W^{1,p}(ℝ^n)) (c : ℝ)
    (i : Fin n) :
    ((((restrictAndRestoreConstant hΩ V c :
        WkpAmbientOn n 1 p Ω) (singleDerivIndex n i) :
          DerivLp n p Ω) : ℝ^n → ℝ))
      =ᵐ[domainMeasure n Ω]
        (((V : WkpAmbientOn n 1 p Set.univ)
          (singleDerivIndex n i) : DerivLp n p Set.univ) : ℝ^n → ℝ) := by
  let R : W^{1,p}(Ω) :=
    restrictCLM hΩ.measurableSet (subset_univ Ω) V
  let C : W^{1,p}(Ω) := wkpConstant c
  have hadd := coordinate_add_ae R C (singleDerivIndex n i)
  have hrestrict :=
    restrictCLM_apply_ae
      (n := n) (k := 1) (p := p)
      hΩ.measurableSet (subset_univ Ω) V (singleDerivIndex n i)
  have hconst :=
    wkpConstant_deriv_ae (n := n) (p := p) (Ω := Ω) c i
  filter_upwards [hadd, hrestrict, hconst] with x hxadd hxrestrict hxconst
  change
    ((((restrictAndRestoreConstant hΩ V c :
      WkpAmbientOn n 1 p Ω) (singleDerivIndex n i) :
        DerivLp n p Ω) : ℝ^n → ℝ) x) = _
  change
    (((((R + C : W^{1,p}(Ω)) : WkpAmbientOn n 1 p Ω)
      (singleDerivIndex n i) : DerivLp n p Ω) : ℝ^n → ℝ) x) = _
  rw [hxadd, hxrestrict, hxconst]
  simp

omit [IsFiniteMeasure (domainMeasure n Ω)] in
/-- Every coordinate of a supplied extension agrees almost everywhere on the
source domain with the corresponding coordinate of the original Sobolev
element. Agreement of the base coordinate is part of the extension
interface; open-domain weak-derivative uniqueness supplies all other
coordinates. -/
theorem extension_coordinate_ae
    (hΩ : IsOpen Ω) (E : Extension.GraphSpace.Operator n 1 p Ω)
    (U : W^{1,p}(Ω)) (a : DerivIndex n 1) :
    ((((E.toContinuousLinearMap U : WkpAmbientOn n 1 p Set.univ) a :
        DerivLp n p Set.univ) : ℝ^n → ℝ))
      =ᵐ[domainMeasure n Ω]
        (((U : WkpAmbientOn n 1 p Ω) a : DerivLp n p Ω) :
          ℝ^n → ℝ) := by
  have hcoordinate :=
    restrictCLM_apply_ae
      (n := n) (k := 1) (p := p)
      hΩ.measurableSet (subset_univ Ω)
      (E.toContinuousLinearMap U) a
  change
    ((((restrictExtension hΩ E U : WkpAmbientOn n 1 p Ω) a :
        DerivLp n p Ω) : ℝ^n → ℝ))
      =ᵐ[domainMeasure n Ω] _ at hcoordinate
  rw [restrictExtension_eq hΩ E U] at hcoordinate
  exact hcoordinate.symm

end SobolevSpace.GraphSpace.DomainComposition
