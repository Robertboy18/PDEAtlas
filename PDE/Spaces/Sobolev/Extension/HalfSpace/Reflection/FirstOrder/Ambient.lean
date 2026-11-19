/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.FirstOrder.Lp

/-!
# Ambient half-space reflection operator

We define the coordinatewise even and odd reflection map on the
first-order Sobolev derivative bundle.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Universitext,
  Springer, 2011, Chapter 9, for extension by reflection across a flat boundary.
  <https://doi.org/10.1007/978-0-387-70914-7>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace

open Set MeasureTheory Function
open scoped ENNReal Topology

section

namespace Extension

namespace GraphSpace

open SobolevSpace.GraphSpace


namespace HalfSpace

variable (n : ℕ)
variable (p : ℝ≥0∞) [Fact (1 ≤ p)]


section PositiveDimension

variable [Fact (0 < n)]

/-!
## The ambient reflection map on the `PiLp`-bundle of derivatives (`k = 1`)

For `W^{1,p}` we choose:
- the base coordinate (`α = []`) to be the even reflection extension;
- tangential first derivatives (`α = [i]`, `i ≠ lastIndex`) to be even;
- the normal derivative (`α = [lastIndex]`) to be odd.

These are the parities of the reflection lemma (Brezis, Chapter 9). Evans, PDE, §5.4, extends
by a higher-order reflection of `C¹` functions instead.
-/

/-- Extend one `W^{1,p}` graph coordinate by even reflection, except for the normal derivative,
which is extended oddly. -/
noncomputable def extendLpAt (a : DerivIndex n 1) :
    DerivLp n p ℝ^n₊ →L[ℝ] DerivLp n p Set.univ :=
  firstOrderRows
    (_root_.SobolevSpace.HalfSpace.evenExtendLp (n := n) (p := p))
    (fun i ↦
      if i = PDE.Common.lastIndex (n := n) then
        _root_.SobolevSpace.HalfSpace.oddExtendLp (n := n) (p := p)
      else
        _root_.SobolevSpace.HalfSpace.evenExtendLp (n := n) (p := p))
    a

/-- The `PiLp`-bundled ambient extension induced by the coordinatewise reflection maps. -/
noncomputable def extendAmbient :
    WkpAmbientOn n 1 p ℝ^n₊ →L[ℝ] WkpAmbientOn n 1 p Set.univ := by
  classical
  -- `PiLp p β ≃L ∀ i, β i` transports continuous linear maps between the Pi-types.
  let eUpper :
      (WkpAmbientOn n 1 p ℝ^n₊) ≃L[ℝ] (∀ a : DerivIndex n 1, DerivLp n p ℝ^n₊) :=
    PiLp.continuousLinearEquiv (𝕜 := ℝ) (p := p) (β := fun _ : DerivIndex n 1 ↦ DerivLp n p ℝ^n₊)
  let eUniv :
      (WkpAmbientOn n 1 p Set.univ) ≃L[ℝ] (∀ a : DerivIndex n 1, DerivLp n p Set.univ) :=
    PiLp.continuousLinearEquiv (𝕜 := ℝ) (p := p)
      (β := fun _ : DerivIndex n 1 ↦ DerivLp n p Set.univ)
  exact eUniv.symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi fun a ↦
        (extendLpAt (n := n) (p := p) a).comp
          (ContinuousLinearMap.proj a)).comp
      eUpper.toContinuousLinearMap)

/-- Each ambient coordinate is reflected with the parity prescribed for its derivative index. -/
@[simp] theorem extendAmbient_apply (U : WkpAmbientOn n 1 p ℝ^n₊) (a : DerivIndex n 1) :
    extendAmbient (n := n) (p := p) U a = extendLpAt (n := n) (p := p) a (U a) := by
  classical
  -- unfold via the `PiLp`/`WithLp` equivalence
  simp [extendAmbient, extendLpAt]

end PositiveDimension

end HalfSpace

end GraphSpace

end Extension

end

end SobolevSpace
