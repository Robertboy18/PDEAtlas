/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Model.Notation

/-!
# Weighted measures and Sobolev coordinates

A nonnegative density `w` replaces the domain measure `μ` by `μ.withDensity w`, so weighted
Sobolev coordinates live in Mathlib's measure-parametric `Lp` theory. The weighted measure,
`Lp`, `MemLp`, Hölder, and multiplication lemmas are Mathlib's; we add only predicates about
the weak-derivative coordinates of `WkpSpaceOn`.

The definitions impose no doubling, Muckenhoupt, or Poincaré hypothesis on the weight; such
assumptions belong to the theorems that need them, as in the classical weighted theory of
Muckenhoupt, Caffarelli-Kohn-Nirenberg, Fabes-Kenig-Serapioni, and Kufner.

## References

* B. Muckenhoupt, "Weighted norm inequalities for the Hardy maximal function",
  *Trans. Amer. Math. Soc.* 165 (1972), 207-226, for the condition on a weight under which the Hardy
  maximal function is bounded on the weighted `Lᵖ` space.
  <https://doi.org/10.1090/S0002-9947-1972-0293384-6>
* L. Caffarelli, R. Kohn and L. Nirenberg, "First order interpolation inequalities with weights",
  *Compositio Math.* 53 (1984), no. 3, 259-275, for interpolation inequalities between a function
  and its gradient with power weights `|x|^a`.
  <https://www.numdam.org/item/CM_1984__53_3_259_0/>
* E. B. Fabes, C. E. Kenig and R. P. Serapioni, "The local regularity of solutions of degenerate
  elliptic equations", *Comm. Partial Differential Equations* 7 (1982), no. 1, 77-116.
  <https://doi.org/10.1080/03605308208820218>
* A. Kufner, *Weighted Sobolev Spaces*, Teubner-Texte zur Mathematik 31, Teubner, Leipzig, 1981.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Sobolev

namespace SobolevSpace
namespace Weighted

variable {n k : ℕ} {p : ℝ≥0∞} {Ω : Set (ℝ^n)}

/-- One Sobolev graph coordinate belongs to `L^p(w dx)`.

The underlying weak-derivative graph is the unweighted `WkpSpaceOn`; this predicate adds a
weighted integrability condition. -/
def CoordinateMemLpWithDensity (w : ℝ^n → ℝ≥0∞)
    (U : W^{k,p}(Ω))
    (a : GraphSpace.DerivIndex n k) : Prop :=
  MemLp
    (((U : GraphSpace.WkpAmbientOn n k p Ω) a : GraphSpace.DerivLp n p Ω) :
      ℝ^n → ℝ)
    p ((domainMeasure n Ω).withDensity w)

/-- Every coordinate of a Sobolev graph bundle satisfies the same density-weighted `L^p`
estimate. -/
def CoordinatesMemLpWithDensity (w : ℝ^n → ℝ≥0∞)
    (U : W^{k,p}(Ω)) : Prop :=
  ∀ a : GraphSpace.DerivIndex n k, CoordinateMemLpWithDensity w U a

/-- Coordinate membership is monotone under almost-everywhere domination of densities. -/
theorem CoordinateMemLpWithDensity.mono_density
    {w v : ℝ^n → ℝ≥0∞}
    {U : W^{k,p}(Ω)}
    {a : GraphSpace.DerivIndex n k}
    (hU : CoordinateMemLpWithDensity v U a)
    (hwv : w ≤ᵐ[domainMeasure n Ω] v) :
    CoordinateMemLpWithDensity w U a :=
  hU.mono_measure (withDensity_mono hwv)

/-- Simultaneous coordinate membership is monotone in the density. -/
theorem CoordinatesMemLpWithDensity.mono_density
    {w v : ℝ^n → ℝ≥0∞}
    {U : W^{k,p}(Ω)}
    (hU : CoordinatesMemLpWithDensity v U)
    (hwv : w ≤ᵐ[domainMeasure n Ω] v) :
    CoordinatesMemLpWithDensity w U :=
  fun a ↦ CoordinateMemLpWithDensity.mono_density (hU a) hwv

end Weighted
end SobolevSpace
