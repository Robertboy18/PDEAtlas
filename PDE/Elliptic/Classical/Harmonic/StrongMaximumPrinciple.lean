/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.MeanValue.MaximumPrinciple
public import PDE.Elliptic.Classical.MeanValue.PDEToMeanValue

/-!
# Strong maximum principle for harmonic functions

Harmonicity supplies the sphere mean-value property; the topological rigidity
argument is in `PDE.Elliptic.Classical.MeanValue.MaximumPrinciple`. The statement is
Evans's Theorem 4 (ii) of §2.2.3 and its minimum version; the domain need not be bounded, and
nothing is assumed at its boundary.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.3, Theorem 4 (Strong maximum principle) (ii), p. 27.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace LaplacianEquation

/-- Strong maximum principle in Evans' global-maximum form.

If a PDE-harmonic function on a connected open domain attains its domain-wide
maximum at an interior point, then it is constant throughout the domain. -/
theorem IsHarmonicPDE.eqOn_const_of_isPreconnected_of_forall_le
    {n : ℕ} [Fact (0 < n)]
    {u : ℝ^n → ℝ} {U : Set (ℝ^n)}
    (hu : IsHarmonicPDE n u U)
    (hUopen : IsOpen U) (hUconn : IsPreconnected U)
    {x₀ : ℝ^n} (hx₀ : x₀ ∈ U)
    (hmax : ∀ y ∈ U, u y ≤ u x₀) :
    Set.EqOn u (fun _ ↦ u x₀) U :=
  hu.hasSphereMeanValueProperty.eqOn_const_of_isPreconnected_of_forall_le
    hu.contDiffOn.continuousOn hUopen hUconn hx₀ hmax

/-- Strong minimum principle, obtained from the strong maximum principle by negation. -/
theorem IsHarmonicPDE.eqOn_const_of_isPreconnected_of_forall_ge
    {n : ℕ} [Fact (0 < n)]
    {u : ℝ^n → ℝ} {U : Set (ℝ^n)}
    (hu : IsHarmonicPDE n u U)
    (hUopen : IsOpen U) (hUconn : IsPreconnected U)
    {x₀ : ℝ^n} (hx₀ : x₀ ∈ U)
    (hmin : ∀ y ∈ U, u x₀ ≤ u y) :
    Set.EqOn u (fun _ ↦ u x₀) U :=
  hu.hasSphereMeanValueProperty.eqOn_const_of_isPreconnected_of_forall_ge
    hu.contDiffOn.continuousOn hUopen hUconn hx₀ hmin

end LaplacianEquation
