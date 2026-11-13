/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.Harmonic.PoissonRepresentation
public import PDE.Elliptic.PotentialTheory.GreenFunction.Ball.PoissonExtension.CenterValue
public import PDE.Elliptic.Classical.MeanValue.Definitions

/-!
# PDE harmonicity implies the mean-value property

We prove Evans's implication from the differential equation `Δu = 0` to the
spherical mean-value property. The proof uses the Poisson solution on a ball
and the maximum-principle uniqueness theorem:

1. translate an admissible ball to the origin;
2. continuously extend the boundary trace by the Tietze theorem;
3. solve the centered-ball Dirichlet problem with the Poisson kernel;
4. identify the original harmonic function with that solution by uniqueness; and
5. evaluate the Poisson integral at the center.

No global regularity of `u` is assumed.  Tietze extension is needed only because the Poisson
integral takes a function on all of space; the resulting value depends solely on the boundary trace.
Evans proves the same implication (§2.2.2, Theorem 2) by showing with Green's formula that the
sphere average has zero radial derivative.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.2, Theorem 2 (Mean-value formulas for Laplace's
  equation) and its proof, pp. 25-26; §2.2.4, Poisson's formula for the ball (45), p. 41.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace LaplacianEquation

open MeasureTheory Set

/-- A `C²` function with vanishing Euclidean Laplacian has the spherical mean-value property.

This is the dimension-generic implication from PDE harmonicity to the canonical sphere mean-value
predicate. -/
theorem IsHarmonicPDE.hasSphereMeanValueProperty {n : ℕ} [Fact (0 < n)]
    {u : ℝ^n → ℝ} {U : Set (ℝ^n)}
    (hu : IsHarmonicPDE n u U) : HasSphereMeanValueProperty n u U := by
  intro x _ r hr hclosed
  obtain ⟨g, hg_boundary, hlocal⟩ := hu.exists_poisson_representation hr hclosed
  calc
    u x = GreenFunction.poissonBallExtension (n := n) r g 0 := by
      simpa using hlocal (Metric.mem_ball_self hr)
    _ = PDE.Analysis.sphereAverage n (g : ℝ^n → ℝ) 0 r :=
      GreenFunction.poissonBallExtension_zero_eq_sphereAverage hr g
    _ = PDE.Analysis.sphereAverage n (fun z ↦ u (x + z)) 0 r :=
      PDE.Analysis.sphereAverage_congr_on_sphere hr hg_boundary
    _ = PDE.Analysis.sphereAverage n u x r :=
      PDE.Analysis.sphereAverage_comp_add_left u x r

end LaplacianEquation

namespace InnerProductSpace

/-- A Mathlib harmonic function has LeanPDE's spherical mean-value property.

This is the Mathlib-native entry point to the Evans mean-value theorem. -/
theorem HarmonicOnNhd.hasSphereMeanValueProperty {n : ℕ} [Fact (0 < n)]
    {u : ℝ^n → ℝ} {U : Set (ℝ^n)}
    (hu : HarmonicOnNhd u U) :
    LaplacianEquation.HasSphereMeanValueProperty n u U :=
  hu.isHarmonicPDE.hasSphereMeanValueProperty

end InnerProductSpace
