/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.Harmonic.Definitions
public import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.PoissonKernel.Definitions
import PDE.Elliptic.Classical.Harmonic.Analyticity
import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.PoissonKernel.Differentiation

/-!
# Interior regularity of the half-space Poisson extension

For measurable ambient data bounded on the boundary hyperplane, differentiating the Poisson integral
twice gives classical harmonicity in the open half-space
(`poissonHalfSpaceExtension_isHarmonicPDE`). Interior harmonic regularity then gives real
analyticity, hence smoothness of every order, with the same data hypotheses
(`analyticOnNhd_poissonHalfSpaceExtension`). These are the smoothness in part (i) and part (ii) of
Evans's §2.2.4(b), Theorem 14. Evans differentiates under the integral sign to all orders in step 2
of the proof; we differentiate twice and take analyticity from
`LaplacianEquation.IsHarmonicPDE.analyticOnNhd`, his §2.2.3(e), Theorem 10.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.3(e), Theorem 10 (Analyticity), p. 31; §2.2.4(b),
  Theorem 14 (Poisson's formula for half-space), p. 37, and step 2 of its proof, p. 38.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace GreenFunction

open LaplacianEquation

variable {n : ℕ} [Fact (0 < n)]

/-- The half-space Poisson extension of measurable data bounded on the boundary
is classically harmonic in the open half-space. -/
theorem poissonHalfSpaceExtension_isHarmonicPDE
    {g : ℝ^n → ℝ}
    (hg : Measurable g)
    (hg_bounded :
      ∃ M, ∀ y ∈ SobolevSpace.HalfSpace.boundary n, |g y| ≤ M) :
    IsHarmonicPDE n
      (poissonHalfSpaceExtension (n := n) g)
      (SobolevSpace.HalfSpace.upper n) :=
  IsHarmonicPDE.mk
    (contDiffOn_poissonHalfSpaceExtension (n := n) hg hg_bounded)
    fun _ hx ↦
      laplacian_poissonHalfSpaceExtension_eq_zero
        (n := n) hg hg_bounded hx

/-- Measurable ambient data bounded on the boundary hyperplane have a real-analytic
Poisson extension in the open half-space. Interior smoothness follows with the same
hypotheses on the data. -/
theorem analyticOnNhd_poissonHalfSpaceExtension
    {g : ℝ^n → ℝ}
    (hg : Measurable g)
    (hg_bounded :
      ∃ M, ∀ y ∈ SobolevSpace.HalfSpace.boundary n, |g y| ≤ M) :
    AnalyticOnNhd ℝ
      (poissonHalfSpaceExtension (n := n) g)
      (SobolevSpace.HalfSpace.upper n) :=
  (poissonHalfSpaceExtension_isHarmonicPDE (n := n) hg hg_bounded).analyticOnNhd
    (SobolevSpace.HalfSpace.isOpen_upper n)

end GreenFunction
