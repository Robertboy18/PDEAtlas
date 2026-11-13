/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.EvenDimensions.Representation
public import PDE.Hyperbolic.Models.Wave.Poisson.Representation

/-!
# The planar case is Poisson's disk formula

At `k=0` the radial transform is the identity. The signed spherical
representation identifies the constructed field with the Poisson
formula, including time zero, before the positive-time weighted-ball formulas
are compared. Evans, §2.4.1(e), notes that (38) agrees with Poisson's formula (27) when `n = 2`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.4.1(c), equation (27); §2.4.1(e), equation (38) and the
  remark after it.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

namespace WaveEquation

open PDE.Analysis PDE.Common

/-- In dimension two the canonical even wave is the Poisson formula
at every signed time, including the assigned value at zero. -/
theorem evenWaveSolution_zero_eq_poissonFormula {g h : ℝ^2 → ℝ}
    (hg : ContDiff ℝ 1 g) (hh : Continuous h) (x : ℝ^2) (t : ℝ) :
    evenWaveSolution 0 g h (timeSpaceCons t x) = poissonFormula g h x t := by
  rw [evenWaveSolution_timeSpaceCons, oddWaveSolution,
    partialDeriv_oddWavePotential_time 0 (hg.comp coordinateProjection.contDiff),
    oddWavePotential_timeSpaceCons, oddSphericalProfile_zero, oddSphericalProfile_zero,
    poissonFormula_eq_sphericalMean hg hh]
  norm_num

/-- The even-dimensional formula (38) of Evans reduces to Poisson's formula (27) for `n = 2`. -/
theorem evansEvenDimensionalFormula_zero_eq_poissonFormula {g h : ℝ^2 → ℝ}
    (hg : ContDiff ℝ 1 g) (hh : Continuous h) (x : ℝ^2) (t : Set.Ioi (0 : ℝ)) :
    evansEvenDimensionalFormula 0 g h x t = poissonFormula g h x t := by
  rw [← evenWaveSolution_eq_evansEvenDimensionalFormula 0 hg hh,
    evenWaveSolution_zero_eq_poissonFormula hg hh]

end WaveEquation
