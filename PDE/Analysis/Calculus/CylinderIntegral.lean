/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.EuclideanBall

/-!
# Integration on a compact spacetime cylinder

Fubini identifies an interval integral of spatial ball integrals with the
spacetime integral. Compactness supplies integrability of a continuous input;
the two time endpoints have zero measure.
-/

@[expose] public section

namespace PDE.Analysis

open MeasureTheory Metric Set

variable {n : ℕ}

/-- The iterated integral of a continuous function over a compact cylinder is
its spacetime integral, with the spatial coordinate first. -/
theorem intervalIntegral_closedBall_eq_setIntegral_prod
    {F : ℝ^n × ℝ → ℝ} (hF : Continuous F)
    (c : ℝ^n) (L : ℝ) {a d : ℝ} (had : a ≤ d) :
    (∫ s in a..d, ∫ x in closedBall c L, F (x, s)) =
      ∫ z in closedBall c L ×ˢ Icc a d, F z := by
  rw [intervalIntegral.integral_of_le had, restrict_Ioc_eq_restrict_Icc]
  have hi : IntegrableOn F (closedBall c L ×ˢ Icc a d) volume :=
    hF.continuousOn.integrableOn_compact
      ((isCompact_closedBall c L).prod isCompact_Icc)
  have hprod := integral_prod_symm
    (μ := (volume : Measure (ℝ^n)).restrict (closedBall c L))
    (ν := (volume : Measure ℝ).restrict (Icc a d)) F
    (by simpa only [Measure.prod_restrict, ← Measure.volume_eq_prod, IntegrableOn] using hi)
  simpa only [Measure.prod_restrict, ← Measure.volume_eq_prod] using hprod.symm

end PDE.Analysis
