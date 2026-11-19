/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Spectral.DomainCauchy.Approximation

/-!
# Continuous domain data in the pivot space

Zero extension makes continuous zero-boundary data compactly supported and continuous
on the ambient Euclidean space. This constructs their pivot-space class without a
measurability or integrability assumption on an arbitrary representative outside the domain.
-/

@[expose] public noncomputable section

namespace HeatEquation

open SobolevSpace SobolevSpace.GraphSpace MeasureTheory Set
open scoped ENNReal

variable {n : ℕ} {Ω : Set (ℝ^n)} (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
  {g : ℝ^n → ℝ} (hg : ContinuousOn g (closure Ω))
  (hzero : ∀ x ∈ frontier Ω, g x = 0)

include hopen hbounded hg hzero in
/-- Continuous zero-boundary data belong to every `Lᵖ` space on a bounded domain. -/
theorem memLp_of_continuousOn_zero_frontier (p : ℝ≥0∞) :
    MemLp g p (domainMeasure n Ω) := by
  classical
  let u := Ω.piecewise g 0
  have hu : Continuous u := continuous_piecewise hzero hg continuousOn_const
  have huc : HasCompactSupport u := by
    apply HasCompactSupport.of_support_subset_isCompact hbounded.isCompact_closure
    intro x hx
    by_contra hc
    exact hx (piecewise_eq_of_notMem Ω g 0 (fun hi ↦ hc (subset_closure hi)))
  have hmem : MemLp u p (domainMeasure n Ω) := hu.memLp_of_hasCompactSupport huc
  refine hmem.ae_eq ?_
  filter_upwards [ae_restrict_mem hopen.measurableSet] with x hx
  exact piecewise_eq_of_mem Ω g 0 hx

/-- The pivot-space initial datum represented by the prescribed continuous function. -/
def continuousInitialL2 : DerivLp n 2 Ω :=
  (memLp_of_continuousOn_zero_frontier hopen hbounded hg hzero 2).toLp g

/-- The constructed pivot datum agrees almost everywhere with the prescribed function. -/
theorem continuousInitialL2_ae :
    (continuousInitialL2 hopen hbounded hg hzero : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] g :=
  (memLp_of_continuousOn_zero_frontier hopen hbounded hg hzero 2).coeFn_toLp

end HeatEquation
