/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HigherRegularity.Smooth.Compatibility.InitialValues
public import PDE.Hyperbolic.HigherRegularity.Compatibility.Values
public import PDE.Spaces.Sobolev.Evolution.Classical.Data.Slices
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.PointwiseBoundary

/-!
# Boundary compatibility from smooth wave data

Canonical time derivatives of one smooth forcing function determine its initial
traces. The wave recurrence then computes every formal initial value. Boundary
compatibility refers to the continuous closure values of those computed functions,
which are independent of arbitrary values outside the open spatial domain.

Pointwise vanishing on the boundary gives the zero Sobolev traces required by
every finite-order wave theorem. No boundary condition is imposed on a forcing
slice itself.
-/

@[expose] public noncomputable section

open PDE (SpaceTime)

open scoped Sobolev

namespace Hyperbolic.HigherRegularity

open MeasureTheory Set PDE.Common SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity SobolevSpace.Evolution.Classical
open scoped ENNReal

variable {n r : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}

/-- A classical closure value vanishing on the boundary has zero Dirichlet
trace in every positive Sobolev order. -/
theorem hasDirichletTraceZero_toWkpSpaceOn (hn : 0 < n) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) (hgraph : Boundary.HasC1GraphBoundary Ω) (hr : 1 ≤ r)
    {q z : ℝ^n → ℝ} (hq : ContDiffUpToBoundary r q Ω) (hz : ContinuousOn z (closure Ω))
    (heq : EqOn z q Ω) (hzero : ∀ x ∈ frontier Ω, z x = 0) :
    HasDirichletTraceZero hr (hq.toWkpSpaceOn hopen hbounded 2) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hbase : baseRepresentative (lowerOrderCLM hr (hq.toWkpSpaceOn hopen hbounded 2))
        =ᵐ[domainMeasure (m + 1) Ω] z := by
    rw [baseRepresentative_lowerOrderCLM]
    filter_upwards [hq.toWkpSpaceOn_base_ae hopen hbounded 2,
      ae_restrict_mem hopen.measurableSet] with x hx hmem
    exact hx.trans (heq hmem).symm
  have htrace (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p = ENNReal.ofReal (2 : ℝ)) (U : W^{1,p}(Ω))
      (hU : baseRepresentative U =ᵐ[domainMeasure (m + 1) Ω] z) :
      U ∈ (wkp0SubmoduleOn (n := m + 1) (k := 1) (p := p) (Ω := Ω)).toSubmodule := by
    subst p
    exact (SobolevSpace.Trace.C1.mem_Wkp0_iff_eq_zero_on_frontier_of_continuousOn
      hopen hbounded hgraph 2 U hz hU).mpr hzero
  exact htrace 2 (by norm_num) _ hbase

namespace SmoothWave

variable (P : SmoothFullCoefficients n Ω)
  (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hab : a < b)
  {f : SpaceTime n → ℝ} {g h : ℝ^n → ℝ}
  (hf : ∀ k, ContDiffUpToBoundary k f (splitSpaceTime ⁻¹' (Ω ×ˢ Ioo a b)))
  (hg : ∀ k, ContDiffUpToBoundary k g Ω)
  (hh : ∀ k, ContDiffUpToBoundary k h Ω)

/-- The initial forcing derivative, with its canonical endpoint values. -/
def forcingTrace (j : ℕ) : ℝ^n → ℝ :=
  derivativeSlice hopen hf (List.replicate j 0) a

include hbounded hab in
/-- Initial forcing traces are smooth in space at every finite order. -/
theorem forcingTrace_regular (j r : ℕ) :
    ContDiffUpToBoundary r (forcingTrace hopen hf j) Ω :=
  derivativeSlice_regular hopen hbounded hab hf (List.replicate j 0) r ⟨le_rfl, hab.le⟩

/-- Initial time derivatives computed directly from one forcing function
and the two initial data functions. -/
def initialValue (j : ℕ) : ℝ^n → ℝ :=
  classicalWaveInitialValue P (forcingTrace hopen hf) g h j

include hbounded hab hg hh in
/-- Every computed initial value has all finite spatial regularities. -/
theorem initialValue_regular (j r : ℕ) :
    ContDiffUpToBoundary r (initialValue P hopen hf (g := g) (h := h) j) Ω :=
  classicalWaveInitialValue_regular P hopen hbounded
    (forcingTrace_regular hopen hbounded hab hf) hg hh j r

/-- The Sobolev realization of a computed initial value. -/
def initialSobolevValue (r j : ℕ) : W^{r,2}(Ω) :=
  classicalWaveInitialSobolevValue P hopen hbounded
    (forcingTrace_regular hopen hbounded hab hf) hg hh r j

/-- Canonical values of the computed initial time derivatives on the closure. -/
def initialBoundaryValue (j : ℕ) : ℝ^n → ℝ :=
  (initialValue_regular P hopen hbounded hab hf hg hh j 0).continuousRepresentative

/-- Smooth wave compatibility: every computed initial time derivative
vanishes on the spatial boundary. -/
def HasCompatibleBoundaryValues : Prop :=
  ∀ j, ∀ x ∈ frontier Ω, initialBoundaryValue P hopen hbounded hab hf hg hh j x = 0

/-- Pointwise compatibility supplies the finite Sobolev trace requirement. -/
theorem initialSobolevValue_trace_zero (hn : 0 < n) (hgraph : Boundary.HasC1GraphBoundary Ω)
    (hcompat : HasCompatibleBoundaryValues P hopen hbounded hab hf hg hh) (hr : 1 ≤ r) (j : ℕ) :
    HasDirichletTraceZero hr (initialSobolevValue P hopen hbounded hab hf hg hh r j) := by
  apply hasDirichletTraceZero_toWkpSpaceOn hn hopen hbounded hgraph hr
    (initialValue_regular P hopen hbounded hab hf hg hh j r)
    (ContDiffUpToBoundary.continuous_continuousRepresentative
      (initialValue_regular P hopen hbounded hab hf hg hh j 0)).continuousOn
    (ContDiffUpToBoundary.continuousRepresentative_eqOn
      (initialValue_regular P hopen hbounded hab hf hg hh j 0))
  exact hcompat j

end SmoothWave

end Hyperbolic.HigherRegularity
