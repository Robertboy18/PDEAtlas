/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.PointwiseBoundary
public import PDE.Spaces.Sobolev.Variational.Spaces.ZeroBoundaryCoordinates
public import PDE.Common.Euclidean.SpaceTime

/-!
# Pointwise lateral boundary values of continuous evolution representatives

A continuous closed-cylinder representative of zero-boundary Sobolev
slices vanishes on the entire lateral boundary. The trace theorem supplies
pointwise spatial boundary values at almost every time; time continuity supplies
all times, including the initial and terminal times. No evolution equation or
smoothness assumption is needed.
-/

@[expose] public noncomputable section

open PDE (SpaceTime)

namespace SobolevSpace.Evolution.Classical

open MeasureTheory Set GraphSpace Boundary PDE.Common
open scoped ENNReal Sobolev

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)} {a b : ℝ}

/-- Continuous representatives of `H¹₀` time slices vanish pointwise
on the closed lateral boundary, in every positive spatial dimension. -/
theorem eq_zero_on_lateral_boundary
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : HasC1GraphBoundary Ω) (hab : a < b)
    (u : ℝ → H¹₀(Ω)) {U : SpaceTime n → ℝ}
    (hU : ContinuousOn U (splitSpaceTime ⁻¹' (closure Ω ×ˢ Icc a b)))
    (hae : ∀ᵐ t ∂volume.restrict (Ioo a b),
      (fun x ↦ U (timeSpaceCons t x)) =ᵐ[domainMeasure n Ω]
        baseRepresentative (h10SubtypeL (u t))) :
    ∀ t ∈ Icc a b, ∀ x ∈ frontier Ω, U (timeSpaceCons t x) = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Fact.out : 0 < n))
  have hslices : ∀ᵐ t ∂volume.restrict (Ioo a b),
      ∀ x ∈ frontier Ω, U (timeSpaceCons t x) = 0 := by
    filter_upwards [hae, ae_restrict_mem measurableSet_Ioo] with t ht htmem
    have hc : ContinuousOn (fun x ↦ U (timeSpaceCons t x)) (closure Ω) :=
      hU.comp ((spaceTimeContinuousLinearEquiv (m + 1)).symm.continuous.comp
        (continuous_id.prodMk continuous_const)).continuousOn
        (by
          intro x hx
          change splitSpaceTime (joinSpaceTime (x, t)) ∈ closure Ω ×ˢ Icc a b
          rw [split_joinSpaceTime]
          exact ⟨hx, Ioo_subset_Icc_self htmem⟩)
    have hz (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : ENNReal.ofReal 2 = p)
        (v : W^{1,p}(Ω))
        (hv : v ∈ (wkp0SubmoduleOn (n := m + 1) (k := 1) (p := p)
          (Ω := Ω)).toSubmodule)
        (hvu : baseRepresentative v =ᵐ[domainMeasure (m + 1) Ω]
          fun x ↦ U (timeSpaceCons t x)) :
        ∀ x ∈ frontier Ω, U (timeSpaceCons t x) = 0 := by
      subst p
      exact (Trace.C1.mem_Wkp0_iff_eq_zero_on_frontier_of_continuousOn
        hopen hbounded hgraph 2 v hc hvu).mp hv
    exact hz 2 (ENNReal.ofReal_ofNat 2) (h10SubtypeL (u t)) (u t).property ht.symm
  intro t ht x hx
  have htime : (fun s ↦ U (timeSpaceCons s x)) =ᵐ[volume.restrict (Icc a b)]
      fun _ ↦ (0 : ℝ) := by
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
    exact hslices.mono fun s hs ↦ hs x hx
  apply Measure.eqOn_Icc_of_ae_eq volume hab.ne htime _ continuousOn_const ht
  exact hU.comp ((spaceTimeContinuousLinearEquiv (m + 1)).symm.continuous.comp
    (continuous_const.prodMk continuous_id)).continuousOn
    (by
      intro s hs
      change splitSpaceTime (joinSpaceTime (x, s)) ∈ closure Ω ×ˢ Icc a b
      rw [split_joinSpaceTime]
      exact ⟨frontier_subset_closure hx, hs⟩)

end SobolevSpace.Evolution.Classical
