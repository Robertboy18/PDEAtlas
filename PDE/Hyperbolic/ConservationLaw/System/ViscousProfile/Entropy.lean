/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.PlanarShock
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.TravelingWave
import PDE.Hyperbolic.ConservationLaw.AffineInterface.Measure
import PDE.Hyperbolic.ConservationLaw.System.VanishingViscosity.Entropy

/-!
# Entropy admissibility of unrestricted viscous profiles

The two end limits and continuity bound the whole profile. Its stretched
traveling waves are therefore a bounded vanishing-viscosity family converging to
the planar shock away from its null interface. The C¹ convex entropy limit theorem
and the planar-shock jump calculation give admissibility for every convex entropy
pair.

This is a necessary entropy condition for the viscous profiles of Evans, §11.4.1: the
stretched waves are the traveling waves (3), their limit is the shock (6), and the inequality
comes from the vanishing-viscosity argument of Theorem 2 in §11.4.2.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.4.1, equations (2)-(6); §11.4.2, Theorem 2.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open scoped Topology

namespace PDE.Hyperbolic.ConservationLaw.System

variable {m : ℕ} {flux : ℝ^m → ℝ^m} {uL uR : ℝ^m} {speed : ℝ} {v : ℝ → ℝ^m}

/-- Finite end limits and continuity bound the whole viscous profile, without
requiring its range to remain close to either end state. -/
theorem IsViscousProfile.exists_norm_le (hv : IsViscousProfile flux uL uR speed v) :
    ∃ M : ℝ, ∀ s, ‖v s‖ ≤ M := by
  obtain ⟨a, ha⟩ := eventually_atBot.mp
    (hv.tendsto_atBot.norm.eventually (gt_mem_nhds (lt_add_one ‖uL‖)))
  obtain ⟨b, hb⟩ := eventually_atTop.mp
    (hv.tendsto_atTop.norm.eventually (gt_mem_nhds (lt_add_one ‖uR‖)))
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn
    hv.contDiff.continuous.continuousOn
  refine ⟨max (‖uL‖ + 1) (max (‖uR‖ + 1) C), fun s ↦ ?_⟩
  by_cases hsa : s ≤ a
  · exact (ha s hsa).le.trans (le_max_left _ _)
  by_cases hbs : b ≤ s
  · exact (hb s hbs).le.trans (le_max_of_le_right (le_max_left _ _))
  exact (hC s ⟨(not_le.mp hsa).le, (not_le.mp hbs).le⟩).trans
    (le_max_of_le_right (le_max_right _ _))

/-- The planar shock arising from a viscous profile satisfies every
C¹ convex entropy inequality on all spacetime. -/
theorem IsViscousProfile.satisfiesEntropyInequality_planarShock
    (hv : IsViscousProfile flux uL uR speed v) (hflux : Differentiable ℝ flux) :
    SatisfiesEntropyInequality flux (⊤ : Opens ℝ^2) (planarShock uL uR speed) := by
  obtain ⟨M, hM⟩ := hv.exists_norm_le
  have hpos : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
  have hlim : ∀ᵐ p : ℝ^2, Tendsto (fun ε : ℝ ↦ travelingWave v speed ε p) (𝓝[>] 0)
        (𝓝 (planarShock uL uR speed p)) :=
    (AffineInterface.ae_ne_interface speed).mono fun _ hp ↦ hv.tendsto_travelingWave hp
  apply satisfiesEntropyInequality_of_vanishingViscosity (l := 𝓝[>] (0 : ℝ)) (ε := fun ε ↦ ε)
    (u := fun ε ↦ travelingWave v speed ε) (M := M)
  · exact hpos.mono fun _ hε ↦ le_of_lt hε
  · exact tendsto_id.mono_left nhdsWithin_le_nhds
  · exact Eventually.of_forall fun ε ↦ (contDiff_travelingWave hv.contDiff speed ε).contDiffOn
  · exact hpos.mono fun _ hε p _ ↦ hv.fluxResidual_travelingWave hflux (ne_of_gt hε) p
  · exact Eventually.of_forall fun ε ↦ Eventually.of_forall fun p ↦ hM (profileCoordinate speed ε p)
  · simpa only [Opens.coe_top, Measure.restrict_univ] using hlim

/-- Every unrestricted viscous profile is admissible for each globally defined
C¹ convex entropy pair of its flux. -/
theorem IsViscousProfile.isAdmissibleShock
    (hv : IsViscousProfile flux uL uR speed v) (E : ConvexEntropyPair flux) :
    E.toEntropyPair.IsAdmissibleShock uL uR speed :=
  ⟨hv.rankineHugoniot E.flux_differentiable, satisfiesEntropyInequalityFor_planarShock_iff.mp
      (hv.satisfiesEntropyInequality_planarShock E.flux_differentiable E)⟩

end PDE.Hyperbolic.ConservationLaw.System
