/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.Perron.Construction
public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.Perron.CompactComparison

/-!
# Continuous Perron solutions on compact spacetime domains

Ordered continuous subsolution and supersolution barriers that agree on the
full frontier of a compact spacetime set give a continuous viscosity solution
of the autonomous Hamilton–Jacobi equation on its interior.

First construct the upper Perron envelope and its lower regularization.
Extend each to the compact set using its respective boundary barrier.
Compact comparison gives the missing ordering between these representatives,
so they agree. Their upper and lower semicontinuity then imply continuity,
including attainment of the common boundary data.

The assumptions include agreement on the full spacetime frontier. On a
time cylinder this includes the terminal face.

This is Perron's method in the form of Theorem 4.1 of Crandall, Ishii and Lions, where comparison
for the Dirichlet problem turns the maximal subsolution into a continuous solution.

## References

* M. G. Crandall, H. Ishii and P.-L. Lions, *User's guide to viscosity solutions of second order
  partial differential equations*, Bull. Amer. Math. Soc. 27 (1992), 1-67, §4, Theorem 4.1.
  <https://doi.org/10.1090/S0273-0979-1992-00266-5>
-/

@[expose] public section

noncomputable section

namespace HamiltonJacobi.Perron

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Perron's construction yields a continuous viscosity solution between
ordered continuous barriers on a compact spacetime set, with their common
values on its full frontier. Envelope stability, the supersolution bump,
boundary extension, and comparison are all proved in the construction. -/
theorem exists_continuous_solution_on_compact {H : E → ℝ} {K : Set (E × ℝ)} {l b : E × ℝ → ℝ}
    (hH : Continuous H) (hK : IsCompact K) (hl : ContinuousOn l K) (hb : ContinuousOn b K)
    (hlsub : IsSpatialViscositySubsolution (fun p _ ↦ H p) (interior K) l)
    (hbsuper : IsSpatialViscositySupersolution (fun p _ ↦ H p) (interior K) b)
    (hlb : ∀ x ∈ K, l x ≤ b x) (hboundary : EqOn l b (frontier K)) :
    ∃ u : E × ℝ → ℝ, ContinuousOn u K ∧ IsSpatialViscositySolution (fun p _ ↦ H p) (interior K) u ∧
      (∀ x ∈ K, l x ≤ u x ∧ u x ≤ b x) ∧ EqOn u l (frontier K) := by
  classical
  obtain ⟨u, hu, husub, ha, hasuper, hbounds⟩ := exists_perron_envelope_between
    (hH.comp continuous_fst) (hl.mono interior_subset) (hb.mono interior_subset)
    hlsub hbsuper (fun x hx ↦ hlb x (interior_subset hx))
  let a : E × ℝ → ℝ := fun x ↦ liminf u (𝓝[interior K] x)
  let ū : E × ℝ → ℝ := (interior K).piecewise u b
  let v : E × ℝ → ℝ := (interior K).piecewise a l
  have hū : EqOn u ū (interior K) := fun x hx ↦ (piecewise_eq_of_mem (interior K) u b hx).symm
  have hv : EqOn a v (interior K) := fun x hx ↦ (piecewise_eq_of_mem (interior K) a l hx).symm
  have hūusc : UpperSemicontinuousOn ū K :=
    PDE.upperSemicontinuousOn_piecewise_interior hu hb.upperSemicontinuousOn
      (fun x hx ↦ (hbounds x hx).2.2)
  have hvlsc : LowerSemicontinuousOn v K :=
    PDE.lowerSemicontinuousOn_piecewise_interior ha hl.lowerSemicontinuousOn
      (fun x hx ↦ (hbounds x hx).1)
  have hūsub := husub.congr hū
  have hvsuper := hasuper.congr hv
  have hūb : ∀ x ∈ K, ū x ≤ b x := fun x _ ↦ by
    by_cases hx : x ∈ interior K
    · simpa [ū, hx] using (hbounds x hx).2.2
    · simp [ū, hx]
  have hlv : ∀ x ∈ K, l x ≤ v x := fun x _ ↦ by
    by_cases hx : x ∈ interior K
    · simpa [v, hx] using (hbounds x hx).1
    · simp [v, hx]
  have hcompare := le_on_compact_of_boundary_barriers hK hūusc hvlsc hūsub hvsuper
    hl hb hūb hlv (fun x hx ↦ (hboundary hx).ge)
  have heq : EqOn ū v K := fun x hx ↦ by
    refine le_antisymm (hcompare x hx) ?_
    by_cases hxU : x ∈ interior K
    · rw [← hū hxU, ← hv hxU]
      exact (hbounds x hxU).2.1
    · simpa [ū, v, hxU] using (hboundary ⟨subset_closure hx, hxU⟩).le
  have hūlsc : LowerSemicontinuousOn ū K := fun x hx ↦ by
    apply LowerSemicontinuousWithinAt.congr_of_eventuallyEq (hvlsc x hx) hx
    filter_upwards [self_mem_nhdsWithin] with y hy using (heq hy).symm
  refine ⟨ū, continuousOn_iff_lower_upperSemicontinuousOn.mpr ⟨hūlsc, hūusc⟩,
    ⟨hūsub, hvsuper.congr (heq.symm.mono interior_subset)⟩,
    fun x hx ↦ ⟨(hlv x hx).trans_eq (heq hx).symm, hūb x hx⟩, fun x hx ↦ ?_⟩
  simpa [ū, hx.2] using (hboundary hx).symm

end HamiltonJacobi.Perron
