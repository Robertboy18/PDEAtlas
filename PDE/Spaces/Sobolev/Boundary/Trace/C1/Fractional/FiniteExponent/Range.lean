/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Fractional.FiniteExponent.Compatibility
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Fractional.FiniteExponent.Lifting

/-!
# The physical finite-exponent trace range on C¹ domains

A surface Lᵖ datum is a Sobolev trace exactly when each of its partitioned,
zero-extended chart coordinates belongs to the intrinsic Gagliardo space of order
`1 - 1 / p`. A finite sum of bounded chart liftings gives a right inverse
on compatible coordinate data, using the graph norms throughout.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Trace.C1.Fractional.FiniteExponent

open MeasureTheory Set
open SobolevSpace.Fractional Boundary.Geometry.SurfaceMeasure
open scoped ENNReal Sobolev

variable {m : ℕ} {Ω : Set (ℝ^(m + 1))}
variable [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
variable (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]

/-- The sum of the bounded chart liftings, acting on the finite family of fractional data. -/
def lifting (hp : 1 < p) :
    (Fin hΩ.N → GagliardoSpace m (1 - 1 / p) univ (p := ENNReal.ofReal p)) →L[ℝ]
      W^{1,ENNReal.ofReal p}(Ω) :=
  ∑ i : Fin hΩ.N, (localLifting p hp i).comp (ContinuousLinearMap.proj i)

/-- Applying the assembled lifting is the finite sum of its chart contributions. -/
theorem lifting_apply (hp : 1 < p)
    (v : Fin hΩ.N → GagliardoSpace m (1 - 1 / p) univ (p := ENNReal.ofReal p)) :
    lifting p hp v = ∑ i : Fin hΩ.N, localLifting p hp i (v i) := by
  simp only [lifting, sum_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]

/-- Compatible localized coordinates lift to exactly the original physical surface datum. -/
theorem traceLp_lifting (hp : 1 < p)
    (g : Lp ℝ (ENNReal.ofReal p) (surfaceMeasure Ω))
    (v : Fin hΩ.N → GagliardoSpace m (1 - 1 / p) univ (p := ENNReal.ofReal p))
    (hv : ∀ i, (GagliardoSpace.toLp m (1 - 1 / p) univ (v i) : ℝ^m → ℝ)
      =ᵐ[volume] localizedBoundaryCoordinates (ENNReal.ofReal p) i g) :
    traceLp p (lifting p hp v) = g := by
  rw [lifting_apply, map_sum]
  simp_rw [traceLp_localLifting_localizedBoundaryCoordinates p hp _ g _ (hv _)]
  exact sum_boundaryCutoff (ENNReal.ofReal p) g

/-- The assembled field is bounded by the sum of the chart graph norms with operator weights. -/
theorem norm_lifting_le (hp : 1 < p)
    (v : Fin hΩ.N → GagliardoSpace m (1 - 1 / p) univ (p := ENNReal.ofReal p)) :
    ‖lifting p hp v‖ ≤ ∑ i : Fin hΩ.N, ‖localLifting p hp i‖ * ‖v i‖ := by
  rw [lifting_apply]
  exact (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun i _ ↦ (localLifting p hp i).le_opNorm (v i))

/-- The range of the physical C¹ trace is characterized by intrinsic fractional chart regularity.
The coordinates include the boundary partition and zero extension off each chart target. -/
theorem mem_range_traceLp_iff (hp : 1 < p)
    (g : Lp ℝ (ENNReal.ofReal p) (surfaceMeasure Ω)) :
    g ∈ Set.range (traceLp (Ω := Ω) p) ↔
      ∀ i : Fin hΩ.N, MemGagliardo m (1 - 1 / p) univ
        (localizedBoundaryCoordinates (ENNReal.ofReal p) i g : ℝ^m → ℝ)
        (p := ENNReal.ofReal p) := by
  constructor
  · rintro ⟨u, rfl⟩ i
    exact memGagliardo_localizedBoundaryCoordinates_traceLp p hp i u
  · intro hg
    let v : Fin hΩ.N → GagliardoSpace m (1 - 1 / p) univ (p := ENNReal.ofReal p) :=
      fun i ↦ GagliardoSpace.ofFunction
        (localizedBoundaryCoordinates (ENNReal.ofReal p) i g) (hg i)
    refine ⟨lifting p hp v, traceLp_lifting p hp g v fun i ↦ ?_⟩
    simpa only [Measure.restrict_univ] using
      GagliardoSpace.toLp_ofFunction_apply_ae
        (localizedBoundaryCoordinates (ENNReal.ofReal p) i g) (hg i)

end SobolevSpace.Trace.C1.Fractional.FiniteExponent
