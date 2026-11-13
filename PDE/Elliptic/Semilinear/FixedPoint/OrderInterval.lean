/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Semilinear.FixedPoint.Contraction
import PDE.Analysis.Order.IntervalFixedPoint

/-!
# Order-interval fixed points for semilinear variational equations

Let `B` be a coercive bilinear form and let `N u` be a nonlinear dual load.
The semilinear weak equation

`B u v + N u v = ell v`

is equivalent to the fixed-point equation for `semilinearPicardMap`

`u = solve B hB (ell - N u)`.

Assume the ambient order is a conditionally complete lattice and the
Lax–Milgram solution map is monotone. Ordered invariant barriers then give
least and greatest weak solutions in their interval. Lattice completeness
is a separate hypothesis from Hilbert-space completeness. No compatibility
between the order and the Hilbert-space topology is required.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.Weak

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V]

/-- A monotone Picard map on a conditionally complete lattice has a least
semilinear weak solution between ordered invariant barriers. -/
theorem exists_least_semilinear_weak_solution_Icc
    [ConditionallyCompleteLattice V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (N : V → StrongDual ℝ V) (ell : StrongDual ℝ V)
    (lower upper : V) (hlowerupper : lower ≤ upper)
    (hmono : Monotone (semilinearPicardMap B hB N ell))
    (hlower : lower ≤ semilinearPicardMap B hB N ell lower)
    (hupper : semilinearPicardMap B hB N ell upper ≤ upper) :
    ∃ u ∈ Set.Icc lower upper,
      (∀ v, B u v + N u v = ell v) ∧
        ∀ w ∈ Set.Icc lower upper,
          (∀ v, B w v + N w v = ell v) → u ≤ w := by
  let T : V → V := semilinearPicardMap B hB N ell
  obtain ⟨u, huIcc, hufixed, hleast⟩ :=
    PDE.OrderInterval.exists_least_fixed_point_Icc
      T hmono lower upper hlowerupper hlower hupper
  refine ⟨u, huIcc, ?_, ?_⟩
  · exact (isFixedPt_semilinearPicardMap_iff B hB N ell u).1 hufixed
  · intro w hwIcc hw
    apply hleast w hwIcc
    exact (isFixedPt_semilinearPicardMap_iff B hB N ell w).2 hw

/-- A monotone Picard map on a conditionally complete lattice has a greatest
semilinear weak solution between ordered invariant barriers. -/
theorem exists_greatest_semilinear_weak_solution_Icc
    [ConditionallyCompleteLattice V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (N : V → StrongDual ℝ V) (ell : StrongDual ℝ V)
    (lower upper : V) (hlowerupper : lower ≤ upper)
    (hmono : Monotone (semilinearPicardMap B hB N ell))
    (hlower : lower ≤ semilinearPicardMap B hB N ell lower)
    (hupper : semilinearPicardMap B hB N ell upper ≤ upper) :
    ∃ u ∈ Set.Icc lower upper,
      (∀ v, B u v + N u v = ell v) ∧
        ∀ w ∈ Set.Icc lower upper,
          (∀ v, B w v + N w v = ell v) → w ≤ u := by
  let T : V → V := semilinearPicardMap B hB N ell
  obtain ⟨u, huIcc, hufixed, hgreatest⟩ :=
    PDE.OrderInterval.exists_greatest_fixed_point_Icc
      T hmono lower upper hlowerupper hlower hupper
  refine ⟨u, huIcc, ?_, ?_⟩
  · exact (isFixedPt_semilinearPicardMap_iff B hB N ell u).1 hufixed
  · intro w hwIcc hw
    apply hgreatest w hwIcc
    exact (isFixedPt_semilinearPicardMap_iff B hB N ell w).2 hw

end SobolevSpace.Weak
