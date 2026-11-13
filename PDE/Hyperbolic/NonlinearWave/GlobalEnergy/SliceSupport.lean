/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.SpaceTime

/-!
# Compact spatial slices and Baire category

Compact support at each time does not itself give locally uniform compact support
at every time. Continuity and Baire category do give a dense set of times with a
common spatial support on a time neighborhood. Evans, §12.1.1, assumes compact support in
space at each time and differentiates the energy directly; this step, followed by finite
propagation, supplies the common support that justifies the differentiation.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.1.1, Theorem 1 and its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open Filter Set PDE.Common
open scoped Topology

namespace WaveEquation

/-- For a continuous family with compact spatial slices, times admitting a common
support on a relative time neighborhood are dense in any Baire time domain. -/
theorem dense_locally_uniform_spatial_support {n : ℕ} {I : Set ℝ} [BaireSpace I] {u : ℝ^(n + 1) → ℝ}
    (hu : ∀ x : ℝ^n, Continuous (fun t : I ↦ u (timeSpaceCons t x)))
    (hs : ∀ t : I, HasCompactSupport (fun x : ℝ^n ↦ u (timeSpaceCons t x))) :
    Dense {t : I | ∃ R : ℕ, ∀ᶠ s : I in 𝓝 t, ∀ x : ℝ^n,
      (R : ℝ) < ‖x‖ → u (timeSpaceCons s x) = 0} := by
  let S : ℕ → Set I := fun R ↦ {t | ∀ x : ℝ^n, (R : ℝ) < ‖x‖ → u (timeSpaceCons t x) = 0}
  have hclosed (R : ℕ) : IsClosed (S R) := by
    simp only [S, ofPred_forall]
    exact isClosed_iInter fun x ↦ isClosed_iInter fun _ ↦ isClosed_eq (hu x) continuous_const
  have hcover : ⋃ R, S R = univ := by
    refine eq_univ_of_forall fun t ↦ ?_
    obtain ⟨r, hr⟩ := (hs t).isCompact.isBounded.subset_closedBall (0 : ℝ^n)
    obtain ⟨R, hR⟩ := exists_nat_gt r
    refine mem_iUnion.mpr ⟨R, fun x hx ↦ ?_⟩
    by_contra hzero
    have hmem := hr (subset_tsupport _ (Function.mem_support.mpr hzero))
    have hnorm : ‖x‖ ≤ r := by simpa using hmem
    exact (hR.trans hx).not_ge hnorm
  refine (dense_iUnion_interior_of_closed hclosed hcover).mono fun t ht ↦ ?_
  obtain ⟨R, ht⟩ := mem_iUnion.mp ht
  exact ⟨R, mem_of_superset (isOpen_interior.mem_nhds ht) interior_subset⟩

end WaveEquation
