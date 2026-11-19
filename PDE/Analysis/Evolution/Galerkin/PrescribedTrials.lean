/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Evolution.Galerkin.RegularTrials

/-!
# Nested Galerkin trials containing prescribed regular tests

A countable family of regular tests can be included in nested finite-dimensional trials
without changing the Hilbert pivot or the orthogonal projection bound. When the regular
realization is injective, finite reconstructions agree on common states and recover every
prescribed test exactly. Stronger approximation properties of the prescribed family are
therefore retained without requiring stronger-norm stability of the energy projections.
-/

@[expose] public section

noncomputable section

open Filter Set TopologicalSpace
open scoped InnerProductSpace Topology

namespace PDE.Analysis.Evolution

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Enlarge regular dense trials by successive prescribed vectors. Orthogonal projections
still have norm at most one in the same Hilbert pivot. -/
theorem exists_stableTrialSystem_le_of_dense_containing [SeparableSpace H]
    (D : Submodule ℝ H) (hD : Dense (D : Set H)) (d : ℕ → D) :
    ∃ trials : StableTrialSystem (GelfandTriple.identity H),
      Monotone trials.space ∧ (∀ n, trials.space n ≤ D) ∧
        trials.stabilityConstant = 1 ∧ ∀ i, (d i : H) ∈ trials.space (i + 1) := by
  classical
  obtain ⟨base, hmono, hsub, _⟩ := exists_stableTrialSystem_le_of_dense D hD
  let A (n : ℕ) : Submodule ℝ H :=
    Submodule.span ℝ ((fun i ↦ (d i : H)) '' (Finset.range n : Set ℕ))
  have hfinite (n : ℕ) : FiniteDimensional ℝ (A n) :=
    FiniteDimensional.span_of_finite ℝ ((Finset.finite_toSet _).image _)
  have hAmono : Monotone A := by
    intro n m hnm
    exact Submodule.span_mono (Set.image_mono (by
      simpa only [Finset.coe_subset] using Finset.range_mono hnm))
  have hAsub (n : ℕ) : A n ≤ D := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, _, rfl⟩
    exact (d i).property
  let S (n : ℕ) : Submodule ℝ H := base.space n ⊔ A n
  have hSfinite (n : ℕ) : FiniteDimensional ℝ (S n) := by
    let := base.finiteDimensional n
    let := hfinite n
    exact Submodule.finiteDimensional_sup _ _
  let trials : StableTrialSystem (GelfandTriple.identity H) :=
    { space := S
      finiteDimensional := hSfinite
      stabilityConstant := 1
      projection := fun n ↦ by
        let := hSfinite n
        exact
          { projection := (S n).orthogonalProjectionOnto
            fixes := (S n).orthogonalProjectionOnto_mem_subspace_eq_self
            pivotOrthogonal := by
              intro u h
              change ⟪(u : H), h - (S n).starProjection h⟫_ℝ = 0
              rw [real_inner_comm]
              exact (S n).starProjection_inner_eq_zero h u u.property
            norm_le := by
              intro h
              simpa using (S n).norm_orthogonalProjectionOnto_apply_le h }
      denseEnergy := by
        intro h ε hε
        filter_upwards [base.denseEnergy h ε hε] with n hn
        obtain ⟨v, hv⟩ := hn
        exact ⟨⟨v, (show base.space n ≤ S n from le_sup_left) v.property⟩, hv⟩ }
  refine ⟨trials, fun n m hnm ↦ sup_le_sup (hmono hnm) (hAmono hnm),
    fun n ↦ sup_le (hsub n) (hAsub n), rfl, fun i ↦ ?_⟩
  exact (show A (i + 1) ≤ S (i + 1) from le_sup_right)
    (Submodule.subset_span ⟨i, Finset.mem_range.mpr (Nat.lt_succ_self i), rfl⟩)

/-- An injective dense regular realization admits coherent finite reconstructions and
nested orthogonal trials containing any prescribed countable family of regular tests.
Coherence is asserted for every common state, irrespective of the two trial levels. -/
theorem exists_stableTrialSystem_with_prescribed_reconstruction
    {R : Type*} [AddCommGroup R] [Module ℝ R] [TopologicalSpace R]
    [IsTopologicalAddGroup R] [ContinuousSMul ℝ R] [SeparableSpace H]
    (J : R →ₗ[ℝ] H) (hJ : DenseRange J) (hinj : Function.Injective J) (d : ℕ → R) :
    ∃ trials : StableTrialSystem (GelfandTriple.identity H),
      Monotone trials.space ∧ trials.stabilityConstant = 1 ∧
        ∃ reconstruct : ∀ n, trials.space n →L[ℝ] R,
          (∀ n (u : trials.space n), J (reconstruct n u) = (u : H)) ∧
          (∀ n m (u : trials.space n) (v : trials.space m),
            (u : H) = (v : H) → reconstruct n u = reconstruct m v) ∧
          ∀ i, ∃ u : trials.space (i + 1), reconstruct (i + 1) u = d i := by
  obtain ⟨trials, hmono, hsub, hconstant, hcontains⟩ :=
    exists_stableTrialSystem_le_of_dense_containing J.range hJ
      (fun i ↦ J.rangeRestrict (d i))
  let e := LinearEquiv.ofInjective J hinj
  let reconstruct (n : ℕ) : trials.space n →L[ℝ] R := by
    let := trials.finiteDimensional n
    exact (e.symm.toLinearMap.comp (Submodule.inclusion (hsub n))).toContinuousLinearMap
  have hrec (n : ℕ) (u : trials.space n) : J (reconstruct n u) = (u : H) :=
    congrArg Subtype.val (e.apply_symm_apply (Submodule.inclusion (hsub n) u))
  refine ⟨trials, hmono, hconstant, reconstruct, hrec, ?_, ?_⟩
  · intro n m u v huv
    exact hinj ((hrec n u).trans (huv.trans (hrec m v).symm))
  · intro i
    let u : trials.space (i + 1) := ⟨J (d i), hcontains i⟩
    exact ⟨u, hinj (hrec (i + 1) u)⟩

end PDE.Analysis.Evolution
