/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Galerkin.TrialProjection
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Galerkin trials in a regular domain

A dense linear subspace of a separable Hilbert pivot contains an increasing family of
finite-dimensional trial spaces with dense union. Their orthogonal projections form a
stable trial system for the identity Gelfand triple. No compact inclusion is needed, and
every trial vector stays in the prescribed regular domain.

If the regular domain is given as the range of a linear realization map, the trial states
also admit continuous linear reconstructions. Continuity follows from finite dimension;
the regular domain can be a topological vector space, including a space of test functions.
If it is normed, the reconstruction norms need not be uniform. The density hypothesis is on
the range of the regular realization.
-/

@[expose] public section

noncomputable section


open Filter Set TopologicalSpace
open scoped InnerProductSpace Topology

namespace PDE.Analysis.Evolution

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A dense regular subspace contains nested, eventually dense finite-dimensional trials.
The projections have norm at most one in this same Hilbert pivot. -/
theorem exists_stableTrialSystem_le_of_dense [SeparableSpace H]
    (D : Submodule ℝ H) (hD : Dense (D : Set H)) :
    ∃ trials : StableTrialSystem (GelfandTriple.identity H),
      Monotone trials.space ∧ (∀ n, trials.space n ≤ D) ∧
        trials.stabilityConstant = 1 := by
  classical
  let d : ℕ → D := denseSeq D
  have hd : DenseRange (fun n ↦ (d n : H)) :=
    hD.denseRange_val.comp (denseRange_denseSeq D) continuous_subtype_val
  let S (n : ℕ) : Submodule ℝ H :=
    Submodule.span ℝ ((fun i ↦ (d i : H)) '' (Finset.range n : Set ℕ))
  have hfinite (n : ℕ) : FiniteDimensional ℝ (S n) :=
    FiniteDimensional.span_of_finite ℝ ((Finset.finite_toSet _).image _)
  have hmono : Monotone S := by
    intro n m hnm
    exact Submodule.span_mono (Set.image_mono (by
      simpa only [Finset.coe_subset] using Finset.range_mono hnm))
  have hsub (n : ℕ) : S n ≤ D := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, _, rfl⟩
    exact (d i).property
  have hdense : ∀ h : H, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∃ w : S n, ‖h - (w : H)‖ < ε := by
    intro h ε hε
    obtain ⟨i, hi⟩ := hd.exists_dist_lt h hε
    filter_upwards [eventually_ge_atTop (i + 1)] with n hn
    refine ⟨⟨d i, Submodule.subset_span ⟨i, ?_, rfl⟩⟩, ?_⟩
    · exact Finset.mem_range.mpr (lt_of_lt_of_le (Nat.lt_succ_self i) hn)
    · simpa only [dist_eq_norm] using hi
  let trials : StableTrialSystem (GelfandTriple.identity H) :=
    { space := S
      finiteDimensional := hfinite
      stabilityConstant := 1
      projection := fun n ↦ by
        letI := hfinite n
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
      denseEnergy := hdense }
  exact ⟨trials, hmono, hsub, rfl⟩

/-- A linear map `J : R → H` with dense range gives nested Galerkin trials `S n` for the
identity triple on `H`, with projections of norm at most one, and continuous linear maps
`reconstruct n : S n → R` with `J (reconstruct n u) = u`. The map `J` need not be continuous. -/
theorem exists_stableTrialSystem_with_reconstruction
    {R : Type*} [AddCommGroup R] [Module ℝ R] [TopologicalSpace R]
    [IsTopologicalAddGroup R] [ContinuousSMul ℝ R] [SeparableSpace H]
    (J : R →ₗ[ℝ] H) (hJ : DenseRange J) :
    ∃ trials : StableTrialSystem (GelfandTriple.identity H),
      Monotone trials.space ∧ trials.stabilityConstant = 1 ∧
        ∃ reconstruct : ∀ n, trials.space n →L[ℝ] R,
          ∀ n (u : trials.space n), J (reconstruct n u) = (u : H) := by
  obtain ⟨trials, hmono, hsub, hconstant⟩ :=
    exists_stableTrialSystem_le_of_dense (LinearMap.range J) hJ
  have hlift (n : ℕ) :
      ∃ L : trials.space n →L[ℝ] R, ∀ u, J (L u) = (u : H) := by
    let := trials.finiteDimensional n
    obtain ⟨L, hL⟩ := Module.projective_lifting_property J.rangeRestrict
      (Submodule.inclusion (hsub n)) J.surjective_rangeRestrict
    refine ⟨L.toContinuousLinearMap, fun u ↦ ?_⟩
    exact congrArg Subtype.val (LinearMap.congr_fun hL u)
  choose reconstruct hreconstruct using hlift
  exact ⟨trials, hmono, hconstant, reconstruct, hreconstruct⟩

end PDE.Analysis.Evolution
