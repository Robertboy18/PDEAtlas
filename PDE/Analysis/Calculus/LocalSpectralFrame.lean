/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.SimpleEigenpair
public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# A normalized spectral frame near an operator with simple real spectrum

Start with a finite eigenbasis whose real eigenvalues are strictly ordered. Each
normalized eigenpair has an analytic branch by the implicit-function theorem.
There are only finitely many branches and inequalities, so they hold together on
one open neighborhood. The eigenvectors there form a basis: distinct eigenvalues
give linear independence, and the number of vectors is the dimension.

Normalization uses the coordinate functionals of the base basis. It does not mean
unit norm, and no inner product or self-adjointness is required.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis.Calculus.SimpleEigenpair

open Filter Set
open scoped ContDiff Topology

/-- An ordered real eigenbasis extends to analytic normalized eigenpairs on one
open operator neighborhood. At every operator in that neighborhood the branches
remain strictly ordered and their vectors form a basis, including in dimension zero. -/
theorem exists_local_spectral_frame
    {ι E : Type*} [Finite ι] [LinearOrder ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : Module.Basis ι ℝ E) (A : E →L[ℝ] E) (eig : ι → ℝ)
    (hA : ∀ k, A (b k) = eig k • b k) (horder : StrictMono eig) :
    ∃ ψ : ι → (E →L[ℝ] E) → E × ℝ,
      (∀ k, ψ k A = (b k, eig k)) ∧
      ∃ U : Set (E →L[ℝ] E), IsOpen U ∧ A ∈ U ∧
        ∀ B ∈ U,
          StrictMono (fun k ↦ (ψ k B).2) ∧
          (∀ k, ContDiffAt ℝ ω (ψ k) B ∧
            Module.End.HasEigenvector B.toLinearMap (ψ k B).2 (ψ k B).1 ∧
            b.equivFun (ψ k B).1 k = 1) ∧
          ∃ bB : Module.Basis ι ℝ E, ∀ k, bB k = (ψ k B).1 := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have : FiniteDimensional ℝ E := b.finiteDimensional_of_finite
  have hbranches (k : ι) := exists_normalized_eigenpair b A eig k (hA := hA)
    (hsep := fun j hj ↦ horder.injective.ne hj)
  choose ψ hbase hreg hnear _hisolated using hbranches
  have hcommon :
      ∀ᶠ B in 𝓝 A, ∀ k,
        ContDiffAt ℝ ω (ψ k) B ∧
        B (ψ k B).1 = (ψ k B).2 • (ψ k B).1 ∧
        b.equivFun (ψ k B).1 k = 1 ∧ (ψ k B).1 ≠ 0 :=
    Filter.eventually_all.mpr hnear
  have hless (i j : ι) :
      ∀ᶠ B in 𝓝 A, i < j → (ψ i B).2 < (ψ j B).2 := by
    by_cases hij : i < j
    · have hbase_lt : (ψ i A).2 < (ψ j A).2 := by
        simpa only [hbase i, hbase j] using horder hij
      exact ((hreg i).continuousAt.snd.eventually_lt
        (hreg j).continuousAt.snd hbase_lt).mono fun _ h _ ↦ h
    · exact Filter.Eventually.of_forall fun _ h ↦ (hij h).elim
  have hordered : ∀ᶠ B in 𝓝 A, StrictMono (fun k ↦ (ψ k B).2) := by
    have h := Filter.eventually_all.mpr fun i ↦
      Filter.eventually_all.mpr (hless i)
    exact h.mono fun _ h i j hij ↦ h i j hij
  obtain ⟨U, hUsub, hUopen, hAU⟩ :=
    _root_.mem_nhds_iff.mp (hcommon.and hordered)
  refine ⟨ψ, hbase, U, hUopen, hAU, ?_⟩
  intro B hBU
  obtain ⟨hB, hBord⟩ := hUsub hBU
  have heigen (k : ι) :
      Module.End.HasEigenvector B.toLinearMap (ψ k B).2 (ψ k B).1 := by
    refine ⟨?_, (hB k).2.2.2⟩
    exact Module.End.mem_eigenspace_iff.mpr (hB k).2.1
  have hlin : LinearIndependent ℝ (fun k ↦ (ψ k B).1) :=
    Module.End.eigenvectors_linearIndependent' B.toLinearMap
      (fun k ↦ (ψ k B).2) hBord.injective (fun k ↦ (ψ k B).1) heigen
  refine ⟨hBord, fun k ↦ ⟨(hB k).1, heigen k, (hB k).2.2.1⟩, ?_⟩
  refine ⟨basisOfLinearIndependentOfCardEqFinrank'
    (fun k ↦ (ψ k B).1) hlin (Module.finrank_eq_card_basis b).symm, ?_⟩
  intro k
  exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _) k

end PDE.Analysis.Calculus.SimpleEigenpair
