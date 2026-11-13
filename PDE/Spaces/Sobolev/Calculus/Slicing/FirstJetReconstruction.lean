/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Slicing.HigherOrder

/-!
# Reconstructing a Sobolev bundle from first-order derivative slices

Every derivative through order `m+1` occurs in the H¹ bundle of some derivative
through order `m`. A bounded coordinate selector therefore reconstructs the
original ambient bundle from these first-order slices. In the Hilbert case,
orthogonal projection onto the closed weak-derivative graph gives a bounded
reconstruction into the Sobolev space itself and fixes derivative bundles.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory
open scoped ENNReal Sobolev

variable {n m : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set ℝ^n}

/-- A derivative through order `m`, followed by at most one derivative. -/
def firstJetIndex (n m : ℕ) (a : DerivIndex n m × DerivIndex n 1) :
    DerivIndex n (m + 1) :=
  derivativeWordIndex a.1.toList (Nat.add_le_add_right a.1.toList_length_le 1) a.2

/-- First-order slices of all derivatives through order `m` contain every
coordinate through order `m+1`. -/
theorem surjective_firstJetIndex : Function.Surjective (firstJetIndex n m) := by
  intro b
  have hlen := b.toList_length_le
  cases hword : b.toList with
  | nil =>
      refine ⟨(baseIndex n m, baseIndex n 1), ?_⟩
      rw [firstJetIndex, derivativeWordIndex_baseIndex]
      have hb := derivIndexOfList_toList b b.toList_length_le
      simpa only [hword, baseIndex_toList] using hb
  | cons i tail =>
      have htail : tail.length ≤ m := by simp only [hword, List.length_cons] at hlen; omega
      let a := derivIndexOfList (n := n) (k := m) tail htail
      refine ⟨(a, singleDerivIndex n i), ?_⟩
      rw [firstJetIndex, derivativeWordIndex_singleDerivIndex]
      rw [← derivIndexOfList_toList b b.toList_length_le]
      apply derivIndexOfList_eq_of_perm
      rw [hword]
      exact ((derivIndexOfList_toList_perm tail htail).append_right [i]).trans
        List.perm_append_comm

/-- All first-order slices of a Sobolev bundle, in the finite product norm. -/
def firstJetCLM : W^{m + 1,p}(Ω) →L[ℝ]
    (DerivIndex n m → W^{1,p}(Ω)) :=
  ContinuousLinearMap.pi fun a ↦
    derivativeWordCLM a.toList (Nat.add_le_add_right a.toList_length_le 1)

/-- A bounded coordinate selector from first-order fields to an ambient
order-`m+1` tuple. It does not impose or assume weak-derivative compatibility. -/
def firstJetReconstructionAmbient :
    (DerivIndex n m → W^{1,p}(Ω)) →L[ℝ] WkpAmbientOn n (m + 1) p Ω :=
  let e := PiLp.continuousLinearEquiv p ℝ
    (fun _ : DerivIndex n (m + 1) ↦ DerivLp n p Ω)
  e.symm.toContinuousLinearMap.comp (ContinuousLinearMap.pi fun b ↦
      let a := (surjective_firstJetIndex (n := n) (m := m) b).choose
      (wkpCoordinateCLM a.2).comp (ContinuousLinearMap.proj a.1))

/-- Reconstruction returns every coordinate of the original Sobolev bundle. -/
theorem firstJetReconstructionAmbient_firstJetCLM (U : W^{m + 1,p}(Ω)) :
    firstJetReconstructionAmbient (firstJetCLM U) = U.val := by
  apply PiLp.ext
  intro b
  change U.val (firstJetIndex n m (surjective_firstJetIndex b).choose) = U.val b
  rw [(surjective_firstJetIndex b).choose_spec]

/-- Bounded reconstruction into the Sobolev graph. Orthogonal projection
enforces compatibility for arbitrary input fields and fixes derivative slices. -/
def firstJetReconstructionCLM :
    (DerivIndex n m → W^{1,2}(Ω)) →L[ℝ] W^{m + 1,2}(Ω) :=
  (wkpSubmoduleOn n (m + 1) 2 Ω).orthogonalProjectionOnto.comp
    firstJetReconstructionAmbient

/-- Reconstructing the first-order slices of a Sobolev element gives that element. -/
theorem firstJetReconstructionCLM_firstJetCLM (U : W^{m + 1,2}(Ω)) :
    firstJetReconstructionCLM (firstJetCLM U) = U := by
  dsimp only [firstJetReconstructionCLM, ContinuousLinearMap.comp_apply]
  rw [firstJetReconstructionAmbient_firstJetCLM]
  exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self U

end SobolevSpace.GraphSpace
