/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.LocalSpectralFrame

import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Smooth local eigenbases with smooth dual coordinates

The analytic eigenbranches already provide a basis at each nearby operator.
Selecting those bases once preserves the supplied base basis exactly. Their
synthesis maps are smooth finite sums; inversion then gives smooth coordinate
maps and joint smoothness of the actual dual-basis evaluation.

The parameter may be time or a state in a normed space. Smoothness is asserted
only on one open neighborhood inside the supplied domain. No topology on the
type of bases, unit normalization, or new eigenpair construction is used.
-/

@[expose] public noncomputable section

open Set
open scoped BigOperators ContDiff Topology

namespace PDE.Analysis.Calculus.SimpleEigenpair

variable {ι X E : Type*} [Fintype ι]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem contDiffOn_basis_coordinates
    (r : X → Module.Basis ι ℝ E) {U : Set X}
    (hr : ∀ k, ContDiffOn ℝ ∞ (fun x ↦ r x k) U) :
    ContDiffOn ℝ ∞
      (fun x ↦ ((r x).equivFunL : E →L[ℝ] (ι → ℝ))) U := by
  have hsynthesis : ContDiffOn ℝ ∞
      (fun x ↦ ((r x).equivFunL.symm : (ι → ℝ) →L[ℝ] E)) U := by
    apply contDiffOn_clm_apply.mpr
    intro c
    change ContDiffOn ℝ ∞ (fun x ↦ (r x).equivFun.symm c) U
    simp_rw [Module.Basis.equivFun_symm_apply]
    exact ContDiffOn.sum fun k _ ↦ contDiffOn_const.smul (hr k)
  intro x hx
  have hinv := (contDiffAt_map_inverse (r x).equivFunL.symm).comp_contDiffWithinAt
    x (hsynthesis x hx)
  simpa only [Function.comp_def, ContinuousLinearMap.inverse_equiv,
    ContinuousLinearEquiv.symm_symm] using hinv

/-- A smooth operator family with an ordered real eigenbasis at one parameter
has one nearby basis family with smooth columns and jointly smooth dual
coordinates. The base basis and its eigenvalue labels are retained exactly.
The eigenvectors keep the base-coordinate normalization supplied by the analytic
branches. No regularity or spectral assumption is imposed outside `I`. -/
theorem exists_contDiffOn_spectral_basis [LinearOrder ι]
    {A : X → E →L[ℝ] E} {I : Set X} {x₀ : X}
    (hI : IsOpen I) (hx₀ : x₀ ∈ I) (hA : ContDiffOn ℝ ∞ A I)
    (b : Module.Basis ι ℝ E) (eig : ι → ℝ)
    (hdiag : ∀ k, A x₀ (b k) = eig k • b k) (horder : StrictMono eig) :
    ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧ U ⊆ I ∧
      ∃ (r : X → Module.Basis ι ℝ E) (eigenvalues : X → ι → ℝ),
        r x₀ = b ∧ eigenvalues x₀ = eig ∧
        (∀ k, ContDiffOn ℝ ∞ (fun x ↦ r x k) U ∧
          ContDiffOn ℝ ∞ (fun x ↦ eigenvalues x k) U) ∧
        ContDiffOn ℝ ∞
          (fun p : X × E ↦ ((r p.1).repr p.2 : ι → ℝ)) (U ×ˢ univ) ∧
        ∀ x ∈ U, StrictMono (eigenvalues x) ∧
          ∀ k, A x (r x k) = eigenvalues x k • r x k ∧ b.equivFun (r x k) k = 1 := by
  classical
  obtain ⟨ψ, hbase, V, hV, hAV, hframe⟩ :=
    exists_local_spectral_frame b (A x₀) eig hdiag horder
  let U : Set X := I ∩ A ⁻¹' V
  have hU : IsOpen U := hA.continuousOn.isOpen_inter_preimage hI hV
  have hxU : x₀ ∈ U := ⟨hx₀, hAV⟩
  let r : X → Module.Basis ι ℝ E := fun x ↦
    if hx : x ∈ U then ((hframe (A x) hx.2).2.2).choose else b
  let eigenvalues : X → ι → ℝ := fun x k ↦ (ψ k (A x)).2
  have hr (x : X) (hx : x ∈ U) (k : ι) : r x k = (ψ k (A x)).1 := by
    simpa only [r, dite_eq_left hx] using ((hframe (A x) hx.2).2.2).choose_spec k
  have hr₀ : r x₀ = b := by
    apply Module.Basis.eq_of_apply_eq
    intro k
    exact (hr x₀ hxU k).trans (congrArg Prod.fst (hbase k))
  have heigenvalues₀ : eigenvalues x₀ = eig := by
    funext k
    exact congrArg Prod.snd (hbase k)
  have hψ (k : ι) : ContDiffOn ℝ ∞ (fun x ↦ ψ k (A x)) U := by
    intro x hx
    have hbranch : ContDiffAt ℝ ∞ (ψ k) (A x) :=
      ((hframe (A x) hx.2).2.1 k).1.of_le le_top
    exact hbranch.comp_contDiffWithinAt x ((hA x hx.1).mono inter_subset_left)
  have hrSmooth (k : ι) : ContDiffOn ℝ ∞ (fun x ↦ r x k) U :=
    (hψ k).fst.congr (fun x hx ↦ hr x hx k)
  have hcoordinates := contDiffOn_basis_coordinates r hrSmooth
  have hcoordinatesPair : ContDiffOn ℝ ∞
      (fun p : X × E ↦ ((r p.1).equivFunL : E →L[ℝ] (ι → ℝ)))
      (U ×ˢ univ) := by
    have hmaps : MapsTo (Prod.fst : X × E → X) (U ×ˢ univ) U :=
      fun _ hp ↦ hp.1
    simpa only [Function.comp_def] using hcoordinates.comp contDiffOn_fst hmaps
  have hrepr : ContDiffOn ℝ ∞
      (fun p : X × E ↦ ((r p.1).repr p.2 : ι → ℝ)) (U ×ˢ univ) := by
    change ContDiffOn ℝ ∞ (fun p : X × E ↦ (r p.1).equivFunL p.2) (U ×ˢ univ)
    exact hcoordinatesPair.clm_apply contDiffOn_snd
  refine ⟨U, hU, hxU, inter_subset_left, r, eigenvalues, hr₀, heigenvalues₀,
    fun k ↦ ⟨hrSmooth k, (hψ k).snd⟩, hrepr, ?_⟩
  intro x hx
  refine ⟨(hframe (A x) hx.2).1, ?_⟩
  intro k
  rw [hr x hx k]
  exact ⟨((hframe (A x) hx.2).2.1 k).2.1.apply_eq_smul,
    ((hframe (A x) hx.2).2.1 k).2.2⟩

end PDE.Analysis.Calculus.SimpleEigenpair
