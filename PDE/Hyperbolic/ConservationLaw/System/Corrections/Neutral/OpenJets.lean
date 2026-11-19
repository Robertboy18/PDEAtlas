/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Operator.NormedSpace

import PDE.Analysis.Calculus.LocalSpectralFrame.Coordinates

/-!
# Open sets of strictly hyperbolic, genuinely nonlinear jets

An operator and a continuous bilinear map satisfy the jet condition when there
is a complete ordered real eigenbasis whose diagonal dual contractions are all
nonzero. Near any such pair, a local spectral basis and its inverse coordinates
vary smoothly. Continuity then preserves the finitely many nonzero contractions.

The condition concerns the supplied pair, without choosing a flux or imposing
signs on eigenvectors.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An ordered real eigenbasis with nonzero diagonal dual contractions of `H`.
For Jacobian and Hessian data, these contractions are the genuine-nonlinearity
quantities. Eigenvectors may have either orientation. -/
def HasOrderedGenuinelyNonlinearEigenbasis (ι : Type*) [LinearOrder ι]
    (A : E →L[ℝ] E) (H : E →L[ℝ] E →L[ℝ] E) : Prop :=
  ∃ (b : Module.Basis ι ℝ E) (eig : ι → ℝ),
    StrictMono eig ∧ (∀ k, A (b k) = eig k • b k) ∧
      ∀ k, b.repr (H (b k) (b k)) k ≠ 0

/-- Ordered real eigenbases with nonzero genuine-nonlinearity contractions
persist under small joint perturbations of the operator and bilinear map.
The index may be empty. -/
theorem isOpen_setOf_hasOrderedGenuinelyNonlinearEigenbasis (ι : Type*) [Finite ι] [LinearOrder ι] :
    IsOpen {p : (E →L[ℝ] E) × (E →L[ℝ] E →L[ℝ] E) |
      HasOrderedGenuinelyNonlinearEigenbasis ι p.1 p.2} := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  apply isOpen_iff_mem_nhds.mpr
  rintro ⟨A₀, H₀⟩ ⟨b, eig, horder, hdiag, hgn⟩
  obtain ⟨U, hU, hAU, _, r, eigenvalues, hrA, _, hreg, hrepr, hframe⟩ :=
    PDE.Analysis.Calculus.SimpleEigenpair.exists_contDiffOn_spectral_basis
      (A := fun A : E →L[ℝ] E ↦ A) (I := univ) (x₀ := A₀)
      isOpen_univ (mem_univ A₀) contDiffOn_id b eig hdiag horder
  have hbase (k : ι) : (r A₀).repr (H₀ (r A₀ k) (r A₀ k)) k ≠ 0 := by
    simpa only [hrA] using hgn k
  have hnonzero (k : ι) : ∀ᶠ p : (E →L[ℝ] E) × (E →L[ℝ] E →L[ℝ] E) in 𝓝 (A₀, H₀),
        (r p.1).repr (p.2 (r p.1 k) (r p.1 k)) k ≠ 0 := by
    have hr : ContinuousAt (fun p : (E →L[ℝ] E) × (E →L[ℝ] E →L[ℝ] E) ↦ r p.1 k) (A₀, H₀) :=
      ContinuousAt.comp (f := fun p : (E →L[ℝ] E) × (E →L[ℝ] E →L[ℝ] E) ↦ p.1)
        (g := fun A : E →L[ℝ] E ↦ r A k) (x := (A₀, H₀))
        ((hreg k).1.continuousOn.continuousAt (hU.mem_nhds hAU)) continuousAt_fst
    have hH : ContinuousAt (fun p : (E →L[ℝ] E) × (E →L[ℝ] E →L[ℝ] E) ↦
          p.2 (r p.1 k) (r p.1 k)) (A₀, H₀) := (continuousAt_snd.clm_apply hr).clm_apply hr
    have hcoordinates : ContinuousAt (fun p : (E →L[ℝ] E) × E ↦ ((r p.1).repr p.2 : ι → ℝ))
        (A₀, H₀ (r A₀ k) (r A₀ k)) := hrepr.continuousOn.continuousAt
        ((hU.prod isOpen_univ).mem_nhds ⟨hAU, mem_univ _⟩)
    have hcontraction : ContinuousAt (fun p : (E →L[ℝ] E) × (E →L[ℝ] E →L[ℝ] E) ↦
          (r p.1).repr (p.2 (r p.1 k) (r p.1 k)) k) (A₀, H₀) :=
      ContinuousAt.comp (f := fun p : (E →L[ℝ] E) × (E →L[ℝ] E →L[ℝ] E) ↦
          ((r p.1).repr (p.2 (r p.1 k) (r p.1 k)) : ι → ℝ))
        (g := fun a : ι → ℝ ↦ a k) (x := (A₀, H₀)) (continuousAt_apply k _)
        (ContinuousAt.comp (f := fun p : (E →L[ℝ] E) × (E →L[ℝ] E →L[ℝ] E) ↦
            (p.1, p.2 (r p.1 k) (r p.1 k))) (x := (A₀, H₀))
          hcoordinates (continuousAt_fst.prodMk hH))
    exact hcontraction.eventually_ne (hbase k)
  have hUeventually : ∀ᶠ p : (E →L[ℝ] E) × (E →L[ℝ] E →L[ℝ] E) in 𝓝 (A₀, H₀), p.1 ∈ U :=
    continuousAt_fst (hU.mem_nhds hAU)
  filter_upwards [hUeventually, Filter.eventually_all.mpr hnonzero] with p hp hpg
  exact ⟨r p.1, eigenvalues p.1, (hframe p.1 hp).1, fun k ↦ ((hframe p.1 hp).2 k).1, hpg⟩

end ContinuousLinearMap
