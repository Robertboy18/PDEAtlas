/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.Characteristics.JetDerivative

import PDE.Hyperbolic.ConservationLaw.System.Corrections.Neutral.CompactTolerance

/-!
# Preservation of characteristic families by neutral flux corrections

A compact family of neutral Hessian segments has a positive tolerance for errors
in the Jacobian and Hessian. Applied on the support of a smooth correction,
this tolerance preserves strict hyperbolicity and genuine nonlinearity of every
canonical characteristic family. Outside the support, the corrected flux agrees
locally with the original flux, so both derivatives are unchanged.

The tolerance depends only on the original flux and the compact reference family.
The correction, its reference coordinate, and its cutoff values are quantified
later; their derivative estimates are hypotheses.
-/

@[expose] public noncomputable section

open Filter Set
open scoped ContDiff Topology

namespace PDE.Hyperbolic.ConservationLaw.System

/-- A compact neutral Hessian family admits one tolerance preserving all canonical
characteristic families of the corrected flux. The correction and its coordinate
and cutoff maps are chosen after the tolerance. Their range and error conditions
are required only on the topological support of the correction. -/
theorem exists_pos_tolerance_for_neutral_flux_corrections {m : ℕ} {f : ℝ^m → ℝ^m} {T : Set ℝ}
    {γ : ℝ → ℝ^m} {B : ℝ → (ℝ^m →L[ℝ] ℝ^m →L[ℝ] ℝ^m)} (hf : ContDiff ℝ 2 f)
    (hhyper : ∀ x, IsStrictlyHyperbolicAt f x) (hgn : ∀ i, IsGenuinelyNonlinearFamily f i)
    (hT : IsCompact T) (hγ : ContinuousOn γ T) (hB : ContinuousOn B T)
    (hneutral : ∀ t ∈ T, ∃ (b : Module.Basis (Fin m) ℝ (ℝ^m)) (eig : Fin m → ℝ), StrictMono eig ∧
      (∀ i, fderiv ℝ f (γ t) (b i) = eig i • b i) ∧ ∀ i, b.repr (B t (b i) (b i)) i = 0) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ P : ℝ^m → ℝ^m, ContDiff ℝ 2 P → ∀ τ θ : ℝ^m → ℝ, MapsTo τ (tsupport P) T →
        MapsTo θ (tsupport P) (Icc (0 : ℝ) 1) → (∀ x ∈ tsupport P, ‖fderiv ℝ (f + P) x -
        fderiv ℝ f (γ (τ x))‖ < ε) → (∀ x ∈ tsupport P, ‖fderiv ℝ (fderiv ℝ (f + P)) x -
        (fderiv ℝ (fderiv ℝ f) (γ (τ x)) + θ x • B (τ x))‖ < ε) →
        (∀ x, IsStrictlyHyperbolicAt (f + P) x) ∧
      ∀ i, IsGenuinelyNonlinearFamily (f + P) i := by
  have hD : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right le_rfl
  have hA : ContinuousOn (fun t ↦ fderiv ℝ f (γ t)) T := hD.continuous.comp_continuousOn' hγ
  have hH : ContinuousOn (fun t ↦ fderiv ℝ (fderiv ℝ f) (γ t)) T :=
    (hD.continuous_fderiv one_ne_zero).comp_continuousOn' hγ
  have hfamily : ∀ t ∈ T, ∃ (b : Module.Basis (Fin m) ℝ (ℝ^m)) (eig : Fin m → ℝ),
        StrictMono eig ∧ (∀ i, fderiv ℝ f (γ t) (b i) = eig i • b i) ∧
          ∀ i, b.repr (fderiv ℝ (fderiv ℝ f) (γ t) (b i) (b i)) i ≠ 0 ∧
            b.repr (B t (b i) (b i)) i = 0 := by
    intro t ht
    obtain ⟨b, eig, horder, hdiag, hzero⟩ := hneutral t ht
    have hcanonical := characteristicSpeed_eq_of_eigenbasis b horder hdiag
    refine ⟨b, eig, horder, hdiag, fun i ↦ ⟨?_, hzero i⟩⟩
    rw [← fderiv_characteristicSpeed_apply_eq hf b eig horder hdiag i (b i)]
    apply (hgn i (γ t)).2 (b i)
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, b.ne_zero i⟩
    change fderiv ℝ f (γ t) (b i) = characteristicSpeed f i (γ t) • b i
    rw [congrFun hcanonical i]
    exact hdiag i
  obtain ⟨ε, hε, htolerance⟩ :=
    ContinuousLinearMap.exists_pos_tolerance_of_compact_neutral_family (Fin m)
      (A := fun t ↦ fderiv ℝ f (γ t)) (H := fun t ↦ fderiv ℝ (fderiv ℝ f) (γ t)) (B := B)
      hT hA hH hB hfamily
  refine ⟨ε, hε, fun P hP τ θ hτ hθ hfirst hsecond ↦ ?_⟩
  refine (forall_hasOrderedGenuinelyNonlinearEigenbasis_fderiv_iff (hf.add hP)).mp fun x ↦ ?_
  by_cases hx : x ∈ tsupport P
  · exact htolerance (τ x) (hτ hx) (θ x) (hθ hx)
      (fderiv ℝ (f + P) x) (fderiv ℝ (fderiv ℝ (f + P)) x) (hfirst x hx) (hsecond x hx)
  · have hsame : f + P =ᶠ[𝓝 x] f := by
      have hzero : P =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
      filter_upwards [hzero] with y hy
      change P y = 0 at hy
      change f y + P y = f y
      rw [hy, add_zero]
    have hJacobian : fderiv ℝ (f + P) x = fderiv ℝ f x := hsame.fderiv_eq
    have hHessian : fderiv ℝ (fderiv ℝ (f + P)) x = fderiv ℝ (fderiv ℝ f) x :=
      (hsame.fderiv (𝕜 := ℝ)).fderiv_eq
    change ContinuousLinearMap.HasOrderedGenuinelyNonlinearEigenbasis (Fin m)
      (fderiv ℝ (f + P) x) (fderiv ℝ (fderiv ℝ (f + P)) x)
    rw [hJacobian, hHessian]
    exact (forall_hasOrderedGenuinelyNonlinearEigenbasis_fderiv_iff hf).mpr ⟨hhyper, hgn⟩ x

end PDE.Hyperbolic.ConservationLaw.System
