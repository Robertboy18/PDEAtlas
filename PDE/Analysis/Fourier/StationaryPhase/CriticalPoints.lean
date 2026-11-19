/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.StationaryPhase.Morse
public import Mathlib.Topology.Covering.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Finiteness and localization of nondegenerate critical points

Nondegeneracy makes the gradient locally invertible. Its zero fiber is therefore
discrete, and its intersection with a compact amplitude support is finite.
Smooth bump functions isolate these points inside prescribed neighborhoods.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology Gradient

namespace PDE.Analysis.StationaryPhase

variable {n : ℕ}

/-- Nondegenerate critical points in the compact amplitude support form a finite set. -/
theorem finite_criticalPoints {φ : ℝ^n → ℝ} {a : ℝ^n → ℂ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport a)
    (hdet : ∀ p ∈ tsupport a, fderiv ℝ φ p = 0 →
      (PDE.Analysis.hessianMatrix φ p).det ≠ 0) :
    {p | p ∈ tsupport a ∧ fderiv ℝ φ p = 0}.Finite := by
  have hD : Continuous (fderiv ℝ φ) :=
    (hφ.fderiv_right (m := 0) (by simp)).continuous
  have hK : IsCompact {p | p ∈ tsupport a ∧ fderiv ℝ φ p = 0} :=
    hc.isCompact.inter_right (isClosed_singleton.preimage hD)
  apply hK.finite
  apply IsDiscrete.of_openPartialHomeomorph (∇ φ) (x := 0)
  · intro p hp
    change ∇ φ p = 0
    rw [gradient, hp.2, map_zero]
  · intro p hp
    have hg : ContDiffAt ℝ 1 (∇ φ) p :=
      PDE.Analysis.contDiffAt_gradient (m := 1) (hφ.contDiffAt.of_le (by simp))
    obtain ⟨e, he, hpe, _⟩ :=
      PDE.Analysis.exists_openPartialHomeomorph_of_det_jacobianMatrix_ne_zero hg one_ne_zero
        (by rw [jacobianMatrix_gradient (hφ.contDiffAt.of_le (by simp))]
            exact hdet p hp.1 hp.2)
    exact ⟨e, hpe, he⟩

/-- A smooth compact cutoff equals one near a chosen point and vanishes near
the other points of a finite set, while staying inside a prescribed open neighborhood. -/
theorem exists_cutoff_separating_finset (C : Finset (ℝ^n)) (p : ℝ^n)
    {U : Set (ℝ^n)} (hU : IsOpen U) (hp : p ∈ U) :
    ∃ χ : ℝ^n → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ U ∧ χ =ᶠ[𝓝 p] 1 ∧
      ∀ q ∈ C, q ≠ p → q ∉ tsupport χ := by
  classical
  let V := U \ (C.erase p : Set (ℝ^n))
  have hV : IsOpen V := hU.sdiff (C.erase p).finite_toSet.isClosed
  have hpV : p ∈ V := ⟨hp, by simp⟩
  obtain ⟨r, hr, hball⟩ :=
    Metric.nhds_basis_closedBall.mem_iff.mp (hV.mem_nhds hpV)
  let χ : ContDiffBump p :=
    { rIn := r / 2
      rOut := r
      rIn_pos := half_pos hr
      rIn_lt_rOut := half_lt_self hr }
  refine ⟨χ, χ.contDiff, χ.hasCompactSupport, ?_, χ.eventuallyEq_one, ?_⟩
  · rw [χ.tsupport_eq]
    exact hball.trans sdiff_subset
  · intro q hq hqp hqχ
    have hqV : q ∈ V := hball (by simpa only [χ.tsupport_eq] using hqχ)
    exact hqV.2 (by simpa only [Finset.mem_coe] using Finset.mem_erase.mpr ⟨hqp, hq⟩)

end PDE.Analysis.StationaryPhase
