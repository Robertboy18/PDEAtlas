/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.StationaryPhase.CriticalPoints

/-!
# A stationary and nonstationary decomposition of the amplitude

Finite separating cutoffs preserve the amplitude at each critical point. Their
complement vanishes on a neighborhood of every critical point, so its support
contains none.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology

namespace PDE.Analysis.StationaryPhase

variable {n : ℕ}

/-- Construct compact smooth pieces near each critical point and a compact smooth
remainder supported away from all critical points. -/
theorem exists_stationary_partition
    {φ : ℝ^n → ℝ} {a : ℝ^n → ℂ}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hc : HasCompactSupport a)
    (C : Finset (ℝ^n))
    (hC : ∀ p, p ∈ C ↔ p ∈ tsupport a ∧ fderiv ℝ φ p = 0)
    (U : C → Set (ℝ^n)) (hU : ∀ p, IsOpen (U p)) (hpU : ∀ p, (p : ℝ^n) ∈ U p) :
    ∃ (b : C → ℝ^n → ℂ) (r : ℝ^n → ℂ),
      (∀ p, ContDiff ℝ (⊤ : ℕ∞) (b p) ∧ HasCompactSupport (b p) ∧
        tsupport (b p) ⊆ U p ∧ b p p = a p) ∧
      ContDiff ℝ (⊤ : ℕ∞) r ∧ HasCompactSupport r ∧
      (∀ x ∈ tsupport r, fderiv ℝ φ x ≠ 0) ∧
      ∀ x, a x = r x + ∑ p, b p x := by
  classical
  choose χ hχd hχc hχU hχone hχother using
    fun p : C ↦ exists_cutoff_separating_finset C (p : ℝ^n) (hU p) (hpU p)
  let b (p : C) (x : ℝ^n) : ℂ := χ p x • a x
  let r (x : ℝ^n) : ℂ := a x - ∑ p : C, b p x
  have hbd (p : C) : ContDiff ℝ (⊤ : ℕ∞) (b p) := (hχd p).smul ha
  have hrSupp : tsupport r ⊆ tsupport a := by
    apply closure_minimal _ (isClosed_tsupport a)
    intro x hx
    by_contra hxa
    have hax := image_eq_zero_of_notMem_tsupport hxa
    exact hx (by simp [r, b, hax])
  have hrzero (p : C) : r =ᶠ[𝓝 (p : ℝ^n)] 0 := by
    have hnear (q : C) :
        ∀ᶠ x in 𝓝 (p : ℝ^n), b q x = if q = p then a x else 0 := by
      by_cases hqp : q = p
      · subst q
        filter_upwards [hχone p] with x hx
        simp [b, hx]
      · have hpq : (p : ℝ^n) ≠ q := fun h ↦ hqp (Subtype.ext h.symm)
        have hz := notMem_tsupport_iff_eventuallyEq.mp
          (hχother q p p.property hpq)
        filter_upwards [hz] with x hx
        simp [b, hx, hqp]
    filter_upwards [Filter.eventually_all.mpr hnear] with x hx
    have hsum : (∑ q : C, b q x) = a x := by
      simp_rw [hx]
      simp
    change a x - ∑ q : C, b q x = 0
    rw [hsum, sub_self]
  refine ⟨b, r, ?_, ha.sub (ContDiff.sum fun p _ ↦ hbd p),
    hc.of_isClosed_subset (isClosed_tsupport r) hrSupp, ?_, ?_⟩
  · intro p
    refine ⟨hbd p, (hχc p).smul_right,
      (tsupport_smul_subset_left (χ p) a).trans (hχU p), ?_⟩
    have hp := (hχone p).self_of_nhds
    simp [b, hp]
  · intro x hx hd
    have hxC : x ∈ C := (hC x).mpr ⟨hrSupp hx, hd⟩
    exact (notMem_tsupport_iff_eventuallyEq.mpr (hrzero ⟨x, hxC⟩)) hx
  · intro x
    simp [r]

end PDE.Analysis.StationaryPhase
