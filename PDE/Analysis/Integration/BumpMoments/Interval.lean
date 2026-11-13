/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.BumpMoments.Finite

/-!
# Independent moments for weights continuous on an interval

The weights need only be continuous on a closed interval containing the chosen
centers in its interior. Mathlib's interval projection extends them continuously
to the line. The normalized bumps are supported inside the interval, so their
weighted integrals are unchanged by that extension.
-/

@[expose] public noncomputable section

open Function MeasureTheory Set
open scoped ContDiff Matrix

namespace PDE.Analysis

/-- Local continuity on a closed interval suffices for independent smooth bump
moments. The weights may be arbitrary outside that interval. -/
theorem exists_bumps_moment_matrix_det_ne_zero_of_continuousOn_Icc
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {W : ℝ → ι → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hW : ContinuousOn W (Icc a b)) (x : ι → ℝ)
    (hx : ∀ j, x j ∈ Ioo a b)
    (hdet : (Matrix.of fun i j : ι ↦ W (x j) i).det ≠ 0) :
    ∃ β : ι → ℝ → ℝ,
      (∀ j, ContDiff ℝ ∞ (β j) ∧ HasCompactSupport (β j) ∧
        tsupport (β j) ⊆ Ioo a b ∧ (∀ t, 0 ≤ β j t) ∧
        (∫ t, β j t) = 1 ∧ ∀ i, Integrable (fun t ↦ β j t * W t i)) ∧
      Pairwise (fun j k ↦ Disjoint (tsupport (β j)) (tsupport (β k))) ∧
      (bumpMomentMatrix W β).det ≠ 0 := by
  let V : ℝ → ι → ℝ := fun t ↦ W (projIcc a b hab t)
  have hV : Continuous V := hW.domRestrict.comp continuous_projIcc
  have hVW {t : ℝ} (ht : t ∈ Icc a b) : V t = W t := by
    simp only [V, projIcc_of_mem hab ht]
  have hmatrix : (Matrix.of fun i j : ι ↦ V (x j) i) =
      (Matrix.of fun i j : ι ↦ W (x j) i) := by
    ext i j
    exact congrFun (hVW (Ioo_subset_Icc_self (hx j))) i
  obtain ⟨β, hβ, hdisjoint, hmoment⟩ :=
    exists_bumps_moment_matrix_det_ne_zero hV isOpen_Ioo x hx
      (hmatrix.symm ▸ hdet)
  have hintegrand (j i : ι) :
      (fun t ↦ β j t * W t i) = (fun t ↦ β j t * V t i) := by
    funext t
    by_cases ht : t ∈ tsupport (β j)
    · rw [hVW (Ioo_subset_Icc_self ((hβ j).2.2.1 ht))]
    · rw [image_eq_zero_of_notMem_tsupport ht, zero_mul, zero_mul]
  have hmoment_eq : bumpMomentMatrix W β = bumpMomentMatrix V β := by
    ext i j
    exact congrArg (fun f : ℝ → ℝ ↦ ∫ t, f t) (hintegrand j i)
  refine ⟨β, ?_, hdisjoint, hmoment_eq.symm ▸ hmoment⟩
  intro j
  rcases hβ j with ⟨hsmooth, hcompact, hinside, hnonneg, hmass, hint⟩
  refine ⟨hsmooth, hcompact, hinside, hnonneg, hmass, fun i ↦ ?_⟩
  rw [hintegrand j i]
  exact hint i

end PDE.Analysis
