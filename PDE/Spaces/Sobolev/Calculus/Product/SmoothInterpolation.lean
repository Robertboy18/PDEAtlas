/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Product.Interpolation
public import PDE.Spaces.Sobolev.Approximation.Density.Constructors

/-!
# Interpolation estimates for smooth Sobolev representatives

The graph-coordinate estimates control classical derivatives and pointwise
values of smooth compactly supported representatives.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Set
open scoped ENNReal Sobolev

namespace SobolevSpace.Product

open GraphSpace GagliardoNirenberg

variable {n k : ℕ} [NeZero n]

/-- The interpolation bound applies directly to classical derivatives of a
smooth compactly supported input, using its Sobolev graph norm. -/
theorem exists_smooth_derivative_bound (hk : (n : ℝ) < 2 * (k : ℝ)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (u : ℝ^n → ℝ) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
      (hc : HasCompactSupport u) (d : ℕ), d ≤ k → ∀ α : List (Fin n), α.length ≤ d →
      lpNorm (iteratedPartialDeriv α u) (derivativeExponent d α.length) volume ≤
        C * ‖mkWkpSpaceOnOfContDiff (k := k) (p := 2) (Ω := univ) u hu hc‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_coordinate_lpNorm_bound hk
  refine ⟨C, hC, ?_⟩
  intro u hu hc d hd α hα
  let a : DerivIndex n d := derivIndexOfList α hα
  have hlen : a.toList.length = α.length := (derivIndexOfList_toList_perm α hα).length_eq
  have he := mkWkpSpaceOnOfContDiff_apply_ae (k := k) (p := (2 : ℝ≥0∞))
    (Ω := univ) u hu hc (a.castOrder hd)
  have hp := iteratedPartialDeriv_congr_perm_smooth hu (derivIndexOfList_toList_perm α hα)
  simp only [DerivIndex.castOrder_toList, domainMeasure, Measure.restrict_univ] at he
  have hb := hbound d hd a (mkWkpSpaceOnOfContDiff (k := k) (p := 2) (Ω := univ) u hu hc)
  simp only [domainMeasure, Measure.restrict_univ, hlen, ← toReal_eLpNorm] at hb ⊢
  rw [eLpNorm_congr_ae he] at hb
  change (eLpNorm (fun x ↦ iteratedPartialDeriv a.toList u x) _ _).toReal ≤ _ at hb
  rw [show (fun x ↦ iteratedPartialDeriv a.toList u x) = iteratedPartialDeriv α u from hp] at hb
  exact hb

omit [NeZero n] in
/-- A continuous representative satisfies its essential supremum bound everywhere. -/
theorem norm_le_lpNorm_top_of_continuous {u : ℝ^n → ℝ}
    (hu : Continuous u) (hm : MemLp u ∞ volume) (x : ℝ^n) :
    ‖u x‖ ≤ lpNorm u ∞ volume := by
  have hd := volume.dense_of_ae (ae_le_lpNorm_exponent_top hm)
  exact (isClosed_le hu.norm continuous_const).closure_subset_iff.mpr
    (fun _ hx ↦ hx) (hd x)

end SobolevSpace.Product
