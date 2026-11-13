/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.LocalExtr.Basic
import CAS.ExactTactic

/-!
# Comparison with a coercive function through derivative norms

A nonnegative continuous function, vanishing at one point and with nonzero derivative
elsewhere, dominates a coercive comparison function whose derivative has smaller norm.
The proof constructs a global minimum of a smooth scalar penalty and applies Fermat's
theorem. No differentiability at the distinguished point or completeness assumption on
the ambient normed space is needed.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open Filter Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A coercive comparison function with dominated derivative norm lies below a
nonnegative function whose derivative is nonzero away from their common zero. -/
theorem coercive_le_of_fderiv_norm_le {f b : E → ℝ} {c : E}
    (hf : Continuous f) (hb : Continuous b) (hfnonneg : ∀ y, 0 ≤ f y)
    (hfc : f c = 0) (hbc : b c = 0)
    (hbtop : Tendsto b (cocompact E) atTop)
    (hfd : ∀ y, y ≠ c → DifferentiableAt ℝ f y)
    (hbd : ∀ y, y ≠ c → DifferentiableAt ℝ b y)
    (hfne : ∀ y, y ≠ c → fderiv ℝ f y ≠ 0)
    (hnorm : ∀ y, y ≠ c → ‖fderiv ℝ b y‖ ≤ ‖fderiv ℝ f y‖)
    (x : E) : b x ≤ f x := by
  by_contra h
  have hgap : f x < b x := lt_of_not_ge h
  let δ := (b x - f x) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let F : E → ℝ := fun y ↦ f y + √(δ ^ 2 + (b y - b x) ^ 2)
  have hF : Continuous F := hf.add
    ((continuous_const.add ((hb.sub continuous_const).pow 2)).sqrt)
  have hFlower (y : E) : b y - b x ≤ F y := by
    have hs : b y - b x ≤ √(δ ^ 2 + (b y - b x) ^ 2) :=
      Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg δ])
    exact hs.trans (le_add_of_nonneg_left (hfnonneg y))
  have hFtop : Tendsto F (cocompact E) atTop := by
    refine tendsto_atTop.2 fun r ↦ ?_
    filter_upwards [hbtop.eventually_ge_atTop (r + b x)] with y hy
    exact (by linarith : r ≤ b y - b x).trans (hFlower y)
  obtain ⟨y, hy⟩ := hF.exists_forall_le hFtop
  have hyc : y = c := by
    by_contra hyc
    let s := b y - b x
    let α := s / √(δ ^ 2 + s ^ 2)
    have hsq : 0 < δ ^ 2 + s ^ 2 := by positivity
    have hsqrt : 0 < √(δ ^ 2 + s ^ 2) := Real.sqrt_pos.mpr hsq
    have hα : |α| < 1 := by
      have hs : |s| < √(δ ^ 2 + s ^ 2) := by
        nlinarith [Real.sq_sqrt hsq.le, sq_abs s, sq_pos_of_pos hδ]
      simpa [α, abs_div, abs_of_pos hsqrt] using (div_lt_one hsqrt).mpr hs
    have hψ : HasDerivAt (fun z : ℝ ↦ √(δ ^ 2 + z ^ 2)) α s := by
      dsimp [α]
      cas using hδ
    have hpen := hψ.comp_hasFDerivAt y ((hbd y hyc).hasFDerivAt.sub_const (b x))
    have hDF : HasFDerivAt F
        (fderiv ℝ f y + α • fderiv ℝ b y) y :=
      (hfd y hyc).hasFDerivAt.add hpen
    have hmin : IsLocalMin F y := Filter.Eventually.of_forall hy
    have hzero := hmin.hasFDerivAt_eq_zero hDF
    have hn : ‖fderiv ℝ f y‖ = |α| * ‖fderiv ℝ b y‖ := by
      rw [eq_neg_of_add_eq_zero_left hzero, norm_neg, norm_smul, Real.norm_eq_abs]
    have hlt : ‖fderiv ℝ f y‖ < ‖fderiv ℝ f y‖ := calc
      ‖fderiv ℝ f y‖ = |α| * ‖fderiv ℝ b y‖ := hn
      _ ≤ |α| * ‖fderiv ℝ f y‖ :=
        mul_le_mul_of_nonneg_left (hnorm y hyc) (abs_nonneg α)
      _ < 1 * ‖fderiv ℝ f y‖ :=
        mul_lt_mul_of_pos_right hα (norm_pos_iff.mpr (hfne y hyc))
      _ = ‖fderiv ℝ f y‖ := one_mul _
    exact (lt_irrefl _) hlt
  subst y
  have hx := hy x
  have hc : b x ≤ √(δ ^ 2 + (b c - b x) ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    rw [hbc]
    nlinarith [sq_nonneg δ]
  simp only [F, hfc, sub_self, zero_pow (by decide : 2 ≠ 0), add_zero,
    Real.sqrt_sq hδ.le, zero_add] at hx
  dsimp [δ] at hx hc
  linarith

end PDE.Analysis
