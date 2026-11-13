/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.LocalExtension
public import PDE.FDeriv.PartialDeriv.Dilation
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import PDE.Spaces.Sobolev.Approximation.Mollification.WeakDerivatives
import PDE.Spaces.Sobolev.Calculus.Product.ClassicalLeibniz

/-!
# Expanding smooth cutoffs

Density of `C_c^∞(ℝ^n)` in `W^{k,p}(ℝ^n)` is proved by mollifying and then truncating with a
smooth cutoff `χ_R` that equals `1` on the ball of radius `R` and vanishes outside the ball of
radius `2R`. The Leibniz rule produces terms `∂^β χ_R · ∂^{α-β} u`, and these are harmless as
`R → ∞` precisely because `|∂^β χ_R| ≤ C_β R^{-|β|}` with `C_β` independent of `R`. We build
the cutoffs and prove that derivative bound; the truncation argument is in the
`SobolevApproximation` modules.

The cutoff is `cutoff R x = χ(x / R)` for the fixed bump `χ = PDE.Analysis.standardBump n`, a
Mathlib `ContDiffBump` with inner radius `1` and outer radius `2`. Every property of `cutoff R` is
transferred from `χ` by the scaling `x ↦ R⁻¹ • x`, and each coordinate derivative of the scaled
function picks up one factor of `R⁻¹` (`PDE.iteratedPartialDeriv_comp_const_smul`).

## Main results

* `cutoff_contDiff`, `cutoff_hasCompactSupport`, `cutoff_nonneg`, `cutoff_le_one`,
  `cutoff_eq_one_of_mem_closedBall`: `χ_R` is smooth, compactly supported (for `R ≠ 0`), takes
  values in `[0, 1]`, and equals `1` on `closedBall 0 R` (for `R > 0`).
* `exists_abs_le_iteratedPartialDeriv_of_hasCompactSupport`: every iterated coordinate derivative
  of a smooth compactly supported function is bounded.
* `exists_abs_iteratedPartialDeriv_cutoff_le`: `|∂^α χ_R| ≤ C R^{-|α|}` with one
  constant for all positive radii.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Universitext,
  Springer, 2011, Chapter 9, Sobolev Spaces and the Variational Formulation of Elliptic Boundary
  Value Problems in N Dimensions, pp. 263-323, for the truncation and regularization argument for
  the density of `C_c^∞(ℝ^N)` in `W^{1,p}(ℝ^N)`.
  <https://doi.org/10.1007/978-0-387-70914-7>
* R. A. Adams and J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Pure and Applied Mathematics 140,
  Academic Press, 2003, Chapter 3, The Sobolev Spaces W^{m,p}(Ω), pp. 59-78, for approximation by
  smooth functions.
  <https://shop.elsevier.com/books/sobolev-spaces/adams/978-0-12-044143-3>
-/

@[expose] public section

open PDE (iteratedPartialDeriv iteratedPartialDeriv_comp_const_smul)

noncomputable section

namespace SobolevSpace

open MeasureTheory Set Function ENNReal
open scoped Convolution Pointwise Topology
open PDE.Analysis (standardBump)

namespace Approximation

variable {n : ℕ}

/-- The base cutoff rescaled to radius `R`. -/
noncomputable def cutoff {n : ℕ} (R : ℝ) : ℝ^n → ℝ :=
  fun x ↦ (standardBump n) (R⁻¹ • x)

/-- The rescaled cutoff is smooth. -/
theorem cutoff_contDiff {n : ℕ} (R : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (cutoff (n := n) R) := by
  have hsmul : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ^n ↦ R⁻¹ • x) := by
    rw [show (fun x : ℝ^n ↦ R⁻¹ • x) =
      (fun _ : ℝ^n ↦ (R⁻¹ : ℝ)) • (fun x : ℝ^n ↦ x) by rfl]
    exact
      (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ^n ↦ (R⁻¹ : ℝ))).smul
        (contDiff_id : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ^n ↦ x))
  rw [show cutoff (n := n) R =
    (standardBump n : ℝ^n → ℝ) ∘ fun x : ℝ^n ↦ R⁻¹ • x by rfl]
  exact (ContDiffBump.contDiff (standardBump n)).comp hsmul

/-- A cutoff at nonzero scale has compact support. -/
theorem cutoff_hasCompactSupport {n : ℕ} {R : ℝ} (hR : R ≠ 0) :
    HasCompactSupport (cutoff (n := n) R) := by
  classical
  have hcs : HasCompactSupport ((standardBump n : ContDiffBump (0 : ℝ^n)) : ℝ^n → ℝ) :=
    (ContDiffBump.hasCompactSupport (standardBump n) : HasCompactSupport (standardBump n : ℝ^n → ℝ))
  rw [show cutoff (n := n) R =
    fun x : ℝ^n ↦ (standardBump n : ℝ^n → ℝ) (R⁻¹ • x) by rfl]
  exact hcs.comp_smul (inv_ne_zero hR)

/-- The expanding cutoff is supported in the closed ball of twice its radius. -/
theorem tsupport_cutoff_subset_closedBall {R : ℝ} (hR : 0 < R) :
    tsupport (cutoff (n := n) R) ⊆ Metric.closedBall 0 (2 * R) := by
  apply closure_minimal ?_ Metric.isClosed_closedBall
  intro x hx
  have hs : R⁻¹ • x ∈ Function.support (standardBump n : ℝ^n → ℝ) := hx
  rw [(standardBump n).support_eq] at hs
  have hscaled : ‖x‖ / R < 2 := by
    simpa [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos hR, div_eq_inv_mul, standardBump] using hs
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    ((div_lt_iff₀ hR).mp hscaled).le

/-- The cutoff is nonnegative. -/
theorem cutoff_nonneg {n : ℕ} (R : ℝ) (x : ℝ^n) : 0 ≤ cutoff (n := n) R x := by
  simpa [cutoff] using (standardBump n).nonneg (x := (R⁻¹ • x))

/-- The cutoff is bounded above by one. -/
theorem cutoff_le_one {n : ℕ} (R : ℝ) (x : ℝ^n) : cutoff (n := n) R x ≤ 1 := by
  simpa [cutoff] using (standardBump n).le_one (x := (R⁻¹ • x))

/-- The absolute value of the cutoff is bounded by one. -/
theorem cutoff_abs_le_one {n : ℕ} (R : ℝ) (x : ℝ^n) : |cutoff (n := n) R x| ≤ 1 := by
  have h0 : 0 ≤ cutoff (n := n) R x := cutoff_nonneg (n := n) R x
  have h1 : cutoff (n := n) R x ≤ 1 := cutoff_le_one (n := n) R x
  simpa [abs_of_nonneg h0] using h1

/-- A positive-scale cutoff equals one on the closed ball of radius `R`. -/
theorem cutoff_eq_one_of_mem_closedBall {n : ℕ} {R : ℝ} (hR : 0 < R) {x : ℝ^n}
    (hx : x ∈ Metric.closedBall (0 : ℝ^n) R) : cutoff (n := n) R x = 1 := by
  have hxnorm : ‖x‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hx
  have hx' : (R⁻¹ • x) ∈ Metric.closedBall (0 : ℝ^n) 1 := by
    have hnorm : ‖R⁻¹ • x‖ = ‖x‖ / R := by
      simp [norm_smul, Real.norm_eq_abs, abs_of_pos hR, div_eq_inv_mul]
    have hdiv : ‖x‖ / R ≤ (1 : ℝ) := (div_le_one hR).2 hxnorm
    have : ‖R⁻¹ • x‖ ≤ (1 : ℝ) := by simpa [hnorm] using hdiv
    simpa [Metric.mem_closedBall, dist_zero_right] using this
  simpa [cutoff] using (ContDiffBump.one_of_mem_closedBall (standardBump n) hx')

/-- Every iterated derivative of a smooth compactly supported function is uniformly bounded. -/
theorem exists_abs_le_iteratedPartialDeriv_of_hasCompactSupport {n : ℕ} {f : ℝ^n → ℝ}
    (hf_cs : HasCompactSupport f) (hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f) (α : List (Fin n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |iteratedPartialDeriv (n := n) α f x| ≤ C := by
  classical
  have hcs :
      HasCompactSupport (fun x : ℝ^n ↦ iteratedPartialDeriv (n := n) α f x) :=
    hasCompactSupport_iteratedPartialDeriv (n := n) (f := f) (hf := hf_cs) α
  have hcont :
      Continuous (fun x : ℝ^n ↦ iteratedPartialDeriv (n := n) α f x) :=
    (PDE.contDiff_top_iteratedPartialDeriv (n := n) (f := f) (hf := hf_smooth) α).continuous
  have hK : IsCompact (tsupport (fun x : ℝ^n ↦ iteratedPartialDeriv (n := n) α f x)) := by
    simpa [HasCompactSupport] using hcs
  have hB :
      Bornology.IsBounded
        ((fun x : ℝ^n ↦ iteratedPartialDeriv (n := n) α f x) ''
          tsupport (fun x : ℝ^n ↦ iteratedPartialDeriv (n := n) α f x)) :=
    (hK.image hcont).isBounded
  rcases hB.subset_closedBall (0 : ℝ) with ⟨C0, hC0⟩
  refine ⟨max C0 0, le_max_right _ _, ?_⟩
  intro x
  by_cases hx : x ∈ tsupport (fun x : ℝ^n ↦ iteratedPartialDeriv (n := n) α f x)
  · have hx_img :
        iteratedPartialDeriv (n := n) α f x ∈
          (fun x : ℝ^n ↦ iteratedPartialDeriv (n := n) α f x) ''
            tsupport (fun x : ℝ^n ↦ iteratedPartialDeriv (n := n) α f x) :=
      ⟨x, hx, rfl⟩
    have hx_ball : iteratedPartialDeriv (n := n) α f x ∈ Metric.closedBall (0 : ℝ) C0 := hC0 hx_img
    have hx_le : |iteratedPartialDeriv (n := n) α f x| ≤ C0 := by
      simpa [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hx_ball
    exact hx_le.trans (le_max_left _ _)
  · have hx0 : iteratedPartialDeriv (n := n) α f x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp [hx0]

/-- Each derivative costs a factor of `R⁻¹`, with the constant chosen before the radius. -/
theorem exists_abs_iteratedPartialDeriv_cutoff_le (α : List (Fin n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℝ), 0 < R → ∀ x : ℝ^n,
      |iteratedPartialDeriv α (cutoff R) x| ≤ C * R⁻¹ ^ α.length := by
  obtain ⟨C, hC, hbound⟩ := exists_abs_le_iteratedPartialDeriv_of_hasCompactSupport
    (standardBump n).hasCompactSupport (standardBump n).contDiff α
  refine ⟨C, hC, ?_⟩
  intro R hR x
  have hscale : 0 ≤ R⁻¹ ^ α.length := pow_nonneg (inv_nonneg.mpr hR.le) _
  unfold cutoff
  rw [iteratedPartialDeriv_comp_const_smul α (standardBump n).contDiff,
    abs_mul, abs_of_nonneg hscale]
  exact (mul_le_mul_of_nonneg_left (hbound _) hscale).trans_eq (mul_comm _ _)

end Approximation

end SobolevSpace
