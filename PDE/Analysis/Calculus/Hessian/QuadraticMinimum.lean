/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Taylor.Quadratic

/-!
# Quadratic lower bounds at a nondegenerate minimum

Positivity of the Hessian gives a uniform bound on the unit sphere.
The quadratic Taylor remainder then gives a local lower bound. For a strict
interior minimum on a compact set, the positive phase gap away from the minimum
extends this bound to the entire set.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open Filter Metric Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Positivity on nonzero vectors gives a uniform quadratic lower bound.
The empty unit sphere in dimension zero is allowed. -/
theorem exists_norm_sq_lower_bound (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v : E, v ≠ 0 → 0 < B v v) :
    ∃ c > 0, ∀ v : E, c * ‖v‖ ^ 2 ≤ B v v := by
  have hc : Continuous (fun v : E ↦ B v v) := by fun_prop
  obtain ⟨c, hcpos, hbound⟩ := (isCompact_sphere (0 : E) 1).exists_forall_le'
    hc.continuousOn (a := (0 : ℝ)) (fun v hv ↦ hB v (by
      intro hz
      simp [hz] at hv))
  refine ⟨c, hcpos, fun v ↦ ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  have hnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hunit : (‖v‖⁻¹ : ℝ) • v ∈ sphere (0 : E) 1 := by
    simpa only [mem_sphere, dist_zero_right, RCLike.ofReal_real_eq_id, id_eq] using
      (norm_smul_inv_norm (𝕜 := ℝ) hv)
  have hs := hbound _ hunit
  apply (le_div_iff₀ (sq_pos_of_ne_zero hnorm)).mp
  convert hs using 1
  simp only [map_smul, smul_apply, smul_eq_mul, div_eq_mul_inv, pow_two, mul_inv]
  ring

/-- A positive Hessian at a stationary point where `f` is `C²` gives a local quadratic lower
bound `c ‖h‖² ≤ f (x + h) - f x`. -/
theorem exists_local_quadratic_lower_bound {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hstationary : fderiv ℝ f x = 0)
    (hH : ∀ v : E, v ≠ 0 → 0 < fderiv ℝ (fderiv ℝ f) x v v) :
    ∃ c > 0, ∃ r > 0, ∀ h : E, ‖h‖ < r → c * ‖h‖ ^ 2 ≤ f (x + h) - f x := by
  obtain ⟨m, hm, hbound⟩ := exists_norm_sq_lower_bound (fderiv ℝ (fderiv ℝ f) x) hH
  obtain ⟨r, hr, hrem⟩ := exists_quadratic_remainder_bound hf
    (div_pos hm (by norm_num : (0 : ℝ) < 4))
  refine ⟨m / 4, div_pos hm (by norm_num), r, hr, fun h hh ↦ ?_⟩
  have hrest := hrem h hh
  simp only [hstationary, zero_apply, sub_zero, Real.norm_eq_abs] at hrest
  have hleft := (abs_le.mp hrest).1
  have hquadratic := hbound h
  nlinarith

/-- If `f` is continuous on a compact set `K` and `C²` at an interior point `x` that is a
strict minimum on `K` with positive Hessian, then `c ‖y - x‖² ≤ f y - f x` on all of `K` for
some `c > 0`. No tail gap is assumed. -/
theorem exists_quadratic_lower_bound_on_compact {f : E → ℝ} {x : E} {K : Set E}
    (hK : IsCompact K) (hx : x ∈ interior K) (hcont : ContinuousOn f K)
    (hf : ContDiffAt ℝ 2 f x)
    (hstrict : ∀ y ∈ K, y ≠ x → f x < f y)
    (hH : ∀ v : E, v ≠ 0 → 0 < fderiv ℝ (fderiv ℝ f) x v v) :
    ∃ c > 0, ∀ y ∈ K, c * ‖y - x‖ ^ 2 ≤ f y - f x := by
  have hminimum : IsMinOn f K x := by
    intro y hy
    by_cases heq : y = x
    · simp [heq]
    · exact (hstrict y hy heq).le
  have hstationary : fderiv ℝ f x = 0 :=
    (hminimum.isLocalMin (mem_interior_iff_mem_nhds.mp hx)).fderiv_eq_zero
  obtain ⟨c, hc, r, hr, hlocal⟩ :=
    exists_local_quadratic_lower_bound hf hstationary hH
  obtain ⟨gap, hgap, hfar⟩ := (hK.diff isOpen_ball).exists_forall_le'
    ((hcont.mono sdiff_subset).sub continuousOn_const) (a := (0 : ℝ)) (by
      intro y hy
      exact sub_pos.mpr (hstrict y hy.1 (by
        intro heq
        apply hy.2
        simpa only [heq] using (mem_ball_self hr : x ∈ ball x r))))
  obtain ⟨R, hR, hRadius⟩ := hK.isBounded.subset_closedBall_lt 0 x
  refine ⟨min c (gap / R ^ 2), lt_min hc (div_pos hgap (sq_pos_of_pos hR)), ?_⟩
  intro y hy
  by_cases hnear : ‖y - x‖ < r
  · have hsum : x + (y - x) = y := by abel
    calc
      min c (gap / R ^ 2) * ‖y - x‖ ^ 2 ≤ c * ‖y - x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)
      _ ≤ f y - f x := by simpa only [hsum] using hlocal (y - x) hnear
  · have hfarMem : y ∈ K \ ball x r :=
      ⟨hy, by simpa only [mem_ball, dist_eq_norm] using hnear⟩
    have hnorm : ‖y - x‖ ≤ R := by
      simpa only [mem_closedBall, dist_eq_norm] using hRadius hy
    calc
      min c (gap / R ^ 2) * ‖y - x‖ ^ 2 ≤ (gap / R ^ 2) * ‖y - x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)
      _ ≤ (gap / R ^ 2) * R ^ 2 := mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ (norm_nonneg _) hR.le).mpr hnorm)
        (div_nonneg hgap.le (sq_nonneg _))
      _ = gap := div_mul_cancel₀ gap (ne_of_gt (sq_pos_of_pos hR))
      _ ≤ f y - f x := hfar y hfarMem

end PDE.Analysis
