/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Analysis.Normed.Module.Connected
public import PDE.Spaces.Sobolev.Boundary.Atlas.Geometric.RegularLevel
public import PDE.Analysis.Calculus.AnnulusExtension.Bounds
public import PDE.Spaces.Sobolev.Inequalities.Poincare.Classical

/-!
# The annulus `1 < |y| < 2`: geometry and Poincaré's inequality

Poincaré's inequality with the mean holds on every bounded connected open set with `C¹` graph
boundary. The annulus `A = {1 < |y| < 2}` is not convex, but it is bounded, it is connected in
dimension at least two, and its boundary is a regular level set. So

`‖v - ⨍_A v‖_{Lᵖ(A)} ≤ C ‖Dv‖_{Lᵖ(A)}`

for every `C¹` function `v` on `ℝ^(n+2)` and every `1 ≤ p ≤ ∞`, with `C` independent of `v`.
Other radii are not treated. An annulus `r₁ < |y| < r₂` is the image of this one under a
dilation only when `r₂ = 2 r₁`, and the general case needs the same three facts with
`(|y|² - r₁²)(r₂² - |y|²)`.

## Main results

* `isBounded_unitAnnulus`: the annulus is bounded.
* `isConnected_unitAnnulus`: the annulus is connected in every real normed space of dimension
  greater than one.
* `unitAnnulus_eq_setOf_pos`, `hasContDiffGraphBoundary_unitAnnulus`: in `ℝⁿ` the annulus is the
  set where `(|y|² - 1)(4 - |y|²) > 0`, and for `n ≥ 1` its boundary is locally a smooth graph.
* `exists_eLpNorm_sub_average_le_unitAnnulus`: Poincaré's inequality above.

## How it works

The annulus is the image of `(1, 2) × S` under `(r, ω) ↦ r ω`, where `S` is the unit sphere,
which is connected in dimension at least two. The derivative of `(|y|² - 1)(4 - |y|²)` in the
direction `y` is `2 |y|² (5 - 2 |y|²)`, which is `6` on the inner sphere and `-24` on the outer
one, so the boundary is a regular level set
(`SobolevSpace.Boundary.hasContDiffGraphBoundary_of_regular_level`).
`SobolevSpace.exists_eLpNorm_sub_average_le` then gives the inequality.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.8.1, Theorem 1, p. 290: Poincaré's inequality.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal

namespace PDE.Analysis

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- The annulus `1 < |y| < 2` is bounded. -/
theorem isBounded_unitAnnulus : Bornology.IsBounded (unitAnnulus E) :=
  isBounded_ball.subset fun y hy ↦ show y ∈ ball (0 : E) 2 from by
    simpa only [mem_ball, dist_zero_right] using hy.2

/-- The annulus `1 < |y| < 2` is connected when the dimension is greater than one: it is the
image of `(1, 2) × S` under `(r, ω) ↦ r ω`, where `S` is the unit sphere. -/
theorem isConnected_unitAnnulus (h : 1 < Module.rank ℝ E) : IsConnected (unitAnnulus E) := by
  have himg : unitAnnulus E =
      (fun p : ℝ × E ↦ p.1 • p.2) '' (Ioo (1 : ℝ) 2 ×ˢ sphere (0 : E) 1) := by
    ext y
    constructor
    · rintro ⟨h1, h2⟩
      have hy : ‖y‖ ≠ 0 := by linarith
      refine ⟨(‖y‖, ‖y‖⁻¹ • y), ⟨⟨h1, h2⟩, ?_⟩, ?_⟩
      · simp [norm_smul, hy]
      · simp [smul_smul, hy]
    · rintro ⟨⟨r, ω⟩, ⟨⟨hr1, hr2⟩, hω⟩, rfl⟩
      have hω' : ‖ω‖ = 1 := by simpa using hω
      change 1 < ‖r • ω‖ ∧ ‖r • ω‖ < 2
      rw [norm_smul, hω', mul_one, Real.norm_of_nonneg (by linarith)]
      exact ⟨hr1, hr2⟩
  rw [himg]
  exact ((isConnected_Ioo (by norm_num)).prod (isConnected_sphere h 0 zero_le_one)).image _
    (continuous_fst.smul continuous_snd).continuousOn

end Normed

section Euclidean

variable {n : ℕ}

/-- The annulus `1 < |y| < 2` is the set where `(|y|² - 1)(4 - |y|²)` is positive. -/
theorem unitAnnulus_eq_setOf_pos :
    unitAnnulus (ℝ^n) = {y | 0 < (‖y‖ ^ 2 - 1) * (4 - ‖y‖ ^ 2)} := by
  ext y
  have hy := norm_nonneg y
  constructor
  · rintro ⟨h1, h2⟩
    have hs1 : 1 < ‖y‖ ^ 2 := one_lt_pow₀ h1 two_ne_zero
    have hs2 : ‖y‖ ^ 2 < 2 ^ 2 := pow_lt_pow_left₀ h2 hy two_ne_zero
    change 0 < (‖y‖ ^ 2 - 1) * (4 - ‖y‖ ^ 2)
    exact mul_pos (by linarith) (by linarith)
  · intro h
    change 0 < (‖y‖ ^ 2 - 1) * (4 - ‖y‖ ^ 2) at h
    change 1 < ‖y‖ ∧ ‖y‖ < 2
    rcases pos_and_pos_or_neg_and_neg_of_mul_pos h with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact ⟨by nlinarith, by nlinarith⟩
    · nlinarith

/-- **The boundary of the annulus `1 < |y| < 2` is locally a smooth graph**, in every dimension
`n ≥ 1`. The annulus is the positive set of `(|y|² - 1)(4 - |y|²)`, and the derivative of this
polynomial does not vanish on the two spheres. -/
theorem hasContDiffGraphBoundary_unitAnnulus [Fact (0 < n)] :
    SobolevSpace.Boundary.HasContDiffGraphBoundary ⊤ (unitAnnulus (ℝ^n)) := by
  let f : ℝ^n → ℝ := fun y ↦ (‖y‖ ^ 2 - 1) * (4 - ‖y‖ ^ 2)
  have hf : ContDiff ℝ (⊤ : ℕ∞) f :=
    ((contDiff_norm_sq ℝ).sub contDiff_const).mul (contDiff_const.sub (contDiff_norm_sq ℝ))
  have hlevel : ∀ x ∈ frontier (unitAnnulus (ℝ^n)), f x = 0 := fun x hx ↦ by
    rw [unitAnnulus_eq_setOf_pos] at hx
    exact (frontier_lt_subset_eq continuous_const hf.continuous hx).symm
  refine SobolevSpace.Boundary.hasContDiffGraphBoundary_of_regular_level (f := f) (c := 0)
    hf.contDiffOn isOpen_univ le_top (fun x hx ↦ ⟨mem_univ x, hlevel x hx⟩) (fun x hx hzero ↦ ?_)
    (fun x _ ↦ by rw [unitAnnulus_eq_setOf_pos]; rfl)
  -- the derivative in the direction `x`
  have hd := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.sub_const 1).mul
    ((hasFDerivAt_const (4 : ℝ) x).sub (hasStrictFDerivAt_norm_sq x).hasFDerivAt)
  have he := congrArg (fun L : ℝ^n →L[ℝ] ℝ ↦ L x) (hd.fderiv.symm.trans hzero)
  simp only [add_apply, smul_apply, sub_apply, zero_apply, innerSL_apply_apply, two_smul,
    real_inner_self_eq_norm_sq, smul_eq_mul, Pi.sub_apply] at he
  have h0 : (‖x‖ ^ 2 - 1) * (4 - ‖x‖ ^ 2) = 0 := hlevel x hx
  rcases mul_eq_zero.1 h0 with h | h
  · have hs : ‖x‖ ^ 2 = 1 := by linarith
    rw [hs] at he
    norm_num at he
  · have hs : ‖x‖ ^ 2 = 4 := by linarith
    rw [hs] at he
    norm_num at he

/-- **Poincaré's inequality on the annulus `1 < |y| < 2`**, in dimension at least two and for
every `1 ≤ p ≤ ∞`: there is a constant `C` such that every `C¹` function `v` on the whole space
satisfies `‖v - ⨍ v‖_{Lᵖ(A)} ≤ C ‖Dv‖_{Lᵖ(A)}`, where `A` is the annulus and the mean is taken
over `A`. -/
theorem exists_eLpNorm_sub_average_le_unitAnnulus (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ∃ C : ℝ≥0, ∀ v : ℝ^(n + 2) → ℝ, ContDiff ℝ 1 v →
      eLpNorm (fun x ↦ v x - ⨍ y in unitAnnulus (ℝ^(n + 2)), v y) p
          (volume.restrict (unitAnnulus (ℝ^(n + 2)))) ≤
        C * eLpNorm (fderiv ℝ v) p (volume.restrict (unitAnnulus (ℝ^(n + 2)))) := by
  have : Fact (0 < n + 2) := ⟨by omega⟩
  have hrank : 1 < Module.rank ℝ (ℝ^(n + 2)) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    exact_mod_cast (by omega : 1 < n + 2)
  exact SobolevSpace.exists_eLpNorm_sub_average_le (n := n + 1) isOpen_unitAnnulus
    isBounded_unitAnnulus (isConnected_unitAnnulus hrank)
    (hasContDiffGraphBoundary_unitAnnulus.hasC1GraphBoundary le_top) p

end Euclidean

end PDE.Analysis
