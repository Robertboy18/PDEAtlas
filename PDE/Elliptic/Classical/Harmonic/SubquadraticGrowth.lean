/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.Harmonic.IteratedDerivativeEstimates
public import PDE.Elliptic.Classical.Harmonic.Reflection

/-!
# Harmonic functions of subquadratic growth

An entire harmonic function with `u(x) = o(|x|²)` is affine: the second-order interior estimate
`‖D²u(x)‖ ≤ n² sup_{B(x, 2r)} |u| / r²` tends to zero as `r → ∞`. A function `C²` on the closed
half-space `{x | 0 ≤ x k}`, harmonic inside, zero on the boundary and `o(|x|²)` is `c x_k` there:
its odd reflection is entire harmonic (`isHarmonicPDE_oddReflection`), hence affine, and odd
under `Rₖ`.

Growth `o(|x|²)` is sharp: `x₀ x₁` is harmonic and vanishes on both coordinate hyperplanes.

## Main results

* `IsHarmonicPDE.eq_add_fderiv_of_isLittleO`: an entire harmonic function with `u(x) = o(|x|²)`
  is affine.
* `eq_mul_apply_of_isLittleO`: a function `C²` on `{x | 0 ≤ x k}`, harmonic on `{x | 0 < x k}`,
  zero on `{x | x k = 0}` and `o(|x|²)` is `c x_k` on the closed half-space.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.3, Theorem 8 (Liouville's Theorem) and its proof, p. 30;
  §2.5, Problem 10 (a) (Reflection principle), p. 86.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Set Filter Topology Metric PDE.Common
open PDE (laplacian)

namespace LaplacianEquation

variable {n : ℕ}

/-- A function `o(|x|²)` at infinity is bounded by `C + ε |x|²` everywhere. -/
private theorem exists_abs_le_add_mul_sq {u : ℝ^n → ℝ} (hu : Continuous u)
    (hgrowth : u =o[cocompact (ℝ^n)] fun x ↦ ‖x‖ ^ 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ C, 0 ≤ C ∧ ∀ y, |u y| ≤ C + ε * ‖y‖ ^ 2 := by
  have h := hgrowth.bound hε
  rw [← Metric.cobounded_eq_cocompact, hasBasis_cobounded_norm.eventually_iff] at h
  obtain ⟨r, -, hr⟩ := h
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℝ^n) r).exists_bound_of_continuousOn
    hu.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun y ↦ ?_⟩
  have hsq : 0 ≤ ε * ‖y‖ ^ 2 := by positivity
  by_cases hy : r ≤ ‖y‖
  · have := hr hy
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖y‖ ^ 2)]
      at this
    linarith [le_max_right C 0]
  · have := hC y (by rw [mem_closedBall, dist_zero_right]; exact (not_le.mp hy).le)
    rw [Real.norm_eq_abs] at this
    linarith [le_max_left C 0]

/-- **Liouville's theorem for subquadratic growth.** An entire harmonic function with
`u(x) = o(|x|²)` as `|x| → ∞` is affine. -/
theorem IsHarmonicPDE.eq_add_fderiv_of_isLittleO [Fact (0 < n)] {u : ℝ^n → ℝ}
    (hu : IsHarmonicPDE n u univ) (hgrowth : u =o[cocompact (ℝ^n)] fun x ↦ ‖x‖ ^ 2)
    (x : ℝ^n) : u x = u 0 + fderiv ℝ u 0 x := by
  have hsmooth : ContDiff ℝ 2 u := contDiffOn_univ.mp hu.contDiffOn
  have hcont : Continuous u := hsmooth.continuous
  have hn : (0 : ℝ) < n := by exact_mod_cast (Fact.out : 0 < n)
  -- the second derivative vanishes
  have hD2 : ∀ z : ℝ^n, ‖iteratedFDeriv ℝ 2 u z‖ = 0 := by
    intro z
    by_contra hne
    set a := ‖iteratedFDeriv ℝ 2 u z‖
    have ha : 0 < a := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    set ε := a / (20 * (n : ℝ) ^ 2)
    have hε : 0 < ε := by positivity
    obtain ⟨C, hC0, hC⟩ := exists_abs_le_add_mul_sq hcont hgrowth hε
    set r := ‖z‖ + 1 + C / ε
    have hCε : 0 ≤ C / ε := by positivity
    have hr1 : 1 ≤ r := by linarith [norm_nonneg z]
    have hr : 0 < r := by linarith
    have hM : ∀ y ∈ closedBall z (((2 : ℕ) : ℝ) * r), |u y| ≤ C + ε * (3 * r) ^ 2 := by
      intro y hy
      rw [mem_closedBall, dist_eq_norm] at hy
      push_cast at hy
      refine (hC y).trans ?_
      gcongr
      linarith [norm_le_norm_add_norm_sub' y z]
    have hest := hu.norm_iteratedFDeriv_le isOpen_univ hr (subset_univ _) hM
    have hCr : C / r ^ 2 ≤ ε := by
      rw [div_le_iff₀ (by positivity)]
      have : C / ε ≤ r := by linarith [norm_nonneg z]
      have h2 : C ≤ ε * r := by rwa [div_le_iff₀ hε, mul_comm] at this
      nlinarith
    have : a ≤ (n : ℝ) ^ 2 * (C / r ^ 2 + 9 * ε) := by
      refine hest.trans (le_of_eq ?_)
      field_simp
      ring
    have : a ≤ (n : ℝ) ^ 2 * (10 * ε) := this.trans (by gcongr; linarith)
    have hval : (n : ℝ) ^ 2 * (10 * ε) = a / 2 := by
      simp only [ε]; field_simp; ring
    linarith
  -- so the derivative is constant
  have hfd (z : ℝ^n) : fderiv ℝ (fderiv ℝ u) z = 0 := by
    have h := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := u) (x := z) (n := 1)
    rw [norm_iteratedFDeriv_one] at h
    exact norm_eq_zero.mp (h.trans (hD2 z))
  have hdiff : Differentiable ℝ (fderiv ℝ u) :=
    (hsmooth.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have hconst : ∀ z, fderiv ℝ u z = fderiv ℝ u 0 := fun z ↦
    is_const_of_fderiv_eq_zero hdiff hfd z 0
  -- and `u` minus its linear part is constant
  set φ : ℝ^n → ℝ := fun y ↦ u y - fderiv ℝ u 0 y
  have hφd : Differentiable ℝ φ :=
    (hsmooth.differentiable (by norm_num)).sub (fderiv ℝ u 0).differentiable
  have hφ (z : ℝ^n) : fderiv ℝ φ z = 0 := by
    rw [(((hsmooth.differentiable (by norm_num)) z).hasFDerivAt.fun_sub
      (fderiv ℝ u 0).hasFDerivAt).fderiv, hconst, sub_self]
  have h := is_const_of_fderiv_eq_zero hφd hφ x 0
  simp only [φ, map_zero, sub_zero] at h
  linarith

/-- **Liouville's theorem on a half-space.** If `g` is `C²` on `{x | 0 ≤ x k}`, harmonic on
`{x | 0 < x k}`, zero on `{x | x k = 0}` and `g(x) = o(|x|²)` there, then `g = c x_k` on the
closed half-space. -/
theorem eq_mul_apply_of_isLittleO [Fact (0 < n)] (k : Fin n) {g : ℝ^n → ℝ}
    (hg : ContDiffOn ℝ 2 g {x | 0 ≤ x k}) (hΔ : ∀ x, 0 < x k → laplacian g x = 0)
    (hb : ∀ x, x k = 0 → g x = 0)
    (hgrowth : g =o[cocompact (ℝ^n) ⊓ 𝓟 {x | 0 ≤ x k}] fun x ↦ ‖x‖ ^ 2) :
    ∃ c, ∀ x, 0 ≤ x k → g x = c * x k := by
  set H := oddReflection k g
  set R := coordinateReflection k
  have hH : IsHarmonicPDE n H univ := isHarmonicPDE_oddReflection k hg hΔ hb
  have hRk : ∀ x, R x k = -x k := fun x ↦ coordinateReflection_apply_same k x
  have hRR : ∀ x, R (R x) = x := fun x ↦ coordinateReflection_involutive k x
  have hRn : ∀ x, ‖R x‖ = ‖x‖ := fun x ↦ norm_coordinateReflection k x
  -- growth of the reflection
  have hRt : Tendsto R (cocompact (ℝ^n)) (cocompact (ℝ^n)) := by
    rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
    simp only [hRn]
    exact tendsto_norm_cobounded_atTop
  have hHgrowth : H =o[cocompact (ℝ^n)] fun x ↦ ‖x‖ ^ 2 := by
    refine Asymptotics.IsLittleO.of_bound fun ε hε ↦ ?_
    have h1 := (eventually_inf_principal.mp (hgrowth.bound hε))
    have h2 := hRt.eventually h1
    filter_upwards [h1, h2] with x hx1 hx2
    by_cases hx : 0 ≤ x k
    · rw [show H x = g x from ite_eq_left hx]
      exact hx1 hx
    · rw [show H x = -g (R x) from ite_eq_right hx, norm_neg, ← hRn x]
      exact hx2 (by simp only [hRk]; linarith [not_le.mp hx])
  -- `H` is affine, vanishes at `0` and is odd under `R`
  have haff : ∀ x, H x = H 0 + fderiv ℝ H 0 x := hH.eq_add_fderiv_of_isLittleO hHgrowth
  have h0 : H 0 = 0 := by
    rw [show H 0 = g 0 from ite_eq_left (by simp)]
    exact hb 0 (by simp)
  set L := fderiv ℝ H 0
  have hodd : ∀ x, H (R x) = -H x := by
    intro x
    rcases lt_trichotomy (x k) 0 with hx | hx | hx
    · rw [show H (R x) = g (R x) from ite_eq_left (by rw [hRk]; linarith),
        show H x = -g (R x) from ite_eq_right (not_le.mpr hx), neg_neg]
    · have hfix : R x = x := (coordinateReflection_eq_self_iff k x).mpr hx
      rw [hfix, show H x = g x from ite_eq_left hx.ge, hb x hx, neg_zero]
    · rw [show H (R x) = -g (R (R x)) from ite_eq_right (by rw [hRk]; linarith), hRR,
        show H x = g x from ite_eq_left hx.le]
  have hLodd : ∀ x, L (R x) = -L x := by
    intro x
    have h := hodd x
    rw [haff (R x), haff x, h0, zero_add, zero_add] at h
    exact h
  set e : ℝ^n := EuclideanSpace.single k 1
  refine ⟨L e, fun x hx ↦ ?_⟩
  have ht : R (x - x k • e) = x - x k • e :=
    (coordinateReflection_eq_self_iff k _).mpr (show (x - x k • e) k = 0 by simp [e])
  have hLt : L (x - x k • e) = 0 := by
    have := hLodd (x - x k • e)
    rw [ht] at this
    linarith
  have hx' : x = (x - x k • e) + x k • e := by abel
  rw [show g x = H x from (ite_eq_left hx).symm, haff x, h0, zero_add, hx', map_add, hLt,
    zero_add, map_smul, smul_eq_mul]
  simp [e, mul_comm]

end LaplacianEquation
