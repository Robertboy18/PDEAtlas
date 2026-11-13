/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Integral.NonnegativeLimit
public import PDE.Parabolic.Heat.Nonlinear.BoundedDirichletBlowup

/-!
# Positive-time moment bounds without an initial corner bound

Every positive-time translate of a global classical Dirichlet solution of `uₜ - Δu = u²` is bounded
on finite cylinders, by continuity on a compact strip
(`isBoundedDirichletSquareSolution_shift_of_positive_time`). The signed Kaplan estimate therefore
bounds its first-eigenfunction moment by the first eigenvalue at every positive time
(`moment_le_eigenvalue_of_global_dirichlet_square_solution`). No regularity, bound or sign is
imposed at the initial/lateral corner for this estimate. For nonnegative candidates, Fatou's lemma
also bounds the initial moment and proves its integrability from the separate pointwise trace
(`integrable_initial_moment_and_le_eigenvalue_of_nonneg`).

The bound is the contrapositive of Evans's §9.4.1, Theorem 1, applied at each positive time: in his
proof a moment above `λ₁` blows up by the time `t*` of p. 549. For signed candidates the bound
concerns strictly positive times; the initial-moment statements assume that the candidate is
nonnegative.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.4.1, Theorem 1 (Blow-up for large data) and its proof,
  (3)-(5), pp. 548-549.
  <https://doi.org/10.1090/gsm/019>
* S. Kaplan, "On the growth of solutions of quasi-linear parabolic equations",
  *Comm. Pure Appl. Math.* 16 (1963), 305-330.
  <https://doi.org/10.1002/cpa.3160160307>
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open PDE (laplacian)
open scoped Topology

namespace HeatEquation.Nonlinear

variable {n : ℕ} {Ω : Set (ℝ^n)} {u : ℝ → ℝ^n → ℝ}

/-- Compactness supplies the bound for a finite cylinder beginning at positive
time. There is no hypothesis about the original solution near time zero. -/
theorem isBoundedDirichletSquareSolution_shift_of_positive_time
    (hb : Bornology.IsBounded Ω)
    (hc : ContinuousOn u.uncurry (Ioi 0 ×ˢ closure Ω))
    (hs : ContDiffOn ℝ 2 u.uncurry (Ioi 0 ×ˢ Ω))
    (heq : ∀ t > 0, ∀ x ∈ Ω,
      deriv (fun r ↦ u r x) t - laplacian (u t) x = u t x ^ 2)
    (hboundary : ∀ x ∈ frontier Ω, ∀ t > 0, u t x = 0)
    {a T : ℝ} (ha : 0 < a) :
    IsBoundedDirichletSquareSolution Ω T (u a) (fun t x ↦ u (a + t) x) := by
  have hcont : ContinuousOn (fun q : ℝ × ℝ^n ↦ u (a + q.1) q.2)
      (Icc 0 T ×ˢ closure Ω) :=
    hc.comp ((continuous_const.add continuous_fst).prodMk continuous_snd).continuousOn
      (fun q hq ↦ ⟨by change 0 < a + q.1; linarith [hq.1.1], hq.2⟩)
  obtain ⟨B, hB⟩ :=
    (isCompact_Icc.prod hb.isCompact_closure).exists_bound_of_continuousOn hcont
  refine ⟨hcont.mono (prod_mono Subset.rfl subset_closure),
    hcont.mono (prod_mono Ioc_subset_Icc_self Subset.rfl), ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨max B 0 + 1, by positivity, ?_⟩
    intro t ht x hx
    have h := hB (t, x) ⟨ht, subset_closure hx⟩
    have h' : |u (a + t) x| ≤ B := by simpa only [Real.norm_eq_abs] using h
    exact h'.trans (le_add_of_le_of_nonneg (le_max_left B 0) zero_le_one)
  · exact hs.comp ((contDiff_const.add contDiff_fst).prodMk contDiff_snd).contDiffOn
      (fun q hq ↦ ⟨by change 0 < a + q.1; linarith [hq.1.1], hq.2⟩)
  · intro t ht x hx
    rw [deriv_comp_const_add (fun r ↦ u r x) a t]
    exact heq (a + t) (by linarith [ht.1]) x hx
  · intro x hx t ht
    exact hboundary x hx (a + t) (by linarith [ht.1])
  · intro x _
    simp

/-- A global signed quadratic heat solution has first-eigenfunction moment at
most the first eigenvalue at every positive time. The only boundedness used is
derived on compact strips strictly away from the omitted initial corner. -/
theorem moment_le_eigenvalue_of_global_dirichlet_square_solution
    {w : ℝ^n → ℝ} {lambda : ℝ}
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hw : ContDiffOn ℝ 2 w Ω) (hwc : ContinuousOn w (closure Ω))
    (hwzero : ∀ x ∈ frontier Ω, w x = 0) (hwpos : ∀ x ∈ Ω, 0 < w x)
    (hunit : ∫ x in Ω, w x = 1)
    (heigen : ∀ x ∈ Ω, laplacian w x = -lambda * w x)
    (hlambda : 0 < lambda)
    (hc : ContinuousOn u.uncurry (Ioi 0 ×ˢ closure Ω))
    (hs : ContDiffOn ℝ 2 u.uncurry (Ioi 0 ×ˢ Ω))
    (heq : ∀ t > 0, ∀ x ∈ Ω,
      deriv (fun r ↦ u r x) t - laplacian (u t) x = u t x ^ 2)
    (hboundary : ∀ x ∈ frontier Ω, ∀ t > 0, u t x = 0)
    {a : ℝ} (ha : 0 < a) : (∫ x in Ω, w x * u a x) ≤ lambda := by
  by_contra h
  apply not_global_bounded_dirichlet_square_solution hΩ hb hw hwc hwzero hwpos hunit
    heigen hlambda (lt_of_not_ge h)
  intro T _
  exact ⟨fun t x ↦ u (a + t) x,
    isBoundedDirichletSquareSolution_shift_of_positive_time hb hc hs heq hboundary ha⟩

/-- Nonnegativity and separate initial traces suffice for the initial Kaplan
bound. Fatou proves the weighted initial datum integrable; no finite-cylinder
bound or weighted initial integrability is assumed. Candidate nonnegativity is
explicit and is not inferred here from the sign of the initial data. -/
theorem integrable_initial_moment_and_le_eigenvalue_of_nonneg
    {w g : ℝ^n → ℝ} {lambda : ℝ}
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hw : ContDiffOn ℝ 2 w Ω) (hwc : ContinuousOn w (closure Ω))
    (hwzero : ∀ x ∈ frontier Ω, w x = 0) (hwpos : ∀ x ∈ Ω, 0 < w x)
    (hunit : ∫ x in Ω, w x = 1)
    (heigen : ∀ x ∈ Ω, laplacian w x = -lambda * w x)
    (hlambda : 0 < lambda)
    (hc : ContinuousOn u.uncurry (Ioi 0 ×ˢ closure Ω))
    (hs : ContDiffOn ℝ 2 u.uncurry (Ioi 0 ×ˢ Ω))
    (heq : ∀ t > 0, ∀ x ∈ Ω,
      deriv (fun r ↦ u r x) t - laplacian (u t) x = u t x ^ 2)
    (hboundary : ∀ x ∈ frontier Ω, ∀ t > 0, u t x = 0)
    (hnonneg : ∀ t > 0, ∀ x ∈ Ω, 0 ≤ u t x)
    (htrace : ∀ x ∈ Ω, Tendsto (fun t ↦ u t x) (𝓝[>] 0) (𝓝 (g x))) :
    IntegrableOn (fun x ↦ w x * g x) Ω ∧ (∫ x in Ω, w x * g x) ≤ lambda := by
  let a : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1)
  have ha (k : ℕ) : 0 < a k := by dsimp [a]; positivity
  have hat : Tendsto a atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall ha⟩
  have hi (k : ℕ) : IntegrableOn (fun x ↦ w x * u (a k) x) Ω := by
    have huc : ContinuousOn (u (a k)) (closure Ω) :=
      hc.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun _ hx ↦ ⟨ha k, hx⟩)
    exact (hwc.mul huc).integrableOn_of_subset_isCompact hb.isCompact_closure
      hΩ.measurableSet subset_closure hb.measure_lt_top.ne
  apply integrable_and_integral_le_of_nonnegative_limit hi
  · intro k
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
    exact mul_nonneg (hwpos x hx).le (hnonneg (a k) (ha k) x hx)
  · exact Eventually.of_forall fun k ↦
      moment_le_eigenvalue_of_global_dirichlet_square_solution hΩ hb hw hwc hwzero hwpos
        hunit heigen hlambda hc hs heq hboundary (ha k)
  · filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
    exact ((htrace x hx).comp hat).const_mul (w x)

end HeatEquation.Nonlinear
