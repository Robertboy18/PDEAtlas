/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Nonlinear.DirichletMoment
public import PDE.Analysis.Calculus.AbsolutelyContinuous.PowerGrowth

/-!
# Large-data blowup for the closed-corner Dirichlet class

Let `Ω` be a bounded open set and `w ≥ 0` a Dirichlet eigenfunction of `-Δ` with eigenvalue `λ > 0`,
normalized by `∫ w = 1`, that is `C²` in `Ω` and continuous with zero values on the boundary. If
`g ≥ 0` and `∫ w g > λ`, then for some `T` no solution of `uₜ - Δu = u²` is `C²` in `(0, T) × Ω`,
continuous on `[0, T] × closure Ω`, zero on the lateral boundary and equal to `g` at time zero
(`not_global_interior_square_solution`, `not_global_square_solution_of_contDiffOn`). No derivative
of `u` or `w` on the boundary is used, and no regularity of the boundary is assumed.

The argument also bounds the lifespan. With `η₀ = ∫ w g`, a solution on `[0, T]` has
`T ≤ λ⁻¹ log (η₀ / (η₀ - λ))` (`IsInteriorDirichletSquareSolution.lifespan_le`). This is Kaplan's
bound: the moment `η = ∫ w u` satisfies `η' ≥ η² - λ η`, and the solution of `η' = η² - λ η`
from `η₀` blows up at this time, since `1 / η` solves the linear equation `v' = λ v - 1`.

The candidate is continuous at the initial/lateral corner. Bounded candidates with separate traces
and no corner condition are treated in `PDE.Parabolic.Heat.Nonlinear.BoundedDirichletBlowup`.

This is Evans's §9.4.1, Theorem 1, for nonnegative data, with solutions that are only continuous up
to the boundary and no regularity of the boundary.

## How it works

Evans differentiates `η = ∫ u w₁` and integrates by parts on all of `U`, his (4). We test instead
with compactly supported convex truncations of `w` (`dirichletTest`), so that no boundary derivative
of `u` is needed; they satisfy the eigenfunction inequality up to a uniform additive error
(`neg_mul_dirichletTest_le_laplacian`). Nonnegative data make the candidate nonnegative by the
minimum principle (`IsInteriorDirichletSquareSolution.nonneg`), which the Jensen step of the moment
inequality uses (`IsInteriorDirichletSquareSolution.compact_moment_inequality`). On each finite time
interval the continuous candidate is bounded, which controls the truncation error, and a strict
margin in the initial moment absorbs this error into slightly larger damping. For damping
`L = λ + δ`, initial moment above `η₀ - δ` and the interval `[0, T - δ]`, the scalar comparison
`one_sub_exp_le_mul_rpow_of_local_ae_damped_power_le_deriv` gives
`1 - exp (-L (T - δ)) ≤ L / (η₀ - δ)`, passing the positive-time moment estimates to the initial
trace by continuity. Letting `δ` tend to zero gives `1 - exp (-λ T) ≤ λ / η₀`, which is the bound.
Nonexistence of global solutions follows by taking `T` beyond it.

## References

* S. Kaplan, "On the growth of solutions of quasi-linear parabolic equations",
  *Comm. Pure Appl. Math.* 16 (1963), 305-330.
  <https://doi.org/10.1002/cpa.3160160307>
* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.4.1, Theorem 1 (Blow-up for large data) and its proof,
  (3)-(5), pp. 548-549.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open PDE (laplacian)
open PDE.Analysis
open scoped Topology

namespace HeatEquation.Nonlinear

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The moments of Kaplan's argument. For a solution on `[0, T₁]`, `0 < T < T₁` and
`λ < L < m < ∫ w g`, the moment `y` of `u` against a compactly supported truncation of `w` is
continuous on `[0, T]`, absolutely continuous on `[a, T]` for `0 < a`, starts above `m`, stays
nonnegative and satisfies `y² ≤ y' + L y` almost everywhere on `(0, T]`. The truncation error is
absorbed into the damping `L > λ`. -/
private theorem exists_damped_moment
    {g w : ℝ^n → ℝ} {u : ℝ → ℝ^n → ℝ} {lambda L m T T₁ : ℝ}
    (hu : IsInteriorDirichletSquareSolution Ω T₁ g u)
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hb : Bornology.IsBounded Ω)
    (hw : ContDiffOn ℝ 2 w Ω) (hwc : ContinuousOn w (closure Ω))
    (hwzero : ∀ x ∈ frontier Ω, w x = 0) (hwpos : ∀ x ∈ Ω, 0 ≤ w x)
    (hunit : ∫ x in Ω, w x = 1)
    (heigen : ∀ x ∈ Ω, laplacian w x = -lambda * w x)
    (hlambda : 0 < lambda) (hg : ∀ x ∈ Ω, 0 ≤ g x)
    (hlambdaL : lambda < L) (hLm : L < m) (hmM : m < ∫ x in Ω, w x * g x)
    (hT : 0 < T) (hTT : T < T₁) :
    ∃ y : ℝ → ℝ, ContinuousOn y (Icc 0 T) ∧
      (∀ a ∈ Ioc 0 T, AbsolutelyContinuousOnInterval y a T) ∧ m ≤ y 0 ∧
      (∀ᵐ t ∂volume.restrict (Ioc 0 T), 0 ≤ y t) ∧
      (∀ᵐ t ∂volume.restrict (Ioc 0 T), 1 * y t ^ (2 : ℝ) ≤ deriv y t + L * y t) := by
  have hL : 0 < L := hlambda.trans hlambdaL
  have hn := hu.nonneg hΩ hne hb (hT.trans hTT) hg
  have hint {f : ℝ^n → ℝ} (hf : ContinuousOn f (closure Ω)) : IntegrableOn f Ω :=
    hf.integrableOn_of_subset_isCompact hb.isCompact_closure hΩ.measurableSet
      subset_closure hb.measure_lt_top.ne
  have huc (t : ℝ) (ht : t ∈ Icc 0 T₁) : ContinuousOn (u t) (closure Ω) :=
    hu.continuous.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hx ↦ ⟨ht, hx⟩)
  obtain ⟨B, hB⟩ :=
    (isCompact_Icc.prod hb.isCompact_closure).exists_bound_of_continuousOn hu.continuous
  let C : ℝ := ∫ x in Ω, max 0 B
  have hCpos : 0 ≤ C := integral_nonneg fun _ ↦ le_max_left _ _
  have hC (t : ℝ) (ht : t ∈ Icc 0 T₁) : ∫ x in Ω, u t x ≤ C :=
    setIntegral_mono_on (hint (huc t ht)) (hint continuousOn_const) hΩ.measurableSet
      fun x hx ↦ (le_abs_self _).trans ((Real.norm_eq_abs _ ▸
        hB (t, x) ⟨ht, subset_closure hx⟩).trans (le_max_right _ _))
  obtain ⟨a, ha, hagap⟩ := exists_pos_mul_lt (sub_pos.mpr hmM) (2 * C)
  obtain ⟨b, hbpos, hbgap⟩ := exists_pos_mul_lt
    (mul_pos (sub_pos.mpr hlambdaL) hL) (2 * lambda * C)
  let ε := min a b
  have hε : 0 < ε := lt_min ha hbpos
  have herr₀ : 2 * ε * C < (∫ x in Ω, w x * g x) - m := by
    have h := (mul_le_mul_of_nonneg_left (min_le_left a b)
      (by positivity : 0 ≤ 2 * C)).trans_lt hagap
    dsimp only [ε]
    nlinarith
  have herr : (2 * lambda * ε) * C < (L - lambda) * L := by
    have h := (mul_le_mul_of_nonneg_left (min_le_right a b)
      (by positivity : 0 ≤ 2 * lambda * C)).trans_lt hbgap
    dsimp only [ε]
    nlinarith
  let φ := dirichletTest Ω w ε
  have hφ : ContDiff ℝ 2 φ := contDiff_dirichletTest hΩ hε hw hwc hwzero
  have hc : HasCompactSupport φ := hasCompactSupport_dirichletTest hb hε hwc hwzero
  have hs : tsupport φ ⊆ Ω := tsupport_dirichletTest_subset hε hwc hwzero
  have hφpos : ∀ x, 0 ≤ φ x := fun x ↦ (dirichletTest_bounds hwpos x).1
  have hrestrict (f : ℝ^n → ℝ) : (∫ x in Ω, φ x * f x) = ∫ x, φ x * f x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs h)), zero_mul]
  have hmass : ∫ x, φ x ≤ 1 := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦
      image_eq_zero_of_notMem_tsupport fun h ↦ hx (hs h), ← hunit]
    exact setIntegral_mono_on (hint hφ.continuous.continuousOn) (hint hwc) hΩ.measurableSet
      fun x hx ↦ by
        simpa only [indicator_of_mem hx] using (dirichletTest_bounds (ε := ε) hwpos x).2
  have hzero : m < ∫ x, φ x * u 0 x := by
    have ht0 : (0 : ℝ) ∈ Icc 0 T₁ := ⟨le_rfl, (hT.trans hTT).le⟩
    have heq : (∫ x in Ω, w x * u 0 x) = ∫ x in Ω, w x * g x :=
      setIntegral_congr_fun hΩ.measurableSet fun x hx ↦ by simp only [hu.initial x hx]
    have h := setIntegral_mono_on
      ((hint (hwc.mul (huc 0 ht0))).sub ((hint (huc 0 ht0)).const_mul (2 * ε)))
      (hint (hφ.continuous.continuousOn.mul (huc 0 ht0))) hΩ.measurableSet
      (fun x hx ↦ by
        simpa only [Pi.sub_apply, Pi.mul_apply, sub_mul] using mul_le_mul_of_nonneg_right
          (sub_two_mul_le_dirichletTest hε hwpos hx) (hn 0 ht0 x (subset_closure hx)))
    change (∫ x in Ω, w x * u 0 x - (2 * ε) * u 0 x) ≤
      ∫ x in Ω, φ x * u 0 x at h
    have hi : IntegrableOn (fun x ↦ w x * u 0 x) Ω := hint (hwc.mul (huc 0 ht0))
    rw [integral_sub hi ((hint (huc 0 ht0)).const_mul (2 * ε)), integral_const_mul, heq,
      hrestrict] at h
    have hC0 := mul_le_mul_of_nonneg_left (hC 0 ht0) (by positivity : 0 ≤ 2 * ε)
    linarith
  let y : ℝ → ℝ := fun t ↦ ∫ x, φ x * u t x
  have hy : ContinuousOn y (Icc 0 T₁) :=
    hu.compact_moment_continuous hφ.continuous hc hs
  have hd (t : ℝ) (ht : t ∈ Ioo 0 T₁) : DifferentiableAt ℝ y t :=
    (hu.hasDerivAt_compact_moment hΩ hφ.continuous hc hs ht).differentiableAt
  have hgrowth (t : ℝ) (ht : t ∈ Ioo 0 T₁) :
      y t ^ 2 ≤ deriv y t + lambda * y t + (2 * lambda * ε) * C :=
    hu.compact_moment_inequality hΩ hb hφ hc hs hφpos hmass
      (fun x _ ↦ neg_mul_dirichletTest_le_laplacian hΩ hε hlambda.le hw hwc
        hwzero hwpos heigen x) (by positivity) ht
      (fun x hx ↦ hn t (Ioo_subset_Icc_self ht) x (subset_closure hx))
      (hC t (Ioo_subset_Icc_self ht))
  have hbarrier := le_of_continuousOn_deriv_pos_at_level hy (hLm.trans hzero) hd (by
    intro t ht heq
    have h := hgrowth t ht
    rw [heq] at h
    nlinarith)
  refine ⟨y, hy.mono (Icc_subset_Icc le_rfl hTT.le), ?_, hzero.le, ?_, ?_⟩
  · intro a ha
    exact (hu.compact_moment_regularity hΩ hφ.continuous hc hs ha.1 hTT ha.2).1
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hL.le.trans (hbarrier t ⟨ht.1.le, by linarith [ht.2]⟩)
  · rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have ht' : t ∈ Ioo 0 T₁ := ⟨ht.1, by linarith [ht.2]⟩
    have h := hgrowth t ht'
    have hk := hbarrier t ⟨ht.1.le, ht'.2⟩
    have herr' := herr.trans_le (mul_le_mul_of_nonneg_left hk (sub_pos.mpr hlambdaL).le)
    simpa only [one_mul, Real.rpow_two] using (show y t ^ 2 ≤ deriv y t + L * y t by
      nlinarith)

/-- **Kaplan's lifespan bound.** Let `w ≥ 0` be a Dirichlet eigenfunction of `-Δ` on `Ω` with
eigenvalue `λ > 0`, normalized by `∫ w = 1`, and let `g ≥ 0` have `η₀ = ∫ w g > λ`. A solution of
`uₜ - Δu = u²` on `[0, T]` that is `C²` in the open cylinder, continuous on its closure, zero on
the lateral boundary and equal to `g` at time zero has `T ≤ λ⁻¹ log (η₀ / (η₀ - λ))`. This is the
time at which the solution of `η' = η² - λ η` from `η₀` blows up. -/
theorem IsInteriorDirichletSquareSolution.lifespan_le
    {g w : ℝ^n → ℝ} {u : ℝ → ℝ^n → ℝ} {lambda T : ℝ}
    (hu : IsInteriorDirichletSquareSolution Ω T g u)
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hb : Bornology.IsBounded Ω)
    (hw : ContDiffOn ℝ 2 w Ω) (hwc : ContinuousOn w (closure Ω))
    (hwzero : ∀ x ∈ frontier Ω, w x = 0) (hwpos : ∀ x ∈ Ω, 0 ≤ w x)
    (hunit : ∫ x in Ω, w x = 1)
    (heigen : ∀ x ∈ Ω, laplacian w x = -lambda * w x)
    (hlambda : 0 < lambda) (hg : ∀ x ∈ Ω, 0 ≤ g x)
    (hlarge : lambda < ∫ x in Ω, w x * g x) :
    T ≤ lambda⁻¹ * Real.log ((∫ x in Ω, w x * g x) / ((∫ x in Ω, w x * g x) - lambda)) := by
  set η := ∫ x in Ω, w x * g x with hη
  have hη0 : 0 < η := hlambda.trans hlarge
  have hgap : 0 < η - lambda := sub_pos.mpr hlarge
  rcases le_or_gt T 0 with hT | hT
  · refine hT.trans (mul_nonneg (inv_nonneg.mpr hlambda.le) (Real.log_nonneg ?_))
    rw [le_div_iff₀ hgap]
    linarith
  -- On `[0, T - δ]` the moments for the damping `λ + δ` and the initial bound `η - δ` give
  -- `1 - exp (-(λ + δ) (T - δ)) ≤ (λ + δ) / (η - δ)`; let `δ` tend to zero.
  have hkey : 1 - Real.exp (-(lambda * T)) ≤ lambda / η := by
    have hδ : 0 < min ((η - lambda) / 2) T := lt_min (by linarith) hT
    have hleft : ContinuousAt (fun δ : ℝ ↦ 1 - Real.exp (-((lambda + δ) * (T - δ)))) 0 := by
      fun_prop
    have hright : ContinuousAt (fun δ : ℝ ↦ (lambda + δ) / (η - δ)) 0 :=
      (continuousAt_const.add continuousAt_id).div (continuousAt_const.sub continuousAt_id)
        (by simpa using hη0.ne')
    have hlimL : Tendsto (fun δ : ℝ ↦ 1 - Real.exp (-((lambda + δ) * (T - δ)))) (𝓝[>] 0)
        (𝓝 (1 - Real.exp (-(lambda * T)))) := by
      simpa using hleft.tendsto.mono_left nhdsWithin_le_nhds
    have hlimR : Tendsto (fun δ : ℝ ↦ (lambda + δ) / (η - δ)) (𝓝[>] 0) (𝓝 (lambda / η)) := by
      simpa using hright.tendsto.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto_of_tendsto hlimL hlimR ?_
    filter_upwards [Ioo_mem_nhdsGT hδ] with δ hδ'
    obtain ⟨hδ0, hδ1⟩ := hδ'
    have hδη : δ < (η - lambda) / 2 := hδ1.trans_le (min_le_left _ _)
    have hδT : δ < T := hδ1.trans_le (min_le_right _ _)
    have hm : 0 < η - δ := by linarith
    obtain ⟨y, hy, hlocal, hzero, hn, hd⟩ := exists_damped_moment (L := lambda + δ)
      (m := η - δ) (T := T - δ) hu hΩ hne hb hw hwc hwzero hwpos hunit heigen hlambda hg
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    have h := one_sub_exp_le_mul_rpow_of_local_ae_damped_power_le_deriv (sub_pos.mpr hδT)
      zero_le_one one_lt_two (by linarith) hy hlocal (hm.trans_le hzero) hn hd
    have hy0 : y 0 ^ ((1 : ℝ) - 2) ≤ (η - δ)⁻¹ := by
      rw [show (1 : ℝ) - 2 = -1 by norm_num, Real.rpow_neg_one]
      exact inv_anti₀ hm hzero
    calc 1 - Real.exp (-((lambda + δ) * (T - δ)))
        ≤ (lambda + δ) * y 0 ^ ((1 : ℝ) - 2) := by
          simpa only [show (2 : ℝ) - 1 = 1 by norm_num, mul_one, one_mul] using h
      _ ≤ (lambda + δ) * (η - δ)⁻¹ := mul_le_mul_of_nonneg_left hy0 (by linarith)
      _ = (lambda + δ) / (η - δ) := (div_eq_mul_inv _ _).symm
  -- Solve `(η - λ) / η ≤ exp (-λ T)` for `T`.
  have h1 : (η - lambda) / η ≤ Real.exp (-(lambda * T)) := by
    rw [sub_div, div_self hη0.ne']
    linarith
  have h2 : Real.log ((η - lambda) / η) ≤ -(lambda * T) := by
    rw [← Real.log_exp (-(lambda * T))]
    exact Real.log_le_log (div_pos hgap hη0) h1
  have h3 : Real.log (η / (η - lambda)) = -Real.log ((η - lambda) / η) := by
    rw [← Real.log_inv, inv_div]
  rw [le_inv_mul_iff₀ hlambda]
  linarith

/-- Evans's first-eigenfunction threshold, for nonnegative data, excludes global Dirichlet
candidates that are `C²` in the open cylinder and continuous at the initial/lateral corner.
Neither time nor spatial derivatives on a closed face are assumed. The eigenfunction itself
only needs interior `C²` regularity and continuous zero boundary values. The lifespan bound
`IsInteriorDirichletSquareSolution.lifespan_le` says how long a solution can live. -/
theorem not_global_interior_square_solution
    {g w : ℝ^n → ℝ} {lambda : ℝ}
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hb : Bornology.IsBounded Ω)
    (hw : ContDiffOn ℝ 2 w Ω) (hwc : ContinuousOn w (closure Ω))
    (hwzero : ∀ x ∈ frontier Ω, w x = 0) (hwpos : ∀ x ∈ Ω, 0 ≤ w x)
    (hunit : ∫ x in Ω, w x = 1)
    (heigen : ∀ x ∈ Ω, laplacian w x = -lambda * w x)
    (hlambda : 0 < lambda) (hg : ∀ x ∈ Ω, 0 ≤ g x)
    (hlarge : lambda < ∫ x in Ω, w x * g x) :
    ¬ ∀ T : ℝ, 0 < T → ∃ u, IsInteriorDirichletSquareSolution Ω T g u := by
  intro hglobal
  have hB := le_max_left
    (lambda⁻¹ * Real.log ((∫ x in Ω, w x * g x) / ((∫ x in Ω, w x * g x) - lambda))) 0
  have h0 := le_max_right
    (lambda⁻¹ * Real.log ((∫ x in Ω, w x * g x) / ((∫ x in Ω, w x * g x) - lambda))) 0
  obtain ⟨u, hu⟩ := hglobal _ (add_pos_of_nonneg_of_pos h0 one_pos)
  have h := hu.lifespan_le hΩ hne hb hw hwc hwzero hwpos hunit heigen hlambda hg hlarge
  linarith

/-- Explicit PDE form of the closed-corner Dirichlet theorem. Joint continuity
on the closed cylinder includes the initial/lateral corner; it is stronger than
separate initial and lateral traces. No derivative trace is required. -/
theorem not_global_square_solution_of_contDiffOn
    {g w : ℝ^n → ℝ} {lambda : ℝ}
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hb : Bornology.IsBounded Ω)
    (hw : ContDiffOn ℝ 2 w Ω) (hwc : ContinuousOn w (closure Ω))
    (hwzero : ∀ x ∈ frontier Ω, w x = 0) (hwpos : ∀ x ∈ Ω, 0 ≤ w x)
    (hunit : ∫ x in Ω, w x = 1)
    (heigen : ∀ x ∈ Ω, laplacian w x = -lambda * w x)
    (hlambda : 0 < lambda) (hg : ∀ x ∈ Ω, 0 ≤ g x)
    (hlarge : lambda < ∫ x in Ω, w x * g x) :
    ¬ ∀ T : ℝ, 0 < T → ∃ u : ℝ → ℝ^n → ℝ,
      ContinuousOn u.uncurry (Icc 0 T ×ˢ closure Ω) ∧
      ContDiffOn ℝ 2 u.uncurry (Ioo 0 T ×ˢ Ω) ∧
      (∀ t ∈ Ioo 0 T, ∀ x ∈ Ω,
        deriv (fun r ↦ u r x) t - laplacian (u t) x = u t x ^ 2) ∧
      (∀ x ∈ frontier Ω, ∀ t ∈ Ioo 0 T, u t x = 0) ∧
      (∀ x ∈ Ω, u 0 x = g x) := by
  intro hglobal
  apply not_global_interior_square_solution hΩ hne hb hw hwc hwzero hwpos hunit heigen
    hlambda hg hlarge
  intro T hT
  obtain ⟨u, hc, hs, heq, hboundary, hinit⟩ := hglobal T hT
  exact ⟨u, hc, hs, heq, hboundary, hinit⟩

end HeatEquation.Nonlinear
