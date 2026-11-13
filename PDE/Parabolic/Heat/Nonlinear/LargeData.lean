/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Variational.Dirichlet
public import PDE.Elliptic.Variational.Eigenfunction.DirichletProbability
public import PDE.Analysis.Calculus.AbsolutelyContinuous.PowerGrowth
public import PDE.Analysis.MeasureTheory.Integral.WeightedJensen
import CAS.ExactTactic
import PDE.Analysis.Evolution.Integrated.Regularity
import PDE.Analysis.Evolution.LionsMagenes.Basic.WeakDerivative

/-!
# Large-data nonexistence for the nonlinear Dirichlet heat equation

Let `F` be convex on `[0, ∞)`. Testing the weak equation `uₜ - Δu = F(u)` of a nonnegative solution
against a normalized positive first Dirichlet eigenfunction `w` gives an absolutely continuous
moment `η(t) = ⟪u(t), w⟫` with `F(η) ≤ η' + λη` almost everywhere (`exists_eigenfunction_moment`).
The weak eigenvalue equation identifies the diffusion term, and the weighted Jensen inequality
bounds the reaction from below. If moreover `F(s) ≥ c sᵖ` for `s ≥ 0` and `p > 1`, scalar comparison
excludes solutions on a prescribed finite interval when the initial moment is large enough
(`initial_moment_bound`, `initial_moment_bound_one_sub_exp`,
`exists_weight_for_large_data_nonexistence`); the time bound is a sufficient condition for
nonexistence. For `F(u) = u²` there is no global nonnegative weak solution when `η(0) > λ`
(`not_global_square_reaction_of_eigenvalue_lt_initial_moment`).

The last statement is Evans's §9.4.1, Theorem 1, with his threshold (3), for nonnegative weak
solutions.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.4.1, Theorem 1 (Blow-up for large data) and its proof,
  (3)-(5), pp. 548-549.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Sobolev InnerProductSpace
open SobolevSpace SobolevSpace.GraphSpace PDE.Analysis PDE.Analysis.Evolution

namespace HeatEquation.Nonlinear

variable {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}

/-- A nonnegative energy trajectory whose dual forcing is the reaction `F(u)`.
The identity and integrability hold against every zero-trace energy test, not
only against the eigenfunction used in the nonexistence argument. -/
def HasNonnegativeReactionForcing
    (F : ℝ → ℝ)
    (ell : Lp (StrongDual ℝ (H¹₀(Ω))) 2 (volume.restrict (Ioc a b)))
    (u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b))) : Prop :=
  ∀ᵐ t ∂volume.restrict (Ioc a b),
    (∀ᵐ x ∂domainMeasure n Ω, 0 ≤ baseCoordCLM (u t) x) ∧
    ∀ v : H¹₀(Ω),
      Integrable (fun x ↦ baseCoordCLM v x * F (baseCoordCLM (u t) x))
        (domainMeasure n Ω) ∧
      ell t v = ∫ x, baseCoordCLM v x * F (baseCoordCLM (u t) x) ∂domainMeasure n Ω

/-- The weak nonlinear PDE implies the first-eigenfunction moment inequality.
The continuous representative and its initial trace are constructed from the
integrated weak solution; neither a scalar curve nor its inequality is assumed. -/
theorem exists_eigenfunction_moment
    (hΩ : IsOpen Ω) (hab : a < b) (w : FirstDirichletEigenfunctionWeight Ω)
    {F : ℝ → ℝ} (hconvex : ConvexOn ℝ (Ici 0) F)
    {ell : Lp (StrongDual ℝ (H¹₀(Ω))) 2 (volume.restrict (Ioc a b))}
    {u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b))} {uInit : DerivLp n 2 Ω}
    (hu : Variational.Dirichlet.IsWeakSolution hΩ ell u uInit)
    (hreact : HasNonnegativeReactionForcing F ell u) :
    ∃ M : ℝ → ℝ, AbsolutelyContinuousOnInterval M a b ∧
      M a = ⟪uInit, baseCoordCLM w.vector⟫_ℝ ∧
      (∀ᵐ t ∂volume.restrict (Ioc a b), 0 ≤ M t) ∧
      (∀ᵐ t ∂volume.restrict (Ioc a b),
        F (M t) ≤ deriv M t + w.eigenvalue * M t) := by
  change IsGelfandIntegratedWeakSolution (h10L2GelfandTriple hΩ)
    Variational.Dirichlet.form (fun t ↦ ell t) u uInit at hu
  obtain ⟨g, E, _, hinit, hres⟩ :=
    hu.exists_continuousPivotEvolutionOn_initial_L2
      (fun _ ↦ aestronglyMeasurable_const) ‖dirichletForm (n := n) (Ω := Ω)‖
      (by filter_upwards with t; exact le_rfl) hab
  let M : ℝ → ℝ := fun t ↦ ⟪E.representative t, baseCoordCLM w.vector⟫_ℝ
  have hpairInt : IntervalIntegrable (fun t ↦ g t w.vector) volume a b :=
    ⟨(ContinuousLinearMap.apply ℝ ℝ w.vector).integrable_comp
      E.integratedDerivative.intervalIntegrable.1,
    (ContinuousLinearMap.apply ℝ ℝ w.vector).integrable_comp
      E.integratedDerivative.intervalIntegrable.2⟩
  have hM : AbsolutelyContinuousOnInterval M a b :=
    absolutelyContinuousOnInterval_of_eq_add_integral hpairInt
      (fun _ ht ↦ E.integratedDerivative.pairing_eq_add_integral w.vector ht)
  have hrep : ∀ᵐ t ∂volume.restrict (Ioc a b),
      E.representative t = baseCoordCLM (u t) :=
    E.ae_eq_inclusion.filter_mono (ae_mono (Measure.restrict_mono_set _
      (by rw [uIcc_of_le hab.le]; exact Ioc_subset_Icc_self)))
  have hderiv : ∀ᵐ t ∂volume.restrict (Ioc a b), HasDerivAt M (g t w.vector) t := by
    filter_upwards [E.integratedDerivative.ae_hasDerivAt_pivotToDual hab] with t ht
    exact (ContinuousLinearMap.apply ℝ ℝ w.vector).hasFDerivAt.comp_hasDerivAt t ht
  have hmom : ∀ᵐ t ∂volume.restrict (Ioc a b),
      M t = ∫ x, baseCoordCLM w.vector x * baseCoordCLM (u t) x ∂domainMeasure n Ω := by
    filter_upwards [hrep] with t ht
    dsimp only [M]
    rw [ht, real_inner_comm, L2.inner_def]
    simp only [Real.inner_apply]
  have hnonneg : ∀ᵐ t ∂volume.restrict (Ioc a b), 0 ≤ M t := by
    filter_upwards [hmom, hreact] with t ht hr
    rw [ht]
    exact integral_nonneg_of_ae (by
      filter_upwards [w.positive, hr.1] with x hx hu using mul_nonneg hx.le hu)
  refine ⟨M, hM, by simp only [M, hinit], hnonneg, ?_⟩
  filter_upwards [hmom, hreact, hderiv, hres, hrep]
    with t ht hr hd hg he
  have hprod : Integrable
      (fun x ↦ baseCoordCLM w.vector x * baseCoordCLM (u t) x) (domainMeasure n Ω) := by
    simpa only [Real.inner_apply] using
      (L2.integrable_inner (𝕜 := ℝ) (baseCoordCLM w.vector) (baseCoordCLM (u t)))
  have hj := convex_map_integral_mul_le
    (w.positive.mono fun _ h ↦ h.le) w.integral_eq_one hprod hr.1
    (hr.2 w.vector).1 hconvex
  have hdiffusion : dirichletForm (u t) w.vector = w.eigenvalue * M t := by
    rw [dirichletForm_symm, w.eigenfunction.2 (u t), massFormCLM_apply]
    dsimp only [M]
    rw [he, real_inner_comm]
  rw [← ht, ← (hr.2 w.vector).2] at hj
  rw [hd.deriv, hg]
  change F (M t) ≤ ell t w.vector - dirichletForm (u t) w.vector + w.eigenvalue * M t
  rw [hdiffusion]
  linarith

/-- A solution of the nonlinear weak heat equation obeys a strict initial-moment
bound whenever its reaction dominates `c s^p` on the nonnegative half-line. -/
theorem initial_moment_bound
    (hΩ : IsOpen Ω) (hab : a < b) (w : FirstDirichletEigenfunctionWeight Ω)
    {c p : ℝ} (hc : 0 ≤ c) (hp : 1 < p)
    {F : ℝ → ℝ} (hconvex : ConvexOn ℝ (Ici 0) F)
    (hpower : ∀ s, 0 ≤ s → c * s ^ p ≤ F s)
    {ell : Lp (StrongDual ℝ (H¹₀(Ω))) 2 (volume.restrict (Ioc a b))}
    {u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b))} {uInit : DerivLp n 2 Ω}
    (hu : Variational.Dirichlet.IsWeakSolution hΩ ell u uInit)
    (hreact : HasNonnegativeReactionForcing F ell u)
    (hinit : 0 < ⟪uInit, baseCoordCLM w.vector⟫_ℝ) :
    (p - 1) * (c * Real.exp (-(w.eigenvalue * (b - a)) * (p - 1))) * (b - a) <
      ⟪uInit, baseCoordCLM w.vector⟫_ℝ ^ (1 - p) := by
  obtain ⟨M, hM, hMa, hnonneg, hgrowth⟩ :=
    exists_eigenfunction_moment hΩ hab w hconvex hu hreact
  have h := mul_sub_lt_rpow_of_ae_damped_power_le_deriv hab.le hc hp
    w.eigenvalue_pos.le hM (hMa.symm ▸ hinit) hnonneg (by
      filter_upwards [hnonneg, hgrowth] with t ht hd
      exact (hpower (M t) ht).trans hd)
  rwa [hMa] at h

/-- On a nonempty bounded connected open domain, domain geometry supplies a
normalized positive first eigenfunction for which sufficiently large initial
moments exclude a nonnegative weak solution up to the prescribed time.

The forcing must represent the nonlinear reaction against every `H¹₀` test.
The explicit sufficient threshold is written using the decreasing power
`m₀^(1-p)`. No moment differential inequality is part of the hypotheses. -/
theorem exists_weight_for_large_data_nonexistence
    (hn : 0 < n) (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hconn : IsPreconnected Ω) (hne : Ω.Nonempty) (hab : a < b)
    {c p : ℝ} (hc : 0 < c) (hp : 1 < p)
    {F : ℝ → ℝ} (hconvex : ConvexOn ℝ (Ici 0) F)
    (hpower : ∀ s, 0 ≤ s → c * s ^ p ≤ F s) :
    ∃ w : FirstDirichletEigenfunctionWeight Ω,
      ∀ uInit : DerivLp n 2 Ω,
        0 < ⟪uInit, baseCoordCLM w.vector⟫_ℝ →
        ⟪uInit, baseCoordCLM w.vector⟫_ℝ ^ (1 - p) ≤
          (p - 1) * (c * Real.exp (-(w.eigenvalue * (b - a)) * (p - 1))) * (b - a) →
        ¬ ∃ (ell : Lp (StrongDual ℝ (H¹₀(Ω))) 2 (volume.restrict (Ioc a b)))
            (u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b))),
          Variational.Dirichlet.IsWeakSolution hΩ ell u uInit ∧
          HasNonnegativeReactionForcing F ell u := by
  obtain ⟨w⟩ := nonempty_firstDirichletEigenfunctionWeight hn hΩ hbounded hconn hne
  refine ⟨w, ?_⟩
  intro uInit hinit hlarge hsolution
  obtain ⟨ell, u, hu, hreact⟩ := hsolution
  exact (not_lt_of_ge hlarge)
    (initial_moment_bound hΩ hab w hc.le hp hconvex hpower hu hreact hinit)

/-- The integrating-factor bound `c (1 - exp (-λ (b - a) (p - 1))) < λ m₀ ^ (1 - p)` for a
nonlinear weak heat solution, where `λ` is the first Dirichlet eigenvalue and
`m₀ = ⟪uInit, w⟫` the initial moment. Keeping the full exponential integral gives the threshold
for global nonexistence. Since `x e^{-x} ≤ 1 - e^{-x}`, it is stronger than
`initial_moment_bound`. -/
theorem initial_moment_bound_one_sub_exp
    (hΩ : IsOpen Ω) (hab : a < b) (w : FirstDirichletEigenfunctionWeight Ω)
    {c p : ℝ} (hc : 0 ≤ c) (hp : 1 < p)
    {F : ℝ → ℝ} (hconvex : ConvexOn ℝ (Ici 0) F)
    (hpower : ∀ s, 0 ≤ s → c * s ^ p ≤ F s)
    {ell : Lp (StrongDual ℝ (H¹₀(Ω))) 2 (volume.restrict (Ioc a b))}
    {u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b))} {uInit : DerivLp n 2 Ω}
    (hu : Variational.Dirichlet.IsWeakSolution hΩ ell u uInit)
    (hreact : HasNonnegativeReactionForcing F ell u)
    (hinit : 0 < ⟪uInit, baseCoordCLM w.vector⟫_ℝ) :
    c * (1 - Real.exp (-(w.eigenvalue * (b - a)) * (p - 1))) <
      w.eigenvalue * ⟪uInit, baseCoordCLM w.vector⟫_ℝ ^ (1 - p) := by
  obtain ⟨M, hM, hMa, hnonneg, hgrowth⟩ :=
    exists_eigenfunction_moment hΩ hab w hconvex hu hreact
  have h := one_sub_exp_lt_mul_rpow_of_ae_damped_power_le_deriv hab.le hc hp
    w.eigenvalue_pos hM (hMa.symm ▸ hinit) hnonneg (by
      filter_upwards [hnonneg, hgrowth] with t ht hd
      exact (hpower (M t) ht).trans hd)
  rwa [hMa] at h

/-- The quadratic nonlinear Dirichlet heat equation has no global nonnegative
weak solution when its initial first-eigenfunction moment exceeds the eigenvalue.
This is the threshold (3) of Evans's §9.4.1, Theorem 1, for nonnegative weak solutions in
the energy formulation. The moment is derived from the weak PDE. -/
theorem not_global_square_reaction_of_eigenvalue_lt_initial_moment
    (hΩ : IsOpen Ω) (w : FirstDirichletEigenfunctionWeight Ω)
    (uInit : DerivLp n 2 Ω)
    (hlarge : w.eigenvalue < ⟪uInit, baseCoordCLM w.vector⟫_ℝ) :
    ¬ ∀ T : ℝ, 0 < T →
      ∃ (ell : Lp (StrongDual ℝ (H¹₀(Ω))) 2 (volume.restrict (Ioc 0 T)))
        (u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc 0 T))),
        Variational.Dirichlet.IsWeakSolution hΩ ell u uInit ∧
        HasNonnegativeReactionForcing (fun s ↦ s ^ (2 : ℕ)) ell u := by
  intro hglobal
  have hm := w.eigenvalue_pos.trans hlarge
  have hbound := le_mul_rpow_of_global_damped_power_trajectories
    (c := 1) (p := 2) hm (by norm_num) (by norm_num) w.eigenvalue_pos (by
      intro T hT
      obtain ⟨ell, u, hu, hr⟩ := hglobal T hT
      have hconvex : ConvexOn ℝ (Ici 0) (fun s : ℝ ↦ s ^ (2 : ℕ)) := by
        simpa only [Real.rpow_two] using (convexOn_rpow (p := 2) (by norm_num))
      obtain ⟨M, hM, hMa, hn, hd⟩ :=
        exists_eigenfunction_moment hΩ hT w hconvex hu hr
      refine ⟨M, hM, hMa, hn, ?_⟩
      simpa only [one_mul, Real.rpow_two] using hd)
  norm_num only [show (1 : ℝ) - 2 = -1 by norm_num, Real.rpow_neg_one,
    ← div_eq_mul_inv] at hbound
  have hle := (le_div_iff₀ hm).mp hbound
  exact (not_le_of_gt hlarge) (by simpa only [one_mul] using hle)

end HeatEquation.Nonlinear
