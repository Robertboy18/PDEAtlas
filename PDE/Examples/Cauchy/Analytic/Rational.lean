/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Cauchy.Hypersurface.Existence
public import PDE.Cauchy.Hypersurface.Uniqueness
public import PDE.Analysis.Calculus.MultiIndex.PartialDeriv
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives

/-!
# Cauchy existence with a local rational coefficient

The equation `uₜ = 1 / (1 - u)` has zero initial value. Its right side is
analytic near the initial jet but has a pole at `u = 1`. The analytic existence
theorem `exists_analytic_solution_of_normal_data` gives a solution on a ball around
`0`, and the uniqueness theorem `eventuallyEq_of_analytic_solution_of_normal_data`
identifies its germ with `1 - √(1 - 2t)` (`exists_analytic_rational_solution`).
-/

@[expose] public noncomputable section

open Filter Set PDE.Analysis.MultiIndex
open scoped Topology Gradient

namespace PDE.Examples.Cauchy.Quasilinear.Analytic

/-- The analytic branch through zero of the rational Cauchy equation. -/
def rationalProfile (x : ℝ^1) : ℝ := 1 - Real.sqrt (1 - 2 * x 0)

private def rationalForcing
    (z : ℝ^1 × (∀ j : Fin 1, Sym (Fin 1) (j : ℕ) → ℝ)) : ℝ :=
  1 / (1 - z.2 0 Sym.nil)

private theorem analyticAt_rationalForcing
    (z : ℝ^1 × (∀ j : Fin 1, Sym (Fin 1) (j : ℕ) → ℝ))
    (hz : z.2 0 Sym.nil ≠ 1) :
    AnalyticAt ℝ rationalForcing z := by
  have hs : AnalyticAt ℝ
      (fun w : ℝ^1 × (∀ j : Fin 1, Sym (Fin 1) (j : ℕ) → ℝ) ↦ w.2) z :=
    analyticAt_snd
  have he := analyticAt_pi_iff.mp (analyticAt_pi_iff.mp hs 0) Sym.nil
  exact analyticAt_const.div (analyticAt_const.sub he) (sub_ne_zero.mpr hz.symm)

private theorem analyticAt_rationalProfile (x : ℝ^1) (hx : 0 < 1 - 2 * x 0) :
    AnalyticAt ℝ rationalProfile x := by
  have ha : AnalyticAt ℝ (fun y : ℝ^1 ↦ 1 - 2 * y 0) x :=
    analyticAt_const.sub
      (analyticAt_const.mul ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).analyticAt x))
  exact analyticAt_const.sub (ha.contDiffAt.sqrt hx.ne').analyticAt

private theorem rationalProfile_equation (x : ℝ^1) (hx : 0 < 1 - 2 * x 0) :
    coordinateDeriv (Sym.replicate 1 0) rationalProfile x =
      1 / (1 - rationalProfile x) := by
  rw [coordinateDeriv_replicate (j := 1) 0 (analyticAt_rationalProfile x hx).contDiffAt]
  simp only [Function.iterate_one]
  unfold rationalProfile
  cas using hx

private theorem time_regular :
    fderiv ℝ (fun x : ℝ^1 ↦ x 0) (0 : ℝ^1) ≠ 0 := by
  have h : fderiv ℝ (fun x : ℝ^1 ↦ x 0) (0 : ℝ^1)
      (EuclideanSpace.single 0 1) = 1 := by cas
  intro hz
  simp [hz] at h

private theorem time_normal :
    PDE.Analysis.Hypersurface.levelNormal (fun x : ℝ^1 ↦ x 0) (0 : ℝ^1) 0 = 1 := by
  have hg : ∇ (fun x : ℝ^1 ↦ x 0) (0 : ℝ^1) =
      EuclideanSpace.single 0 (1 : ℝ) := by
    ext i
    fin_cases i
    rw [gradient_apply_eq_partialDeriv]
    cas
  simp [PDE.Analysis.Hypersurface.levelNormal, hg]

/-- The equation `u' = 1 / (1 - u)` with `u 0 = 0` has an analytic solution on a ball
around `0`, and near `0` it equals `1 - √(1 - 2t)`. -/
theorem exists_analytic_rational_solution :
    ∃ r : ℝ, 0 < r ∧ ∃ u : ℝ^1 → ℝ,
      AnalyticOnNhd ℝ u (Metric.ball 0 r) ∧
      (∀ x ∈ Metric.ball 0 r,
        coordinateDeriv (Sym.replicate 1 0) u x = 1 / (1 - u x)) ∧
      u 0 = 0 ∧ u =ᶠ[𝓝 0] rationalProfile := by
  let φ : ℝ^1 → ℝ := fun x ↦ x 0
  let g : Fin 1 → ℝ^1 → ℝ := fun _ _ ↦ 0
  have hzero (f : ℝ^1 → ℝ) (x : ℝ^1) : coordinateJetLT 1 f x 0 Sym.nil = f x := rfl
  have hφ : AnalyticAt ℝ φ (0 : ℝ^1) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).analyticAt 0
  have hq : PDE.Analysis.Cauchy.normalDataJet φ g (0 : ℝ^1) 0 Sym.nil = 0 := by
    have hjet := PDE.Analysis.Cauchy.coordinateJetLT_eq_normalDataJet hφ
      (by rfl) time_regular g (fun _ ↦ analyticAt_const)
      (G := fun _ ↦ 0) analyticAt_const (by
        filter_upwards [] with x
        intro _ j
        fin_cases j
        simp [g])
    exact (congrFun (congrFun hjet 0) Sym.nil).symm
  have hsymbol (q : ∀ j : Fin 1, Sym (Fin 1) (j : ℕ) → ℝ) :
      ∑ α : Sym (Fin 1) 1, (fun _ _ ↦ (1 : ℝ)) α ((0 : ℝ^1), q) *
        monomial α (PDE.Analysis.Hypersurface.levelNormal φ 0) ≠ 0 := by
    rw [Fintype.sum_subsingleton _ (Sym.replicate 1 (0 : Fin 1)),
      one_mul, monomial_replicate, pow_one, time_normal]
    exact one_ne_zero
  obtain ⟨r, hr, _, u, hu, hP, hdata⟩ :=
    PDE.Cauchy.Quasilinear.Analytic.exists_analytic_solution_of_normal_data
      (d := 0) (k := 0) isOpen_univ (mem_univ (0 : ℝ^1))
      (fun _ _ ↦ 1) rationalForcing hφ rfl time_regular g
      (fun _ ↦ analyticAt_const) (fun _ ↦ analyticAt_const)
      (analyticAt_rationalForcing _ (by simp only [hq]; exact zero_ne_one))
      (hsymbol (PDE.Analysis.Cauchy.normalDataJet φ g 0))
  have hvalue : u 0 = 0 := by
    simpa only [Fin.val_zero, normalData_zero, g] using
      hdata 0 (Metric.mem_ball_self hr) rfl 0
  have hnormal : ∀ᶠ x in 𝓝 (0 : ℝ^1), φ x = 0 → ∀ j : Fin 1,
      normalData (j : ℕ) u (PDE.Analysis.Hypersurface.levelNormal φ x) x =
        normalData (j : ℕ) rationalProfile
          (PDE.Analysis.Hypersurface.levelNormal φ x) x := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ^1) hr] with x hx
    intro hx0 j
    have hgx := hdata x hx hx0 j
    fin_cases j
    simpa [normalData_zero, rationalProfile, g, φ, show x 0 = 0 from hx0] using hgx
  have hpositive : ∀ᶠ x in 𝓝 (0 : ℝ^1), 0 < 1 - 2 * x 0 :=
    (isOpen_lt continuous_const
      (continuous_const.sub (continuous_const.mul
        (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).continuous))).mem_nhds (by simp)
  have heq := PDE.Cauchy.Quasilinear.Analytic.eventuallyEq_of_analytic_solution_of_normal_data
    (d := 0) (k := 0)
    (fun _ _ ↦ 1) rationalForcing (fun _ ↦ analyticAt_const)
    (analyticAt_rationalForcing _ (by
      change u 0 ≠ 1
      rw [hvalue]
      exact zero_ne_one))
    hφ rfl time_regular (hsymbol (coordinateJetLT 1 u 0)) (hu 0 (Metric.mem_ball_self hr))
    (analyticAt_rationalProfile 0 (by simp)) hnormal
    (Filter.Eventually.mono (Metric.ball_mem_nhds (0 : ℝ^1) hr) (fun x hx ↦ hP x hx))
    (Filter.Eventually.mono hpositive fun x hx ↦ by
      simpa only [Fintype.sum_subsingleton _ (Sym.replicate 1 (0 : Fin 1)),
        one_mul, rationalForcing, hzero] using
        rationalProfile_equation x hx)
  refine ⟨r, hr, u, hu, ?_, hvalue, heq⟩
  intro x hx
  simpa only [Fintype.sum_subsingleton _ (Sym.replicate 1 (0 : Fin 1)),
    one_mul, rationalForcing, hzero] using hP x hx

end PDE.Examples.Cauchy.Quasilinear.Analytic
