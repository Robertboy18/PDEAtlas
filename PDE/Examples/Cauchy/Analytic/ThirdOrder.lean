/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Cauchy.Hypersurface.Existence
public import PDE.Analysis.Calculus.MultiIndex.CoordinateJet.Basis
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# A nonlinear analytic Cauchy problem of order three

The equation `∂ₜ³u = (1 + u²) ∂ₜ²∂ₓu + ∂ₜu ∂ₜ∂ₓ²u + ∂ₓ³u + exp(t + x)` contains the
coefficient `1 + u²`, the coefficient `∂ₜu` and all four third-order derivatives. The
analytic Cauchy–Kovalevskaya theorem `exists_analytic_solution_of_normal_data` gives an
analytic solution near the origin with data `u = 1 + x`, `∂ₜu = exp x`, `∂ₜ²u = cos x`
on `t = 0` (`exists_analytic_third_order_solution`). Evans, §4.6.3, reduces such a
problem to the form (14), with zero Cauchy data, and then to the first-order system (15) of
Theorem 2.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.6.3, (14)-(15) and Theorem 2 (Cauchy–Kovalevskaya
  Theorem), pp. 239-240.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set PDE.Analysis.MultiIndex
open scoped Topology

namespace PDE.Examples.Cauchy.Quasilinear.Analytic

/-- The mixed derivative with two time directions and one spatial direction. -/
def timeTimeSpace : Sym (Fin 2) 3 := 0 ::ₛ 0 ::ₛ 1 ::ₛ Sym.nil

/-- The mixed derivative with one time direction and two spatial directions. -/
def timeSpaceSpace : Sym (Fin 2) 3 := 0 ::ₛ 1 ::ₛ 1 ::ₛ Sym.nil

private def thirdCoefficients (α : Sym (Fin 2) 3)
    (z : ℝ^2 × (∀ j : Fin 3, Sym (Fin 2) (j : ℕ) → ℝ)) : ℝ :=
  (if α = Sym.replicate 3 0 then 1 else 0) -
    (if α = timeTimeSpace then 1 else 0) * (1 + (z.2 0 Sym.nil) ^ 2) -
    (if α = timeSpaceSpace then 1 else 0) * z.2 1 (Sym.replicate 1 0) -
    (if α = Sym.replicate 3 1 then 1 else 0)

private theorem thirdCoefficients_sum
    (z : ℝ^2 × (∀ j : Fin 3, Sym (Fin 2) (j : ℕ) → ℝ))
    (w : Sym (Fin 2) 3 → ℝ) :
    ∑ α, thirdCoefficients α z * w α =
      w (Sym.replicate 3 0) - (1 + (z.2 0 Sym.nil) ^ 2) * w timeTimeSpace -
        z.2 1 (Sym.replicate 1 0) * w timeSpaceSpace -
        w (Sym.replicate 3 1) := by
  classical
  simp [thirdCoefficients, sub_mul, Finset.sum_sub_distrib, ite_mul]

private theorem analyticAt_thirdCoefficients
    (α : Sym (Fin 2) 3)
    (z : ℝ^2 × (∀ j : Fin 3, Sym (Fin 2) (j : ℕ) → ℝ)) :
    AnalyticAt ℝ (thirdCoefficients α) z := by
  have hs : AnalyticAt ℝ
      (fun z : ℝ^2 × (∀ j : Fin 3, Sym (Fin 2) (j : ℕ) → ℝ) ↦ z.2) z :=
    analyticAt_snd
  have h0 := analyticAt_pi_iff.mp (analyticAt_pi_iff.mp hs 0) Sym.nil
  have h1 := analyticAt_pi_iff.mp (analyticAt_pi_iff.mp hs 1) (Sym.replicate 1 0)
  exact ((analyticAt_const.sub (analyticAt_const.mul
    (analyticAt_const.add (h0.pow 2)))).sub (analyticAt_const.mul h1)).sub analyticAt_const

private theorem levelNormal_proj {n : ℕ} (i : Fin n) (x : ℝ^n) :
    PDE.Analysis.Hypersurface.levelNormal (fun y : ℝ^n ↦ y i) x =
      EuclideanSpace.basisFun (Fin n) ℝ i := by
  have hdual : InnerProductSpace.toDual ℝ (ℝ^n)
      (EuclideanSpace.basisFun (Fin n) ℝ i) = EuclideanSpace.proj (𝕜 := ℝ) i := by
    ext y
    change inner ℝ (EuclideanSpace.basisFun (Fin n) ℝ i) y = y i
    rw [real_inner_comm, EuclideanSpace.inner_basisFun_real]
  have hg : HasGradientAt (fun y : ℝ^n ↦ y i)
      (EuclideanSpace.basisFun (Fin n) ℝ i) x := by
    rw [hasGradientAt_iff_hasFDerivAt, hdual]
    exact (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt
  simp [PDE.Analysis.Hypersurface.levelNormal, hg.gradient]

private theorem fderiv_proj_ne_zero {n : ℕ} (i : Fin n) (x : ℝ^n) :
    fderiv ℝ (fun y : ℝ^n ↦ y i) x ≠ 0 := by
  change fderiv ℝ (EuclideanSpace.proj (𝕜 := ℝ) i) x ≠ 0
  rw [(EuclideanSpace.proj (𝕜 := ℝ) i).fderiv]
  intro h
  have he := congrArg (fun L : ℝ^n →L[ℝ] ℝ ↦
    L (EuclideanSpace.basisFun (Fin n) ℝ i)) h
  simp at he

/-- The nonlinear third-order equation has an analytic solution near the origin with
the three stated data on `t = 0`. -/
theorem exists_analytic_third_order_solution :
    ∃ r : ℝ, 0 < r ∧ ∃ u : ℝ^2 → ℝ,
      AnalyticOnNhd ℝ u (Metric.ball 0 r) ∧
      (∀ x ∈ Metric.ball 0 r,
        coordinateDeriv (Sym.replicate 3 0) u x =
          (1 + (u x) ^ 2) * coordinateDeriv timeTimeSpace u x +
          coordinateDeriv (Sym.replicate 1 0) u x * coordinateDeriv timeSpaceSpace u x +
          coordinateDeriv (Sym.replicate 3 1) u x + Real.exp (x 0 + x 1)) ∧
      ∀ x ∈ Metric.ball 0 r, x 0 = 0 →
        u x = 1 + x 1 ∧
          coordinateDeriv (Sym.replicate 1 0) u x = Real.exp (x 1) ∧
          coordinateDeriv (Sym.replicate 2 0) u x = Real.cos (x 1) := by
  classical
  let g : Fin 3 → ℝ^2 → ℝ :=
    ![(fun x ↦ 1 + x 1), (fun x ↦ Real.exp (x 1)), (fun x ↦ Real.cos (x 1))]
  have hg : ∀ i, AnalyticAt ℝ (g i) 0 := by
    intro i
    fin_cases i
    · exact analyticAt_const.add ((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).analyticAt (0 : ℝ^2))
    · exact ((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).analyticAt (0 : ℝ^2)).rexp
    · exact Real.analyticAt_cos.comp
        ((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).analyticAt (0 : ℝ^2))
  have hb : AnalyticOnNhd ℝ
      (fun z : ℝ^2 × (∀ j : Fin 3, Sym (Fin 2) (j : ℕ) → ℝ) ↦
        Real.exp (z.1 0 + z.1 1)) (univ ×ˢ univ) := by
    intro z _
    have hf : AnalyticAt ℝ
        (fun z : ℝ^2 × (∀ j : Fin 3, Sym (Fin 2) (j : ℕ) → ℝ) ↦ z.1) z :=
      analyticAt_fst
    exact (((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).analyticAt z.1).comp_of_eq hf rfl |>.add
      (((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).analyticAt z.1).comp_of_eq hf rfl)).rexp
  have hsymbol (x : ℝ^2)
      (q : ∀ j : Fin 3, Sym (Fin 2) (j : ℕ) → ℝ) :
      ∑ α, thirdCoefficients α (x, q) *
        monomial α (PDE.Analysis.Hypersurface.levelNormal (fun y : ℝ^2 ↦ y 0) x) ≠ 0 := by
    rw [levelNormal_proj]
    simp only [monomial_basisFun, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    have hts : Sym.replicate 3 (0 : Fin 2) ≠ timeTimeSpace := by decide
    have hss : Sym.replicate 3 (0 : Fin 2) ≠ timeSpaceSpace := by decide
    have hxx : Sym.replicate 3 (0 : Fin 2) ≠ Sym.replicate 3 1 := by decide
    simp [thirdCoefficients, hts, hss, hxx]
  obtain ⟨r, hr, _, u, hu, hP, hdata⟩ :=
    PDE.Cauchy.Quasilinear.Analytic.exists_analytic_solution_of_normal_data (d := 1) (k := 2)
      (φ := fun y : ℝ^2 ↦ y 0)
      isOpen_univ (mem_univ (0 : ℝ^2)) thirdCoefficients _
      ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).analyticAt 0) (by simp)
      (fderiv_proj_ne_zero 0 0) g hg
      (fun α ↦ analyticAt_thirdCoefficients α _) (hb _ ⟨mem_univ _, mem_univ _⟩)
      (hsymbol 0 _)
  · refine ⟨r, hr, u, hu, ?_, ?_⟩
    · intro x hx
      have heq := (thirdCoefficients_sum (x, coordinateJetLT 3 u x)
        (fun α ↦ coordinateDeriv α u x)).symm.trans (hP x hx)
      change coordinateDeriv (Sym.replicate 3 0) u x -
        (1 + (u x) ^ 2) * coordinateDeriv timeTimeSpace u x -
        coordinateDeriv (Sym.replicate 1 0) u x * coordinateDeriv timeSpaceSpace u x -
        coordinateDeriv (Sym.replicate 3 1) u x = Real.exp (x 0 + x 1) at heq
      linarith
    · intro x hx hx0
      have h := hdata x hx hx0
      have h0 := h 0
      have h1 := h 1
      have h2 := h 2
      rw [levelNormal_proj, normalData_basisFun] at h0 h1 h2
      exact ⟨h0, h1, h2⟩

end PDE.Examples.Cauchy.Quasilinear.Analytic
