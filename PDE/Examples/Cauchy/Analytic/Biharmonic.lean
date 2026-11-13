/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Cauchy.Hypersurface.Existence
public import PDE.Cauchy.Hypersurface.Uniqueness
public import PDE.Analysis.Calculus.MultiIndex.CoordinateJet.Word
public import PDE.Analysis.Calculus.MultiIndex.NormalData
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives

/-!
# A fourth-order analytic Cauchy problem on a parabola

The analytic Cauchy–Kovalevskaya theorem `exists_analytic_solution_of_normal_data`
gives an analytic solution of the biharmonic equation `∂₀⁴u + 2∂₀²∂₁²u + ∂₁⁴u = 0` near
`(1, 1)` with four prescribed normal data `biharmonicData` on the parabola `x₀ = x₁²`.
The data are the normal derivatives of the biharmonic polynomial `biharmonicProfile`,
and the uniqueness theorem `eventuallyEq_of_analytic_solution_of_normal_data` shows that
the solution agrees with this polynomial near `(1, 1)`
(`exists_analytic_biharmonic_parabola_solution`). Both mixed and pure fourth derivatives
enter the equation. Evans, §4.6.3, reduces such a problem on an analytic noncharacteristic
hypersurface to the first-order system (15) of Theorem 2.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.6.3, (14)-(15) and Theorem 2 (Cauchy–Kovalevskaya
  Theorem), pp. 239-240.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter Set PDE.Analysis.MultiIndex
open scoped Topology ContDiff Gradient

namespace PDE.Examples.Cauchy.Quasilinear.Analytic

/-- A regular defining function for the parabolic initial curve. -/
def parabolaLevel (x : ℝ^2) : ℝ := x 0 - (x 1) ^ 2

/-- A nonzero biharmonic polynomial carrying nontrivial lower normal data. -/
def biharmonicProfile (x : ℝ^2) : ℝ :=
  1 + x 0 + x 1 * x 0 + (x 1) ^ 4 - 6 * (x 1) ^ 2 * (x 0) ^ 2 + (x 0) ^ 4

/-- The mixed fourth derivative appearing with coefficient two in the
square of the Laplacian. -/
def twoTimeTwoSpace : Sym (Fin 2) 4 := 0 ::ₛ 0 ::ₛ 1 ::ₛ 1 ::ₛ Sym.nil

/-- On the parabola `x₀ = x₁²`, the profile is `1 + x₁² + x₁³ + x₁⁴ - 6x₁⁶ + x₁⁸`. -/
theorem biharmonicProfile_on_parabola (x : ℝ^2) (hx : x 0 = (x 1) ^ 2) :
    biharmonicProfile x =
      1 + (x 1) ^ 2 + (x 1) ^ 3 + (x 1) ^ 4 - 6 * (x 1) ^ 6 + (x 1) ^ 8 := by
  unfold biharmonicProfile
  rw [hx]
  cas

private theorem biharmonicProfile_base :
    biharmonicProfile (WithLp.toLp 2 ![1, 1]) = -1 := by
  norm_num [biharmonicProfile]

private def biharmonicCoefficients (α : Sym (Fin 2) 4)
    (_z : ℝ^2 × (∀ j : Fin 4, Sym (Fin 2) (j : ℕ) → ℝ)) : ℝ :=
  (if α = Sym.replicate 4 0 then 1 else 0) +
    (if α = twoTimeTwoSpace then 2 else 0) +
    (if α = Sym.replicate 4 1 then 1 else 0)

private theorem biharmonicCoefficients_sum
    (z : ℝ^2 × (∀ j : Fin 4, Sym (Fin 2) (j : ℕ) → ℝ))
    (w : Sym (Fin 2) 4 → ℝ) :
    ∑ α, biharmonicCoefficients α z * w α =
      w (Sym.replicate 4 0) + 2 * w twoTimeTwoSpace + w (Sym.replicate 4 1) := by
  classical
  simp [biharmonicCoefficients, add_mul, Finset.sum_add_distrib, ite_mul]

private theorem analyticAt_parabolaLevel (x : ℝ^2) :
    AnalyticAt ℝ parabolaLevel x :=
  ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).analyticAt x).sub
    (((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).analyticAt x).pow 2)

private theorem parabolaLevel_regular (x : ℝ^2) :
    fderiv ℝ parabolaLevel x ≠ 0 := by
  have h : fderiv ℝ parabolaLevel x (EuclideanSpace.single 0 1) = 1 := by
    cas
  intro hz
  simp [hz] at h

private theorem analyticAt_biharmonicProfile (x : ℝ^2) :
    AnalyticAt ℝ biharmonicProfile x := by
  have ht := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).analyticAt x
  have hx := (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).analyticAt x
  exact ((((analyticAt_const.add ht).add (hx.mul ht)).add (hx.pow 4)).sub
    ((analyticAt_const.mul (hx.pow 2)).mul (ht.pow 2))).add (ht.pow 4)

private theorem biharmonic_symbol (x : ℝ^2)
    (q : ∀ j : Fin 4, Sym (Fin 2) (j : ℕ) → ℝ) :
    ∑ α, biharmonicCoefficients α (x, q) *
      monomial α (PDE.Analysis.Hypersurface.levelNormal parabolaLevel x) = 1 := by
  let ν := PDE.Analysis.Hypersurface.levelNormal parabolaLevel x
  have hn : ν 0 ^ 2 + ν 1 ^ 2 = 1 := by
    have h := EuclideanSpace.real_norm_sq_eq ν
    rw [PDE.Analysis.Hypersurface.norm_levelNormal (parabolaLevel_regular x)] at h
    simpa [Fin.sum_univ_two] using h.symm
  rw [biharmonicCoefficients_sum (x, q), monomial_replicate, monomial_replicate]
  have hm : monomial twoTimeTwoSpace ν = ν 0 ^ 2 * ν 1 ^ 2 := by
    norm_num [monomial, twoTimeTwoSpace, Fin.prod_univ_two, Sym.coe_cons, Sym.coe_nil]
  change ν 0 ^ 4 + 2 * monomial twoTimeTwoSpace ν + ν 1 ^ 4 = 1
  rw [hm]
  nlinarith [sq_nonneg (ν 0 ^ 2 + ν 1 ^ 2 - 1)]

/-- The prescribed normal derivatives of orders `0` to `3` on the parabola, as explicit
functions of `x₁`. The denominators are powers of `√(1 + 4x₁²) > 0`. -/
def biharmonicData (j : Fin 4) (x : ℝ^2) : ℝ :=
  ![1 + (x 1) ^ 2 + (x 1) ^ 3 + (x 1) ^ 4 - 6 * (x 1) ^ 6 + (x 1) ^ 8,
    (1 + x 1 - 2 * (x 1) ^ 3 - 20 * (x 1) ^ 4 + 28 * (x 1) ^ 6) /
      Real.sqrt (1 + 4 * (x 1) ^ 2),
    (-4 * x 1 - 12 * (x 1) ^ 2 + 156 * (x 1) ^ 4 - 48 * (x 1) ^ 6) /
      (1 + 4 * (x 1) ^ 2),
    24 * (x 1) ^ 2 * (7 - 20 * (x 1) ^ 2) /
      (Real.sqrt (1 + 4 * (x 1) ^ 2)) ^ 3] j

private theorem parabola_denominator_pos (x : ℝ^2) : 0 < 1 + 4 * (x 1) ^ 2 := by
  positivity

private theorem parabola_gradient (x : ℝ^2) :
    ∇ parabolaLevel x = WithLp.toLp 2 ![1, -2 * x 1] := by
  ext i
  rw [gradient_apply_eq_partialDeriv]
  fin_cases i
  · cas
  · cas

private theorem parabola_normal (x : ℝ^2) :
    PDE.Analysis.Hypersurface.levelNormal parabolaLevel x =
      (Real.sqrt (1 + 4 * (x 1) ^ 2))⁻¹ • WithLp.toLp 2 ![1, -2 * x 1] := by
  rw [PDE.Analysis.Hypersurface.levelNormal, parabola_gradient]
  have hn : ‖(WithLp.toLp 2 ![1, -2 * x 1] : ℝ^2)‖ =
      Real.sqrt (1 + 4 * (x 1) ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    congr 1
    simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
    change 1 ^ 2 + (-2 * x 1) ^ 2 = 1 + 4 * (x 1) ^ 2
    cas
  rw [hn]

private theorem analyticAt_biharmonicData (j : Fin 4) (x : ℝ^2) :
    AnalyticAt ℝ (biharmonicData j) x := by
  have hs : AnalyticAt ℝ (fun y : ℝ^2 ↦ y 1) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).analyticAt x
  have hq : AnalyticAt ℝ (fun y : ℝ^2 ↦ 1 + 4 * (y 1) ^ 2) x :=
    analyticAt_const.add (analyticAt_const.mul (hs.pow 2))
  have hn : 1 + 4 * (x 1) ^ 2 ≠ 0 := (parabola_denominator_pos x).ne'
  have hr : AnalyticAt ℝ (fun y : ℝ^2 ↦ Real.sqrt (1 + 4 * (y 1) ^ 2)) x :=
    (hq.contDiffAt.sqrt hn).analyticAt
  have hrn : Real.sqrt (1 + 4 * (x 1) ^ 2) ≠ 0 :=
    (Real.sqrt_pos.mpr (parabola_denominator_pos x)).ne'
  fin_cases j
  · exact ((((analyticAt_const.add (hs.pow 2)).add (hs.pow 3)).add (hs.pow 4)).sub
      (analyticAt_const.mul (hs.pow 6))).add (hs.pow 8)
  · exact ((((analyticAt_const.add hs).sub (analyticAt_const.mul (hs.pow 3))).sub
      (analyticAt_const.mul (hs.pow 4))).add (analyticAt_const.mul (hs.pow 6))).div hr hrn
  · exact ((((analyticAt_const.mul hs).sub (analyticAt_const.mul (hs.pow 2))).add
      (analyticAt_const.mul (hs.pow 4))).sub (analyticAt_const.mul (hs.pow 6))).div hq hn
  · exact ((analyticAt_const.mul (hs.pow 2)).mul
      (analyticAt_const.sub (analyticAt_const.mul (hs.pow 2)))).div
        (hr.pow 3) (pow_ne_zero 3 hrn)

private theorem biharmonicProfile_contDiff : ContDiff ℝ ∞ biharmonicProfile := by
  cas

private theorem biharmonicProfile_time : ∂[0] biharmonicProfile =
    fun x ↦ 1 + x 1 - 12 * (x 1) ^ 2 * x 0 + 4 * (x 0) ^ 3 := by
  funext x
  cas

private theorem biharmonicProfile_space : ∂[1] biharmonicProfile =
    fun x ↦ x 0 + 4 * (x 1) ^ 3 - 12 * x 1 * (x 0) ^ 2 := by
  funext x
  cas

/-- On the parabola, the normal derivatives of `biharmonicProfile` of orders `0` to `3`
are `biharmonicData`. -/
theorem biharmonicProfile_normalData (j : Fin 4) (x : ℝ^2) (hx : x 0 = (x 1) ^ 2) :
    normalData (j : ℕ) biharmonicProfile
      (PDE.Analysis.Hypersurface.levelNormal parabolaLevel x) x = biharmonicData j x := by
  have hq := parabola_denominator_pos x
  have hroot : Real.sqrt (1 + 4 * (x 1) ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
  let f := fun t : ℝ ↦
    1 + ((x 1) ^ 2 + t) + (x 1 - 2 * t * x 1) * ((x 1) ^ 2 + t) +
      (x 1 - 2 * t * x 1) ^ 4 -
        6 * (x 1 - 2 * t * x 1) ^ 2 * ((x 1) ^ 2 + t) ^ 2 + ((x 1) ^ 2 + t) ^ 4
  have hline : (fun t : ℝ ↦ biharmonicProfile
      (x + t • WithLp.toLp 2 ![1, -2 * x 1])) = f := by
    funext t
    change 1 + (x 0 + t * 1) + (x 1 + t * (-2 * x 1)) * (x 0 + t * 1) +
      (x 1 + t * (-2 * x 1)) ^ 4 -
        6 * (x 1 + t * (-2 * x 1)) ^ 2 * (x 0 + t * 1) ^ 2 +
          (x 0 + t * 1) ^ 4 = _
    rw [hx]
    dsimp [f]
    cas
  fin_cases j
  · rw [normalData_zero]
    exact biharmonicProfile_on_parabola x hx
  · rw [parabola_normal, normalData_smul,
      normalData_eq_iteratedDeriv (analyticAt_biharmonicProfile x).contDiffAt, hline]
    have hD : deriv f 0 =
        1 + x 1 - 2 * (x 1) ^ 3 - 20 * (x 1) ^ 4 + 28 * (x 1) ^ 6 := by
      dsimp [f]
      cas
    simp only [iteratedDeriv_succ, iteratedDeriv_zero, hD]
    dsimp [biharmonicData]
    cas [hq, hroot]
  · rw [parabola_normal, normalData_smul,
      normalData_eq_iteratedDeriv (analyticAt_biharmonicProfile x).contDiffAt, hline]
    have hD : deriv (deriv f) 0 =
        -4 * x 1 - 12 * (x 1) ^ 2 + 156 * (x 1) ^ 4 - 48 * (x 1) ^ 6 := by
      dsimp [f]
      cas
    simp only [iteratedDeriv_succ, iteratedDeriv_zero, hD]
    dsimp [biharmonicData]
    cas [hq, hroot]
  · rw [parabola_normal, normalData_smul,
      normalData_eq_iteratedDeriv (analyticAt_biharmonicProfile x).contDiffAt, hline]
    have hD : deriv (deriv (deriv f)) 0 = 24 * (x 1) ^ 2 * (7 - 20 * (x 1) ^ 2) := by
      dsimp [f]
      cas
    simp only [iteratedDeriv_succ, iteratedDeriv_zero, hD]
    dsimp [biharmonicData]
    cas [hq, hroot]

private theorem biharmonicProfile_equation (x : ℝ^2) :
    coordinateDeriv (Sym.replicate 4 0) biharmonicProfile x +
      2 * coordinateDeriv twoTimeTwoSpace biharmonicProfile x +
      coordinateDeriv (Sym.replicate 4 1) biharmonicProfile x = 0 := by
  have hs := biharmonicProfile_contDiff
  have htt : ∂[0]
      ((fun x : ℝ^2 ↦ 1 + x 1 - 12 * (x 1) ^ 2 * x 0 + 4 * (x 0) ^ 3) : ℝ^2 → ℝ) =
      fun x ↦ -12 * (x 1) ^ 2 + 12 * (x 0) ^ 2 := by
    funext x
    cas
  have httt : ∂[0] ((fun x : ℝ^2 ↦ -12 * (x 1) ^ 2 + 12 * (x 0) ^ 2) : ℝ^2 → ℝ) =
      fun x ↦ 24 * x 0 := by
    funext x
    cas
  have hxx : ∂[1]
      ((fun x : ℝ^2 ↦ x 0 + 4 * (x 1) ^ 3 - 12 * x 1 * (x 0) ^ 2) : ℝ^2 → ℝ) =
      fun x ↦ 12 * (x 1) ^ 2 - 12 * (x 0) ^ 2 := by
    funext x
    cas
  have hxxx : ∂[1] ((fun x : ℝ^2 ↦ 12 * (x 1) ^ 2 - 12 * (x 0) ^ 2) : ℝ^2 → ℝ) =
      fun x ↦ 24 * x 1 := by
    funext x
    cas
  have htxx : ∂[0] ((fun x : ℝ^2 ↦ 12 * (x 1) ^ 2 - 12 * (x 0) ^ 2) : ℝ^2 → ℝ) =
      fun x ↦ -24 * x 0 := by
    funext x
    cas
  have hm : List.ofFn twoTimeTwoSpace.sortedTuple = [0, 0, 1, 1] := by
    simp [twoTimeTwoSpace, Sym.sortedTuple, Sym.coe_cons, Sym.coe_nil, List.ofFn_succ,
      Multiset.sort_cons, Fin.cast]
  rw [coordinateDeriv_eq_iteratedPartialDeriv hs twoTimeTwoSpace, hm,
    coordinateDeriv_replicate 0 (hs.contDiffAt.of_le (by simp)),
    coordinateDeriv_replicate 1 (hs.contDiffAt.of_le (by simp))]
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply,
    iteratedPartialDeriv, biharmonicProfile_space, hxx, hxxx,
    biharmonicProfile_time, htt, httt, htxx]
  have ht4 : (∂[0] (fun y : ℝ^2 ↦ 24 * y 0)) x = 24 := by cas
  have hm4 : (∂[0] (fun y : ℝ^2 ↦ -24 * y 0)) x = -24 := by cas
  have hx4 : (∂[1] (fun y : ℝ^2 ↦ 24 * y 1)) x = 24 := by cas
  rw [ht4, hm4, hx4]
  norm_num

/-- There is an analytic solution of the biharmonic equation near `(1, 1)` with normal
data `biharmonicData` on the parabola. It equals `-1` at `(1, 1)` and agrees with
`biharmonicProfile` near that point. -/
theorem exists_analytic_biharmonic_parabola_solution :
    ∃ r : ℝ, 0 < r ∧ ∃ u : ℝ^2 → ℝ,
      AnalyticOnNhd ℝ u (Metric.ball (WithLp.toLp 2 ![1, 1]) r) ∧
      (∀ x ∈ Metric.ball (WithLp.toLp 2 ![1, 1]) r,
        coordinateDeriv (Sym.replicate 4 0) u x +
          2 * coordinateDeriv twoTimeTwoSpace u x +
          coordinateDeriv (Sym.replicate 4 1) u x = 0) ∧
      (∀ x ∈ Metric.ball (WithLp.toLp 2 ![1, 1] : ℝ^2) r, x 0 = (x 1) ^ 2 →
        ∀ j : Fin 4,
          normalData (j : ℕ) u (PDE.Analysis.Hypersurface.levelNormal parabolaLevel x) x =
            biharmonicData j x) ∧
      u (WithLp.toLp 2 ![1, 1]) = -1 ∧
      u =ᶠ[𝓝 (WithLp.toLp 2 ![1, 1])] biharmonicProfile := by
  let p : ℝ^2 := WithLp.toLp 2 ![1, 1]
  let g := biharmonicData
  have hg : ∀ j, AnalyticAt ℝ (g j) p := fun j ↦ analyticAt_biharmonicData j p
  have hp : parabolaLevel p = 0 := by norm_num [parabolaLevel, p]
  obtain ⟨r, hr, _, u, hu, hP, hdata⟩ :=
    PDE.Cauchy.Quasilinear.Analytic.exists_analytic_solution_of_normal_data (d := 1) (k := 3)
      (φ := parabolaLevel)
      isOpen_univ (mem_univ p) biharmonicCoefficients (fun _ ↦ 0)
      (analyticAt_parabolaLevel p) hp (parabolaLevel_regular p) g hg
      (fun _ ↦ analyticAt_const) analyticAt_const
      (by rw [biharmonic_symbol p]; exact one_ne_zero)
  have hnormal : ∀ᶠ x in 𝓝 p, parabolaLevel x = 0 → ∀ j : Fin 4,
      normalData (j : ℕ) u (PDE.Analysis.Hypersurface.levelNormal parabolaLevel x) x =
        normalData (j : ℕ) biharmonicProfile
          (PDE.Analysis.Hypersurface.levelNormal parabolaLevel x) x := by
    filter_upwards [Metric.ball_mem_nhds p hr] with x hx
    intro hlevel j
    exact (hdata x hx hlevel j).trans
      (biharmonicProfile_normalData j x (sub_eq_zero.mp hlevel)).symm
  have heq := PDE.Cauchy.Quasilinear.Analytic.eventuallyEq_of_analytic_solution_of_normal_data
    (d := 1) (k := 3) (φ := parabolaLevel)
    biharmonicCoefficients (fun _ ↦ 0)
    (fun _ ↦ analyticAt_const) analyticAt_const
    (analyticAt_parabolaLevel p) hp (parabolaLevel_regular p)
    (by rw [biharmonic_symbol p]; exact one_ne_zero)
    (hu p (Metric.mem_ball_self hr)) (analyticAt_biharmonicProfile p) hnormal
    (Filter.Eventually.mono (Metric.ball_mem_nhds p hr) (fun x hx ↦ hP x hx))
    (Filter.Eventually.of_forall fun x ↦
      (biharmonicCoefficients_sum (x, coordinateJetLT 4 biharmonicProfile x)
        (fun α ↦ coordinateDeriv α biharmonicProfile x)).trans (biharmonicProfile_equation x))
  refine ⟨r, hr, u, hu, ?_, ?_, ?_, heq⟩
  · intro x hx
    exact (biharmonicCoefficients_sum (x, coordinateJetLT 4 u x)
      (fun α ↦ coordinateDeriv α u x)).symm.trans (hP x hx)
  · intro x hx hlevel
    apply hdata x hx
    exact sub_eq_zero.mpr hlevel
  · exact heq.self_of_nhds.trans biharmonicProfile_base

end PDE.Examples.Cauchy.Quasilinear.Analytic
