/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.TestFunction
public import PDE.FDeriv.PartialDeriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Pointwise finite differences

The scalar forward difference quotient

`Dᵢʰ f (x) = (f (x + h eᵢ) - f x) / h`

and the elementary facts about it that the bundled `Lᵖ` and `H¹` difference-quotient
operators (`DifferenceQuotient.Operators`) and the interior regularity argument of Evans,
§6.3.1, rely on. There are three groups of statements.

* Algebra: the exact discrete product rule
  `Dᵢʰ(fg) = f(· + h eᵢ) Dᵢʰg + (Dᵢʰf) g`, and the commutator identity that isolates the
  coefficient term `(Dᵢʰa) v`.
* Convergence: for a smooth test function `φ`, `Dᵢʰ φ → ∂ᵢφ` pointwise as `h → 0`.
* Uniform bounds: a test function is globally Lipschitz, so its difference quotients and
  partial derivatives are bounded by a single constant independent of `h`; for `|h| ≤ 1` both
  vanish outside the closed `1`-thickening of the support, which supplies the compact set for
  dominated convergence.

## Main results

* `coordinateStep`, `forwardDifference`: the displacement `h eᵢ` and the quotient `Dᵢʰ f`.
* `forwardDifference_mul`, `forwardDifference_mul'`, `forwardDifference_mul_sub`: product
  and commutator rules.
* `tendsto_forwardDifference_testFunction`: `Dᵢʰ φ (x) → ∂ᵢφ (x)` as `h → 0`.
* `norm_forwardDifference_le_of_lipschitz`, `norm_forwardDifference_testFunction_le`,
  `norm_partialDeriv_testFunction_le`: Lipschitz bounds uniform in `h`.
* `forwardDifference_sub_partial_eq_zero_of_not_mem_cthickening`: support control for the
  difference `Dᵢʰ φ - ∂ᵢφ`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.1, proof of Theorem 1, pp. 328-331, for difference
  quotients in the interior regularity argument, with the summation by parts formula (16) and the
  product rule (17) `D_k^h(vw) = v^h D_k^h w + w D_k^h v`, `v^h(x) = v(x + h e_k)`, p. 329.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (partialDeriv)

noncomputable section

open TopologicalSpace
open scoped Distributions

namespace SobolevSpace.GraphSpace.DifferenceQuotient

open MeasureTheory Set Function
open scoped ENNReal Topology InnerProductSpace RealInnerProductSpace

variable {n : ℕ}

/-- The coordinate displacement `h e_i`. -/
def coordinateStep (i : Fin n) (h : ℝ) : ℝ^n :=
  h • EuclideanSpace.single i (1 : ℝ)

/-- Pointwise forward difference quotient.  The bundled `L²` operator below
is the quotient-class realization of this expression. -/
def forwardDifference (i : Fin n) (h : ℝ) (f : ℝ^n → ℝ) (x : ℝ^n) : ℝ :=
  h⁻¹ * (f (x + coordinateStep i h) - f x)

/-- Exact finite-difference product rule.  This is the algebraic identity
behind the cutoff and coefficient commutators in Evans §6.3.1, (17). -/
theorem forwardDifference_mul (i : Fin n) (h : ℝ)
    (f g : ℝ^n → ℝ) (x : ℝ^n) :
    forwardDifference i h (fun y ↦ f y * g y) x =
      f (x + coordinateStep i h) * forwardDifference i h g x +
        g x * forwardDifference i h f x := by
  simp only [forwardDifference]
  ring

/-- Equivalent product rule with the translated factor on the other term. -/
theorem forwardDifference_mul' (i : Fin n) (h : ℝ)
    (f g : ℝ^n → ℝ) (x : ℝ^n) :
    forwardDifference i h (fun y ↦ f y * g y) x =
      f x * forwardDifference i h g x +
        g (x + coordinateStep i h) * forwardDifference i h f x := by
  simp only [forwardDifference]
  ring

/-- Difference-quotient commutator with multiplication by a coefficient. -/
theorem forwardDifference_mul_sub (i : Fin n) (h : ℝ)
    (a f : ℝ^n → ℝ) (x : ℝ^n) :
    forwardDifference i h (fun y ↦ a y * f y) x -
        a (x + coordinateStep i h) * forwardDifference i h f x =
      f x * forwardDifference i h a x := by
  rw [forwardDifference_mul]
  ring

/-- A classical coordinate difference quotient of a smooth test function
converges pointwise to the corresponding partial derivative. -/
theorem tendsto_forwardDifference_testFunction
    (i : Fin n) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (x : ℝ^n) :
    Filter.Tendsto (fun h : ℝ ↦ forwardDifference i h φ.toFun x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds ((∂[i] φ.toFun) x)) := by
  let : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
  let : Module ℝ ℝ :=
    (RCLike.toInnerProductSpaceReal.toModule : Module ℝ ℝ)
  let e : ℝ^n := EuclideanSpace.single i (1 : ℝ)
  let q : ℝ → ℝ := fun t ↦ φ.toFun (x + t • e)
  have hline : HasDerivAt q ((∂[i] φ.toFun) x) 0 := by
    have hφ : HasFDerivAt φ.toFun (fderiv ℝ φ.toFun x) x :=
      (φ.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
    have hpath : HasDerivAt (fun t : ℝ ↦ x + t • e) e 0 := by
      simpa using ((hasDerivAt_id (x := (0 : ℝ))).smul_const e).const_add x
    have hφ0 : HasFDerivAt φ.toFun (fderiv ℝ φ.toFun x) (x + (0 : ℝ) • e) := by
      simpa using hφ
    have hcomp := hφ0.comp_hasDerivAt 0 hpath
    change HasDerivAt
      (φ.toFun ∘ fun t : ℝ ↦ x + t • e)
      ((∂[i] φ.toFun) x) 0
    simpa only [e, partialDeriv] using hcomp
  simpa [forwardDifference, coordinateStep, q, e, smul_eq_mul] using
    hline.tendsto_slope_zero

/-- Sequential form of pointwise convergence, convenient for the compactness
sequence used in the Sobolev difference-quotient criterion. -/
theorem tendsto_forwardDifference_testFunction_sequence
    (i : Fin n) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (x : ℝ^n)
    (h : ℕ → ℝ) (hzero : Filter.Tendsto h Filter.atTop (nhds 0))
    (hne : ∀ m, h m ≠ 0) :
    Filter.Tendsto (fun m ↦ forwardDifference i (h m) φ.toFun x)
      Filter.atTop (nhds ((∂[i] φ.toFun) x)) := by
  apply (tendsto_forwardDifference_testFunction i φ x).comp
  rw [tendsto_nhdsWithin_iff]
  exact ⟨hzero, Filter.Eventually.of_forall fun m ↦ by simpa using hne m⟩

/-- A smooth compactly supported test function is globally Lipschitz.  The
constant is retained explicitly for the dominated-convergence estimate. -/
theorem exists_lipschitzWith_testFunction
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    ∃ C : NNReal, LipschitzWith C φ.toFun := by
  exact φ.contDiff.lipschitzWith_of_hasCompactSupport
    φ.hasCompactSupport (by simp)

/-- Difference quotients of a Lipschitz function are bounded by its
Lipschitz constant. -/
theorem norm_forwardDifference_le_of_lipschitz
    (i : Fin n) (f : ℝ^n → ℝ)
    {C : NNReal} (hf : LipschitzWith C f)
    {h : ℝ} (hh : h ≠ 0) (x : ℝ^n) :
    ‖forwardDifference i h f x‖ ≤ C := by
  rw [forwardDifference, norm_mul, norm_inv]
  calc
    ‖h‖⁻¹ * ‖f (x + coordinateStep i h) - f x‖
        ≤ ‖h‖⁻¹ * (C * ‖(x + coordinateStep i h) - x‖) :=
      mul_le_mul_of_nonneg_left
        (hf.norm_sub_le (x + coordinateStep i h) x) (inv_nonneg.mpr (norm_nonneg h))
    _ = C := by
      rw [add_sub_cancel_left, coordinateStep, norm_smul,
        show ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 by
          simp [PiLp.norm_single], mul_one]
      field_simp [Real.norm_eq_abs, abs_ne_zero.mpr hh]

/-- Coordinate difference quotients of one test function are uniformly
bounded pointwise by any global Lipschitz constant for that function. -/
theorem norm_forwardDifference_testFunction_le
    (i : Fin n) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    {C : NNReal} (hφ : LipschitzWith C φ.toFun)
    {h : ℝ} (hh : h ≠ 0) (x : ℝ^n) :
    ‖forwardDifference i h φ.toFun x‖ ≤ C :=
  norm_forwardDifference_le_of_lipschitz i φ.toFun hφ hh x

/-- The same Lipschitz constant bounds every classical coordinate partial
derivative of the test function. -/
theorem norm_partialDeriv_testFunction_le
    (i : Fin n) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    {C : NNReal} (hφ : LipschitzWith C φ.toFun) (x : ℝ^n) :
    ‖(∂[i] φ.toFun) x‖ ≤ C := by
  calc
    ‖(∂[i] φ.toFun) x‖
        ≤ ‖fderiv ℝ φ.toFun x‖ * ‖EuclideanSpace.single i (1 : ℝ)‖ := by
          exact ContinuousLinearMap.le_opNorm _ _
    _ = ‖fderiv ℝ φ.toFun x‖ := by
      rw [show ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 by
        simp [PiLp.norm_single], mul_one]
    _ ≤ C := norm_fderiv_le_of_lipschitz ℝ hφ

/-- For steps of size at most one, the difference quotient and its limiting
partial derivative are supported in one fixed compact thickening of the test
function's support. -/
theorem forwardDifference_sub_partial_eq_zero_of_not_mem_cthickening
    (i : Fin n) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    {h : ℝ} (hh : |h| ≤ 1) {x : ℝ^n}
    (hx : x ∉ Metric.cthickening 1 (tsupport φ.toFun)) :
    forwardDifference i h φ.toFun x - (∂[i] φ.toFun) x = 0 := by
  have hself : tsupport φ.toFun ⊆ Metric.cthickening 1 (tsupport φ.toFun) :=
    Metric.self_subset_cthickening (δ := 1) (tsupport φ.toFun)
  have hx0 : φ.toFun x = 0 := by
    rw [← Function.notMem_support]
    intro hxs
    exact hx (hself (subset_tsupport φ.toFun hxs))
  have hxstep : φ.toFun (x + coordinateStep i h) = 0 := by
    rw [← Function.notMem_support]
    intro hs
    apply hx
    apply Metric.mem_cthickening_of_dist_le x (x + coordinateStep i h) 1
      (tsupport φ.toFun) (subset_tsupport φ.toFun hs)
    have hstepnorm : ‖coordinateStep i h‖ = |h| := by
      rw [coordinateStep, norm_smul,
        show ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 by
          simp [PiLp.norm_single], mul_one,
        Real.norm_eq_abs]
    simpa [dist_eq_norm, hstepnorm] using hh
  have hpartial : (∂[i] φ.toFun) x = 0 := by
    have hxt : x ∉ tsupport φ.toFun := by
      intro hxt
      exact hx (hself hxt)
    have hfderiv : fderiv ℝ φ.toFun x = 0 :=
      fderiv_of_notMem_tsupport (𝕜 := ℝ) (f := φ.toFun) hxt
    change (fderiv ℝ φ.toFun x) (EuclideanSpace.single i (1 : ℝ)) = 0
    rw [hfderiv]
    rfl
  rw [hpartial]
  simp [forwardDifference, hx0, hxstep]

/-- The displacement `h eᵢ` has Euclidean norm `|h|`. -/
@[simp]
theorem norm_coordinateStep (i : Fin n) (h : ℝ) :
    ‖coordinateStep i h‖ = |h| := by
  rw [coordinateStep, norm_smul,
    show ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 by
      simp [PiLp.norm_single],
    mul_one, Real.norm_eq_abs]
end SobolevSpace.GraphSpace.DifferenceQuotient
