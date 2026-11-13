/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import PDE.Analysis.Evolution.Compactness.Lp.Basic -- shake: keep
import CAS.ExactTactic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Scalar time tests for integrated weak evolution

The integrated weak formulation of a parabolic problem on `[a, b]` tests the equation
`u' + B u = f` against products `τ(t) v` of a scalar function of time and a fixed vector
`v` of the energy space, and then integrates by parts in `t` to move the time derivative
onto `τ`. The admissible scalar tests form the class `TimeTest a b`: a
function `τ : ℝ → ℝ` together with a function `τ'` that is its derivative at every point
of `[a, b]`, such that `τ, τ' ∈ L²(a, b)` and `τ b = 0`. Vanishing at the final time is
built in; vanishing at the initial time is a separate hypothesis where it is needed, so
the same class serves both the equation (initial value visible) and the definition of the
weak time derivative (both boundary terms absent).

The class is larger than `C_c^∞((a, b))`: it contains the affine hat
`t ↦ (b - t)/(b - a)`, which reads off the initial datum, and it is closed under
multiplication by `e^{γ(t - a)}`, the exponential weight that converts a Gårding-type
form into a coercive one in `PDE.Analysis.Evolution.Integrated.Solution`.

## Main results

* `absolutelyContinuousOnInterval_of_hasDerivAt_intervalIntegrable`: a scalar function
  with an everywhere-specified, interval-integrable derivative is absolutely continuous.
* `TimeTest`: the structure described above, with `TimeTest.absolutelyContinuousOnInterval`.
* `TimeTest.integrationByParts_inner`: for an absolutely continuous `X`-valued trajectory
  `u` with a.e. derivative `du`,
  `-∫ₐᵇ ⟪u, v⟫ τ' = ∫ₐᵇ ⟪du, v⟫ τ + ⟪u a, v⟫ τ a`; the final boundary term is absent
  because `τ b = 0`.
* `TimeTest.initialHat`: the affine test with `τ a = 1`, `τ b = 0`, `τ' = -1/(b - a)`.
* `TimeTest.ofContDiffSupported`: every `φ ∈ C_c^∞((a, b))` is a time test, with the
  supporting `_toLp_ae`, `_derivToLp_ae`, `_initial_zero` lemmas.
* `TimeTest.toLp`, `TimeTest.derivToLp`: the `L²(Ioc a b)` classes of `τ` and `τ'`.
* `TimeTest.expMul`: multiplication by `e^{γ(t - a)}`, with the product rule recorded in
  the derivative field and the a.e. identifications `expMul_toLp_ae`, `expMul_derivToLp_ae`.

## Implementation notes

The derivative is a field of the structure rather than `deriv τ`, so that constructions
such as `expMul` can state the derivative by an explicit formula and prove `HasDerivAt`
once, instead of re-deriving it from `deriv` each time. The `L²` classes live on
`Ioc a b`, matching the measure used for the Bochner trajectories throughout
`PDE.Analysis.Evolution.Integrated`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.9.2 (weak derivatives in time, tested against `φ ∈
  C_c^∞(0, T)`), and §7.1.2, proof of Theorem 3, (28) and (32). <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BoundedContinuousFunction Interval

namespace PDE.Analysis.Evolution

/-- A scalar function with a derivative at every point of `[a, b]` that is
interval integrable is absolutely continuous on `[a, b]`.

The fundamental theorem of calculus writes the function as a constant plus
an indefinite integral of an integrable function.
-/
theorem absolutelyContinuousOnInterval_of_hasDerivAt_intervalIntegrable
    {f f' : ℝ → ℝ} {a b : ℝ}
    (hderiv : ∀ t ∈ Set.uIcc a b, HasDerivAt f (f' t) t)
    (hint : IntervalIntegrable f' volume a b) :
    AbsolutelyContinuousOnInterval f a b := by
  let primitive : ℝ → ℝ := fun x ↦ ∫ t in a..x, f' t
  have hprimitive :
      AbsolutelyContinuousOnInterval primitive a b :=
    hint.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hconst :
      AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ f a) a b := by
    rw [absolutelyContinuousOnInterval_iff]
    intro ε hε
    refine ⟨1, zero_lt_one, ?_⟩
    intro E hE hlength
    simpa using hε
  have hsum :
      AbsolutelyContinuousOnInterval
        (fun x ↦ f a + primitive x) a b := by
    apply (hconst.add hprimitive).congr
    intro x _
    simp only [Pi.add_apply]
  apply hsum.congr
  intro x hx
  have hsubset : Set.uIcc a x ⊆ Set.uIcc a b :=
    Set.uIcc_subset_uIcc_left hx
  have hintax : IntervalIntegrable f' volume a x :=
    hint.mono_set hsubset
  have hfundamental :
      (∫ t in a..x, f' t) = f x - f a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht ↦ hderiv t (hsubset ht)) hintax
  dsimp only [primitive]
  linarith

/-- Scalar time tests for the integrated parabolic equation on `[a,b]`.
The function and its derivative are required to belong to `L²` on `Ioc a b`,
and the test vanishes at the final time. -/
structure TimeTest (a b : ℝ) where
  /-- Scalar test function. -/
  toFun : ℝ → ℝ
  /-- Classical derivative chosen for the test function. -/
  derivFun : ℝ → ℝ
  /-- The chosen derivative is correct throughout the oriented time interval. -/
  hasDerivAt : ∀ t ∈ Set.Icc a b, HasDerivAt toFun (derivFun t) t
  /-- The test function is square-integrable on the time interval. -/
  memLp : MemLp toFun 2 (volume.restrict (Set.Ioc a b))
  /-- Its derivative is square-integrable on the time interval. -/
  derivMemLp : MemLp derivFun 2 (volume.restrict (Set.Ioc a b))
  /-- The test vanishes at the final endpoint. -/
  final_zero : toFun b = 0

namespace TimeTest

/-- A time test is absolutely continuous on `[a, b]` when `a ≤ b`. -/
theorem absolutelyContinuousOnInterval
    {a b : ℝ} (τ : TimeTest a b) (hab : a ≤ b) :
    AbsolutelyContinuousOnInterval τ.toFun a b := by
  apply absolutelyContinuousOnInterval_of_hasDerivAt_intervalIntegrable
    (fun t ht ↦ τ.hasDerivAt t (by simpa only [Set.uIcc_of_le hab] using ht))
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  exact τ.derivMemLp.integrable (by norm_num)

/--
Integration by parts against a time test: if `u` is absolutely continuous on `[a, b]` with
derivative `du` a.e. on `(a, b]`, then for every fixed `v`

`-∫ₐᵇ ⟪u, v⟫ τ' = ∫ₐᵇ ⟪du, v⟫ τ + ⟪u(a), v⟫ τ(a)`.

The boundary term at `b` vanishes because `τ b = 0`.
-/
theorem integrationByParts_inner
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    {u du : ℝ → X} {a b : ℝ} (τ : TimeTest a b) (hab : a ≤ b)
    (v : X) (hu : AbsolutelyContinuousOnInterval u a b)
    (hdu : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
      HasDerivAt u (du t) t) :
    -(∫ t in a..b, inner ℝ (u t) v * τ.derivFun t) =
      (∫ t in a..b, inner ℝ (du t) v * τ.toFun t) +
        inner ℝ (u a) v * τ.toFun a := by
  let L : X →L[ℝ] ℝ := innerSL ℝ v
  have hpairAC :
      AbsolutelyContinuousOnInterval (fun t ↦ inner ℝ (u t) v) a b := by
    have hcomp :=
      L.lipschitzWith.comp_absolutelyContinuousOnInterval hu
    apply hcomp.congr
    intro t _
    simp only [Function.comp_apply, L, innerSL_apply_apply]
    exact real_inner_comm _ _
  have hpairDeriv :
      ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
        HasDerivAt (fun s ↦ inner ℝ (u s) v) (inner ℝ (du t) v) t := by
    filter_upwards [hdu] with t ht
    have hcomp : HasDerivAt (L ∘ u) (L (du t)) t :=
      L.hasFDerivAt.comp_hasDerivAt t ht
    convert hcomp using 1
    · funext s
      simp only [Function.comp_apply, L, innerSL_apply_apply]
      exact real_inner_comm _ _
    · simp only [L, innerSL_apply_apply]
      exact real_inner_comm _ _
  have hparts :=
    hpairAC.integral_mul_deriv_eq_deriv_mul
      (τ.absolutelyContinuousOnInterval hab)
  have hpairDerivVolume :
      ∀ᵐ t ∂volume, t ∈ Set.Ioc a b →
        HasDerivAt (fun s ↦ inner ℝ (u s) v) (inner ℝ (du t) v) t :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).1 hpairDeriv
  have hleft :
      (∫ t in a..b, inner ℝ (u t) v * deriv τ.toFun t) =
        ∫ t in a..b, inner ℝ (u t) v * τ.derivFun t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t ht
    rw [(τ.hasDerivAt t (by
      simpa only [Set.uIcc_of_le hab] using Set.uIoc_subset_uIcc ht)).deriv]
  have hright :
      (∫ t in a..b, deriv (fun s ↦ inner ℝ (u s) v) t * τ.toFun t) =
        ∫ t in a..b, inner ℝ (du t) v * τ.toFun t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hpairDerivVolume] with t ht hmem
    have htIoc : t ∈ Set.Ioc a b := by
      simpa only [Set.uIoc_of_le hab] using hmem
    rw [(ht htIoc).deriv]
  rw [hleft, hright, τ.final_zero] at hparts
  simp only [mul_zero, zero_sub] at hparts
  linarith

/-- The affine endpoint test `t ↦ (b-t)/(b-a)`.  For `a < b` it equals
one at the initial endpoint, vanishes at the final endpoint, and has the
constant derivative `-1/(b-a)`. -/
noncomputable def initialHat (a b : ℝ) : TimeTest a b where
  toFun := fun t ↦ (b - t) / (b - a)
  derivFun := fun _ ↦ -1 / (b - a)
  hasDerivAt := fun t _ ↦
    ((hasDerivAt_id t).const_sub b).div_const (b - a)
  memLp := memLp_restrict_Ioc_of_continuousOn
    ((continuous_const.sub continuous_id).div_const (b - a)).continuousOn
  derivMemLp := memLp_restrict_Ioc_of_continuousOn continuous_const.continuousOn
  final_zero := by
    simp

/-- The affine hat `t ↦ (b - t)/(b - a)` equals one at the initial time `a`. -/
@[simp]
theorem initialHat_initial {a b : ℝ} (hab : a < b) :
    (initialHat a b).toFun a = 1 := by
  exact div_self (sub_ne_zero.mpr (ne_of_gt hab))

/-- The recorded derivative of the affine hat is the constant `-1/(b - a)`. -/
@[simp]
theorem initialHat_deriv (a b t : ℝ) :
    (initialHat a b).derivFun t = -1 / (b - a) := rfl

/-- A smooth scalar function whose support has closure in `(a, b)` is a time test, with
derivative `deriv φ`. These are the tests `C_c^∞((a, b))` in Evans's definition of the weak
time derivative (§5.9.2). -/
noncomputable def ofContDiffSupported
    {a b : ℝ} (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsupp : closure (Function.support φ) ⊆ Set.Ioo a b) : TimeTest a b where
  toFun := φ
  derivFun := deriv φ
  hasDerivAt := fun t _ ↦
    (hφ.differentiable (by simp)).differentiableAt.hasDerivAt
  memLp := memLp_restrict_Ioc_of_continuousOn hφ.continuous.continuousOn
  derivMemLp := by
    have hφone : ContDiff ℝ 1 φ := hφ.of_le (by simp)
    exact memLp_restrict_Ioc_of_continuousOn
      hφone.continuous_deriv_one.continuousOn
  final_zero := by
    by_contra hb
    have hbmem : b ∈ Function.support φ := Function.mem_support.mpr hb
    exact (lt_irrefl b) (hsupp (subset_closure hbmem)).2

/-- The `L²` equivalence class of a scalar time test. -/
noncomputable def toLp {a b : ℝ} (τ : TimeTest a b) :
    Lp ℝ 2 (volume.restrict (Set.Ioc a b)) :=
  τ.memLp.toLp τ.toFun

/-- The `L²` equivalence class of the derivative of a scalar time test. -/
noncomputable def derivToLp {a b : ℝ} (τ : TimeTest a b) :
    Lp ℝ 2 (volume.restrict (Set.Ioc a b)) :=
  τ.derivMemLp.toLp τ.derivFun

/-- Multiply an endpoint time test by `exp (gamma * (t-a))`.

The derivative field records the exact product rule

`(e^{gamma(t-a)} τ)' = e^{gamma(t-a)} (τ' + gamma τ)`.

This is the test-function half of the exponential shift from a Gårding
form to a coercive form. -/
noncomputable def expMul {a b : ℝ} (gamma : ℝ) (τ : TimeTest a b) :
    TimeTest a b where
  toFun := fun t ↦ Real.exp (gamma * (t - a)) * τ.toFun t
  derivFun := fun t ↦
    Real.exp (gamma * (t - a)) * (τ.derivFun t + gamma * τ.toFun t)
  hasDerivAt := by
    intro t ht
    have hexp :
        HasDerivAt (fun s : ℝ ↦ Real.exp (gamma * (s - a)))
          (gamma * Real.exp (gamma * (t - a))) t := by
      cas
    convert! hexp.mul (τ.hasDerivAt t ht) using 1
    ring
  memLp := by
    simpa only [smul_eq_mul] using
      memLp_restrict_Ioc_smul_of_continuousOn
        (fun t ↦ Real.exp (gamma * (t - a)))
        ((Real.continuous_exp.comp
          (continuous_const.mul
            (continuous_id.sub continuous_const))).continuousOn)
        τ.toFun τ.memLp
  derivMemLp := by
    have hweight : ContinuousOn
        (fun t : ℝ ↦ Real.exp (gamma * (t - a))) (Set.Icc a b) :=
      (Real.continuous_exp.comp
        (continuous_const.mul (continuous_id.sub continuous_const))).continuousOn
    have hderiv :=
      memLp_restrict_Ioc_smul_of_continuousOn
        (fun t ↦ Real.exp (gamma * (t - a))) hweight
        τ.derivFun τ.derivMemLp
    have hfun :=
      memLp_restrict_Ioc_smul_of_continuousOn
        (fun t ↦ gamma * Real.exp (gamma * (t - a)))
        (continuousOn_const.mul hweight) τ.toFun τ.memLp
    apply MemLp.ae_eq _ (hderiv.add hfun)
    filter_upwards with t
    change
      Real.exp (gamma * (t - a)) * τ.derivFun t +
          gamma * Real.exp (gamma * (t - a)) * τ.toFun t =
        Real.exp (gamma * (t - a)) *
          (τ.derivFun t + gamma * τ.toFun t)
    ring
  final_zero := by simp [τ.final_zero]

/-- Pointwise value of the exponentially weighted test `e^{γ(t - a)} τ(t)`. -/
@[simp]
theorem expMul_toFun {a b : ℝ} (gamma : ℝ) (τ : TimeTest a b) (t : ℝ) :
    (τ.expMul gamma).toFun t =
      Real.exp (gamma * (t - a)) * τ.toFun t :=
  by simp [expMul]

/-- The recorded derivative of the weighted test is the product rule
`e^{γ(t - a)} (τ'(t) + γ τ(t))`. -/
@[simp]
theorem expMul_derivFun {a b : ℝ} (gamma : ℝ) (τ : TimeTest a b) (t : ℝ) :
    (τ.expMul gamma).derivFun t =
      Real.exp (gamma * (t - a)) *
        (τ.derivFun t + gamma * τ.toFun t) :=
  by simp [expMul]

/-- The `L²` representative of an exponentially weighted time test agrees
almost everywhere with the pointwise product. -/
theorem expMul_toLp_ae {a b : ℝ} (gamma : ℝ) (τ : TimeTest a b) :
    ((τ.expMul gamma).toLp : ℝ → ℝ) =ᵐ[
      volume.restrict (Set.Ioc a b)]
        fun t ↦ Real.exp (gamma * (t - a)) * τ.toLp t := by
  filter_upwards [(τ.expMul gamma).memLp.coeFn_toLp,
    τ.memLp.coeFn_toLp] with t hweighted hτ
  have hτrev : τ.toFun t = τ.toLp t := by
    simpa only [toLp] using hτ.symm
  calc
    (τ.expMul gamma).toLp t =
        (τ.expMul gamma).toFun t := by
          simpa only [toLp] using hweighted
    _ = Real.exp (gamma * (t - a)) * τ.toFun t :=
      expMul_toFun gamma τ t
    _ = Real.exp (gamma * (t - a)) * τ.toLp t := by rw [hτrev]

/-- The derivative representative of an exponentially weighted time test
agrees almost everywhere with the product-rule expression. -/
theorem expMul_derivToLp_ae {a b : ℝ} (gamma : ℝ) (τ : TimeTest a b) :
    ((τ.expMul gamma).derivToLp : ℝ → ℝ) =ᵐ[
      volume.restrict (Set.Ioc a b)]
        fun t ↦ Real.exp (gamma * (t - a)) *
          (τ.derivToLp t + gamma * τ.toLp t) := by
  filter_upwards [(τ.expMul gamma).derivMemLp.coeFn_toLp,
    τ.derivMemLp.coeFn_toLp, τ.memLp.coeFn_toLp]
      with t hweighted hτ' hτ
  have hτ'rev : τ.derivFun t = τ.derivToLp t := by
    simpa only [derivToLp] using hτ'.symm
  have hτrev : τ.toFun t = τ.toLp t := by
    simpa only [toLp] using hτ.symm
  calc
    (τ.expMul gamma).derivToLp t =
        (τ.expMul gamma).derivFun t := by
          simpa only [derivToLp] using hweighted
    _ = Real.exp (gamma * (t - a)) *
        (τ.derivFun t + gamma * τ.toFun t) :=
      expMul_derivFun gamma τ t
    _ = Real.exp (gamma * (t - a)) *
        (τ.derivToLp t + gamma * τ.toLp t) := by rw [hτ'rev, hτrev]

/-- The `L²` representative of a smooth supported test agrees almost
everywhere with the original scalar function. -/
theorem ofContDiffSupported_toLp_ae
    {a b : ℝ} (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsupp : closure (Function.support φ) ⊆ Set.Ioo a b) :
    (ofContDiffSupported φ hφ hsupp).toLp =ᵐ[
      volume.restrict (Set.Ioc a b)] φ :=
  (ofContDiffSupported φ hφ hsupp).memLp.coeFn_toLp

/-- The derivative `L²` representative of a smooth supported test agrees
almost everywhere with its classical derivative. -/
theorem ofContDiffSupported_derivToLp_ae
    {a b : ℝ} (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsupp : closure (Function.support φ) ⊆ Set.Ioo a b) :
    (ofContDiffSupported φ hφ hsupp).derivToLp =ᵐ[
      volume.restrict (Set.Ioc a b)] deriv φ :=
  (ofContDiffSupported φ hφ hsupp).derivMemLp.coeFn_toLp

/-- A smooth test supported in `(a,b)` vanishes at the initial endpoint. -/
theorem ofContDiffSupported_initial_zero
    {a b : ℝ} (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsupp : closure (Function.support φ) ⊆ Set.Ioo a b) :
    (ofContDiffSupported φ hφ hsupp).toFun a = 0 := by
  dsimp [ofContDiffSupported]
  by_contra ha
  have hamem : a ∈ Function.support φ := Function.mem_support.mpr ha
  exact (lt_irrefl a) (hsupp (subset_closure hamem)).1

/-- If `q(t) = q₀ + ∫ₐᵗ g` on `[a, b]` with `g` continuous, then every time test satisfies
`-∫ₐᵇ q τ' = ∫ₐᵇ g τ + q₀ τ(a)`. -/
theorem initial_identity_of_integral_eq
    {a b : ℝ} (hab : a ≤ b) (τ : TimeTest a b)
    {q g : ℝ → ℝ} (hg : Continuous g) (q₀ : ℝ)
    (hq : ∀ t ∈ Icc a b, (∫ s in a..t, g s) = q t - q₀) :
    -(∫ t in a..b, q t * τ.derivFun t) =
      (∫ t in a..b, g t * τ.toFun t) + q₀ * τ.toFun a := by
  let Q := fun t ↦ q₀ + ∫ s in a..t, g s
  have hQderiv (t : ℝ) : HasDerivAt Q (g t) t :=
    (intervalIntegral.integral_hasDerivAt_right
      (hg.intervalIntegrable (μ := volume) a t)
      hg.aestronglyMeasurable.stronglyMeasurableAtFilter
      hg.continuousAt).const_add q₀
  have hQeq (t : ℝ) (ht : t ∈ Icc a b) : Q t = q t := by
    dsimp only [Q]
    rw [hq t ht]
    linarith
  have hQinitial : Q a = q₀ := by
    simp only [Q, intervalIntegral.integral_same, add_zero]
  have hτint : IntervalIntegrable τ.derivFun volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact τ.derivMemLp.integrable (by norm_num)
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun t _ ↦ hQderiv t)
    (fun t ht ↦ τ.hasDerivAt t (by simpa only [uIcc_of_le hab] using ht))
    (hg.intervalIntegrable (μ := volume) a b) hτint
  have hleft :
      (∫ t in a..b, Q t * τ.derivFun t) =
        ∫ t in a..b, q t * τ.derivFun t := by
    apply intervalIntegral.integral_congr
    intro t ht
    change Q t * τ.derivFun t = q t * τ.derivFun t
    rw [hQeq t (by simpa only [uIcc_of_le hab] using ht)]
  rw [hleft, τ.final_zero, hQinitial] at hparts
  simp only [mul_zero, zero_sub] at hparts
  linarith

end TimeTest

end PDE.Analysis.Evolution
