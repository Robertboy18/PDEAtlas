/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Transport
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import PDE.Analysis.Integration.ParametricInterval

/-!
# Nonhomogeneous transport equation

We study the characteristic formula (5) of Evans, §2.1.2, for the nonhomogeneous problem (4)
with constant velocity, posed as the problem with source `f` defined in
`PDE.Hyperbolic.Models.Transport`:

`u(t, x) = g(x - t b) + ∫₀ᵗ f(s, x + (s - t) b) ds`.

We prove the representation for every classical solution, construct the
explicit source integral, check that it solves the IVP, and derive
classical uniqueness on nonnegative time.

## Main results

* `transportCharacteristic`: the straight characteristic `s ↦ (s, x + (s-t)b)`
  through `(t, x)`; `hasDerivAt_comp_transportCharacteristic` is the chain
  rule identifying `d/ds u(characteristic)` with the transport operator.
* `transportIVP_representation`: every solution of the forced IVP that is
  differentiable along the characteristic segment is given by the formula,
  by the fundamental theorem of calculus along the characteristic.
* `transportSolutionFormula`, `transportSolutionFormula_satisfiesPDEProblem`:
  the formula itself solves the IVP for differentiable `g` and `C¹` source.
* `transportIVP_unique`: two globally differentiable solutions with the same
  data agree for `t ≥ 0`.

## Implementation notes

Spacetime points are `p : ℝ^(n+1)` with `p 0` the time; `transportInner b p`
is the characteristic foot `x - t b`. Differentiability of the explicit
formula is obtained by writing it in the adapted coordinates
`transportCoordinatesCLM` and differentiating a parametric interval
integral.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.1.2, equations (4)-(5).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (advectiveDerivative SatisfiesPDEProblem)

namespace TransportEquation

open scoped Interval

open PDE.Common

variable {n : ℕ}

private theorem continuous_timeSpaceCons :
    Continuous fun p : ℝ × ℝ^n ↦ timeSpaceCons (n := n) p.1 p.2 := by
  let e0 : ℝ^(n + 1) := EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)
  have heq : (fun p : ℝ × ℝ^n ↦ timeSpaceCons (n := n) p.1 p.2) =
        fun p ↦ p.1 • e0 + PDE.Common.embedWithTimeZeroCLM n p.2 := by
    funext p
    ext i
    cases i using Fin.cases
    · simp [e0]
    · simp [e0]
  rw [heq]
  exact (continuous_fst.smul continuous_const).add
    ((PDE.Common.embedWithTimeZeroCLM n).continuous.comp continuous_snd)

/-- The characteristic through `x` at time `t`, parametrized by time `s`. -/
noncomputable def transportCharacteristic (b : ℝ^n) (t : ℝ) (x : ℝ^n) (s : ℝ) :
    ℝ^(n + 1) :=
  timeSpaceCons (n := n) s (x + (s - t) • b)

/-- At time zero, the characteristic reaches the foot point `x - t • b`. -/
@[simp]
theorem transportCharacteristic_zero (b : ℝ^n) (t : ℝ) (x : ℝ^n) :
    transportCharacteristic b t x 0 = timeSpaceCons 0 (x - t • b) := by
  ext i
  cases i using Fin.cases <;> simp [transportCharacteristic, sub_eq_add_neg]

/-- At time `t`, the characteristic passes through the prescribed point `(t, x)`. -/
@[simp]
theorem transportCharacteristic_self (b : ℝ^n) (t : ℝ) (x : ℝ^n) :
    transportCharacteristic b t x t = timeSpaceCons t x := by
  ext i
  cases i using Fin.cases <;> simp [transportCharacteristic]

/-- A constant-velocity characteristic has spacetime velocity `(1,b)`. -/
theorem hasDerivAt_transportCharacteristic (b : ℝ^n) (t : ℝ) (x : ℝ^n) (s : ℝ) :
    HasDerivAt (transportCharacteristic b t x) (timeSpaceCons 1 b) s := by
  have hline : transportCharacteristic b t x =
        fun r ↦ timeSpaceCons 0 (x - t • b) + r • timeSpaceCons 1 b := by
    funext r
    ext i
    cases i using Fin.cases
    · simp [transportCharacteristic]
    · simp only [transportCharacteristic, timeSpaceCons_succ, PiLp.add_apply, PiLp.smul_apply,
        smul_eq_mul, PiLp.sub_apply]
      ring
  rw [hline]
  simpa only [id_eq, one_smul] using ((hasDerivAt_id s).smul_const (timeSpaceCons 1 b)).const_add
      (timeSpaceCons 0 (x - t • b))

/-- Constant-velocity characteristics are differentiable. -/
theorem differentiable_transportCharacteristic (b : ℝ^n) (t : ℝ) (x : ℝ^n) :
    Differentiable ℝ (transportCharacteristic b t x) :=
  fun s ↦ (hasDerivAt_transportCharacteristic b t x s).differentiableAt

/-- The chain rule along a constant-velocity characteristic. -/
theorem hasDerivAt_comp_transportCharacteristic (b : ℝ^n) (u : ℝ^(n + 1) → ℝ) (t : ℝ) (x : ℝ^n)
    (s : ℝ) (hu : DifferentiableAt ℝ u (transportCharacteristic b t x s)) :
    HasDerivAt (fun r ↦ u (transportCharacteristic b t x r))
      (transportOperator b u (transportCharacteristic b t x s)) s := by
  have hcomp := hu.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_transportCharacteristic b t x s)
  simpa only [Function.comp_def, transportOperator, advectiveDerivative] using hcomp

/-- The representation formula (5) of Evans, §2.1.2, for a classical forced transport solution
at `(t,x)`.

The assumptions are local to the characteristic segment. In particular, the source only needs
to be interval integrable along that segment. -/
theorem transportIVP_representation {b : ℝ^n} {f : ℝ^(n + 1) → ℝ} {g : ℝ^n → ℝ} {u : ℝ^(n + 1) → ℝ}
    (hu : SatisfiesPDEProblem (transportIVP b f g) u) {t : ℝ} (ht : 0 ≤ t) (x : ℝ^n)
    (hdu : ∀ s ∈ Set.Icc (0 : ℝ) t, DifferentiableAt ℝ u (transportCharacteristic b t x s))
    (hf :
      IntervalIntegrable (fun s ↦ f (transportCharacteristic b t x s)) MeasureTheory.volume 0 t) :
    u (timeSpaceCons t x) = g (x - t • b) + ∫ s in (0 : ℝ)..t,
      f (transportCharacteristic b t x s) := by
  let curve : ℝ → ℝ := fun s ↦ u (transportCharacteristic b t x s)
  let source : ℝ → ℝ := fun s ↦ f (transportCharacteristic b t x s)
  have hcurve_cont : ContinuousOn curve (Set.Icc 0 t) :=
    fun s hs ↦ (hasDerivAt_comp_transportCharacteristic b u t x s (hdu s hs)).continuousAt
      |>.continuousWithinAt
  have hcurve_deriv :
      ∀ s ∈ Set.Ioo (0 : ℝ) t, HasDerivAt curve (source s) s := by
    intro s hs
    have hp : transportCharacteristic b t x s ∈ transportDomain n := by
      simpa [transportDomain, transportCharacteristic] using hs.1
    have hres := transportIVP.residual_eq hu hp
    simpa [curve, source, hres] using hasDerivAt_comp_transportCharacteristic b u t x s
        (hdu s ⟨hs.1.le, hs.2.le⟩)
  have hFTC : (∫ s in (0 : ℝ)..t, source s) = curve t - curve 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht hcurve_cont hcurve_deriv hf
  have hinit :
      u (timeSpaceCons 0 (x - t • b)) = g (x - t • b) := by
    apply transportIVP.initial_eq hu
    simp [initialDomain]
  have hend : curve t = u (timeSpaceCons t x) := by
    simp [curve]
  have hzero : curve 0 = u (timeSpaceCons 0 (x - t • b)) := by
    simp [curve]
  dsimp only [source] at hFTC
  rw [hend, hzero, hinit] at hFTC
  linarith

/-- Continuous sources satisfy the integrability condition in the representation theorem. -/
theorem transportIVP_representation_of_continuous {b : ℝ^n} {f : ℝ^(n + 1) → ℝ} {g : ℝ^n → ℝ}
    {u : ℝ^(n + 1) → ℝ} (hu : SatisfiesPDEProblem (transportIVP b f g) u)
    (hdu : ∀ p, DifferentiableAt ℝ u p) (hf : Continuous f) {t : ℝ} (ht : 0 ≤ t) (x : ℝ^n) :
    u (timeSpaceCons t x) = g (x - t • b) + ∫ s in (0 : ℝ)..t,
      f (transportCharacteristic b t x s) := by
  apply transportIVP_representation hu ht x
  · exact fun s _hs ↦ hdu (transportCharacteristic b t x s)
  · simpa [Function.comp_def] using (hf.comp
        (differentiable_transportCharacteristic b t x).continuous).intervalIntegrable
          (μ := MeasureTheory.volume) 0 t

/-- Explicit characteristic formula for the forced transport equation. -/
noncomputable def transportSolutionFormula
    (b : ℝ^n) (f : ℝ^(n + 1) → ℝ) (g : ℝ^n → ℝ) :
    ℝ^(n + 1) → ℝ :=
  fun p ↦
    g (transportInner b p) +
      ∫ s in (0 : ℝ)..p 0,
        f (transportCharacteristic b (p 0) (spatialPartCLM n p) s)

/-- The characteristic foot `x - t•b` of a spacetime point, through its spatial part and time. -/
@[simp]
theorem transportInner_eq_spatialPartCLM_sub_time_smul (b : ℝ^n) (p : ℝ^(n + 1)) :
    transportInner b p = spatialPartCLM n p - (p 0) • b := by
  ext i
  simp [transportInner_apply, spatialPartCLM_apply]

/--
Every point of the characteristic through `(t, x)` has the same foot `x - t•b`:
the foot is a first integral of the constant-velocity flow.
-/
theorem transportInner_transportCharacteristic (b : ℝ^n) (t : ℝ) (x : ℝ^n) (s : ℝ) :
    transportInner b (transportCharacteristic b t x s) = x - t • b := by
  ext i
  simp only [transportCharacteristic, sub_eq_add_neg,
    transportInner_eq_spatialPartCLM_sub_time_smul, spatialPartCLM_timeSpaceCons,
    timeSpaceCons_zero, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.neg_apply]
  ring

/-- The characteristic through any point of a characteristic is the same curve. -/
@[simp]
theorem transportCharacteristic_comp (b : ℝ^n) (t : ℝ) (x : ℝ^n) (r s : ℝ) :
    transportCharacteristic b r (spatialPartCLM n (transportCharacteristic b t x r)) s =
      transportCharacteristic b t x s := by
  ext i
  cases i using Fin.cases
  · simp [transportCharacteristic]
  · simp only [transportCharacteristic, spatialPartCLM_timeSpaceCons, timeSpaceCons_succ,
      PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring

/-- On a characteristic, the explicit solution is an ordinary source antiderivative. -/
theorem transportSolutionFormula_apply_characteristic (b : ℝ^n) (f : ℝ^(n + 1) → ℝ) (g : ℝ^n → ℝ)
    (t : ℝ) (x : ℝ^n) (r : ℝ) :
    transportSolutionFormula b f g (transportCharacteristic b t x r) =
      g (x - t • b) + ∫ s in (0 : ℝ)..r, f (transportCharacteristic b t x s) := by
  unfold transportSolutionFormula
  rw [transportInner_transportCharacteristic]
  have htime : transportCharacteristic b t x r 0 = r := by
    simp [transportCharacteristic]
  rw [htime]
  congr 1
  refine intervalIntegral.integral_congr fun s _hs ↦ ?_
  exact congrArg f (transportCharacteristic_comp b t x r s)

private theorem differentiableAt_transportSourceIntegral (b : ℝ^n) (f : ℝ^(n + 1) → ℝ)
    (hf : ContDiff ℝ 1 f) (p : ℝ × ℝ^n) :
    DifferentiableAt ℝ (fun q ↦ ∫ s in (0 : ℝ)..q.1, f (timeSpaceCons (n := n) s (q.2 + s • b)))
    p := by
  let L : (ℝ × ℝ^n) →L[ℝ] ℝ^(n + 1) := (PDE.Common.embedWithTimeZeroCLM n).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ^n))
  let A : ℝ × ℝ^n → ℝ → ℝ^(n + 1) := fun q s ↦ timeSpaceCons (n := n) s (q.2 + s • b)
  let H : ℝ × ℝ^n → ℝ → ℝ := fun q s ↦ f (A q s)
  let F' : ℝ × ℝ^n → ℝ → (ℝ × ℝ^n) →L[ℝ] ℝ := fun q s ↦ (fderiv ℝ f (A q s)).comp L
  have hA : Continuous fun qs : (ℝ × ℝ^n) × ℝ ↦ A qs.1 qs.2 := by
    have hinput : Continuous fun qs : (ℝ × ℝ^n) × ℝ ↦ (qs.2, qs.1.2 + qs.2 • b) :=
      continuous_snd.prodMk ((continuous_snd.comp continuous_fst).add
          (continuous_snd.smul continuous_const))
    simpa [A, Function.comp_def] using continuous_timeSpaceCons.comp hinput
  have hH : Continuous fun qs : (ℝ × ℝ^n) × ℝ ↦ H qs.1 qs.2 := hf.continuous.comp hA
  have hfderiv : Continuous (fderiv ℝ f) :=
    (hf.fderiv_right (m := 0) (n := 1) (by norm_num)).continuous
  have hF' : Continuous fun qs : (ℝ × ℝ^n) × ℝ ↦ F' qs.1 qs.2 :=
    (hfderiv.comp hA).clm_comp continuous_const
  have hderiv (q : ℝ × ℝ^n) (s : ℝ) :
      HasFDerivAt (fun y ↦ H y s) (F' q s) q := by
    have hmap : HasFDerivAt (A · s) L q := by
      have heq : (A · s) = fun y : ℝ × ℝ^n ↦
              timeSpaceCons (n := n) s (s • b) + L y := by
        funext y
        ext i
        cases i using Fin.cases
        · simp [A, L]
        · simp [A, L, add_comm]
      rw [heq]
      exact L.hasFDerivAt.const_add (timeSpaceCons (n := n) s (s • b))
    have hcomp := (hf.differentiable one_ne_zero).differentiableAt.hasFDerivAt.comp q hmap
    simpa [H, F', A, Function.comp_def] using hcomp
  simpa [H, A] using (PDE.Analysis.hasFDerivAt_intervalIntegral_moving_right_fst_of_continuous
      H F' hH hF' hderiv p).differentiableAt

/-- Spacetime coordinates adapted to the transport flow: time and characteristic foot. -/
noncomputable def transportCoordinatesCLM (b : ℝ^n) :
    ℝ^(n + 1) →L[ℝ] ℝ × ℝ^n :=
  ContinuousLinearMap.prod
    (EuclideanSpace.proj (0 : Fin (n + 1))) (transportInnerCLM b)

/-- The adapted coordinates of `p` are its time `p 0` and its characteristic foot. -/
@[simp]
theorem transportCoordinatesCLM_apply (b : ℝ^n) (p : ℝ^(n + 1)) :
    transportCoordinatesCLM b p = (p 0, transportInner b p) := by
  simp [transportCoordinatesCLM, transportInner, ContinuousLinearMap.prod_apply]

/--
The characteristic through `p`, written from its foot: at parameter `s` it sits
at `(s, foot(p) + s•b)`.  This is the form used in the adapted coordinates.
-/
theorem transportCharacteristic_eq_timeSpaceCons_foot (b : ℝ^n) (p : ℝ^(n + 1)) (s : ℝ) :
    transportCharacteristic b (p 0) (spatialPartCLM n p) s =
      timeSpaceCons s (transportInner b p + s • b) := by
  ext i
  cases i using Fin.cases
  · simp [transportCharacteristic]
  · simp only [transportCharacteristic, timeSpaceCons_succ, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul, transportInner_eq_spatialPartCLM_sub_time_smul, PiLp.sub_apply]
    ring

/-- Coordinate form of the explicit formula, separating the characteristic foot from time. -/
theorem transportSolutionFormula_eq_coordinates (b : ℝ^n) (f : ℝ^(n + 1) → ℝ) (g : ℝ^n → ℝ)
    (p : ℝ^(n + 1)) :
    transportSolutionFormula b f g p = let q := transportCoordinatesCLM b p; g q.2 +
      ∫ s in (0 : ℝ)..q.1, f (timeSpaceCons s (q.2 + s • b)) := by
  simp only [transportSolutionFormula, transportCoordinatesCLM_apply]
  congr 1
  refine intervalIntegral.integral_congr fun s _hs ↦ ?_
  exact congrArg f (transportCharacteristic_eq_timeSpaceCons_foot b p s)

/-- The explicit formula is differentiable when the profile is differentiable and the source is
`C¹`. -/
theorem differentiableAt_transportSolutionFormula (b : ℝ^n) (f : ℝ^(n + 1) → ℝ) (g : ℝ^n → ℝ)
    (p : ℝ^(n + 1)) (hg : DifferentiableAt ℝ g (transportInner b p)) (hf : ContDiff ℝ 1 f) :
    DifferentiableAt ℝ (transportSolutionFormula b f g) p := by
  let Q : ℝ^(n + 1) →L[ℝ] ℝ × ℝ^n := transportCoordinatesCLM b
  let J : ℝ × ℝ^n → ℝ := fun q ↦ ∫ s in (0 : ℝ)..q.1, f (timeSpaceCons (n := n) s (q.2 + s • b))
  have hJ : DifferentiableAt ℝ J (Q p) := differentiableAt_transportSourceIntegral b f hf (Q p)
  have hprofile :
      DifferentiableAt ℝ (fun q : ℝ × ℝ^n ↦ g q.2 + J q) (Q p) := by
    apply DifferentiableAt.add
    · exact hg.comp (Q p) (ContinuousLinearMap.snd ℝ ℝ (ℝ^n)).differentiableAt
    · exact hJ
  have hcomp : DifferentiableAt ℝ (fun z ↦ g (Q z).2 + J (Q z)) p :=
    hprofile.comp p Q.differentiableAt
  have heq : transportSolutionFormula b f g =
        fun z ↦ g (Q z).2 + J (Q z) := by
    funext z
    dsimp only [Q, J]
    rw [transportCoordinatesCLM_apply]
    exact transportSolutionFormula_eq_coordinates b f g z
  rw [heq]
  exact hcomp

/-- Global differentiability of the explicit formula for a differentiable profile and `C¹`
source. -/
theorem differentiable_transportSolutionFormula (b : ℝ^n) (f : ℝ^(n + 1) → ℝ) (g : ℝ^n → ℝ)
    (hg : Differentiable ℝ g) (hf : ContDiff ℝ 1 f) :
    Differentiable ℝ (transportSolutionFormula b f g) :=
  fun p ↦ differentiableAt_transportSolutionFormula b f g p (hg (transportInner b p)) hf

/-- The explicit forced transport formula has the prescribed value on the initial slice. -/
theorem transportSolutionFormula_initial (b : ℝ^n) (f : ℝ^(n + 1) → ℝ) (g : ℝ^n → ℝ) (p : ℝ^(n + 1))
    (hp : p ∈ initialDomain n) :
    transportSolutionFormula b f g p = g (spatialPartCLM n p) := by
  have hp0 : p 0 = 0 := hp
  simp [transportSolutionFormula, hp0]

/-- The explicit formula has source derivative along each characteristic. -/
theorem hasDerivAt_transportSolutionFormula_characteristic (b : ℝ^n) (f : ℝ^(n + 1) → ℝ)
    (g : ℝ^n → ℝ) (hf : Continuous f) (t : ℝ) (x : ℝ^n) (r : ℝ) :
    HasDerivAt (fun s ↦ transportSolutionFormula b f g (transportCharacteristic b t x s))
      (f (transportCharacteristic b t x r)) r := by
  let source : ℝ → ℝ := fun s ↦ f (transportCharacteristic b t x s)
  have hsource : Continuous source :=
    hf.comp (differentiable_transportCharacteristic b t x).continuous
  have hFTC : HasDerivAt (fun q ↦ ∫ s in (0 : ℝ)..q, source s) (source r) r :=
    (hsource.integral_hasStrictDerivAt 0 r).hasDerivAt
  have heq : (fun s ↦ transportSolutionFormula b f g (transportCharacteristic b t x s)) =
        fun s ↦ g (x - t • b) + ∫ q in (0 : ℝ)..s, source q := by
    funext s
    exact transportSolutionFormula_apply_characteristic b f g t x s
  rw [heq]
  simpa [source] using hFTC.const_add (g (x - t • b))

/-- At differentiability points, the explicit formula satisfies the forced transport residual. -/
theorem transportOperator_transportSolutionFormula (b : ℝ^n) (f : ℝ^(n + 1) → ℝ) (g : ℝ^n → ℝ)
    (hf : Continuous f) (p : ℝ^(n + 1))
    (hU : DifferentiableAt ℝ (transportSolutionFormula b f g) p) :
    transportOperator b (transportSolutionFormula b f g) p = f p := by
  let t := p 0
  let x := spatialPartCLM n p
  have hp : transportCharacteristic b t x t = p := by
    ext i
    cases i using Fin.cases
    · simp [t, x, transportCharacteristic]
    · simp [t, x, transportCharacteristic]
  have hchain := hasDerivAt_comp_transportCharacteristic b
      (transportSolutionFormula b f g) t x t (by rw [hp]; exact hU)
  have hformula := hasDerivAt_transportSolutionFormula_characteristic b f g hf t x t
  rw [hp] at hchain hformula
  exact hchain.unique hformula

/-- The explicit formula satisfies the bundled forced IVP once its classical differentiability is
available on positive-time spacetime. -/
theorem transportSolutionFormula_satisfiesPDEProblem_of_differentiable (b : ℝ^n) (f : ℝ^(n + 1) → ℝ)
    (g : ℝ^n → ℝ) (hf : Continuous f)
    (hU : ∀ p ∈ transportDomain n, DifferentiableAt ℝ (transportSolutionFormula b f g) p) :
    SatisfiesPDEProblem (transportIVP b f g) (transportSolutionFormula b f g) := by
  apply transportIVP.of_residual_initial
  · exact fun p hp ↦ transportOperator_transportSolutionFormula b f g hf p (hU p hp)
  · exact transportSolutionFormula_initial b f g

/-- The characteristic formula satisfies the bundled forced IVP for differentiable initial data
and a `C¹` source. -/
theorem transportSolutionFormula_satisfiesPDEProblem (b : ℝ^n) (f : ℝ^(n + 1) → ℝ) (g : ℝ^n → ℝ)
    (hg : Differentiable ℝ g) (hf : ContDiff ℝ 1 f) :
    SatisfiesPDEProblem (transportIVP b f g) (transportSolutionFormula b f g) := by
  apply transportSolutionFormula_satisfiesPDEProblem_of_differentiable b f g hf.continuous
  exact fun p _hp ↦ differentiableAt_transportSolutionFormula b f g p (hg (transportInner b p)) hf

/-- Every globally classical forced transport solution equals the characteristic formula at
nonnegative times. -/
theorem eq_transportSolutionFormula {b : ℝ^n} {f : ℝ^(n + 1) → ℝ} {g : ℝ^n → ℝ} {u : ℝ^(n + 1) → ℝ}
    (hu : SatisfiesPDEProblem (transportIVP b f g) u) (hdu : ∀ p, DifferentiableAt ℝ u p)
    (hf : Continuous f) (p : ℝ^(n + 1)) (hp : 0 ≤ p 0) :
    u p = transportSolutionFormula b f g p := by
  let t := p 0
  let x := spatialPartCLM n p
  have htx : timeSpaceCons t x = p := by
    simp [t, x]
  have hrep := transportIVP_representation_of_continuous hu hdu hf hp x
  rw [htx] at hrep
  unfold transportSolutionFormula
  rw [transportInner_eq_spatialPartCLM_sub_time_smul]
  simpa [t, x] using hrep

/-- Uniqueness of globally classical forced transport solutions on nonnegative time. -/
theorem transportIVP_unique {b : ℝ^n} {f : ℝ^(n + 1) → ℝ} {g : ℝ^n → ℝ} {u v : ℝ^(n + 1) → ℝ}
    (hu : SatisfiesPDEProblem (transportIVP b f g) u)
    (hv : SatisfiesPDEProblem (transportIVP b f g) v) (hdu : ∀ p, DifferentiableAt ℝ u p)
    (hdv : ∀ p, DifferentiableAt ℝ v p) (hf : Continuous f) {p : ℝ^(n + 1)} (hp : 0 ≤ p 0) :
    u p = v p := by
  rw [eq_transportSolutionFormula hu hdu hf p hp, eq_transportSolutionFormula hv hdv hf p hp]

end TransportEquation
