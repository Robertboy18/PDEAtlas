/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.SimpleWave
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Wave curves for one-dimensional conservation-law systems

We formalize the elementary waves used in Evans's local solution of the Riemann problem:

* genuine nonlinearity and linear degeneracy of a characteristic field;
* Lax shocks, contact discontinuities, and rarefaction connections;
* a local family of ordered wave transformations;
* the derivative of their composition with respect to wave strengths.

For a family `Tₖ`, `composedWaveMap` applies

`T₀(t₀, ·), T₁(t₁, ·), ..., Tₘ₋₁(tₘ₋₁, ·)`

in characteristic order. Its derivative at zero sends the `k`th coordinate
vector to the `k`th right eigenvector. This is the nonsingularity input for
the local Riemann solver.

The conditions are those of Evans: genuine nonlinearity and linear degeneracy are (11)-(12) of
§11.2.1, rarefaction connections come from Theorem 1 of §11.2.2, and contact discontinuities
and the Lax entropy condition (42) are in §11.2.3(b). Our `LaxShock` also asks for separation
from the neighboring families, which (42) does not include. The ordered composition is the map
`Φ` of the proof of Theorem 4 in §11.2.4, and its derivative at zero is (49).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.2.1, equations (11)-(12); §11.2.2, Theorem 1;
  §11.2.3(b), equations (32)-(42); §11.2.4, proof of Theorem 4, equations (44)-(49).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System

variable {m : ℕ}

/-! ## Shocks, contacts, and rarefactions -/

/-- A Lax shock satisfies Rankine–Hugoniot, compression in family `k`, and separation
from every lower family on the left and every higher family on the right. The indices
are the characteristic order; endpoint families have only one separating side. -/
def LaxShock
    {flux : ℝ^m → ℝ^m} (fields : Fin m → CharacteristicField flux) (k : Fin m)
    (uL uR : ℝ^m) (speed : ℝ) : Prop :=
  RankineHugoniot flux uL uR speed ∧ (fields k).speed uR < speed ∧ speed < (fields k).speed uL ∧
    (∀ j, j < k → (fields j).speed uL < speed) ∧
    (∀ j, k < j → speed < (fields j).speed uR)

/-- A contact discontinuity satisfies Rankine–Hugoniot and travels at the
same characteristic speed on both sides. Linear degeneracy and the
regularity needed to produce such connections are separate hypotheses. -/
def ContactDiscontinuity
    {flux : ℝ^m → ℝ^m} (C : CharacteristicField flux)
    (uL uR : ℝ^m) (speed : ℝ) : Prop :=
  RankineHugoniot flux uL uR speed ∧ speed = C.speed uL ∧ speed = C.speed uR

/-- A rarefaction connection follows a characteristic integral curve from
the left state to the right state, with characteristic speed strictly
increasing all along the oriented segment.

The curve is defined on an open neighborhood of its closed parameter segment.
The auxiliary parameter `θ ∈ [0, 1]` orients the segment from `uL` to `uR` independently of the sign
of `strength`. Requiring monotonicity on the whole segment is the condition needed to invert the
speed when constructing the self-similar rarefaction fan; an endpoint inequality alone would not
suffice. -/
def IsRarefactionConnection
    {flux : ℝ^m → ℝ^m} (C : CharacteristicField flux)
    (uL uR : ℝ^m) : Prop :=
  ∃ curve : ℝ → ℝ^m, ∃ strength : ℝ,
    ∃ interval : Set ℝ, IsOpen interval ∧ Set.uIcc 0 strength ⊆ interval ∧
      ContDiffOn ℝ 1 curve interval ∧
      curve 0 = uL ∧
      IsIntegralCurveOn curve C.vectorField interval ∧
      curve strength = uR ∧
      StrictMonoOn (fun θ : ℝ ↦ C.speed (curve (θ * strength))) (Set.Icc 0 1)

/-- The characteristic speed at the right state of a rarefaction connection
is greater than at the left state. -/
theorem IsRarefactionConnection.speed_lt {flux : ℝ^m → ℝ^m} {C : CharacteristicField flux}
    {uL uR : ℝ^m} (h : IsRarefactionConnection C uL uR) :
    C.speed uL < C.speed uR := by
  rcases h with
    ⟨curve, strength, _interval, _hopen, _hsegment, _hreg, hleft, _hflow, hright, hmono⟩
  have hzero : (0 : ℝ) ∈ Set.Icc 0 1 := by norm_num
  have hone : (1 : ℝ) ∈ Set.Icc 0 1 := by norm_num
  simpa [hleft, hright] using hmono hzero hone zero_lt_one

/-- An elementary admissible connection is either no jump, a rarefaction,
a Lax shock, or a contact discontinuity. -/
inductive IsElementaryConnection
    {flux : ℝ^m → ℝ^m} (fields : Fin m → CharacteristicField flux) (k : Fin m) :
    ℝ^m → ℝ^m → Prop
  | same (state : ℝ^m) : IsElementaryConnection fields k state state
  | rarefaction {uL uR : ℝ^m} :
      IsRarefactionConnection (fields k) uL uR →
      IsElementaryConnection fields k uL uR
  | shock {uL uR : ℝ^m} (speed : ℝ) :
      LaxShock fields k uL uR speed →
      IsElementaryConnection fields k uL uR
  | contact {uL uR : ℝ^m} (speed : ℝ) :
      ContactDiscontinuity (fields k) uL uR speed →
      IsElementaryConnection fields k uL uR

/-- A linearly degenerate integral curve lies in the Hugoniot locus and
therefore connects any two of its states by a contact discontinuity.

The Rankine–Hugoniot identity follows from the vector-valued fundamental
theorem of calculus and the characteristic eigenvector equation. -/
theorem ContactDiscontinuity.of_linearlyDegenerate_integralCurve {flux : ℝ^m → ℝ^m}
    (C : CharacteristicField flux) {curve : ℝ → ℝ^m} (hdegenerate : C.IsLinearlyDegenerate)
    (hflux : ContDiff ℝ 1 flux) (hcurve : ContDiff ℝ 1 curve)
    (hintegral : IsIntegralCurve curve C.vectorField) (sL sR : ℝ) :
    ContactDiscontinuity C (curve sL) (curve sR) (C.speed (curve sL)) := by
  have hfluxDiff : Differentiable ℝ flux := hflux.differentiable one_ne_zero
  have hcurveDiff : Differentiable ℝ curve := hcurve.differentiable one_ne_zero
  have hspeedEq (s : ℝ) : C.speed (curve sL) = C.speed (curve s) :=
    hdegenerate.speed_eq_on_integralCurve hintegral sL s
  have hcurveDeriv (s : ℝ) : HasDerivAt curve (C.rightEigenvector (curve s)) s := hintegral s
  have hfluxCurveDeriv (s : ℝ) : HasDerivAt (flux ∘ curve)
        (C.speed (curve sL) • C.rightEigenvector (curve s)) s := by
    have hchain := (hfluxDiff (curve s)).hasFDerivAt.comp_hasDerivAt s (hcurveDeriv s)
    exact hchain.congr_deriv <| by
      calc
        (fderiv ℝ flux (curve s)) (C.rightEigenvector (curve s)) =
            C.speed (curve s) • C.rightEigenvector (curve s) :=
          (C.eigenvector (curve s)).apply_eq_smul
        _ = C.speed (curve sL) • C.rightEigenvector (curve s) := by
          rw [hspeedEq s]
  have hfluxCurve : ContDiff ℝ 1 (flux ∘ curve) := hflux.comp hcurve
  have hFTCFlux : (∫ s in sL..sR, deriv (flux ∘ curve) s) = flux (curve sR) - flux (curve sL) :=
    intervalIntegral.integral_deriv_eq_sub (fun s _ ↦ (hfluxCurve.differentiable one_ne_zero) s)
      (hfluxCurve.continuous_deriv_one.intervalIntegrable sL sR)
  have hFTCCurve : (∫ s in sL..sR, deriv curve s) = curve sR - curve sL :=
    intervalIntegral.integral_deriv_eq_sub (fun s _ ↦ hcurveDiff s)
      (hcurve.continuous_deriv_one.intervalIntegrable sL sR)
  have hderivCurve (s : ℝ) : deriv curve s = C.rightEigenvector (curve s) := (hcurveDeriv s).deriv
  refine ⟨?_, rfl, hspeedEq sR⟩
  change flux (curve sR) - flux (curve sL) = C.speed (curve sL) • (curve sR - curve sL)
  calc
    flux (curve sR) - flux (curve sL) = ∫ s in sL..sR, deriv (flux ∘ curve) s := hFTCFlux.symm
    _ = ∫ s in sL..sR, C.speed (curve sL) • deriv curve s := by
      refine intervalIntegral.integral_congr fun s _ ↦ ?_
      rw [(hfluxCurveDeriv s).deriv]
      exact congrArg (fun z ↦ C.speed (curve sL) • z) (hderivCurve s).symm
    _ = C.speed (curve sL) • ∫ s in sL..sR, deriv curve s := by
      rw [intervalIntegral.integral_smul]
    _ = C.speed (curve sL) • (curve sR - curve sL) := by
      rw [hFTCCurve]

/-! ## Ordered local wave families -/

/-- Derivative of one wave transformation at zero strength:
`(δt, δu) ↦ δt rₖ(u) + δu`. -/
def waveStepDerivative (rightEigenvector : ℝ^m) :
    (ℝ × ℝ^m) →L[ℝ] ℝ^m :=
  ContinuousLinearMap.smulRight (ContinuousLinearMap.fst ℝ ℝ (ℝ^m)) rightEigenvector +
    ContinuousLinearMap.snd ℝ ℝ (ℝ^m)

/-- The derivative of one wave step sends `(δt, δu)` to `δt • r + δu`. -/
@[simp]
theorem waveStepDerivative_apply (rightEigenvector : ℝ^m) (v : ℝ × ℝ^m) :
    waveStepDerivative rightEigenvector v = v.1 • rightEigenvector + v.2 :=
  rfl

/-- A differentiable wave transformation that fixes every state at zero
strength has the expected joint derivative there.

The strength derivative supplies the characteristic-vector column. The
identity law at zero strength determines the entire state block. -/
theorem hasFDerivAt_waveStep_zero (curve : ℝ → ℝ^m → ℝ^m) (state velocity : ℝ^m)
    (hzero : ∀ current, curve 0 current = current)
    (hdiff : DifferentiableAt ℝ (fun p : ℝ × ℝ^m ↦ curve p.1 p.2) (0, state))
    (htime : HasDerivAt (fun strength ↦ curve strength state) velocity 0) :
    HasFDerivAt (fun p : ℝ × ℝ^m ↦ curve p.1 p.2) (waveStepDerivative velocity) (0, state) := by
  let D := fderiv ℝ (fun p : ℝ × ℝ^m ↦ curve p.1 p.2) (0, state)
  have hcurve : HasFDerivAt (fun p : ℝ × ℝ^m ↦ curve p.1 p.2) D (0, state) := hdiff.hasFDerivAt
  have htimeFromJoint : HasDerivAt (fun strength ↦ curve strength state)
        (D ((1 : ℝ), (0 : ℝ^m))) 0 := by
    simpa [Function.comp_def] using hcurve.comp_hasDerivAt (0 : ℝ) (HasDerivAt.prodMk
          (hasDerivAt_id' (0 : ℝ)) (hasDerivAt_const (0 : ℝ) state))
  have htimeDerivative : D ((1 : ℝ), (0 : ℝ^m)) = velocity := htimeFromJoint.unique htime
  have hstrength (strength : ℝ) : D (strength, (0 : ℝ^m)) = strength • velocity := by
    calc
      D (strength, (0 : ℝ^m)) = D (strength • ((1 : ℝ), (0 : ℝ^m))) := by
        congr 1
        ext <;> simp
      _ = strength • D ((1 : ℝ), (0 : ℝ^m)) := by
        rw [map_smul]
      _ = strength • velocity := by
        rw [htimeDerivative]
  have hstate : HasFDerivAt (fun current : ℝ^m ↦ curve 0 current)
        (D.comp (ContinuousLinearMap.inr ℝ ℝ (ℝ^m))) state := by
    simpa [Function.comp_def] using hcurve.comp state (hasFDerivAt_prodMk_right (0 : ℝ) state)
  have hstateDerivative : D.comp (ContinuousLinearMap.inr ℝ ℝ (ℝ^m)) =
        ContinuousLinearMap.id ℝ (ℝ^m) := by
    have hidentity : (fun current : ℝ^m ↦ curve 0 current) = id := funext hzero
    rw [hidentity] at hstate
    exact hstate.unique (hasFDerivAt_id state)
  have hstateBlock (u : ℝ^m) : D ((0 : ℝ), u) = u := by
    calc
      D ((0 : ℝ), u) = (D.comp (ContinuousLinearMap.inr ℝ ℝ (ℝ^m))) u := rfl
      _ = (ContinuousLinearMap.id ℝ (ℝ^m)) u := by
        rw [hstateDerivative]
      _ = u := rfl
  refine hcurve.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v ↦ ?_
  rw [← D.comp_inl_add_comp_inr v]
  change D (v.1, 0) + D (0, v.2) = v.1 • velocity + v.2
  rw [hstrength, hstateBlock]

/-- A wave transformation for every characteristic family, with the strict
derivative required at zero strength for states in a specified local domain.

At zero strength the transformation fixes the base state. Its derivative
adds the strength variation in the right-eigenvector direction and passes
state variations through unchanged. The carrier functions are globally
defined for convenience; the local inverse theorem uses only their germs at
zero strength. Physical admissibility is recorded separately by
`LocalWaveFamily.IsElementary`. The identity carrier may be totalized outside
the state domain without asserting any regularity there. -/
structure LocalWaveFamily
    (flux : ℝ^m → ℝ^m)
    (fields : Fin m → CharacteristicField flux)
    (states : Set (ℝ^m) := Set.univ) where
  /-- Wave transformation `Tₖ(strength, state)`. -/
  curve : Fin m → ℝ → ℝ^m → ℝ^m
  /-- Zero strength leaves every state fixed. -/
  curve_zero : ∀ k state, curve k 0 state = state
  /-- The strict derivative at zero has the characteristic vector as its
  strength column and the identity as its state block. -/
  hasStrictFDerivAt_zero : ∀ k state, state ∈ states →
    HasStrictFDerivAt
      (fun p : ℝ × ℝ^m ↦ curve k p.1 p.2)
      (waveStepDerivative ((fields k).rightEigenvector state))
      (0, state)

namespace LocalWaveFamily

variable {flux : ℝ^m → ℝ^m}
variable {fields : Fin m → CharacteristicField flux}
variable {states : Set (ℝ^m)}

/-- A wave family is physically elementary when every transformation joins
its input and output by one of the admissible elementary connections. -/
def IsElementary (W : LocalWaveFamily flux fields states) : Prop :=
  ∀ k strength state, IsElementaryConnection fields k state (W.curve k strength state)

/-- Lift one wave step to the pair of strength vector and current state. -/
def liftStep (W : LocalWaveFamily flux fields states) (k : Fin m)
    (p : ℝ^m × ℝ^m) : ℝ^m × ℝ^m :=
  (p.1, W.curve k (p.1 k) p.2)

/-- Derivative of `liftStep` at zero strength and a fixed state. -/
def liftStepDerivative (_ : LocalWaveFamily flux fields states)
    (k : Fin m) (state : ℝ^m) :
    (ℝ^m × ℝ^m) →L[ℝ] ℝ^m × ℝ^m :=
  (ContinuousLinearMap.fst ℝ (ℝ^m) (ℝ^m)).prod
    ((waveStepDerivative ((fields k).rightEigenvector state)).comp (((EuclideanSpace.proj k).comp
        (ContinuousLinearMap.fst ℝ (ℝ^m) (ℝ^m))).prod (ContinuousLinearMap.snd ℝ (ℝ^m) (ℝ^m))))

/-- At zero strengths a lifted wave step fixes the pair. -/
@[simp]
theorem liftStep_apply_zero (W : LocalWaveFamily flux fields states) (k : Fin m) (state : ℝ^m) :
    W.liftStep k (0, state) = (0, state) := by
  simp [liftStep, W.curve_zero]

/-- The lifted step derivative passes the strength variation through and moves
the state by `(δt)ₖ • rₖ(u) + δu`. -/
@[simp]
theorem liftStepDerivative_apply (W : LocalWaveFamily flux fields states) (k : Fin m) (state : ℝ^m)
    (v : ℝ^m × ℝ^m) :
    W.liftStepDerivative k state v = (v.1, v.1 k • (fields k).rightEigenvector state + v.2) :=
  rfl

/-- Strict Fréchet derivative of one lifted wave step. -/
theorem hasStrictFDerivAt_liftStep (W : LocalWaveFamily flux fields states) (k : Fin m)
    (state : ℝ^m) (hstate : state ∈ states) :
    HasStrictFDerivAt (W.liftStep k) (W.liftStepDerivative k state) (0, state) := by
  have hcoord : HasStrictFDerivAt (fun p : ℝ^m × ℝ^m ↦ p.1 k) ((EuclideanSpace.proj k).comp
          (ContinuousLinearMap.fst ℝ (ℝ^m) (ℝ^m)))
        (0, state) := by
    have hproj : HasStrictFDerivAt (fun x : ℝ^m ↦ x k) (EuclideanSpace.proj k : ℝ^m →L[ℝ] ℝ) 0 := by
      simpa using (EuclideanSpace.proj k : ℝ^m →L[ℝ] ℝ).hasStrictFDerivAt
    have hfst : HasStrictFDerivAt (Prod.fst : ℝ^m × ℝ^m → ℝ^m)
          (ContinuousLinearMap.fst ℝ (ℝ^m) (ℝ^m)) ((0 : ℝ^m), state) := hasStrictFDerivAt_fst
    exact hproj.comp ((0 : ℝ^m), state) hfst
  have hpair : HasStrictFDerivAt (fun p : ℝ^m × ℝ^m ↦ (p.1 k, p.2)) (((EuclideanSpace.proj k).comp
          (ContinuousLinearMap.fst ℝ (ℝ^m) (ℝ^m))).prod (ContinuousLinearMap.snd ℝ (ℝ^m) (ℝ^m)))
        (0, state) := hcoord.prodMk hasStrictFDerivAt_snd
  have hcurve := (W.hasStrictFDerivAt_zero k state hstate).comp (0, state) hpair
  exact hasStrictFDerivAt_fst.prodMk hcurve

/-- Fréchet derivative of one lifted wave step. -/
theorem hasFDerivAt_liftStep (W : LocalWaveFamily flux fields states) (k : Fin m) (state : ℝ^m)
    (hstate : state ∈ states) :
    HasFDerivAt (W.liftStep k) (W.liftStepDerivative k state) (0, state) :=
  (W.hasStrictFDerivAt_liftStep k state hstate).hasFDerivAt

/-- Apply a list of characteristic wave transformations in order. The first
component of the input stores all strengths and the second is the initial
state. -/
def waveMapAlong (W : LocalWaveFamily flux fields states)
    (indices : List (Fin m)) (p : ℝ^m × ℝ^m) : ℝ^m :=
  indices.foldl (fun state k ↦ W.curve k (p.1 k) state) p.2

/-- Applying the families `k :: indices` is the lifted step for `k` followed by
the remaining families. -/
theorem waveMapAlong_cons (W : LocalWaveFamily flux fields states) (k : Fin m)
    (indices : List (Fin m)) :
    W.waveMapAlong (k :: indices) = W.waveMapAlong indices ∘ W.liftStep k := by
  funext p
  simp [waveMapAlong, liftStep]

/-- Recursive derivative of an ordered list of wave transformations. -/
def waveDerivativeAlong (W : LocalWaveFamily flux fields states) :
    List (Fin m) → ℝ^m →
      (ℝ^m × ℝ^m) →L[ℝ] ℝ^m
  | [], _ => ContinuousLinearMap.snd ℝ (ℝ^m) (ℝ^m)
  | k :: indices, state =>
      (W.waveDerivativeAlong indices state).comp
        (W.liftStepDerivative k state)

/-- The ordered wave composition has the recursively computed strict
derivative at zero strengths. -/
theorem hasStrictFDerivAt_waveMapAlong (W : LocalWaveFamily flux fields states)
    (indices : List (Fin m)) (state : ℝ^m) (hstate : state ∈ states) :
    HasStrictFDerivAt (W.waveMapAlong indices)
      (W.waveDerivativeAlong indices state) (0, state) := by
  induction indices with
  | nil =>
      exact hasStrictFDerivAt_snd
  | cons k indices ih =>
      rw [W.waveMapAlong_cons]
      have houter : HasStrictFDerivAt (W.waveMapAlong indices) (W.waveDerivativeAlong indices state)
            (W.liftStep k (0, state)) := by
        simpa using ih
      exact houter.comp (0, state) (W.hasStrictFDerivAt_liftStep k state hstate)

/-- The ordered wave composition has the corresponding Fréchet derivative
at zero strengths. -/
theorem hasFDerivAt_waveMapAlong (W : LocalWaveFamily flux fields states) (indices : List (Fin m))
    (state : ℝ^m) (hstate : state ∈ states) :
    HasFDerivAt (W.waveMapAlong indices) (W.waveDerivativeAlong indices state) (0, state) :=
  (W.hasStrictFDerivAt_waveMapAlong indices state hstate).hasFDerivAt

/-- Explicit action of the derivative for an ordered list of waves. -/
theorem waveDerivativeAlong_apply (W : LocalWaveFamily flux fields states) (indices : List (Fin m))
    (state : ℝ^m) (v : ℝ^m × ℝ^m) :
    W.waveDerivativeAlong indices state v =
      v.2 + (indices.map fun k ↦ v.1 k • (fields k).rightEigenvector state).sum := by
  induction indices generalizing v with
  | nil =>
      simp [waveDerivativeAlong]
  | cons k indices ih =>
      simp only [waveDerivativeAlong, ContinuousLinearMap.comp_apply,
        liftStepDerivative_apply, List.map_cons, List.sum_cons]
      rw [ih]
      let a : ℝ^m := v.1 k • (fields k).rightEigenvector state
      let b : ℝ^m := v.2
      let c : ℝ^m := (indices.map fun i ↦ v.1 i • (fields i).rightEigenvector state).sum
      change a + b + c = b + (a + c)
      rw [add_comm a b, add_assoc]

/-- The ordered wave map, `Φ` in the proof of Theorem 4 of Evans, §11.2.4, from wave
strengths to the final state. -/
def composedWaveMap (W : LocalWaveFamily flux fields states)
    (state : ℝ^m) : ℝ^m → ℝ^m :=
  fun strength ↦ W.waveMapAlong (List.finRange m) (strength, state)

/-- Derivative of the ordered wave map at zero strengths. -/
def composedWaveDerivative (W : LocalWaveFamily flux fields states)
    (state : ℝ^m) : ℝ^m →L[ℝ] ℝ^m :=
  (W.waveDerivativeAlong (List.finRange m) state).comp ((ContinuousLinearMap.id ℝ (ℝ^m)).prod
      (0 : ℝ^m →L[ℝ] ℝ^m))

/-- The ordered wave map has the declared strict derivative at zero. -/
theorem hasStrictFDerivAt_composedWaveMap
    (W : LocalWaveFamily flux fields states) (state : ℝ^m) (hstate : state ∈ states) :
    HasStrictFDerivAt (W.composedWaveMap state) (W.composedWaveDerivative state) 0 := by
  have hinput : HasStrictFDerivAt (fun strength : ℝ^m ↦ (strength, state))
        ((ContinuousLinearMap.id ℝ (ℝ^m)).prod (0 : ℝ^m →L[ℝ] ℝ^m)) 0 :=
    (hasStrictFDerivAt_id 0).prodMk (hasStrictFDerivAt_const state 0)
  exact (W.hasStrictFDerivAt_waveMapAlong (List.finRange m) state hstate).comp 0 hinput

/-- The ordered wave map has the corresponding Fréchet derivative at zero. -/
theorem hasFDerivAt_composedWaveMap
    (W : LocalWaveFamily flux fields states) (state : ℝ^m) (hstate : state ∈ states) :
    HasFDerivAt (W.composedWaveMap state) (W.composedWaveDerivative state) 0 :=
  (W.hasStrictFDerivAt_composedWaveMap state hstate).hasFDerivAt

/-- Zero wave strengths leave the initial state unchanged. -/
theorem waveMapAlong_zero (W : LocalWaveFamily flux fields states) (indices : List (Fin m))
    (state : ℝ^m) :
    W.waveMapAlong indices (0, state) = state := by
  induction indices generalizing state with
  | nil =>
      rfl
  | cons k indices ih =>
      rw [W.waveMapAlong_cons]
      simp only [Function.comp_apply, liftStep_apply_zero]
      exact ih state

/-- Zero wave strengths leave the left state unchanged. -/
@[simp]
theorem composedWaveMap_zero (W : LocalWaveFamily flux fields states) (state : ℝ^m) :
    W.composedWaveMap state 0 = state :=
  W.waveMapAlong_zero (List.finRange m) state

/-- The derivative of the ordered wave map is the linear combination of
right eigenvectors with coefficients given by the strength variation. -/
theorem composedWaveDerivative_apply (W : LocalWaveFamily flux fields states) (state v : ℝ^m) :
    W.composedWaveDerivative state v = ∑ k, v k • (fields k).rightEigenvector state := by
  rw [composedWaveDerivative, ContinuousLinearMap.comp_apply, waveDerivativeAlong_apply]
  simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, zero_apply, zero_add]
  rw [← List.sum_toFinset (fun k ↦ v k • (fields k).rightEigenvector state) (List.nodup_finRange m)]
  simp only [List.toFinset_finRange]

/-- The `k`th column of the derivative at zero is the `k`th right
characteristic vector, as in (49) of Evans, §11.2.4. -/
theorem composedWaveDerivative_single (W : LocalWaveFamily flux fields states) (state : ℝ^m)
    (k : Fin m) :
    W.composedWaveDerivative state (EuclideanSpace.single k (1 : ℝ)) =
      (fields k).rightEigenvector state := by
  rw [W.composedWaveDerivative_apply]
  simp

end LocalWaveFamily

end PDE.Hyperbolic.ConservationLaw.System
