/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.FirstOrder.MollifiedWeakEvolution
public import PDE.Hyperbolic.FirstOrder.TransportCommutator
public import PDE.Hyperbolic.FirstOrder.MollifiedH1
import PDE.Hyperbolic.FirstOrder.L2Cauchy

/-!
# Uniqueness in the Bochner L² weak class

Two Bochner L² states with the same forcing and initial boundary term are
spatially mollified. Their weak equations construct absolutely continuous
mollified representatives with the prescribed mollified initial value.
The residual from commuting transport and mollification is a Bochner
L² load tending to zero. The symmetric transport difference energy
estimate then forces the original states to agree almost everywhere.

The matrices are symmetric, their values are continuous in L∞ on the closed
time interval, and all first spatial derivatives have a uniform L∞ bound.
Those derivatives need not be continuous in time.

The weak identities use the library's `TimeTest` functions and fixed H¹
spatial tests. Combining uniqueness with the Cauchy construction gives a
continuous representative with the prescribed initial value and energy bound.
Equality of Bochner L² classes is almost-everywhere equality; point values
belong to the continuous representative.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal InnerProductSpace Topology

namespace PDE.Hyperbolic.FirstOrder

open PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Approximation

open scoped SobolevSpace.WholeSpaceHilbert

variable {n m : ℕ} {a b : ℝ}

local notation "D" => DerivLp n 2 univ
local notation "H" => PiLp 2 (fun _ : Fin m ↦ D)
local notation "V" => PiLp 2 (fun _ : Fin m ↦ H¹(ℝ^n))
local notation "ν" => volume.restrict (Ioc a b)

/-- At positive scale, the difference of two weak solutions is bounded by
the norms of their transport commutators. The AC representatives and their initial equality are
derived from the weak equations. -/
theorem ae_norm_mollified_sub_sq_le_of_weak_equations {ε : ℝ} (hε : 0 < ε)
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n))))
    (hA : ∀ j p q,
      ContinuousOn (fun t ↦ (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) (Icc a b))
    (hab : a < b)
    (hsym : ∀ t ∈ Icc a b, ∀ j p q, (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1) =
      (A t j q p : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1))
    {C : ℝ} (hC : 0 ≤ C) (hdiv : ∀ t ∈ Icc a b, coefficientDerivativeBound (A t) ≤ C) (L : ℝ≥0)
    (hL : ∀ t ∈ Icc a b, ∀ j p q,
      ‖(A t j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)‖ ≤ L)
    (u v f : Lp H 2 ν) (x : H)
    (hu : ∀ (φ : V) (τ : TimeTest a b), -(∫ t, ⟪u t, transportBaseCLM φ⟫_ℝ * τ.derivFun t ∂ν) =
      (∫ t, transportTestFunctional (A t) φ (u t) * τ.toFun t ∂ν) +
      (∫ t, ⟪f t, transportBaseCLM φ⟫_ℝ * τ.toFun t ∂ν) + ⟪x, transportBaseCLM φ⟫_ℝ * τ.toFun a)
    (hv : ∀ (φ : V) (τ : TimeTest a b), -(∫ t, ⟪v t, transportBaseCLM φ⟫_ℝ * τ.derivFun t ∂ν) =
      (∫ t, transportTestFunctional (A t) φ (v t) * τ.toFun t ∂ν) +
      (∫ t, ⟪f t, transportBaseCLM φ⟫_ℝ * τ.toFun t ∂ν) + ⟪x, transportBaseCLM φ⟫_ℝ * τ.toFun a)
    (R Q : Lp H 2 ν)
    (hR : (R : ℝ → H) =ᵐ[ν] fun t ↦ transportCommutator (standardMollifier n) hε (A t) (u t))
    (hQ : (Q : ℝ → H) =ᵐ[ν] fun t ↦ transportCommutator (standardMollifier n) hε (A t) (v t)) :
    ∀ᵐ t ∂ν, ‖transportBaseCLM (mollifierProductH1CLM (standardMollifier n) hε (u t)) -
      transportBaseCLM (mollifierProductH1CLM (standardMollifier n) hε (v t))‖ ^ 2 ≤ ‖R -
      Q‖ ^ 2 * Real.exp ((C + 1) * (t - a)) := by
  classical
  let S : H →L[ℝ] V := mollifierProductH1CLM (standardMollifier n) hε
  let J : H →L[ℝ] H := transportBaseCLM.comp S
  let F : Lp H 2 ν := J.compLpL 2 ν f
  obtain ⟨z, _hzcont, hzU, hzx, hz, hzeq⟩ :=
    exists_mollified_absolutelyContinuous_of_weak_equation hε A hA hab L hL u f x hu
  obtain ⟨w, _hwcont, hwV, hwx, hw, hweq⟩ :=
    exists_mollified_absolutelyContinuous_of_weak_equation hε A hA hab L hL v f x hv
  have hez : ∀ᵐ t ∂ν,
      HasDerivAt z (transportDrift (A t) (S (u t)) + (R + F) t) t := by
    filter_upwards [hzeq, hR, J.coeFn_compLpL f, Lp.coeFn_add R F] with t ht hRt hFt hsum
    rw [hsum, Pi.add_apply, hFt, hRt]
    simpa only [mollifiedTransportDrift_eq_transportDrift_add, add_assoc] using ht
  have hew : ∀ᵐ t ∂ν,
      HasDerivAt w (transportDrift (A t) (S (v t)) + (Q + F) t) t := by
    filter_upwards [hweq, hQ, J.coeFn_compLpL f, Lp.coeFn_add Q F] with t ht hQt hFt hsum
    rw [hsum, Pi.add_apply, hFt, hQt]
    simpa only [mollifiedTransportDrift_eq_transportDrift_add, add_assoc] using ht
  have henergy := h1_transport_trajectory_stability A hab.le hsym hC hdiv
    (U := fun t ↦ S (u t)) (V' := fun t ↦ S (v t)) (z := z) (w := w)
    (R + F) (Q + F) hz hw hzU hwV hez hew
  have hloads : (R + F) - (Q + F) = R - Q := by abel
  filter_upwards [hzU, hwV, ae_restrict_mem measurableSet_Ioc] with t hzt hwt ht
  have he := henergy t (Ioc_subset_Icc_self ht)
  simpa only [hzt, hwt, hzx, hwx, sub_self, norm_zero,
    zero_pow (by decide : 2 ≠ 0), zero_add, hloads, ContinuousLinearMap.comp_apply] using he

/-- Each matrix entry contributes a nonnegative part of the full gradient bound. -/
private theorem entry_gradient_sum_le (A : Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n))))
    (j : Fin n) (p q : Fin m) :
    (∑ l : Fin n, ‖(A j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n l)‖) ≤
      coefficientGradientBound A := by
  classical
  unfold coefficientGradientBound
  refine Finset.sum_le_sum fun l _ ↦ ?_
  calc
    _ ≤ ∑ q', ‖(A j p q' : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n l)‖ :=
      Finset.single_le_sum (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ q)
    _ ≤ ∑ j', ∑ q', ‖(A j' p q' : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n l)‖ :=
      Finset.single_le_sum (f := fun j' : Fin n ↦ ∑ q' : Fin m,
          ‖(A j' p q' : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n l)‖)
        (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ p', ∑ j', ∑ q', ‖(A j' p' q' : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n l)‖ :=
      Finset.single_le_sum (f := fun p' : Fin m ↦ ∑ j' : Fin n, ∑ q' : Fin m,
          ‖(A j' p' q' : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n l)‖)
        (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦
          Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) (Finset.mem_univ p)

/-- Two Bochner L² solutions of the same symmetric transport initial-value
problem agree as L² classes. Full spatial coefficient-gradient bounds control
the commutator limit; the divergence-coordinate bound controls the energy
exponent. Spatial mollification supplies the time regularity used in the proof. -/
theorem eq_of_symmetric_transport_weak_equations
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n))))
    (hA : ∀ j p q,
      ContinuousOn (fun t ↦ (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) (Icc a b))
    (hab : a < b)
    (hsym : ∀ t ∈ Icc a b, ∀ j p q, (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1) =
      (A t j q p : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1))
    {C L : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L) (hdiv : ∀ t ∈ Icc a b, coefficientDerivativeBound (A t) ≤ C)
    (hgrad : ∀ t ∈ Icc a b, coefficientGradientBound (A t) ≤ L) (u v f : Lp H 2 ν) (x : H)
    (hu : ∀ (φ : V) (τ : TimeTest a b), -(∫ t, ⟪u t, transportBaseCLM φ⟫_ℝ * τ.derivFun t ∂ν) =
      (∫ t, transportTestFunctional (A t) φ (u t) * τ.toFun t ∂ν) +
      (∫ t, ⟪f t, transportBaseCLM φ⟫_ℝ * τ.toFun t ∂ν) + ⟪x, transportBaseCLM φ⟫_ℝ * τ.toFun a)
    (hv : ∀ (φ : V) (τ : TimeTest a b), -(∫ t, ⟪v t, transportBaseCLM φ⟫_ℝ * τ.derivFun t ∂ν) =
      (∫ t, transportTestFunctional (A t) φ (v t) * τ.toFun t ∂ν) +
      (∫ t, ⟪f t, transportBaseCLM φ⟫_ℝ * τ.toFun t ∂ν) + ⟪x, transportBaseCLM φ⟫_ℝ * τ.toFun a) :
    u = v := by
  classical
  let ε : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1)
  have hε (k : ℕ) : 0 < ε k := by positivity
  have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let LN : ℝ≥0 := ⟨L, hL⟩
  have hentry (t : ℝ) (ht : t ∈ Icc a b) (j : Fin n) (p q : Fin m) : (∑ l : Fin n,
        ‖(A t j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n l)‖) ≤ LN :=
    (entry_gradient_sum_le (A t) j p q).trans (hgrad t ht)
  have hderiv (t : ℝ) (ht : t ∈ Icc a b) (j : Fin n) (p q : Fin m) :
      ‖(A t j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)‖ ≤ LN :=
    (Finset.single_le_sum (fun l _ ↦ norm_nonneg
      ((A t j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n l)))
      (Finset.mem_univ j)).trans (hentry t ht j p q)
  obtain ⟨R, hR, hRzero⟩ := exists_transportCommutatorLp_sequence
    (standardMollifier n) ε hε hε0 hab.le A hA LN hentry u
  obtain ⟨Q, hQ, hQzero⟩ := exists_transportCommutatorLp_sequence
    (standardMollifier n) ε hε hε0 hab.le A hA LN hentry v
  let S (k : ℕ) : H →L[ℝ] V := mollifierProductH1CLM (standardMollifier n) (hε k)
  let J (k : ℕ) : H →L[ℝ] H := transportBaseCLM.comp (S k)
  have hstrong (y : H) : Tendsto (fun k ↦ J k y) atTop (𝓝 y) := by
    have hcoord : Tendsto (fun k p ↦ J k y p) atTop (𝓝 (fun p ↦ y p)) := by
      refine tendsto_pi_nhds.mpr fun p ↦ ?_
      change Tendsto (fun k ↦ wkpCoordinateCLM (baseIndex n 1)
        (mollifierH1CLM (standardMollifier n) (hε k) (y p))) atTop (𝓝 (y p))
      simpa only [mollifierH1CLM_base] using
        tendsto_mollifierRowCLM (standardMollifier n) ε hε hε0 (y p)
    exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m ↦ D)).symm.continuous
      ).continuousAt.tendsto.comp hcoord
  have henergy (k : ℕ) : ∀ᵐ t ∂ν, ‖J k (u t) - J k (v t)‖ ^ 2 ≤
        ‖R k - Q k‖ ^ 2 * Real.exp ((C + 1) * (t - a)) :=
    ae_norm_mollified_sub_sq_le_of_weak_equations (hε k) A hA hab hsym hC hdiv
      LN hderiv u v f x hu hv (R k) (Q k) (hR k) (hQ k)
  apply Lp.ext
  filter_upwards [ae_all_iff.mpr henergy] with t ht
  have hle := le_of_tendsto_of_tendsto (((hstrong (u t)).sub (hstrong (v t))).norm.pow 2)
    ((((hRzero.sub hQzero).norm.pow 2)).mul
      (tendsto_const_nhds (x := Real.exp ((C + 1) * (t - a))))) (Eventually.of_forall ht)
  have hsq : ‖u t - v t‖ ^ 2 ≤ 0 := by
    simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_mul] using hle
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hsq (sq_nonneg _))))

/-- The constructed continuous Cauchy solution represents the unique Bochner
L² weak solution with these data. Its initial value, energy bound, and weak
equation come from `exists_symmetric_cauchy_l2`. Every competing Bochner class
satisfying the same `TimeTest`/H¹ identities equals its `MemLp.toLp` class.

The trace belongs to the displayed continuous representative. No point value
is assigned to the arbitrary measurable representative of a Bochner class. -/
theorem exists_symmetric_cauchy_l2_unique
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n))))
    (hA : ∀ j p q,
      ContinuousOn (fun t ↦ (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) (Icc a b))
    (hab : a < b)
    (hsym : ∀ t ∈ Icc a b, ∀ j p q, (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1) =
      (A t j q p : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1))
    {C L : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L) (hdiv : ∀ t ∈ Icc a b, coefficientDerivativeBound (A t) ≤ C)
    (hgrad : ∀ t ∈ Icc a b, coefficientGradientBound (A t) ≤ L) (x : H) (f : Lp H 2 ν) :
    ∃ (u : ℝ → H) (hu : MemLp u 2 ν),
      ContinuousOn u (Icc a b) ∧
      u a = x ∧
      (∀ t ∈ Icc a b, ‖u t‖ ^ 2 ≤
        (‖x‖ ^ 2 + ‖f‖ ^ 2) * Real.exp ((C + 1) * (t - a))) ∧
      (∀ (φ : V) (τ : TimeTest a b),
        Integrable (fun t ↦ transportTestFunctional (A t) φ (u t) * τ.toFun t) ν ∧
        -(∫ t, ⟪u t, transportBaseCLM φ⟫_ℝ * τ.derivFun t ∂ν) =
          (∫ t, transportTestFunctional (A t) φ (u t) * τ.toFun t ∂ν) +
            (∫ t, ⟪f t, transportBaseCLM φ⟫_ℝ * τ.toFun t ∂ν) +
              ⟪x, transportBaseCLM φ⟫_ℝ * τ.toFun a) ∧
      ∀ v : Lp H 2 ν,
        (∀ (φ : V) (τ : TimeTest a b),
          -(∫ t, ⟪v t, transportBaseCLM φ⟫_ℝ * τ.derivFun t ∂ν) =
            (∫ t, transportTestFunctional (A t) φ (v t) * τ.toFun t ∂ν) +
              (∫ t, ⟪f t, transportBaseCLM φ⟫_ℝ * τ.toFun t ∂ν) +
                ⟪x, transportBaseCLM φ⟫_ℝ * τ.toFun a) →
        v = hu.toLp u := by
  obtain ⟨u, hucont, hux, huenergy, huweak⟩ :=
    exists_symmetric_cauchy_l2 A hA hab hsym hC hL hdiv hgrad x f
  have hu : MemLp u 2 ν := memLp_restrict_Ioc_of_continuousOn hucont
  let U : Lp H 2 ν := hu.toLp u
  have hU : (U : ℝ → H) =ᵐ[ν] u := hu.coeFn_toLp
  have hUweak (φ : V) (τ : TimeTest a b) : -(∫ t, ⟪U t, transportBaseCLM φ⟫_ℝ * τ.derivFun t ∂ν) =
        (∫ t, transportTestFunctional (A t) φ (U t) * τ.toFun t ∂ν) +
          (∫ t, ⟪f t, transportBaseCLM φ⟫_ℝ * τ.toFun t ∂ν) +
            ⟪x, transportBaseCLM φ⟫_ℝ * τ.toFun a := by
    have htime : (∫ t, ⟪U t, transportBaseCLM φ⟫_ℝ * τ.derivFun t ∂ν) =
          ∫ t, ⟪u t, transportBaseCLM φ⟫_ℝ * τ.derivFun t ∂ν := by
      apply integral_congr_ae
      filter_upwards [hU] with t ht
      rw [ht]
    have htransport : (∫ t, transportTestFunctional (A t) φ (U t) * τ.toFun t ∂ν) =
          ∫ t, transportTestFunctional (A t) φ (u t) * τ.toFun t ∂ν := by
      apply integral_congr_ae
      filter_upwards [hU] with t ht
      rw [ht]
    rw [htime, htransport]
    exact (huweak φ τ).2
  refine ⟨u, hu, hucont, hux, huenergy, huweak, fun v hv ↦ ?_⟩
  exact eq_of_symmetric_transport_weak_equations A hA hab hsym hC hL hdiv hgrad v U f x hv hUweak

end PDE.Hyperbolic.FirstOrder
