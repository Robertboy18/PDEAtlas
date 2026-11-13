/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.CompactSecondDerivative
import PDE.FDeriv.PartialDeriv.Support

/-!
# Testing a local energy balance

A classical energy equation holding near the support of a compact scalar
test gives its distributional energy identity. The time derivative and
spatial derivatives transfer to the test. Only the dissipation pairing needs
a separate integrability hypothesis; regularity and compact support supply
integrability of the differential terms.

The coordinate directions are explicit, so this theorem applies to a time
coordinate and any chosen collection of spatial coordinates without depending
on a fluid model.
-/

@[expose] public section

namespace PDE.Analysis

open EuclideanSpace MeasureTheory

set_option linter.missingDocs true

/-- A continuous compactly supported factor times a function continuous on its support is
integrable. -/
private theorem integrable_mul_of_continuousAt {m : ℕ} {g f : ℝ^m → ℝ} (hg : Continuous g)
    (hc : HasCompactSupport g) (hf : ∀ x ∈ tsupport g, ContinuousAt f x) :
    Integrable (fun x ↦ g x * f x) :=
  hc.integrable_of_continuousOn_tsupport
    (hg.continuousOn.mul fun x hx ↦ (hf x hx).continuousWithinAt)
    fun x hx ↦ by rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]

/-- Transfer the differential terms of an energy equation onto a compact `C²` test.
The energy and flux need regularity only near the support of that test. -/
theorem integral_tested_energy_balance {m k : ℕ}
    (time : Fin m) (direction : Fin k → Fin m) (ν : ℝ)
    {φ e d q : ℝ^m → ℝ} {F : Fin k → ℝ^m → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (he : ∀ x ∈ tsupport φ, ContDiffAt ℝ 2 e x)
    (hF : ∀ j, ∀ x ∈ tsupport φ, ContDiffAt ℝ 1 (F j) x)
    (hd : Integrable (fun x ↦ φ x * d x))
    (hbalance : ∀ x ∈ tsupport φ,
      (∂[time] e) x - ν * (∑ j : Fin k, (∂[direction j] (∂[direction j] e)) x) +
        d x + (∑ j : Fin k, (∂[direction j] (F j)) x) = q x) :
    (∫ x, φ x * d x) =
      (∫ x, (∂[time] φ) x * e x) +
        ν * (∫ x, (∑ j : Fin k, (∂[direction j] (∂[direction j] φ)) x) * e x) +
        (∫ x, ∑ j : Fin k, (∂[direction j] φ) x * F j x) +
        ∫ x, φ x * q x := by
  have htime : Integrable (fun x ↦ φ x * (∂[time] e) x) :=
    integrable_mul_of_continuousAt hφ.continuous hc fun x hx ↦
      ((he x hx).partialDeriv time (k := 1) (by norm_num)).continuousAt
  have hsecond (j : Fin k) :
      Integrable (fun x ↦ φ x * (∂[direction j] (∂[direction j] e)) x) :=
    integrable_mul_of_continuousAt hφ.continuous hc fun x hx ↦
      (((he x hx).partialDeriv (direction j) (k := 1) (by norm_num)).partialDeriv
        (direction j) (k := 0) (by norm_num)).continuousAt
  have hflux (j : Fin k) : Integrable (fun x ↦ φ x * (∂[direction j] (F j)) x) :=
    integrable_mul_of_continuousAt hφ.continuous hc fun x hx ↦
      ((hF j x hx).partialDeriv (direction j) (k := 0) (by norm_num)).continuousAt
  have hsecondTest (j : Fin k) :
      Integrable (fun x ↦ (∂[direction j] (∂[direction j] φ)) x * e x) :=
    integrable_mul_of_continuousAt ((hφ.partialDeriv (direction j) (k := 1)
        (by norm_num)).partialDeriv (direction j) (k := 0) (by norm_num)).continuous
      ((hc.partialDeriv _).partialDeriv _) fun x hx ↦ (he x (tsupport_partialDeriv_subset _
        (tsupport_partialDeriv_subset _ hx))).continuousAt
  have hfluxTest (j : Fin k) : Integrable (fun x ↦ (∂[direction j] φ) x * F j x) :=
    integrable_mul_of_continuousAt
      (hφ.partialDeriv (direction j) (k := 1) (by norm_num)).continuous (hc.partialDeriv _)
      fun x hx ↦ (hF j x (tsupport_partialDeriv_subset _ hx)).continuousAt
  have hs := integrable_finsetSum Finset.univ (fun j _ ↦ hsecond j)
  have hf := integrable_finsetSum Finset.univ (fun j _ ↦ hflux j)
  have htest : (∫ x, φ x * q x) =
      (∫ x, φ x * (∂[time] e) x) -
        ν * (∫ x, ∑ j : Fin k, φ x * (∂[direction j] (∂[direction j] e)) x) +
        (∫ x, φ x * d x) +
        ∫ x, ∑ j : Fin k, φ x * (∂[direction j] (F j)) x := by
    calc
      _ = ∫ x, (φ x * (∂[time] e) x -
          ν * (∑ j : Fin k, φ x * (∂[direction j] (∂[direction j] e)) x) +
          φ x * d x) + (∑ j : Fin k, φ x * (∂[direction j] (F j)) x) := by
        refine integral_congr_ae (.of_forall fun x ↦ ?_)
        by_cases hx : x ∈ tsupport φ
        · simp only [← Finset.mul_sum]
          linear_combination -congrArg (φ x * ·) (hbalance x hx)
        · simp [image_eq_zero_of_notMem_tsupport hx]
      _ = _ := by
        rw [integral_add, integral_add, integral_sub, integral_const_mul]
        exacts [htime, hs.const_mul ν, htime.sub (hs.const_mul ν), hd,
          (htime.sub (hs.const_mul ν)).add hd, hf]
  rw [integral_mul_partialDeriv_eq_neg_of_contDiffAt time (hφ.of_le (by norm_num))
    (fun x hx ↦ (he x hx).of_le (by norm_num)) hc,
    integral_finsetSum _ (fun j _ ↦ hsecond j),
    integral_finsetSum _ (fun j _ ↦ hflux j)] at htest
  simp_rw [integral_mul_secondPartialDeriv_eq_of_contDiffAt _ _ hφ he hc,
    integral_mul_partialDeriv_eq_neg_of_contDiffAt _ (hφ.of_le (by norm_num))
      (fun x hx ↦ hF _ x hx) hc] at htest
  rw [← integral_finsetSum _ (fun j _ ↦ hsecondTest j),
    Finset.sum_neg_distrib, ← integral_finsetSum _ (fun j _ ↦ hfluxTest j)] at htest
  simp only [Finset.sum_mul]
  linarith

end PDE.Analysis
