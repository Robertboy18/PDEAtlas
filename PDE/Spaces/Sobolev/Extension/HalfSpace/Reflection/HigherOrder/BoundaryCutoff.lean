/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.HalfSpace.FirstOrder.NormalDerivative.BoundaryLimit

/-!
# Removing boundary cutoffs from weak derivative tests

A compactly supported smooth test may meet the boundary of the upper half-space.
The weak integration identity still holds if the test vanishes there in the normal
case. Tangential differentiation requires no boundary condition, since the normal
cutoff has zero tangential derivative.

The normal case uses the boundary-strip dominated-convergence estimate from the
first-order reflection proof. Only local integrability of the `L^p` coordinates
enters, so the statement includes `p = 1` and `p = ∞`.
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

namespace SobolevSpace.GraphSpace.HigherOrderReflection

open Set MeasureTheory TopologicalSpace Filter
open SobolevSpace.Extension.GraphSpace.HalfSpace
open scoped ENNReal Distributions Topology

variable (n : ℕ) [Fact (0 < n)] (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- Weak integration by parts admits tests meeting the flat boundary if their normal
boundary contribution vanishes. No vanishing condition is needed tangentially. -/
theorem integral_mul_partialDeriv_eq_neg_of_boundary
    (i : Fin n) (u du : DerivLp n p ℝ^n₊)
    (hweak : HasWeakDerivativeOn ℝ^n₊ [i] (u : ℝ^n → ℝ) (du : ℝ^n → ℝ))
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hψ : i = PDE.Common.lastIndex (n := n) →
      ∀ x : ℝ^n, x (PDE.Common.lastIndex (n := n)) = 0 → ψ x = 0) :
    (∫ x, u x * (∂[i] ψ.toFun) x ∂domainMeasure n ℝ^n₊) =
      -(∫ x, du x * ψ x ∂domainMeasure n ℝ^n₊) := by
  let ψi : 𝓓((⊤ : Opens (ℝ^n)), ℝ) :=
    _root_.TestFunction.lineDerivCLM ℝ (EuclideanSpace.single i (1 : ℝ)) ψ
  have hψi (x : ℝ^n) : ψi x = (∂[i] ψ.toFun) x :=
    testFunction_lineDerivCLM_apply ψ _ x
  have hInt (v : DerivLp n p ℝ^n₊) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
      Integrable (fun x ↦ v x * φ x) (domainMeasure n ℝ^n₊) :=
    integrable_mul_of_memLp n p (Lp.memLp v) φ.contDiff.continuous φ.hasCompactSupport
  have hErr :
      Tendsto (fun m ↦ ∫ x, u x *
        (∂[i] (HalfSpace.cutoffAway (n := n) (δSeq m))) x * ψ x
          ∂domainMeasure n ℝ^n₊) atTop (𝓝 (0 : ℝ)) := by
    by_cases hi : i = PDE.Common.lastIndex (n := n)
    · subst i
      exact tendsto_integral_mul_cutoff_deriv_of_zero_on_boundary n p u ψ (hψ rfl)
    · have hz (m : ℕ) (x : ℝ^n) :
          (∂[i] (HalfSpace.cutoffAway (n := n) (δSeq m))) x = 0 :=
        partialDeriv_cutoffAway_of_ne_last n (δSeq_pos m).ne' i hi x
      simpa only [hz, mul_zero, zero_mul, integral_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0))
  have hEq (m : ℕ) :
      (∫ x, (u x * ψi x) * HalfSpace.cutoffAway (n := n) (δSeq m) x
        ∂domainMeasure n ℝ^n₊) +
      (∫ x, u x * (∂[i] (HalfSpace.cutoffAway (n := n) (δSeq m))) x * ψ x
        ∂domainMeasure n ℝ^n₊) =
      -(∫ x, (du x * ψ x) * HalfSpace.cutoffAway (n := n) (δSeq m) x
        ∂domainMeasure n ℝ^n₊) := by
    have hw := hweak (cutoffMul n (δSeq m) ψ)
      (tsupport_cutoffMul_subset_upper n (δSeq_pos m) ψ)
    have hder (x : ℝ^n) :
        iteratedPartialDeriv [i] (cutoffMul n (δSeq m) ψ).toFun x =
          HalfSpace.cutoffAway (n := n) (δSeq m) x * ψi x +
            (∂[i] (HalfSpace.cutoffAway (n := n) (δSeq m))) x * ψ x := by
      change (∂[i]
        (fun y ↦ HalfSpace.cutoffAway (n := n) (δSeq m) y * ψ y)) x = _
      rw [PDE.partialDeriv_mul (differentiableAt_cutoffAway n (δSeq m) x)
        (ψ.contDiff.differentiable (by simp)).differentiableAt, hψi]
      exact add_comm _ _
    have hA := hInt u (cutoffMul n (δSeq m) ψi)
    have hB := integrable_mul_of_memLp n p (Lp.memLp u)
      ((continuous_partialDeriv_cutoffAway n (δSeq m) i).mul ψ.contDiff.continuous)
      ψ.hasCompactSupport.mul_left
    have hA' : Integrable (fun x ↦ (u x * ψi x) *
        HalfSpace.cutoffAway (n := n) (δSeq m) x) (domainMeasure n ℝ^n₊) := by
      change Integrable (fun x ↦ u x *
        (HalfSpace.cutoffAway (n := n) (δSeq m) x * ψi x)) _ at hA
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hA
    have hB' : Integrable (fun x ↦ u x *
        (∂[i] (HalfSpace.cutoffAway (n := n) (δSeq m))) x * ψ x)
        (domainMeasure n ℝ^n₊) := by
      simpa only [Pi.mul_apply, mul_assoc] using hB
    rw [← integral_add hA' hB']
    convert hw using 1
    · apply integral_congr_ae
      filter_upwards with x
      rw [hder]
      ring
    · simp only [List.length_singleton, pow_one, neg_one_mul]
      congr 1
      apply integral_congr_ae
      filter_upwards with x
      change du x * ψ x * HalfSpace.cutoffAway (n := n) (δSeq m) x =
        du x * (HalfSpace.cutoffAway (n := n) (δSeq m) x * ψ x)
      ring
  have hL := (tendsto_integral_mul_cutoff n (hInt u ψi)).add hErr
  have hR := (tendsto_integral_mul_cutoff n (hInt du ψ)).neg
  have hlim := tendsto_nhds_unique hL (hR.congr (fun m ↦ (hEq m).symm))
  simpa only [add_zero, hψi] using hlim

end SobolevSpace.GraphSpace.HigherOrderReflection
