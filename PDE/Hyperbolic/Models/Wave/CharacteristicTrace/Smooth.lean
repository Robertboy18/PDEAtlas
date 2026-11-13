/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.CharacteristicTrace.Differential
import PDE.Analysis.Calculus.Gradient
import PDE.Analysis.InnerProductSpace.Calculus.Normalization
import PDE.Analysis.Integration.CompactByParts
import PDE.FDeriv.PartialDeriv.Regularity
import PDE.FDeriv.PartialDeriv.Support

/-!
# Weak characteristic traces of smooth waves

Compactly supported tests turn the characteristic-current identity into a weak
trace equation. Only C² germs at the cone points above the test support are
needed; the test support avoids the vertex.
-/

@[expose] public noncomputable section

open PDE PDE.Common PDE.Analysis Filter MeasureTheory Set
open scoped Topology RealInnerProductSpace Gradient

namespace WaveEquation

variable {n : ℕ}

/-- The weak characteristic trace equation for a field that is C² near the
compact test support. The test avoids the tip. -/
theorem integral_characteristicTrace_of_contDiffAt {u : ℝ^(n + 1) → ℝ} (c : ℝ^n) (T : ℝ)
    {φ : ℝ^n → ℝ} (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) (haway : ∀ x ∈ tsupport φ, x ≠ c)
    (hu : ∀ x ∈ tsupport φ, ContDiffAt ℝ 2 u (backwardConeGraph c T x)) :
    (∫ x, u (backwardConeGraph c T x) * PDE.laplacian φ x) -
        2 * (∫ x, ∂[0] u (backwardConeGraph c T x) *
          ⟪NormedSpace.normalize (x - c), ∇ φ x⟫) -
        ((n : ℝ) - 1) *
          (∫ x, (∂[0] u (backwardConeGraph c T x) / ‖x - c‖) * φ x) =
      -(∫ x, waveOperator u (backwardConeGraph c T x) * φ x) := by
  let q := u ∘ backwardConeGraph c T
  let w := (∂[0] u) ∘ backwardConeGraph c T
  let J := characteristicCurrent u c T
  have hq (x : ℝ^n) (hx : x ∈ tsupport φ) : ContDiffAt ℝ 1 q x :=
    ((hu x hx).of_le (by norm_num)).comp x ((contDiffOn_backwardConeGraph c T).contDiffAt
      (isClosed_singleton.isOpen_compl.mem_nhds (haway x hx)))
  have hw : ContinuousOn w (tsupport φ) := fun x hx ↦
    (((hu x hx).partialDeriv 0 (k := 1) (by norm_num)).continuousAt.comp
      (hasFDerivAt_backwardConeGraph c T (haway x hx)).continuousAt).continuousWithinAt
  have hJ (i : Fin n) (x : ℝ^n) (hx : x ∈ tsupport φ) : ContDiffAt ℝ 1 (fun y ↦ J y i) x :=
    contDiffAt_characteristicCurrent_coord c T (haway x hx) (hu x hx) i
  have hp (i : Fin n) : ContDiff ℝ 1 (∂[i] φ) := hφ.partialDeriv i (by norm_num)
  have hqq (i : Fin n) : Integrable (fun x ↦ ∂[i] φ x * ∂[i] q x) :=
    hc.integrable_of_continuousOn_tsupport ((hp i).continuous.continuousOn.mul
      (fun x hx ↦ ((hq x hx).continuousAt_partialDeriv i).continuousWithinAt))
      fun x hx ↦ by simp [partialDeriv_eq_zero_of_notMem_tsupport i hx]
  have hqc : ContinuousOn q (tsupport φ) := fun x hx ↦ (hq x hx).continuousAt.continuousWithinAt
  have hqφ (i : Fin n) : Integrable (fun x ↦ q x * ∂[i] (∂[i] φ) x) :=
    hc.integrable_of_continuousOn_tsupport (hqc.mul ((hp i).continuous_partialDeriv i).continuousOn)
      fun x hx ↦ by
        rw [partialDeriv_eq_zero_of_notMem_tsupport i
          (fun h ↦ hx (tsupport_partialDeriv_subset i h)), mul_zero]
  have hjφ (i : Fin n) : Integrable (fun x ↦ ∂[i] φ x * J x i) :=
    hc.integrable_of_continuousOn_tsupport ((hp i).continuous.continuousOn.mul
      (fun x hx ↦ (hJ i x hx).continuousAt.continuousWithinAt))
      fun x hx ↦ by simp [partialDeriv_eq_zero_of_notMem_tsupport i hx]
  have hφj (i : Fin n) : Integrable (fun x ↦ φ x * ∂[i] (fun y ↦ J y i) x) :=
    hc.integrable_of_continuousOn_tsupport (hφ.continuous.continuousOn.mul
      (fun x hx ↦ ((hJ i x hx).continuousAt_partialDeriv i).continuousWithinAt))
      fun x hx ↦ by simp [image_eq_zero_of_notMem_tsupport hx]
  have hgreen : (∫ x, q x * PDE.laplacian φ x) =
      -(∫ x, ∑ i : Fin n, ∂[i] φ x * ∂[i] q x) := by
    simp only [PDE.laplacian, Finset.mul_sum]
    rw [integral_finsetSum _ (fun i _ ↦ hqφ i),
      integral_finsetSum _ (fun i _ ↦ hqq i), ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simpa only [mul_comm, neg_neg] using (congrArg Neg.neg
      (PDE.Analysis.integral_mul_partialDeriv_eq_neg_of_contDiffAt i (hp i)
        (fun x hx ↦ hq x (tsupport_partialDeriv_subset i hx)) (hc.partialDeriv i))).symm
  have hdiv : (∫ x, φ x * ∇· J x) =
      -(∫ x, ∑ i : Fin n, ∂[i] φ x * J x i) := by
    simp only [PDE.divergence, Finset.mul_sum]
    rw [integral_finsetSum _ (fun i _ ↦ hφj i),
      integral_finsetSum _ (fun i _ ↦ hjφ i), ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ ↦
      PDE.Analysis.integral_mul_partialDeriv_eq_neg_of_contDiffAt i
        (hφ.of_le (by norm_num)) (hJ i) hc
  have hradc : ContinuousOn (fun x : ℝ^n ↦ NormedSpace.normalize (x - c))
      (tsupport φ) := by
    intro x hx
    exact ((NormedSpace.contDiffAt_normalize (k := 1) (sub_ne_zero.mpr (haway x hx))).comp x
      (contDiffAt_id.sub contDiffAt_const)).continuousAt.continuousWithinAt
  have hgrad : Continuous (∇ φ) := continuous_gradient_of_contDiff (hφ.of_le (by norm_num))
  have hR : Integrable (fun x ↦ w x * ⟪NormedSpace.normalize (x - c), ∇ φ x⟫) := by
    apply hc.integrable_of_continuousOn_tsupport (hw.mul (hradc.inner hgrad.continuousOn))
    intro x hx
    have hgzero : ∇ φ x = 0 := by
      ext i
      simp [gradient_apply_eq_partialDeriv, partialDeriv_eq_zero_of_notMem_tsupport i hx]
    change w x * ⟪NormedSpace.normalize (x - c), ∇ φ x⟫ = 0
    rw [hgzero, inner_zero_right, mul_zero]
  have hcur : (∫ x, ∑ i : Fin n, ∂[i] φ x * J x i) = (∫ x, ∑ i : Fin n, ∂[i] φ x * ∂[i] q x) +
        2 * (∫ x, w x * ⟪NormedSpace.normalize (x - c), ∇ φ x⟫) := by
    rw [← integral_const_mul, ← integral_add (integrable_finsetSum _ (fun i _ ↦ hqq i))
      (hR.const_mul 2)]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x ∈ tsupport φ
    · have he := characteristicCurrent_eq_gradient c T (haway x hx)
        ((hu x hx).differentiableAt (by norm_num))
      have hinner (v : ℝ^n) : ⟪∇ φ x, v⟫ = ∑ i : Fin n, ∂[i] φ x * v i := by
        rw [inner_gradient_left, fderiv_apply_eq_sum_partialDeriv_mul]
      rw [← hinner, show J x = _ from he, inner_add_right, inner_smul_right,
        real_inner_comm (∇ φ x), hinner]
      simp only [gradient_apply_eq_partialDeriv]
      dsimp only [q, w, Function.comp_apply]
      ring
    · simp [partialDeriv_eq_zero_of_notMem_tsupport _ hx,
        show ∇ φ x = 0 from by
          ext i
          simp [gradient_apply_eq_partialDeriv, partialDeriv_eq_zero_of_notMem_tsupport i hx]]
  have hD : Integrable (fun x ↦ (w x / ‖x - c‖) * φ x) := hc.integrable_of_continuousOn_tsupport
      ((hw.div (continuous_norm.comp (continuous_id.sub continuous_const)).continuousOn
        (fun x hx ↦ norm_ne_zero_iff.mpr (sub_ne_zero.mpr (haway x hx)))).mul
          hφ.continuous.continuousOn) fun x hx ↦ by simp [image_eq_zero_of_notMem_tsupport hx]
  have hWc : ContinuousOn (fun x ↦ waveOperator u (backwardConeGraph c T x))
      (tsupport φ) := fun x hx ↦ by
    have hs (i j : Fin (n + 1)) : ContinuousAt (∂[i] (∂[j] u)) (backwardConeGraph c T x) :=
      ((hu x hx).partialDeriv j (k := 1) (by norm_num)).continuousAt_partialDeriv i
    have hsum : ContinuousAt (fun z : ℝ^(n + 1) ↦ ∑ i : Fin n, ∂[i.succ] (∂[i.succ] u) z)
        (backwardConeGraph c T x) := tendsto_finsetSum _ (fun (i : Fin n) _ ↦ hs i.succ i.succ)
    exact ((hs 0 0).sub hsum).comp
      (hasFDerivAt_backwardConeGraph c T (haway x hx)).continuousAt |>.continuousWithinAt
  have hW : Integrable (fun x ↦ waveOperator u (backwardConeGraph c T x) * φ x) :=
    hc.integrable_of_continuousOn_tsupport (hWc.mul hφ.continuous.continuousOn)
      fun x hx ↦ by simp [image_eq_zero_of_notMem_tsupport hx]
  have hdivwave : (∫ x, φ x * ∇· J x) = -(∫ x, waveOperator u (backwardConeGraph c T x) * φ x) +
        ((n : ℝ) - 1) * (∫ x, (w x / ‖x - c‖) * φ x) := by
    rw [← integral_neg, ← integral_const_mul,
      ← integral_add (f := fun x ↦ -(waveOperator u (backwardConeGraph c T x) * φ x))
        (g := fun x ↦ ((n : ℝ) - 1) * ((w x / ‖x - c‖) * φ x)) hW.neg (hD.const_mul _)]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x ∈ tsupport φ
    · rw [show ∇· J x = _ from divergence_characteristicCurrent c T (haway x hx) (hu x hx)]
      dsimp only [w, Function.comp_apply]
      ring
    · simp [image_eq_zero_of_notMem_tsupport hx]
  rw [hcur] at hdiv
  change (∫ x, q x * PDE.laplacian φ x) - 2 * (∫ x, w x * _) -
    ((n : ℝ) - 1) * (∫ x, (w x / ‖x - c‖) * φ x) = _
  linarith [hgreen, hdiv, hdivwave]

end WaveEquation
