/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Core.Gronwall
import CAS.ExactTactic

/-!
# Gronwall estimates with a retarded exponential

The semigroup growth rate is removed by an integrating factor before applying
integral Gronwall. This retains linear dependence on the spatial weight
parameter in the final exponential, as required for finite propagation.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet

/-- A retarded exponential bound with integrable forcing has a single
exponential growth rate, equal to the sum of the two coefficients. -/
theorem le_exp_mul_integral_of_retarded_bound {e g : ℝ → ℝ} {T ω K : ℝ} (hT : 0 ≤ T) (hω : 0 ≤ ω)
    (hK : 0 ≤ K) (he : ContinuousOn e (Icc 0 T)) (hg : IntervalIntegrable g volume 0 T)
    (hg0 : ∀ t ∈ Icc 0 T, 0 ≤ g t)
    (hb : ∀ t ∈ Icc 0 T, e t ≤ ∫ s in (0 : ℝ)..t, Real.exp (ω * (t - s)) * (K * e s + g s)) :
    ∀ t ∈ Icc 0 T, e t ≤ Real.exp ((ω + K) * t) * ∫ s in (0 : ℝ)..T, g s := by
  let E : ℝ → ℝ := fun t ↦ Real.exp (-ω * t) * e t
  have hc : Continuous (fun t : ℝ ↦ Real.exp (-ω * t)) := by fun_prop
  have hE : ContinuousOn E (Icc 0 T) := hc.continuousOn.mul he
  have hineq (t : ℝ) (ht : t ∈ Icc 0 T) :
      E t ≤ (∫ s in (0 : ℝ)..T, g s) + K * ∫ s in (0 : ℝ)..t, E s := by
    have hsub : Icc (0 : ℝ) t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
    have hgi : IntervalIntegrable g volume 0 t := hg.mono_set (by
      simpa only [uIcc_of_le ht.1, uIcc_of_le hT] using hsub)
    have hEi : IntervalIntegrable E volume 0 t := (hE.mono hsub).intervalIntegrable_of_Icc ht.1
    have hweighted := hgi.continuousOn_mul hc.continuousOn
    have hkernel (s : ℝ) : Real.exp (-ω * t) * (Real.exp (ω * (t - s)) * (K * e s + g s)) =
          K * E s + Real.exp (-ω * s) * g s := by
      rw [← mul_assoc, ← Real.exp_add]
      have hex : -ω * t + ω * (t - s) = -ω * s := by cas
      rw [hex]
      dsimp only [E]
      ring
    have h := mul_le_mul_of_nonneg_left (hb t ht) (Real.exp_pos (-ω * t)).le
    rw [← intervalIntegral.integral_const_mul] at h
    simp_rw [hkernel] at h
    rw [intervalIntegral.integral_add (hEi.const_mul K) hweighted,
      intervalIntegral.integral_const_mul] at h
    have hsmall : (∫ s in (0 : ℝ)..t, Real.exp (-ω * s) * g s) ≤
        ∫ s in (0 : ℝ)..t, g s := by
      refine intervalIntegral.integral_mono_on ht.1 hweighted hgi fun s hs ↦ ?_
      exact mul_le_of_le_one_left (hg0 s (hsub hs))
        (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hω) hs.1))
    have hpref' : (∫ s in (0 : ℝ)..t, g s) ≤ ∫ s in (0 : ℝ)..T, g s := by
      apply intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2 _ hg
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact hg0 s (Ioc_subset_Icc_self hs)
    change E t ≤ _ at h
    linarith only [h, hsmall, hpref']
  have hbound := PDE.Analysis.Evolution.le_mul_exp_of_le_const_add_mul_intervalIntegral
    hE hK hineq
  intro t ht
  have h := mul_le_mul_of_nonneg_left (hbound t ht) (Real.exp_pos (ω * t)).le
  have hleft : Real.exp (ω * t) * E t = e t := by
    dsimp only [E]
    rw [← mul_assoc, ← Real.exp_add]
    simp
  have hright : Real.exp (ω * t) * ((∫ s in (0 : ℝ)..T, g s) * Real.exp (K * (t - 0))) =
        Real.exp ((ω + K) * t) * ∫ s in (0 : ℝ)..T, g s := by
    rw [sub_zero, mul_comm (∫ s in (0 : ℝ)..T, g s) (Real.exp (K * t)), ← mul_assoc, ← Real.exp_add]
    congr 2
    cas
  rwa [hleft, hright] at h

end PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet
