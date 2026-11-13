/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Duhamel.TimeTruncation
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Replacing the retarded Gaussian on a localized source

A continuous kernel which agrees with the Gaussian after multiplication by
a compact source gives the same Duhamel integral. The time interval
can be fixed past the evaluation time if the source vanishes there at the
spatial evaluation point. Compactness gives the required Fubini integrability.
-/

@[expose] public section

open MeasureTheory Set
open scoped Interval

namespace HeatEquation

variable {n : ℕ}

/-- A continuous replacement of the retarded kernel on a compact source
represents the Duhamel integral. Kernel agreement is needed only where
the source is nonzero. The replacement used for interior regularity cuts off
the Gaussian near its singularity and at infinity. -/
theorem integral_kernel_eq_duhamel
    {K : Set (ℝ^n)} {a b t : ℝ} {R G : ℝ^n × ℝ → ℝ}
    (hat : a ≤ t) (htb : t ≤ b) (hK : IsCompact K)
    (hR : ContinuousOn R (univ ×ˢ Icc a b)) (hG : Continuous G)
    (hsupport : ∀ s ∈ Icc a b, ∀ y ∉ K, R (y, s) = 0)
    {x : ℝ^n} (hfuture : ∀ s ∈ Icc t b, R (x, s) = 0)
    (hkernel : ∀ q ∈ K ×ˢ Icc a b,
      R q * G ((x, t) - q) = R q *
        fundamentalSolutionHeat (x - q.1) (t - q.2)) :
    (∫ q in K ×ˢ Icc a b, R q * G ((x, t) - q)) =
      ∫ s in a..t, initialValueSolution (fun y ↦ R (y, s)) x (t - s) := by
  have hab := hat.trans htb
  have hI : IntegrableOn (fun q ↦ R q * G ((x, t) - q)) (K ×ˢ Icc a b) :=
    ((hR.mono (prod_mono_left (subset_univ K))).mul
      (hG.comp (continuous_const.sub continuous_id)).continuousOn).integrableOn_compact
        (hK.prod isCompact_Icc)
  have hprod : Integrable (fun q ↦ R q * G ((x, t) - q))
      ((volume.restrict K).prod (volume.restrict (Icc a b))) := by
    rwa [Measure.prod_restrict, ← Measure.volume_eq_prod]
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod_symm _ hprod,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  calc
    _ = ∫ s in a..b, initialValueSolution (fun y ↦ R (y, s)) x (t - s) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hab] at hs
      dsimp only
      calc
        _ = ∫ y in K, fundamentalSolutionHeat (x - y) (t - s) * R (y, s) := by
          apply setIntegral_congr_fun hK.measurableSet
          intro y hy
          exact (hkernel (y, s) ⟨hy, hs⟩).trans (mul_comm _ _)
        _ = ∫ y, fundamentalSolutionHeat (x - y) (t - s) * R (y, s) := by
          apply setIntegral_eq_integral_of_forall_compl_eq_zero
          intro y hy
          rw [hsupport s hs y hy, mul_zero]
        _ = _ := by
          by_cases hts : t - s ≤ 0
          · have hsFuture : s ∈ Icc t b := ⟨sub_nonpos.mp hts, hs.2⟩
            simp [initialValueSolution, fundamentalSolutionHeat, hts, hfuture s hsFuture]
          · simp only [initialValueSolution, ite_eq_right hts]
    _ = _ := integral_initialValueSolution_eq_of_future_source_zero
      hat htb hK hR hsupport hfuture

end HeatEquation
