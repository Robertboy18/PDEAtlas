/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Duhamel.OffSupport
public import PDE.Parabolic.Heat.Duhamel.Representation.CompactSupport

/-!
# Fixed source intervals for retarded heat potentials

Away from the spatial source, the retarded Gaussian integral over a fixed
closed time interval equals the Duhamel integral ending at the evaluation time.
The future part vanishes, including the zero-age slice. This permits a local
heat field to be represented by a function smooth across its terminal time.
-/

@[expose] public section

open MeasureTheory Set
open scoped Interval

namespace HeatEquation

variable {n : ℕ}

/-- Outside the support of the datum, its heat evolution is its Gaussian
integral on that support at every heat age, including nonpositive ages. -/
theorem initialValueSolution_eq_setIntegral_of_support
    {K : Set (ℝ^n)} {f : ℝ^n → ℝ}
    (hsupport : ∀ y ∉ K, f y = 0) {x : ℝ^n} (hx : x ∉ K) (t : ℝ) :
    initialValueSolution f x t =
      ∫ y in K, fundamentalSolutionHeat (x - y) t * f y := by
  by_cases ht : t ≤ 0
  · simp [initialValueSolution, fundamentalSolutionHeat, ht, hsupport x hx]
  · rw [initialValueSolution, ite_eq_right ht]
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    rw [hsupport y hy, mul_zero]

/-- The future part of a heat evolution integral vanishes when the source
vanishes at the spatial evaluation point during that future interval.
The compact source family supplies integrability up to both endpoints. -/
theorem integral_initialValueSolution_eq_of_future_source_zero
    {K : Set (ℝ^n)} {a b t : ℝ} {R : ℝ^n × ℝ → ℝ}
    (hat : a ≤ t) (htb : t ≤ b) (hK : IsCompact K)
    (hR : ContinuousOn R (univ ×ˢ Icc a b))
    (hsupport : ∀ s ∈ Icc a b, ∀ y ∉ K, R (y, s) = 0)
    {x : ℝ^n} (hfuture : ∀ s ∈ Icc t b, R (x, s) = 0) :
    (∫ s in a..b, initialValueSolution (fun y ↦ R (y, s)) x (t - s)) =
      ∫ s in a..t, initialValueSolution (fun y ↦ R (y, s)) x (t - s) := by
  have hcont : ContinuousOn (fun s ↦
      initialValueSolution (fun y ↦ R (y, s)) x (t - s)) (Icc a b) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hfamily := continuous_initialValueSolution_compact_family isCompact_Icc hK
      (u := fun s y ↦ R (y, s))
      (hR.comp continuous_swap.continuousOn (fun p hp ↦ ⟨hp.2, hp.1⟩)) hsupport
    exact hfamily.comp (continuous_id.prodMk (continuous_const.prodMk
      (continuous_const.sub continuous_subtype_val)))
  rw [← intervalIntegral.integral_add_adjacent_intervals
    ((hcont.mono (Icc_subset_Icc le_rfl htb)).intervalIntegrable_of_Icc hat)
    ((hcont.mono (Icc_subset_Icc hat le_rfl)).intervalIntegrable_of_Icc htb)]
  have htail : (∫ s in t..b,
      initialValueSolution (fun y ↦ R (y, s)) x (t - s)) = 0 := by
    calc
      _ = ∫ _ in t..b, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le htb] at hs
        exact (initialValueSolution_of_t_le_zero (fun y ↦ R (y, s)) x
          (sub_nonpos.mpr hs.1)).trans (hfuture s hs)
      _ = 0 := by simp
  rw [htail, add_zero]

/-- A continuous compactly supported source has the same retarded potential
whether integrated to the evaluation time or to any later fixed terminal time.
All interval integrability follows from the compact source family. -/
theorem heatPotential_eq_duhamel_of_notMem
    {K : Set (ℝ^n)} {a b t : ℝ} {R : ℝ^n × ℝ → ℝ}
    (hat : a ≤ t) (htb : t ≤ b) (hK : IsCompact K)
    (hR : ContinuousOn R (univ ×ˢ Icc a b))
    (hsupport : ∀ s ∈ Icc a b, ∀ y ∉ K, R (y, s) = 0)
    {x : ℝ^n} (hx : x ∉ K) :
    (∫ q in K ×ˢ Icc a b,
      R q * fundamentalSolutionHeat (x - q.1) (t - q.2)) =
      ∫ s in a..t, initialValueSolution (fun y ↦ R (y, s)) x (t - s) := by
  have hab := hat.trans htb
  rw [heatPotential_eq_intervalIntegral_of_notMem hab hK
    (hR.mono (prod_mono_left (subset_univ K))) hx t]
  calc
    _ = ∫ s in a..b, initialValueSolution (fun y ↦ R (y, s)) x (t - s) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hab] at hs
      exact (initialValueSolution_eq_setIntegral_of_support (hsupport s hs) hx (t - s)).symm
    _ = _ := integral_initialValueSolution_eq_of_future_source_zero hat htb hK hR
      hsupport (fun s hs ↦ hsupport s ⟨hat.trans hs.1, hs.2⟩ x hx)

end HeatEquation
