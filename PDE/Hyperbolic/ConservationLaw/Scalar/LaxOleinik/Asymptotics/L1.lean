/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.LaxOleinik.Asymptotics.L1.SmallTime
public import PDE.Hyperbolic.ConservationLaw.Scalar.LaxOleinik.Asymptotics.L1.LargeTime

/-!
# Quantitative scalar N-wave asymptotics

For the Lax–Oleinik solution with bounded, essentially compactly supported datum,
positive lobe parameters give the N-wave approximation at rate `t⁻¹ᐟ²`. The
large-time comparison and the separate bounded-time estimate give one constant for all
positive times. The datum need not be continuous, and the flux drift need not vanish.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.4.5(b), equations (63)-(67) and Theorem 6.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set MeasureTheory PDE.Analysis PDE.Common HamiltonJacobi.HopfLax
open scoped ENNReal NNReal

namespace PDE.Hyperbolic.ConservationLaw.LaxOleinik

/-- Quantitative N-wave asymptotics for the Lax–Oleinik solution. A single
constant works at every positive time, and each error slice is integrable. The lobe
parameters come from the datum itself. The flux needs only C³ regularity and a positive lower
Hessian bound; its drift is arbitrary.

This is Evans, §3.4.5, Theorem 6, with bounded support understood almost everywhere. -/
theorem exists_integral_abs_sub_nWave_le {F g : ℝ → ℝ} (hF : ContDiff ℝ 3 F) {θ : ℝ} (hθ : 0 < θ)
    (hlower : ∀ r, θ ≤ deriv (deriv F) r) (hzero : F 0 = 0) (hg : MemLp g ∞ volume) {R : ℝ}
    (hsupport : ∀ᵐ y ∂volume, y ∉ Icc (-R) R → g y = 0) (hp : 0 < negativeLobeMass g)
    (hq : 0 < positiveLobeMass g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → Integrable (fun x ↦ |solution F g !₂[t, x] - nWave F g t x|)
      volume ∧ (∫ x, |solution F g !₂[t, x] - nWave F g t x|) ≤ C / √t := by
  have hg1 : Integrable g volume := by
    have hgi : IntegrableOn g (Icc (-R) R) volume :=
      (hg.locallyIntegrable le_top).integrableOn_isCompact isCompact_Icc
    exact hgi.integrable_of_ae_notMem_eq_zero hsupport
  have hR : 0 ≤ max R 0 := le_max_right _ _
  have hsupp : ∀ᵐ y ∂volume, y ∉ Icc (-(max R 0)) (max R 0) → g y = 0 := by
    filter_upwards [hsupport] with y hy hout
    refine hy fun hmem ↦ ?_
    apply hout
    exact ⟨(neg_le_neg (le_max_left R 0)).trans hmem.1, hmem.2.trans (le_max_left R 0)⟩
  obtain ⟨S, hS, C₁, hC₁, hlarge⟩ :=
    exists_integral_abs_sub_nWave_le_of_sq_time_ge hF hθ hlower hzero hg hg1 hR hsupp hp hq
  have hF2 : ContDiff ℝ 2 F := hF.of_le (by norm_num)
  obtain ⟨C₀, hC₀, hsmall⟩ := exists_integral_abs_sub_nWave_le_of_sq_time_le hF2 hθ hlower hzero
      hg hg1 hR hsupp hS
  refine ⟨max C₀ C₁, hC₀.trans (le_max_left _ _), fun t ht ↦ ⟨?_, ?_⟩⟩
  · exact integrable_abs_solution_sub_nWave_of_ae_support_Icc hF2 hθ hlower hzero hg hsupport ht
  · have hs : 0 < √t := Real.sqrt_pos.mpr ht
    rcases le_total (√t) S with h | h
    · have hb := hsmall (√t) hs h
      rw [Real.sq_sqrt ht.le] at hb
      exact hb.trans (div_le_div_of_nonneg_right (le_max_left _ _) hs.le)
    · have hb := hlarge (√t) h
      rw [Real.sq_sqrt ht.le] at hb
      exact hb.trans (div_le_div_of_nonneg_right (le_max_right _ _) hs.le)

end PDE.Hyperbolic.ConservationLaw.LaxOleinik
