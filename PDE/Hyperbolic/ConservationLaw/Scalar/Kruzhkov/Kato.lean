/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.Kruzhkov.DiagonalTest
public import PDE.Hyperbolic.ConservationLaw.Scalar.Kruzhkov.DiagonalLimit
import PDE.DistributionTheory.TestFunction

/-!
# The scalar Kato inequality

The doubled entropy inequality is tested against a shrinking spacetime kernel. On the
compact support of the base test, an integrable localization of the second solution
controls the diagonal error. Strong `L¹` translation continuity makes this error vanish.

The resulting inequality is (49) of Evans, §11.4.3, at the end of step 3 of the proof of
Theorem 3, with `a = |u - ũ|` and `b = sgn(u - ũ)(F(u) - F(ũ))`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.4.3, proof of Theorem 3, step 3, equations (46)-(49).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open PDE.Common SobolevSpace.Approximation
open scoped Distributions Topology

namespace PDE.Hyperbolic.ConservationLaw.Scalar

/-- The distributional entropy comparison of two scalar states at the same point. -/
def katoWeakIntegrand (flux : ℝ → ℝ) (u v : ℝ^2 → ℝ)
    {U : Opens ℝ^2} (φ : 𝓓^{1}(U, ℝ)) (x : ℝ^2) : ℝ :=
  |u x - v x| * (∂[0] (φ : ℝ^2 → ℝ)) x +
    kruzhkovFlux flux (v x) (u x) * (∂[1] (φ : ℝ^2 → ℝ)) x

/-- The two-state entropy flux is locally integrable whenever the states and their
physical fluxes are locally integrable. -/
theorem locallyIntegrableOn_kruzhkovFlux {flux : ℝ → ℝ} (hf : Measurable flux) {U : Opens ℝ^2}
    {u v : ℝ^2 → ℝ} (hu : LocallyIntegrableOn u U volume) (hv : LocallyIntegrableOn v U volume)
    (hfu : LocallyIntegrableOn (flux ∘ u) U volume)
    (hfv : LocallyIntegrableOn (flux ∘ v) U volume) :
    LocallyIntegrableOn (fun x ↦ kruzhkovFlux flux (v x) (u x)) U volume := by
  refine (locallyIntegrableOn_iff U.isOpen.isLocallyClosed).2 fun K hKU hK ↦ ?_
  have hum := (hu.integrableOn_compact_subset hKU hK).aestronglyMeasurable
  have hvm := (hv.integrableOn_compact_subset hKU hK).aestronglyMeasurable
  have hm := ((measurable_kruzhkovFlux hf).comp_aemeasurable
    (hvm.prodMk hum).aemeasurable).aestronglyMeasurable
  exact ((hfu.integrableOn_compact_subset hKU hK).sub
    (hfv.integrableOn_compact_subset hKU hK)).norm.mono' hm
      (Eventually.of_forall fun x ↦ norm_kruzhkovFlux_le flux (v x) (u x))

/-- The Kato integrand is integrable under the weak-solution integrability assumptions. -/
theorem IsWeakSolution.integrable_katoWeakIntegrand {flux : ℝ → ℝ} {U : Opens ℝ^2} {u v : ℝ^2 → ℝ}
    (hu : IsWeakSolution flux U u) (hv : IsWeakSolution flux U v) (hf : Measurable flux)
    (φ : 𝓓^{1}(U, ℝ)) :
    Integrable (katoWeakIntegrand flux u v φ) volume :=
  (φ.integrable_mul_partialDeriv (hu.u_locallyIntegrable.sub hv.u_locallyIntegrable).norm 0).add
    (φ.integrable_mul_partialDeriv
      (locallyIntegrableOn_kruzhkovFlux hf hu.u_locallyIntegrable hv.u_locallyIntegrable
        hu.flux_locallyIntegrable hv.flux_locallyIntegrable) 1)

namespace Kruzhkov

/-- Changing only the second state gives a linear error bound for the tested entropy
density and flux. The first state need not lie in the bounded state interval. -/
theorem norm_tested_state_sub_le {flux : ℝ → ℝ} (hf : ContDiff ℝ 1 flux) {a b C r s : ℝ}
    (hC : ∀ z ∈ Icc a b, ‖deriv flux z‖ ≤ C) (k A B : ℝ) (hr : r ∈ Icc a b) (hs : s ∈ Icc a b) :
    ‖(|k - r| * A + kruzhkovFlux flux r k * B) - (|k - s| * A + kruzhkovFlux flux s k * B)‖ ≤
      (‖A‖ + C * ‖B‖) * ‖r - s‖ := by
  have hη : ‖|k - r| - |k - s|‖ ≤ ‖r - s‖ := by
    simpa using norm_abs_sub_sub_abs_sub_le r k s k
  have hq : ‖kruzhkovFlux flux r k - kruzhkovFlux flux s k‖ ≤ C * ‖r - s‖ := by
    rw [kruzhkovFlux_comm flux r k, kruzhkovFlux_comm flux s k]
    exact norm_kruzhkovFlux_sub_right_le hf hC k hr hs
  calc
    _ = ‖(|k - r| - |k - s|) * A +
        (kruzhkovFlux flux r k - kruzhkovFlux flux s k) * B‖ := by ring_nf
    _ ≤ ‖r - s‖ * ‖A‖ + (C * ‖r - s‖) * ‖B‖ :=
      (norm_add_le _ _).trans (by simp only [norm_mul]; gcongr)
    _ = _ := by ring

end Kruzhkov

open Kruzhkov

/-- The spacetime diagonal limit of the doubled integrand for locally integrable weak
solutions. Local essential boundedness of the second state controls the flux error. -/
theorem IsWeakSolution.tendsto_doubled_diagonal {flux : ℝ → ℝ} {U : Opens ℝ^2} {u v : ℝ^2 → ℝ}
    (hu : IsWeakSolution flux U u) (hv : IsWeakSolution flux U v) (hf : ContDiff ℝ 1 flux)
    (hbv : ∀ K : Set ℝ^2, K ⊆ U → IsCompact K → ∃ M : ℝ, ∀ᵐ x ∂volume.restrict K, ‖v x‖ ≤ M)
    (φ : 𝓓^{1}(U, ℝ)) (μ : Mollifier 2) {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n)
    (hlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ p : ℝ^2 × ℝ^2, scaled μ (ε n) (p.1 - p.2) *
      (|u p.1 - v p.2| * (∂[0] (φ : ℝ^2 → ℝ)) p.1 + kruzhkovFlux flux (v p.2) (u p.1) *
      (∂[1] (φ : ℝ^2 → ℝ)) p.1)) atTop (𝓝 (∫ x, katoWeakIntegrand flux u v φ x)) := by
  obtain ⟨L, hLc, hLU, hKL, hL⟩ := exists_compact_diagonal_neighborhood φ μ hε hlim
  obtain ⟨M, hM⟩ := hbv L hLU hLc
  let w := L.indicator v
  have hw : Integrable w volume :=
    (hv.u_locallyIntegrable.integrableOn_compact_subset hLU hLc).integrable_indicator
      hLc.measurableSet
  obtain ⟨C₀, hC₀⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hf.continuous_deriv (by norm_num)).continuousOn (s := Icc (-M) M)
  let C := max C₀ 0
  have hC0 : 0 ≤ C := le_max_right _ _
  have hC : ∀ z ∈ Icc (-M) M, ‖deriv flux z‖ ≤ C := fun z hz ↦ (hC₀ z hz).trans (le_max_left _ _)
  obtain ⟨A, hA⟩ := (φ.continuous_partialDeriv 0).bounded_above_of_compact_support
    (φ.hasCompactSupport_partialDeriv 0)
  obtain ⟨B, hB⟩ := (φ.continuous_partialDeriv 1).bounded_above_of_compact_support
    (φ.hasCompactSupport_partialDeriv 1)
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hD0 : 0 ≤ A + C * B := add_nonneg hA0 (mul_nonneg hC0 hB0)
  have hM' := (ae_restrict_iff' hLc.measurableSet).1 hM
  have hMp : ∀ᵐ p : ℝ^2 × ℝ^2 ∂volume,
      (p.1 ∈ L → ‖v p.1‖ ≤ M) ∧ (p.2 ∈ L → ‖v p.2‖ ≤ M) := by
    rw [Measure.volume_eq_prod]
    exact ((Measure.quasiMeasurePreserving_fst.ae hM').and
      (Measure.quasiMeasurePreserving_snd.ae hM'))
  apply tendsto_integral_of_kernel_error hw
    (hu.integrable_katoWeakIntegrand hv hf.continuous.measurable φ) μ hε hlim
    _ (A + C * B)
  · filter_upwards [hL] with n hn
    have hU : ∀ x ∈ tsupport (φ : ℝ^2 → ℝ), ∀ z ∈ tsupport (scaled μ (ε n)), x - z ∈ U :=
      fun x hx z hz ↦ hLU (hn x hx z hz)
    have hρ : ContDiff ℝ 1 (scaled μ (ε n)) :=
      (scaled_contDiff μ).of_le (by norm_num)
    have hi := hu.integrable_doubledWeakIntegrand hv hf.continuous.measurable
      (diagonalTest φ _ hρ (scaled_hasCompactSupport μ (hε n)) hU)
    exact hi.congr (Eventually.of_forall (doubledWeakIntegrand_diagonalTest flux u v φ _ hρ
        (scaled_hasCompactSupport μ (hε n)) hU))
  · filter_upwards [hL] with n hn
    filter_upwards [hMp] with p hp
    have hρ0 := scaled_nonneg μ (hε n) (p.1 - p.2)
    by_cases hx : p.1 ∈ tsupport (φ : ℝ^2 → ℝ)
    · by_cases hz : scaled μ (ε n) (p.1 - p.2) = 0
      · simp [hz]
      have hyL : p.2 ∈ L := by
        simpa using hn p.1 hx (p.1 - p.2) (subset_tsupport _ hz)
      have hxL := hKL hx
      have hpx : v p.1 ∈ Icc (-M) M := by
        simpa only [Real.norm_eq_abs, abs_le, mem_Icc] using hp.1 hxL
      have hpy : v p.2 ∈ Icc (-M) M := by
        simpa only [Real.norm_eq_abs, abs_le, mem_Icc] using hp.2 hyL
      have he := norm_tested_state_sub_le hf hC (u p.1)
        ((∂[0] (φ : ℝ^2 → ℝ)) p.1) ((∂[1] (φ : ℝ^2 → ℝ)) p.1) hpy hpx
      have hcoeff : ‖(∂[0] (φ : ℝ^2 → ℝ)) p.1‖ + C * ‖(∂[1] (φ : ℝ^2 → ℝ)) p.1‖ ≤ A + C * B :=
        add_le_add (hA p.1) (mul_le_mul_of_nonneg_left (hB p.1) hC0)
      change ‖scaled μ (ε n) (p.1 - p.2) * _ - scaled μ (ε n) (p.1 - p.2) * _‖ ≤ _
      rw [← mul_sub, norm_mul, Real.norm_eq_abs, abs_of_nonneg hρ0]
      change _ ≤ (A + C * B) * (scaled μ (ε n) (p.1 - p.2) *
        ‖L.indicator v p.2 - L.indicator v p.1‖)
      rw [indicator_of_mem hyL, indicator_of_mem hxL, mul_left_comm]
      gcongr
      exact he.trans (mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _))
    · have hnonneg : 0 ≤ (A + C * B) * (scaled μ (ε n) (p.1 - p.2) * ‖w p.2 - w p.1‖) :=
        mul_nonneg hD0 (mul_nonneg hρ0 (norm_nonneg _))
      simpa [katoWeakIntegrand, φ.partialDeriv_eq_zero_of_notMem_tsupport hx] using hnonneg

/-- Locally essentially bounded scalar entropy weak solutions satisfy the interior
Kato inequality. -/
theorem IsEntropyWeakSolution.kato_inequality {flux : ℝ → ℝ} {U : Opens ℝ^2} {u v : ℝ^2 → ℝ}
    (hu : IsEntropyWeakSolution flux U u) (hv : IsEntropyWeakSolution flux U v)
    (hf : ContDiff ℝ 1 flux)
    (hbu : ∀ K : Set ℝ^2, K ⊆ U → IsCompact K → ∃ M : ℝ, ∀ᵐ x ∂volume.restrict K, ‖u x‖ ≤ M)
    (hbv : ∀ K : Set ℝ^2, K ⊆ U → IsCompact K → ∃ M : ℝ, ∀ᵐ x ∂volume.restrict K, ‖v x‖ ≤ M)
    (φ : 𝓓^{1}(U, ℝ)) (hφ : ∀ x, 0 ≤ φ x) :
    0 ≤ ∫ x, katoWeakIntegrand flux u v φ x := by
  let μ := standardMollifier 2
  let ε : ℕ → ℝ := fun n ↦ 1 / (n + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  apply ge_of_tendsto (hu.weak.tendsto_doubled_diagonal hv.weak hf hbv φ μ hε hlim)
  filter_upwards [eventually_diagonalTest_admissible φ μ hε hlim] with n hn
  have hρ : ContDiff ℝ 1 (scaled μ (ε n)) :=
    (scaled_contDiff μ).of_le (by norm_num)
  have h := hu.doubling_inequality hv hf hbu hbv
    (diagonalTest φ _ hρ (scaled_hasCompactSupport μ (hε n)) hn)
    (fun p ↦ mul_nonneg (hφ p.1) (scaled_nonneg μ (hε n) (p.1 - p.2)))
  simpa only [doubledWeakIntegrand_diagonalTest] using h

end PDE.Hyperbolic.ConservationLaw.Scalar
