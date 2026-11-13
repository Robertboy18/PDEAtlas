/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Critical.Amplitude
public import PDE.Hyperbolic.NonlinearWave.Critical.DerivativeInputs
public import PDE.Hyperbolic.NonlinearWave.Critical.GlobalLinearEstimate
public import PDE.Hyperbolic.NonlinearWave.Critical.LinearEstimate
import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Persistence.SmoothMaximalExistence

/-!
# Global smooth solutions of the quintic wave equation

Compact smooth initial data give a unique smooth solution of `uₜₜ − Δu + u⁵ = 0` for every
nonnegative time. This is Evans, §12.4, Theorem 3, which Evans attributes to Grillakis (§12.7).
Uniqueness holds even among classical solutions that are C² at positive times and C¹ up to the
initial slice, with no imposed spatial growth bound.

## How it works

We start with the maximal smooth solution of Evans, §12.3.2, Theorem 2
(`exists_maximal_smooth_wave`). If its lifespan `T` were finite, the estimates of steps 2-6 of the
proof of Theorem 3 would bound the amplitude on a late interval `[s, T)`, which is the bound (16),
and contradict the blow-up alternative of the maximal solution. The three linear estimates used
there, versions of the estimate (4) of Theorem 1 on backward cones and on the whole space, follow
from the Cauchy problem: finite propagation supplies compact spatial support, and the conserved
energy controls the restart data. Uniqueness follows from the energy argument on backward cones.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.3.2, Theorem 2; §12.4, Theorem 1, equation (4),
  and Theorem 3 with its proof, equations (16)-(24); §12.7.
  <https://doi.org/10.1090/gsm/019>
* M. G. Grillakis, *Regularity and asymptotic behavior of the wave equation with a critical
  nonlinearity*, Ann. of Math. (2) 132 (1990), 485-509.
  <https://doi.org/10.2307/1971427>
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter PDE PDE.Common PDE.Analysis
open scoped ENNReal Topology

namespace WaveEquation.Critical

open PDE.Hyperbolic.NonlinearWave.Cauchy

/-- Smooth compact initial data give a unique global smooth quintic wave.
Uniqueness holds on the closed forward half-space, even among solutions that
are only C² at positive time and C¹ up to the initial slice. The initial velocity
is the right derivative at time zero. -/
theorem exists_unique_global_smooth_quintic_wave (g h : ℝ^3 → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hgc : HasCompactSupport g) (hhc : HasCompactSupport h) :
    ∃ u : ℝ^4 → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) u {p | 0 ≤ p 0} ∧
      (∀ x, u (timeSpaceCons 0 x) = g x) ∧
      (∀ x, HasDerivWithinAt (fun t ↦ u (timeSpaceCons t x)) (h x) (Ici 0) 0) ∧
      (∀ t : ℝ, 0 < t → ∀ x : ℝ^3,
        waveOperator u (timeSpaceCons t x) + u (timeSpaceCons t x) ^ 5 = 0) ∧
      ∀ v : ℝ^4 → ℝ,
        ContDiffOn ℝ 2 v {p | 0 < p 0} → ContDiffOn ℝ 1 v {p | 0 ≤ p 0} →
        (∀ x, v (timeSpaceCons 0 x) = g x) →
        (∀ x, HasDerivWithinAt (fun t ↦ v (timeSpaceCons t x)) (h x) (Ici 0) 0) →
        (∀ t : ℝ, 0 < t → ∀ x : ℝ^3,
          waveOperator v (timeSpaceCons t x) + v (timeSpaceCons t x) ^ 5 = 0) →
        EqOn v u {p | 0 ≤ p 0} := by
  have hf : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ ↦ z ^ 5) := contDiff_id.pow 5
  obtain ⟨L, hL, u, hu, hpos, hvel, hwave, _, hblowup⟩ :=
    exists_maximal_smooth_wave hf (by simp) g h hg hh hgc hhc
  have hinfty : L = ∞ := by
    by_contra hfinite
    let T := L.toReal
    have hT : 0 < T := ENNReal.toReal_pos (ne_of_gt hL) hfinite
    have hreg : ContDiffOn ℝ (⊤ : ℕ∞) u {p | p 0 ∈ Ico 0 T} :=
      hu.mono fun p hp ↦ ⟨hp.1, (ENNReal.ofReal_lt_iff_lt_toReal hp.1 hfinite).mpr hp.2⟩
    have hu₂ : ContDiffOn ℝ 2 u {p | 0 < p 0 ∧ p 0 < T} :=
      (hreg.of_le (by simp)).mono fun p hp ↦ ⟨hp.1.le, hp.2⟩
    have hpde : ∀ t ∈ Ioo 0 T, ∀ x : ℝ^3,
        waveOperator u (timeSpaceCons t x) + u (timeSpaceCons t x) ^ 5 = 0 :=
      fun t ht x ↦ hwave t ht.1 ((ENNReal.ofReal_lt_iff_lt_toReal ht.1.le hfinite).mpr ht.2) x
    obtain ⟨R, hR⟩ := (hgc.union hhc).isBounded.exists_norm_le
    have hsupp := eq_zero_of_cauchyData_finite_strip
      ((hf.of_le (by simp)).locallyLipschitz) (by simp) hu₂
      (hreg.of_le (by simp)) hpde hpos (fun x ↦ (hvel x).derivWithin (uniqueDiffWithinAt_Ici 0))
      (R := R) (fun x hx ↦ image_eq_zero_of_notMem_tsupport
        (fun hx' ↦ (not_le_of_gt hx) (hR x (Or.inl hx'))))
      (fun x hx ↦ image_eq_zero_of_notMem_tsupport
        (fun hx' ↦ (not_le_of_gt hx) (hR x (Or.inr hx'))))
    obtain ⟨C, K, hC, hK, hcritical⟩ := exists_uniform_critical_linear_estimate_of_quintic_cauchy
        hT g h hreg hgc hhc hpde hpos hvel
    obtain ⟨D, hD, hcone⟩ := exists_uniform_cone_derivative_estimate_of_quintic_cauchy
        hT g h hreg hgc hhc hpde hpos hvel
    obtain ⟨N, hN, hglobal⟩ := exists_global_derivative_linear_estimate_of_quintic_cauchy
        hT g h hreg hgc hhc hpde hpos hvel
    obtain ⟨s, hs, M, hM⟩ := exists_amplitude_bound_of_wave_strichartz
      hT hu₂ hpde (fun t ht ↦ hsupp t ⟨ht.1.le, ht.2⟩) hC hK hD hcritical hcone hN hglobal
    obtain ⟨t, ht, x, hx⟩ := hblowup hfinite s hs.2 M
    exact (not_lt_of_ge (hM t ⟨(le_max_right 0 s).trans ht.1, ht.2⟩ x)) hx
  have hug : ContDiffOn ℝ (⊤ : ℕ∞) u {p | 0 ≤ p 0} := by
    simpa only [hinfty, ENNReal.ofReal_lt_top, and_true] using hu
  have hwg : ∀ t : ℝ, 0 < t → ∀ x : ℝ^3,
      waveOperator u (timeSpaceCons t x) + u (timeSpaceCons t x) ^ 5 = 0 :=
    fun t ht x ↦ hwave t ht (by simp [hinfty]) x
  refine ⟨u, hug, hpos, hvel, hwg, fun v hv hv₀ hvpos hvvel hvwave p hp ↦ ?_⟩
  change 0 ≤ p 0 at hp
  have hu₂ : ContDiffOn ℝ 2 u {p | 0 < p 0} :=
    (hug.of_le (by simp)).mono fun p hp ↦ by
      change 0 < p 0 at hp
      exact hp.le
  have he := eq_on_closed_cone_forward_locallyLipschitz
    (hf.of_le (by simp)).locallyLipschitz hv hu₂ hv₀ (hug.of_le (by simp))
    (spatialPart p) (T := p 0 + 1) (by linarith) (fun t ht x _ ↦ hvwave t ht.1 x)
    (fun t ht x _ ↦ hwg t ht.1 x) (fun x _ ↦ (hvpos x).trans (hpos x).symm)
    (fun x _ ↦ (hvvel x).derivWithin (uniqueDiffWithinAt_Ici 0) |>.trans
      ((hvel x).derivWithin (uniqueDiffWithinAt_Ici 0)).symm)
    (p 0) ⟨hp, by linarith⟩ (spatialPart p)
    (Metric.mem_closedBall_self (by linarith))
  simpa only [timeSpaceCons_spatialPart] using he

end WaveEquation.Critical
