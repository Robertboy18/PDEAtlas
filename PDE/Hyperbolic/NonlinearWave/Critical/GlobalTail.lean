/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Critical.Cone.EnlargedBootstrap
public import PDE.Hyperbolic.NonlinearWave.Critical.Cone.FiniteCover

/-!
# A critical tail for the compactly supported quintic wave

The PDE, speed-one support, and uniform linear estimates give whole-space L⁴ in time with L¹² in
space on a late interval. Energy decay, cone enlargement, and finite spatial localization are
derived in the proof. Only C² regularity on the open band is assumed.

This assembles steps 3-6 of the proof of Evans, §12.4, Theorem 3: the energy decay (18)-(19), the
enlarged cones of (22)-(24) and the finite cover of step 6. The linear estimates are hypotheses, and
the result is not a continuation theorem.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.4, Theorem 3, steps 3-6 of its proof,
  equations (18)-(24).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter PDE PDE.Common PDE.Analysis
open scoped ENNReal Topology

namespace WaveEquation.Critical

/-- The quintic equation, speed-one support and uniform linear prefix estimates
produce a whole-space critical tail by energy decay, cone enlargement and a finite cover.
The physical linear estimates remain explicit; this is not a continuation theorem. -/
theorem exists_global_critical_tail_of_wave_strichartz {u : ℝ^4 → ℝ} {T R C K L : ℝ} (hT : 0 < T)
    (hu : ContDiffOn ℝ 2 u {p | 0 < p 0 ∧ p 0 < T})
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x : ℝ^3,
      waveOperator u (timeSpaceCons t x) + u (timeSpaceCons t x) ^ 5 = 0)
    (hsupport : ∀ t ∈ Ioo 0 T, ∀ x : ℝ^3, R + t < ‖x‖ → u (timeSpaceCons t x) = 0) (hC : 0 < C)
    (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hlinear : ∀ c : ℝ^3, ∀ A : ℝ, T ≤ A → ∀ s ∈ Ioo 0 T, ∀ t ∈ Ico s T,
      lpNorm (fun r ↦ lpNorm (fun x ↦ u (timeSpaceCons r x)) 12
      (volume.restrict (Metric.ball c (A - r)))) 4 (volume.restrict (Icc s t)) ≤ C + K * ∫ r in Icc
      s t, lpNorm (fun x ↦ u (timeSpaceCons r x) ^ 5) 2 (volume.restrict (Metric.ball c (A - r))))
    (hderivative : ∀ c : ℝ^3, ∀ i : Fin 4, ∀ s ∈ Ioo 0 T, ∃ A : ℝ, ∀ r ∈ Ico s T,
      lpNorm (fun x ↦ (∂[i] u) (timeSpaceCons r x)) 6 (volume.restrict (Metric.ball c (T - r))) ≤
      A + L * ∫ q in Icc s r, lpNorm (fun x ↦ u (timeSpaceCons q x) ^ 4 *
      (∂[i] u) (timeSpaceCons q x)) 2 (volume.restrict (Metric.ball c (T - q)))) :
    ∃ s ∈ Ioo 0 T, MemLp (fun t ↦ lpNorm (fun x ↦ u (timeSpaceCons t x)) 12 volume)
      4 (volume.restrict (Ico s T)) := by
  apply exists_memLp_four_twelve_of_forward_support_and_enlarged_cones hT hu.continuousOn hsupport
  intro c
  obtain ⟨s, hs, δ, hδ, hboot⟩ := exists_enlarged_cone_bootstrap_of_wave_strichartz
    hT hu c hwave hC hK hL (hlinear c T le_rfl) (hderivative c) hC hK
  exact ⟨s, hs, δ, hδ, hboot (hlinear c (T + δ) (le_add_of_nonneg_right hδ.le) s hs)⟩

end WaveEquation.Critical
