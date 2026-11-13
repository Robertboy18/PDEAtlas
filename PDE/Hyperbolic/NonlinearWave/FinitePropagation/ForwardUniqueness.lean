/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.FinitePropagation.ForwardVanishing
public import PDE.Hyperbolic.NonlinearWave.FinitePropagation.ForwardQuadraticEnergy
public import PDE.Hyperbolic.NonlinearWave.SmallData.Mass
public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.Uniqueness

/-!
# Classical uniqueness with no spatial growth assumptions

Compact backward cones bound the ranges of both continuous fields. A locally
Lipschitz scalar reaction consequently has a Lipschitz extension on each cone.
The forward quadratic energy and its zero initial limit propagate equality from the right Cauchy
traces.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.1.2, Theorem 2(ii).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Common PDE.Analysis WaveEquation
open scoped Topology

namespace WaveEquation

variable {n : ℕ}

/-- Locally Lipschitz reactions have classical domain of
dependence for forward C² fields with C¹ right boundary regularity. -/
theorem eq_on_closed_cone_forward_locallyLipschitz [Fact (0 < n)] {f : ℝ → ℝ} {u v : ℝ^(n + 1) → ℝ}
    (hf : LocallyLipschitz f) (hu : ContDiffOn ℝ 2 u {p | 0 < p 0})
    (hv : ContDiffOn ℝ 2 v {p | 0 < p 0}) (hu₀ : ContDiffOn ℝ 1 u {p | 0 ≤ p 0})
    (hv₀ : ContDiffOn ℝ 1 v {p | 0 ≤ p 0}) (c : ℝ^n) {T : ℝ} (hT : 0 < T)
    (huwave : ∀ s ∈ Ioo 0 T, ∀ x ∈ Metric.ball c (T - s),
      waveOperator u (timeSpaceCons s x) + f (u (timeSpaceCons s x)) = 0)
    (hvwave : ∀ s ∈ Ioo 0 T, ∀ x ∈ Metric.ball c (T - s),
      waveOperator v (timeSpaceCons s x) + f (v (timeSpaceCons s x)) = 0)
    (hpos : ∀ x ∈ Metric.ball c T, u (timeSpaceCons 0 x) = v (timeSpaceCons 0 x))
    (hvel : ∀ x ∈ Metric.ball c T, derivWithin (fun t ↦ u (timeSpaceCons t x)) (Ici 0) 0 =
      derivWithin (fun t ↦ v (timeSpaceCons t x)) (Ici 0) 0) :
    ∀ t ∈ Icc 0 T, ∀ x ∈ Metric.closedBall c (T - t),
      u (timeSpaceCons t x) = v (timeSpaceCons t x) := by
  let P : ℝ^(n + 1) → ℝ^(n + 1) := fun p ↦ timeSpaceCons (max (p 0) 0) (spatialPart p)
  have hP : Continuous P := (contDiff_timeSpaceCons_uncurry n (m := 1)).continuous.comp
    (((EuclideanSpace.proj 0).continuous.max continuous_const).prodMk (spatialPartCLM n).continuous)
  have hPs : ∀ p : ℝ^(n + 1), P p ∈ {q | 0 ≤ q 0} := fun p ↦ le_max_right (p 0) 0
  have hPu : Continuous (u ∘ P) := hu₀.continuousOn.comp_continuous hP hPs
  have hPv : Continuous (v ∘ P) := hv₀.continuousOn.comp_continuous hP hPs
  obtain ⟨Cu, _, hCu⟩ := exists_norm_le_on_timeSpaceCylinder (u ∘ P) hPu 0 T c T
  obtain ⟨Cv, _, hCv⟩ := exists_norm_le_on_timeSpaceCylinder (v ∘ P) hPv 0 T c T
  let B := max Cu Cv
  obtain ⟨K, hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (s := Icc (-B) B) isCompact_Icc hf.locallyLipschitzOn
  obtain ⟨F, hF, hFeq⟩ := hK.extend_real
  have hrange (s : ℝ) (hs : s ∈ Ioo 0 T) (x : ℝ^n) (hx : x ∈ Metric.ball c (T - s)) :
      u (timeSpaceCons s x) ∈ Icc (-B) B ∧ v (timeSpaceCons s x) ∈ Icc (-B) B := by
    have hx' : x ∈ Metric.closedBall c T := Metric.mem_closedBall.mpr
      ((Metric.mem_ball.mp hx).le.trans (sub_le_self T hs.1.le))
    have hu' := hCu s (Ioo_subset_Icc_self hs) x hx'
    have hv' := hCv s (Ioo_subset_Icc_self hs) x hx'
    simp only [Function.comp_apply, P, timeSpaceCons_zero, spatialPart_timeSpaceCons,
      max_eq_left hs.1.le, Real.norm_eq_abs] at hu' hv'
    exact ⟨abs_le.mp (hu'.trans (le_max_left _ _)), abs_le.mp (hv'.trans (le_max_right _ _))⟩
  have hpos' : ∀ x ∈ Metric.ball c T, (u - v) (timeSpaceCons 0 x) = 0 :=
    fun x hx ↦ sub_eq_zero.mpr (hpos x hx)
  have hvel' : ∀ x ∈ Metric.ball c T,
      derivWithin (fun t ↦ (u - v) (timeSpaceCons t x)) (Ici 0) 0 = 0 := by
    intro x hx
    change derivWithin (fun t ↦ u (timeSpaceCons t x) - v (timeSpaceCons t x)) (Ici 0) 0 = 0
    rw [derivWithin_fun_sub (differentiableWithinAt_initial_time hu₀ x)
      (differentiableWithinAt_initial_time hv₀ x), hvel x hx, sub_self]
  have henergy (s : ℝ) (hs : s ∈ Ioo 0 T) : backwardConeEnergy (u - v) c T s = 0 := by
    have he := quadraticConeEnergy_sub_eq_zero_forward hF hu hv (hu₀.sub hv₀) c hT
      (fun r hr x hx ↦ ?_) (fun r hr x hx ↦ ?_) hpos' hvel' hs
    · have hnonneg : 0 ≤ ballIntegral n (fun x ↦ (u - v) (timeSpaceCons s x) ^ 2 / 2) c (T - s) :=
        setIntegral_nonneg measurableSet_ball (fun x _ ↦ by positivity)
      unfold semilinearBackwardConeEnergy at he
      have hclassical := backwardConeEnergy_nonneg (u - v) c T s
      linarith
    · rw [← hFeq (hrange r hr x hx).1]
      exact huwave r hr x hx
    · rw [← hFeq (hrange r hr x hx).2]
      exact hvwave r hr x hx
  have he := eq_zero_on_closed_backwardCone_of_energy_eq_zero_forward
    (hu.sub hv) (hu₀.sub hv₀) c hT hpos' henergy
  exact fun t ht x hx ↦ sub_eq_zero.mp (he t ht x hx)


/-- Compact Cauchy data propagate at speed one with only forward regularity.
The reaction need not arise from a nonnegative potential. -/
theorem hasForwardSupport_of_cauchyData [Fact (0 < n)] {f : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    {g h : ℝ^n → ℝ} {R : ℝ} (hf : LocallyLipschitz f) (hf0 : f 0 = 0)
    (hu : ContDiffOn ℝ 2 u {p | 0 < p 0}) (hu₀ : ContDiffOn ℝ 1 u {p | 0 ≤ p 0})
    (hwave : ∀ t, 0 < t → ∀ x, waveOperator u (timeSpaceCons t x) + f (u (timeSpaceCons t x)) = 0)
    (hpos : ∀ x, u (timeSpaceCons 0 x) = g x)
    (hvel : ∀ x, derivWithin (fun t ↦ u (timeSpaceCons t x)) (Ici 0) 0 = h x)
    (hg : ∀ x, R < ‖x‖ → g x = 0) (hh : ∀ x, R < ‖x‖ → h x = 0) :
    SmallData.HasForwardSupport u R := by
  intro t ht x hx
  rcases ht.eq_or_lt with rfl | htpos
  · exact (hpos x).trans (hg x (by simpa using hx))
  have hbase (y : ℝ^n) (hy : y ∈ Metric.ball x t) : R < ‖y‖ := by
    have hy' : ‖y - x‖ < t := by simpa only [Metric.mem_ball, dist_eq_norm] using hy
    have hn := norm_le_norm_add_norm_sub y x
    linarith
  exact eq_on_closed_cone_forward_locallyLipschitz (v := fun _ ↦ 0) hf hu
    contDiffOn_const hu₀ contDiffOn_const x htpos (fun s hs y _ ↦ hwave s hs.1 y)
    (fun _ _ _ _ ↦ by simp [waveOperator, hf0]) (fun y hy ↦ (hpos y).trans (hg y (hbase y hy)))
    (fun y hy ↦ by simp [hvel, hh y (hbase y hy)])
    t ⟨ht, le_rfl⟩ x (by simp)

/-- Evans, §12.1.2, Theorem 2(ii), with right initial velocity.
Zero Cauchy data on the open ball force vanishing on the entire closed cone;
only interior C² and closed-halfspace C¹ regularity are needed. -/
theorem eq_zero_on_closed_cone_forward_semilinear_of_open_ball [Fact (0 < n)] {V : ℝ → ℝ}
    {u : ℝ^(n + 1) → ℝ} (hV : ContDiff ℝ 2 V) (hVnonneg : ∀ z, 0 ≤ V z) (hVzero : V 0 = 0)
    (hu : ContDiffOn ℝ 2 u {p | 0 < p 0}) (hu₀ : ContDiffOn ℝ 1 u {p | 0 ≤ p 0}) (c : ℝ^n) {T : ℝ}
    (hT : 0 < T)
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x ∈ Metric.ball c (T - t),
      semilinearWaveOperator V u (timeSpaceCons t x) = 0)
    (hpos : ∀ x ∈ Metric.ball c T, u (timeSpaceCons 0 x) = 0)
    (hvel : ∀ x ∈ Metric.ball c T, derivWithin (fun t ↦ u (timeSpaceCons t x)) (Ici 0) 0 = 0) :
    ∀ t ∈ Icc 0 T, ∀ x ∈ Metric.closedBall c (T - t), u (timeSpaceCons t x) = 0 := by
  have hmin : IsLocalMin V 0 := Filter.Eventually.of_forall fun z ↦ by
    rw [hVzero]
    exact hVnonneg z
  have hfzero : deriv V 0 = 0 := hmin.deriv_eq_zero
  have hf : ContDiff ℝ 1 (deriv V) := hV.deriv'
  exact eq_on_closed_cone_forward_locallyLipschitz (v := fun _ ↦ 0)
    hf.locallyLipschitz hu contDiffOn_const hu₀ contDiffOn_const c hT hwave
    (fun _ _ _ _ ↦ by simp [waveOperator, hfzero]) hpos
    (fun x hx ↦ by simpa using hvel x hx)

end WaveEquation
