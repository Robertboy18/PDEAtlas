/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Classical.ForwardLocalization
public import PDE.Hyperbolic.NonlinearWave.DomainOfDependence
import PDE.FDeriv.Calculus
import PDE.FDeriv.SpaceTime

/-!
# Local uniqueness before a classical wave endpoint

In every positive spatial dimension, compact cone ranges reduce a locally
Lipschitz scalar reaction to a globally Lipschitz one. The quadratic
cone energy theorem then identifies classical solutions from their
Cauchy data.
-/

@[expose] public noncomputable section

open PDE.Common PDE.Analysis Set
open scoped Topology

namespace WaveEquation.SmallData.Classical

variable {n : ℕ}

/-- Smooth time reflection gives an ambient representative on every proper
closed substrip. It imposes no regularity at the terminal time. -/
theorem exists_contDiff_eventuallyEq_before {m : ℕ∞} {u : ℝ^(n + 1) → ℝ} {S T : ℝ}
    (hu : ContDiffOn ℝ m u {p | p 0 < T}) (hST : S < T) :
    ∃ v : ℝ^(n + 1) → ℝ, ContDiff ℝ m v ∧ ∀ p : ℝ^(n + 1), p 0 ≤ S → v =ᶠ[𝓝 p] u := by
  let P : ℝ^(n + 1) → ℝ^(n + 1) := fun p ↦ timeSpaceCons (T - p 0) (spatialPart p)
  have hP : ContDiff ℝ m P := (contDiff_timeSpaceCons_uncurry n).comp
      ((contDiff_const.sub (EuclideanSpace.proj 0).contDiff).prodMk (spatialPartCLM n).contDiff)
  have hPP (p : ℝ^(n + 1)) : P (P p) = p := by
    simp [P]
  have hU : ContDiffOn ℝ m (u ∘ P) {p : ℝ^(n + 1) | 0 < p 0} := by
    apply hu.comp hP.contDiffOn
    intro p hp
    change T - p 0 < T
    exact sub_lt_self T hp
  obtain ⟨v, hv, he⟩ := exists_contDiff_eqOn_forward hU (half_pos (sub_pos.mpr hST))
  refine ⟨v ∘ P, hv.comp hP, fun p hp ↦ ?_⟩
  have hlt : (T - S) / 2 < P p 0 := by
    change (T - S) / 2 < T - p 0
    linarith
  have hgerm := (eventuallyEq_of_eqOn_forward he hlt).comp_tendsto hP.continuous.continuousAt
  simpa only [Function.comp_def, hPP] using hgerm

variable [Fact (0 < n)]

/-- A Lipschitz restriction of the source to a set containing both solution ranges
is sufficient for classical domain of dependence. -/
theorem eq_on_closed_backwardCone_of_eq_cauchyData_lipschitzOn {K : NNReal} {f : ℝ → ℝ} {s : Set ℝ}
    {u v : ℝ^(n + 1) → ℝ} (hf : LipschitzOnWith K f s) (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (c : ℝ^n) {a T : ℝ}
    (huwave : ∀ t ∈ Ico a T, ∀ x ∈ Metric.ball c (T - t), waveOperator (n := n) u
      (timeSpaceCons t x) = -f (u (timeSpaceCons t x)))
    (hvwave : ∀ t ∈ Ico a T, ∀ x ∈ Metric.ball c (T - t), waveOperator (n := n) v
      (timeSpaceCons t x) = -f (v (timeSpaceCons t x)))
    (hus : ∀ t ∈ Ico a T, ∀ x ∈ Metric.ball c (T - t), u (timeSpaceCons t x) ∈ s)
    (hvs : ∀ t ∈ Ico a T, ∀ x ∈ Metric.ball c (T - t), v (timeSpaceCons t x) ∈ s)
    (hposition : ∀ x ∈ Metric.closedBall c (T - a), u (timeSpaceCons a x) = v (timeSpaceCons a x))
    (hvelocity : ∀ x ∈ Metric.closedBall c (T - a), (∂[0] u) (timeSpaceCons a x) =
      (∂[0] v) (timeSpaceCons a x)) :
    ∀ t ∈ Icc a T, ∀ x ∈ Metric.closedBall c (T - t), u (timeSpaceCons t x) =
      v (timeSpaceCons t x) := by
  obtain ⟨F, hF, hEq⟩ := hf.extend_real
  apply eq_on_closed_backwardCone_of_eq_cauchyData_semilinear hF hu hv c
  · intro t ht x hx
    dsimp only
    rw [← hEq (hus t ht x hx), huwave t ht x hx, neg_add_cancel]
  · intro t ht x hx
    dsimp only
    rw [← hEq (hvs t ht x hx), hvwave t ht x hx, neg_add_cancel]
  · exact hposition
  · exact hvelocity

/-- All ambient C² solutions with a locally Lipschitz reaction obey finite speed
of dependence. Only the PDE inside the cone and data on its base are required. -/
theorem eq_on_closed_backwardCone_of_eq_cauchyData_locallyLipschitz {f : ℝ → ℝ}
    {u v : ℝ^(n + 1) → ℝ} (hf : LocallyLipschitz f) (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (c : ℝ^n) {a T : ℝ}
    (huwave : ∀ t ∈ Ico a T, ∀ x ∈ Metric.ball c (T - t), waveOperator (n := n) u
      (timeSpaceCons t x) = -f (u (timeSpaceCons t x)))
    (hvwave : ∀ t ∈ Ico a T, ∀ x ∈ Metric.ball c (T - t), waveOperator (n := n) v
      (timeSpaceCons t x) = -f (v (timeSpaceCons t x)))
    (hposition : ∀ x ∈ Metric.closedBall c (T - a), u (timeSpaceCons a x) = v (timeSpaceCons a x))
    (hvelocity : ∀ x ∈ Metric.closedBall c (T - a), (∂[0] u) (timeSpaceCons a x) =
      (∂[0] v) (timeSpaceCons a x)) :
    ∀ t ∈ Icc a T, ∀ x ∈ Metric.closedBall c (T - t), u (timeSpaceCons t x) =
      v (timeSpaceCons t x) := by
  obtain ⟨Cu, _, hCu⟩ := exists_norm_le_on_timeSpaceCylinder u hu.continuous a T c (T - a)
  obtain ⟨Cv, _, hCv⟩ := exists_norm_le_on_timeSpaceCylinder v hv.continuous a T c (T - a)
  obtain ⟨K, hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (s := Icc (-max Cu Cv) (max Cu Cv)) isCompact_Icc hf.locallyLipschitzOn
  apply eq_on_closed_backwardCone_of_eq_cauchyData_lipschitzOn hK hu hv c huwave hvwave
  · intro t ht x hx
    apply abs_le.mp
    exact (hCu t (Ico_subset_Icc_self ht) x (Metric.ball_subset_closedBall
        (Metric.ball_subset_ball (sub_le_sub_left ht.1 T) hx))).trans (le_max_left _ _)
  · intro t ht x hx
    apply abs_le.mp
    exact (hCv t (Ico_subset_Icc_self ht) x (Metric.ball_subset_closedBall
        (Metric.ball_subset_ball (sub_le_sub_left ht.1 T) hx))).trans (le_max_right _ _)
  · exact hposition
  · exact hvelocity

/-- Equality of Cauchy data propagates across a finite forward strip for arbitrary
C² solutions. No global bound on either field is needed. -/
theorem eq_on_forward_strip_of_eq_cauchyData_locallyLipschitz {f : ℝ → ℝ} {u v : ℝ^(n + 1) → ℝ}
    {a T : ℝ} (hf : LocallyLipschitz f) (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (huwave : ∀ p : ℝ^(n + 1), p 0 ∈ Ico a T → waveOperator (n := n) u p = -f (u p))
    (hvwave : ∀ p : ℝ^(n + 1), p 0 ∈ Ico a T → waveOperator (n := n) v p = -f (v p))
    (hposition : ∀ x : ℝ^n, u (timeSpaceCons a x) = v (timeSpaceCons a x))
    (hvelocity : ∀ x : ℝ^n, (∂[0] u) (timeSpaceCons a x) = (∂[0] v) (timeSpaceCons a x)) :
    ∀ p : ℝ^(n + 1), p 0 ∈ Icc a T → u p = v p := by
  intro p hp
  have he := eq_on_closed_backwardCone_of_eq_cauchyData_locallyLipschitz hf hu hv (spatialPart p)
    (fun t ht x _ ↦ huwave (timeSpaceCons t x) (by simpa using ht))
    (fun t ht x _ ↦ hvwave (timeSpaceCons t x) (by simpa using ht))
    (fun x _ ↦ hposition x) (fun x _ ↦ hvelocity x)
    (p 0) hp (spatialPart p) (Metric.mem_closedBall_self (sub_nonneg.mpr hp.2))
  simpa using he

/-- Classical uniqueness before a terminal time requires no regularity at that
time. The fields need only be C² on the open half-space `t < T`, including a
neighborhood of the initial slice. -/
theorem eq_on_forward_open_strip_of_eq_cauchyData_locallyLipschitz {f : ℝ → ℝ} {u v : ℝ^(n + 1) → ℝ}
    {a T : ℝ} (hf : LocallyLipschitz f) (hu : ContDiffOn ℝ 2 u {p | p 0 < T})
    (hv : ContDiffOn ℝ 2 v {p | p 0 < T})
    (huwave : ∀ p : ℝ^(n + 1), p 0 ∈ Ico a T → waveOperator (n := n) u p = -f (u p))
    (hvwave : ∀ p : ℝ^(n + 1), p 0 ∈ Ico a T → waveOperator (n := n) v p = -f (v p))
    (hposition : ∀ x : ℝ^n, u (timeSpaceCons a x) = v (timeSpaceCons a x))
    (hvelocity : ∀ x : ℝ^n, (∂[0] u) (timeSpaceCons a x) = (∂[0] v) (timeSpaceCons a x)) :
    ∀ p : ℝ^(n + 1), p 0 ∈ Ico a T → u p = v p := by
  intro p hp
  let S := (p 0 + T) / 2
  have hpS : p 0 ≤ S := by dsimp [S]; linarith [hp.2]
  have hST : S < T := by dsimp [S]; linarith [hp.2]
  have haS : a ≤ S := hp.1.trans hpS
  obtain ⟨U, hU, hUeq⟩ := exists_contDiff_eventuallyEq_before hu hST
  obtain ⟨V, hV, hVeq⟩ := exists_contDiff_eventuallyEq_before hv hST
  have he := eq_on_forward_strip_of_eq_cauchyData_locallyLipschitz hf hU hV
    (a := a) (T := S) (fun q hq ↦ ?_) (fun q hq ↦ ?_) (fun x ↦ ?_) (fun x ↦ ?_) p ⟨hp.1, hpS⟩
  · rwa [(hUeq p hpS).eq_of_nhds, (hVeq p hpS).eq_of_nhds] at he
  · rw [waveOperator_congr_nhds (hUeq q hq.2.le), (hUeq q hq.2.le).eq_of_nhds]
    exact huwave q ⟨hq.1, hq.2.trans hST⟩
  · rw [waveOperator_congr_nhds (hVeq q hq.2.le), (hVeq q hq.2.le).eq_of_nhds]
    exact hvwave q ⟨hq.1, hq.2.trans hST⟩
  · rw [(hUeq (timeSpaceCons a x) (by simpa using haS)).eq_of_nhds,
      (hVeq (timeSpaceCons a x) (by simpa using haS)).eq_of_nhds]
    exact hposition x
  · rw [PDE.partialDeriv_congr_nhds 0 (hUeq (timeSpaceCons a x) (by simpa using haS)),
      PDE.partialDeriv_congr_nhds 0 (hVeq (timeSpaceCons a x) (by simpa using haS))]
    exact hvelocity x

end WaveEquation.SmallData.Classical
