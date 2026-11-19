/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Finite regularity of interval averages

A compact integration interval supplies the local uniform bounds needed to
differentiate an average. Iterating this argument preserves every finite order
of joint regularity. The parameter neighborhood is open; no global growth
bound or integrability hypothesis is needed.
-/

@[expose] public section
noncomputable section

namespace PDE.Calculus

open Filter MeasureTheory Metric Set
open scoped Topology Interval

universe u

variable {H : Type u} [NormedAddCommGroup H]

/-- Tube lemma for the parameter interval: a family continuous at every `(p, t)` with `p ∈ U`,
`t ∈ [0, 1]` is bounded on `ball x r × [0, 1]` for a ball inside `U`. No properness of the
parameter space is needed, only compactness of `[0, 1]`. -/
private theorem exists_ball_bound_of_joint {G : Type*} [NormedAddCommGroup G] (g : H × ℝ → G)
    {U : Set H} (hU : IsOpen U) (hg : ∀ p ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, ContinuousAt g (p, t))
    {x : H} (hx : x ∈ U) :
    ∃ r > 0, ∃ M : ℝ, ∀ p ∈ ball x r, p ∈ U ∧ ∀ t ∈ Icc (0 : ℝ) 1, ‖g (p, t)‖ ≤ M := by
  have hsec : ContinuousOn (fun t ↦ g (x, t)) (Icc (0 : ℝ) 1) := fun t ht ↦
    ((hg x hx t ht).comp (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hsec
  have hev : ∀ᶠ p in 𝓝 x, ∀ t ∈ Icc (0 : ℝ) 1, p ∈ U ∧ ‖g (p, t)‖ < M₀ + 1 := by
    refine isCompact_Icc.eventually_forall_of_forall_eventually fun t ht ↦ ?_
    have h1 : ∀ᶠ z : H × ℝ in 𝓝 (x, t), z.1 ∈ U :=
      continuous_fst.continuousAt.preimage_mem_nhds (hU.mem_nhds hx)
    have h2 : ∀ᶠ z : H × ℝ in 𝓝 (x, t), ‖g z‖ < M₀ + 1 :=
      (hg x hx t ht).norm.eventually (gt_mem_nhds (by linarith [hM₀ t ht]))
    exact h1.and h2
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  exact ⟨r, hr, M₀ + 1, fun p hp ↦
    ⟨(hball p hp 0 ⟨le_rfl, zero_le_one⟩).1, fun t ht ↦ (hball p hp t ht).2.le⟩⟩

section FirstOrder

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Joint continuity on the parameter neighborhood and compact interval gives
continuity of the average. The local domination comes from the compactness of `[0, 1]`. -/
theorem continuousAt_intervalAverage_of_joint
    (f : H × ℝ → F) {U : Set H} (hU : IsOpen U)
    (hf : ∀ p ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, ContinuousAt f (p, t))
    {x : H} (hx : x ∈ U) :
    ContinuousAt (fun p ↦ ∫ t in (0 : ℝ)..1, f (p, t)) x := by
  obtain ⟨R, hR, M, hM⟩ := exists_ball_bound_of_joint f hU hf hx
  have hsection (p : H) (hp : p ∈ U) :
      ContinuousOn (fun t ↦ f (p, t)) (Icc (0 : ℝ) 1) := fun t ht ↦
    ((hf p hp t ht).comp (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
  have hsub : Ι (0 : ℝ) 1 ⊆ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le zero_le_one] using
      (uIoc_subset_uIcc : Ι (0 : ℝ) 1 ⊆ uIcc (0 : ℝ) 1)
  apply intervalIntegral.continuousAt_of_dominated_interval (μ := volume)
    (F := fun p t ↦ f (p, t)) (bound := fun _ ↦ M)
  · filter_upwards [ball_mem_nhds x hR] with p hp
    exact ((hsection p (hM p hp).1).mono hsub).aestronglyMeasurable measurableSet_uIoc
  · filter_upwards [ball_mem_nhds x hR] with p hp
    filter_upwards [] with t ht
    exact (hM p hp).2 t (hsub ht)
  · exact intervalIntegrable_const
  · filter_upwards [] with t ht
    exact (hf x hx t (hsub ht)).comp (f := fun p : H ↦ (p, t))
      (continuous_id.prodMk continuous_const).continuousAt

variable [NormedSpace ℝ H]

/-- A jointly continuous parameter derivative differentiates the interval average.
The compactness of `[0, 1]` supplies the derivative bound required by the dominated theorem. -/
theorem hasFDerivAt_intervalAverage_of_joint
    (f : H × ℝ → F) (D : H × ℝ → H →L[ℝ] F)
    {U : Set H} (hU : IsOpen U)
    (hf : ∀ p ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, ContinuousAt f (p, t))
    (hD : ∀ p ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, ContinuousAt D (p, t))
    (hd : ∀ p ∈ U, ∀ t ∈ Icc (0 : ℝ) 1,
      HasFDerivAt (fun y ↦ f (y, t)) (D (p, t)) p)
    {x : H} (hx : x ∈ U) :
    HasFDerivAt (fun p ↦ ∫ t in (0 : ℝ)..1, f (p, t))
      (∫ t in (0 : ℝ)..1, D (x, t)) x := by
  obtain ⟨R, hR, M, hM⟩ := exists_ball_bound_of_joint D hU hD hx
  have hsection (p : H) (hp : p ∈ U) :
      ContinuousOn (fun t ↦ f (p, t)) (Icc (0 : ℝ) 1) := by
    intro t ht
    exact ((hf p hp t ht).comp
      (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
  have hsectionD : ContinuousOn (fun t ↦ D (x, t)) (Icc (0 : ℝ) 1) := by
    intro t ht
    exact ((hD x hx t ht).comp
      (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
  have hsub : Ι (0 : ℝ) 1 ⊆ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le zero_le_one] using
      (uIoc_subset_uIcc : Ι (0 : ℝ) 1 ⊆ uIcc (0 : ℝ) 1)
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (𝕜 := ℝ) (μ := volume) (F := fun p t ↦ f (p, t))
    (F' := fun p t ↦ D (p, t)) (bound := fun _ ↦ M)
    (s := ball x R) (ball_mem_nhds x hR)
  · filter_upwards [ball_mem_nhds x hR] with p hp
    exact ContinuousOn.aestronglyMeasurable
      ((hsection p (hM p hp).1).mono hsub) measurableSet_uIoc
  · exact (hsection x hx).intervalIntegrable_of_Icc zero_le_one
  · exact (hsectionD.mono hsub).aestronglyMeasurable measurableSet_uIoc
  · filter_upwards [] with t ht p hp
    exact (hM p hp).2 t (hsub ht)
  · exact intervalIntegrable_const
  · filter_upwards [] with t ht p hp
    exact hd p (hM p hp).1 t (hsub ht)

end FirstOrder

variable [NormedSpace ℝ H]
variable {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Averaging a jointly `Cⁿ` family over `[0,1]` preserves its finite regularity
on any open parameter neighborhood. The codomain may be any real Banach space,
so the same argument applies recursively to its derivative. -/
theorem contDiffAt_intervalAverage_of_joint (n : ℕ)
    (f : H × ℝ → F) {U : Set H} (hU : IsOpen U)
    (hf : ∀ p ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ n f (p, t))
    {x : H} (hx : x ∈ U) :
    ContDiffAt ℝ n (fun p ↦ ∫ t in (0 : ℝ)..1, f (p, t)) x := by
  induction n generalizing F with
  | zero =>
    refine contDiffAt_zero.mpr ⟨U, hU.mem_nhds hx, fun p hp ↦ ?_⟩
    exact (continuousAt_intervalAverage_of_joint f hU
      (fun y hy t ht ↦ (hf y hy t ht).continuousAt) hp).continuousWithinAt
  | succ n ih =>
    let D : H × ℝ → H →L[ℝ] F := fun q ↦
      (fderiv ℝ f q).comp (ContinuousLinearMap.inl ℝ H ℝ)
    have hDn (p : H) (hp : p ∈ U) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
        ContDiffAt ℝ n D (p, t) :=
      ((hf p hp t ht).fderiv_right (m := (n : WithTop ℕ∞))
        (by norm_num)).clm_comp contDiffAt_const
    have hd (p : H) (hp : p ∈ U) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
        HasFDerivAt (fun y ↦ f (y, t)) (D (p, t)) p := by
      have hline : HasFDerivAt (fun y : H ↦ (y, t))
          (ContinuousLinearMap.inl ℝ H ℝ) p :=
        (hasFDerivAt_id p).prodMk (hasFDerivAt_const t p)
      exact ((hf p hp t ht).differentiableAt (by norm_num)).hasFDerivAt.comp p hline
    apply contDiffAt_succ_iff_hasFDerivAt.mpr
    refine ⟨fun p ↦ ∫ t in (0 : ℝ)..1, D (p, t), ⟨U, hU.mem_nhds hx, ?_⟩, ?_⟩
    · intro p hp
      exact hasFDerivAt_intervalAverage_of_joint f D hU
        (fun y hy t ht ↦ (hf y hy t ht).continuousAt)
        (fun y hy t ht ↦ (hDn y hy t ht).continuousAt) hd hp
    · exact ih D hDn

end PDE.Calculus
