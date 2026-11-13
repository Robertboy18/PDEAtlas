/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Autonomous.Bounded.Existence
public import PDE.Analysis.Evolution.ODE.Autonomous.Uniqueness
public import Mathlib.Dynamics.Flow

/-!
# Global flows of bounded autonomous fields

Finite Picard–Lindelöf families agree wherever their initial balls and time intervals
overlap. Around every state-time pair, the chosen global family equals one fixed
larger finite family. This establishes joint continuity and ordinary time derivatives,
including at time zero. Autonomous uniqueness then gives the flow law.
-/

@[expose] public noncomputable section

open Filter Function Metric Set
open scoped Topology

namespace PDE.Analysis.Evolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A bounded field Lipschitz on bounded balls has one jointly continuous family of
whole-line classical solutions, with the prescribed initial state. -/
theorem exists_continuous_solution_family_of_bounded {F : E → E} {M : NNReal}
    (hbound : ∀ x, ‖F x‖ ≤ M)
    (hF : ∀ R : ℝ, 0 < R → ∃ K : NNReal, LipschitzOnWith K F (closedBall 0 R)) :
    ∃ β : E × ℝ → E, Continuous β ∧ (∀ x, β (x, 0) = x) ∧
      ∀ x t, HasDerivAt (fun s ↦ β (x, s)) (F (β (x, t))) t := by
  choose α hα hc using fun N : NNReal ↦
    exists_continuousOn_solution_family_of_bounded hbound hF N N
  have hcohere (S T : NNReal) (hS : 0 < S) (hT : 0 < T) (x : E)
      (hxS : ‖x‖ ≤ S) (hxT : ‖x‖ ≤ T) (t : ℝ)
      (htS : |t| ≤ S) (htT : |t| ≤ T) : α S (x, t) = α T (x, t) := by
    let U : ℝ := min (S : ℝ) T
    have hU : 0 < U := lt_min hS hT
    have hUS : U ≤ S := min_le_left _ _
    have hUT : U ≤ T := min_le_right _ _
    have hxS' : x ∈ closedBall (0 : E) S := by simpa using hxS
    have hxT' : x ∈ closedBall (0 : E) T := by simpa using hxT
    have hfS := (hα S x hxS').2
    have hfT := (hα T x hxT').2
    apply eqOn_Icc_of_hasDerivAt_of_lipschitzOn_balls hF
      (a := -U) (b := U) (t₀ := 0) ⟨neg_neg_of_pos hU, hU⟩
      ((HasDerivWithinAt.continuousOn hfS).mono
        (Icc_subset_Icc (neg_le_neg hUS) hUS)) ?_
      ((HasDerivWithinAt.continuousOn hfT).mono
        (Icc_subset_Icc (neg_le_neg hUT) hUT)) ?_
      ((hα S x hxS').1.trans (hα T x hxT').1.symm)
    · exact abs_le.mp (le_min htS htT)
    · intro s hs
      have hsS : s ∈ Ioo (-(S : ℝ)) S :=
        ⟨(neg_le_neg hUS).trans_lt hs.1, hs.2.trans_le hUS⟩
      exact (hfS s ⟨hsS.1.le, hsS.2.le⟩).hasDerivAt
        (Icc_mem_nhds hsS.1 hsS.2)
    · intro s hs
      have hsT : s ∈ Ioo (-(T : ℝ)) T :=
        ⟨(neg_le_neg hUT).trans_lt hs.1, hs.2.trans_le hUT⟩
      exact (hfT s ⟨hsT.1.le, hsT.2.le⟩).hasDerivAt
        (Icc_mem_nhds hsT.1 hsT.2)
  let radius (p : E × ℝ) : NNReal := ⟨‖p.1‖ + |p.2| + 1, by positivity⟩
  have hrpos (p : E × ℝ) : 0 < radius p := by
    change (0 : ℝ) < ‖p.1‖ + |p.2| + 1
    positivity
  have hrx (p : E × ℝ) : ‖p.1‖ < radius p := by
    change ‖p.1‖ < ‖p.1‖ + |p.2| + 1
    linarith [abs_nonneg p.2]
  have hrt (p : E × ℝ) : |p.2| < radius p := by
    change |p.2| < ‖p.1‖ + |p.2| + 1
    linarith [norm_nonneg p.1]
  let β (p : E × ℝ) := α (radius p) p
  have heq (T : NNReal) (hT : 0 < T) (p : E × ℝ)
      (hx : ‖p.1‖ ≤ T) (ht : |p.2| ≤ T) : β p = α T p :=
    hcohere (radius p) T (hrpos p) hT p.1 (hrx p).le hx p.2 (hrt p).le ht
  have hlocal (T : NNReal) (hT : 0 < T) (p : E × ℝ)
      (hx : ‖p.1‖ < T) (ht : |p.2| < T) : β =ᶠ[𝓝 p] α T := by
    have hmem : ball (0 : E) T ×ˢ Ioo (-(T : ℝ)) T ∈ 𝓝 p :=
      (isOpen_ball.prod isOpen_Ioo).mem_nhds ⟨by simpa using hx, abs_lt.mp ht⟩
    filter_upwards [hmem] with q hq
    exact heq T hT q (by
      exact (show ‖q.1‖ < T by simpa using hq.1).le)
      (abs_le.mpr ⟨hq.2.1.le, hq.2.2.le⟩)
  refine ⟨β, ?_, ?_, ?_⟩
  · apply continuous_iff_continuousAt.mpr
    intro p
    let T := radius p
    have hmem : ball (0 : E) T ×ˢ Ioo (-(T : ℝ)) T ∈ 𝓝 p :=
      (isOpen_ball.prod isOpen_Ioo).mem_nhds
        ⟨by simpa using hrx p, abs_lt.mp (hrt p)⟩
    have hclosed : closedBall (0 : E) T ×ˢ Icc (-(T : ℝ)) T ∈ 𝓝 p :=
      mem_of_superset hmem (fun _ hq ↦
        ⟨ball_subset_closedBall hq.1, ⟨hq.2.1.le, hq.2.2.le⟩⟩)
    exact ((hc T).continuousAt hclosed).congr_of_eventuallyEq
      (hlocal T (hrpos p) p (hrx p) (hrt p))
  · intro x
    exact (hα (radius (x, 0)) x (by simpa using (hrx (x, 0)).le)).1
  · intro x t
    let T := radius (x, t)
    have ht : t ∈ Ioo (-(T : ℝ)) T := abs_lt.mp (hrt (x, t))
    have hd := ((hα T x (by simpa using (hrx (x, t)).le)).2 t
      ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    have hevent : (fun s ↦ β (x, s)) =ᶠ[𝓝 t] fun s ↦ α T (x, s) :=
      (hlocal T (hrpos (x, t)) (x, t) (hrx (x, t)) (hrt (x, t))).comp_tendsto
        (continuous_const.prodMk continuous_id).continuousAt
    rw [heq T (hrpos (x, t)) (x, t) (hrx (x, t)).le (hrt (x, t)).le]
    exact hd.congr_of_eventuallyEq hevent

/-- A bounded autonomous field Lipschitz on every bounded ball generates a
continuous two-sided flow, with the vector field as its ordinary time derivative. -/
theorem exists_flow_hasDerivAt_of_bounded {F : E → E} {M : NNReal}
    (hbound : ∀ x, ‖F x‖ ≤ M)
    (hF : ∀ R : ℝ, 0 < R → ∃ K : NNReal, LipschitzOnWith K F (closedBall 0 R)) :
    ∃ Φ : Flow ℝ E, ∀ x t, HasDerivAt (fun s ↦ Φ s x) (F (Φ t x)) t := by
  obtain ⟨β, hc, hz, hd⟩ := exists_continuous_solution_family_of_bounded hbound hF
  have hadd (s t : ℝ) (x : E) : β (x, s + t) = β (β (x, t), s) := by
    have heq : (fun r ↦ β (x, r + t)) = fun r ↦ β (β (x, t), r) := by
      apply eq_of_hasDerivAt_of_lipschitzOn_balls hF (t₀ := 0) ?_
        (hd (β (x, t))) (by simp only [zero_add, hz])
      intro r
      simpa only [one_smul, Function.comp_def, id_eq] using
        (hd x (r + t)).scomp r ((hasDerivAt_id r).add_const t)
    exact congrFun heq s
  exact ⟨{ toFun := fun t x ↦ β (x, t)
           cont' := hc.comp continuous_swap
           map_add' := hadd
           map_zero' := hz }, hd⟩

end PDE.Analysis.Evolution
