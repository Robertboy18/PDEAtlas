/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Atlas.Geometric.GraphCover
public import PDE.Spaces.Sobolev.Boundary.Flux.Graph.SlabBound

/-!
# Linear volume growth of boundary distance collars

A nearest frontier point and a Lebesgue number select a patch in the finite C¹
graph cover. A Lipschitz graph-height bound places the distance collar in slabs
whose thickness is proportional to its width. Finite subadditivity finishes.
-/

@[expose] public noncomputable section

open Set Metric
open scoped Topology

namespace SobolevSpace.Boundary

open Trace.HalfSpace Flux.Graph

/-- Physical graph coordinates associated with the tangential-normal
coordinates retained by a finite graph cover. -/
def C1GraphBoundaryCover.linearCoordinates {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    (c : C1GraphBoundaryCover m Ω) (i : Fin c.N) :
    ℝ^(m + 1) ≃L[ℝ] ℝ^(m + 1) :=
  (c.coordinates i).trans tangentialNormalContinuousLinearEquiv.symm

/-- Graph height in the original tangential-normal coordinates. -/
theorem C1GraphBoundaryCover.linearGraphHeight_eq {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    (c : C1GraphBoundaryCover m Ω) (i : Fin c.N) (x : ℝ^(m + 1)) :
    linearGraphHeight (c.linearCoordinates i) (c.height i) x =
      (c.coordinates i x).2 - c.height i (c.coordinates i x).1 := by
  change (tangentialNormalContinuousLinearEquiv (c.linearCoordinates i x)).2 -
    c.height i (tangentialNormalContinuousLinearEquiv (c.linearCoordinates i x)).1 = _
  simp only [linearCoordinates, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.apply_symm_apply]

/-- A sufficiently thin interior distance collar is contained in a finite
union of graph slabs whose thicknesses are proportional to the collar width. -/
theorem C1GraphBoundaryCover.exists_pos_collar_subset_slabs
    {m : ℕ} {Ω : Set (ℝ^(m + 1))} (c : C1GraphBoundaryCover m Ω) :
    ∃ δ > 0, ∃ L : Fin c.N → ℝ, (∀ i, 0 < L i) ∧
      ∀ r ∈ Ioo 0 δ, ∀ x ∈ Ω, infDist x Ωᶜ ≤ r →
        ∃ i, linearGraphHeight (c.linearCoordinates i) (c.height i) x ∈ Ioo 0 (L i * r) := by
  have hcompact : IsCompact (frontier Ω) :=
    c.bounded.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨δ, hδ, hcover⟩ := lebesgue_number_lemma_of_metric hcompact
    c.boundaryPatch_open c.frontier_subset_iUnion
  obtain ⟨R, _, hR⟩ := c.bounded.isCompact_closure.isBounded.subset_closedBall_lt
    0 (0 : ℝ^(m + 1))
  have hheight (i : Fin c.N) :
      ContDiff ℝ 1 (linearGraphHeight (c.linearCoordinates i) (c.height i)) := by
    have heq : linearGraphHeight (c.linearCoordinates i) (c.height i) =
        fun x ↦ (c.coordinates i x).2 - c.height i (c.coordinates i x).1 :=
      funext (c.linearGraphHeight_eq i)
    rw [heq]
    exact (c.coordinates i).contDiff.snd.sub
      ((c.height_contDiff i).comp (c.coordinates i).contDiff.fst)
  have hlip (i : Fin c.N) := (hheight i).contDiffOn.exists_lipschitzOnWith
    (by norm_num) (convex_closedBall (0 : ℝ^(m + 1)) R) (isCompact_closedBall _ _)
  choose L hL using hlip
  refine ⟨δ, hδ, fun i ↦ (L i : ℝ) + 1, fun i ↦ by positivity, ?_⟩
  intro r hr x hx hd
  have hΩne : Ω ≠ univ := by
    intro heq
    exact NormedSpace.unbounded_univ ℝ (ℝ^(m + 1)) (heq ▸ c.bounded)
  obtain ⟨z, hz, hdist⟩ := exists_mem_frontier_infDist_compl_eq_dist hx hΩne
  obtain ⟨i, hi⟩ := hcover z hz
  have hzpatch : z ∈ c.boundaryPatch i := hi (mem_ball_self hδ)
  have hxpatch : x ∈ c.boundaryPatch i := hi (by
    rw [mem_ball, ← hdist]
    exact hd.trans_lt hr.2)
  have hside : ∀ y ∈ c.boundaryPatch i,
      y ∈ Ω ↔ y ∈ linearEpigraph (c.linearCoordinates i) (c.height i) := by
    intro y hy
    have hh := c.linearGraphHeight_eq i y
    have he : y ∈ linearEpigraph (c.linearCoordinates i) (c.height i) ↔
        0 < linearGraphHeight (c.linearCoordinates i) (c.height i) y := by
      exact sub_pos.symm
    rw [he, hh, sub_pos]
    exact c.mem_iff_epigraph i y hy
  have hzheight := (mem_frontier_iff_graphHeight_eq_zero (c.boundaryPatch_open i)
    (c.linearCoordinates i) (c.height i) (c.height_contDiff i).continuous
    hside hzpatch).mp hz
  have hxheight : 0 < linearGraphHeight (c.linearCoordinates i) (c.height i) x := by
    rw [c.linearGraphHeight_eq, sub_pos]
    exact (c.mem_iff_epigraph i x hxpatch).mp hx
  have hbound := (hL i).dist_le_mul x (hR (subset_closure hx))
    z (hR (frontier_subset_closure hz))
  rw [hzheight, dist_zero_right, Real.norm_eq_abs, abs_of_pos hxheight, ← hdist] at hbound
  refine ⟨i, hxheight, ?_⟩
  calc
    linearGraphHeight (c.linearCoordinates i) (c.height i) x ≤
        (L i : ℝ) * r := hbound.trans (mul_le_mul_of_nonneg_left hd (L i).coe_nonneg)
    _ < ((L i : ℝ) + 1) * r := mul_lt_mul_of_pos_right (lt_add_one _) hr.1

open MeasureTheory Filter Flux.Graph
open scoped ENNReal

/-- An interior collar of a bounded domain with a finite C¹ graph cover has
volume bounded by a constant times its thickness. -/
theorem C1GraphBoundaryCover.exists_pos_volume_collar_le
    {m : ℕ} {Ω : Set (ℝ^(m + 1))} (c : C1GraphBoundaryCover m Ω) :
    ∃ C > 0, ∀ r > 0,
      volume.real {x : ℝ^(m + 1) | x ∈ Ω ∧ Metric.infDist x Ωᶜ ≤ r} ≤ C * r := by
  classical
  obtain ⟨δ, hδ, L, hL, hcover⟩ := c.exists_pos_collar_subset_slabs
  obtain ⟨f, _, hfOne, _, hfRange⟩ :=
    TestFunction.exists_eq_one_on_compact_finiteDimensional isOpen_univ
      c.bounded.isCompact_closure (subset_univ _)
  have hf : Continuous (f : ℝ^(m + 1) → ℝ) := f.contDiff.continuous
  have hfi : Integrable (f : ℝ^(m + 1) → ℝ) :=
    hf.integrable_of_hasCompactSupport f.hasCompactSupport
  have hfnonneg : ∀ x, 0 ≤ f x := fun x ↦ (hfRange x).1
  have hslab (i : Fin c.N) := exists_pos_integral_linearGraphSlab_le
    (c.linearCoordinates i) (c.height_contDiff i).continuous hf f.hasCompactSupport hfnonneg
  choose B hB hslabBound using hslab
  let S : ℝ := ∑ i, B i * L i
  let V : ℝ := volume.real Ω
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ ↦ mul_nonneg (hB i).le (hL i).le
  have hV : 0 ≤ V := measureReal_nonneg
  let C : ℝ := S + 1 + V / δ
  have hfrac : 0 ≤ V / δ := div_nonneg hV hδ.le
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨C, hC, fun r hr ↦ ?_⟩
  let E : Set (ℝ^(m + 1)) := {x | x ∈ Ω ∧ Metric.infDist x Ωᶜ ≤ r}
  have hEΩ : E ⊆ Ω := fun _ hx ↦ hx.1
  have hΩfinite : volume Ω ≠ ∞ := c.bounded.measure_lt_top.ne
  change volume.real E ≤ C * r
  by_cases hsmall : r < δ
  · let H : Fin c.N → Set (ℝ^(m + 1)) := fun i ↦
      {x | linearGraphHeight (c.linearCoordinates i) (c.height i) x ∈ Ioo 0 (L i * r)}
    let F : Fin c.N → Set (ℝ^(m + 1)) := fun i ↦ Ω ∩ H i
    have hFmeas (i : Fin c.N) : MeasurableSet (F i) := by
      have hheight : Continuous
          (linearGraphHeight (c.linearCoordinates i) (c.height i)) := by
        have heq : linearGraphHeight (c.linearCoordinates i) (c.height i) =
            fun x ↦ (c.coordinates i x).2 - c.height i (c.coordinates i x).1 :=
          funext (c.linearGraphHeight_eq i)
        rw [heq]
        exact (c.coordinates i).continuous.snd.sub
          ((c.height_contDiff i).continuous.comp (c.coordinates i).continuous.fst)
      exact c.isOpen.measurableSet.inter (measurableSet_Ioo.preimage hheight.measurable)
    have hsub : E ⊆ ⋃ i, F i := by
      intro x hx
      obtain ⟨i, hi⟩ := hcover r ⟨hr, hsmall⟩ x hx.1 hx.2
      exact mem_iUnion.mpr ⟨i, hx.1, hi⟩
    have hUΩ : (⋃ i, F i) ⊆ Ω := iUnion_subset fun _ ↦ inter_subset_left
    have hUF : volume (⋃ i, F i) ≠ ∞ := measure_ne_top_of_subset hUΩ hΩfinite
    have hlocal (i : Fin c.N) : volume.real (F i) ≤ B i * (L i * r) := by
      have hFeq : volume.real (F i) = ∫ x in F i, f x := by
        calc
          volume.real (F i) = ∫ _ in F i, (1 : ℝ) := by
            rw [setIntegral_const, smul_eq_mul, mul_one]
          _ = ∫ x in F i, f x := by
            apply setIntegral_congr_fun (hFmeas i)
            intro x hx
            exact (hfOne x (subset_closure hx.1)).symm
      rw [hFeq]
      apply le_trans (setIntegral_mono_set hfi.integrableOn
        (Eventually.of_forall hfnonneg)
        (Eventually.of_forall (show F i ⊆ H i from inter_subset_right)))
      exact hslabBound i (L i * r) (mul_pos (hL i) hr)
    calc
      volume.real E ≤ volume.real (⋃ i, F i) := measureReal_mono hsub hUF
      _ ≤ ∑ i, volume.real (F i) := measureReal_iUnion_fintype_le F
      _ ≤ ∑ i, B i * (L i * r) := Finset.sum_le_sum fun i _ ↦ hlocal i
      _ = S * r := by simp only [S, Finset.sum_mul, mul_assoc]
      _ ≤ C * r := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hr.le
  · have hδr : δ ≤ r := le_of_not_gt hsmall
    have hVr : V ≤ (V / δ) * r := by
      have h := mul_le_mul_of_nonneg_left hδr hfrac
      simpa only [div_mul_cancel₀ _ hδ.ne'] using h
    exact (measureReal_mono hEΩ hΩfinite).trans (hVr.trans
      (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hr.le))

/-- A bounded open C¹ domain has linear interior collar-volume growth. -/
theorem HasC1GraphBoundary.exists_pos_volume_collar_le
    {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}
    (hgraph : HasC1GraphBoundary Ω) (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    ∃ C > 0, ∀ r > 0,
      volume.real {x : ℝ^n | x ∈ Ω ∧ Metric.infDist x Ωᶜ ≤ r} ≤ C * r := by
  cases n with
  | zero => exact False.elim (Nat.lt_irrefl 0 Fact.out)
  | succ m =>
    obtain ⟨c⟩ := hgraph.nonempty_c1GraphBoundaryCover hΩ hb
    exact c.exists_pos_volume_collar_le

end SobolevSpace.Boundary
