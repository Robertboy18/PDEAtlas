/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flow.Candidate.Regularity

import CAS.ExactTactic

/-!
# A common neighborhood for the matched scalar candidate

The gate uses the same supplied bumps and one fixed base denominator. A matched
base tail and joint continuity of the scalar candidate give a strict fast-state
margin on one product neighborhood of speed/displacement and signed coefficients.
The closed time interval extends past the base terminal time.

The continuity hypothesis follows from `contDiff_prescribed_clock_scalar_candidate` and
`contDiff_prescribed_clock_gate`.
-/

@[expose] public noncomputable section

open Set
open PDE.Analysis.Evolution
open scoped BigOperators Topology

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

/-- The same scalar candidate stays above the fixed nonnegative threshold on a
closed tail, uniformly on one product of open neighborhoods. Both factors can be
restricted to previously chosen neighborhoods. Matching is imposed only at
`((0, 0), cStar)`; nearby coefficients remain arbitrary signed selections.

The base tail hypothesis is the conclusion of `prescribed_clock_selected_matched_tail` with endpoint
`Hmax`. Its restriction to times at most `τ0` supplies the compact base margin. The open time factor
then extends that margin beyond `τ0`. -/
theorem exists_prescribed_clock_matched_neighborhood {F : ℝ × (ℝ × ℝ) → ℝ × ℝ} {L Bhit : ℝ × ℝ → ℝ}
    {β : Fin 3 → ℝ → ℝ} {cStar : Fin 3 → ℝ} {N : Set (ℝ × ℝ)} {V : Set (Fin 3 → ℝ)}
    {B rDown τ0 Hmax : ℝ} (hN : IsOpen N) (hbase : (0, 0) ∈ N) (hV : IsOpen V) (hcStar : cStar ∈ V)
    (hHmax : τ0 < Hmax) (hB : 0 ≤ B) (hmargin : B < (F (τ0, (0, 0))).2) :
    let D0 := parameterizedClockPassageData L Bhit (0, 0)
    let b : (Fin 3 → ℝ) × ℝ → ℝ := fun q ↦
      (Ioo (205 : ℝ) (2051 / 10)).indicator
        (fun y ↦ (∑ j, q.1 j * β j y) / D0.wMinus y) q.2
    let xhat : ℝ × ((ℝ × ℝ) × (Fin 3 → ℝ)) → ℝ := fun q ↦
      (F (q.1, q.2.1)).2 * scalarLinearSolution (fun _ ↦ 4)
        (fun s ↦ b (q.2.2, (F (s, q.2.1)).1)) 0 0 q.1
    Continuous xhat →
    EqOn (fun t ↦ xhat (t, ((0, 0), cStar)))
      (fun t ↦ (F (τ0, (0, 0))).2 * Real.exp (2 * (τ0 - t))) (Icc rDown Hmax) →
    ∃ (H : ℝ) (N' : Set (ℝ × ℝ)) (V' : Set (Fin 3 → ℝ)),
      H ∈ Ioo τ0 Hmax ∧ IsOpen N' ∧ (0, 0) ∈ N' ∧ N' ⊆ N ∧
        IsOpen V' ∧ cStar ∈ V' ∧ V' ⊆ V ∧
        ∀ p ∈ N', ∀ c ∈ V', ∀ t ∈ Icc rDown H, B < xhat (t, (p, c)) := by
  intro D0 b xhat hcont htail
  -- Below `rDown` a short enough time window leaves `Icc rDown H` empty.
  rcases lt_or_ge τ0 rDown with hτr | hrτ
  · have hm := lt_min hτr hHmax
    refine ⟨(τ0 + min rDown Hmax) / 2, N, V, ⟨by linarith, by linarith [min_le_right rDown Hmax]⟩,
      hN, hbase, subset_rfl, hV, hcStar, subset_rfl, fun p _ c _ t ht ↦ ?_⟩
    linarith [ht.1.trans ht.2, min_le_left rDown Hmax]
  let Ω : Set (((ℝ × ℝ) × (Fin 3 → ℝ)) × ℝ) := {q | B < xhat (q.2, q.1)}
  have hΩ : IsOpen Ω :=
    isOpen_lt continuous_const (hcont.comp (continuous_snd.prodMk continuous_fst))
  have hbaseTube : {(((0, 0) : ℝ × ℝ), cStar)} ×ˢ Icc rDown τ0 ⊆ Ω := by
    rintro ⟨p, t⟩ ⟨rfl, ht : t ∈ Icc rDown τ0⟩
    change B < xhat (t, ((0, 0), cStar))
    rw [show xhat (t, ((0, 0), cStar)) = _ from htail ⟨ht.1, ht.2.trans hHmax.le⟩]
    exact hmargin.trans_le (le_mul_of_one_le_right (hB.trans hmargin.le)
      (Real.one_le_exp (by linarith [ht.2])))
  obtain ⟨W, J, hW, hJ, hbaseW, htimesJ, htube⟩ := generalized_tube_lemma
      (s := {(((0, 0) : ℝ × ℝ), cStar)}) (t := Icc rDown τ0)
      isCompact_singleton isCompact_Icc hΩ hbaseTube
  have hτnhds : J ∩ Iio Hmax ∈ 𝓝[≥] τ0 :=
    nhdsWithin_le_nhds ((hJ.inter isOpen_Iio).mem_nhds ⟨htimesJ ⟨hrτ, le_rfl⟩, hHmax⟩)
  obtain ⟨H, hτH, hinterval⟩ := mem_nhdsGE_iff_exists_Icc_subset.mp hτnhds
  have htimesExtended : Icc rDown H ⊆ J := fun t ht ↦ (le_total t τ0).elim
    (fun h ↦ htimesJ ⟨ht.1, h⟩) fun h ↦ (hinterval ⟨h, ht.2⟩).1
  obtain ⟨N0, V0, hN0, hbaseN0, hV0, hcV0, hproduct⟩ :=
    mem_nhds_prod_iff'.mp (hW.mem_nhds (hbaseW (mem_singleton _)))
  exact ⟨H, N ∩ N0, V ∩ V0, ⟨hτH, (hinterval ⟨hτH.le, le_rfl⟩).2⟩, hN.inter hN0,
    ⟨hbase, hbaseN0⟩, (fun _ hp ↦ hp.1), hV.inter hV0, ⟨hcStar, hcV0⟩, (fun _ hc ↦ hc.1),
    fun p hp c hc t ht ↦
      htube (show ((p, c), t) ∈ W ×ˢ J from ⟨hproduct ⟨hp.2, hc.2⟩, htimesExtended ht⟩)⟩

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
