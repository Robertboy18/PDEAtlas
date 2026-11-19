/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Composition.AbsoluteValue
import PDE.Analysis.MeasureTheory.DominatedLp
import PDE.Spaces.Sobolev.GraphSpace.Topology.Convergence

/-!
# Strong continuity of Sobolev positive parts

For every finite exponent `p ≥ 1`, taking the positive part is continuous
in the full `W¹ᵖ` norm. The derivative is the original derivative on the
positive set and zero elsewhere. At points where the limiting value is zero,
Stampacchia's theorem makes the limiting derivative zero too. Vitali convergence
then handles the moving positive sets, including the endpoint `p = 1`.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace

open Filter MeasureTheory Set
open scoped ENNReal Topology Sobolev

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Taking the positive part commutes with the base projection. -/
theorem positivePart_base (U : W^{1,p}(ℝ^n)) :
    wkpCoordinateCLM (baseIndex n 1) (positivePart U) =
      Lp.posPart (wkpCoordinateCLM (baseIndex n 1) U) := by
  apply Lp.ext
  exact (positivePart_base_ae U).trans (Lp.coeFn_posPart _).symm

/-- Positive parts are continuous in the full finite-exponent Sobolev norm. -/
theorem continuous_positivePart (hp : p ≠ ∞) :
    Continuous (positivePart (n := n) (p := p)) := by
  rw [continuous_iff_seqContinuous]
  intro U V hU
  let b : W^{1,p}(ℝ^n) → DerivLp n p Set.univ :=
    wkpCoordinateCLM (baseIndex n 1)
  have hb : Tendsto (fun j ↦ b (U j)) atTop (𝓝 (b V)) :=
    ((wkpCoordinateCLM (baseIndex n 1)).continuous.tendsto V).comp hU
  apply tendsto_wkp_of_coordinate_eLpNorm
  intro a
  rcases a.eq_baseIndex_or_eq_singleDerivIndex with ha | ⟨i, ha⟩
  · subst a
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp
    simpa only [Function.comp_def, b, positivePart_base] using
      Lp.continuous_posPart.continuousAt.tendsto.comp hb
  · subst a
    let d : W^{1,p}(ℝ^n) → DerivLp n p Set.univ :=
      wkpCoordinateCLM (singleDerivIndex n i)
    have hd : Tendsto (fun j ↦ d (U j)) atTop (𝓝 (d V)) :=
      ((wkpCoordinateCLM (singleDerivIndex n i)).continuous.tendsto V).comp hU
    have hbound (W : W^{1,p}(ℝ^n)) :
        ∀ᵐ x ∂domainMeasure n Set.univ,
          ‖(d (positivePart W) : ℝ^n → ℝ) x‖ ≤ ‖(d W : ℝ^n → ℝ) x‖ := by
      filter_upwards [positivePart_derivative_indicator_ae W i] with x hx
      change (d (positivePart W) : ℝ^n → ℝ) x = _ at hx
      rw [hx]
      split_ifs <;> simp [d]
    obtain ⟨_, hui, hut⟩ := (tendstoInMeasure_iff_tendsto_Lp
      (Fact.out : 1 ≤ p) hp (fun j ↦ Lp.memLp (d (U j))) (Lp.memLp (d V))).mpr
        ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp hd)
    have huiP := hui.mono_norm
      (fun j ↦ Lp.aestronglyMeasurable (d (positivePart (U j)))) (fun j ↦ hbound (U j))
    have hutP := hut.mono_norm
      (fun j ↦ Lp.aestronglyMeasurable (d (positivePart (U j)))) (fun j ↦ hbound (U j))
    refine tendsto_of_subseq_tendsto fun ns hns ↦ ?_
    obtain ⟨ms, hms, hbAE⟩ :=
      ((tendstoInMeasure_of_tendsto_Lp hb).comp hns).exists_seq_tendsto_ae
    obtain ⟨ks, hks, hdAE⟩ :=
      ((tendstoInMeasure_of_tendsto_Lp hd).comp (hns.comp hms.tendsto_atTop)).exists_seq_tendsto_ae
    refine ⟨fun j ↦ ms (ks j), tendsto_Lp_of_tendsto_ae (Fact.out : 1 ≤ p) hp
      (fun j ↦ Lp.aestronglyMeasurable (d (positivePart (U (ns (ms (ks j)))))))
      (Lp.memLp (d (positivePart V)))
      (huiP.comp (fun j ↦ ns (ms (ks j)))) (hutP.comp (fun j ↦ ns (ms (ks j)))) ?_⟩
    filter_upwards [hbAE, hdAE,
      ae_all_iff.mpr (fun j ↦ positivePart_derivative_indicator_ae (U (ns (ms (ks j)))) i),
      positivePart_derivative_indicator_ae V i,
      derivative_eq_zero_ae_of_base_eq_zero V i] with x hbx hdx hPx hPVx hzero
    change Tendsto (fun j ↦ (d (positivePart (U (ns (ms (ks j))))) : ℝ^n → ℝ) x)
      atTop (𝓝 ((d (positivePart V) : ℝ^n → ℝ) x))
    change (d (positivePart V) : ℝ^n → ℝ) x =
      if 0 < (b V : ℝ^n → ℝ) x then (d V : ℝ^n → ℝ) x else 0 at hPVx
    change ∀ j, (d (positivePart (U (ns (ms (ks j))))) : ℝ^n → ℝ) x =
      if 0 < (b (U (ns (ms (ks j)))) : ℝ^n → ℝ) x then
        (d (U (ns (ms (ks j)))) : ℝ^n → ℝ) x else 0 at hPx
    rw [hPVx]
    have hb' := hbx.comp hks.tendsto_atTop
    simp only [Function.comp_def] at hb' hdx
    rcases lt_trichotomy ((b V : ℝ^n → ℝ) x) 0 with hneg | hz | hpos
    · rw [ite_eq_right (not_lt.mpr hneg.le)]
      apply tendsto_const_nhds.congr'
      filter_upwards [hb'.eventually (gt_mem_nhds hneg)] with j hj
      rw [hPx j, ite_eq_right (not_lt.mpr hj.le)]
    · rw [ite_eq_right (show ¬ 0 < (b V : ℝ^n → ℝ) x by simp [hz])]
      have hdx0 : Tendsto (fun j ↦ (d (U (ns (ms (ks j)))) : ℝ^n → ℝ) x) atTop (𝓝 0) := by
        simpa only [show (d V : ℝ^n → ℝ) x = 0 from hzero hz] using hdx
      apply squeeze_zero_norm (fun j ↦ ?_) (by simpa using hdx0.norm)
      rw [hPx j]
      split_ifs <;> simp [d]
    · rw [ite_eq_left hpos]
      apply hdx.congr'
      filter_upwards [hb'.eventually (lt_mem_nhds hpos)] with j hj
      rw [hPx j, ite_eq_left hj]

end SobolevSpace.GraphSpace
