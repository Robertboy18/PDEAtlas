/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.VectorValued.HalfSpace.Operator
public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.FirstOrder
import PDE.Spaces.Sobolev.Boundary.Trace.VectorValued.HalfSpace.Density
import PDE.Spaces.Sobolev.Calculus.Differentiation.VectorValued.ClassicalToWeak

/-!
# Completion of Banach-valued fractional trace estimates

A uniform fractional boundary estimate for compactly supported ambient `C¹` functions
passes to the Sobolev trace. Compact smooth density supplies the approximants;
boundary `Lp` convergence supplies an almost-everywhere convergent subsequence. Fatou's
lemma retains the smooth constant and the weak partial-derivative energy.

The smooth estimate is a hypothesis here; `Fractional.Estimate` proves it. The Banach
space needs no approximation property.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal Sobolev Topology

namespace SobolevSpace.VectorValued

open GraphSpace

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

namespace Trace.HalfSpace

open SobolevSpace.Trace.HalfSpace

private theorem coordinate_enorm_rpow_eq_lintegral
    {n : ℕ} {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 0 < p)
    (U : W^{1,ENNReal.ofReal p}(⟨ℝ^(n + 1)₊,
      SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩; F))
    {f : ℝ^(n + 1) → F} (hf : ContDiff ℝ 1 f)
    (hbase : (U.val (baseIndex (n + 1) 1) : ℝ^(n + 1) → F)
      =ᵐ[volume.restrict ℝ^(n + 1)₊] f) (i : Fin (n + 1)) :
    ‖∂[i] U‖ₑ ^ p = ∫⁻ x in ℝ^(n + 1)₊, ‖(∂[i] f) x‖ₑ ^ p := by
  rw [enorm_partialDeriv_eq_coordinate]
  let v := U.val (singleDerivIndex (n + 1) i)
  have hv := coordinate_ae_partialDeriv_of_contDiffOn U hf.contDiffOn hbase i
  have hnorm : ‖v‖ₑ ^ p =
      ∫⁻ x, ‖v x‖ₑ ^ p ∂(volume.restrict ℝ^(n + 1)₊) := by
    rw [Lp.enorm_def, eLpNorm_eq_eLpNorm' (by positivity) ENNReal.ofReal_ne_top
      (Lp.aestronglyMeasurable v), ENNReal.toReal_ofReal hp.le]
    exact (lintegral_rpow_enorm_eq_rpow_eLpNorm' hp).symm
  exact hnorm.trans (lintegral_congr_ae (hv.mono fun x hx ↦
    congrArg (fun t : F ↦ ‖t‖ₑ ^ p) hx))

omit [NormedSpace ℝ F] [CompleteSpace F] in
private theorem lintegral_sub_rpow_div_le_liminf
    (n : ℕ) {p a : ℝ} (hp : 0 < p)
    {f : ℕ → ℝ^n → F} {g : ℝ^n → F}
    (hf : ∀ j, AEStronglyMeasurable (f j) (volume : Measure (ℝ^n)))
    (hfg : ∀ᵐ x ∂(volume : Measure (ℝ^n)),
      Tendsto (fun j ↦ f j x) atTop (𝓝 (g x))) :
    (∫⁻ z : ℝ^n × ℝ^n,
      ‖g z.1 - g z.2‖ₑ ^ p / (ENNReal.ofReal ‖z.1 - z.2‖) ^ a
      ∂((volume : Measure (ℝ^n)).prod volume)) ≤
    atTop.liminf (fun j ↦ ∫⁻ z : ℝ^n × ℝ^n,
      ‖f j z.1 - f j z.2‖ₑ ^ p / (ENNReal.ofReal ‖z.1 - z.2‖) ^ a
      ∂((volume : Measure (ℝ^n)).prod volume)) := by
  let E (v : ℝ^n → F) (z : ℝ^n × ℝ^n) :=
    ‖v z.1 - v z.2‖ₑ ^ p / (ENNReal.ofReal ‖z.1 - z.2‖) ^ a
  have hmeas (j : ℕ) :
      AEMeasurable (E (f j)) ((volume : Measure (ℝ^n)).prod volume) := by
    have hd := ((hf j).comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_fst (μ := volume) (ν := volume))).sub
        ((hf j).comp_quasiMeasurePreserving
          (Measure.quasiMeasurePreserving_snd (μ := volume) (ν := volume)))
    exact (hd.enorm.pow_const p).div
      (((measurable_fst.sub measurable_snd).norm.ennreal_ofReal).pow_const a).aemeasurable
  have hfst := (Measure.quasiMeasurePreserving_fst
    (μ := (volume : Measure (ℝ^n))) (ν := (volume : Measure (ℝ^n)))).ae hfg
  have hsnd := (Measure.quasiMeasurePreserving_snd
    (μ := (volume : Measure (ℝ^n))) (ν := (volume : Measure (ℝ^n)))).ae hfg
  have hlim : ∀ᵐ z ∂((volume : Measure (ℝ^n)).prod volume),
      Tendsto (fun j ↦ E (f j) z) atTop (𝓝 (E g z)) := by
    filter_upwards [hfst, hsnd] with z hz₁ hz₂
    by_cases hz : z.1 = z.2
    · simp [E, hz, ENNReal.zero_rpow_of_pos hp]
    · apply ENNReal.Tendsto.div_const
        ((ENNReal.continuous_rpow_const.tendsto _).comp (hz₁.sub hz₂).enorm)
      exact Or.inr (ENNReal.rpow_pos
        (ENNReal.ofReal_pos.mpr (norm_pos_iff.mpr (sub_ne_zero.mpr hz)))
        ENNReal.ofReal_ne_top).ne'
  calc
    _ = ∫⁻ z, atTop.liminf (fun j ↦ E (f j) z)
        ∂((volume : Measure (ℝ^n)).prod volume) :=
      lintegral_congr_ae (hlim.mono fun z hz ↦ hz.liminf_eq.symm)
    _ ≤ _ := lintegral_liminf_le' hmeas

/-- A uniform compact `C¹` fractional estimate passes to the trace.
The smooth estimate is an intermediate premise; density is supplied by the
half-space theorem. The constant and the full weak derivative energy are preserved. -/
theorem lintegral_traceLp_sub_rpow_div_le_of_smooth
    (n : ℕ) (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) (C : ℝ≥0)
    (hsmooth : ∀ f : ℝ^(n + 1) → F, ContDiff ℝ 1 f → HasCompactSupport f →
      (∫⁻ z : ℝ^n × ℝ^n,
        ‖normalSlice f z.1 0 - normalSlice f z.2 0‖ₑ ^ p /
          (ENNReal.ofReal ‖z.1 - z.2‖) ^ ((n : ℝ) + p - 1)
        ∂((volume : Measure (ℝ^n)).prod volume)) ≤
      (C : ℝ≥0∞) * ∑ i : Fin (n + 1),
        ∫⁻ x in ℝ^(n + 1)₊, ‖(∂[i] f) x‖ₑ ^ p)
    (U : W^{1,ENNReal.ofReal p}(⟨ℝ^(n + 1)₊,
      SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩; F)) :
    (∫⁻ z : ℝ^n × ℝ^n,
      ‖traceLp n p hp.le U z.1 - traceLp n p hp.le U z.2‖ₑ ^ p /
        (ENNReal.ofReal ‖z.1 - z.2‖) ^ ((n : ℝ) + p - 1)
      ∂((volume : Measure (ℝ^n)).prod volume)) ≤
    (C : ℝ≥0∞) * ∑ i : Fin (n + 1), ‖∂[i] U‖ₑ ^ p := by
  classical
  let T := traceLp (F := F) n p hp.le
  let energy (v : ℝ^n → F) :=
    ∫⁻ z : ℝ^n × ℝ^n,
      ‖v z.1 - v z.2‖ₑ ^ p /
        (ENNReal.ofReal ‖z.1 - z.2‖) ^ ((n : ℝ) + p - 1)
      ∂((volume : Measure (ℝ^n)).prod volume)
  let bound (V : W^{1,ENNReal.ofReal p}(⟨ℝ^(n + 1)₊,
      SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩; F)) :=
    (C : ℝ≥0∞) * ∑ i : Fin (n + 1), ‖∂[i] V‖ₑ ^ p
  obtain ⟨V, hV, hVlim⟩ := mem_closure_iff_seq_limit.mp
    (dense_compact_smooth (n := n) (F := F) ENNReal.ofReal_ne_top U)
  choose f hf hfc hbase using hV
  have hTlim := (T.continuous.tendsto U).comp hVlim
  obtain ⟨ns, hns, hlim⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hTlim).exists_seq_tendsto_ae
  have hbound (j : ℕ) : energy (T (V j)) ≤ bound (V j) := by
    have hc1 : ContDiff ℝ 1 (f j) := (hf j).of_le (by simp)
    have htrace := traceLp_coeFn_ae hp.le (V j) hc1 (hfc j) (hbase j)
    have hfst := (Measure.quasiMeasurePreserving_fst
      (μ := (volume : Measure (ℝ^n))) (ν := (volume : Measure (ℝ^n)))).ae htrace
    have hsnd := (Measure.quasiMeasurePreserving_snd
      (μ := (volume : Measure (ℝ^n))) (ν := (volume : Measure (ℝ^n)))).ae htrace
    calc
      energy (T (V j)) = energy (fun y ↦ normalSlice (f j) y 0) := by
        apply lintegral_congr_ae
        filter_upwards [hfst, hsnd] with z hz₁ hz₂
        rw [hz₁, hz₂]
      _ ≤ (C : ℝ≥0∞) * ∑ i : Fin (n + 1),
          ∫⁻ x in ℝ^(n + 1)₊, ‖(∂[i] (f j)) x‖ₑ ^ p := hsmooth (f j) hc1 (hfc j)
      _ = bound (V j) := by
        congr 1
        exact Finset.sum_congr rfl fun i _ ↦
          (coordinate_enorm_rpow_eq_lintegral (zero_lt_one.trans hp)
            (V j) hc1 (hbase j) i).symm
  have hboundlim : Tendsto (fun j ↦ bound (V (ns j))) atTop (𝓝 (bound U)) := by
    apply ENNReal.Tendsto.const_mul _ (Or.inr ENNReal.coe_ne_top)
    apply tendsto_finsetSum
    intro i _
    exact (((partialDerivCLM i).continuous.tendsto U).comp
      (hVlim.comp hns.tendsto_atTop)).enorm.ennrpow_const p
  calc
    energy (T U) ≤ atTop.liminf (fun j ↦ energy (T (V (ns j)))) :=
      lintegral_sub_rpow_div_le_liminf n (zero_lt_one.trans hp)
        (fun j ↦ Lp.aestronglyMeasurable _) hlim
    _ ≤ atTop.liminf (fun j ↦ bound (V (ns j))) :=
      Filter.liminf_le_liminf (Eventually.of_forall fun j ↦ hbound (ns j))
    _ = bound U := hboundlim.liminf_eq

end Trace.HalfSpace

end SobolevSpace.VectorValued
