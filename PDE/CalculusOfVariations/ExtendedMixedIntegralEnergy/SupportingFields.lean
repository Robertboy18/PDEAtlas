/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.DominatedLp
public import PDE.Analysis.WeakCompactness
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.MeasureTheory.Function.Holder

/-!
# Lower semicontinuity from locally bounded supporting fields

A supporting affine function need not be integrable on the whole domain. On a finite
measure space, pointwise convergent densities and supporting fields are uniformly bounded
on measurable sets that exhaust almost every point. On each such set, dominated convergence
and the continuous `Lᵠ`–`Lᵖ` pairing give an integral lower bound. Fatou's lemma removes the
truncation. The energy is a nonnegative Lebesgue integral and may be infinite.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace PDE.CalculusOfVariations

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The positive part bounds the integral of a signed integrable minorant. This comparison
also applies when the nonnegative energy on the right is infinite. -/
private theorem ofReal_integral_le_lintegral_ofReal {g : α → ℝ}
    (hg : Integrable g μ) :
    ENNReal.ofReal (∫ x, g x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂μ := by
  calc
    ENNReal.ofReal (∫ x, g x ∂μ) ≤
        ENNReal.ofReal (∫ x, max (g x) 0 ∂μ) :=
      ENNReal.ofReal_le_ofReal (integral_mono hg hg.pos_part fun x ↦ le_max_left _ _)
    _ = ∫⁻ x, ENNReal.ofReal (max (g x) 0) ∂μ :=
      ofReal_integral_eq_lintegral_ofReal hg.pos_part
        (Eventually.of_forall fun x ↦ le_max_right _ _)
    _ = ∫⁻ x, ENNReal.ofReal (g x) ∂μ := by simp

/-- A pointwise convergent sequence is uniformly bounded on measurable sets exhausting
almost every point. No uniform bound on the original sequence is required. -/
private theorem exists_bounded_exhaustion_of_tendsto_ae
    {G : Type*} [NormedAddCommGroup G]
    {f : ℕ → α → G} {g : α → G}
    (hf : ∀ j, StronglyMeasurable (f j)) (hg : StronglyMeasurable g)
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun j ↦ f j x) atTop (𝓝 (g x))) :
    ∃ s : ℕ → Set α, (∀ k, MeasurableSet (s k)) ∧
      (∀ k x, x ∈ s k → ‖g x‖ ≤ (k : ℝ) ∧ ∀ j, ‖f j x‖ ≤ (k : ℝ)) ∧
      (∀ᵐ x ∂μ, ∀ᶠ k in atTop, x ∈ s k) := by
  let s (k : ℕ) : Set α := {x | ‖g x‖ ≤ (k : ℝ)} ∩
    ⋂ j : ℕ, {x | ‖f j x‖ ≤ (k : ℝ)}
  refine ⟨s, ?_, ?_, ?_⟩
  · intro k
    exact (measurableSet_le hg.norm.measurable measurable_const).inter
      (MeasurableSet.iInter fun j ↦
        measurableSet_le (hf j).norm.measurable measurable_const)
  · intro k x hx
    exact ⟨hx.1, fun j ↦ mem_iInter.mp hx.2 j⟩
  · filter_upwards [hfg] with x hx
    obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto (fun j ↦ f j x) hx).exists_norm_le
    obtain ⟨N, hN⟩ := exists_nat_ge (max C ‖g x‖)
    filter_upwards [eventually_ge_atTop N] with k hk
    have hNk : (N : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    refine ⟨(le_max_right C ‖g x‖).trans (hN.trans hNk), mem_iInter.mpr ?_⟩
    intro j
    exact (hC (f j x) (mem_range_self j)).trans
      ((le_max_left C ‖g x‖).trans (hN.trans hNk))

section FiniteMeasure

variable [IsFiniteMeasure μ]

/-- A bounded part of an almost-everywhere convergent sequence converges in every finite
`Lᵖ`. The same measurable set is used for all terms and for the limit. -/
private theorem tendsto_eLpNorm_indicator_of_bound
    {G : Type*} [NormedAddCommGroup G] {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    {f : ℕ → α → G} {g : α → G}
    (hf : ∀ j, StronglyMeasurable (f j)) (hg : StronglyMeasurable g)
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun j ↦ f j x) atTop (𝓝 (g x)))
    {s : Set α} (hs : MeasurableSet s) {C : ℝ} (hC : 0 ≤ C)
    (hfb : ∀ j x, x ∈ s → ‖f j x‖ ≤ C) (hgb : ∀ x, x ∈ s → ‖g x‖ ≤ C) :
    Tendsto (fun j ↦ eLpNorm (s.indicator (f j) - s.indicator g) p μ)
      atTop (𝓝 0) := by
  refine tendsto_Lp_of_tendsto_ae_of_ae_norm_le hp hp_top
    (fun j ↦ ((hf j).indicator hs).aestronglyMeasurable)
    (MemLp.of_bound (hg.indicator hs).aestronglyMeasurable C
      (Eventually.of_forall fun x ↦ by
        rw [norm_indicator_eq_indicator_norm]
        exact Set.indicator_le' hgb (fun _ _ ↦ hC) x))
    (memLp_const C) ?_ ?_
  · intro j
    refine Eventually.of_forall fun x ↦ ?_
    rw [norm_indicator_eq_indicator_norm]
    exact (Set.indicator_le' (hfb j) (fun _ _ ↦ hC) x).trans (le_abs_self C)
  · filter_upwards [hfg] with x hx
    by_cases hxs : x ∈ s
    · simpa only [indicator_of_mem hxs] using hx
    · simp only [indicator_of_notMem hxs]
      exact tendsto_const_nhds

/-- On a finite measure space, a measurable bounded part of a function belongs to every
`Lᵖ`. The bound is needed only on the set retained by the indicator. -/
private theorem memLp_indicator_of_bound
    {G : Type*} [NormedAddCommGroup G] {r : ℝ≥0∞}
    {s : Set α} (hs : MeasurableSet s) {C : ℝ} (hC : 0 ≤ C)
    {f : α → G} (hf : StronglyMeasurable f) (hb : ∀ x, x ∈ s → ‖f x‖ ≤ C) :
    MemLp (s.indicator f) r μ := by
  refine MemLp.of_bound (hf.indicator hs).aestronglyMeasurable C ?_
  refine Eventually.of_forall fun x ↦ ?_
  rw [norm_indicator_eq_indicator_norm]
  exact Set.indicator_le' hb (fun _ _ ↦ hC) x

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

/-- On a set where the density and its supporting field are uniformly bounded, the
supporting affine functions give a lower bound for the limiting extended energy. -/
private theorem lintegral_indicator_le_liminf_of_bounded_supports
    (hq_top : q ≠ ∞)
    {a : ℕ → α → ℝ} {aLimit : α → ℝ}
    {d : ℕ → α → H} {dLimit : α → H} {e : ℕ → α → ℝ}
    (ha : ∀ j, StronglyMeasurable (a j)) (haLimit : StronglyMeasurable aLimit)
    (hd : ∀ j, StronglyMeasurable (d j)) (hdLimit : StronglyMeasurable dLimit)
    (hae : ∀ᵐ x ∂μ, Tendsto (fun j ↦ a j x) atTop (𝓝 (aLimit x)))
    (hde : ∀ᵐ x ∂μ, Tendsto (fun j ↦ d j x) atTop (𝓝 (dLimit x)))
    (ha_nonneg : ∀ᵐ x ∂μ, 0 ≤ aLimit x)
    {v : ℕ → Lp H p μ} {vLimit : Lp H p μ}
    (hv : Tendsto (fun j ↦ toWeakSpace ℝ (Lp H p μ) (v j)) atTop
      (𝓝 (toWeakSpace ℝ (Lp H p μ) vLimit)))
    (R : ℝ) (hvR : ∀ j, ‖v j‖ ≤ R)
    (hsupport : ∀ j, ∀ᵐ x ∂μ,
      a j x + inner ℝ (d j x) (v j x - vLimit x) ≤ e j x)
    {s : Set α} (hs : MeasurableSet s) {C : ℝ} (hC : 0 ≤ C)
    (hab : ∀ j x, x ∈ s → ‖a j x‖ ≤ C)
    (haLimitb : ∀ x, x ∈ s → ‖aLimit x‖ ≤ C)
    (hdb : ∀ j x, x ∈ s → ‖d j x‖ ≤ C)
    (hdLimitb : ∀ x, x ∈ s → ‖dLimit x‖ ≤ C) :
    (∫⁻ x, ENNReal.ofReal (s.indicator aLimit x) ∂μ) ≤
      liminf (fun j ↦ ∫⁻ x, ENNReal.ofReal (e j x) ∂μ) atTop := by
  have haint (j : ℕ) : Integrable (s.indicator (a j)) μ :=
    memLp_one_iff_integrable.mp (memLp_indicator_of_bound hs hC (ha j) (hab j))
  have haLimitint : Integrable (s.indicator aLimit) μ :=
    memLp_one_iff_integrable.mp (memLp_indicator_of_bound hs hC haLimit haLimitb)
  have haint_tendsto : Tendsto (fun j ↦ ∫ x, s.indicator (a j) x ∂μ) atTop
      (𝓝 (∫ x, s.indicator aLimit x ∂μ)) := by
    simpa only [Measure.restrict_univ] using
      tendsto_setIntegral_of_L1' (s.indicator aLimit)
        (Eventually.of_forall haint)
        (tendsto_eLpNorm_indicator_of_bound (p := 1) le_rfl (by simp)
          ha haLimit hae hs hC hab haLimitb) univ
  let D (j : ℕ) : Lp H q μ :=
    (memLp_indicator_of_bound hs hC (hd j) (hdb j)).toLp (s.indicator (d j))
  let DLimit : Lp H q μ :=
    (memLp_indicator_of_bound hs hC hdLimit hdLimitb).toLp (s.indicator dLimit)
  have hD : Tendsto D atTop (𝓝 DLimit) := by
    exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ _).mpr
      (tendsto_eLpNorm_indicator_of_bound (Fact.out : 1 ≤ q) hq_top
        hd hdLimit hde hs hC hdb hdLimitb)
  let P : Lp H q μ →L[ℝ] Lp H p μ →L[ℝ] ℝ :=
    (innerSL ℝ : H →L[ℝ] H →L[ℝ] ℝ).lpPairing μ q p
  have hell : Tendsto (fun j ↦ P (D j)) atTop (𝓝 (P DLimit)) :=
    P.continuous.continuousAt.tendsto.comp hD
  have hpair := PDE.Analysis.WeakCompactness.tendsto_dual_apply_of_tendsto_strong_weak
    hell hv R hvR
  have hfixed : Tendsto (fun j ↦ P (D j) vLimit) atTop (𝓝 (P DLimit vLimit)) :=
    (ContinuousLinearMap.apply ℝ ℝ vLimit).continuous.continuousAt.tendsto.comp hell
  have hcorrection : Tendsto (fun j ↦ P (D j) (v j - vLimit)) atTop (𝓝 0) := by
    simpa only [map_sub, sub_self] using hpair.sub hfixed
  have htotal := haint_tendsto.add hcorrection
  have hminorant (j : ℕ) :
      ENNReal.ofReal ((∫ x, s.indicator (a j) x ∂μ) + P (D j) (v j - vLimit)) ≤
        ∫⁻ x, ENNReal.ofReal (e j x) ∂μ := by
    have hwork : Integrable (fun x ↦ inner ℝ (D j x) ((v j - vLimit) x)) μ :=
      memLp_one_iff_integrable.mp
        ((innerSL ℝ).memLp_of_bilin 1 (Lp.memLp (D j)) (Lp.memLp (v j - vLimit)))
    have heq : (∫ x, s.indicator (a j) x ∂μ) + P (D j) (v j - vLimit) =
        ∫ x, s.indicator (a j) x + inner ℝ (D j x) ((v j - vLimit) x) ∂μ := by
      change (∫ x, s.indicator (a j) x ∂μ) +
        (innerSL ℝ).lpPairing μ q p (D j) (v j - vLimit) = _
      rw [ContinuousLinearMap.lpPairing_eq_integral]
      exact (integral_add (haint j) hwork).symm
    rw [heq]
    refine (ofReal_integral_le_lintegral_ofReal ((haint j).add hwork)).trans ?_
    refine lintegral_mono_ae ?_
    filter_upwards [hsupport j, (memLp_indicator_of_bound hs hC (hd j) (hdb j) :
      MemLp (s.indicator (d j)) q μ).coeFn_toLp, Lp.coeFn_sub (v j) vLimit]
      with x hx hDx hvx
    change ENNReal.ofReal (s.indicator (a j) x +
      inner ℝ (D j x) ((v j - vLimit) x)) ≤ ENNReal.ofReal (e j x)
    change D j x = s.indicator (d j) x at hDx
    rw [hDx, hvx, Pi.sub_apply]
    by_cases hxs : x ∈ s
    · simpa only [indicator_of_mem hxs] using ENNReal.ofReal_le_ofReal hx
    · simp only [indicator_of_notMem hxs, inner_zero_left, add_zero,
        ENNReal.ofReal_zero, zero_le]
  have hlim : Tendsto
      (fun j ↦ ENNReal.ofReal ((∫ x, s.indicator (a j) x ∂μ) +
        P (D j) (v j - vLimit))) atTop
      (𝓝 (ENNReal.ofReal (∫ x, s.indicator aLimit x ∂μ))) := by
    simpa only [Function.comp_def, add_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp htotal
  have hnonneg : 0 ≤ᵐ[μ] s.indicator aLimit := by
    filter_upwards [ha_nonneg] with x hx
    by_cases hxs : x ∈ s
    · simpa only [indicator_of_mem hxs, Pi.zero_apply] using hx
    · simp only [indicator_of_notMem hxs, Pi.zero_apply, le_refl]
  rw [← ofReal_integral_eq_lintegral_ofReal haLimitint hnonneg, ← hlim.liminf_eq]
  exact liminf_le_liminf (Eventually.of_forall hminorant)

/-- On a finite measure space, almost-everywhere convergent supporting densities and fields
give a lower bound against a bounded weakly convergent `Lᵖ` sequence, with finite conjugate
exponent `q`. The affine minorants are `a j + ⟪d j, v j - vLimit⟫ ≤ e j`, and the limiting
density `aLimit` is nonnegative. The right-hand integrals take the positive parts of `e j`
and may be infinite; `e j` itself need not be nonnegative. No global growth or integrability
bound on the supporting densities and fields is assumed. -/
theorem lintegral_le_liminf_of_tendsto_supports_ae
    (hq_top : q ≠ ∞)
    {a : ℕ → α → ℝ} {aLimit : α → ℝ}
    {d : ℕ → α → H} {dLimit : α → H} {e : ℕ → α → ℝ}
    (ha : ∀ j, StronglyMeasurable (a j)) (haLimit : StronglyMeasurable aLimit)
    (hd : ∀ j, StronglyMeasurable (d j)) (hdLimit : StronglyMeasurable dLimit)
    (hae : ∀ᵐ x ∂μ, Tendsto (fun j ↦ a j x) atTop (𝓝 (aLimit x)))
    (hde : ∀ᵐ x ∂μ, Tendsto (fun j ↦ d j x) atTop (𝓝 (dLimit x)))
    (ha_nonneg : ∀ᵐ x ∂μ, 0 ≤ aLimit x)
    {v : ℕ → Lp H p μ} {vLimit : Lp H p μ}
    (hv : Tendsto (fun j ↦ toWeakSpace ℝ (Lp H p μ) (v j)) atTop
      (𝓝 (toWeakSpace ℝ (Lp H p μ) vLimit)))
    (R : ℝ) (hvR : ∀ j, ‖v j‖ ≤ R)
    (hsupport : ∀ j, ∀ᵐ x ∂μ,
      a j x + inner ℝ (d j x) (v j x - vLimit x) ≤ e j x) :
    (∫⁻ x, ENNReal.ofReal (aLimit x) ∂μ) ≤
      liminf (fun j ↦ ∫⁻ x, ENNReal.ofReal (e j x) ∂μ) atTop := by
  obtain ⟨s, hs, hb, hexhaust⟩ := exists_bounded_exhaustion_of_tendsto_ae
    (fun j ↦ (ha j).prodMk (hd j)) (haLimit.prodMk hdLimit)
    (by filter_upwards [hae, hde] with x hx hy using hx.prodMk_nhds hy)
  have hlocal (k : ℕ) : (∫⁻ x, ENNReal.ofReal ((s k).indicator aLimit x) ∂μ) ≤
      liminf (fun j ↦ ∫⁻ x, ENNReal.ofReal (e j x) ∂μ) atTop := by
    refine lintegral_indicator_le_liminf_of_bounded_supports hq_top
      ha haLimit hd hdLimit hae hde ha_nonneg hv R hvR hsupport
      (hs k) (Nat.cast_nonneg k) ?_ ?_ ?_ ?_
    · intro j x hx
      exact (norm_fst_le (a j x, d j x)).trans ((hb k x hx).2 j)
    · intro x hx
      exact (norm_fst_le (aLimit x, dLimit x)).trans (hb k x hx).1
    · intro j x hx
      exact (norm_snd_le (a j x, d j x)).trans ((hb k x hx).2 j)
    · intro x hx
      exact (norm_snd_le (aLimit x, dLimit x)).trans (hb k x hx).1
  have hpoint : ∀ᵐ x ∂μ,
      liminf (fun k ↦ ENNReal.ofReal ((s k).indicator aLimit x)) atTop =
        ENNReal.ofReal (aLimit x) := by
    filter_upwards [hexhaust] with x hx
    have heq : (fun k ↦ ENNReal.ofReal ((s k).indicator aLimit x)) =ᶠ[atTop]
        fun _ ↦ ENNReal.ofReal (aLimit x) :=
      hx.mono fun k hk ↦ by simp only [indicator_of_mem hk]
    exact (tendsto_const_nhds.congr' heq.symm).liminf_eq
  calc
    (∫⁻ x, ENNReal.ofReal (aLimit x) ∂μ) =
        ∫⁻ x, liminf (fun k ↦ ENNReal.ofReal ((s k).indicator aLimit x)) atTop ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hpoint] with x hx
      exact hx.symm
    _ ≤ liminf (fun k ↦ ∫⁻ x, ENNReal.ofReal ((s k).indicator aLimit x) ∂μ) atTop :=
      lintegral_liminf_le' fun k ↦
        (ENNReal.measurable_ofReal.comp
          (haLimit.indicator (hs k)).measurable).aemeasurable
    _ ≤ liminf (fun j ↦ ∫⁻ x, ENNReal.ofReal (e j x) ∂μ) atTop := by
      simpa only [liminf_const] using
        (liminf_le_liminf (f := (atTop : Filter ℕ)) (Eventually.of_forall hlocal))

end FiniteMeasure

end PDE.CalculusOfVariations
