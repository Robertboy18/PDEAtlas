/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition.DisplacementLimit
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition.Spacetime
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition.ReactionConvergence
public import PDE.Analysis.MeasureTheory.Lp.CommonSupportConvergence
import PDE.Analysis.MeasureTheory.Lp.Continuous

/-!
# Strong convergence of joint displacement representatives

Fubini identifies the L² seminorm of any jointly measurable representative with
its Bochner L² seminorm. Uniform convergence of spatial L² sections on a finite
time window therefore gives strong spacetime convergence. These statements remain valid on spatial
domains of infinite measure.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition

/-- The L² seminorm of a joint representative equals that of its L²-valued
sections. Almost-everywhere section agreement is sufficient. -/
theorem eLpNorm_prod_eq_of_ae_eq_L2_sections {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] {μ : Measure α} {ν : Measure β} [SFinite ν] {u : α → Lp E 2 ν}
    {U : α × β → E} (hu : MemLp u 2 μ) (hU : AEStronglyMeasurable U (μ.prod ν))
    (hsection : ∀ᵐ t ∂μ, (fun x ↦ U (t, x)) =ᵐ[ν] (u t : β → E)) :
    eLpNorm U 2 (μ.prod ν) = eLpNorm u 2 μ := by
  have hUp := memLp_prod_of_ae_eq_L2_sections hu hU hsection
  have hnorm : ‖hUp.toLp U‖ = ‖hu.toLp u‖ := by
    apply Lp.norm_eq_of_ae_eq_L2_sections
    filter_upwards [Measure.ae_ae_of_ae_prod hUp.coeFn_toLp, hu.coeFn_toLp,
      hsection] with t ht hut hst
    filter_upwards [ht, hst] with x htx hstx
    rw [htx, hstx, hut]
  simpa only [ofReal_norm, Lp.enorm_toLp] using congrArg ENNReal.ofReal hnorm

/-- Uniform convergence on a measurable full-measure set implies Lᵖ convergence
for finite measures. Measurability is needed only for the differences. -/
theorem tendsto_eLpNorm_sub_of_tendstoUniformlyOn_ae {α E ι : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} [IsFiniteMeasure μ] {p : ENNReal} {l : Filter ι}
    {s : Set α} (hs : MeasurableSet s) (hfull : ∀ᵐ t ∂μ, t ∈ s) {u : ι → α → E} {v : α → E}
    (hp : p ≠ ∞) (hmeas : ∀ᶠ i in l, AEStronglyMeasurable (u i - v) μ)
    (hconv : TendstoUniformlyOn u v l s) :
    Tendsto (fun i ↦ eLpNorm (u i - v) p μ) l (𝓝 0) := by
  have hind : TendstoUniformlyOn (fun i ↦ s.indicator (u i)) (s.indicator v) l s :=
    (hconv.congr (Eventually.of_forall fun i t ht ↦ (indicator_of_mem ht _).symm)).congr_right
      (fun t ht ↦ (indicator_of_mem ht _).symm)
  have ht := tendsto_eLpNorm_sub_of_tendstoUniformlyOn hp hs.nullMeasurableSet
    (measure_ne_top μ s) (hmeas.mono fun i hi ↦ by
      simpa only [← indicator_sub'] using hi.indicator hs)
    (Eventually.of_forall fun i ↦ support_indicator_subset) (support_indicator_subset) hind
  apply ht.congr'
  filter_upwards with i
  apply eLpNorm_congr_ae
  filter_upwards [hfull] with t ht
  simp only [Pi.sub_apply, indicator_of_mem ht]

/-- Uniform convergence of L² sections on a finite time window gives convergence
in product L² of any jointly measurable representatives of those sections. -/
theorem tendsto_L2_jointRepresentative_of_tendstoUniformlyOn {α β E ι : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [NormedAddCommGroup E] {μ : Measure α} [IsFiniteMeasure μ] {ν : Measure β}
    [SFinite ν] {l : Filter ι} {s : Set α} (hs : MeasurableSet s) (hfull : ∀ᵐ t ∂μ, t ∈ s)
    {u : ι → α → Lp E 2 ν} {v : α → Lp E 2 ν} {U : ι → α × β → E} {V : α × β → E}
    (hu : ∀ i, MemLp (u i) 2 μ) (hv : MemLp v 2 μ) (hU : ∀ i, AEStronglyMeasurable (U i) (μ.prod ν))
    (hV : AEStronglyMeasurable V (μ.prod ν))
    (hUsec : ∀ i, ∀ᵐ t ∂μ, (fun x ↦ U i (t, x)) =ᵐ[ν] (u i t : β → E))
    (hVsec : ∀ᵐ t ∂μ, (fun x ↦ V (t, x)) =ᵐ[ν] (v t : β → E)) (hconv : TendstoUniformlyOn u v l s) :
    Tendsto (fun i ↦ eLpNorm (U i - V) 2 (μ.prod ν)) l (𝓝 0) := by
  have ht := tendsto_eLpNorm_sub_of_tendstoUniformlyOn_ae hs hfull
    (by norm_num : (2 : ENNReal) ≠ ∞)
    (Eventually.of_forall fun i ↦ ((hu i).sub hv).aestronglyMeasurable) hconv
  apply ht.congr'
  filter_upwards with i
  symm
  apply eLpNorm_prod_eq_of_ae_eq_L2_sections ((hu i).sub hv) ((hU i).sub hV)
  filter_upwards [hUsec i, hVsec] with t hut hvt
  filter_upwards [hut, hvt, Lp.coeFn_sub (u i t) (v t)] with x hux hvx hx
  change U i (t, x) - V (t, x) = ((u i - v) t) x
  rw [hux, hvx]
  exact hx.symm

open SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev SobolevSpace.WholeSpaceHilbert

/-- For truncated energy waves, strong local spacetime convergence
identifies an integrable arbitrary-growth reaction and gives local L¹ convergence.
The necessary uniform-integrability bound is derived from the PDE and common
physical energy; it is not an extra nonlinear hypothesis. -/
theorem integrable_reaction_and_tendsto_L1_of_energy_waves {n : ℕ} {f : ℝ → ℝ} {g : ℕ → ℝ → ℝ}
    {K : ℕ → NNReal} (hf : Continuous f) (hg : ∀ i, LipschitzWith (K i) (g i))
    (hsign : ∀ i z, 0 ≤ z * g i z) (hdom : ∀ i z, |g i z| ≤ |f z|) {r : ℕ → ℝ}
    (hagree : ∀ i, EqOn (g i) f (Metric.closedBall 0 (r i))) (hr : Tendsto r atTop atTop)
    {x : H¹(ℝ^n) × DerivLp n 2 univ} {u : ℕ → C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)}
    (hu : ∀ i, Cauchy.IsEnergySolution (hg i) (reaction_zero (hg i).continuous (hsign i)) x (u i))
    {T E : ℝ} (hT : 0 ≤ T) (he : ∀ i t, 0 ≤ t → physicalEnergy (g i) (u i t) ≤ E) (s : Set (ℝ^n))
    [IsFiniteMeasure ((domainMeasure n univ).restrict s)] {U : ℕ → ℝ × (ℝ^n) → ℝ}
    {V : ℝ × (ℝ^n) → ℝ}
    (hU : ∀ i, MemLp (U i) 2 ((volume.restrict (Ioc 0 T)).prod (domainMeasure n univ)))
    (hUsec : ∀ i, ∀ᵐ t ∂volume.restrict (Ioc 0 T), (fun y ↦ U i (t, y)) =ᵐ[domainMeasure n univ]
      (energyTriple n).inclusion (u i t).1)
    (hconv : Tendsto (fun i ↦ eLpNorm (U i - V) 2 ((volume.restrict (Ioc 0 T)).prod
      ((domainMeasure n univ).restrict s))) atTop (𝓝 0)) :
    Integrable (fun z ↦ f (V z))
        ((volume.restrict (Ioc 0 T)).prod ((domainMeasure n univ).restrict s)) ∧
      Tendsto (fun i ↦ eLpNorm (fun z ↦ g i (U i z) - f (V z)) 1
        ((volume.restrict (Ioc 0 T)).prod ((domainMeasure n univ).restrict s))) atTop (𝓝 0) := by
  let B := 2 * Real.sqrt (2 * E) * (‖(energyTriple n).inclusion x.1‖ + T * Real.sqrt (2 * E)) +
      T * Real.sqrt (2 * E) ^ 2
  apply integrable_reaction_and_tendsto_L1_of_tendstoInMeasure hf (fun i ↦ (hg i).continuous) hdom
    (fun i ↦ (hU i).aestronglyMeasurable.mono_measure
      (Measure.prod_mono le_rfl Measure.restrict_le_self)) (M := Real.toNNReal B) _
    hagree hr (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ENNReal) ≠ 0) hconv)
  intro i
  change (∫⁻ z, ‖U i z * g i (U i z)‖ₑ
    ∂(volume.restrict (Ioc 0 T)).prod ((domainMeasure n univ).restrict s)) ≤ ENNReal.ofReal B
  exact lintegral_reaction_product_restrict_le
    (lintegral_reaction_product_le (hg i) (hsign i) (hu i) hT (he i) (hU i) (hUsec i)) s

open scoped Distributions

/-- Strong uniform convergence of one spatial cutoff gives unweighted spacetime
L² convergence wherever that cutoff is one. The joint representatives may be
chosen independently, and the limiting H¹ curve need not be norm-continuous. -/
theorem tendsto_L2_restrict_of_cutoff_convergence {n : ℕ} {T : ℝ} {q : ℕ → ℝ → H¹(ℝ^n)}
    {p : ℝ → H¹(ℝ^n)} (hq : ∀ i, ContinuousOn (q i) (Icc 0 T))
    (χ : 𝓓((⊤ : TopologicalSpace.Opens (ℝ^n)), ℝ)) (s : Set (ℝ^n)) (hs : MeasurableSet s)
    (hχ : ∀ x ∈ s, χ.toFun x = 1) {U : ℕ → ℝ × (ℝ^n) → ℝ} {V : ℝ × (ℝ^n) → ℝ}
    (hU : ∀ i, AEStronglyMeasurable (U i) ((volume.restrict (Ioc 0 T)).prod (domainMeasure n univ)))
    (hV : AEStronglyMeasurable V ((volume.restrict (Ioc 0 T)).prod (domainMeasure n univ)))
    (hUsec : ∀ i, ∀ᵐ t ∂volume.restrict (Ioc 0 T), (fun y ↦ U i (t, y)) =ᵐ[domainMeasure n univ]
      (energyTriple n).inclusion (q i t))
    (hVsec : ∀ᵐ t ∂volume.restrict (Ioc 0 T), (fun y ↦ V (t, y)) =ᵐ[domainMeasure n univ]
      (energyTriple n).inclusion (p t))
    (hconv : TendstoUniformlyOn (fun i t ↦ (energyTriple n).inclusion (cutoffCLM χ (q i t)))
      (fun t ↦ (energyTriple n).inclusion (cutoffCLM χ (p t))) atTop (Icc 0 T)) :
    Tendsto (fun i ↦ eLpNorm (U i - V) 2 ((volume.restrict (Ioc 0 T)).prod
      ((domainMeasure n univ).restrict s))) atTop (𝓝 0) := by
  let A := (energyTriple n).inclusion.comp (cutoffCLM (n := n) (p := 2) (Ω := univ) χ)
  have hcont (i : ℕ) : ContinuousOn (fun t ↦ A (q i t)) (Icc 0 T) :=
    A.continuous.comp_continuousOn (hq i)
  have hcontp : ContinuousOn (fun t ↦ A (p t)) (Icc 0 T) :=
    hconv.continuousOn (Eventually.of_forall hcont).frequently
  have hmχ : StronglyMeasurable (fun z : ℝ × (ℝ^n) ↦ χ.toFun z.2) :=
    χ.continuous.stronglyMeasurable.comp_measurable measurable_snd
  have ht : Tendsto (fun i ↦ eLpNorm ((fun z ↦ χ.toFun z.2 * U i z) - (fun z ↦ χ.toFun z.2 * V z)) 2
      ((volume.restrict (Ioc 0 T)).prod (domainMeasure n univ))) atTop (𝓝 0) := by
    apply tendsto_L2_jointRepresentative_of_tendstoUniformlyOn measurableSet_Icc
      ((ae_restrict_mem measurableSet_Ioc).mono fun _ ht ↦ Ioc_subset_Icc_self ht)
      (fun i ↦ (hcont i).memLp_of_subset_isCompact isCompact_Icc
        measurableSet_Ioc Ioc_subset_Icc_self)
      (hcontp.memLp_of_subset_isCompact isCompact_Icc measurableSet_Ioc Ioc_subset_Icc_self)
      (fun i ↦ hmχ.aestronglyMeasurable.mul (hU i)) (hmχ.aestronglyMeasurable.mul hV) _ _ hconv
    · intro i
      filter_upwards [hUsec i] with t ht
      filter_upwards [ht, cutoffCLM_base_apply_ae χ (q i t)] with y hy hcut
      simp only [Pi.mul_apply]
      rw [hy]
      exact hcut.symm
    · filter_upwards [hVsec] with t ht
      filter_upwards [ht, cutoffCLM_base_apply_ae χ (p t)] with y hy hcut
      simp only [Pi.mul_apply]
      rw [hy]
      exact hcut.symm
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ ↦ bot_le) (fun i ↦ ?_)
  have hχae : ∀ᵐ z ∂(volume.restrict (Ioc 0 T)).prod ((domainMeasure n univ).restrict s),
      χ.toFun z.2 = 1 := Measure.quasiMeasurePreserving_snd.ae ((ae_restrict_mem hs).mono hχ)
  calc
    _ = eLpNorm ((fun z ↦ χ.toFun z.2 * U i z) - (fun z ↦ χ.toFun z.2 * V z)) 2
        ((volume.restrict (Ioc 0 T)).prod ((domainMeasure n univ).restrict s)) := by
      apply eLpNorm_congr_ae
      filter_upwards [hχae] with z hz
      simp only [Pi.sub_apply, hz, one_mul]
    _ ≤ _ := eLpNorm_mono_measure _ (Measure.prod_mono le_rfl Measure.restrict_le_self)

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition
