/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module
public import PDE.Analysis.MeasureTheory.Lp.IndicatorExtension
public import PDE.Hyperbolic.Models.Wave.Fourier.Lp.Duhamel
public import PDE.Hyperbolic.Models.Wave.Strichartz.L2Identification

/-!
# The physical Duhamel solution in the wave Strichartz space

Compact tensor testing and Bochner Fubini identify the retarded mixed-space
operator with the real part of the physical L2 Duhamel integral for arbitrary
complex L1L2 forcing on a finite interval. Joint representatives retain their
spatial almost-everywhere identity at every time. The resulting L4L12 bounds
apply to the Duhamel field and to its sum with the homogeneous Fourier
wave; their spacetime membership and bounds are derived from the operators.
-/

@[expose] public section

open MeasureTheory FourierTransform Filter Set
open scoped ENNReal SchwartzMap

namespace WaveEquation.Strichartz

private theorem exists_compactTensorL2Test
    (a : ({w : 𝓢(ℝ, ℝ) // HasCompactSupport (w : ℝ → ℝ)} ×
      {f : 𝓢(ℝ^3, ℝ) // HasCompactSupport (f : ℝ^3 → ℝ)}) →₀ ℝ) :
    ∃ q : ℝ → Lp ℂ 2 (volume : Measure (ℝ^3)) →L[ℝ] ℝ, Continuous q ∧ HasCompactSupport q ∧ ∀ t u,
      q t u = (inner ℂ (((SchwartzMap.compactTensorSchwartzLinearMap a t).postcompCLM
      Complex.ofRealCLM).toLp 2 volume) u).re := by
  let : InnerProductSpace ℝ (Lp ℂ 2 (volume : Measure (ℝ^3))) := InnerProductSpace.rclikeToReal ℂ _
  let L : 𝓢(ℝ^3, ℝ) →L[ℝ] (Lp ℂ 2 (volume : Measure (ℝ^3)) →L[ℝ] ℝ) :=
    (innerSL ℝ).comp ((SchwartzMap.toLpCLM ℝ ℂ 2 volume).comp
      (SchwartzMap.postcompCLM Complex.ofRealCLM))
  let q := fun t ↦ L (SchwartzMap.compactTensorSchwartzLinearMap a t)
  have he : q = fun t ↦ ∑ z ∈ a.support, (a z * z.1.1 t) • L z.2.1 := by
    funext t
    simp only [q, SchwartzMap.compactTensorSchwartzLinearMap,
      Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply,
      map_sum, map_smul, smul_smul]
  refine ⟨q, ?_, ?_, ?_⟩
  · rw [he]
    exact continuous_finsetSum _ fun z _ ↦
      (continuous_const.mul z.1.1.continuous).smul continuous_const
  · rw [he]
    have hc : HasCompactSupport (∑ z ∈ a.support,
        fun t : ℝ ↦ (a z * z.1.1 t) • L z.2.1) := by
      refine HasCompactSupport.finset_sum fun z _ ↦ ?_
      have hz : HasCompactSupport (fun t : ℝ ↦ a z * z.1.1 t) := z.1.2.mul_left (f := fun _ ↦ a z)
      exact hz.smul_right (f' := fun _ ↦ L z.2.1)
    have heq : (∑ z ∈ a.support, fun t : ℝ ↦ (a z * z.1.1 t) • L z.2.1) =
        (fun t : ℝ ↦ ∑ z ∈ a.support, (a z * z.1.1 t) • L z.2.1) := by
      funext t
      simp only [Finset.sum_apply]
    exact heq ▸ hc
  · intro t u
    simp only [q, L]
    exact real_inner_eq_re_inner ℂ _ _

/-- Compact tensor testing of a causal L2 impulse uses the physical sine
propagator, including at and before its initial time. -/
theorem spacetimePairing_retardedWaveAt_L2_compactTensor
    (u : Lp ℂ 2 (volume : Measure (ℝ^3))) (s : ℝ)
    (a : ({w : 𝓢(ℝ, ℝ) // HasCompactSupport (w : ℝ → ℝ)} ×
      {f : 𝓢(ℝ^3, ℝ) // HasCompactSupport (f : ℝ^3 → ℝ)}) →₀ ℝ) :
    spacetimePairing (retardedWaveAt s u)
      (SchwartzMap.compactTensorLpLinearMap (4 / 3) (12 / 11) volume volume a) =
        ∫ t, (inner ℂ (((SchwartzMap.compactTensorSchwartzLinearMap a t).postcompCLM
          Complex.ofRealCLM).toLp 2 volume)
          (Fourier.sineEvolution (max (t - s) 0) u)).re := by
  have hex := exists_jointRepresentative_homogeneousWaveOperator_rotationColumn_L2 u s
  rcases hex with ⟨F, hF, hsection, _⟩
  have hp := jointRepresentative_retardedWaveAt_L2 u s hF hsection
  refine (spacetimePairing_compactTensor_eq_jointIntegral (retardedWaveAt s u) a).trans ?_
  apply integral_congr_ae
  filter_upwards [Measure.ae_ae_of_ae_prod hp] with t ht
  by_cases hs : s ≤ t
  · rw [max_eq_left (sub_nonneg.mpr hs), re_inner_schwartz_L2_eq_integral _ _ (hsection t)]
    apply integral_congr_ae
    filter_upwards [ht] with x hx
    simp only [hx, Set.indicator_of_mem (show (t, x) ∈ Prod.fst ⁻¹' Ici s from hs)]
  · have hz : Fourier.sineEvolution (max (t - s) 0) u = 0 := by
      rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge hs))]
      exact Fourier.sineEvolution_zero_apply u
    have hr : (inner ℂ (((SchwartzMap.compactTensorSchwartzLinearMap a t).postcompCLM
        Complex.ofRealCLM).toLp 2 volume) (Fourier.sineEvolution (max (t - s) 0) u)).re = 0 :=
      (congrArg (fun v : Lp ℂ 2 (volume : Measure (ℝ^3)) ↦
        (inner ℂ (((SchwartzMap.compactTensorSchwartzLinearMap a t).postcompCLM
          Complex.ofRealCLM).toLp 2 volume) v).re) hz).trans
            (by simp only [inner_zero_right, Complex.zero_re])
    refine Eq.trans ?_ hr.symm
    apply integral_eq_zero_of_ae
    filter_upwards [ht] with x hx
    simp only [hx, Set.indicator_of_notMem (show (t, x) ∉ Prod.fst ⁻¹' Ici s from hs),
      mul_zero, Pi.zero_apply]

/-- A finite-interval forcing extension pairs with the restricted
retarded integral; quotient representatives are transported explicitly. -/
theorem spacetimePairing_retardedWaveOperator_extendByZero_eq_integral (a b : ℝ)
    (f : Lp (Lp ℂ 2 (volume : Measure (ℝ^3))) 1 (volume.restrict (Icc a b)))
    (v : Lp (Lp ℝ (12 / 11) (volume : Measure (ℝ^3))) (4 / 3) (volume : Measure ℝ)) :
    spacetimePairing (retardedWaveOperator (Lp.extendByZeroₗᵢ (𝕜 := ℝ) measurableSet_Icc f)) v =
      ∫ s in Icc a b, spacetimePairing (retardedWaveAt s (f s)) v := by
  refine (spacetimePairing_retardedWaveOperator_eq_integral
    (Lp.extendByZeroₗᵢ (𝕜 := ℝ) measurableSet_Icc f) v).trans ?_
  calc
    _ = ∫ s, (Icc a b).indicator (fun r ↦ spacetimePairing (retardedWaveAt r (f r)) v) s := by
      apply integral_congr_ae
      filter_upwards [Lp.extendByZeroₗᵢ_apply_ae (𝕜 := ℝ) measurableSet_Icc f] with s hs
      refine (congrArg (fun z : Lp ℂ 2 (volume : Measure (ℝ^3)) ↦
        spacetimePairing (retardedWaveAt s z) v) hs).trans ?_
      by_cases h : s ∈ Icc a b
      · simp only [Set.indicator_of_mem h]
      · simp only [Set.indicator_of_notMem h, map_zero, zero_apply]
    _ = _ := integral_indicator measurableSet_Icc

/-- The continuous physical Duhamel trajectory has locally integrable joint
representatives, as required for spatial-temporal test uniqueness. -/
theorem locallyIntegrable_re_duhamelL2 (a b : ℝ)
    (f : Lp (Lp ℂ 2 (volume : Measure (ℝ^3))) 1 (volume.restrict (Icc a b))) {F : ℝ × ℝ^3 → ℂ}
    (hF : Measurable F)
    (hsection : ∀ t, (fun x ↦ F (t, x)) =ᵐ[volume] (Fourier.duhamelL2 a b t f : ℝ^3 → ℂ)) :
    LocallyIntegrable (fun z ↦ (F z).re) (volume.prod volume) := by
  have hc : Continuous (fun t : ℝ ↦ Fourier.duhamelL2 a b t f) :=
    (Fourier.lipschitzWith_duhamelL2 a b f).continuous
  have hl : LocallyIntegrable F (volume.prod volume) :=
    Continuous.locallyIntegrable_jointLpRepresentative
      (p := 2) (μ := volume) (ν := volume) hc hF hsection
  exact hl.mono (Complex.continuous_re.measurable.comp hF).aestronglyMeasurable
    (.of_forall fun z ↦ by simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm (F z))

/-- Compact tensor pairing of the constructed retarded operator equals pairing
of the physical Bochner Duhamel integral. -/
theorem spacetimePairing_retardedWaveOperator_duhamelL2_compactTensor (a b : ℝ)
    (f : Lp (Lp ℂ 2 (volume : Measure (ℝ^3))) 1 (volume.restrict (Icc a b)))
    (c : ({w : 𝓢(ℝ, ℝ) // HasCompactSupport (w : ℝ → ℝ)} ×
      {f : 𝓢(ℝ^3, ℝ) // HasCompactSupport (f : ℝ^3 → ℝ)}) →₀ ℝ) :
    spacetimePairing (retardedWaveOperator
      (Lp.extendByZeroₗᵢ (𝕜 := ℝ) measurableSet_Icc f))
      (SchwartzMap.compactTensorLpLinearMap (4 / 3) (12 / 11) volume volume c) =
        ∫ t, (inner ℂ (((SchwartzMap.compactTensorSchwartzLinearMap c t).postcompCLM
          Complex.ofRealCLM).toLp 2 volume) (Fourier.duhamelL2 a b t f)).re := by
  let q := (exists_compactTensorL2Test c).choose
  have hq : Continuous q := (exists_compactTensorL2Test c).choose_spec.1
  have hqc : HasCompactSupport q := (exists_compactTensorL2Test c).choose_spec.2.1
  have htest (t : ℝ) (u : Lp ℂ 2 (volume : Measure (ℝ^3))) :
      q t u = (inner ℂ (((SchwartzMap.compactTensorSchwartzLinearMap c t).postcompCLM
        Complex.ofRealCLM).toLp 2 volume) u).re :=
    (exists_compactTensorL2Test c).choose_spec.2.2 t u
  refine (spacetimePairing_retardedWaveOperator_extendByZero_eq_integral a b f
    (SchwartzMap.compactTensorLpLinearMap (4 / 3) (12 / 11) volume volume c)).trans ?_
  calc
    _ = ∫ s in Icc a b, ∫ t, q t (Fourier.sineEvolution (max (t - s) 0) (f s)) := by
      apply integral_congr_ae
      filter_upwards with s
      simpa only [htest] using spacetimePairing_retardedWaveAt_L2_compactTensor (f s) s c
    _ = ∫ t, q t (Fourier.duhamelL2 a b t f) :=
      (Fourier.integral_test_duhamelL2_eq a b f q hq hqc).symm
    _ = _ := integral_congr_ae (.of_forall fun t ↦ htest t _)

/-- The retarded mixed output is the real part of the physical L2
Duhamel field for arbitrary complex L1L2 forcing. -/
theorem jointRepresentative_retardedWaveOperator_duhamelL2 (a b : ℝ)
    (f : Lp (Lp ℂ 2 (volume : Measure (ℝ^3))) 1 (volume.restrict (Icc a b))) {F : ℝ × ℝ^3 → ℂ}
    (hF : Measurable F)
    (hsection : ∀ t, (fun x ↦ F (t, x)) =ᵐ[volume] (Fourier.duhamelL2 a b t f : ℝ^3 → ℂ)) :
    Lp.jointRepresentative (retardedWaveOperator (Lp.extendByZeroₗᵢ (𝕜 := ℝ) measurableSet_Icc f))
      =ᵐ[volume.prod volume] fun z ↦ (F z).re := by
  apply jointRepresentative_eq_of_compactTensor_pairing _
    (locallyIntegrable_re_duhamelL2 a b f hF hsection)
  intro c
  refine (spacetimePairing_retardedWaveOperator_duhamelL2_compactTensor a b f c).trans ?_
  exact integral_congr_ae (.of_forall fun t ↦ re_inner_schwartz_L2_eq_integral _ _ (hsection t))

/-- A measurable physical Duhamel representative exists at every time and
represents the constructed retarded mixed output almost everywhere in spacetime. -/
theorem exists_jointRepresentative_retardedWaveOperator_duhamelL2 (a b : ℝ)
    (f : Lp (Lp ℂ 2 (volume : Measure (ℝ^3))) 1 (volume.restrict (Icc a b))) :
    ∃ F : ℝ × ℝ^3 → ℂ, Measurable F ∧
      (∀ t, (fun x ↦ F (t, x)) =ᵐ[volume]
        (Fourier.duhamelL2 a b t f : ℝ^3 → ℂ)) ∧
      Lp.jointRepresentative (retardedWaveOperator
        (Lp.extendByZeroₗᵢ (𝕜 := ℝ) measurableSet_Icc f))
          =ᵐ[volume.prod volume] fun z ↦ (F z).re := by
  have hc : Continuous (fun t : ℝ ↦ Fourier.duhamelL2 a b t f) :=
    (Fourier.lipschitzWith_duhamelL2 a b f).continuous
  have hex := StronglyMeasurable.exists_jointLpRepresentative
    (p := 2) (ν := (volume : Measure (ℝ^3))) hc.stronglyMeasurable
  exact ⟨hex.choose, hex.choose_spec.1, hex.choose_spec.2,
    jointRepresentative_retardedWaveOperator_duhamelL2 a b f hex.choose_spec.1 hex.choose_spec.2⟩

/-- The physical Duhamel mixed seminorm is exactly the norm of the constructed
retarded output. -/
theorem eLpNorm_duhamelL2_eq (a b : ℝ)
    (f : Lp (Lp ℂ 2 (volume : Measure (ℝ^3))) 1 (volume.restrict (Icc a b))) {F : ℝ × ℝ^3 → ℂ}
    (hF : Measurable F)
    (hsection : ∀ t, (fun x ↦ F (t, x)) =ᵐ[volume] (Fourier.duhamelL2 a b t f : ℝ^3 → ℂ)) :
    eLpNorm (fun t ↦ eLpNorm (fun x ↦ (F (t, x)).re) 12 volume) 4 volume =
      ‖retardedWaveOperator (Lp.extendByZeroₗᵢ (𝕜 := ℝ) measurableSet_Icc f)‖ₑ := by
  rw [← Lp.eLpNorm_jointRepresentative]
  apply eLpNorm_congr_ae
  filter_upwards [Measure.ae_ae_of_ae_prod
    (jointRepresentative_retardedWaveOperator_duhamelL2 a b f hF hsection)] with t ht
  exact eLpNorm_congr_ae (Filter.EventuallyEq.symm ht)

/-- Physical Duhamel solutions have finite L4L12 mixed seminorm. -/
theorem memLp_eLpNorm_duhamelL2 (a b : ℝ)
    (f : Lp (Lp ℂ 2 (volume : Measure (ℝ^3))) 1 (volume.restrict (Icc a b))) {F : ℝ × ℝ^3 → ℂ}
    (hF : Measurable F)
    (hsection : ∀ t, (fun x ↦ F (t, x)) =ᵐ[volume] (Fourier.duhamelL2 a b t f : ℝ^3 → ℂ)) :
    MemLp (fun t ↦ eLpNorm (fun x ↦ (F (t, x)).re) 12 volume) 4 volume := by
  change eLpNorm _ _ _ < (∞ : ℝ≥0∞)
  rw [eLpNorm_duhamelL2_eq a b f hF hsection]
  exact enorm_lt_top

/-- The physical Duhamel field has the proved L1L2 to L4L12 estimate. -/
theorem mixedNorm_duhamelL2_le (a b : ℝ)
    (f : Lp (Lp ℂ 2 (volume : Measure (ℝ^3))) 1 (volume.restrict (Icc a b))) {F : ℝ × ℝ^3 → ℂ}
    (hF : Measurable F)
    (hsection : ∀ t, (fun x ↦ F (t, x)) =ᵐ[volume] (Fourier.duhamelL2 a b t f : ℝ^3 → ℂ)) :
    (eLpNorm (fun t ↦ eLpNorm (fun x ↦ (F (t, x)).re) 12 volume) 4 volume).toReal ≤
      energyAdjointBound * ‖f‖ := by
  rw [eLpNorm_duhamelL2_eq a b f hF hsection, toReal_enorm]
  exact ((retardedWaveOperator.le_opNorm _).trans
    (mul_le_mul_of_nonneg_right norm_retardedWaveOperator_le (norm_nonneg _))).trans_eq
    (congrArg (energyAdjointBound * ·) ((Lp.extendByZeroₗᵢ (𝕜 := ℝ) measurableSet_Icc).norm_map f))

/-- The Fourier homogeneous solution plus the physical causal Duhamel
field represents the sum of the two constructed spacetime outputs. -/
theorem jointRepresentative_fourierWave_add_duhamelL2 (g h : 𝓢(ℝ^3, ℂ)) (a b : ℝ)
    (f : Lp (Lp ℂ 2 (volume : Measure (ℝ^3))) 1 (volume.restrict (Icc a b))) {F : ℝ × ℝ^3 → ℂ}
    (hF : Measurable F)
    (hsection : ∀ t, (fun x ↦ F (t, x)) =ᵐ[volume] (Fourier.duhamelL2 a b t f : ℝ^3 → ℂ)) :
    Lp.jointRepresentative (homogeneousWaveOperator (initialEnergyDatum g h) +
      retardedWaveOperator (Lp.extendByZeroₗᵢ (𝕜 := ℝ) measurableSet_Icc f))
        =ᵐ[volume.prod volume] fun z ↦ (Fourier.waveSolution
          (𝓕 g : 𝓢(ℝ^3, ℂ)) (𝓕 h : 𝓢(ℝ^3, ℂ)) z).re + (F z).re := by
  filter_upwards [Lp.jointRepresentative_add (homogeneousWaveOperator (initialEnergyDatum g h))
    (retardedWaveOperator (Lp.extendByZeroₗᵢ (𝕜 := ℝ) measurableSet_Icc f)),
    jointRepresentative_homogeneousWaveOperator_initialEnergyDatum g h,
    jointRepresentative_retardedWaveOperator_duhamelL2 a b f hF hsection] with z hsum hh hd
  simpa only [Pi.add_apply, hh, hd] using hsum

/-- The mixed norm of the homogeneous-plus-forcing construction equals
the norm of its spacetime quotient class. -/
theorem eLpNorm_fourierWave_add_duhamelL2_eq (g h : 𝓢(ℝ^3, ℂ)) (a b : ℝ)
    (f : Lp (Lp ℂ 2 (volume : Measure (ℝ^3))) 1 (volume.restrict (Icc a b))) {F : ℝ × ℝ^3 → ℂ}
    (hF : Measurable F)
    (hsection : ∀ t, (fun x ↦ F (t, x)) =ᵐ[volume] (Fourier.duhamelL2 a b t f : ℝ^3 → ℂ)) :
    eLpNorm (fun t ↦ eLpNorm (fun x ↦ (Fourier.waveSolution
      (𝓕 g : 𝓢(ℝ^3, ℂ)) (𝓕 h : 𝓢(ℝ^3, ℂ)) (t, x)).re + (F (t, x)).re)
        12 volume) 4 volume =
      ‖homogeneousWaveOperator (initialEnergyDatum g h) +
        retardedWaveOperator (Lp.extendByZeroₗᵢ (𝕜 := ℝ) measurableSet_Icc f)‖ₑ := by
  rw [← Lp.eLpNorm_jointRepresentative]
  apply eLpNorm_congr_ae
  filter_upwards [Measure.ae_ae_of_ae_prod
    (jointRepresentative_fourierWave_add_duhamelL2 g h a b f hF hsection)] with t ht
  exact eLpNorm_congr_ae (Filter.EventuallyEq.symm ht)

/-- The homogeneous-plus-Duhamel construction has finite mixed norm. -/
theorem memLp_eLpNorm_fourierWave_add_duhamelL2 (g h : 𝓢(ℝ^3, ℂ)) (a b : ℝ)
    (f : Lp (Lp ℂ 2 (volume : Measure (ℝ^3))) 1 (volume.restrict (Icc a b))) {F : ℝ × ℝ^3 → ℂ}
    (hF : Measurable F)
    (hsection : ∀ t, (fun x ↦ F (t, x)) =ᵐ[volume] (Fourier.duhamelL2 a b t f : ℝ^3 → ℂ)) :
    MemLp (fun t ↦ eLpNorm (fun x ↦ (Fourier.waveSolution (𝓕 g : 𝓢(ℝ^3, ℂ)) (𝓕 h : 𝓢(ℝ^3, ℂ))
      (t, x)).re + (F (t, x)).re) 12 volume) 4 volume := by
  change eLpNorm _ _ _ < (∞ : ℝ≥0∞)
  rw [eLpNorm_fourierWave_add_duhamelL2_eq g h a b f hF hsection]
  exact enorm_lt_top

/-- The physical homogeneous-plus-forcing construction satisfies the
L4L12 estimate with precisely the initial energy norm and L1L2 forcing norm. -/
theorem mixedNorm_fourierWave_add_duhamelL2_le (g h : 𝓢(ℝ^3, ℂ)) (a b : ℝ)
    (f : Lp (Lp ℂ 2 (volume : Measure (ℝ^3))) 1 (volume.restrict (Icc a b))) {F : ℝ × ℝ^3 → ℂ}
    (hF : Measurable F)
    (hsection : ∀ t, (fun x ↦ F (t, x)) =ᵐ[volume] (Fourier.duhamelL2 a b t f : ℝ^3 → ℂ)) :
    (eLpNorm (fun t ↦ eLpNorm (fun x ↦ (Fourier.waveSolution (𝓕 g : 𝓢(ℝ^3, ℂ)) (𝓕 h : 𝓢(ℝ^3, ℂ))
      (t, x)).re + (F (t, x)).re) 12 volume) 4 volume).toReal ≤
      energyAdjointBound * (‖initialEnergyDatum g h‖ + ‖f‖) := by
  rw [eLpNorm_fourierWave_add_duhamelL2_eq g h a b f hF hsection, toReal_enorm]
  apply (norm_add_le (homogeneousWaveOperator (initialEnergyDatum g h))
    (retardedWaveOperator (Lp.extendByZeroₗᵢ (𝕜 := ℝ) measurableSet_Icc f))).trans
  refine (add_le_add ?_ ?_).trans_eq (mul_add energyAdjointBound _ _).symm
  · exact (homogeneousWaveOperator.le_opNorm _).trans
      (mul_le_mul_of_nonneg_right norm_homogeneousWaveOperator_le (norm_nonneg _))
  · exact ((retardedWaveOperator.le_opNorm _).trans
      (mul_le_mul_of_nonneg_right norm_retardedWaveOperator_le (norm_nonneg _))).trans_eq
      (congrArg (energyAdjointBound * ·)
        ((Lp.extendByZeroₗᵢ (𝕜 := ℝ) measurableSet_Icc).norm_map f))

end WaveEquation.Strichartz
