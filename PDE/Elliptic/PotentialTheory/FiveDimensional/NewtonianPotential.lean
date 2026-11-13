/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.FiveDimensional.PrincipalValueHessian
public import PDE.Analysis.Integration.ConvolutionDerivative
public import PDE.Analysis.Integration.ConvolutionL2
public import PDE.Spaces.Sobolev.Approximation.Mollification.WeakDerivatives
import PDE.Elliptic.Classical.Poisson.FundamentalSolution
import PDE.Elliptic.PotentialTheory.FundamentalSolution.LocalIntegrability

/-!
# Five-dimensional Newtonian convolution

Split `fundamentalSolution 5` into an integrable kernel on the unit ball and
an L² kernel outside it. This gives almost-everywhere convolution existence,
L² membership for L¹ ∩ L² sources, and a uniform potential bound when source
supports lie in one compact set.

For smooth compact sources, coordinate derivatives move onto the source.
Classical Poisson inversion supplies the pointwise source equation.
If a source vanishes at the evaluation point, the classical Hessian kernel
is absolutely integrable there and equals the Hessian of its potential.
-/

@[expose] public section

open PDE (partialDeriv iteratedPartialDeriv)

noncomputable section

open MeasureTheory Filter LineDeriv
open scoped Distributions ENNReal RealInnerProductSpace Topology
open PDE.Analysis SobolevSpace

namespace PotentialTheory

/-- The singular part of the Newtonian kernel, cut off at unit distance. -/
private def nearFiveDimensionalGamma : ℝ^5 → ℝ :=
  (Metric.closedBall (0 : ℝ^5) 1).indicator (fundamentalSolution 5)

/-- Outside the unit ball, the Newtonian kernel has no singularity and decays as `|X|⁻³`. -/
private def farFiveDimensionalGamma : ℝ^5 → ℝ :=
  (Metric.closedBall (0 : ℝ^5) 1)ᶜ.indicator (fundamentalSolution 5)

/-- The two cutoffs partition the kernel, including the sphere where they meet. -/
private theorem nearFiveDimensionalGamma_add_far :
    nearFiveDimensionalGamma + farFiveDimensionalGamma = (fundamentalSolution 5) := by
  funext X
  change (Metric.closedBall (0 : ℝ^5) 1).indicator
      (fundamentalSolution 5) X +
    (Metric.closedBall (0 : ℝ^5) 1)ᶜ.indicator
      (fundamentalSolution 5) X = (fundamentalSolution 5) X
  by_cases hX : X ∈ Metric.closedBall (0 : ℝ^5) 1
  · simp only [Set.indicator_of_mem hX, Set.indicator_of_notMem
      (show X ∉ (Metric.closedBall (0 : ℝ^5) 1)ᶜ
        from fun h ↦ h hX), add_zero]
  · simp only [Set.indicator_of_notMem hX, Set.indicator_of_mem
      (show X ∈ (Metric.closedBall (0 : ℝ^5) 1)ᶜ from hX), zero_add]

/-- Local integrability controls the singularity on the compact unit ball. -/
private theorem integrable_nearFiveDimensionalGamma :
    Integrable nearFiveDimensionalGamma volume :=
  (integrable_indicator_iff measurableSet_closedBall).2
    ((locallyIntegrable_fundamentalSolution 5).integrableOn_isCompact
      (isCompact_closedBall _ _))

/-- The exterior kernel is in `L²`: its square decays as `|X|⁻⁶` in dimension five.
Comparison with `(1 + |X|)⁻³` avoids a separate polar-coordinate calculation. -/
private theorem memLp_farFiveDimensionalGamma :
    MemLp farFiveDimensionalGamma 2 volume := by
  let w : ℝ^5 → ℝ := fun X ↦ ((1 + ‖X‖) ^ 3)⁻¹
  let K : ℝ := 1 / (8 * Real.pi ^ 2)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hwc : Continuous w := by fun_prop (disch := intro X; positivity)
  have hw : MemLp w 2 volume := by
    apply (memLp_two_iff_integrable_sq hwc.aestronglyMeasurable).2
    have heq : (fun X ↦ w X ^ 2) =
        (fun X : ℝ^5 ↦ (1 + ‖X‖) ^ (-6 : ℝ)) := by
      funext X
      norm_num only [w, inv_pow, ← pow_mul,
        Real.rpow_neg (by positivity : 0 ≤ 1 + ‖X‖) 6, Real.rpow_ofNat]
    rw [heq]
    exact integrable_one_add_norm (by norm_num)
  have hbound (X : ℝ^5) : ‖farFiveDimensionalGamma X‖ ≤ (8 * K) * w X := by
    by_cases hX : X ∈ Metric.closedBall (0 : ℝ^5) 1
    · rw [farFiveDimensionalGamma, Set.indicator_of_notMem (not_not_intro hX), norm_zero]
      dsimp [w]
      positivity
    have hnorm : 1 < ‖X‖ := by simpa using hX
    rw [farFiveDimensionalGamma, Set.indicator_of_mem hX, fundamentalSolution_five]
    change ‖K * ‖X‖ ^ (-3 : ℝ)‖ ≤ (8 * K) * w X
    rw [norm_mul, Real.norm_of_nonneg hK, Real.norm_of_nonneg (by positivity),
      Real.rpow_neg (norm_nonneg _), Real.rpow_ofNat]
    calc K * (‖X‖ ^ 3)⁻¹ ≤ K * (((1 + ‖X‖) / 2) ^ 3)⁻¹ := by gcongr; linarith
      _ = (8 * K) * w X := by dsimp [w]; rw [div_pow, inv_div]; ring
  exact (hw.const_mul (8 * K)).mono'
    ((locallyIntegrable_fundamentalSolution 5).aestronglyMeasurable.indicator
      measurableSet_closedBall.compl) (Filter.Eventually.of_forall hbound)

/-- The near part uses an `L¹` kernel and an `L²` source. For the far part, the roles
reverse: the source is integrable and the exterior kernel is square-integrable. -/
private theorem ae_convolutionExistsAt_near_far
    {f : ℝ^5 → ℝ} (hfi : Integrable f volume)
    (hf : MemLp f 2 volume) :
    ∀ᵐ X ∂volume,
      ConvolutionExistsAt nearFiveDimensionalGamma f X (ContinuousLinearMap.mul ℝ ℝ) ∧
      ConvolutionExistsAt farFiveDimensionalGamma f X (ContinuousLinearMap.mul ℝ ℝ) := by
  have hn := PDE.Analysis.ae_convolutionExistsAt_of_integrable_memLp_two
    integrable_nearFiveDimensionalGamma hf
  have ht := PDE.Analysis.ae_convolutionExistsAt_of_integrable_memLp_two
    hfi memLp_farFiveDimensionalGamma
  filter_upwards [hn, ht] with X hn ht
  constructor
  · exact hn
  · change Integrable (fun Y ↦ farFiveDimensionalGamma Y * f (X - Y)) volume
    have hs : Integrable (fun Y ↦ f (X - Y) * farFiveDimensionalGamma Y) volume :=
      ht.integrable_swap
    exact hs.congr (Filter.Eventually.of_forall fun Y ↦ mul_comm _ _)

/-- An `L¹ ∩ L²` source has an absolutely convergent Newtonian integral almost everywhere.
The kernel is integrable near its singularity and square-integrable at infinity; the
two pieces use the two source hypotheses in opposite orders. -/
theorem ae_convolutionExistsAt_fundamentalSolution_five_of_integrable
    {f : ℝ^5 → ℝ} (hfi : Integrable f volume)
    (hf : MemLp f 2 volume) :
    ∀ᵐ X ∂volume, ConvolutionExistsAt (fundamentalSolution 5) f X
      (ContinuousLinearMap.mul ℝ ℝ) := by
  filter_upwards [ae_convolutionExistsAt_near_far hfi hf] with X hX
  have hn : Integrable (fun Y ↦ nearFiveDimensionalGamma Y * f (X - Y)) volume := hX.1
  have ht : Integrable (fun Y ↦ farFiveDimensionalGamma Y * f (X - Y)) volume := hX.2
  have hs : Integrable (fun Y ↦
      nearFiveDimensionalGamma Y * f (X - Y) +
        farFiveDimensionalGamma Y * f (X - Y)) volume := hn.add ht
  rw [← nearFiveDimensionalGamma_add_far]
  change Integrable (fun Y ↦
    (nearFiveDimensionalGamma Y + farFiveDimensionalGamma Y) * f (X - Y)) volume
  simpa only [add_mul] using hs

/-- The Newtonian convolution of an `L¹ ∩ L²` source belongs to `L²(ℝ⁵)`.
Convolution by an `L¹` function preserves `L²`; splitting the kernel at unit distance
allows that estimate to control both its singularity and its tail. -/
theorem memLp_fundamentalSolution_five_convolution_of_integrable
    {f : ℝ^5 → ℝ} (hfi : Integrable f volume)
    (hf : MemLp f 2 volume) :
    MemLp (convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume)
      2 volume := by
  have hn : MemLp
      (convolution nearFiveDimensionalGamma f (ContinuousLinearMap.mul ℝ ℝ) volume)
      2 volume := by
    have h := PDE.Analysis.memLp_convolution_two integrable_nearFiveDimensionalGamma hf
    change MemLp (fun X ↦ ∫ Y, nearFiveDimensionalGamma Y * f (X - Y)) 2 volume at h ⊢
    exact h
  have ht : MemLp
      (convolution farFiveDimensionalGamma f (ContinuousLinearMap.mul ℝ ℝ) volume)
      2 volume := by
    have heq : convolution farFiveDimensionalGamma f (ContinuousLinearMap.mul ℝ ℝ) volume =
        convolution f farFiveDimensionalGamma (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
      funext X
      rw [convolution_mul_swap]
      change (∫ Y, farFiveDimensionalGamma (X - Y) * f Y) =
        ∫ Y, f Y * farFiveDimensionalGamma (X - Y)
      apply integral_congr_ae
      filter_upwards with Y
      exact mul_comm _ _
    rw [heq]
    exact PDE.Analysis.memLp_convolution_two hfi memLp_farFiveDimensionalGamma
  have heq :
      convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume =ᵐ[volume]
        convolution nearFiveDimensionalGamma f (ContinuousLinearMap.mul ℝ ℝ) volume +
          convolution farFiveDimensionalGamma f (ContinuousLinearMap.mul ℝ ℝ) volume := by
    filter_upwards [ae_convolutionExistsAt_near_far hfi hf] with X hX
    rw [← nearFiveDimensionalGamma_add_far]
    exact hX.1.add_distrib hX.2
  exact (hn.add ht).ae_eq heq.symm

/-- A square-integrable source that vanishes almost everywhere outside a compact set
has an `L²` Newtonian potential. Finite volume supplies the `L¹` source hypothesis;
no continuity or boundary trace of the source is needed. -/
theorem memLp_fundamentalSolution_five_convolution_of_ae_compact_support
    {f : ℝ^5 → ℝ} {K : Set ℝ^5}
    (hf : MemLp f 2 volume) (hK : IsCompact K)
    (hf0 : ∀ᵐ X ∂volume, X ∉ K → f X = 0) :
    MemLp (convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume)
      2 volume := by
  have hlocal : IntegrableOn f K volume :=
    (integrableOn_Lp_of_measure_ne_top (hf.toLp f)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hK.measure_lt_top.ne).congr
        (ae_restrict_of_ae hf.coeFn_toLp)
  exact memLp_fundamentalSolution_five_convolution_of_integrable
    (hlocal.integrable_of_ae_notMem_eq_zero hf0) hf

/-- Cauchy–Schwarz against the support indicator bounds the `L¹` norm by the `L²` norm.
The norm of this indicator is the square root of the support volume. -/
private theorem integral_norm_le_indicator_norm_mul
    {f : ℝ^5 → ℝ} {K : Set (ℝ^5)} (hf : MemLp f 2 volume) (hK : IsCompact K)
    (hf0 : ∀ᵐ X ∂volume, X ∉ K → f X = 0) :
    (∫ X, ‖f X‖) ≤
      ‖indicatorConstLp (μ := volume) 2 hK.measurableSet hK.measure_lt_top.ne (1 : ℝ)‖ *
        ‖hf.toLp f‖ := by
  let u : Lp ℝ 2 (volume : Measure (ℝ^5)) := hf.norm.toLp (fun X ↦ ‖f X‖)
  have hnorm : ‖u‖ = ‖hf.toLp f‖ := by
    simp only [u, Lp.norm_toLp, eLpNorm_norm f hf.aestronglyMeasurable]
  calc
    (∫ X, ‖f X‖) =
        inner ℝ (indicatorConstLp (μ := volume) 2 hK.measurableSet
          hK.measure_lt_top.ne (1 : ℝ)) u := by
      rw [L2.inner_indicatorConstLp_one, ← integral_indicator hK.measurableSet]
      apply integral_congr_ae
      filter_upwards [hf.norm.coeFn_toLp, hf0] with X hu hx
      by_cases hX : X ∈ K
      · rw [Set.indicator_of_mem hX]
        exact hu.symm
      · rw [Set.indicator_of_notMem hX, hx hX, norm_zero]
    _ ≤ ‖indicatorConstLp (μ := volume) 2 hK.measurableSet hK.measure_lt_top.ne (1 : ℝ)‖ *
        ‖u‖ :=
      real_inner_le_norm _ _
    _ = _ := by rw [hnorm]

/-- Split the kernel at unit distance. Its near part acts on the source in `L²`;
for the far part, scalar convolution commutes and the source acts as an `L¹` kernel. -/
private theorem norm_fundamentalSolution_five_convolution_le_near_far
    {f : ℝ^5 → ℝ} (hfi : Integrable f volume) (hf : MemLp f 2 volume) :
    ‖(memLp_fundamentalSolution_five_convolution_of_integrable hfi hf).toLp
        (convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume)‖ ≤
      (∫ X, ‖nearFiveDimensionalGamma X‖) * ‖hf.toLp f‖ +
        (∫ X, ‖f X‖) * ‖memLp_farFiveDimensionalGamma.toLp farFiveDimensionalGamma‖ := by
  let un : Lp ℝ 2 (volume : Measure (ℝ^5)) :=
    PDE.Analysis.convolutionL2CLM nearFiveDimensionalGamma
      integrable_nearFiveDimensionalGamma (hf.toLp f)
  let ut : Lp ℝ 2 (volume : Measure (ℝ^5)) :=
    PDE.Analysis.convolutionL2CLM f hfi
      (memLp_farFiveDimensionalGamma.toLp farFiveDimensionalGamma)
  have hn : (fun X ↦ un X) =ᵐ[volume]
      convolution nearFiveDimensionalGamma f (ContinuousLinearMap.mul ℝ ℝ) volume :=
    (PDE.Analysis.convolutionL2CLM_ae_eq nearFiveDimensionalGamma
      integrable_nearFiveDimensionalGamma _).trans (.of_eq
        (convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ) .rfl hf.coeFn_toLp))
  have ht : (fun X ↦ ut X) =ᵐ[volume]
      convolution farFiveDimensionalGamma f (ContinuousLinearMap.mul ℝ ℝ) volume := by
    refine (PDE.Analysis.convolutionL2CLM_ae_eq f hfi _).trans (.of_eq ?_)
    rw [convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ) .rfl
      memLp_farFiveDimensionalGamma.coeFn_toLp]
    funext X
    rw [convolution_mul_swap]
    exact integral_congr_ae (.of_forall fun Y ↦ mul_comm _ _)
  have heq :
      (memLp_fundamentalSolution_five_convolution_of_integrable hfi hf).toLp
        (convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume) =
          un + ut := by
    apply Lp.ext
    filter_upwards [(memLp_fundamentalSolution_five_convolution_of_integrable hfi hf).coeFn_toLp,
      Lp.coeFn_add un ut, hn, ht, ae_convolutionExistsAt_near_far hfi hf] with X hp hs hn ht hX
    rw [hp, hs, Pi.add_apply, hn, ht, ← (hX.1.add_distrib hX.2), nearFiveDimensionalGamma_add_far]
  rw [heq]
  exact (norm_add_le un ut).trans (add_le_add
    (ContinuousLinearMap.le_of_opNorm_le _ (PDE.Analysis.norm_convolutionL2CLM_le (E := ℝ) _ _) _)
    (ContinuousLinearMap.le_of_opNorm_le _ (PDE.Analysis.norm_convolutionL2CLM_le (E := ℝ) _ _) _))

/-- On a fixed compact source set, the Newtonian potential is bounded in `L²` by the
`L²` source norm. Cauchy–Schwarz on the support supplies the `L¹` bound needed for the
kernel's tail. The constant depends on the support, not on the source; no continuity,
radial symmetry, or zero mean is required. -/
theorem exists_norm_fundamentalSolution_five_convolution_le_of_ae_compact_support
    (K : Set (ℝ^5)) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ℝ^5 → ℝ) (hf : MemLp f 2 volume)
      (hf0 : ∀ᵐ X ∂volume, X ∉ K → f X = 0),
      ‖(memLp_fundamentalSolution_five_convolution_of_ae_compact_support hf hK hf0).toLp
          (convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume)‖ ≤
        C * ‖hf.toLp f‖ := by
  let a : ℝ := ∫ X, ‖nearFiveDimensionalGamma X‖
  let b : ℝ := ‖memLp_farFiveDimensionalGamma.toLp farFiveDimensionalGamma‖
  let I : Lp ℝ 2 (volume : Measure (ℝ^5)) :=
    indicatorConstLp 2 hK.measurableSet hK.measure_lt_top.ne (1 : ℝ)
  refine ⟨a + ‖I‖ * b, add_nonneg (integral_nonneg fun X ↦ norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)), ?_⟩
  intro f hf hf0
  have hlocal : IntegrableOn f K volume :=
    (integrableOn_Lp_of_measure_ne_top (hf.toLp f)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hK.measure_lt_top.ne).congr
        (ae_restrict_of_ae hf.coeFn_toLp)
  have hfi : Integrable f volume := hlocal.integrable_of_ae_notMem_eq_zero hf0
  calc
    _ ≤ a * ‖hf.toLp f‖ + (∫ X, ‖f X‖) * b :=
      norm_fundamentalSolution_five_convolution_le_near_far hfi hf
    _ ≤ a * ‖hf.toLp f‖ + (‖I‖ * ‖hf.toLp f‖) * b :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right
        (integral_norm_le_indicator_norm_mul hf hK hf0) (norm_nonneg _))
    _ = (a + ‖I‖ * b) * ‖hf.toLp f‖ := by
      rw [add_mul, mul_right_comm ‖I‖ ‖hf.toLp f‖ b]

/-- A continuous compact source has an `L²` Newtonian potential. Its `L¹ ∩ L²`
membership is enough; no derivatives of the source are required. -/
theorem memLp_fundamentalSolution_five_convolution
    (f : ℝ^5 → ℝ) (hf : Continuous f)
    (hfc : HasCompactSupport f) :
    MemLp (convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume)
      2 volume := by
  exact memLp_fundamentalSolution_five_convolution_of_integrable
    (hf.integrable_of_hasCompactSupport hfc) (hf.memLp_of_hasCompactSupport hfc)

/-- Every Cartesian Hessian entry of the Newtonian convolution is square integrable
for a compactly supported `C²` source on `ℝ⁵`. Both derivatives move onto the source,
whose continuity and compact support give the same integrable tail as the potential. -/
theorem fundamentalSolution_five_convolution_iteratedPartialDeriv_two_memLp
    (f : ℝ^5 → ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (i j : Fin 5) :
    MemLp (fun X ↦ iteratedPartialDeriv (n := 5) [i, j]
      (convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume) X)
      2 volume := by
  let dg : ℝ^5 → ℝ := fun X ↦ (∂[j] f) X
  have hdgc : HasCompactSupport dg := by
    simpa only [dg, partialDeriv] using
      hfc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single j (1 : ℝ))
  have hdg : ContDiff ℝ 1 dg := by
    simpa only [dg, partialDeriv] using
      (hf.fderiv_right (m := 1) (n := 2) (by norm_num)).clm_apply
        (contDiff_const : ContDiff ℝ 1 fun _ : ℝ^5 ↦
          EuclideanSpace.single j (1 : ℝ))
  have hddgc : HasCompactSupport (fun X ↦ (∂[i] dg) X) := by
    simpa only [partialDeriv] using
      hdgc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i (1 : ℝ))
  have hddg : Continuous (fun X ↦ (∂[i] dg) X) := by
    simpa only [partialDeriv] using
      ((hdg.fderiv_right (m := 0) (n := 1) (by norm_num)).clm_apply
        (contDiff_const : ContDiff ℝ 0 fun _ : ℝ^5 ↦
          EuclideanSpace.single i (1 : ℝ))).continuous
  have heq : (fun X ↦ iteratedPartialDeriv (n := 5) [i, j]
      (convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume) X) =
      convolution (fundamentalSolution 5) (fun X ↦ (∂[i] dg) X)
        (ContinuousLinearMap.mul ℝ ℝ) volume := by
    funext X
    exact PDE.Analysis.convolution_iteratedPartialDeriv_two_right
      (fundamentalSolution 5) f (locallyIntegrable_fundamentalSolution 5) hfc hf i j X
  rw [heq]
  exact memLp_fundamentalSolution_five_convolution _ hddg hddgc


/-- Every finite coordinate derivative of the Newtonian convolution of a smooth
compact source lies in `L²(ℝ⁵)`. Derivatives move onto the source and remain compactly
supported, so the single potential tail estimate applies to every word. -/
theorem fundamentalSolution_five_convolution_iteratedPartialDeriv_memLp_two
    (f : ℝ^5 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) (alpha : List (Fin 5)) :
    MemLp (fun X ↦ iteratedPartialDeriv (n := 5) alpha
      (convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume) X)
      2 volume := by
  have heq : (fun X ↦ iteratedPartialDeriv (n := 5) alpha
      (convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume) X) =
      convolution (fundamentalSolution 5)
        (fun Y ↦ iteratedPartialDeriv (n := 5) alpha f Y)
        (ContinuousLinearMap.mul ℝ ℝ) volume := by
    funext X
    exact PDE.Analysis.convolution_iteratedPartialDeriv_right
      (fundamentalSolution 5) f (locallyIntegrable_fundamentalSolution 5) hfc hf alpha X
  rw [heq]
  exact memLp_fundamentalSolution_five_convolution _
    (PDE.contDiff_top_iteratedPartialDeriv hf alpha).continuous
    (SobolevSpace.hasCompactSupport_iteratedPartialDeriv hfc alpha)

/-- Two derivatives of the convolution agree with pairing the kernel against the
translated test-function Hessian. The two signs from `X - Y` cancel. -/
theorem fundamentalSolution_five_convolution_hessian_eq_translatedPairing
    (i j : Fin 5) (X : ℝ^5) (φ : 𝓓((⊤ : TopologicalSpace.Opens (ℝ^5)), ℝ)) :
    iteratedPartialDeriv (n := 5) [i, j]
        (convolution (fundamentalSolution 5) φ.toFun (ContinuousLinearMap.mul ℝ ℝ) volume) X =
      ∫ Y : ℝ^5, (fundamentalSolution 5) Y *
        iteratedPartialDeriv (n := 5) [i, j]
          (fiveDimensionalConvolutionTestFunction X φ).toFun Y := by
  rw [PDE.Analysis.convolution_iteratedPartialDeriv_two_right
    (fundamentalSolution 5) φ.toFun (locallyIntegrable_fundamentalSolution 5)
    φ.hasCompactSupport (φ.contDiff.of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))) i j X]
  rw [convolution]
  apply integral_congr_ae
  filter_upwards [] with Y
  have hchain := SobolevSpace.Approximation.iteratedPartialDeriv_comp_const_sub
    (n := 5) [i, j] (φ.contDiff.of_le (by simp)) X Y
  change (fundamentalSolution 5) Y *
      iteratedPartialDeriv (n := 5) [i, j] φ.toFun (X - Y) =
    (fundamentalSolution 5) Y *
      iteratedPartialDeriv (n := 5) [i, j] (fun Z ↦ φ (X - Z)) Y
  rw [hchain]
  norm_num

/-- If a smooth compact source vanishes at `X`, the classical Hessian kernel is
absolutely integrable against the source and gives the Hessian of its Newtonian
potential at `X`. Vanishing at this single point removes the local Dirac term;
no principal value or boundary term remains. -/
theorem fundamentalSolution_five_convolution_hessian_eq_integral_of_zero
    (f : ℝ^5 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) (i j : Fin 5) (X : ℝ^5)
    (hzero : f X = 0) :
    Integrable (fun Y : ℝ^5 ↦
      iteratedPartialDeriv (n := 5) [i, j] (fundamentalSolution 5) (X - Y) * f Y) ∧
      iteratedPartialDeriv (n := 5) [i, j]
        (convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume) X =
      ∫ Y : ℝ^5,
        iteratedPartialDeriv (n := 5) [i, j] (fundamentalSolution 5) (X - Y) * f Y := by
  let φ : 𝓓((⊤ : TopologicalSpace.Opens (ℝ^5)), ℝ) :=
    { toFun := f
      contDiff' := hf
      hasCompactSupport' := hfc
      tsupport_subset' := Set.subset_univ _ }
  let ψ := fiveDimensionalConvolutionTestFunction X φ
  obtain ⟨hint, hpair⟩ := fundamentalSolution_five_distributionalHessian_eq_classical_of_zero j i
    ψ (show f (X - 0) = 0 by rwa [sub_zero])
  have hcomm : iteratedPartialDeriv (n := 5) [j, i] ψ.toFun =
      iteratedPartialDeriv (n := 5) [i, j] ψ.toFun :=
    PDE.partialDeriv_partialDeriv_comm_of_contDiff j i
      (ψ.contDiff.of_le (WithTop.coe_le_coe.mpr le_top))
  rw [hcomm] at hpair
  have hshift (Y : ℝ^5) : ψ.toFun (X - Y) = f Y :=
    show f (X - (X - Y)) = f Y by rw [sub_sub_cancel]
  have hchange :
      (∫ Y : ℝ^5,
        iteratedPartialDeriv (n := 5) [i, j] (fundamentalSolution 5) (X - Y) * f Y) =
      ∫ Y : ℝ^5,
        iteratedPartialDeriv (n := 5) [i, j] (fundamentalSolution 5) Y * ψ.toFun Y := by
    simpa only [hshift] using
      (integral_sub_left_eq_self
        (fun Y : ℝ^5 ↦
          iteratedPartialDeriv (n := 5) [i, j] (fundamentalSolution 5) Y * ψ.toFun Y)
        (volume : Measure (ℝ^5)) X)
  refine ⟨?_, ?_⟩
  · simpa only [hshift] using hint.comp_sub_left X
  · exact (fundamentalSolution_five_convolution_hessian_eq_translatedPairing i j X φ).trans
      (hpair.trans hchange.symm)

/-- The Newtonian convolution of a smooth compact source on `ℝ⁵` solves `-ΔU = f`
at every point. Moving both derivatives onto the source lets the distributional
identity for the fundamental solution act on a translated compact test function. -/
theorem fundamentalSolution_five_convolution_solves_poisson
    (f : ℝ^5 → ℝ) (X : ℝ^5) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) :
    -(∑ i : Fin 5, iteratedPartialDeriv (n := 5) [i, i]
      (convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume) X) = f X := by
  let φ : 𝓓^{2}((⊤ : TopologicalSpace.Opens (ℝ^5)), ℝ) :=
    { toFun := f
      contDiff' := hf.of_le (WithTop.coe_le_coe.mpr le_top)
      hasCompactSupport' := hfc
      tsupport_subset' := Set.subset_univ _ }
  change -PDE.laplacian (PoissonEquation.fundamentalSolutionConvolution 5 φ) X = φ X
  exact PoissonEquation.negative_laplacian_fundamentalSolutionConvolution
    (by norm_num : 2 ≤ 5) φ X

end PotentialTheory
