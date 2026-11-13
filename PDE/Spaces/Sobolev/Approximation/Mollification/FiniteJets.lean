/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.ConvolutionDerivative
public import PDE.Analysis.MeasureTheory.Lp.CommonSupportConvergence
public import PDE.Spaces.Sobolev.Approximation.Mollification.Radial
public import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Definitions
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Mollification of finite differentiability jets

Coordinate derivatives through the available finite order commute with convolution against a
compact kernel. Applying the approximate-identity theorem to each continuous derivative gives
uniform jet convergence on the whole space with one common compact support. Radial kernels
preserve coordinate evenness, and a fixed even bump preserves a zero value at the origin.
-/

@[expose] public section

noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Filter Set
open scoped ENNReal Topology Pointwise

namespace PDE.Analysis

variable {n m : ℕ}

/-- A derivative word of length at most `m` transfers through convolution with a compactly
supported `C^m` right factor. -/
theorem convolution_iteratedPartialDeriv_right_of_contDiff
    (f g : ℝ^n → ℝ) (hf : LocallyIntegrable f volume) (hgc : HasCompactSupport g)
    (hg : ContDiff ℝ m g) (indices : List (Fin n)) (hindices : indices.length ≤ m) :
    iteratedPartialDeriv indices (convolution f g (ContinuousLinearMap.mul ℝ ℝ) volume) =
      convolution f (iteratedPartialDeriv indices g) (ContinuousLinearMap.mul ℝ ℝ) volume := by
  induction indices with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.length_cons] at hindices
    have hrest : rest.length ≤ m := by omega
    have hregular : ContDiff ℝ 1 (iteratedPartialDeriv rest g) := by
      apply (contDiff_iteratedPartialDeriv_of_le hg rest hrest).of_le
      exact_mod_cast (show 1 ≤ m - rest.length by omega)
    change ∂[i]
        (iteratedPartialDeriv rest (convolution f g (ContinuousLinearMap.mul ℝ ℝ) volume)) = _
    rw [ih hrest]
    funext x
    exact convolution_partialDeriv_right f (iteratedPartialDeriv rest g) hf
      (SobolevSpace.hasCompactSupport_iteratedPartialDeriv hgc rest) hregular i x

end PDE.Analysis

namespace SobolevSpace.Approximation

variable {n m : ℕ}

/-- Mollification commutes with every coordinate derivative word through the finite
differentiability order of a compactly supported function. -/
theorem iteratedPartialDeriv_mollify_of_contDiff
    (μ : Mollifier n) {ε : ℝ} {f : ℝ^n → ℝ}
    (hf : ContDiff ℝ m f) (hfc : HasCompactSupport f)
    (indices : List (Fin n)) (hindices : indices.length ≤ m) :
    iteratedPartialDeriv indices (mollify μ ε f) =
      mollify μ ε (iteratedPartialDeriv indices f) := by
  simpa only [mollify, convolution_lsmul_eq_mul] using
    PDE.Analysis.convolution_iteratedPartialDeriv_right_of_contDiff (scaled μ ε) f
      (scaled_contDiff μ).continuous.locallyIntegrable hfc hf indices hindices

/-- Every available finite jet of the mollifications converges uniformly on each
compact set. -/
theorem iteratedPartialDeriv_mollify_tendstoUniformlyOn
    (μ : Mollifier n) {f : ℝ^n → ℝ} (hf : ContDiff ℝ m f)
    (hfc : HasCompactSupport f) (ε : ℕ → ℝ) (hεpos : ∀ j, 0 < ε j)
    (hε0 : Tendsto ε atTop (𝓝 0)) (indices : List (Fin n))
    (hindices : indices.length ≤ m) {K : Set (ℝ^n)} (hK : IsCompact K) :
    TendstoUniformlyOn (fun j ↦ iteratedPartialDeriv indices (mollify μ (ε j) f))
      (iteratedPartialDeriv indices f) atTop K := by
  have hcontinuous : Continuous (iteratedPartialDeriv indices f) :=
    (PDE.contDiff_iteratedPartialDeriv_of_le hf indices hindices).continuous
  have hlocal := mollifyVector_tendstoLocallyUniformly_of_continuous
    μ hcontinuous ε hεpos hε0
  have hon := tendstoLocallyUniformly_iff_forall_isCompact.mp hlocal K hK
  have heq : (fun j ↦ iteratedPartialDeriv indices (mollify μ (ε j) f)) =
      fun j ↦ mollifyVector μ (ε j) (iteratedPartialDeriv indices f) := by
    funext j
    rw [iteratedPartialDeriv_mollify_of_contDiff μ (ε := ε j) hf hfc indices hindices]
    rfl
  rw [heq]
  exact hon

/-- Bounded positive scales put the original profile and every mollification in one compact
set. This set is independent of the sequence index. -/
theorem exists_common_compact_mollify_support
    (μ : Mollifier n) {f : ℝ^n → ℝ} (hfc : HasCompactSupport f)
    (ε : ℕ → ℝ) (hεpos : ∀ j, 0 < ε j) (hεle : ∀ j, ε j ≤ 1) :
    ∃ K : Set (ℝ^n), IsCompact K ∧ tsupport f ⊆ K ∧
      ∀ j, tsupport (mollify μ (ε j) f) ⊆ K := by
  obtain ⟨R₀, hR₀⟩ := μ.compactSupport.isCompact.isBounded.subset_closedBall (0 : ℝ^n)
  let R : ℝ := max R₀ 0
  have hRnonneg : 0 ≤ R := le_max_right _ _
  have hR : tsupport μ.ρ ⊆ Metric.closedBall (0 : ℝ^n) R :=
    hR₀.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  let K : Set (ℝ^n) := Metric.closedBall (0 : ℝ^n) R + tsupport f
  have hK : IsCompact K := (isCompact_closedBall (0 : ℝ^n) R).add hfc.isCompact
  refine ⟨K, hK, ?_, ?_⟩
  · intro x hx
    exact ⟨0, by simpa only [Metric.mem_closedBall, dist_self] using hRnonneg,
      x, hx, zero_add x⟩
  · intro j
    apply closure_minimal _ hK.isClosed
    apply (support_mollify_subset_closedBall_add_support μ (hεpos j) hR f).trans
    apply add_subset_add _ (subset_tsupport f)
    apply Metric.closedBall_subset_closedBall
    calc
      ε j * R ≤ 1 * R := mul_le_mul_of_nonneg_right (hεle j) hRnonneg
      _ = R := one_mul R

/-- The finite jets of compactly supported profiles converge uniformly on the whole space
under mollification at positive scales bounded by one. -/
theorem iteratedPartialDeriv_mollify_tendstoUniformly
    (μ : Mollifier n) {f : ℝ^n → ℝ} (hf : ContDiff ℝ m f)
    (hfc : HasCompactSupport f) (ε : ℕ → ℝ) (hεpos : ∀ j, 0 < ε j)
    (hεle : ∀ j, ε j ≤ 1) (hε0 : Tendsto ε atTop (𝓝 0))
    (indices : List (Fin n)) (hindices : indices.length ≤ m) :
    TendstoUniformly (fun j ↦ iteratedPartialDeriv indices (mollify μ (ε j) f))
      (iteratedPartialDeriv indices f) atTop := by
  obtain ⟨K, hK, hfK, hKj⟩ := exists_common_compact_mollify_support μ hfc ε hεpos hεle
  have hon := iteratedPartialDeriv_mollify_tendstoUniformlyOn
    μ hf hfc ε hεpos hε0 indices hindices hK
  rw [Metric.tendstoUniformly_iff]
  intro δ hδ
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hon δ hδ] with j hj x
  by_cases hx : x ∈ K
  · exact hj x hx
  · have hfzero : iteratedPartialDeriv indices f x = 0 :=
      image_eq_zero_of_notMem_tsupport fun hmem ↦
        hx (hfK (tsupport_iteratedPartialDeriv_subset_tsupport indices f hmem))
    have hjzero : iteratedPartialDeriv indices (mollify μ (ε j) f) x = 0 :=
      image_eq_zero_of_notMem_tsupport fun hmem ↦
        hx (hKj j (tsupport_iteratedPartialDeriv_subset_tsupport
          indices (mollify μ (ε j) f) hmem))
    simpa only [hfzero, hjzero, dist_self] using hδ

/-- Mollification by a radial kernel preserves evenness under each coordinate reflection.
The equality follows by the measure-preserving reflection substitution. -/
theorem mollify_even_of_radial
    (μ : Mollifier n) (w : ℝ → ℝ) (hρ : ∀ x, μ.ρ x = w ‖x‖)
    {ε : ℝ} (hε : 0 < ε) (i : Fin n) {f : ℝ^n → ℝ}
    (hf : PDE.Common.IsEvenUnderCoordinateReflection i f) :
    PDE.Common.IsEvenUnderCoordinateReflection i (mollify μ ε f) := by
  intro x
  have hscaled : ∀ y, scaled μ ε (PDE.Common.coordinateReflection i y) = scaled μ ε y := by
    intro y
    simp only [scaled_of_pos μ hε, hρ, norm_smul, PDE.Common.norm_coordinateReflection]
  calc
    mollify μ ε f (PDE.Common.coordinateReflection i x) =
        ∫ y, scaled μ ε (PDE.Common.coordinateReflection i y) *
          f (PDE.Common.coordinateReflection i x - PDE.Common.coordinateReflection i y) := by
      simpa only [mollify, convolution_lsmul, smul_eq_mul, PDE.Common.coordinateReflection] using
        (MeasureTheory.integral_comp (PDE.Common.coordinateReflectionLinearIsometryEquiv i)
          (fun y ↦ scaled μ ε y * f (PDE.Common.coordinateReflection i x - y))).symm
    _ = mollify μ ε f x := by
      change (∫ y, _) = ∫ y, scaled μ ε y * f (x - y)
      apply integral_congr_ae
      filter_upwards [] with y
      rw [hscaled, ← PDE.Common.coordinateReflection_sub, hf]

/-- Every compactly supported `C^m` profile even in one coordinate has smooth even
approximants whose supports lie in one compact set and whose jets through order `m` converge
uniformly on the whole space. -/
theorem exists_even_smooth_compact_jet_approximation
    {f : ℝ^n → ℝ} (hf : ContDiff ℝ m f) (hfc : HasCompactSupport f)
    (i : Fin n) (heven : PDE.Common.IsEvenUnderCoordinateReflection i f) :
    ∃ (K : Set (ℝ^n)) (g : ℕ → ℝ^n → ℝ),
      IsCompact K ∧ tsupport f ⊆ K ∧
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (g j) ∧ tsupport (g j) ⊆ K ∧
        PDE.Common.IsEvenUnderCoordinateReflection i (g j)) ∧
      ∀ indices : List (Fin n), indices.length ≤ m →
        TendstoUniformly (fun j ↦ iteratedPartialDeriv indices (g j))
          (iteratedPartialDeriv indices f) atTop := by
  obtain ⟨μ, w, _, hρ, _⟩ := exists_radial_mollifier n
  let ε : ℕ → ℝ := fun j ↦ 1 / ((j : ℝ) + 1)
  have hεpos : ∀ j, 0 < ε j := by
    intro j
    exact one_div_pos.mpr (add_pos_of_nonneg_of_pos (Nat.cast_nonneg j) zero_lt_one)
  have hεle : ∀ j, ε j ≤ 1 := by
    intro j
    exact (div_le_one (add_pos_of_nonneg_of_pos (Nat.cast_nonneg j) zero_lt_one)).mpr
      (le_add_of_nonneg_left (Nat.cast_nonneg j))
  have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨K, hK, hfK, hgK⟩ := exists_common_compact_mollify_support μ hfc ε hεpos hεle
  refine ⟨K, fun j ↦ mollify μ (ε j) f, hK, hfK, ?_, ?_⟩
  · intro j
    exact ⟨mollify_contDiff_of_pos μ (hεpos j) f hf.continuous.locallyIntegrable,
      hgK j, mollify_even_of_radial μ w hρ (hεpos j) i heven⟩
  · intro indices hindices
    exact iteratedPartialDeriv_mollify_tendstoUniformly
      μ hf hfc ε hεpos hεle hε0 indices hindices

/-- There is one smooth compact bump equal to one at the origin and even in every
coordinate. It can normalize an entire approximating sequence. -/
theorem exists_even_compact_bump_one (n : ℕ) :
    ∃ b : ℝ^n → ℝ, ContDiff ℝ (⊤ : ℕ∞) b ∧ HasCompactSupport b ∧ b 0 = 1 ∧
      ∀ i : Fin n, PDE.Common.IsEvenUnderCoordinateReflection i b := by
  let base := ContDiffBumpBase.ofInnerProductSpace (ℝ^n)
  let b : ℝ^n → ℝ := base.toFun 2
  have htwo : (1 : ℝ) < 2 := one_lt_two
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) b :=
    base.smooth.comp_contDiff (contDiff_const.prodMk contDiff_id)
      (fun x ↦ ⟨htwo, mem_univ x⟩)
  have hcompact : HasCompactSupport b := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℝ^n) 2)
    rw [show Function.support b = Metric.ball (0 : ℝ^n) 2 from base.support 2 htwo]
    exact Metric.ball_subset_closedBall
  refine ⟨b, hsmooth, hcompact, base.eq_one 2 htwo 0 (by simp), ?_⟩
  intro i x
  simp only [b, base, ContDiffBumpBase.ofInnerProductSpace,
    PDE.Common.norm_coordinateReflection]

private theorem tendstoUniformly_const_mul_zero
    {c : ℕ → ℝ} (hc : Tendsto c atTop (𝓝 0))
    {b : ℝ^n → ℝ} (hb : Continuous b) (hbc : HasCompactSupport b) :
    TendstoUniformly (fun j x ↦ c j * b x) (fun _ ↦ 0) atTop := by
  obtain ⟨C, hC⟩ := hbc.exists_bound_of_continuous hb
  have hbound : Tendsto (fun j ↦ ‖c j‖ * C) atTop (𝓝 0) := by
    simpa using hc.norm.mul_const C
  rw [Metric.tendstoUniformly_iff]
  intro δ hδ
  filter_upwards [hbound.eventually (Iio_mem_nhds hδ)] with j hj x
  simpa only [dist_zero_left, norm_mul] using
    (mul_le_mul_of_nonneg_left (hC x) (norm_nonneg (c j))).trans_lt hj

/-- Smooth even approximation preserves the profile's origin value exactly. Subtracting
the error at the origin times one fixed even bump leaves every finite jet convergent
and enlarges the common support by only that bump's support. -/
theorem exists_even_smooth_compact_jet_approximation_preserving_origin
    {f : ℝ^n → ℝ} (hf : ContDiff ℝ m f) (hfc : HasCompactSupport f)
    (i : Fin n) (heven : PDE.Common.IsEvenUnderCoordinateReflection i f) :
    ∃ (K : Set (ℝ^n)) (g : ℕ → ℝ^n → ℝ),
      IsCompact K ∧ tsupport f ⊆ K ∧
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (g j) ∧ tsupport (g j) ⊆ K ∧
        PDE.Common.IsEvenUnderCoordinateReflection i (g j) ∧ g j 0 = f 0) ∧
      ∀ indices : List (Fin n), indices.length ≤ m →
        TendstoUniformly (fun j ↦ iteratedPartialDeriv indices (g j))
          (iteratedPartialDeriv indices f) atTop := by
  obtain ⟨K, g, hK, hfK, hg, hconv⟩ :=
    exists_even_smooth_compact_jet_approximation hf hfc i heven
  obtain ⟨b, hb, hbc, hbzero, hbeven⟩ := exists_even_compact_bump_one n
  let c : ℕ → ℝ := fun j ↦ g j 0 - f 0
  let a : ℕ → ℝ^n → ℝ := fun j ↦ g j - c j • b
  have hvalue : Tendsto (fun j ↦ g j 0) atTop (𝓝 (f 0)) := by
    simpa only [iteratedPartialDeriv] using
      (hconv [] (Nat.zero_le m)).tendsto_at 0
  have hcoef : Tendsto c atTop (𝓝 0) := by
    simpa only [sub_self] using hvalue.sub_const (f 0)
  refine ⟨K ∪ tsupport b, a, hK.union hbc.isCompact,
    hfK.trans subset_union_left, ?_, ?_⟩
  · intro j
    refine ⟨(hg j).1.sub (hb.const_smul (c j)), ?_, ?_, ?_⟩
    · exact (tsupport_sub _ _).trans (union_subset_union (hg j).2.1
        (tsupport_smul_subset_right (fun _ ↦ c j) b))
    · intro x
      change g j (PDE.Common.coordinateReflection i x) -
        c j * b (PDE.Common.coordinateReflection i x) = g j x - c j * b x
      rw [(hg j).2.2, hbeven i]
    · change g j 0 - (g j 0 - f 0) * b 0 = f 0
      rw [hbzero, mul_one, sub_sub_cancel]
  · intro indices hindices
    have hcorrection := tendstoUniformly_const_mul_zero hcoef
      (PDE.contDiff_top_iteratedPartialDeriv hb indices).continuous
      (hasCompactSupport_iteratedPartialDeriv hbc indices)
    have hjets : ∀ j, iteratedPartialDeriv indices (a j) =
        iteratedPartialDeriv indices (g j) -
          c j • iteratedPartialDeriv indices b := by
      intro j
      have hsub : iteratedPartialDeriv indices (a j) =
          iteratedPartialDeriv indices (g j) -
            iteratedPartialDeriv indices (c j • b) :=
        PDE.iteratedPartialDeriv_sub_of_contDiff indices
          ((hg j).1.of_le (by simp)) ((hb.const_smul (c j)).of_le (by simp))
      have hmul : iteratedPartialDeriv indices (c j • b) =
          c j • iteratedPartialDeriv indices b :=
        PDE.iteratedPartialDeriv_const_smul (c j) indices b
      rw [hsub, hmul]
    simp_rw [hjets]
    have hlim := (hconv indices hindices).sub hcorrection
    change TendstoUniformly
      (fun j x ↦ iteratedPartialDeriv indices (g j) x -
        c j * iteratedPartialDeriv indices b x)
      (fun x ↦ iteratedPartialDeriv indices f x - 0) atTop at hlim
    have hseq : (fun j ↦ iteratedPartialDeriv indices (g j) -
        c j • iteratedPartialDeriv indices b) =
        fun j x ↦ iteratedPartialDeriv indices (g j) x -
          c j * iteratedPartialDeriv indices b x := by
      funext j x
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [hseq]
    simpa only [sub_zero] using hlim

/-- The same even approximants preserve the origin value and converge as `Lp`
classes for every finite exponent at least one and every measure finite on their common
compact support. The sequence is chosen before the measure, so different jet rows can use
different singular weights. A zero origin value is preserved exactly. -/
theorem exists_even_smooth_compact_jet_Lp_approximation
    {f : ℝ^n → ℝ} (hf : ContDiff ℝ m f) (hfc : HasCompactSupport f)
    (i : Fin n) (heven : PDE.Common.IsEvenUnderCoordinateReflection i f) :
    ∃ (K : Set (ℝ^n)) (g : ℕ → ℝ^n → ℝ),
      IsCompact K ∧ tsupport f ⊆ K ∧
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (g j) ∧ tsupport (g j) ⊆ K ∧
        PDE.Common.IsEvenUnderCoordinateReflection i (g j) ∧ g j 0 = f 0) ∧
      ∀ indices : List (Fin n), indices.length ≤ m →
        TendstoUniformly (fun j ↦ iteratedPartialDeriv indices (g j))
          (iteratedPartialDeriv indices f) atTop ∧
        ∀ (ν : Measure (ℝ^n)) (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ → ν K ≠ ∞ →
          ∃ (hlim : MemLp (iteratedPartialDeriv indices f) p ν)
            (hseq : ∀ j, MemLp (iteratedPartialDeriv indices (g j)) p ν),
            Tendsto (fun j ↦ (hseq j).toLp (iteratedPartialDeriv indices (g j))) atTop
              (𝓝 (hlim.toLp (iteratedPartialDeriv indices f))) := by
  obtain ⟨K, g, hK, hfK, hg, hconv⟩ :=
    exists_even_smooth_compact_jet_approximation_preserving_origin hf hfc i heven
  refine ⟨K, g, hK, hfK, hg, ?_⟩
  intro indices hindices
  refine ⟨hconv indices hindices, ?_⟩
  intro ν p hpinst hp hν
  have hfcontinuous : Continuous (iteratedPartialDeriv indices f) :=
    (PDE.contDiff_iteratedPartialDeriv_of_le hf indices hindices).continuous
  have hfcompact := hasCompactSupport_iteratedPartialDeriv hfc indices
  have hfsupport : Function.support (iteratedPartialDeriv indices f) ⊆ K :=
    (subset_tsupport _).trans
      ((tsupport_iteratedPartialDeriv_subset_tsupport indices f).trans hfK)
  have hflp : MemLp (iteratedPartialDeriv indices f) p ν := by
    have htop := hfcontinuous.memLp_top_of_hasCompactSupport hfcompact ν
    exact htop.mono_exponent_of_measure_support_ne_top
      (fun x hx ↦ Function.notMem_support.mp (mt (@hfsupport x) hx)) hν le_top
  have hgsupport : ∀ j, Function.support (iteratedPartialDeriv indices (g j)) ⊆ K := by
    intro j
    exact (subset_tsupport _).trans
      ((tsupport_iteratedPartialDeriv_subset_tsupport indices (g j)).trans (hg j).2.1)
  have hglp : ∀ j, MemLp (iteratedPartialDeriv indices (g j)) p ν := by
    intro j
    have hc : HasCompactSupport (g j) :=
      HasCompactSupport.of_support_subset_isCompact hK
        ((subset_tsupport _).trans (hg j).2.1)
    have hjcontinuous := (PDE.contDiff_top_iteratedPartialDeriv (hg j).1 indices).continuous
    have htop := hjcontinuous.memLp_top_of_hasCompactSupport
      (hasCompactSupport_iteratedPartialDeriv hc indices) ν
    exact htop.mono_exponent_of_measure_support_ne_top
      (fun x hx ↦ Function.notMem_support.mp (mt (@hgsupport j x) hx)) hν le_top
  refine ⟨hflp, hglp, (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun j ↦ iteratedPartialDeriv indices (g j)) hglp
    (iteratedPartialDeriv indices f) hflp).mpr ?_⟩
  exact MeasureTheory.tendsto_eLpNorm_sub_of_tendstoUniformlyOn hp
    hK.measurableSet.nullMeasurableSet hν
    (Eventually.of_forall fun j ↦ (hglp j).aestronglyMeasurable.sub hflp.aestronglyMeasurable)
    (Eventually.of_forall hgsupport) hfsupport
    (hconv indices hindices).tendstoUniformlyOn

end SobolevSpace.Approximation
