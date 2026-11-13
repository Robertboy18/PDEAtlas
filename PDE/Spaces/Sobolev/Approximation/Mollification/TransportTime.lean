/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.MollifiedCoefficientContinuity
public import PDE.Spaces.Sobolev.Approximation.Mollification.TransportCommutatorBound
import PDE.Analysis.MeasureTheory.DominatedLp

/-!
# Mollified transport and commutators in Bochner spaces

The coefficient's base coordinate is continuous in L∞ on the closed time
interval. Its weak spatial derivatives have uniform L∞ bounds but need not
be continuous in time. At each positive mollifier scale, the smoothed
derivative product is jointly continuous in time and the L² input.

This continuity gives Bochner measurability before any norm estimate is used.
The mollified transport row therefore belongs to the same Bochner
Lp space as its input. For finite exponents at least one, the transport
commutator converges to zero in that space: its spatial uniform bound gives
an integrable dominator, and its spatial strong convergence gives the
pointwise limit. No convergence of the input is required.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology Sobolev

namespace SobolevSpace.Approximation

open GraphSpace

variable {n : ℕ}

local notation "L2" => DerivLp n 2 univ

/-- Clipping the time coordinate extends the continuous family beyond the interval.
This gives a measurable composition for an arbitrary Bochner-measurable input. -/
private theorem aestronglyMeasurable_apply_of_continuousOn_prod
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {a b : ℝ} (hab : a ≤ b) {f : ℝ × E → F}
    (hf : ContinuousOn f (Icc a b ×ˢ univ))
    {u : ℝ → E} (hu : AEStronglyMeasurable u (volume.restrict (Ioc a b))) :
    AEStronglyMeasurable (fun t ↦ f (t, u t)) (volume.restrict (Ioc a b)) := by
  let c : ℝ → ℝ := fun t ↦ max a (min b t)
  have hc : Continuous c := continuous_const.max (continuous_const.min continuous_id)
  have hcI (t : ℝ) : c t ∈ Icc a b :=
    ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
  have hext : Continuous (fun z : ℝ × E ↦ f (c z.1, z.2)) :=
    hf.comp_continuous ((hc.comp continuous_fst).prodMk continuous_snd)
      (fun z ↦ ⟨hcI z.1, mem_univ _⟩)
  have hmeas := hext.comp_aestronglyMeasurable
    (continuous_id.aestronglyMeasurable.prodMk hu)
  apply hmeas.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have hct : c t = t := by
    dsimp only [c]
    rw [min_eq_right ht.2, max_eq_right ht.1.le]
  simp only [id_eq, hct]

/-- The L∞–L² multiplication map is bounded bilinear, so a continuous base
coefficient gives a jointly continuous multiplier. -/
private theorem continuousOn_lpSMul_base
    {X : Type*} [TopologicalSpace X] {s : Set X}
    (A : X → W^{1,∞}(ℝ^n))
    (hA : ContinuousOn
      (fun t ↦ (A t : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) s) :
    ContinuousOn (fun z : X × L2 ↦
      ((A z.1 : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) • z.2)
      (s ×ˢ univ) := by
  let T : DerivLp n ∞ univ →L[ℝ] L2 →L[ℝ] L2 :=
    (ContinuousLinearMap.lsmul ℝ ℝ :
      ℝ →L[ℝ] ℝ →L[ℝ] ℝ).holderL (domainMeasure n univ) ∞ 2 2
  have hT (c : DerivLp n ∞ univ) (v : L2) : T c v = c • v := by
    apply Lp.ext
    filter_upwards [(ContinuousLinearMap.lsmul ℝ ℝ :
      ℝ →L[ℝ] ℝ →L[ℝ] ℝ).coeFn_holder (r := 2) c v,
      Lp.coeFn_lpSMul (r := 2) c v] with x hleft hright
    exact hleft.trans hright.symm
  have hbase : ContinuousOn
      (fun z : X × L2 ↦ (A z.1 : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1))
      (s ×ˢ univ) := hA.comp continuous_fst.continuousOn (fun _ hz ↦ hz.1)
  have hcont := (T.continuous.comp_continuousOn hbase).clm_apply
    continuous_snd.continuousOn
  simpa only [Function.comp_apply, hT] using hcont

/-- A continuous L∞ base coefficient multiplies a Bochner Lp input into the same
space. Compactness of the closed time interval supplies the coefficient norm bound. -/
theorem memLp_coefficientBase_mul
    {a b : ℝ} (hab : a ≤ b) (A : ℝ → W^{1,∞}(ℝ^n))
    (hA : ContinuousOn
      (fun t ↦ (A t : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) (Icc a b))
    {p : ℝ≥0∞} {u : ℝ → L2} (hu : MemLp u p (volume.restrict (Ioc a b))) :
    MemLp (fun t ↦ ((A t : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) • u t)
      p (volume.restrict (Ioc a b)) := by
  have hmeas := aestronglyMeasurable_apply_of_continuousOn_prod hab
    (continuousOn_lpSMul_base A hA) hu.aestronglyMeasurable
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
  refine hu.of_le_mul (c := max 0 M) hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact (Lp.norm_smul_le _ _).trans (mul_le_mul_of_nonneg_right
    ((hM t (Ioc_subset_Icc_self ht)).trans (le_max_right _ _)) (norm_nonneg _))

/-- A uniformly bounded weak spatial derivative, multiplied by a Bochner-measurable
L² input, is Bochner measurable even without time continuity of that derivative.
At each positive scale its mollification is measurable; spatial strong convergence
identifies the pointwise L² limit. -/
theorem aestronglyMeasurable_coefficientDerivative_mul
    {a b : ℝ} (hab : a ≤ b) (A : ℝ → W^{1,∞}(ℝ^n))
    (hA : ContinuousOn
      (fun t ↦ (A t : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) (Icc a b))
    (j : Fin n) (L : ℝ≥0)
    (hL : ∀ t ∈ Icc a b,
      ‖(A t : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)‖ ≤ L)
    {u : ℝ → L2} (hu : AEStronglyMeasurable u (volume.restrict (Ioc a b))) :
    AEStronglyMeasurable
      (fun t ↦ ((A t : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)) • u t)
      (volume.restrict (Ioc a b)) := by
  let ε : ℕ → ℝ := fun k ↦ 1 / (k + 1 : ℝ)
  have hε (k : ℕ) : 0 < ε k := by dsimp only [ε]; positivity
  have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have happrox (k : ℕ) : AEStronglyMeasurable
      (fun t ↦ mollifierRowCLM (standardMollifier n) (hε k)
        (((A t : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)) • u t))
      (volume.restrict (Ioc a b)) :=
    aestronglyMeasurable_apply_of_continuousOn_prod hab
      (continuousOn_mollifierRowCLM_coefficientDerivative_mul
        (standardMollifier n) (hε k) A hA j L hL) hu
  exact aestronglyMeasurable_of_tendsto_ae atTop happrox
    (Eventually.of_forall fun t ↦ tendsto_mollifierRowCLM
      (standardMollifier n) ε hε hε0
        (((A t : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)) • u t))

/-- Multiplication by the indicated weak spatial derivative preserves every Bochner
Lp class under a uniform L∞ derivative bound. Measurability follows from the mollified
limit argument; it is not inferred from the displayed norm estimate. -/
theorem memLp_coefficientDerivative_mul
    {a b : ℝ} (hab : a ≤ b) (A : ℝ → W^{1,∞}(ℝ^n))
    (hA : ContinuousOn
      (fun t ↦ (A t : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) (Icc a b))
    (j : Fin n) (L : ℝ≥0)
    (hL : ∀ t ∈ Icc a b,
      ‖(A t : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)‖ ≤ L)
    {p : ℝ≥0∞} {u : ℝ → L2} (hu : MemLp u p (volume.restrict (Ioc a b))) :
    MemLp (fun t ↦ ((A t : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)) • u t)
      p (volume.restrict (Ioc a b)) := by
  refine hu.of_le_mul (c := (L : ℝ))
    (aestronglyMeasurable_coefficientDerivative_mul hab A hA j L hL
      hu.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact (Lp.norm_smul_le _ _).trans (mul_le_mul_of_nonneg_right
    (hL t (Ioc_subset_Icc_self ht)) (norm_nonneg _))

/-- At fixed positive scale, mollifying `-a ∂ⱼu` gives a Bochner Lp row
`-Dεⱼ(a u) + Jε((∂ⱼa)u)`. Only base-coefficient continuity and a bound on
the indicated weak derivative are needed; the input has no spatial derivative. -/
theorem memLp_mollified_transport_row
    (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    {a b : ℝ} (hab : a ≤ b) (A : ℝ → W^{1,∞}(ℝ^n))
    (hA : ContinuousOn
      (fun t ↦ (A t : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) (Icc a b))
    (j : Fin n) (L : ℝ≥0)
    (hL : ∀ t ∈ Icc a b,
      ‖(A t : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)‖ ≤ L)
    {p : ℝ≥0∞} {u : ℝ → L2} (hu : MemLp u p (volume.restrict (Ioc a b))) :
    MemLp (fun t ↦
      -mollifierDerivativeRowCLM μ hε j
          (((A t : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) • u t) +
        mollifierRowCLM μ hε
          (((A t : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)) • u t))
      p (volume.restrict (Ioc a b)) := by
  have hbase := memLp_coefficientBase_mul hab A hA hu
  have hderiv := memLp_coefficientDerivative_mul hab A hA j L hL hu
  have hsum := ((mollifierDerivativeRowCLM μ hε j).comp_memLp' hbase).neg.add
    ((mollifierRowCLM μ hε).comp_memLp' hderiv)
  simpa only [Function.comp_def, Pi.neg_def, Pi.add_def] using hsum

/-- At each positive scale, the transport commutator belongs to the
same Bochner Lp space as its input. Base-coefficient continuity supplies
measurability; only the indicated weak derivative needs a uniform bound. -/
theorem memLp_mollifierTransportCommutatorCLM
    (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    {a b : ℝ} (hab : a ≤ b) (A : ℝ → W^{1,∞}(ℝ^n))
    (hA : ContinuousOn
      (fun t ↦ (A t : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) (Icc a b))
    (j : Fin n) (L : ℝ≥0)
    (hL : ∀ t ∈ Icc a b,
      ‖(A t : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)‖ ≤ L)
    {p : ℝ≥0∞} {u : ℝ → L2} (hu : MemLp u p (volume.restrict (Ioc a b))) :
    MemLp (fun t ↦ mollifierTransportCommutatorCLM μ hε (A t) j (u t))
      p (volume.restrict (Ioc a b)) := by
  let K := mollifierDerivativeRowCLM μ hε j
  have hprincipalLp := memLp_coefficientBase_mul hab A hA (K.comp_memLp' hu)
  have hsum := hprincipalLp.add
    (memLp_mollified_transport_row μ hε hab A hA j L hL hu)
  apply hsum.ae_eq
  filter_upwards with t
  change _ + (-_ + _) = mollifierTransportCommutatorCLM μ hε (A t) j (u t)
  rw [mollifierTransportCommutatorCLM_apply]
  dsimp only [K, Function.comp_apply]
  abel

/-- The transport commutator tends to zero in Bochner Lp for every finite
exponent at least one. A uniform bound on the sum of all weak spatial
derivatives controls the commutators; no time continuity of those derivatives
or supplied Bochner convergence is assumed. -/
theorem tendsto_eLpNorm_mollifierTransportCommutatorCLM
    (μ : Mollifier n) (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k)
    (hε0 : Tendsto ε atTop (𝓝 0))
    {a b : ℝ} (hab : a ≤ b) (A : ℝ → W^{1,∞}(ℝ^n))
    (hA : ContinuousOn
      (fun t ↦ (A t : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) (Icc a b))
    (L : ℝ≥0)
    (hL : ∀ t ∈ Icc a b,
      (∑ l : Fin n, ‖(A t : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n l)‖) ≤ L)
    (j : Fin n) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    {u : ℝ → L2} (hu : MemLp u p (volume.restrict (Ioc a b))) :
    Tendsto (fun k ↦ eLpNorm
      (fun t ↦ mollifierTransportCommutatorCLM μ (hε k) (A t) j (u t))
      p (volume.restrict (Ioc a b))) atTop (𝓝 0) := by
  classical
  let M : ℝ := ∫ x, ‖x‖ * ‖(∂[j] μ.ρ) x‖
  have hM : 0 ≤ M := integral_nonneg fun _ ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _)
  let C : ℝ := (L : ℝ) * M + L
  have hC : 0 ≤ C := add_nonneg (mul_nonneg L.prop hM) L.prop
  have hderiv (t : ℝ) (ht : t ∈ Icc a b) :
      ‖(A t : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)‖ ≤ L :=
    (Finset.single_le_sum (fun l _ ↦ norm_nonneg
      ((A t : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n l)))
      (Finset.mem_univ j)).trans (hL t ht)
  have hmeas (k : ℕ) : AEStronglyMeasurable
      (fun t ↦ mollifierTransportCommutatorCLM μ (hε k) (A t) j (u t))
      (volume.restrict (Ioc a b)) :=
    (memLp_mollifierTransportCommutatorCLM μ (hε k) hab A hA j L hderiv
      hu).aestronglyMeasurable
  have hbound : MemLp (fun t ↦ C * ‖u t‖) p (volume.restrict (Ioc a b)) :=
    hu.norm.const_mul C
  have hdom (k : ℕ) : ∀ᵐ t ∂volume.restrict (Ioc a b),
      ‖mollifierTransportCommutatorCLM μ (hε k) (A t) j (u t)‖ ≤ ‖C * ‖u t‖‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC (norm_nonneg _))]
    apply (norm_mollifierTransportCommutatorCLM_apply_le μ (hε k) (A t) j (u t)).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact add_le_add
      (mul_le_mul_of_nonneg_right (hL t (Ioc_subset_Icc_self ht)) hM)
      (hderiv t (Ioc_subset_Icc_self ht))
  have hzero : MemLp (fun _ : ℝ ↦ (0 : L2)) p (volume.restrict (Ioc a b)) := MemLp.zero
  have hconv := tendsto_Lp_of_tendsto_ae_of_ae_norm_le hp hp_top hmeas hzero hbound hdom
    (Filter.Eventually.of_forall fun t ↦
      tendsto_mollifierTransportCommutatorCLM μ ε hε hε0 (A t) j (u t))
  have hzero_fun : (fun _ : ℝ ↦ (0 : L2)) = 0 := rfl
  simpa only [hzero_fun, sub_zero] using hconv

end SobolevSpace.Approximation
