/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.WeakFormulation
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition.LocalConvergence
import PDE.Analysis.MeasureTheory.Lp.Continuous

/-!
# Second-order weak equations and integral limits

Integrating the displacement equation against the derivative of a time test
eliminates the approximate velocity from the weak wave equation. Both initial
data remain as explicit boundary terms. This form is suited to the compact
spatial displacement and local L¹ reaction convergence of sign-preserving
truncations.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set SobolevSpace SobolevSpace.GraphSpace
open PDE.Analysis.Evolution
open scoped ENNReal Topology InnerProductSpace Sobolev SobolevSpace.WholeSpaceHilbert

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition

/-- Strong Lᵖ convergence passes the integral pairing with a fixed conjugate
Lᑫ test, including the L¹–L∞ endpoint needed for the reaction. -/
theorem tendsto_integral_mul_of_tendsto_eLpNorm {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    {l : Filter ι} {p q : ENNReal} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    {f : ι → α → ℝ} {v w : α → ℝ} (hf : ∀ i, MemLp (f i) p μ) (hv : MemLp v p μ) (hw : MemLp w q μ)
    (hconv : Tendsto (fun i ↦ eLpNorm (f i - v) p μ) l (𝓝 0)) :
    Tendsto (fun i ↦ ∫ x, f i x * w x ∂μ) l (𝓝 (∫ x, v x * w x ∂μ)) := by
  let B := (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ p q
  have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf v hv).mpr hconv
  have hpair := (B.flip (hw.toLp w)).continuous.continuousAt.tendsto.comp ht
  have hident (a : α → ℝ) (ha : MemLp a p μ) :
      B (ha.toLp a) (hw.toLp w) = ∫ x, a x * w x ∂μ := by
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [ha.coeFn_toLp, hw.coeFn_toLp] with x hx hwx
    simp only [ContinuousLinearMap.mul_apply', hx, hwx]
  simpa only [Function.comp_def, ContinuousLinearMap.flip_apply, hident] using hpair

/-- The second-order weak wave identity for Lipschitz energy solutions.
The time test and its derivative both vanish at the final endpoint. There is
no vanishing condition at the initial endpoint, where both Cauchy data appear. -/
theorem second_order_weak_pde {n : ℕ} {f : ℝ → ℝ} {K : NNReal} {hf : LipschitzWith K f}
    {hf0 : f 0 = 0} {x : H¹(ℝ^n) × DerivLp n 2 univ} {u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)}
    (hu : Cauchy.IsEnergySolution hf hf0 x u) {T : ℝ} (hT : 0 ≤ T) (w : H¹(ℝ^n))
    (τ σ : TimeTest 0 T) (hσ : σ.toFun = τ.derivFun) :
    (∫ t in (0 : ℝ)..T, ⟪(energyTriple n).inclusion (u t).1,
      (energyTriple n).inclusion w⟫_ℝ * σ.derivFun t) +
      (∫ t in (0 : ℝ)..T, (gradientForm n (u t).1 w +
        ⟪hf.compLp hf0 ((energyTriple n).inclusion (u t).1),
          (energyTriple n).inclusion w⟫_ℝ) * τ.toFun t) =
      ⟪x.2, (energyTriple n).inclusion w⟫_ℝ * τ.toFun 0 -
        ⟪(energyTriple n).inclusion x.1, (energyTriple n).inclusion w⟫_ℝ * σ.toFun 0 := by
  let J := (energyTriple n).inclusion
  have hvel : Continuous (fun t ↦ ⟪(u t).2, J w⟫_ℝ) := by fun_prop
  have hscalar (t : ℝ) (ht : t ∈ Icc 0 T) : (∫ s in (0 : ℝ)..t, ⟪(u s).2, J w⟫_ℝ) =
        ⟪J (u t).1, J w⟫_ℝ - ⟪J x.1, J w⟫_ℝ := by
    have heq := congrArg (innerSL ℝ (J w)) (hu.displacement t ht.1)
    rw [← (innerSL ℝ (J w)).intervalIntegral_comp_comm
      (u.continuous.snd.intervalIntegrable (μ := volume) 0 t)] at heq
    simpa only [innerSL_apply_apply, inner_sub_right, real_inner_comm (J w)] using heq
  have hid := σ.initial_identity_of_integral_eq hT hvel ⟪J x.1, J w⟫_ℝ hscalar
  have hpde := hu.weak_pde hT w τ
  simp only [← gradientForm_apply] at hpde
  rw [hσ] at hid ⊢
  dsimp only [J] at hid
  linarith

/-- Uniform weak displacement convergence and L¹ convergence of the
reaction pairing pass the second-order wave equation to the limit. The
reaction is tested in L¹–L∞, whereas the two linear terms use L²–L². Both
initial data survive, without an assumed velocity trace for the limit. -/
theorem second_order_weak_pde_of_tendsto {n : ℕ} {g : ℕ → ℝ → ℝ} {K : ℕ → NNReal}
    {hg : ∀ i, LipschitzWith (K i) (g i)} {hg0 : ∀ i, g i 0 = 0} {x : H¹(ℝ^n) × DerivLp n 2 univ}
    {u : ℕ → C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)}
    (hu : ∀ i, Cauchy.IsEnergySolution (hg i) (hg0 i) x (u i)) {T : ℝ} (hT : 0 ≤ T)
    {q : ℝ → H¹(ℝ^n)}
    (hweak : ∀ ell : StrongDual ℝ H¹(ℝ^n), TendstoUniformlyOn (fun i t ↦ ell (u i t).1)
      (fun t ↦ ell (q t)) atTop (Icc 0 T))
    (w : H¹(ℝ^n)) {R : ℝ → ℝ} (hR : Integrable R (volume.restrict (Ioc 0 T)))
    (hreact : Tendsto (fun i ↦ eLpNorm ((fun t ↦ ⟪(hg i).compLp (hg0 i)
      ((energyTriple n).inclusion (u i t).1), (energyTriple n).inclusion w⟫_ℝ) - R) 1
      (volume.restrict (Ioc 0 T))) atTop (𝓝 0))
    (τ σ : TimeTest 0 T) (hσ : σ.toFun = τ.derivFun) :
    (∫ t in (0 : ℝ)..T, ⟪(energyTriple n).inclusion (q t),
      (energyTriple n).inclusion w⟫_ℝ * σ.derivFun t) +
      (∫ t in (0 : ℝ)..T, gradientForm n (q t) w * τ.toFun t) +
      (∫ t in (0 : ℝ)..T, R t * τ.toFun t) =
      ⟪x.2, (energyTriple n).inclusion w⟫_ℝ * τ.toFun 0 -
        ⟪(energyTriple n).inclusion x.1, (energyTriple n).inclusion w⟫_ℝ * σ.toFun 0 := by
  let J := (energyTriple n).inclusion
  have hlin (ell : StrongDual ℝ H¹(ℝ^n)) (a : ℝ → ℝ) (ha : MemLp a 2 (volume.restrict (Ioc 0 T))) :
      Tendsto (fun i ↦ ∫ t in (0 : ℝ)..T, ell (u i t).1 * a t) atTop
        (𝓝 (∫ t in (0 : ℝ)..T, ell (q t) * a t)) := by
    have hc (i : ℕ) : ContinuousOn (fun t ↦ ell (u i t).1) (Icc 0 T) :=
      (ell.continuous.comp (u i).continuous.fst).continuousOn
    have hm (i : ℕ) : MemLp (fun t ↦ ell (u i t).1) 2 (volume.restrict (Ioc 0 T)) :=
      (hc i).memLp_of_subset_isCompact isCompact_Icc measurableSet_Ioc Ioc_subset_Icc_self
    have hqm : MemLp (fun t ↦ ell (q t)) 2 (volume.restrict (Ioc 0 T)) :=
      ((hweak ell).continuousOn (Eventually.of_forall hc).frequently).memLp_of_subset_isCompact
        isCompact_Icc measurableSet_Ioc Ioc_subset_Icc_self
    simp only [intervalIntegral.integral_of_le hT]
    apply tendsto_integral_mul_of_tendsto_eLpNorm hm hqm ha
    exact tendsto_eLpNorm_sub_of_tendstoUniformlyOn_ae measurableSet_Icc
      ((ae_restrict_mem measurableSet_Ioc).mono fun _ ht ↦ Ioc_subset_Icc_self ht)
      (by norm_num : (2 : ENNReal) ≠ ∞)
      (Eventually.of_forall fun i ↦ ((hm i).sub hqm).aestronglyMeasurable) (hweak ell)
  have hbase := hlin ((innerSL ℝ (J w)).comp J) σ.derivFun σ.derivMemLp
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply] at hbase
  simp_rw [← real_inner_comm (J w)] at hbase
  have hgrad := hlin ((gradientForm n).flip w) τ.toFun τ.memLp
  have hτc : ContinuousOn τ.toFun (Icc 0 T) :=
    fun t ht ↦ (τ.hasDerivAt t ht).continuousAt.continuousWithinAt
  have hτm : MemLp τ.toFun ∞ (volume.restrict (Ioc 0 T)) :=
    hτc.memLp_of_subset_isCompact isCompact_Icc measurableSet_Ioc Ioc_subset_Icc_self
  have hrc (i : ℕ) : Continuous (fun t ↦ ⟪(hg i).compLp (hg0 i) (J (u i t).1), J w⟫_ℝ) :=
    (((hg i).continuous_compLp (hg0 i)).comp
      (J.continuous.comp (u i).continuous.fst)).inner continuous_const
  have hrm (i : ℕ) : MemLp (fun t ↦ ⟪(hg i).compLp (hg0 i) (J (u i t).1), J w⟫_ℝ) 1
      (volume.restrict (Ioc 0 T)) := (hrc i).continuousOn.memLp_of_subset_isCompact isCompact_Icc
      measurableSet_Ioc Ioc_subset_Icc_self
  have hr := tendsto_integral_mul_of_tendsto_eLpNorm hrm
    (memLp_one_iff_integrable.mpr hR) hτm hreact
  simp only [← intervalIntegral.integral_of_le hT] at hr
  have hlim := (hbase.add hgrad).add hr
  simp only [ContinuousLinearMap.flip_apply] at hlim
  dsimp only [J] at hlim
  apply tendsto_nhds_unique hlim
  have hid (i : ℕ) := second_order_weak_pde (hu i) hT w τ σ hσ
  have hsplit (i : ℕ) : (∫ t in (0 : ℝ)..T, (gradientForm n (u i t).1 w +
        ⟪(hg i).compLp (hg0 i) (J (u i t).1), J w⟫_ℝ) * τ.toFun t) =
      (∫ t in (0 : ℝ)..T, gradientForm n (u i t).1 w * τ.toFun t) +
      (∫ t in (0 : ℝ)..T, ⟪(hg i).compLp (hg0 i) (J (u i t).1), J w⟫_ℝ * τ.toFun t) := by
    simp only [add_mul, intervalIntegral.integral_of_le hT]
    apply integral_add
    · have hc : Continuous (fun t ↦ gradientForm n (u i t).1 w) := by fun_prop
      have hm : MemLp (fun t ↦ gradientForm n (u i t).1 w) 2 (volume.restrict (Ioc 0 T)) :=
        hc.continuousOn.memLp_of_subset_isCompact isCompact_Icc
          measurableSet_Ioc Ioc_subset_Icc_self
      exact hm.integrable_mul τ.memLp
    · exact (hrm i).integrable_mul hτm
  have heq (i : ℕ) := by
    have hi := hid i
    rw [hsplit i] at hi
    simpa only [← add_assoc] using hi
  convert (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦
    ⟪x.2, J w⟫_ℝ * τ.toFun 0 - ⟪J x.1, J w⟫_ℝ * σ.toFun 0) atTop (𝓝 _)) using 1
  funext i
  exact heq i

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition
