/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition.WeakEquation
import PDE.Spaces.Sobolev.Calculus.Slicing.FirstOrder

/-!
# Spatial reaction pairings from local spacetime convergence

Integration in the spatial variable contracts the L¹ seminorm. Multiplication
by a bounded spatial test therefore turns local spacetime L¹ convergence into
L¹ convergence of the time-dependent reaction pairing. Almost-everywhere sections suffice.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set SobolevSpace SobolevSpace.GraphSpace
open PDE.Analysis.Evolution
open scoped ENNReal Topology InnerProductSpace Sobolev SobolevSpace.WholeSpaceHilbert

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition

/-- Strong product L¹ convergence passes to the spatial integrals in time L¹. -/
theorem tendsto_L1_integral_sections {α β E ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure α} {ν : Measure β} [SFinite ν]
    {l : Filter ι} {F : ι → α × β → E} {G : α × β → E} (hF : ∀ i, Integrable (F i) (μ.prod ν))
    (hG : Integrable G (μ.prod ν))
    (hconv : Tendsto (fun i ↦ eLpNorm (F i - G) 1 (μ.prod ν)) l (𝓝 0)) :
    Tendsto (fun i ↦ eLpNorm (fun t ↦ (∫ x, F i (t, x) ∂ν) - ∫ x, G (t, x) ∂ν) 1 μ) l (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconv
    (fun _ ↦ bot_le) fun i ↦ ?_
  calc
    _ = eLpNorm (fun t ↦ ∫ x, (F i - G) (t, x) ∂ν) 1 μ := by
      apply eLpNorm_congr_ae
      filter_upwards [((integrable_prod_iff (hF i).aestronglyMeasurable).mp (hF i)).1,
        ((integrable_prod_iff hG.aestronglyMeasurable).mp hG).1] with t htF htG
      exact (integral_sub htF htG).symm
    _ ≤ _ := SobolevSpace.Slices.eLpNorm_one_integral_prod_right_le ((hF i).sub hG)

/-- A bounded spatial multiplier preserves product L¹ convergence, and the
resulting spatial pairings converge in time L¹. -/
theorem tendsto_L1_weighted_integral_sections {α β ι : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {ν : Measure β} [SFinite ν] {l : Filter ι}
    {F : ι → α × β → ℝ} {G : α × β → ℝ} {w : β → ℝ} {C : NNReal}
    (hF : ∀ i, Integrable (F i) (μ.prod ν)) (hG : Integrable G (μ.prod ν))
    (hw : StronglyMeasurable w) (hbound : ∀ x, ‖w x‖ ≤ C)
    (hconv : Tendsto (fun i ↦ eLpNorm (F i - G) 1 (μ.prod ν)) l (𝓝 0)) :
    Integrable (fun t ↦ ∫ x, G (t, x) * w x ∂ν) μ ∧
      Tendsto (fun i ↦ eLpNorm (fun t ↦ (∫ x, F i (t, x) * w x ∂ν) - ∫ x, G (t, x) * w x ∂ν) 1 μ) l
        (𝓝 0) := by
  have hwm : AEStronglyMeasurable (fun z : α × β ↦ w z.2) (μ.prod ν) :=
    (hw.comp_measurable measurable_snd).aestronglyMeasurable
  have hb : ∀ᵐ z : α × β ∂μ.prod ν, ‖w z.2‖ ≤ C := Eventually.of_forall fun z ↦ hbound z.2
  have hFw (i : ι) := (hF i).mul_bdd hwm hb
  have hGw := hG.mul_bdd hwm hb
  refine ⟨hGw.integral_prod_left, ?_⟩
  apply tendsto_L1_integral_sections
    (F := fun i z ↦ F i z * w z.2) (G := fun z ↦ G z * w z.2) hFw hGw
  have hbound' (i : ι) : eLpNorm ((fun z ↦ F i z * w z.2) - fun z ↦ G z * w z.2) 1 (μ.prod ν) ≤
      C • eLpNorm (F i - G) 1 (μ.prod ν) := by
    apply eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul ((hFw i).sub hGw).aestronglyMeasurable _ 1
    filter_upwards with z
    simp only [Pi.sub_apply, ← sub_mul, nnnorm_mul]
    have hc : ‖w z.2‖₊ ≤ C := by exact_mod_cast hbound z.2
    exact (mul_le_mul_right hc _).trans_eq (mul_comm _ _)
  have ht : Tendsto (fun i ↦ C • eLpNorm (F i - G) 1 (μ.prod ν)) l (𝓝 0) := by
    change Tendsto (fun i ↦ (C : ENNReal) * eLpNorm (F i - G) 1 (μ.prod ν)) l (𝓝 0)
    simpa only [mul_zero] using
      ENNReal.Tendsto.const_mul (a := (C : ENNReal)) hconv (Or.inr ENNReal.coe_ne_top)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ ↦ bot_le) hbound'

/-- Local spacetime L¹ convergence of reactions gives L¹ convergence of their
L² pairings with a bounded spatial test supported in a finite-measure
set. The limiting reaction need only be integrable on that cylinder. -/
theorem tendsto_L1_reaction_pairing_of_joint_convergence {α β ι : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} [IsFiniteMeasure μ] {ν : Measure β} [SFinite ν]
    {l : Filter ι} {s : Set β} [IsFiniteMeasure (ν.restrict s)] {g : ι → ℝ → ℝ} {K : ι → NNReal}
    (hg : ∀ i, LipschitzWith (K i) (g i)) (hg0 : ∀ i, g i 0 = 0) {u : ι → α → Lp ℝ 2 ν}
    {U : ι → α × β → ℝ} {G : α × β → ℝ} (hU : ∀ i, MemLp (U i) 2 (μ.prod ν))
    (hUsec : ∀ i, ∀ᵐ t ∂μ, (fun y ↦ U i (t, y)) =ᵐ[ν] (u i t : β → ℝ))
    (hG : Integrable G (μ.prod (ν.restrict s)))
    (hconv : Tendsto (fun i ↦ eLpNorm (fun z ↦ g i (U i z) - G z) 1 (μ.prod (ν.restrict s))) l
      (𝓝 0))
    (w : Lp ℝ 2 ν) {ψ : β → ℝ} {C : NNReal} (hψ : StronglyMeasurable ψ) (hb : ∀ y, ‖ψ y‖ ≤ C)
    (hsupp : ∀ y, y ∉ s → ψ y = 0) (hw : (w : β → ℝ) =ᵐ[ν] ψ) :
    Integrable (fun t ↦ ∫ y, G (t, y) * ψ y ∂ν) μ ∧
      Tendsto (fun i ↦ eLpNorm (fun t ↦ ⟪(hg i).compLp (hg0 i) (u i t), w⟫_ℝ - ∫ y,
        G (t, y) * ψ y ∂ν) 1 μ) l (𝓝 0) := by
  have hFi (i : ι) : Integrable (fun z ↦ g i (U i z)) (μ.prod (ν.restrict s)) :=
    ((hg i).comp_memLp (hg0 i) ((hU i).mono_measure
      (Measure.prod_mono le_rfl Measure.restrict_le_self))).integrable (by norm_num)
  obtain ⟨hint, ht⟩ := tendsto_L1_weighted_integral_sections hFi hG hψ hb hconv
  have hrestrict (A : β → ℝ) : (∫ y in s, A y * ψ y ∂ν) = ∫ y, A y * ψ y ∂ν :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ by rw [hsupp y hy, mul_zero]
  simp only [hrestrict] at hint ht
  refine ⟨hint, ht.congr' ?_⟩
  filter_upwards with i
  apply eLpNorm_congr_ae
  filter_upwards [hUsec i] with t hsection
  congr 1
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hsection, hw, (hg i).coeFn_compLp (hg0 i) (u i t)] with y hy hwy hgy
  simp only [Real.inner_apply, Function.comp_apply, hy, hwy, hgy]

/-- The second-order weak equation passes from energy waves to the
original local reaction. Compact spatial support replaces any global growth
or L² condition on that reaction. Both initial data appear explicitly. -/
theorem second_order_weak_pde_of_joint_convergence {n : ℕ} {f : ℝ → ℝ} {g : ℕ → ℝ → ℝ}
    {K : ℕ → NNReal} {hg : ∀ i, LipschitzWith (K i) (g i)} {hg0 : ∀ i, g i 0 = 0}
    {x : H¹(ℝ^n) × DerivLp n 2 univ} {u : ℕ → C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)}
    (hu : ∀ i, Cauchy.IsEnergySolution (hg i) (hg0 i) x (u i)) {T : ℝ} (hT : 0 ≤ T)
    {q : ℝ → H¹(ℝ^n)}
    (hweak : ∀ ell : StrongDual ℝ H¹(ℝ^n), TendstoUniformlyOn (fun i t ↦ ell (u i t).1)
      (fun t ↦ ell (q t)) atTop (Icc 0 T))
    {s : Set (ℝ^n)} [IsFiniteMeasure ((domainMeasure n univ).restrict s)] {U : ℕ → ℝ × (ℝ^n) → ℝ}
    {V : ℝ × (ℝ^n) → ℝ}
    (hU : ∀ i, MemLp (U i) 2 ((volume.restrict (Ioc 0 T)).prod (domainMeasure n univ)))
    (hUsec : ∀ i, ∀ᵐ t ∂volume.restrict (Ioc 0 T), (fun y ↦ U i (t, y)) =ᵐ[domainMeasure n univ]
      (energyTriple n).inclusion (u i t).1)
    (hF : Integrable (fun z ↦ f (V z)) ((volume.restrict (Ioc 0 T)).prod
      ((domainMeasure n univ).restrict s)))
    (hconv : Tendsto (fun i ↦ eLpNorm (fun z ↦ g i (U i z) - f (V z)) 1
      ((volume.restrict (Ioc 0 T)).prod ((domainMeasure n univ).restrict s))) atTop (𝓝 0))
    (w : H¹(ℝ^n)) {ψ : (ℝ^n) → ℝ} {C : NNReal} (hψ : StronglyMeasurable ψ) (hb : ∀ y, ‖ψ y‖ ≤ C)
    (hsupp : ∀ y, y ∉ s → ψ y = 0)
    (hw : ((energyTriple n).inclusion w : (ℝ^n) → ℝ) =ᵐ[domainMeasure n univ] ψ)
    (τ σ : TimeTest 0 T) (hσ : σ.toFun = τ.derivFun) :
    (∫ t in (0 : ℝ)..T, ⟪(energyTriple n).inclusion (q t),
      (energyTriple n).inclusion w⟫_ℝ * σ.derivFun t) +
      (∫ t in (0 : ℝ)..T, gradientForm n (q t) w * τ.toFun t) +
      (∫ t in (0 : ℝ)..T, (∫ y, f (V (t, y)) * ψ y ∂domainMeasure n univ) * τ.toFun t) =
      ⟪x.2, (energyTriple n).inclusion w⟫_ℝ * τ.toFun 0 -
        ⟪(energyTriple n).inclusion x.1, (energyTriple n).inclusion w⟫_ℝ * σ.toFun 0 := by
  obtain ⟨hR, hreact⟩ := tendsto_L1_reaction_pairing_of_joint_convergence
    hg hg0 hU hUsec hF hconv ((energyTriple n).inclusion w) hψ hb hsupp hw
  exact second_order_weak_pde_of_tendsto hu hT hweak w hR hreact τ σ hσ

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition
