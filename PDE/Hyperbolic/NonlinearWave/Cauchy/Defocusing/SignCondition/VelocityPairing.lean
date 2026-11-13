/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition.WeakEquation
import PDE.Analysis.MeasureTheory.Lp.Continuous

/-!
# Integrated velocity pairings

Strong L¹ convergence gives uniform convergence of indefinite integrals. For
energy waves, this passes the fixed spatial velocity pairing to the integral
of the limiting gradient and reaction. The value at zero remains the original velocity datum.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set SobolevSpace SobolevSpace.GraphSpace
open PDE.Analysis.Evolution
open scoped ENNReal Topology InnerProductSpace Sobolev SobolevSpace.WholeSpaceHilbert

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition

/-- Strong L¹ convergence on an interval gives uniform convergence of its
indefinite Bochner integrals. -/
theorem tendstoUniformlyOn_integral_of_tendsto_L1 {E ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a b : ℝ} {l : Filter ι} {F : ι → ℝ → E} {G : ℝ → E}
    (hF : ∀ i, Integrable (F i) (volume.restrict (Ioc a b)))
    (hG : Integrable G (volume.restrict (Ioc a b)))
    (hconv : Tendsto (fun i ↦ eLpNorm (F i - G) 1 (volume.restrict (Ioc a b))) l (𝓝 0)) :
    TendstoUniformlyOn (fun i t ↦ ∫ r in a..t, F i r) (fun t ↦ ∫ r in a..t, G r) l (Icc a b) := by
  rw [EMetric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hconv.eventually (eventually_lt_nhds hε)] with i hi
  intro t ht
  have hsub : Ioc a t ⊆ Ioc a b := Ioc_subset_Ioc le_rfl ht.2
  have hFi : IntervalIntegrable (F i) volume a t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).mpr
      ((hF i).mono_measure (Measure.restrict_mono_set volume hsub))
  have hGi : IntervalIntegrable G volume a t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).mpr
      (hG.mono_measure (Measure.restrict_mono_set volume hsub))
  rw [edist_comm, edist_eq_enorm_sub, ← intervalIntegral.integral_sub hFi hGi,
    intervalIntegral.integral_of_le ht.1]
  calc
    _ ≤ ∫⁻ r in Ioc a t, ‖(F i - G) r‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ r in Ioc a b, ‖(F i - G) r‖ₑ := lintegral_mono_set hsub
    _ = eLpNorm (F i - G) 1 (volume.restrict (Ioc a b)) :=
      (eLpNorm_one_eq_lintegral_enorm ((hF i).sub hG).aestronglyMeasurable).symm
    _ < ε := hi

/-- The Cauchy velocity equation evaluated against a fixed H¹ test,
with the gradient and reaction integrals separated. -/
theorem velocity_pairing_eq_integrals {n : ℕ} {f : ℝ → ℝ} {K : NNReal} {hf : LipschitzWith K f}
    {hf0 : f 0 = 0} {x : H¹(ℝ^n) × DerivLp n 2 univ} {u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)}
    (hu : Cauchy.IsEnergySolution hf hf0 x u) (w : H¹(ℝ^n)) {t : ℝ} (ht : 0 ≤ t) :
    ⟪(u t).2, (energyTriple n).inclusion w⟫_ℝ =
      ⟪x.2, (energyTriple n).inclusion w⟫_ℝ -
        (∫ s in (0 : ℝ)..t, gradientForm n (u s).1 w) -
        ∫ s in (0 : ℝ)..t,
          ⟪hf.compLp hf0 ((energyTriple n).inclusion (u s).1),
            (energyTriple n).inclusion w⟫_ℝ := by
  have hacc : Continuous (fun s ↦ Cauchy.acceleration hf hf0 (u s).1) :=
    (Cauchy.continuous_acceleration hf hf0).comp u.continuous.fst
  have heq := congrArg (fun ell : StrongDual ℝ H¹(ℝ^n) ↦ ell w) (hu.velocity t ht)
  change (∫ s in (0 : ℝ)..t, Cauchy.acceleration hf hf0 (u s).1) w =
    ((energyTriple n).pivotToDual (u t).2 - (energyTriple n).pivotToDual x.2) w at heq
  rw [ContinuousLinearMap.intervalIntegral_apply (hacc.intervalIntegrable (μ := volume) 0 t)] at heq
  simp only [sub_apply, GelfandTriple.pivotToDual_apply, Cauchy.acceleration_apply,
    ← gradientForm_apply, intervalIntegral.integral_neg] at heq
  have hg : Continuous (fun s ↦ gradientForm n (u s).1 w) := by fun_prop
  have hr : Continuous (fun s ↦ ⟪hf.compLp hf0 ((energyTriple n).inclusion (u s).1),
        (energyTriple n).inclusion w⟫_ℝ) := ((hf.continuous_compLp hf0).comp
      ((energyTriple n).inclusion.continuous.comp u.continuous.fst)).inner continuous_const
  rw [intervalIntegral.integral_add (hg.intervalIntegrable 0 t) (hr.intervalIntegrable 0 t)] at heq
  linarith

/-- Convergence of the displacement and local reaction pairings determines
uniformly the tested velocity on each finite interval, including its initial
value. The conclusion requires no preselected limiting velocity. -/
theorem tendstoUniformlyOn_velocity_pairing {n : ℕ} {g : ℕ → ℝ → ℝ} {K : ℕ → NNReal}
    {hg : ∀ i, LipschitzWith (K i) (g i)} {hg0 : ∀ i, g i 0 = 0} {x : H¹(ℝ^n) × DerivLp n 2 univ}
    {u : ℕ → C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)}
    (hu : ∀ i, Cauchy.IsEnergySolution (hg i) (hg0 i) x (u i)) {T : ℝ} {q : ℝ → H¹(ℝ^n)}
    (hweak : ∀ ell : StrongDual ℝ H¹(ℝ^n),
      TendstoUniformlyOn (fun i t ↦ ell (u i t).1) (fun t ↦ ell (q t)) atTop (Icc 0 T))
    (w : H¹(ℝ^n)) {R : ℝ → ℝ} (hR : Integrable R (volume.restrict (Ioc 0 T)))
    (hreact : Tendsto (fun i ↦ eLpNorm ((fun t ↦ ⟪(hg i).compLp (hg0 i)
      ((energyTriple n).inclusion (u i t).1), (energyTriple n).inclusion w⟫_ℝ) - R) 1
      (volume.restrict (Ioc 0 T))) atTop (𝓝 0)) :
    TendstoUniformlyOn (fun i t ↦ ⟪(u i t).2, (energyTriple n).inclusion w⟫_ℝ)
      (fun t ↦ ⟪x.2, (energyTriple n).inclusion w⟫_ℝ - (∫ s in (0 : ℝ)..t, gradientForm n (q s) w) -
      ∫ s in (0 : ℝ)..t, R s) atTop (Icc 0 T) := by
  have hgrad := hweak ((gradientForm n).flip w)
  simp only [ContinuousLinearMap.flip_apply] at hgrad
  have hc (i : ℕ) : ContinuousOn (fun t ↦ gradientForm n (u i t).1 w) (Icc 0 T) :=
    (by fun_prop : Continuous (fun t ↦ gradientForm n (u i t).1 w)).continuousOn
  have hm (i : ℕ) : MemLp (fun t ↦ gradientForm n (u i t).1 w) 1 (volume.restrict (Ioc 0 T)) :=
    (hc i).memLp_of_subset_isCompact isCompact_Icc measurableSet_Ioc Ioc_subset_Icc_self
  have hqm : MemLp (fun t ↦ gradientForm n (q t) w) 1 (volume.restrict (Ioc 0 T)) :=
    (hgrad.continuousOn (Eventually.of_forall hc).frequently).memLp_of_subset_isCompact
      isCompact_Icc measurableSet_Ioc Ioc_subset_Icc_self
  have hgconv := tendsto_eLpNorm_sub_of_tendstoUniformlyOn_ae measurableSet_Icc
    ((ae_restrict_mem measurableSet_Ioc).mono fun _ ht ↦ Ioc_subset_Icc_self ht)
    (by norm_num : (1 : ENNReal) ≠ ∞)
    (Eventually.of_forall fun i ↦ ((hm i).sub hqm).aestronglyMeasurable) hgrad
  have hgint := tendstoUniformlyOn_integral_of_tendsto_L1
    (fun i ↦ memLp_one_iff_integrable.mp (hm i)) (memLp_one_iff_integrable.mp hqm) hgconv
  have hrc (i : ℕ) : Continuous (fun t ↦
      ⟪(hg i).compLp (hg0 i) ((energyTriple n).inclusion (u i t).1),
        (energyTriple n).inclusion w⟫_ℝ) := (((hg i).continuous_compLp (hg0 i)).comp
      ((energyTriple n).inclusion.continuous.comp (u i).continuous.fst)).inner continuous_const
  have hri (i : ℕ) : Integrable (fun t ↦
      ⟪(hg i).compLp (hg0 i) ((energyTriple n).inclusion (u i t).1),
        (energyTriple n).inclusion w⟫_ℝ) (volume.restrict (Ioc 0 T)) :=
    (memLp_one_iff_integrable.mp ((hrc i).continuousOn.memLp_of_subset_isCompact
      isCompact_Icc measurableSet_Ioc Ioc_subset_Icc_self))
  have hrint := tendstoUniformlyOn_integral_of_tendsto_L1 hri hR hreact
  have hconst : TendstoUniformlyOn (fun (_ : ℕ) (_ : ℝ) ↦ ⟪x.2, (energyTriple n).inclusion w⟫_ℝ)
      (fun _ ↦ ⟪x.2, (energyTriple n).inclusion w⟫_ℝ) atTop (Icc 0 T) :=
    tendsto_const_nhds.tendstoUniformlyOn_const (Icc 0 T)
  apply ((hconst.sub hgint).sub hrint).congr
  filter_upwards with i
  exact fun t ht ↦ (velocity_pairing_eq_integrals (hu i) w ht.1).symm

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition
