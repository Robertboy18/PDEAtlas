/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.Regularity.H2Persistence
public import PDE.Analysis.Evolution.LionsMagenes.Basic.WeakDerivative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# Strong integrated time equations at H² regularity

The bounded higher lifts satisfy the time equations in H¹ and L² themselves.
Injectivity of the Gelfand embeddings identifies their Bochner
integrals. Thus the energy trajectory is absolutely continuous, and the
higher velocity and acceleration are its derivatives almost everywhere.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Sobolev SobolevSpace.WholeSpaceHilbert

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet

open SobolevSpace SobolevSpace.GraphSpace PDE.Analysis.Evolution

variable {n : ℕ} {f : (ℝ^n × ℝ × ℝ) → ℝ} {L : NNReal}
variable {hf : LipschitzWith L f} {hf0 : f 0 = 0}
variable {x : H¹(ℝ^n) × DerivLp n 2 univ}
variable {u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)}

/-- An H¹ lift of velocity integrates to displacement in H¹. -/
theorem IsEnergySolution.integral_velocity_lift (h : IsEnergySolution hf hf0 x u) {T : ℝ}
    {V : ℝ → H¹(ℝ^n)} (hV : MemLp V ∞ (volume.restrict (Icc 0 T)))
    (hrep : ∀ t ∈ Icc (0 : ℝ) T, (energyTriple n).inclusion (V t) = (u t).2) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    (∫ s in (0 : ℝ)..t, V s) = (u t).1 - x.1 := by
  have hVi : IntervalIntegrable V volume 0 t := by
    apply IntegrableOn.intervalIntegrable
    rw [uIcc_of_le ht.1]
    exact IntegrableOn.mono_set (show IntegrableOn V (Icc 0 T) volume from
      hV.integrable le_top) (Icc_subset_Icc le_rfl ht.2)
  apply (energyTriple n).injective
  rw [map_sub, ← (energyTriple n).inclusion.intervalIntegral_comp_comm hVi, ← h.displacement t ht.1]
  refine intervalIntegral.integral_congr fun s hs ↦ ?_
  rw [uIcc_of_le ht.1] at hs
  exact hrep s ⟨hs.1, hs.2.trans ht.2⟩

/-- The L² acceleration lift integrates to velocity in L². -/
theorem IsEnergySolution.integral_acceleration_lift (h : IsEnergySolution hf hf0 x u) {T : ℝ}
    {A : ℝ → DerivLp n 2 univ} (hA : MemLp A ∞ (volume.restrict (Icc 0 T)))
    (hrep : ∀ t ∈ Icc (0 : ℝ) T, (energyTriple n).pivotToDual (A t) = acceleration hf hf0 (u t))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    (∫ s in (0 : ℝ)..t, A s) = (u t).2 - x.2 := by
  have hAi : IntervalIntegrable A volume 0 t := by
    apply IntegrableOn.intervalIntegrable
    rw [uIcc_of_le ht.1]
    exact IntegrableOn.mono_set (show IntegrableOn A (Icc 0 T) volume from
      hA.integrable le_top) (Icc_subset_Icc le_rfl ht.2)
  apply (energyTriple n).pivotToDual_injective
  rw [map_sub, ← (energyTriple n).pivotToDual.intervalIntegral_comp_comm hAi, ← h.velocity t ht.1]
  refine intervalIntegral.integral_congr fun s hs ↦ ?_
  rw [uIcc_of_le ht.1] at hs
  exact hrep s ⟨hs.1, hs.2.trans ht.2⟩

/-- Bounded velocity and acceleration lifts give an absolutely continuous
energy trajectory and identify its strong derivative almost everywhere. -/
theorem IsEnergySolution.absolutelyContinuous_of_lifts (h : IsEnergySolution hf hf0 x u) {T : ℝ}
    (hT : 0 ≤ T) {V : ℝ → H¹(ℝ^n)} {A : ℝ → DerivLp n 2 univ}
    (hV : MemLp V ∞ (volume.restrict (Icc 0 T))) (hA : MemLp A ∞ (volume.restrict (Icc 0 T)))
    (hrepV : ∀ t ∈ Icc (0 : ℝ) T, (energyTriple n).inclusion (V t) = (u t).2)
    (hrepA : ∀ t ∈ Icc (0 : ℝ) T, (energyTriple n).pivotToDual (A t) = acceleration hf hf0 (u t)) :
    AbsolutelyContinuousOnInterval u 0 T ∧
      ∀ᵐ t ∂volume.restrict (Ioo 0 T), HasDerivAt u (V t, A t) t := by
  let d : ℝ → H¹(ℝ^n) × DerivLp n 2 univ := fun t ↦ (V t, A t)
  have hVi : IntervalIntegrable V volume 0 T := by
    apply IntegrableOn.intervalIntegrable
    simpa only [uIcc_of_le hT, IntegrableOn] using hV.integrable le_top
  have hAi : IntervalIntegrable A volume 0 T := by
    apply IntegrableOn.intervalIntegrable
    simpa only [uIcc_of_le hT, IntegrableOn] using hA.integrable le_top
  have hdi : IntervalIntegrable d volume 0 T :=
    ⟨hVi.1.integrable.prodMk hAi.1.integrable, hVi.2.integrable.prodMk hAi.2.integrable⟩
  have heq : ∀ t ∈ Icc (0 : ℝ) T, u t = x + ∫ s in (0 : ℝ)..t, d s := by
    intro t ht
    have hds : IntervalIntegrable d volume 0 t := hdi.mono_set (by
      simpa only [uIcc_of_le ht.1, uIcc_of_le hT] using Icc_subset_Icc le_rfl ht.2)
    apply Prod.ext
    · have hi := ContinuousLinearMap.intervalIntegral_comp_comm
        (ContinuousLinearMap.fst ℝ H¹(ℝ^n) (DerivLp n 2 univ)) hds
      change (∫ s in (0 : ℝ)..t, V s) = (∫ s in (0 : ℝ)..t, d s).1 at hi
      change (u t).1 = x.1 + (∫ s in (0 : ℝ)..t, d s).1
      rw [← hi, h.integral_velocity_lift hV hrepV ht]
      abel
    · have hi := ContinuousLinearMap.intervalIntegral_comp_comm
        (ContinuousLinearMap.snd ℝ H¹(ℝ^n) (DerivLp n 2 univ)) hds
      change (∫ s in (0 : ℝ)..t, A s) = (∫ s in (0 : ℝ)..t, d s).2 at hi
      change (u t).2 = x.2 + (∫ s in (0 : ℝ)..t, d s).2
      rw [← hi, h.integral_acceleration_lift hA hrepA ht]
      abel
  constructor
  · refine absolutelyContinuousOnInterval_of_eq_add_integral hdi fun t ht ↦ ?_
    rw [h.initial]
    exact heq t (by simpa only [uIcc_of_le hT, IntegrableOn] using ht)
  · have hp := IntervalIntegrable.ae_hasDerivAt_integral hdi
    filter_upwards [hp.filter_mono (ae_mono Measure.restrict_le_self),
      ae_restrict_mem measurableSet_Ioo] with t hd ht
    have hprim := (hd (by simpa only [uIcc_of_le hT, IntegrableOn] using (Ioo_subset_Icc_self ht))
      0 left_mem_uIcc).const_add x
    apply hprim.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs using heq s (Ioo_subset_Icc_self hs)

end PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet
