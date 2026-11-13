/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Linearity of continuous representatives

For a measure positive on nonempty open sets, continuous representatives inherit
almost-everywhere addition and scalar multiplication laws. The representative family
is arbitrary.
-/

@[expose] public section

namespace MeasureTheory

variable {X E F : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [TopologicalSpace F] [T2Space F] {μ : Measure X} [μ.IsOpenPosMeasure]

/-- Continuous representatives inherit an almost-everywhere addition law. -/
theorem map_add_of_continuous_ae_eq [Add E] [Add F] [ContinuousAdd F]
    {f g : E → X → F} (hf : ∀ u, Continuous (f u))
    (hfg : ∀ u, f u =ᵐ[μ] g u) {u v : E}
    (hadd : g (u + v) =ᵐ[μ] (fun x ↦ g u x + g v x)) :
    f (u + v) = (fun x ↦ f u x + f v x) := by
  apply (Continuous.ae_eq_iff_eq μ (hf _) ((hf u).add (hf v))).mp
  exact (hfg _).trans (hadd.trans ((hfg u).add (hfg v)).symm)

/-- Continuous representatives inherit an almost-everywhere scalar multiplication law. -/
theorem map_smul_of_continuous_ae_eq {𝕜 : Type*} [SMul 𝕜 E] [SMul 𝕜 F]
    [ContinuousConstSMul 𝕜 F] {f g : E → X → F}
    (hf : ∀ u, Continuous (f u)) (hfg : ∀ u, f u =ᵐ[μ] g u) {c : 𝕜} {u : E}
    (hsmul : g (c • u) =ᵐ[μ] (fun x ↦ c • g u x)) : f (c • u) = (fun x ↦ c • f u x) := by
  apply (Continuous.ae_eq_iff_eq μ (hf _) ((hf u).const_smul c)).mp
  exact (hfg _).trans (hsmul.trans ((hfg u).fun_comp (c • ·)).symm)

end MeasureTheory
