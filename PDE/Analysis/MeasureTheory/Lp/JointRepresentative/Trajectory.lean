/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module
public import PDE.Analysis.MeasureTheory.Lp.JointRepresentative.LocalIntegrability

/-!
# Joint representatives of integrable and continuous Lebesgue trajectories

Integrable Lp families have integrable jointly measurable representatives
against finite spatial submeasures. Applying this to compact parameter sets
derives local spacetime integrability for continuous Lp trajectories, including
infinite spatial exponent. Representatives are transported explicitly through
almost-everywhere equality.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace MeasureTheory

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] {μ : Measure α} {ν : Measure β}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- On finite parameter measure, an integrable Lp family has integrable joint
representatives against every finite spatial submeasure. -/
theorem Integrable.integrable_jointLpRepresentative [IsFiniteMeasure μ]
    {u : α → Lp E p ν} (hu : Integrable u μ) (ν' : Measure β)
    [IsFiniteMeasure ν'] (hν : ν' ≤ ν) {F : α × β → E} (hF : Measurable F)
    (hsection : ∀ᵐ t ∂μ, (fun x ↦ F (t, x)) =ᵐ[ν] (u t : β → E)) :
    Integrable F (μ.prod ν') := by
  let U : Lp (Lp E p ν) 1 μ := (memLp_one_iff_integrable.mpr hu).toLp u
  have hi := Lp.integrable_jointRepresentative_of_finite_submeasures U μ ν' le_rfl hν
  apply hi.congr
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
    (Lp.measurable_jointRepresentative U) hF)).mpr
  filter_upwards [(memLp_one_iff_integrable.mpr hu).coeFn_toLp, hsection] with t ht hs
  have he : U t = u t := ht
  filter_upwards [((Lp.jointRepresentative_section U t).trans
    (by simpa only [he] using hs.symm)).filter_mono (ae_mono hν)] with x hx
  exact hx

/-- Every measurable representative of a continuous Lp trajectory is locally
integrable in spacetime. Local integrability is derived, not an input premise. -/
theorem _root_.Continuous.locallyIntegrable_jointLpRepresentative
    [TopologicalSpace α] [TopologicalSpace β] [T2Space α]
    [BorelSpace α] [LocallyCompactSpace α] [LocallyCompactSpace β]
    [SecondCountableTopology α] [IsFiniteMeasureOnCompacts μ]
    [IsFiniteMeasureOnCompacts ν] [SFinite ν]
    {u : α → Lp E p ν} (hu : Continuous u) {F : α × β → E} (hF : Measurable F)
    (hsection : ∀ t, (fun x ↦ F (t, x)) =ᵐ[ν] (u t : β → E)) :
    LocallyIntegrable F (μ.prod ν) := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  let A := Prod.fst '' K
  let B := Prod.snd '' K
  have hA : IsCompact A := hK.image continuous_fst
  have hB : IsCompact B := hK.image continuous_snd
  let : IsFiniteMeasure (μ.restrict A) := isFiniteMeasure_restrict.mpr hA.measure_ne_top
  let : IsFiniteMeasure (ν.restrict B) := isFiniteMeasure_restrict.mpr hB.measure_ne_top
  have hi := (hu.continuousOn.integrableOn_compact (μ := μ) hA).integrable_jointLpRepresentative
    (ν.restrict B) Measure.restrict_le_self hF (.of_forall hsection)
  rw [Measure.prod_restrict] at hi
  have hi' : IntegrableOn F (A ×ˢ B) (μ.prod ν) := hi
  exact hi'.mono_set (fun z hz ↦ ⟨⟨z, hz, rfl⟩, ⟨z, hz, rfl⟩⟩)

end MeasureTheory
