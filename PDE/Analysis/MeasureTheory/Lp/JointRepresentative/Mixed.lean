/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.JointRepresentative

/-!
# Joint representatives for general mixed Lᵖ spaces

A strongly measurable map into Lᵖ has a jointly measurable representative agreeing
with every spatial section almost everywhere. Summably accurate simple approximations
construct the representative, including at the infinite exponent; no measurable
selection of representatives on all of Lᵖ is assumed.

For nested Bochner classes the representative recovers the mixed norm exactly.
Addition and scalar multiplication commute with it almost everywhere for product
measure. Only these product-measure transport results need the inner measure s-finite.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace MeasureTheory

/-- A strongly measurable Lp-valued map admits joint measurable representatives at every
parameter. Summably accurate simple approximations give the representative without a
measurable choice of representatives on all of Lp. -/
theorem StronglyMeasurable.exists_jointLpRepresentative {α β E : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [NormedAddCommGroup E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {ν : Measure β} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {u : α → Lp E p ν} (hu : StronglyMeasurable u) :
    ∃ U : α × β → E, Measurable U ∧
      ∀ t, (fun x ↦ U (t, x)) =ᵐ[ν] (u t : β → E) := by
  obtain ⟨U, hU, hsection⟩ := hu.exists_stronglyMeasurable_jointLpRepresentative
  exact ⟨U, stronglyMeasurable_iff_measurable.mp hU, hsection⟩

end MeasureTheory

namespace MeasureTheory.Lp

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [_root_.SecondCountableTopology E] {μ : Measure α} {ν : Measure β}
  {p q : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A jointly measurable representative of a nested Bochner Lp class. -/
noncomputable def jointRepresentative (u : Lp (Lp E p ν) q μ) : α × β → E :=
  (Lp.stronglyMeasurable u).exists_jointLpRepresentative.choose

/-- The chosen representative is measurable for the product sigma algebra. -/
theorem measurable_jointRepresentative (u : Lp (Lp E p ν) q μ) :
    Measurable (Lp.jointRepresentative u) :=
  (Lp.stronglyMeasurable u).exists_jointLpRepresentative.choose_spec.1

/-- Every section agrees almost everywhere with the corresponding canonical Lp value. -/
theorem jointRepresentative_section (u : Lp (Lp E p ν) q μ) (t : α) :
    (fun x ↦ (Lp.jointRepresentative u) (t, x)) =ᵐ[ν] (u t : β → E) :=
  (Lp.stronglyMeasurable u).exists_jointLpRepresentative.choose_spec.2 t

section Norm

variable [Fact (1 ≤ q)]

/-- The section norms recover the original nested norm, including infinite exponents. -/
theorem eLpNorm_jointRepresentative (u : Lp (Lp E p ν) q μ) :
    eLpNorm (fun t ↦ eLpNorm (fun x ↦ (Lp.jointRepresentative u) (t, x)) p ν) q μ = ‖u‖ₑ := by
  have hsection (t : α) : eLpNorm (fun x ↦ (Lp.jointRepresentative u) (t, x)) p ν = ‖u t‖ₑ := by
    rw [Lp.enorm_def]
    exact eLpNorm_congr_ae ((Lp.jointRepresentative_section u) t)
  simp_rw [hsection]
  rw [eLpNorm_enorm _ (Lp.aestronglyMeasurable u), Lp.enorm_def]

/-- The mixed norm of the joint representative is finite. -/
theorem memLp_eLpNorm_jointRepresentative (u : Lp (Lp E p ν) q μ) :
    MemLp (fun t ↦ eLpNorm (fun x ↦ (Lp.jointRepresentative u) (t, x)) p ν) q μ := by
  change eLpNorm _ _ _ < ∞
  rw [eLpNorm_jointRepresentative]
  exact enorm_lt_top

end Norm

/-- Addition of nested classes agrees with addition of their joint representatives
almost everywhere for product measure. -/
theorem jointRepresentative_add [SFinite ν] (u v : Lp (Lp E p ν) q μ) :
    Lp.jointRepresentative (u + v) =ᵐ[μ.prod ν]
      Lp.jointRepresentative u + Lp.jointRepresentative v := by
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_eq_fun (Lp.measurable_jointRepresentative (u + v))
      ((Lp.measurable_jointRepresentative u).add (Lp.measurable_jointRepresentative v)))).mpr
  filter_upwards [Lp.coeFn_add u v] with t ht
  filter_upwards [(Lp.jointRepresentative_section (u + v)) t,
    (Lp.jointRepresentative_section u) t, (Lp.jointRepresentative_section v) t,
    Lp.coeFn_add (u t) (v t)] with x huv hu hv hsum
  simp only [Pi.add_apply] at ht hsum ⊢
  rw [huv, ht, hsum, hu, hv]

/-- Scalar multiplication of nested classes agrees with scalar multiplication of their
joint representatives almost everywhere for product measure. -/
theorem jointRepresentative_smul {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [NormedSpace 𝕜 E] [SFinite ν] (c : 𝕜) (u : Lp (Lp E p ν) q μ) :
    (Lp.jointRepresentative (c • u)) =ᵐ[μ.prod ν] c • (Lp.jointRepresentative u) := by
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_eq_fun (Lp.measurable_jointRepresentative (c • u))
      ((Lp.measurable_jointRepresentative u).const_smul c))).mpr
  filter_upwards [Lp.coeFn_smul c u] with t ht
  filter_upwards [(Lp.jointRepresentative_section (c • u)) t,
    (Lp.jointRepresentative_section u) t, Lp.coeFn_smul c (u t)] with x hcu hu hsmul
  simp only [Pi.smul_apply] at ht hsmul ⊢
  rw [hcu, ht, hsmul, hu]

end MeasureTheory.Lp
