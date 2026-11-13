/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.TestFunction.CompactCutoff
public import PDE.Spaces.Sobolev.Localization.Cutoff.VectorValued.FixedPoints

/-!
# Supported zero extension of Banach-valued Sobolev jets

A Sobolev function on `V ∩ Ω` whose base vanishes off a compact subset of `V` extends
by zero into `Ω` without changing its graph norm. A smooth cutoff equal to one on the
support fixes the whole weak jet, so each derivative coordinate has the indicator
representative. The support buffer is inside `V` and may meet the physical boundary of `Ω`.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal Sobolev Distributions

namespace SobolevSpace.VectorValued

open GraphSpace

variable {n k : ℕ} {p : ℝ≥0∞} {Ω V : Opens ℝ^n}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Sobolev jets whose base representative vanishes almost everywhere outside `C`. -/
def supportedSubmodule (C : Set ℝ^n) : Submodule ℝ W^{k,p}(Ω; F) where
  carrier := {U | ∀ᵐ x ∂domainMeasure n Ω, x ∉ C → U.val (baseIndex n k) x = 0}
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero F p (domainMeasure n Ω)] with x hx
    exact fun _ ↦ hx
  add_mem' := by
    intro U W hU hW
    filter_upwards [hU, hW, Lp.coeFn_add (U.val (baseIndex n k)) (W.val (baseIndex n k))]
      with x hxU hxW hx
    intro hxC
    exact hx.trans (by simp only [Pi.add_apply, hxU hxC, hxW hxC, add_zero])
  smul_mem' := by
    intro c U hU
    filter_upwards [hU, Lp.coeFn_smul c (U.val (baseIndex n k))] with x hxU hx
    intro hxC
    exact hx.trans (by simp only [Pi.smul_apply, hxU hxC, smul_zero])

/-- Membership requires support of the base only, not separate derivative support data. -/
@[simp] theorem mem_supportedSubmodule (C : Set ℝ^n) (U : W^{k,p}(Ω; F)) :
    U ∈ supportedSubmodule C ↔
      ∀ᵐ x ∂domainMeasure n Ω, x ∉ C → U.val (baseIndex n k) x = 0 :=
  Iff.rfl

variable [Fact (1 ≤ p)]

/-- The relative cutoff acts by an indicator product for any supplied base representative.
Its support is required only in the ambient neighborhood `V`. -/
theorem interMultiplier_base_indicator_ae
    (ψ : 𝓓((⊤ : Opens ℝ^n), ℝ)) (hψ : tsupport ψ.toFun ⊆ V)
    (U : W^{k,p}((V ⊓ Ω); F)) {f : ℝ^n → F}
    (hU : (U.val (baseIndex n k) : ℝ^n → F) =ᵐ[domainMeasure n (V ⊓ Ω)] f) :
    ((interMultiplier ψ hψ U).val (baseIndex n k) : ℝ^n → F)
      =ᵐ[domainMeasure n Ω] (V : Set ℝ^n).indicator (fun x ↦ ψ.toFun x • f x) := by
  apply (interMultiplier_base_ae ψ hψ U hU).trans
  exact Filter.Eventually.of_forall fun x ↦ by
    by_cases hx : x ∈ V
    · simp only [Set.indicator_of_mem hx]
    · have hzero : ψ.toFun x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hs ↦ hx (hψ hs))
      simp only [Set.indicator_of_notMem hx, hzero, zero_smul]

/-- Zero extension from `V ∩ Ω` into `Ω` is isometric on jets supported in a compact
subset of `V`. No support condition at the physical boundary of `Ω` is imposed. -/
def supportedZeroExtendₗᵢ {C : Set ℝ^n} (hC : IsCompact C) (hCV : C ⊆ V) :
    supportedSubmodule (k := k) (p := p) (Ω := V ⊓ Ω) (F := F) C
      →ₗᵢ[ℝ] W^{k,p}(Ω; F) :=
  let hex := TestFunction.exists_eq_one_on_compact V.isOpen hC hCV
  let ψ := hex.choose
  { toLinearMap := (interMultiplier ψ hex.choose_spec.1).toLinearMap.comp
      (supportedSubmodule C).subtype
    norm_map' U := by
      change ‖interMultiplier ψ hex.choose_spec.1 U.val‖ = ‖U.val‖
      rw [norm_interMultiplier_eq,
        compactSmoothMultiplierCLM_eq_self_of_base_support ψ.toFun ψ.contDiff
          ψ.hasCompactSupport U.val C hex.choose_spec.2.1 U.property] }

/-- Restricting supported zero extension recovers the entire original weak jet. -/
@[simp] theorem restrictCLM_supportedZeroExtendₗᵢ {C : Set ℝ^n}
    (hC : IsCompact C) (hCV : C ⊆ V)
    (U : supportedSubmodule (k := k) (p := p) (Ω := V ⊓ Ω) (F := F) C) :
    restrictCLM (show V ⊓ Ω ≤ Ω from inf_le_right) (supportedZeroExtendₗᵢ hC hCV U)
      = U.val := by
  let hex := TestFunction.exists_eq_one_on_compact V.isOpen hC hCV
  change restrictCLM _ (interMultiplier hex.choose hex.choose_spec.1 U.val) = U.val
  rw [restrictCLM_interMultiplier]
  exact compactSmoothMultiplierCLM_eq_self_of_base_support hex.choose.toFun
    hex.choose.contDiff hex.choose.hasCompactSupport U.val C hex.choose_spec.2.1 U.property

/-- The supported extension preserves the full graph norm at every exponent endpoint. -/
theorem norm_supportedZeroExtendₗᵢ {C : Set ℝ^n} (hC : IsCompact C) (hCV : C ⊆ V)
    (U : supportedSubmodule (k := k) (p := p) (Ω := V ⊓ Ω) (F := F) C) :
    ‖supportedZeroExtendₗᵢ hC hCV U‖ = ‖U‖ :=
  (supportedZeroExtendₗᵢ hC hCV).norm_map U

/-- Every extended derivative coordinate is zero almost everywhere outside `V`. -/
theorem supportedZeroExtendₗᵢ_eq_zero_ae {C : Set ℝ^n}
    (hC : IsCompact C) (hCV : C ⊆ V)
    (U : supportedSubmodule (k := k) (p := p) (Ω := V ⊓ Ω) (F := F) C) :
    ∀ᵐ x ∂domainMeasure n Ω, x ∉ V →
      ∀ a, (supportedZeroExtendₗᵢ hC hCV U).val a x = 0 := by
  let hex := TestFunction.exists_eq_one_on_compact V.isOpen hC hCV
  filter_upwards [interMultiplier_eq_zero_ae hex.choose hex.choose_spec.1 U.val] with x hx
  intro hxV a
  exact hx (fun hs ↦ hxV (hex.choose_spec.1 hs)) a

/-- Each derivative of supported zero extension is the indicator of the input derivative. -/
theorem supportedZeroExtendₗᵢ_coordinate_ae {C : Set ℝ^n}
    (hC : IsCompact C) (hCV : C ⊆ V)
    (U : supportedSubmodule (k := k) (p := p) (Ω := V ⊓ Ω) (F := F) C)
    (a : DerivIndex n k) :
    ((supportedZeroExtendₗᵢ hC hCV U).val a : ℝ^n → F) =ᵐ[domainMeasure n Ω]
      (V : Set ℝ^n).indicator (fun x ↦ U.val.val a x) := by
  have hinside := restrictCLM_apply_ae (show V ⊓ Ω ≤ Ω from inf_le_right)
    (supportedZeroExtendₗᵢ hC hCV U) a
  rw [restrictCLM_supportedZeroExtendₗᵢ] at hinside
  apply ae_of_ae_restrict_of_ae_restrict_compl (V : Set ℝ^n)
  · have hmeasure : (domainMeasure n Ω).restrict V = domainMeasure n (V ⊓ Ω) := by
      rw [domainMeasure, Measure.restrict_restrict V.isOpen.measurableSet]
      rfl
    rw [hmeasure]
    filter_upwards [hinside, ae_restrict_mem (V ⊓ Ω).isOpen.measurableSet] with x hx hxV
    exact hx.symm.trans (Set.indicator_of_mem hxV.1 _).symm
  · filter_upwards [ae_mono Measure.restrict_le_self
      (supportedZeroExtendₗᵢ_eq_zero_ae hC hCV U),
      ae_restrict_mem V.isOpen.measurableSet.compl] with x hx hxV
    exact (hx hxV a).trans (Set.indicator_of_notMem hxV _).symm

/-- Any representative of an input derivative gives the same indicator representative
for the extended derivative. -/
theorem supportedZeroExtendₗᵢ_coordinate_ae_of_ae {C : Set ℝ^n}
    (hC : IsCompact C) (hCV : C ⊆ V)
    (U : supportedSubmodule (k := k) (p := p) (Ω := V ⊓ Ω) (F := F) C)
    (a : DerivIndex n k) {f : ℝ^n → F}
    (hf : (U.val.val a : ℝ^n → F) =ᵐ[domainMeasure n (V ⊓ Ω)] f) :
    ((supportedZeroExtendₗᵢ hC hCV U).val a : ℝ^n → F) =ᵐ[domainMeasure n Ω]
      (V : Set ℝ^n).indicator f := by
  apply (supportedZeroExtendₗᵢ_coordinate_ae hC hCV U a).trans
  apply (ae_eq_restrict_iff_indicator_ae_eq V.isOpen.measurableSet).mp
  simpa only [domainMeasure, Opens.coe_inf, Set.inf_eq_inter,
    Measure.restrict_restrict V.isOpen.measurableSet] using hf

/-- The physical base of supported extension is the zero extension of any supplied
representative on the intersection. -/
theorem supportedZeroExtendₗᵢ_base_ae {C : Set ℝ^n}
    (hC : IsCompact C) (hCV : C ⊆ V)
    (U : supportedSubmodule (k := k) (p := p) (Ω := V ⊓ Ω) (F := F) C)
    {f : ℝ^n → F}
    (hf : (U.val.val (baseIndex n k) : ℝ^n → F) =ᵐ[domainMeasure n (V ⊓ Ω)] f) :
    ((supportedZeroExtendₗᵢ hC hCV U).val (baseIndex n k) : ℝ^n → F)
      =ᵐ[domainMeasure n Ω] (V : Set ℝ^n).indicator f :=
  supportedZeroExtendₗᵢ_coordinate_ae_of_ae hC hCV U (baseIndex n k) hf

end SobolevSpace.VectorValued
