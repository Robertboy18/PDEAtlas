/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Semilinear.SubSupersolution
public import PDE.Elliptic.Semilinear.SubSupersolution.BoundaryTrace

/-!
# Signed-trace barriers and reactions on a bounded value range

Ordered H¹ barriers with opposite boundary trace signs enclose a zero-boundary
weak solution. Continuity and a monotone linear shift are required only on a
bounded interval containing the barriers. Extending the shifted reaction gives
the global iteration problem; the barrier bounds then identify its solution
and nonlinear load with those of the original reaction.
-/

open scoped Sobolev

@[expose] public noncomputable section

namespace PDE.Elliptic.Semilinear

open SobolevSpace SobolevSpace.GraphSpace

open MeasureTheory Set Boundary
open Boundary.Geometry.SurfaceMeasure
open PDE.Analysis.Variational
open scoped ENNReal NNReal

variable {m : ℕ} {Ω : Set ℝ^(m + 1)}
local notation "μ" => domainMeasure (m + 1) Ω

/-- General H¹ barriers with signed geometric traces enclose a weak solution when
the reaction is continuous and has a lower one-sided slope bound only on their
bounded value range. No condition is imposed on the reaction outside that range. -/
theorem exists_weak_solution_between_H1_barriers_of_continuousOn_of_monotone_shift
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hgraph : HasC1GraphBoundary Ω)
    (a : Fin (m + 1) → Fin (m + 1) → DerivLp (m + 1) ∞ Ω)
    (b : Fin (m + 1) → DerivLp (m + 1) ∞ Ω) (c : DerivLp (m + 1) ∞ Ω)
    {alpha beta gamma : ℝ}
    (hA : IntegratedElliptic (multiplicationCoefficientOperator a) alpha)
    (hbc : LowerOrderBounds (multiplicationFirstOrderOperator b)
      (multiplicationZeroOrderOperator c) beta gamma)
    (f : ℝ → ℝ) {left right M : ℝ}
    (hf : ContinuousOn f (Icc left right))
    (hmono : MonotoneOn (fun s ↦ f s + M * s) (Icc left right))
    (lower upper : H¹(Ω))
    (htraceLower : let := hgraph.c1ExtensionAtlas hΩ hb
      ∀ᵐ x ∂surfaceMeasure Ω, Trace.C1.trace lower x ≤ 0)
    (htraceUpper : let := hgraph.c1ExtensionAtlas hΩ hb
      ∀ᵐ x ∂surfaceMeasure Ω, 0 ≤ Trace.C1.trace upper x)
    (hlr : ∀ᵐ x ∂μ, wkpBaseCoordinateCLM lower x ≤ wkpBaseCoordinateCLM upper x)
    (hleft : ∀ᵐ x ∂μ, left ≤ wkpBaseCoordinateCLM lower x)
    (hright : ∀ᵐ x ∂μ, wkpBaseCoordinateCLM upper x ≤ right)
    (hlower : ∀ v : H¹₀(Ω), (∀ᵐ x ∂μ, 0 ≤ baseCoordCLM v x) →
      interiorFullDivergenceOperator a b c lower v ≤
        ∫ x, f (wkpBaseCoordinateCLM lower x) * baseCoordCLM v x ∂μ)
    (hupper : ∀ v : H¹₀(Ω), (∀ᵐ x ∂μ, 0 ≤ baseCoordCLM v x) →
      (∫ x, f (wkpBaseCoordinateCLM upper x) * baseCoordCLM v x ∂μ) ≤
        interiorFullDivergenceOperator a b c upper v) :
    ∃ u : H¹₀(Ω),
      (∀ᵐ x ∂μ, wkpBaseCoordinateCLM lower x ≤ baseCoordCLM u x) ∧
      (∀ᵐ x ∂μ, baseCoordCLM u x ≤ wkpBaseCoordinateCLM upper x) ∧
      MemLp (fun x ↦ f (baseCoordCLM u x)) 2 μ ∧
      ∀ v : H¹₀(Ω), interiorFullDivergenceOperator a b c (u : H¹(Ω)) v =
        ∫ x, f (baseCoordCLM u x) * baseCoordCLM v x ∂μ := by
  obtain ⟨g, A, hg, hfg, hgrowth, hgmono⟩ :=
    exists_linear_growth_extension_of_monotoneOn_shift f hf hmono
  have hlo : (fun x ↦ f (wkpBaseCoordinateCLM lower x)) =ᵐ[μ]
      fun x ↦ g (wkpBaseCoordinateCLM lower x) := by
    filter_upwards [hleft, hlr, hright] with x hx hxy hy
    exact hfg ⟨hx, hxy.trans hy⟩
  have hup : (fun x ↦ f (wkpBaseCoordinateCLM upper x)) =ᵐ[μ]
      fun x ↦ g (wkpBaseCoordinateCLM upper x) := by
    filter_upwards [hleft, hlr, hright] with x hx hxy hy
    exact hfg ⟨hx.trans hxy, hy⟩
  obtain ⟨u, hlu, huu, hmem, heq⟩ :=
    exists_weak_solution_between_H1_barriers_of_continuous_of_monotone_shift
      hΩ hb hgraph a b c hA hbc g hg hgrowth hgmono lower upper
      htraceLower htraceUpper hlr
      (fun v hv ↦ (hlower v hv).trans_eq
        (integral_congr_ae (hlo.mono fun x hx ↦ congrArg (· * baseCoordCLM v x) hx)))
      (fun v hv ↦ (integral_congr_ae
        (hup.mono fun x hx ↦ congrArg (· * baseCoordCLM v x) hx)).symm.trans_le
          (hupper v hv))
  have hu : (fun x ↦ f (baseCoordCLM u x)) =ᵐ[μ]
      fun x ↦ g (baseCoordCLM u x) := by
    filter_upwards [hleft, hlu, huu, hright] with x hx hl hu hy
    exact hfg ⟨hx.trans hl, hu.trans hy⟩
  refine ⟨u, hlu, huu, MemLp.ae_eq hu.symm hmem, fun v ↦ ?_⟩
  exact (heq v).trans (integral_congr_ae
    (hu.symm.mono fun x hx ↦ congrArg (· * baseCoordCLM v x) hx))

/-- A reaction that is Lipschitz only on the bounded barrier range admits a
zero-boundary weak solution between arbitrary H¹ barriers with signed traces. -/
theorem exists_weak_solution_between_H1_barriers_of_lipschitzOn
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hgraph : HasC1GraphBoundary Ω)
    (a : Fin (m + 1) → Fin (m + 1) → DerivLp (m + 1) ∞ Ω)
    (b : Fin (m + 1) → DerivLp (m + 1) ∞ Ω) (c : DerivLp (m + 1) ∞ Ω)
    {alpha beta gamma : ℝ}
    (hA : IntegratedElliptic (multiplicationCoefficientOperator a) alpha)
    (hbc : LowerOrderBounds (multiplicationFirstOrderOperator b)
      (multiplicationZeroOrderOperator c) beta gamma)
    (f : ℝ → ℝ) {left right : ℝ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f (Icc left right))
    (lower upper : H¹(Ω))
    (htraceLower : let := hgraph.c1ExtensionAtlas hΩ hb
      ∀ᵐ x ∂surfaceMeasure Ω, Trace.C1.trace lower x ≤ 0)
    (htraceUpper : let := hgraph.c1ExtensionAtlas hΩ hb
      ∀ᵐ x ∂surfaceMeasure Ω, 0 ≤ Trace.C1.trace upper x)
    (hlr : ∀ᵐ x ∂μ, wkpBaseCoordinateCLM lower x ≤ wkpBaseCoordinateCLM upper x)
    (hleft : ∀ᵐ x ∂μ, left ≤ wkpBaseCoordinateCLM lower x)
    (hright : ∀ᵐ x ∂μ, wkpBaseCoordinateCLM upper x ≤ right)
    (hlower : ∀ v : H¹₀(Ω), (∀ᵐ x ∂μ, 0 ≤ baseCoordCLM v x) →
      interiorFullDivergenceOperator a b c lower v ≤
        ∫ x, f (wkpBaseCoordinateCLM lower x) * baseCoordCLM v x ∂μ)
    (hupper : ∀ v : H¹₀(Ω), (∀ᵐ x ∂μ, 0 ≤ baseCoordCLM v x) →
      (∫ x, f (wkpBaseCoordinateCLM upper x) * baseCoordCLM v x ∂μ) ≤
        interiorFullDivergenceOperator a b c upper v) :
    ∃ u : H¹₀(Ω),
      (∀ᵐ x ∂μ, wkpBaseCoordinateCLM lower x ≤ baseCoordCLM u x) ∧
      (∀ᵐ x ∂μ, baseCoordCLM u x ≤ wkpBaseCoordinateCLM upper x) ∧
      MemLp (fun x ↦ f (baseCoordCLM u x)) 2 μ ∧
      ∀ v : H¹₀(Ω), interiorFullDivergenceOperator a b c (u : H¹(Ω)) v =
        ∫ x, f (baseCoordCLM u x) * baseCoordCLM v x ∂μ := by
  have hmono : MonotoneOn (fun s ↦ f s + (K : ℝ) * s) (Icc left right) := by
    intro s hs t ht hst
    have h := hf.le_add_mul hs ht
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hst)] at h
    nlinarith
  exact exists_weak_solution_between_H1_barriers_of_continuousOn_of_monotone_shift
    hΩ hb hgraph a b c hA hbc f hf.continuousOn hmono lower upper
    htraceLower htraceUpper hlr hleft hright hlower hupper

end PDE.Elliptic.Semilinear
