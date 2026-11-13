/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.JointRepresentative.Basic
public import PDE.Analysis.MeasureTheory.Lp.RealL2.Integral

/-!
# Minkowski inequality for Bochner integrals in real L2

The spatial Lq norm of an L2-valued Bochner integral is bounded by the integral
of the spatial Lq norms, for every finite q at least one. Joint representatives
are constructed from Bochner integrability, with explicit almost-everywhere transport.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal

namespace MeasureTheory.Lp

/-- Minkowski bounds the spatial Lq norm of the actual Bochner integral of an
integrable real L2 curve by its section Lq norms. No joint representative or
spatial Lq membership is assumed. -/
theorem eLpNorm_integral_le_lintegral_eLpNorm {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    [SFinite μ] [SigmaFinite ν] {u : α → Lp ℝ 2 ν} (hu : Integrable u μ)
    {q : ℝ} (hq : 1 ≤ q) :
    eLpNorm (∫ t, u t ∂μ : Lp ℝ 2 ν) (ENNReal.ofReal q) ν ≤
      ∫⁻ t, eLpNorm (u t) (ENNReal.ofReal q) ν ∂μ := by
  obtain ⟨U, hU, hsec⟩ :=
    hu.aestronglyMeasurable.stronglyMeasurable_mk.exists_stronglyMeasurable_jointLpRepresentative
  have he : ∀ᵐ t ∂μ, (fun x ↦ U (t, x)) =ᵐ[ν] (u t : β → ℝ) := by
    filter_upwards [hu.aestronglyMeasurable.ae_eq_mk] with t ht
    rw [ht]
    exact hsec t
  apply (eLpNorm_integral_le_lintegral_sections hu hU he hq).trans_eq
  apply lintegral_congr_ae
  filter_upwards [he] with t ht
  exact eLpNorm_congr_ae ht

end MeasureTheory.Lp
