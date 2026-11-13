/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Lattice

/-!
# Order and domination at the boundary

An almost-everywhere inequality between Sobolev functions passes to their
geometric traces. Indeed, the positive part of their difference vanishes in
the domain, and taking a trace commutes with positive parts.

Consequently, if `|u| ≤ v` and `v` has zero trace, then `u` has zero trace too.
This is useful for nonlinear variations: a pointwise bound on their change
can preserve the boundary data without requiring smooth test functions.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Trace.C1

open MeasureTheory Set GraphSpace Boundary Approximation.UpToBoundary
open Boundary.Geometry.SurfaceMeasure
open scoped ENNReal Sobolev

variable {m : ℕ} {Ω : Set ℝ^(m + 1)} [H : C1ExtensionAtlas (m + 1) Ω]

private theorem trace_le_of_posPart
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (T : W^{1,p}(Ω) →L[ℝ] Lp ℝ p (surfaceMeasure Ω))
    (hT : ∀ U, T (lipschitzCompositionOn H.isOpen Lp.lipschitzWith_pos_part U) =
      Lp.posPart (T U))
    {U V : W^{1,p}(Ω)}
    (hUV : ∀ᵐ x ∂domainMeasure (m + 1) Ω,
      baseRepresentative U x ≤ baseRepresentative V x) :
    ∀ᵐ x ∂surfaceMeasure Ω,
      (T U : ℝ^(m + 1) → ℝ) x ≤ (T V : ℝ^(m + 1) → ℝ) x := by
  have hzero : lipschitzCompositionOn H.isOpen Lp.lipschitzWith_pos_part (U - V) = 0 := by
    apply WkpSpaceOn.ext_of_base_ae H.isOpen
    filter_upwards [lipschitzCompositionOn_base_ae H.isOpen Lp.lipschitzWith_pos_part (U - V),
      baseRepresentative_sub_ae U V, baseRepresentative_zero_ae, hUV] with
      x hpos hsub hz hle
    change baseRepresentative
      (lipschitzCompositionOn H.isOpen Lp.lipschitzWith_pos_part (U - V)) x =
        baseRepresentative (0 : W^{1,p}(Ω)) x
    change baseRepresentative
      (lipschitzCompositionOn H.isOpen Lp.lipschitzWith_pos_part (U - V)) x =
        max (baseRepresentative (U - V) x) 0 at hpos
    rw [hpos, hsub, hz]
    exact max_eq_right (sub_nonpos.mpr hle)
  apply (Lp.posPart_sub_eq_zero_iff (T U) (T V)).mp
  rw [← map_sub, ← hT, hzero, map_zero]

private theorem trace_eq_zero_of_domination
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (T : W^{1,p}(Ω) →L[ℝ] Lp ℝ p (surfaceMeasure Ω))
    (hT : ∀ U, T (lipschitzCompositionOn H.isOpen Lp.lipschitzWith_pos_part U) =
      Lp.posPart (T U))
    {U V : W^{1,p}(Ω)} (hV : T V = 0)
    (hUV : ∀ᵐ x ∂domainMeasure (m + 1) Ω,
      |baseRepresentative U x| ≤ baseRepresentative V x) :
    T U = 0 := by
  have hupper := trace_le_of_posPart T hT
    (hUV.mono fun x hx ↦ (le_abs_self _).trans hx)
  have hlower := trace_le_of_posPart T hT
    (U := -U) (V := V) (by
      filter_upwards [hUV, baseRepresentative_neg_ae U] with x hx hneg
      rw [hneg]
      exact (neg_le_abs _).trans hx)
  rw [hV] at hupper
  rw [map_neg, hV] at hlower
  apply Lp.ext
  filter_upwards [hupper, hlower, Lp.coeFn_neg (T U),
    Lp.coeFn_zero (E := ℝ) (p := p) (μ := surfaceMeasure Ω)] with x hu hl hn hz
  rw [hn, hz] at hl
  rw [hz] at hu ⊢
  exact le_antisymm hu (neg_nonpos.mp hl)

/-- Almost-everywhere order in the domain passes to the finite-exponent trace. -/
theorem traceLp_le_of_le_ae (P : InwardPartition Ω)
    (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    {U V : W^{1,ENNReal.ofReal p}(Ω)}
    (hUV : ∀ᵐ x ∂domainMeasure (m + 1) Ω,
      baseRepresentative U x ≤ baseRepresentative V x) :
    ∀ᵐ x ∂surfaceMeasure Ω,
      (traceLp p U : ℝ^(m + 1) → ℝ) x ≤
        (traceLp p V : ℝ^(m + 1) → ℝ) x :=
  trace_le_of_posPart (traceLp p) (traceLp_posPart P p) hUV

/-- Almost-everywhere order passes to the trace in the Hilbert convention. -/
theorem trace_le_of_le_ae (P : InwardPartition Ω)
    {U V : H¹(Ω)}
    (hUV : ∀ᵐ x ∂domainMeasure (m + 1) Ω,
      baseRepresentative U x ≤ baseRepresentative V x) :
    ∀ᵐ x ∂surfaceMeasure Ω,
      (trace U : ℝ^(m + 1) → ℝ) x ≤ (trace V : ℝ^(m + 1) → ℝ) x :=
  trace_le_of_posPart trace (trace_posPart P) hUV

/-- A Sobolev function dominated in absolute value by a zero-trace function
belongs to the closure-defined zero-boundary space. -/
theorem mem_Wkp0_of_abs_le_ae (P : InwardPartition Ω)
    (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    {U V : W^{1,ENNReal.ofReal p}(Ω)}
    (hV : V ∈ (wkp0SubmoduleOn (n := m + 1) (k := 1)
      (p := ENNReal.ofReal p) (Ω := Ω)).toSubmodule)
    (hUV : ∀ᵐ x ∂domainMeasure (m + 1) Ω,
      |baseRepresentative U x| ≤ baseRepresentative V x) :
    U ∈ (wkp0SubmoduleOn (n := m + 1) (k := 1)
      (p := ENNReal.ofReal p) (Ω := Ω)).toSubmodule :=
  (traceLp_eq_zero_iff_mem_Wkp0 p U).mp
    (trace_eq_zero_of_domination (traceLp p) (traceLp_posPart P p)
      ((traceLp_eq_zero_iff_mem_Wkp0 p V).mpr hV) hUV)

/-- Domination by an `H¹₀` function preserves zero boundary values for an
`H¹` function, without a smoothness assumption on either function. -/
theorem mem_H10_of_abs_le_ae (P : InwardPartition Ω)
    {U V : H¹(Ω)}
    (hV : V ∈ (h10SubmoduleOn (n := m + 1) (Ω := Ω)).toSubmodule)
    (hUV : ∀ᵐ x ∂domainMeasure (m + 1) Ω,
      |baseRepresentative U x| ≤ baseRepresentative V x) :
    U ∈ (h10SubmoduleOn (n := m + 1) (Ω := Ω)).toSubmodule :=
  (trace_eq_zero_iff_mem_H10 U).mp
    (trace_eq_zero_of_domination trace (trace_posPart P)
      ((trace_eq_zero_iff_mem_H10 V).mpr hV) hUV)

end SobolevSpace.Trace.C1
