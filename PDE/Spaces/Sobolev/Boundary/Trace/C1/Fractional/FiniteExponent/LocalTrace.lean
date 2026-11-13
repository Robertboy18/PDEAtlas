/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.FiniteExponentOperator
public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.Fractional.Gagliardo

/-!
# Localized fractional traces for finite exponents

A partition piece of a C¹ domain is flattened into the upper half-space. Its trace
belongs to the intrinsic Gagliardo graph at order `1 - 1 / p` for every
real `p > 1`. The base coordinate is the physical flat trace; the graph norm keeps
both the boundary Lᵖ norm and the fractional difference energy.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Trace.C1.Fractional.FiniteExponent

open MeasureTheory Set
open SobolevSpace.Fractional
open Boundary.Geometry.SurfaceMeasure Extension.C1.BoundaryPiece
open scoped ENNReal Sobolev

variable {m : ℕ} {Ω : Set (ℝ^(m + 1))}
variable [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
variable (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]

/-- The fractional trace of a localized partition piece in a boundary chart. -/
def localTrace (hp : 1 < p) (i : Fin hΩ.N) :
    W^{1,ENNReal.ofReal p}(Ω) →L[ℝ]
      GagliardoSpace m (1 - 1 / p) univ (p := ENNReal.ofReal p) :=
  (HalfSpace.traceGagliardo m p hp).comp (flattenCLM (p := ENNReal.ofReal p) i)

/-- The base of the chart Gagliardo graph is the flat Lᵖ trace. -/
theorem toLp_localTrace_apply_ae (hp : 1 < p) (i : Fin hΩ.N)
    (u : W^{1,ENNReal.ofReal p}(Ω)) :
    (GagliardoSpace.toLp m (1 - 1 / p) univ (localTrace p hp i u) : ℝ^m → ℝ)
      =ᵐ[volume] (HalfSpace.traceLp m p hp.le
        (flattenCLM (p := ENNReal.ofReal p) i u) : ℝ^m → ℝ) :=
  HalfSpace.toLp_traceGagliardo_apply_ae m p hp _

/-- The exact base-coordinate equality, with the boundary measure restricted to `univ`. -/
@[simp]
theorem toLp_localTrace (hp : 1 < p) (i : Fin hΩ.N)
    (u : W^{1,ENNReal.ofReal p}(Ω)) :
    GagliardoSpace.toLp m (1 - 1 / p) univ (localTrace p hp i u) =
      Lp.restrictionCLMOfLE Measure.restrict_le_self
        (HalfSpace.traceLp m p hp.le (flattenCLM (p := ENNReal.ofReal p) i u)) :=
  HalfSpace.toLp_traceGagliardo m p hp _

/-- The flattening and flat trace bounds control the full fractional graph norm. -/
theorem norm_localTrace_le (hp : 1 < p) (i : Fin hΩ.N)
    (u : W^{1,ENNReal.ofReal p}(Ω)) :
    ‖localTrace p hp i u‖ ≤
      (‖HalfSpace.traceGagliardo m p hp‖ * ‖flattenCLM (p := ENNReal.ofReal p) i‖) *
        ‖u‖ := by
  calc
    ‖localTrace p hp i u‖ ≤ ‖HalfSpace.traceGagliardo m p hp‖ *
        ‖flattenCLM (p := ENNReal.ofReal p) i u‖ :=
      (HalfSpace.traceGagliardo m p hp).le_opNorm _
    _ ≤ ‖HalfSpace.traceGagliardo m p hp‖ *
        (‖flattenCLM (p := ENNReal.ofReal p) i‖ * ‖u‖) :=
      mul_le_mul_of_nonneg_left ((flattenCLM (p := ENNReal.ofReal p) i).le_opNorm u)
        (norm_nonneg (HalfSpace.traceGagliardo m p hp))
    _ = _ := (mul_assoc _ _ _).symm

end SobolevSpace.Trace.C1.Fractional.FiniteExponent
