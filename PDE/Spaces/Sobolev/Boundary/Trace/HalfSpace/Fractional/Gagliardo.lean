/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.Fractional.Estimate
public import PDE.Spaces.Sobolev.Boundary.Trace.VectorValued.HalfSpace.Fractional.Gagliardo
public import PDE.Spaces.Sobolev.Boundary.Trace.VectorValued.HalfSpace.Scalar

/-!
# The finite-exponent half-space trace in the Gagliardo graph

For `1 < p < ∞`, the boundary trace of a real `W¹ᵖ` function belongs to the
intrinsic space of order `1 - 1 / p`. The graph norm combines the boundary
`Lᵖ` norm and the weighted-difference `Lᵖ` norm by their p-sum.

The map `traceGagliardo` takes the physical `traceLp` class into this graph,
with operator norm at most `(p + C) ^ (1 / p)`, where `C` is a constant of the fractional
energy estimate `exists_trace_fractional_bound`. It is the Banach-valued trace at
`F := ℝ`: the canonical isometry between the real and Banach-valued Sobolev
graphs carries one trace to the other. All boundary dimensions, including zero,
are allowed.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal Sobolev

namespace SobolevSpace.Trace.HalfSpace

open SobolevSpace.Fractional
open VectorValued.Trace.HalfSpace (upperScalarEquiv traceLp_upperScalarEquiv_symm)

variable (n : ℕ) (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]

/-- The physical finite-exponent trace satisfies the intrinsic Gagliardo
condition at order `1 - 1 / p`. -/
theorem memGagliardo_traceLp (hp : 1 < p)
    (u : W^{1,ENNReal.ofReal p}(ℝ^(n+1)₊)) :
    MemGagliardo n (1 - 1 / p) Set.univ (traceLp n p hp.le u)
      (p := ENNReal.ofReal p) := by
  simpa only [traceLp_upperScalarEquiv_symm] using
    VectorValued.Trace.HalfSpace.memGagliardo_traceLp n p hp
      ((upperScalarEquiv n p).symm u)

/-- The bounded trace into the intrinsic Gagliardo space of order `1 - 1 / p`.
It is the Banach-valued Gagliardo trace at `F := ℝ`, and its first graph
coordinate is the physical `Lᵖ` boundary trace. -/
def traceGagliardo (hp : 1 < p) :
    W^{1,ENNReal.ofReal p}(ℝ^(n+1)₊) →L[ℝ]
      GagliardoSpace n (1 - 1 / p) Set.univ (p := ENNReal.ofReal p) :=
  (VectorValued.Trace.HalfSpace.traceGagliardo (F := ℝ) n p hp).comp
    ((upperScalarEquiv n p).symm.toContinuousLinearEquiv : _ →L[ℝ] _)

/-- The Gagliardo trace has the physical `traceLp` representative almost
everywhere on the boundary. -/
theorem toLp_traceGagliardo_apply_ae (hp : 1 < p)
    (u : W^{1,ENNReal.ofReal p}(ℝ^(n+1)₊)) :
    (GagliardoSpace.toLp n (1 - 1 / p) Set.univ (traceGagliardo n p hp u) : ℝ^n → ℝ)
      =ᵐ[volume] (traceLp n p hp.le u : ℝ^n → ℝ) := by
  have h := VectorValued.Trace.HalfSpace.toLp_traceGagliardo_apply_ae n p hp
    ((upperScalarEquiv n p).symm u)
  rw [traceLp_upperScalarEquiv_symm] at h
  exact h

/-- Projection of the Gagliardo trace is exactly the `Lᵖ` trace. Restriction
to `univ` transports between the two equal boundary measures. -/
@[simp]
theorem toLp_traceGagliardo (hp : 1 < p)
    (u : W^{1,ENNReal.ofReal p}(ℝ^(n+1)₊)) :
    GagliardoSpace.toLp n (1 - 1 / p) Set.univ (traceGagliardo n p hp u) =
      Lp.restrictionCLMOfLE Measure.restrict_le_self (traceLp n p hp.le u) := by
  rw [← traceLp_upperScalarEquiv_symm]
  exact VectorValued.Trace.HalfSpace.toLp_traceGagliardo n p hp
    ((upperScalarEquiv n p).symm u)

/-- The physical projection commutes with the trace as an equality of
continuous linear maps. -/
theorem toLp_comp_traceGagliardo (hp : 1 < p) :
    (GagliardoSpace.toLp n (1 - 1 / p) Set.univ).comp (traceGagliardo n p hp) =
      (Lp.restrictionCLMOfLE Measure.restrict_le_self).comp (traceLp n p hp.le) := by
  apply ContinuousLinearMap.ext
  intro u
  exact toLp_traceGagliardo n p hp u

/-- There is a constant `C` for the fractional energy estimate of
`exists_trace_fractional_bound` such that the same `C` bounds the trace operator by
`(p + C) ^ (1 / p)`. -/
theorem exists_norm_traceGagliardo_le (hp : 1 < p) :
    ∃ C : ℝ≥0,
      (∀ u : W^{1,ENNReal.ofReal p}(ℝ^(n+1)₊),
        (∫⁻ z : ℝ^n × ℝ^n,
          ‖traceLp n p hp.le u z.1 - traceLp n p hp.le u z.2‖ₑ ^ p /
            (ENNReal.ofReal ‖z.1 - z.2‖) ^ ((n : ℝ) + p - 1)
          ∂((volume : Measure (ℝ^n)).prod volume)) ≤
        (C : ℝ≥0∞) * ∑ i : Fin (n + 1), ‖∂[i] u‖ₑ ^ p) ∧
      ‖traceGagliardo n p hp‖ ≤ (p + C) ^ (1 / p) := by
  obtain ⟨C, hC⟩ := exists_trace_fractional_bound n p hp
  refine ⟨C, hC, ?_⟩
  have hCvec := VectorValued.Trace.HalfSpace.norm_traceGagliardo_le_of_energy_bound
    (F := ℝ) n p hp C fun U ↦ by
      have h := hC (upperScalarEquiv n p U)
      rw [← VectorValued.Trace.HalfSpace.traceLp_eq_scalar_traceLp] at h
      refine h.trans_eq ?_
      congr 1
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u ↦ ?_
  calc
    ‖traceGagliardo n p hp u‖ ≤
        ‖VectorValued.Trace.HalfSpace.traceGagliardo (F := ℝ) n p hp‖ *
          ‖(upperScalarEquiv n p).symm u‖ :=
      (VectorValued.Trace.HalfSpace.traceGagliardo (F := ℝ) n p hp).le_opNorm _
    _ ≤ (p + C) ^ (1 / p) * ‖u‖ := by
      rw [LinearIsometryEquiv.norm_map]
      exact mul_le_mul_of_nonneg_right hCvec (norm_nonneg u)

/-- At exponent two, the physical Gagliardo trace agrees with the Hilbert
`H¹` trace under the canonical identification of the interior spaces. -/
theorem toLp_traceGagliardo_two_apply_ae
    (u : W^{1,ENNReal.ofReal (2 : ℝ)}(ℝ^(n+1)₊)) :
    (GagliardoSpace.toLp n (1 - 1 / (2 : ℝ)) Set.univ
        (traceGagliardo n 2 (by norm_num) u) : ℝ^n → ℝ)
      =ᵐ[volume] (trace n (upperW1pTwoEquivH1 n u) : ℝ^n → ℝ) := by
  refine (toLp_traceGagliardo_apply_ae n 2 (by norm_num) u).trans ?_
  rw [← boundaryLpTwoEquivL2_traceLp n u]
  exact Filter.Eventually.of_forall fun x ↦
    congrFun (Lp.coeFn_congrExponent (ENNReal.ofReal_ofNat 2) volume
      (traceLp n 2 (by norm_num) u)).symm x

end SobolevSpace.Trace.HalfSpace
