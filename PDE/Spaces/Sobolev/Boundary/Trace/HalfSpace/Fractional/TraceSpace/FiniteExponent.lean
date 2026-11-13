/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.Fractional.Range
public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.FiniteExponentTraceSpace

/-!
# The finite-exponent quotient trace space is a Gagliardo space

For `1 < p < ∞`, the quotient of `W^{1,p}(ℝ^(n + 1)₊)` by its physical trace
kernel is continuously linearly equivalent to `W^{1 - 1 / p,p}(ℝ^n)`, realized
by the Gagliardo graph space. The forward map descends the fractional
trace. Its inverse takes the quotient class of the constructed mollified lifting.

The equivalence preserves the physical boundary `Lᵖ` value. The norm estimates
use the fractional trace bound and the lifting bound; the equivalence need not
be an isometry. All dimensions,
including the singleton boundary when `n = 0`, are allowed.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Trace.HalfSpace

open MeasureTheory Set
open scoped ENNReal Sobolev
open Approximation Fractional

variable (n : ℕ) (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p)

/-- The fractional trace and the physical `Lᵖ` trace have the same kernel. -/
theorem ker_traceGagliardo :
    (traceGagliardo n p hp).ker = (traceLp n p hp.le).ker := by
  ext u
  change traceGagliardo n p hp u = 0 ↔ traceLp n p hp.le u = 0
  constructor
  · intro hu
    have h := toLp_traceGagliardo_apply_ae n p hp u
    rw [hu, map_zero] at h
    have hz :
        ((0 : Lp ℝ (ENNReal.ofReal p) (volume.restrict (univ : Set (ℝ^n)))) :
          ℝ^n → ℝ) =ᵐ[volume] 0 := by
      exact (Lp.coeFn_zero ℝ (ENNReal.ofReal p) (volume.restrict univ)).filter_mono
        (ae_mono (by simp only [Measure.restrict_univ, le_refl]))
    apply Lp.ext
    exact h.symm.trans (hz.trans (Lp.coeFn_zero ℝ (ENNReal.ofReal p) volume).symm)
  · intro hu
    apply GagliardoSpace.toLp_injective
    rw [map_zero, toLp_traceGagliardo, hu, map_zero]

/-- Identify the intrinsic quotient trace space with the fractional Gagliardo space. -/
def lpTraceSpaceEquivGagliardo :
    LpTraceSpace n p hp.le ≃L[ℝ]
      GagliardoSpace n (1 - 1 / p) univ (p := ENNReal.ofReal p) :=
  let forward := (traceLp n p hp.le).ker.liftQL (traceGagliardo n p hp)
    (le_of_eq (ker_traceGagliardo n p hp).symm)
  let backward := (traceLpClass n p hp.le).comp
    (mollifiedLifting (standardMollifier n) hp)
  ContinuousLinearEquiv.equivOfInverse forward backward
    (by
      intro q
      obtain ⟨u, rfl⟩ := (traceLp n p hp.le).ker.mkQ_surjective q
      change Submodule.Quotient.mk
          (mollifiedLifting (standardMollifier n) hp (traceGagliardo n p hp u)) =
        (Submodule.Quotient.mk u : LpTraceSpace n p hp.le)
      rw [Submodule.Quotient.eq, ← ker_traceGagliardo n p hp]
      change traceGagliardo n p hp
        (mollifiedLifting (standardMollifier n) hp (traceGagliardo n p hp u) - u) = 0
      rw [map_sub, traceGagliardo_mollifiedLifting, sub_self])
    (by
      intro g
      exact traceGagliardo_mollifiedLifting (standardMollifier n) hp g)

/-- A quotient class maps to the fractional trace of any representative. -/
@[simp]
theorem lpTraceSpaceEquivGagliardo_traceLpClass
    (u : W^{1,ENNReal.ofReal p}(ℝ^(n + 1)₊)) :
    lpTraceSpaceEquivGagliardo n p hp (traceLpClass n p hp.le u) =
      traceGagliardo n p hp u := rfl

/-- The inverse is the quotient class of the standard mollified lifting. -/
@[simp ←]
theorem lpTraceSpaceEquivGagliardo_symm_apply
    (g : GagliardoSpace n (1 - 1 / p) univ (p := ENNReal.ofReal p)) :
    (lpTraceSpaceEquivGagliardo n p hp).symm g =
      traceLpClass n p hp.le (mollifiedLifting (standardMollifier n) hp g) := rfl

/-- The quotient and fractional descriptions have the same physical `Lᵖ` value.
Restriction to `univ` transports between the two equal boundary measures. -/
@[simp]
theorem toLp_lpTraceSpaceEquivGagliardo (q : LpTraceSpace n p hp.le) :
    GagliardoSpace.toLp n (1 - 1 / p) univ (lpTraceSpaceEquivGagliardo n p hp q) =
      Lp.restrictionCLMOfLE Measure.restrict_le_self (boundaryValueLp n p hp.le q) := by
  obtain ⟨u, rfl⟩ := (traceLp n p hp.le).ker.mkQ_surjective q
  exact toLp_traceGagliardo n p hp u

/-- Passing from fractional data to their quotient class preserves the physical `Lᵖ` value. -/
@[simp]
theorem restrict_boundaryValueLp_lpTraceSpaceEquivGagliardo_symm
    (g : GagliardoSpace n (1 - 1 / p) univ (p := ENNReal.ofReal p)) :
    Lp.restrictionCLMOfLE Measure.restrict_le_self
        (boundaryValueLp n p hp.le ((lpTraceSpaceEquivGagliardo n p hp).symm g)) =
      GagliardoSpace.toLp n (1 - 1 / p) univ g := by
  rw [← toLp_lpTraceSpaceEquivGagliardo n p hp, ContinuousLinearEquiv.apply_symm_apply]

/-- The fractional norm is bounded by the quotient norm with the fractional trace constant. -/
theorem norm_lpTraceSpaceEquivGagliardo_le (q : LpTraceSpace n p hp.le) :
    ‖lpTraceSpaceEquivGagliardo n p hp q‖ ≤ ‖traceGagliardo n p hp‖ * ‖q‖ := by
  by_cases hT : ‖traceGagliardo n p hp‖ = 0
  · obtain ⟨u, rfl⟩ := (traceLp n p hp.le).ker.mkQ_surjective q
    change ‖traceGagliardo n p hp u‖ ≤ _
    simpa only [hT, zero_mul] using (traceGagliardo n p hp).le_opNorm u
  · have hpos : 0 < ‖traceGagliardo n p hp‖ :=
      lt_of_le_of_ne (norm_nonneg (traceGagliardo n p hp)) (Ne.symm hT)
    rw [mul_comm]
    apply (div_le_iff₀ hpos).mp
    apply QuotientAddGroup.le_norm_iff.mpr
    intro u hu
    have heq := congrArg (lpTraceSpaceEquivGagliardo n p hp) hu
    change lpTraceSpaceEquivGagliardo n p hp (traceLpClass n p hp.le u) = _ at heq
    rw [lpTraceSpaceEquivGagliardo_traceLpClass] at heq
    rw [← heq]
    apply (div_le_iff₀ hpos).mpr
    exact ((traceGagliardo n p hp).le_opNorm u).trans_eq (mul_comm _ _)

/-- The quotient norm is no greater than the norm of the constructed lifting. -/
theorem norm_lpTraceSpaceEquivGagliardo_symm_le_norm_mollifiedLifting
    (g : GagliardoSpace n (1 - 1 / p) univ (p := ENNReal.ofReal p)) :
    ‖(lpTraceSpaceEquivGagliardo n p hp).symm g‖ ≤
      ‖mollifiedLifting (standardMollifier n) hp g‖ := by
  rw [lpTraceSpaceEquivGagliardo_symm_apply]
  exact Submodule.Quotient.norm_mk_le (traceLp n p hp.le).ker
    (mollifiedLifting (standardMollifier n) hp g)

/-- The quotient norm is bounded by the fractional norm with the lifting constant. -/
theorem norm_lpTraceSpaceEquivGagliardo_symm_le
    (g : GagliardoSpace n (1 - 1 / p) univ (p := ENNReal.ofReal p)) :
    ‖(lpTraceSpaceEquivGagliardo n p hp).symm g‖ ≤
      ‖mollifiedLifting (standardMollifier n) hp‖ * ‖g‖ :=
  (norm_lpTraceSpaceEquivGagliardo_symm_le_norm_mollifiedLifting n p hp g).trans
    ((mollifiedLifting (standardMollifier n) hp).le_opNorm g)

end SobolevSpace.Trace.HalfSpace
