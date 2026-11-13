/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.VectorValued.ZeroBoundary.Coordinates
public import PDE.Spaces.Sobolev.Boundary.Trace.VectorValued.HalfSpace.Naturality
import PDE.Spaces.Sobolev.Boundary.Trace.VectorValued.HalfSpace.Scalar
import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.ZeroTraceExtension

/-!
# Zero extension of Banach-valued functions with zero half-space trace

If a first-order Sobolev function has zero trace, extending it by zero extends
each weak derivative by zero as well. We apply the scalar zero-trace theorem
after every continuous linear functional, using naturality of the trace.
Bochner local integrability follows from `Lp` membership before duality recovers
the vector weak derivative identities.

The resulting linear extension on the trace kernel preserves the
Sobolev graph norm and is a right inverse of restriction. The codomain is any
real Banach space, the real exponent is finite and at least one, and boundary
dimension zero is included.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace Set
open scoped ENNReal Sobolev

namespace SobolevSpace.VectorValued.Trace.HalfSpace

open GraphSpace GeometricExtension

private theorem zeroOrderExtensionLp_real {d : ℕ} {q : ℝ≥0∞} [Fact (1 ≤ q)]
    {Ω : Opens ℝ^d} (u : Lp ℝ q (domainMeasure d Ω)) :
    zeroOrderExtensionLp u = Extension.Lp.zeroExtendLp Ω.isOpen.measurableSet u := by
  apply Lp.ext
  exact (zeroOrderExtensionLp_apply_ae u).trans
    (Extension.Lp.zeroExtendLp_apply_ae Ω.isOpen.measurableSet u).symm

variable {n : ℕ} {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Zero trace makes the indicator extensions of all first-order coordinates
satisfy the global Banach-valued weak derivative identities. -/
theorem zeroExtendAmbient_mem_of_traceLp_eq_zero (hp : 1 ≤ p)
    (U : W^{1,ENNReal.ofReal p}(⟨ℝ^(n + 1)₊,
      SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩; F))
    (hU : traceLp n p hp U = 0) :
    IsWkpOn (zeroExtendAmbient U.val) := by
  intro a
  apply (hasWeakDerivativeOn_iff_forall_dual
    (locallyIntegrableOn_of_locallyIntegrable_restrict
      ((Lp.memLp _).locallyIntegrable Fact.out))
    (locallyIntegrableOn_of_locallyIntegrable_restrict
      ((Lp.memLp _).locallyIntegrable Fact.out))).mpr
  intro L
  have htrace : SobolevSpace.Trace.HalfSpace.traceLp n p hp
      (scalarEquiv (mapCLM L U)) = 0 := by
    rw [← traceLp_eq_scalar_traceLp, traceLp_mapCLM, hU, map_zero]
  have hweak := SobolevSpace.Trace.HalfSpace.zeroExtendAmbient_mem_of_traceLp_eq_zero
    p hp (scalarEquiv (mapCLM L U)) htrace a
  have hcoord (b : DerivIndex (n + 1) 1) :
      (GraphSpace.ZeroTrace.zeroExtendAmbient
        (SobolevSpace.HalfSpace.measurableSet_upper (n := n + 1))
        (scalarEquiv (mapCLM L U)).val b : ℝ^(n + 1) → ℝ)
        =ᵐ[domainMeasure (n + 1) univ]
          L ∘ (zeroExtendAmbient U.val b : ℝ^(n + 1) → F) := by
    rw [GraphSpace.ZeroTrace.zeroExtendAmbient_apply]
    change (Extension.Lp.zeroExtendLp _ (L.compLpL _ _ (U.val b)) :
      ℝ^(n + 1) → ℝ) =ᵐ[_] _
    rw [← zeroOrderExtensionLp_real, zeroExtendAmbient_apply]
    simpa only [domainMeasure, Measure.restrict_univ] using
      zeroOrderExtensionLp_compLpL_ae L (U.val b)
  exact hweak.congr_ae (hcoord (baseIndex (n + 1) 1)) (hcoord a)

/-- Zero extension on the kernel of the Banach-valued half-space trace.
All global weak derivatives are constructed from the zero-trace hypothesis. -/
def zeroExtendCLM (hp : 1 ≤ p) :
    (traceLp (F := F) n p hp).ker →L[ℝ] W^{1,ENNReal.ofReal p}(ℝ^(n + 1); F) :=
  ((zeroExtendAmbient.comp
    (wkpSubmoduleOn (n + 1) 1 (ENNReal.ofReal p)
      ⟨ℝ^(n + 1)₊, SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩ F).subtypeL).comp
        (traceLp (F := F) n p hp).ker.subtypeL).codRestrict
    (wkpSubmoduleOn (n + 1) 1 (ENNReal.ofReal p) ⊤ F)
    (fun U ↦ zeroExtendAmbient_mem_of_traceLp_eq_zero hp U.val U.property)

/-- Every coordinate of the Sobolev zero extension is the `Lp` zero extension. -/
theorem zeroExtendCLM_coordinate (hp : 1 ≤ p)
    (U : (traceLp (F := F) n p hp).ker) (a : DerivIndex (n + 1) 1) :
    coordinateCLM a (zeroExtendCLM hp U) = zeroOrderExtensionLp (U.val.val a) :=
  rfl

/-- The representatives of the function and all its first weak derivatives
extend by zero, almost everywhere on the whole space. -/
theorem zeroExtendCLM_coordinate_apply_ae (hp : 1 ≤ p)
    (U : (traceLp (F := F) n p hp).ker) (a : DerivIndex (n + 1) 1) :
    (coordinateCLM a (zeroExtendCLM hp U) : ℝ^(n + 1) → F) =ᵐ[volume]
      (ℝ^(n + 1)₊ : Set ℝ^(n + 1)).indicator (U.val.val a : ℝ^(n + 1) → F) :=
  zeroExtendAmbient_apply_ae U.val.val a

/-- Zero extension preserves the full first-order Sobolev graph norm. -/
theorem norm_zeroExtendCLM (hp : 1 ≤ p) (U : (traceLp (F := F) n p hp).ker) :
    ‖zeroExtendCLM hp U‖ = ‖U‖ :=
  norm_zeroExtendAmbient U.val.val

/-- Restriction of the zero extension recovers the original Sobolev function. -/
@[simp] theorem restrictCLM_zeroExtendCLM (hp : 1 ≤ p)
    (U : (traceLp (F := F) n p hp).ker) :
    restrictCLM (show
      (⟨ℝ^(n + 1)₊, SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩ :
        Opens ℝ^(n + 1)) ≤ ⊤ from le_top) (zeroExtendCLM hp U) = U.val := by
  apply Subtype.ext
  apply PiLp.ext
  intro a
  exact restrict_zeroExtendAmbient U.val.val a

/-- As continuous linear maps, zero extension followed by restriction on the
trace kernel gives the inclusion into the original Sobolev space. -/
@[simp] theorem restrictCLM_comp_zeroExtendCLM (hp : 1 ≤ p) :
    (restrictCLM (show
      (⟨ℝ^(n + 1)₊, SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩ :
        Opens ℝ^(n + 1)) ≤ ⊤ from le_top)).comp (zeroExtendCLM (F := F) hp) =
          (traceLp (F := F) n p hp).ker.subtypeL := by
  ext U : 1
  exact restrictCLM_zeroExtendCLM hp U

end SobolevSpace.VectorValued.Trace.HalfSpace
