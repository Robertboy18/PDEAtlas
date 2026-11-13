/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Foundations.VectorValued.WeakDerivatives
public import PDE.Spaces.Sobolev.GraphSpace.Model.Definitions

/-!
# Banach-valued Sobolev graph spaces

The coordinates use the scalar graph model's symmetric derivative indices and Mathlib's
`Lp` quotient. Their finite `PiLp p` product carries the same Sobolev norm convention:
the finite ℓᵖ norm when `p < ∞`, and the maximum of the coordinate norms at infinity.
The graph submodule imposes the Banach-valued weak-derivative relation.

The codomain is any complete normed real vector space. No finite-dimensionality,
reflexivity, bounded-domain, or finite-measure assumption is needed.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal

namespace SobolevSpace.VectorValued

open GraphSpace

/-- The finite product of Banach-valued `Lp` derivative coordinates, with the ℓᵖ norm. -/
abbrev WkpAmbientOn (n k : ℕ) (p : ℝ≥0∞) (Ω : Opens ℝ^n)
    (F : Type*) [NormedAddCommGroup F] :=
  GraphSpace.DerivativeFamily n k p Ω F

variable {n k : ℕ} {p : ℝ≥0∞} {Ω : Opens ℝ^n}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Every coordinate is the indicated weak derivative of the base coordinate. -/
def IsWkpOn (U : WkpAmbientOn n k p Ω F) : Prop :=
  ∀ a : DerivIndex n k, HasWeakDerivativeOn Ω a.toList (U (baseIndex n k)) (U a)

/-- The graph relation also holds for any ordering of a symmetric derivative word. -/
theorem IsWkpOn.hasWeakDerivativeOn_list {U : WkpAmbientOn n k p Ω F}
    (hU : IsWkpOn U) (α : List (Fin n)) (hα : α.length ≤ k) :
    HasWeakDerivativeOn Ω α (U (baseIndex n k)) (U (derivIndexOfList α hα)) :=
  (hU (derivIndexOfList α hα)).perm (derivIndexOfList_toList_perm α hα)

/-- The zero bundle satisfies every weak-derivative identity. -/
theorem isWkpOn_zero : IsWkpOn (0 : WkpAmbientOn n k p Ω F) := by
  intro a
  have hzero : HasWeakDerivativeOn Ω a.toList (0 : ℝ^n → F) 0 := by
    refine ⟨locallyIntegrableOn_const 0, locallyIntegrableOn_const 0, ?_⟩
    intro φ
    simp
  exact hzero.congr_ae (Lp.coeFn_zero F p (domainMeasure n Ω)).symm
    (Lp.coeFn_zero F p (domainMeasure n Ω)).symm

/-- Addition of derivative bundles preserves the weak-derivative constraints. -/
theorem IsWkpOn.add {U V : WkpAmbientOn n k p Ω F}
    (hU : IsWkpOn U) (hV : IsWkpOn V) : IsWkpOn (U + V) := by
  intro a
  exact ((hU a).add (hV a)).congr_ae
    (Lp.coeFn_add (U (baseIndex n k)) (V (baseIndex n k))).symm
    (Lp.coeFn_add (U a) (V a)).symm

/-- Real scalar multiplication preserves the weak-derivative constraints. -/
theorem IsWkpOn.smul {U : WkpAmbientOn n k p Ω F}
    (hU : IsWkpOn U) (c : ℝ) : IsWkpOn (c • U) := by
  intro a
  exact ((hU a).smul c).congr_ae
    (Lp.coeFn_smul c (U (baseIndex n k))).symm (Lp.coeFn_smul c (U a)).symm

/-- The weak-derivative graph as a real submodule of the finite `Lp` product. -/
def wkpSubmoduleOn (n k : ℕ) (p : ℝ≥0∞) (Ω : Opens ℝ^n)
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] :
    Submodule ℝ (WkpAmbientOn n k p Ω F) where
  carrier := {U | IsWkpOn U}
  zero_mem' := isWkpOn_zero
  add_mem' := IsWkpOn.add
  smul_mem' := fun c _ hU ↦ hU.smul c

/-- Banach-valued `W^{k,p}(Ω)`, with the norm inherited from its derivative coordinates. -/
abbrev WkpSpaceOn (n k : ℕ) (p : ℝ≥0∞) (Ω : Opens ℝ^n)
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] :=
  wkpSubmoduleOn n k p Ω F

/-- Realize a compatible family of `Lp` representatives as a Sobolev bundle. -/
def ofWeakDerivatives (d : DerivIndex n k → ℝ^n → F)
    (hmem : ∀ a, MemLp (d a) p (domainMeasure n Ω))
    (hweak : ∀ a, HasWeakDerivativeOn Ω a.toList (d (baseIndex n k)) (d a)) :
    WkpSpaceOn n k p Ω F :=
  ⟨WithLp.toLp p (fun a ↦ (hmem a).toLp (d a)), fun a ↦
    (hweak a).congr_ae (hmem (baseIndex n k)).coeFn_toLp.symm (hmem a).coeFn_toLp.symm⟩

/-- The reconstructed bundle has the supplied derivative representatives almost everywhere. -/
theorem ofWeakDerivatives_apply_ae (d : DerivIndex n k → ℝ^n → F)
    (hmem : ∀ a, MemLp (d a) p (domainMeasure n Ω))
    (hweak : ∀ a, HasWeakDerivativeOn Ω a.toList (d (baseIndex n k)) (d a))
    (a : DerivIndex n k) :
    ((ofWeakDerivatives d hmem hweak).val a : ℝ^n → F) =ᵐ[domainMeasure n Ω] d a :=
  (hmem a).coeFn_toLp

/-- On the open domain, agreement of base representatives determines the whole bundle. -/
theorem WkpSpaceOn.ext_of_base_ae {U V : WkpSpaceOn n k p Ω F}
    (h : (U.val (baseIndex n k) : ℝ^n → F) =ᵐ[domainMeasure n Ω]
      (V.val (baseIndex n k) : ℝ^n → F)) : U = V := by
  apply Subtype.ext
  apply PiLp.ext
  intro a
  exact Lp.ext (((U.property a).congr_ae h Filter.EventuallyEq.rfl).ae_eq (V.property a))

variable [Fact (1 ≤ p)]

/-- A derivative coordinate is a continuous linear map out of the Sobolev graph. -/
def coordinateCLM (a : DerivIndex n k) :
    WkpSpaceOn n k p Ω F →L[ℝ] Lp F p (domainMeasure n Ω) :=
  (PiLp.proj p (fun _ : DerivIndex n k ↦ Lp F p (domainMeasure n Ω)) a).comp
    (wkpSubmoduleOn n k p Ω F).subtypeL

/-- The coordinate map returns the original `Lp` derivative coordinate. -/
@[simp] theorem coordinateCLM_apply (a : DerivIndex n k) (U : WkpSpaceOn n k p Ω F) :
    coordinateCLM a U = U.val a :=
  rfl

/-- Every derivative coordinate is bounded by the Sobolev graph norm. -/
theorem norm_coordinate_le (a : DerivIndex n k) (U : WkpSpaceOn n k p Ω F) :
    ‖coordinateCLM a U‖ ≤ ‖U‖ :=
  PiLp.norm_apply_le U.val a

/-- The base function determines the Sobolev graph element. -/
theorem baseCoordinateCLM_injective :
    Function.Injective (coordinateCLM (F := F) (p := p) (Ω := Ω) (baseIndex n k)) := by
  intro U V h
  apply WkpSpaceOn.ext_of_base_ae
  exact Filter.EventuallyEq.of_eq
    (congrArg (fun u : Lp F p (domainMeasure n Ω) ↦ (u : ℝ^n → F)) h)

end SobolevSpace.VectorValued
