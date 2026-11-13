/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Gelfand.Triple
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Finite Hilbert products of Gelfand triples

Coordinatewise dense injections give a dense injection between the finite Hilbert products.
Compactness follows by writing the product inclusion as the finite sum of its coordinate
injections. The construction also includes the empty product.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.Evolution.GelfandTriple

variable {ι : Type*} [Fintype ι]
variable {V H : ι → Type*}
variable [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace ℝ (V i)]
variable [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]

/-- Coordinatewise inclusion of a finite family of real Gelfand triples, with Hilbert norms. -/
def finiteProduct (T : ∀ i, GelfandTriple (V := V i) (H := H i)) :
    GelfandTriple (V := PiLp 2 V) (H := PiLp 2 H) where
  inclusion :=
    (PiLp.continuousLinearEquiv 2 ℝ H).symm.toContinuousLinearMap.comp
      ((ContinuousLinearMap.piMap fun i ↦ (T i).inclusion).comp
        (PiLp.continuousLinearEquiv 2 ℝ V).toContinuousLinearMap)
  injective := by
    intro v w h
    apply PiLp.ext
    intro i
    exact (T i).injective (congrArg (fun z : PiLp 2 H ↦ z i) h)
  denseRange := by
    exact (PiLp.continuousLinearEquiv 2 ℝ H).symm.surjective.denseRange.comp
      ((DenseRange.piMap fun i ↦ (T i).denseRange).comp
        (PiLp.continuousLinearEquiv 2 ℝ V).surjective.denseRange
        (ContinuousLinearMap.piMap fun i ↦ (T i).inclusion).continuous)
      (PiLp.continuousLinearEquiv 2 ℝ H).symm.continuous

/-- The product inclusion acts componentwise. -/
@[simp]
theorem finiteProduct_inclusion_apply
    (T : ∀ i, GelfandTriple (V := V i) (H := H i)) (v : PiLp 2 V) (i : ι) :
    (finiteProduct T).inclusion v i = (T i).inclusion (v i) :=
  rfl

/-- A finite Hilbert product of compact Gelfand inclusions is compact. -/
theorem finiteProduct_inclusion_isCompactOperator
    (T : ∀ i, GelfandTriple (V := V i) (H := H i))
    (hcompact : ∀ i, IsCompactOperator (T i).inclusion) :
    IsCompactOperator (finiteProduct T).inclusion := by
  classical
  have hsum : (ContinuousLinearMap.piMap fun i ↦ (T i).inclusion) =
      ∑ i, (ContinuousLinearMap.single ℝ H i).comp
        ((T i).inclusion.comp (ContinuousLinearMap.proj i)) := by
    ext v i
    simp [ContinuousLinearMap.piMap]
  have hplain : IsCompactOperator (ContinuousLinearMap.piMap fun i ↦ (T i).inclusion) := by
    change (ContinuousLinearMap.piMap fun i ↦ (T i).inclusion) ∈
      compactOperator (RingHom.id ℝ) (∀ i, V i) (∀ i, H i)
    rw [hsum]
    apply Submodule.sum_mem
    intro i _
    exact ((hcompact i).comp_clm (ContinuousLinearMap.proj i)).clm_comp
      (ContinuousLinearMap.single ℝ H i)
  exact (hplain.comp_clm (PiLp.continuousLinearEquiv 2 ℝ V).toContinuousLinearMap).clm_comp
    (PiLp.continuousLinearEquiv 2 ℝ H).symm.toContinuousLinearMap

end PDE.Analysis.Evolution.GelfandTriple
