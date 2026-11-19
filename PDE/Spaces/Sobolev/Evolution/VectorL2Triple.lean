/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Evolution.WholeSpaceL2Triple
public import PDE.Analysis.Evolution.Gelfand.FiniteProduct
public import PDE.Spaces.Sobolev.GraphSpace.Operators.WholeSpaceVector
import PDE.Analysis.Normed.PiLp.Coordinatewise
import PDE.Spaces.Sobolev.GraphSpace.Topology.OrderDensity

/-!
# The weak Laplacian on a finite Hilbert product

The scalar negative gradient forms add over the components. Their sum agrees
with the vector L² Laplacian on H² data and is dissipative without restrictions
on the number of components. Lowering the Sobolev order acts componentwise and is
injective on open domains; on whole-space vector fields, forgetting the top order
keeps the physical field and does not increase the norm.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory PDE.Analysis.Evolution
open scoped ENNReal InnerProductSpace Sobolev Laplacian

variable {n m : ℕ} {Ω : Set (ℝ^n)}

/-- The canonical real normed-space structure on the finite Sobolev product. -/
local instance coordinateProductNormedSpace {k : ℕ} :
    NormedSpace ℝ (PiLp 2 (fun _ : Fin m ↦ W^{k,2}(Ω))) :=
  PiLp.normedSpace 2 ℝ (fun _ : Fin m ↦ W^{k,2}(Ω))

/-- Lower the Sobolev order in each component of a finite Hilbert product. -/
def vectorLowerOrderCLM {k l : ℕ} (hkl : k ≤ l) :
    PiLp 2 (fun _ : Fin m ↦ W^{l,2}(Ω)) →L[ℝ]
      PiLp 2 (fun _ : Fin m ↦ W^{k,2}(Ω)) :=
  ContinuousLinearMap.piLpMap (𝕜 := ℝ)
    (E := fun _ : Fin m ↦ W^{l,2}(Ω)) (F := fun _ : Fin m ↦ W^{k,2}(Ω))
    2 (fun _ ↦ lowerOrderCLM hkl)

/-- Order restriction acts componentwise. -/
@[simp]
theorem vectorLowerOrderCLM_apply {k l : ℕ} (hkl : k ≤ l)
    (U : PiLp 2 (fun _ : Fin m ↦ W^{l,2}(Ω))) (p : Fin m) :
    vectorLowerOrderCLM hkl U p = lowerOrderCLM hkl (U p) :=
  rfl

/-- Lowering the order of a finite product to the same order is the identity. -/
@[simp]
theorem vectorLowerOrderCLM_refl_apply {k : ℕ} (U : PiLp 2 (fun _ : Fin m ↦ W^{k,2}(Ω))) :
    vectorLowerOrderCLM le_rfl U = U :=
  PiLp.ext fun i ↦ lowerOrderCLM_refl_apply (U i)

/-- Lowering the order of a finite product in two stages is lowering it directly. -/
theorem vectorLowerOrderCLM_trans_apply {r k l : ℕ} (hrk : r ≤ k) (hkl : k ≤ l)
    (U : PiLp 2 (fun _ : Fin m ↦ W^{l,2}(Ω))) :
    vectorLowerOrderCLM hrk (vectorLowerOrderCLM hkl U) =
      vectorLowerOrderCLM (hrk.trans hkl) U :=
  PiLp.ext fun i ↦ lowerOrderCLM_trans_apply hrk hkl (U i)

/-- On an open domain, lowering the order of a finite product is injective. -/
theorem vectorLowerOrderCLM_injective {k l : ℕ} (hkl : k ≤ l) (hΩ : IsOpen Ω) :
    Function.Injective (vectorLowerOrderCLM (m := m) (Ω := Ω) hkl) := fun _ _ h ↦
  PiLp.ext fun i ↦ lowerOrderCLM_injective hkl hΩ (congrArg (fun W ↦ W i) h)

/-- Forgetting the top derivative order of a whole-space vector Sobolev field. -/
def vectorLower (n k : ℕ) : VectorH n (k + 1) →L[ℝ] VectorH n k :=
  vectorLowerOrderCLM (Ω := Set.univ) (m := n) (Nat.le_succ k)

/-- Forgetting the top order acts componentwise. -/
theorem vectorLower_apply {k : ℕ} (u : VectorH n (k + 1)) (j : Fin n) :
    vectorLower n k u j = lowerOrderCLM (Nat.le_succ k) (u j) :=
  rfl

/-- Forgetting derivatives keeps the physical field. -/
theorem l2SobolevRow_base_vectorLower {k : ℕ} (u : VectorH n (k + 1)) :
    l2SobolevRow (baseIndex n k) (vectorLower n k u) = l2SobolevRow (baseIndex n (k + 1)) u :=
  rfl

/-- Forgetting the top order of whole-space vector fields is injective. -/
theorem vectorLower_injective (n k : ℕ) : Function.Injective (vectorLower n k) :=
  vectorLowerOrderCLM_injective _ isOpen_univ

theorem norm_vectorLower_le {k : ℕ} (u : VectorH n (k + 1)) : ‖vectorLower n k u‖ ≤ ‖u‖ :=
  PiLp.norm_mono _ _ fun j ↦ norm_lowerOrderCLM_apply_le (Nat.le_succ k) (u j)

theorem norm_vectorLower_opNorm_le {k : ℕ} : ‖vectorLower n k‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u ↦ by
    simpa only [one_mul] using norm_vectorLower_le u

/-- The canonical H¹–L² Gelfand triple on a finite Hilbert product. -/
def vectorHOneLTwoGelfandTriple (hΩ : IsOpen Ω) :
    GelfandTriple (V := PiLp 2 (fun _ : Fin m ↦ W^{1,2}(Ω)))
      (H := PiLp 2 (fun _ : Fin m ↦ DerivLp n 2 Ω)) :=
  GelfandTriple.finiteProduct (fun _ : Fin m ↦ hOneLTwoGelfandTriple hΩ)

/-- The canonical pivot inclusion is the componentwise Sobolev base coordinate. -/
@[simp]
theorem vectorHOneLTwoGelfandTriple_inclusion_apply (hΩ : IsOpen Ω)
    (U : PiLp 2 (fun _ : Fin m ↦ W^{1,2}(Ω))) (p : Fin m) :
    (vectorHOneLTwoGelfandTriple hΩ).inclusion U p = wkpBaseCoordinateCLM (U p) :=
  rfl

/-- The sum of the component weak Laplacians on a finite H¹ Hilbert product. -/
def vectorWeakLaplacianCLM :
    PiLp 2 (fun _ : Fin m ↦ W^{1,2}(Ω)) →L[ℝ]
      StrongDual ℝ (PiLp 2 (fun _ : Fin m ↦ W^{1,2}(Ω))) :=
  ∑ p : Fin m, weakLaplacianCLM.bilinearComp
    (PiLp.proj 2 (fun _ : Fin m ↦ W^{1,2}(Ω)) p)
    (PiLp.proj 2 (fun _ : Fin m ↦ W^{1,2}(Ω)) p)

/-- The vector weak Laplacian is the sum of the scalar weak pairings. -/
theorem vectorWeakLaplacianCLM_apply
    (U V : PiLp 2 (fun _ : Fin m ↦ W^{1,2}(Ω))) :
    vectorWeakLaplacianCLM U V = ∑ p, weakLaplacianCLM (U p) (V p) := by
  simp [vectorWeakLaplacianCLM, sum_apply]

/-- The vector weak Laplacian is dissipative. -/
theorem vectorWeakLaplacianCLM_apply_self_nonpos
    (U : PiLp 2 (fun _ : Fin m ↦ W^{1,2}(Ω))) :
    vectorWeakLaplacianCLM U U ≤ 0 := by
  rw [vectorWeakLaplacianCLM_apply]
  exact Finset.sum_nonpos fun p _ ↦ weakLaplacianCLM_apply_self_nonpos (U p)

/-- On whole-space H² data the vector weak Laplacian is the dual image of
its actual componentwise L² Laplacian. -/
theorem vectorWeakLaplacianCLM_lowerOrder_univ
    (U : PiLp 2 (fun _ : Fin m ↦ W^{2,2}(ℝ^n))) :
    vectorWeakLaplacianCLM
      (ContinuousLinearMap.piLpMap 2 (fun _ : Fin m ↦
        lowerOrderCLM (by decide : 1 ≤ 2)) U) =
      (GelfandTriple.finiteProduct (fun _ : Fin m ↦
        hOneLTwoGelfandTriple (n := n) isOpen_univ)).pivotToDual
          (WithLp.toLp 2 (fun p ↦ Δ (U p))) := by
  ext V
  simp only [vectorWeakLaplacianCLM_apply, ContinuousLinearMap.piLpMap_apply,
    weakLaplacianCLM_lowerOrder_univ, GelfandTriple.pivotToDual_apply,
    PiLp.inner_apply, GelfandTriple.finiteProduct_inclusion_apply]

end SobolevSpace.GraphSpace
