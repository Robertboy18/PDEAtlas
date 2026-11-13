/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Notation

/-!
# Scalar specialization of the Banach-valued Sobolev graph

At real codomain the ambient `PiLp` space is definitionally the scalar ambient space.
The weak constraints agree by the scalar specialization theorem, so the two graph
submodules are equal. The resulting linear isometry keeps every `Lp` coordinate unchanged,
including the norm convention at infinity.
-/

@[expose] public noncomputable section

open TopologicalSpace
open scoped ENNReal Sobolev

namespace SobolevSpace.VectorValued

variable {n k : ℕ} {p : ℝ≥0∞} {Ω : Opens ℝ^n}

/-- At real codomain the constraints are precisely the scalar constraints. -/
theorem isWkpOn_real_iff (U : WkpAmbientOn n k p Ω ℝ) :
    IsWkpOn U ↔ GraphSpace.IsWkpOn U := by
  apply forall_congr'
  intro a
  exact hasWeakDerivativeOn_real_iff

/-- Scalar specialization gives the same submodule, not merely equivalent normed spaces. -/
theorem wkpSubmoduleOn_real_eq :
    wkpSubmoduleOn n k p Ω ℝ = GraphSpace.wkpSubmoduleOn n k p (Ω : Set ℝ^n) := by
  ext U
  exact isWkpOn_real_iff U

variable [Fact (1 ≤ p)]

/-- The identity on derivative coordinates identifies the real specialization isometrically
with the scalar Sobolev graph. -/
def scalarEquiv :
    W^{k,p}(Ω; ℝ) ≃ₗᵢ[ℝ] W^{k,p}(Ω) where
  toFun U := ⟨U.val, (isWkpOn_real_iff U.val).mp U.property⟩
  invFun U := ⟨U.val, (isWkpOn_real_iff U.val).mpr U.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

/-- Scalar specialization preserves every derivative coordinate in the `Lp` quotient. -/
@[simp] theorem scalarEquiv_coordinate (U : W^{k,p}(Ω; ℝ))
    (a : GraphSpace.DerivIndex n k) : (scalarEquiv U).val a = U.val a :=
  rfl

/-- The inverse scalar identification also preserves every derivative coordinate. -/
@[simp] theorem scalarEquiv_symm_coordinate
    (U : W^{k,p}(Ω)) (a : GraphSpace.DerivIndex n k) :
    (scalarEquiv.symm U).val a = U.val a :=
  rfl

end SobolevSpace.VectorValued
