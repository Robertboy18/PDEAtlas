/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Compact pullbacks of Hilbert pairings

Pulling a Hilbert inner product back along a continuous linear map gives a
bilinear form. When the map is compact, the resulting dual-valued operator is
compact; this is the mass operator in the variational Fredholm reduction.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

/-- The mass operator induced by a Hilbert-space map `P : V → W`:
`u ↦ (v ↦ ⟪Pu, Pv⟫)`. -/
def innerPullbackOperator (P : V →L[ℝ] W) :
    V →L[ℝ] StrongDual ℝ V := by
  let Pstar : W →L[ℝ] V :=
    ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := V) (F := W) P
  let riesz : V →L[ℝ] StrongDual ℝ V :=
    (InnerProductSpace.toDual ℝ V).toContinuousLinearEquiv.toContinuousLinearMap
  exact riesz.comp (Pstar.comp P)

/-- The mass operator pairs `u` and `v` through their images: `(M u)(v) = ⟪P u, P v⟫`. This
follows from the defining identity `⟪P* w, v⟫ = ⟪w, P v⟫` of the Hilbert adjoint. -/
@[simp]
theorem innerPullbackOperator_apply (P : V →L[ℝ] W) (u v : V) :
    innerPullbackOperator P u v = ⟪P u, P v⟫_ℝ := by
  change ⟪P.adjoint (P u), v⟫_ℝ = ⟪P u, P v⟫_ℝ
  exact P.adjoint_inner_left v (P u)

/-- Pulling an inner product back along a compact operator produces a compact
operator into the dual space. -/
theorem isCompactOperator_innerPullbackOperator
    (P : V →L[ℝ] W) (hP : IsCompactOperator P) :
    IsCompactOperator (innerPullbackOperator P) := by
  let Pstar : W →L[ℝ] V :=
    ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := V) (F := W) P
  let riesz : V →L[ℝ] StrongDual ℝ V :=
    (InnerProductSpace.toDual ℝ V).toContinuousLinearEquiv.toContinuousLinearMap
  have hPstarP : IsCompactOperator (Pstar.comp P) := hP.clm_comp Pstar
  have hcompact : IsCompactOperator (riesz.comp (Pstar.comp P)) :=
    hPstarP.clm_comp riesz
  simpa [innerPullbackOperator, Pstar, riesz] using hcompact

end PDE.Analysis
