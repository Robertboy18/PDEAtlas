/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Real and complex Euclidean matrix actions

Coordinatewise inclusion and real part are continuous real-linear maps. They
intertwine a real matrix action with its entrywise complexification.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace EuclideanSpace

variable (ι : Type*)

/-- Include a real Euclidean vector coordinatewise into the complex space. -/
def ofRealCLM : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℂ ι :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ ℂ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i ↦ Complex.ofRealCLM.comp (EuclideanSpace.proj i))

/-- The real inclusion acts on the coordinates. -/
@[simp]
theorem ofRealCLM_apply (v : EuclideanSpace ℝ ι) (i : ι) :
    ofRealCLM ι v i = (v i : ℂ) := rfl

/-- Take the real part of each coordinate as a continuous real-linear map. -/
def realPartCLM : EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℝ ι :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i ↦
      Complex.reCLM.comp ((EuclideanSpace.proj i).restrictScalars ℝ))

/-- The real-part map acts on the coordinates. -/
@[simp]
theorem realPartCLM_apply (v : EuclideanSpace ℂ ι) (i : ι) :
    realPartCLM ι v i = (v i).re := rfl

/-- Taking real parts recovers an included real vector. -/
@[simp]
theorem realPartCLM_ofRealCLM (v : EuclideanSpace ℝ ι) :
    realPartCLM ι (ofRealCLM ι v) = v := by ext i; simp

variable {ι} [Fintype ι] [DecidableEq ι]

/-- Including real vectors commutes with a real matrix action. -/
theorem ofRealCLM_toEuclideanCLM (A : Matrix ι ι ℝ) (v : EuclideanSpace ℝ ι) :
    ofRealCLM ι (Matrix.toEuclideanCLM (𝕜 := ℝ) A v) =
      Matrix.toEuclideanCLM (𝕜 := ℂ) (A.map Complex.ofReal) (ofRealCLM ι v) := by
  ext i
  change ((∑ j, A i j * v j : ℝ) : ℂ) = ∑ j, (A i j : ℂ) * (v j : ℂ)
  simp

/-- Taking real parts commutes with a real matrix action. -/
theorem realPartCLM_toEuclideanCLM (A : Matrix ι ι ℝ) (v : EuclideanSpace ℂ ι) :
    realPartCLM ι (Matrix.toEuclideanCLM (𝕜 := ℂ) (A.map Complex.ofReal) v) =
      Matrix.toEuclideanCLM (𝕜 := ℝ) A (realPartCLM ι v) := by
  ext i
  change (∑ j, (A i j : ℂ) * v j).re = ∑ j, A i j * (v j).re
  simp

end EuclideanSpace
