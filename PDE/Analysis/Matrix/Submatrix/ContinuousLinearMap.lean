/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Matrix.Normed

/-!
# Continuous linear selection of matrix entries

Selecting rows and columns is continuous and linear for the product topology.
For finite matrices this is the topology of the usual elementwise norm.
The selection maps may repeat indices; no injectivity is needed.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Elementwise

namespace Matrix

variable {𝕜 E l m n o : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Row and column selection, bundled as a continuous linear map. -/
def submatrixCLM (r : l → m) (c : o → n) : Matrix m n E →L[𝕜] Matrix l o E where
  toFun A := A.submatrix r c
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_id.matrix_submatrix r c

/-- The bundled selection evaluates to the usual matrix submatrix. -/
@[simp] theorem submatrixCLM_apply (r : l → m) (c : o → n) (A : Matrix m n E) :
    submatrixCLM (𝕜 := 𝕜) r c A = A.submatrix r c := rfl

end Matrix
