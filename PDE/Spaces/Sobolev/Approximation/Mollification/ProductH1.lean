/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.H1Operator
public import PDE.Spaces.Sobolev.Variational.Spaces.WholeSpaceHilbert

/-!
# Componentwise H¹ mollification

The scalar map from L² into H¹ lifts to any finite component product. This
keeps the Sobolev coordinates available when mollifying vector-valued
weak equations. The operator bound may depend on the positive scale.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal Sobolev

namespace SobolevSpace.Approximation

open GraphSpace

open scoped SobolevSpace.WholeSpaceHilbert

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- Apply the scalar L²-to-H¹ mollifier to each component of a finite L² product. -/
def mollifierProductH1CLM (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) :
    PiLp 2 (fun _ : ι ↦ DerivLp n 2 univ) →L[ℝ]
      PiLp 2 (fun _ : ι ↦ W^{1,2}(ℝ^n)) :=
  (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : ι ↦ W^{1,2}(ℝ^n))).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun p ↦
        (mollifierH1CLM μ hε).comp
          (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι ↦ DerivLp n 2 univ) p))

omit [Fintype ι] in
/-- Each component is the scalar mollifier in the H¹ graph space. -/
@[simp]
theorem mollifierProductH1CLM_apply (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    (u : PiLp 2 (fun _ : ι ↦ DerivLp n 2 univ)) (p : ι) :
    mollifierProductH1CLM μ hε u p = mollifierH1CLM μ hε (u p) := rfl

end SobolevSpace.Approximation
