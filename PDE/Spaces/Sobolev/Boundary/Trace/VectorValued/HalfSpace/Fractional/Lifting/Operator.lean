/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.VectorValued.HalfSpace.Fractional.Lifting.Sobolev
public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.Fractional.Lifting.Linearity

/-!
# A bounded lifting of fractional boundary data

Cutoff mollification extends data of order `1 - 1 / p` to the upper half-space.
The derivative estimates place this formula in `W¹ᵖ`. Uniqueness of weak
derivatives transfers its linearity to Sobolev classes, and the coordinate
bounds make the resulting linear map continuous.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal Sobolev

namespace SobolevSpace.VectorValued.Trace.HalfSpace

open Approximation Fractional GraphSpace SobolevSpace.Trace.HalfSpace

variable {n : ℕ} {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

private theorem extension_add (μ : Mollifier n) (hp : 1 < p)
    (g h : GagliardoSpace n (1 - 1 / p) univ (p := ENNReal.ofReal p) (F := F)) :
    mollifiedExtensionSobolev μ hp (g + h) =
      mollifiedExtensionSobolev μ hp g + mollifiedExtensionSobolev μ hp h := by
  have hboundary :
      (GagliardoSpace.toLp n (1 - 1 / p) univ (g + h) : ℝ^n → F) =ᵐ[volume]
        (GagliardoSpace.toLp n (1 - 1 / p) univ g : ℝ^n → F) +
          (GagliardoSpace.toLp n (1 - 1 / p) univ h : ℝ^n → F) := by
    simpa only [map_add, Measure.restrict_univ] using
      Lp.coeFn_add (GagliardoSpace.toLp n (1 - 1 / p) univ g)
        (GagliardoSpace.toLp n (1 - 1 / p) univ h)
  have hlocal (f : GagliardoSpace n (1 - 1 / p) univ (p := ENNReal.ofReal p) (F := F)) :
      LocallyIntegrable (GagliardoSpace.toLp n (1 - 1 / p) univ f) volume := by
    simpa only [Measure.restrict_univ] using
      (Lp.memLp (GagliardoSpace.toLp n (1 - 1 / p) univ f)).locallyIntegrable
        (Fact.out : 1 ≤ ENNReal.ofReal p)
  have hraw := (mollifiedExtension_congr_ae μ hboundary).trans
    (mollifiedExtension_add μ (hlocal g) (hlocal h))
  apply baseCoordinateCLM_injective
  rw [map_add]
  apply Lp.ext
  filter_upwards [mollifiedExtensionSobolev_base_ae μ hp (g + h),
    mollifiedExtensionSobolev_base_ae μ hp g, mollifiedExtensionSobolev_base_ae μ hp h,
    Lp.coeFn_add (coordinateCLM (baseIndex (n + 1) 1) (mollifiedExtensionSobolev μ hp g))
      (coordinateCLM (baseIndex (n + 1) 1) (mollifiedExtensionSobolev μ hp h))]
    with z hsum hg hh hout
  exact hsum.trans ((congrFun hraw z).trans
    ((congrArg₂ (· + ·) hg.symm hh.symm).trans hout.symm))

private theorem extension_smul (μ : Mollifier n) (hp : 1 < p)
    (c : ℝ) (g : GagliardoSpace n (1 - 1 / p) univ (p := ENNReal.ofReal p) (F := F)) :
    mollifiedExtensionSobolev μ hp (c • g) = c • mollifiedExtensionSobolev μ hp g := by
  have hboundary :
      (GagliardoSpace.toLp n (1 - 1 / p) univ (c • g) : ℝ^n → F) =ᵐ[volume]
        c • (GagliardoSpace.toLp n (1 - 1 / p) univ g : ℝ^n → F) := by
    simpa only [map_smul, Measure.restrict_univ] using
      Lp.coeFn_smul c (GagliardoSpace.toLp n (1 - 1 / p) univ g)
  have hraw := (mollifiedExtension_congr_ae μ hboundary).trans
    (mollifiedExtension_smul μ c (GagliardoSpace.toLp n (1 - 1 / p) univ g))
  apply baseCoordinateCLM_injective
  rw [map_smul]
  apply Lp.ext
  filter_upwards [mollifiedExtensionSobolev_base_ae μ hp (c • g),
    mollifiedExtensionSobolev_base_ae μ hp g,
    Lp.coeFn_smul c (coordinateCLM (baseIndex (n + 1) 1) (mollifiedExtensionSobolev μ hp g))]
    with z hsmul hg hout
  exact hsmul.trans ((congrFun hraw z).trans ((congrArg (c • ·) hg.symm).trans hout.symm))

/-- The cutoff mollified extension as a bounded linear map into `W¹ᵖ`.
The boundary space has intrinsic fractional order `1 - 1 / p`. -/
def mollifiedLifting (μ : Mollifier n) (hp : 1 < p) :
    GagliardoSpace n (1 - 1 / p) univ (p := ENNReal.ofReal p) (F := F) →L[ℝ]
      W^{1,ENNReal.ofReal p}(⟨ℝ^(n + 1)₊, HalfSpace.isOpen_upper (n + 1)⟩; F) :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := mollifiedExtensionSobolev μ hp
      map_add' := by exact extension_add μ hp
      map_smul' := by exact extension_smul μ hp }
    (by
      obtain ⟨C, _, hC⟩ := exists_pos_norm_mollifiedExtensionSobolev_bound (F := F) μ hp
      exact ⟨C, hC⟩)

/-- The bounded lifting retains the cutoff and convolution formula. -/
theorem mollifiedLifting_base_ae (μ : Mollifier n) (hp : 1 < p)
    (g : GagliardoSpace n (1 - 1 / p) univ (p := ENNReal.ofReal p) (F := F)) :
    (coordinateCLM (baseIndex (n + 1) 1) (mollifiedLifting μ hp g) : ℝ^(n + 1) → F)
      =ᵐ[volume.restrict ℝ^(n + 1)₊]
        mollifiedExtension μ (GagliardoSpace.toLp n (1 - 1 / p) univ g) :=
  mollifiedExtensionSobolev_base_ae μ hp g

end SobolevSpace.VectorValued.Trace.HalfSpace
