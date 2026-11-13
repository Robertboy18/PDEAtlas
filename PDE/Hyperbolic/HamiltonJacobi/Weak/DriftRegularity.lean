/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Weak.DriftConvergence

/-!
# Smoothness of the mollified drift

The spatial gradient of a spacetime mollification is smooth jointly in space
and time. A `C²` Hamiltonian therefore gives a jointly `C¹` regularized drift,
as needed for the classical divergence and moving-ball formulas.
-/

open scoped Gradient

@[expose] public section

noncomputable section

namespace HamiltonJacobi.Weak

open MeasureTheory
open scoped ContDiff Convolution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

/-- Taking the spatial gradient loses one order of joint spacetime regularity. -/
theorem contDiff_gradient_spaceSlice {n : ℕ∞} {f : E × ℝ → ℝ} (hf : ContDiff ℝ ((n : ℕ∞ω) + 1) f) :
    ContDiff ℝ n (fun z : E × ℝ ↦ ∇ (fun x ↦ f (x, z.2)) z.1) := by
  let R := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have heq : (fun z : E × ℝ ↦ ∇ (fun x ↦ f (x, z.2)) z.1) =
      (fun z ↦ R ((fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ E ℝ))) := by
    funext z
    exact gradient_spaceSlice_eq (hf.differentiable (by simp) z)
  rw [heq]
  exact R.contDiff.comp ((hf.fderiv_right le_rfl).clm_comp contDiff_const)

variable [MeasurableSpace E] [BorelSpace E]
    {μ : Measure (E × ℝ)} [μ.IsAddHaarMeasure]

/-- The drift formed from the two mollified spatial gradients is `C¹`
jointly in space and time. -/
theorem contDiff_mollifiedDrift {H : E → ℝ} (hH : ContDiff ℝ 2 H) {u v : E × ℝ → ℝ} {Ku Kv : NNReal}
    (hu : LipschitzOnWith Ku u {z | 0 ≤ z.2}) (hv : LipschitzOnWith Kv v {z | 0 ≤ z.2})
    (φ : ContDiffBump (0 : E × ℝ)) :
    ContDiff ℝ 1 (mollifiedDrift (μ := μ) H φ u v) := by
  have hsmooth (f : E × ℝ → ℝ) (hf : Continuous f) : ContDiff ℝ 1 (fun z : E × ℝ ↦ ∇ (fun x ↦
        (φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) (x, z.2)) z.1) :=
    contDiff_gradient_spaceSlice (φ.hasCompactSupport_normed.contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) φ.contDiff_normed hf.locallyIntegrable)
  let p : E × ℝ → E := fun z ↦ ∇ (fun x ↦
    (φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] forwardExtension u) (x, z.2)) z.1
  let q : E × ℝ → E := fun z ↦ ∇ (fun x ↦
    (φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] forwardExtension v) (x, z.2)) z.1
  have hp : ContDiff ℝ 1 p :=
    hsmooth (forwardExtension u) (lipschitzWith_forwardExtension hu).continuous
  have hq : ContDiff ℝ 1 q :=
    hsmooth (forwardExtension v) (lipschitzWith_forwardExtension hv).continuous
  have hF : ContDiff ℝ 1 (fun zr : (E × ℝ) × ℝ ↦ ∇ H (zr.2 • p zr.1 + (1 - zr.2) • q zr.1)) :=
    (PDE.Analysis.contDiff_gradient (n := 1) hH).comp
    ((contDiff_snd.smul (hp.comp contDiff_fst)).add
      ((contDiff_const.sub contDiff_snd).smul (hq.comp contDiff_fst)))
  exact PDE.Analysis.contDiff_intervalIntegral hF 0 1

end HamiltonJacobi.Weak
