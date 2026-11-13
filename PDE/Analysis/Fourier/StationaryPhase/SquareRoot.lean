/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Analytic square roots near the identity

The derivative of squaring at the identity is twice the identity, including in a
noncommutative Banach algebra. The inverse function theorem therefore constructs
an analytic local square root. This provides the matrix factorization used in
quadratic coordinates near a nondegenerate critical point.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology ContDiff

namespace PDE.Analysis.StationaryPhase

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- Squaring has an analytic local inverse at the identity of a real Banach algebra. -/
theorem exists_contDiffAt_square_root :
    ∃ r : A → A, r 1 = 1 ∧ ContDiffAt ℝ ω r 1 ∧
      (∀ᶠ y in 𝓝 (1 : A), r y * r y = y) ∧
      (∀ᶠ x in 𝓝 (1 : A), r (x * x) = x) := by
  let d : A ≃L[ℝ] A :=
    ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := A)
      (Units.mk0 (2 : ℝ) (by norm_num))
  have hf : ContDiffAt ℝ ω (fun x : A ↦ x * x) 1 :=
    (contDiff_id.mul contDiff_id).contDiffAt
  have hd : HasFDerivAt (fun x : A ↦ x * x) (d : A →L[ℝ] A) 1 := by
    apply ((hasFDerivAt_id (𝕜 := ℝ) (1 : A)).mul'
      (hasFDerivAt_id (1 : A))).congr_fderiv
    ext x
    simp [d, two_smul]
  let r := hf.localInverse hd (by simp)
  have hs := hf.hasStrictFDerivAt' hd (by simp)
  refine ⟨r, ?_, ?_, ?_, ?_⟩
  · simpa [r] using hf.localInverse_apply_image hd (by simp)
  · simpa [r] using hf.to_localInverse hd (by simp)
  · simpa [r, ContDiffAt.localInverse] using hs.eventually_right_inverse
  · simpa [r, ContDiffAt.localInverse] using hs.eventually_left_inverse

/-- A continuous operation fixing the identity and preserving squares commutes
locally with the constructed square root. In particular this applies to an
adjoint conjugated by an invertible symmetric operator. -/
theorem exists_contDiffAt_square_root_commuting
    {J : A → A} (hJ : ContinuousAt J 1) (hJone : J 1 = 1)
    (hJsq : ∀ x, J (x * x) = J x * J x) :
    ∃ r : A → A, r 1 = 1 ∧ ContDiffAt ℝ ω r 1 ∧
      (∀ᶠ y in 𝓝 (1 : A), r y * r y = y) ∧
      (∀ᶠ y in 𝓝 (1 : A), r (J y) = J (r y)) := by
  obtain ⟨r, hrone, hr, hrsq, hrl⟩ := exists_contDiffAt_square_root (A := A)
  refine ⟨r, hrone, hr, hrsq, ?_⟩
  have ht : Tendsto (fun y ↦ J (r y)) (𝓝 (1 : A)) (𝓝 1) := by
    have ht := hJ.tendsto.comp (show Tendsto r (𝓝 (1 : A)) (𝓝 1) by
      simpa [hrone] using hr.continuousAt.tendsto)
    simpa only [Function.comp_def, hJone] using ht
  filter_upwards [hrsq, ht.eventually hrl] with y hy hjy
  calc
    r (J y) = r (J (r y * r y)) := congrArg (fun z ↦ r (J z)) hy.symm
    _ = r (J (r y) * J (r y)) := congrArg r (hJsq (r y))
    _ = J (r y) := hjy

end PDE.Analysis.StationaryPhase
