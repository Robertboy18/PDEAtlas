/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.LerayProjection
public import PDE.Analysis.MeasureTheory.Lp.Composition.Dilation

/-!
# Dilation invariance of the whole-space Leray projection

Scalar dilation maps compact smooth gradients to scalar multiples of compact
smooth gradients. Its exact L² norm scales every inner product by the same
factor. Both the solenoidal subspace and its orthogonal complement are therefore
invariant, so the actual Leray projection commutes with spatial dilation.
-/

@[expose] public noncomputable section

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Sobolev

namespace IncompressibleFlow

variable {n : ℕ}

local notation "μ" => domainMeasure n Set.univ

/-- Composition with a nonzero scalar dilation on the physical vector L² space. -/
def l2Dilation (a : ℝ) (ha : a ≠ 0) : WholeSpaceL2 n →L[ℝ] WholeSpaceL2 n :=
  Lp.compSMul μ 2 a ha

/-- Dilation agrees with composition of representatives almost everywhere. -/
theorem l2Dilation_ae (a : ℝ) (ha : a ≠ 0) (u : WholeSpaceL2 n) :
    l2Dilation a ha u =ᵐ[μ] fun x ↦ u (a • x) :=
  Lp.coeFn_compSMul μ 2 a ha u

/-- The `L²` class of a scaled dilate `x ↦ c f(a x)` is the scaled `L²` dilation of the class
of `f`. -/
theorem toLp_smul_comp_smul {f : ℝ^n → ℝ^n} (hf : MemLp f 2 (domainMeasure n Set.univ))
    (c : ℝ) {a : ℝ} (ha : a ≠ 0)
    (hg : MemLp (fun x ↦ c • f (a • x)) 2 (domainMeasure n Set.univ)) :
    hg.toLp _ = c • l2Dilation a ha (hf.toLp f) := by
  apply Lp.ext
  have h₁ := hg.coeFn_toLp
  have h₂ := l2Dilation_ae a ha (hf.toLp f)
  have h₃ := Lp.coeFn_smul c (l2Dilation a ha (hf.toLp f))
  have h₄ := hf.coeFn_toLp
  simp only [domainMeasure, Measure.restrict_univ] at h₁ h₂ h₃ h₄ ⊢
  have h₅ := (Measure.quasiMeasurePreserving_smul (volume : Measure (ℝ^n)) ha).ae_eq_comp h₄
  filter_upwards [h₁, h₂, h₃, h₅] with x hx₁ hx₂ hx₃ hx₅
  rw [hx₁, hx₃, Pi.smul_apply, hx₂]
  simp only [Function.comp_apply] at hx₅
  rw [hx₅]

/-- The physical norm includes the full spatial volume factor. -/
theorem norm_l2Dilation (a : ℝ) (ha : a ≠ 0) (u : WholeSpaceL2 n) :
    ‖l2Dilation a ha u‖ = |(a ^ n)⁻¹| ^ (1 / (2 : ℝ≥0∞)).toReal * ‖u‖ := by
  simpa only [l2Dilation, finrank_euclideanSpace_fin] using Lp.norm_compSMul μ 2 a ha u

/-- Dilating both entries scales the real Hilbert pairing by the squared norm factor. -/
theorem inner_l2Dilation_l2Dilation (a : ℝ) (ha : a ≠ 0) (u v : WholeSpaceL2 n) :
    inner ℝ (l2Dilation a ha u) (l2Dilation a ha v) =
      (|(a ^ n)⁻¹| ^ (1 / (2 : ℝ≥0∞)).toReal) ^ 2 * inner ℝ u v := by
  rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
    ← map_add, norm_l2Dilation, norm_l2Dilation, norm_l2Dilation,
    real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two]
  ring

/-- Reciprocal dilation moves from one side of the physical pairing to the other. -/
theorem inner_l2Dilation_left (a : ℝ) (ha : a ≠ 0) (u v : WholeSpaceL2 n) :
    inner ℝ (l2Dilation a ha u) v =
      (|(a ^ n)⁻¹| ^ (1 / (2 : ℝ≥0∞)).toReal) ^ 2 *
        inner ℝ u (l2Dilation a⁻¹ (inv_ne_zero ha) v) := by
  have hinv : l2Dilation a ha (l2Dilation a⁻¹ (inv_ne_zero ha) v) = v := by
    change Lp.compSMul μ 2 a ha (Lp.compSMul μ 2 a⁻¹ (inv_ne_zero ha) v) = v
    rw [← Lp.compSMul_mul]
    simp only [mul_inv_cancel₀ ha, Lp.compSMul_one]
  calc
    _ = inner ℝ (l2Dilation a ha u)
        (l2Dilation a ha (l2Dilation a⁻¹ (inv_ne_zero ha) v)) := by rw [hinv]
    _ = _ := inner_l2Dilation_l2Dilation a ha u _

/-- Pull back a compact smooth scalar test by an invertible scalar dilation. -/
def dilatedTest (a : ℝ) (ha : a ≠ 0) (φ : TestFunctionOn n Set.univ) :
    TestFunctionOn n Set.univ :=
  ⟨TestFunction.mk (fun x ↦ φ.1.toFun (a • x))
    (φ.1.contDiff.comp (contDiff_id.const_smul a))
    (φ.1.hasCompactSupport.comp_homeomorph
      (ContinuousLinearEquiv.smulLeft (Units.mk0 a ha) : ℝ^n ≃L[ℝ] ℝ^n).toHomeomorph)
    (Set.subset_univ _), Set.subset_univ _⟩

/-- The classical chain rule identifies the dilated test gradient in the L² pivot. -/
theorem l2Dilation_testGradient (a : ℝ) (ha : a ≠ 0) (φ : TestFunctionOn n Set.univ) :
    l2Dilation a ha (l2TestGradient φ) = a⁻¹ • l2TestGradient (dilatedTest a ha φ) := by
  apply Lp.ext
  have hs := (Measure.quasiMeasurePreserving_smul μ ha).ae (l2TestGradient_apply_ae φ)
  filter_upwards [l2Dilation_ae a ha (l2TestGradient φ),
    Lp.coeFn_smul a⁻¹ (l2TestGradient (dilatedTest a ha φ)),
    l2TestGradient_apply_ae (dilatedTest a ha φ), hs] with x hd hsm hg hs
  apply PiLp.ext
  intro i
  rw [hd, hsm, Pi.smul_apply, PiLp.smul_apply, hg i, hs i]
  change fderiv ℝ φ.1.toFun (a • x) (EuclideanSpace.single i (1 : ℝ)) =
    a⁻¹ * fderiv ℝ (fun y ↦ φ.1.toFun (a • y)) x (EuclideanSpace.single i (1 : ℝ))
  have hφ : DifferentiableAt ℝ φ.1.toFun (a • x) :=
    (φ.1.contDiff.differentiable (by simp)).differentiableAt
  have hchain : HasFDerivAt (fun y ↦ φ.1.toFun (a • y))
      ((fderiv ℝ φ.1.toFun (a • x)).comp (a • ContinuousLinearMap.id ℝ (ℝ^n))) x :=
    hφ.hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul a)
  rw [hchain.fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ ha,
    one_mul]

/-- Nonzero spatial dilation preserves distributional divergence freedom. -/
theorem l2Dilation_mem_solenoidal (a : ℝ) (ha : a ≠ 0) {u : WholeSpaceL2 n}
    (hu : u ∈ l2Solenoidal n) : l2Dilation a ha u ∈ l2Solenoidal n := by
  apply (mem_l2Solenoidal_iff_inner _).mpr
  intro φ
  rw [inner_l2Dilation_left, l2Dilation_testGradient, inner_smul_right,
    (mem_l2Solenoidal_iff_inner _).mp hu, mul_zero, mul_zero]

/-- Dilation also preserves the orthogonal complement of solenoidal fields. -/
theorem l2Dilation_mem_solenoidal_orthogonal (a : ℝ) (ha : a ≠ 0) {u : WholeSpaceL2 n}
    (hu : u ∈ (l2Solenoidal n).orthogonal) :
    l2Dilation a ha u ∈ (l2Solenoidal n).orthogonal := by
  apply (Submodule.mem_orthogonal' _ _).mpr
  intro v hv
  rw [inner_l2Dilation_left,
    (Submodule.mem_orthogonal' _ _).mp hu _
      (l2Dilation_mem_solenoidal a⁻¹ (inv_ne_zero ha) hv), mul_zero]

/-- The actual whole-space Leray projection commutes with nonzero spatial dilation. -/
theorem lerayProjection_l2Dilation (a : ℝ) (ha : a ≠ 0) (u : WholeSpaceL2 n) :
    lerayProjection n (l2Dilation a ha u) = l2Dilation a ha (lerayProjection n u) := by
  apply (l2Solenoidal n).eq_starProjection_of_mem_orthogonal
    (l2Dilation_mem_solenoidal a ha (lerayProjection_mem n u))
  rw [← map_sub]
  exact l2Dilation_mem_solenoidal_orthogonal a ha
    ((l2Solenoidal n).sub_starProjection_mem_orthogonal u)

end IncompressibleFlow
