/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Nonuniqueness.ProfileIncrement
public import PDE.Spaces.Sobolev.Calculus.Slicing.ClassicalDerivative
public import PDE.FDeriv.PartialDeriv.MemLp

/-!
# The equation of the profile increment

The increment `Ψ(a) = a Ũ(a ·) - Ũ` of the dilations of an unstable profile satisfies, in every
`Hᴺ` with `N ≥ 2`, the equation

`Ψ'(a) = 2 a⁻³ Π ((Ũ·∇)Ũ - ΔŨ + (Ũ·∇)Ψ + (Ψ·∇)Ũ + (Ψ·∇)Ψ - ΔΨ)`

(`UnstableProfile.dilatedScaling_eq`): the derivative `(Ũ + ξ·∇Ũ)(a ·)` is the dilation of
`2 Π ((Ũ·∇)Ũ - ΔŨ)`, and the nonlinear field `(X·∇)X - ΔX` of `X = a Ũ(a ·) = Ũ + Ψ(a)` is
`a³` times its dilation. The right side is a smooth function of `Ψ(a)` in `Hᴺ⁺²`, so the
increment is smooth in `a > 0` in every `Hᴺ` (`UnstableProfile.contDiffOn_profileIncrement`).
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Set Filter Topology SobolevSpace SobolevSpace.GraphSpace
open IncompressibleFlow HeatEquation.WholeSpace NavierStokes.SobolevConvection
open scoped NNReal ENNReal Sobolev

namespace NavierStokes.Nonuniqueness

set_option linter.missingDocs true

/-- A component of a partial derivative is the partial derivative of the component. -/
theorem partialDeriv_component {F : ℝ^3 → ℝ^3} {x : ℝ^3} (hF : DifferentiableAt ℝ F x)
    (i j : Fin 3) : PDE.partialDeriv i F x j = PDE.partialDeriv i (fun y ↦ F y j) x := by
  have h : HasFDerivAt (fun y ↦ (F y) j)
      ((EuclideanSpace.proj j : ℝ^3 →L[ℝ] ℝ).comp (fderiv ℝ F x)) x :=
    (EuclideanSpace.proj j : ℝ^3 →L[ℝ] ℝ).hasFDerivAt.comp x hF.hasFDerivAt
  unfold PDE.partialDeriv
  rw [h.fderiv]
  rfl

/-- A component of the Laplacian is the sum of the second derivative words of the component. -/
theorem laplacian_component {X : ℝ^3 → ℝ^3} (hX : ContDiff ℝ (⊤ : ℕ∞) X) (x : ℝ^3)
    (j : Fin 3) :
    PDE.laplacian X x j = ∑ i : Fin 3, iteratedPartialDeriv [i, i] (fun y ↦ X y j) x := by
  unfold PDE.laplacian
  rw [show (∑ i : Fin 3, PDE.partialDeriv i (fun y ↦ PDE.partialDeriv i X y) x) j =
      ∑ i : Fin 3, PDE.partialDeriv i (fun y ↦ PDE.partialDeriv i X y) x j from by
    simp only [Fin.sum_univ_three, PiLp.add_apply]]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hd : Differentiable ℝ (fun y ↦ PDE.partialDeriv i X y) :=
    (PDE.contDiff_top_partialDeriv hX).differentiable (by simp)
  rw [partialDeriv_component (hd x)]
  have hX1 : Differentiable ℝ X := hX.differentiable (by simp)
  have hcomp : (fun y ↦ PDE.partialDeriv i X y j) = fun y ↦ PDE.partialDeriv i (fun z ↦ X z j) y :=
    funext fun y ↦ partialDeriv_component (hX1 y) i j
  rw [hcomp]
  rfl

/-- The Laplacian is additive on smooth fields. -/
theorem laplacian_add_of_contDiff {X Y : ℝ^3 → ℝ^3} (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hY : ContDiff ℝ (⊤ : ℕ∞) Y) (x : ℝ^3) :
    PDE.laplacian (X + Y) x = PDE.laplacian X x + PDE.laplacian Y x := by
  unfold PDE.laplacian
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hX1 : Differentiable ℝ X := hX.differentiable (by simp)
  have hY1 : Differentiable ℝ Y := hY.differentiable (by simp)
  have h₁ : (fun y ↦ PDE.partialDeriv i (X + Y) y) =
      fun y ↦ PDE.partialDeriv i X y + PDE.partialDeriv i Y y :=
    funext fun y ↦ PDE.partialDeriv_add (hX1 y) (hY1 y)
  rw [h₁]
  exact PDE.partialDeriv_add ((PDE.contDiff_top_partialDeriv hX).differentiable (by simp) x)
    ((PDE.contDiff_top_partialDeriv hY).differentiable (by simp) x)

namespace UnstableProfile

variable (D : UnstableProfile)

/-- Pointwise form of the increment equation: with `ψ = a Ũ(a ·) - Ũ`,
`((Ũ·∇)Ũ - ΔŨ)(a x) = a⁻³ ((Ũ·∇)Ũ - ΔŨ + (Ũ·∇)ψ + (ψ·∇)Ũ + (ψ·∇)ψ - Δψ)(x)`. -/
theorem nonlinearField_smul_component {a : ℝ} (ha : a ≠ 0) (x : ℝ^3) (j : Fin 3) :
    nonlinearField D.U (a • x) j = (a⁻¹) ^ 3 * (nonlinearField D.U x j +
      ∑ i : Fin 3, (D.U x i * fderiv ℝ (dilateField a D.U - D.U) x (EuclideanSpace.single i 1) j +
        fderiv ℝ D.U x (EuclideanSpace.single i 1) j * (dilateField a D.U - D.U) x i) +
      ∑ i : Fin 3, (dilateField a D.U - D.U) x i *
        fderiv ℝ (dilateField a D.U - D.U) x (EuclideanSpace.single i 1) j -
      ∑ i : Fin 3, iteratedPartialDeriv [i, i] (fun y ↦ (dilateField a D.U - D.U) y j) x) := by
  set ψ := dilateField a D.U - D.U with hψ
  have hU := D.contDiff_U
  have hψc : ContDiff ℝ (⊤ : ℕ∞) ψ := (contDiff_dilateField a hU).sub hU
  have hsum : dilateField a D.U = D.U + ψ := by
    rw [hψ]
    abel
  have h := nonlinearField_dilateField hU a x
  have h' : nonlinearField D.U (a • x) = (a⁻¹) ^ 3 • nonlinearField (D.U + ψ) x := by
    rw [← hsum, h, smul_smul, ← mul_pow, inv_mul_cancel₀ ha, one_pow, one_smul]
  rw [h', PiLp.smul_apply, smul_eq_mul]
  congr 1
  have hd : fderiv ℝ (D.U + ψ) x = fderiv ℝ D.U x + fderiv ℝ ψ x :=
    fderiv_add ((hU.differentiable (by simp)) x) ((hψc.differentiable (by simp)) x)
  unfold nonlinearField
  rw [hd, laplacian_add_of_contDiff hU hψc, PiLp.sub_apply, PiLp.sub_apply, PiLp.add_apply,
    laplacian_component hψc, ContinuousLinearMap.apply_eq_sum_mul_apply_single,
    ContinuousLinearMap.apply_eq_sum_mul_apply_single (fderiv ℝ D.U x)]
  simp only [add_apply, Pi.add_apply, PiLp.add_apply, Fin.sum_univ_three]
  ring

/-- The right side of the increment equation: `Π ((Ũ·∇)Ũ - ΔŨ + (Ũ·∇)v + (v·∇)Ũ + (v·∇)v - Δw)`
for `v ∈ Hᴺ⁺¹`, `w ∈ Hᴺ⁺²`. -/
def incrementNonlinearity (N : ℕ) (hm : (3 : ℝ) < 2 * N) (v : VectorH 3 (N + 1))
    (w : VectorH 3 (N + 2)) : VectorH 3 N :=
  leraySobolev 3 N (D.profileNonlinearSobolev N +
    NavierStokes.SobolevConvection.profileConvection N (D.velocityWkTop (N + 1)) v +
    mixedConvection N hm (vectorLower 3 N v) v - vectorLaplacian 3 N w)

/-- The base representative of a component of a smooth vector field in vector `Hᴺ`. -/
theorem baseRepresentative_toLp_vectorWkpOfContDiff_ae {N : ℕ} {X : ℝ^3 → ℝ^3}
    (hX : ContDiff ℝ (⊤ : ℕ∞) X) (hmem : ∀ m ≤ N, MemLp (iteratedFDeriv ℝ m X) 2 volume)
    (j : Fin 3) :
    baseRepresentative ((WithLp.toLp 2 (vectorWkpOfContDiff X hX hmem) : VectorH 3 N) j)
      =ᵐ[volume] fun x ↦ X x j := by
  rw [PiLp.toLp_apply]
  exact baseRepresentative_vectorWkpOfContDiff X hX hmem j

/-- **The dilations of the nonlinear field** in vector `Hᴺ`:
`δₐ((Ũ·∇)Ũ - ΔŨ) = a⁻³ ((Ũ·∇)Ũ - ΔŨ + (Ũ·∇)Ψ + (Ψ·∇)Ũ + (Ψ·∇)Ψ - ΔΨ)` with `Ψ` the
increment at `a`. -/
theorem vectorDilation_profileNonlinearSobolev (N : ℕ) (hm : (3 : ℝ) < 2 * N) {a : ℝ}
    (ha : 0 < a) :
    vectorDilation 3 N a ha.ne' (D.profileNonlinearSobolev N) = (a⁻¹) ^ 3 •
      (D.profileNonlinearSobolev N +
        NavierStokes.SobolevConvection.profileConvection N (D.velocityWkTop (N + 1))
          (D.profileIncrement (N + 1) a) +
        mixedConvection N hm (vectorLower 3 N (D.profileIncrement (N + 1) a))
          (D.profileIncrement (N + 1) a) -
        vectorLaplacian 3 N (D.profileIncrement (N + 2) a)) := by
  set ψ := dilateField a D.U - D.U with hψ
  have hU := D.contDiff_U
  have hψc : ContDiff ℝ (⊤ : ℕ∞) ψ := (contDiff_dilateField a hU).sub hU
  rw [D.profileIncrement_eq (N + 1) ha, D.profileIncrement_eq (N + 2) ha]
  set v : VectorH 3 (N + 1) := WithLp.toLp 2 (vectorWkpOfContDiff ψ hψc
    fun m _ ↦ D.memLp_iteratedFDeriv_dilateField_sub ha m) with hv
  set w : VectorH 3 (N + 2) := WithLp.toLp 2 (vectorWkpOfContDiff ψ hψc
    fun m _ ↦ D.memLp_iteratedFDeriv_dilateField_sub ha m) with hw
  refine PiLp.ext fun j ↦ WkpSpaceOn.ext_of_base_ae isOpen_univ _ _ ?_
  change baseRepresentative _ =ᵐ[domainMeasure 3 univ] baseRepresentative _
  simp only [domainMeasure, Measure.restrict_univ]
  -- the left side
  have hK := baseRepresentative_toLp_vectorWkpOfContDiff_ae (N := N) D.contDiff_nonlinearField
    (fun m _ ↦ D.memLp_iteratedFDeriv_nonlinearField m) j
  have hL₁ := dilationWkpCLM_base_ae (by norm_num) a ha.ne' (D.profileNonlinearSobolev N j)
  have hL₂ := (Measure.quasiMeasurePreserving_smul (volume : Measure (ℝ^3)) ha.ne').ae_eq_comp hK
  simp only [domainMeasure, Measure.restrict_univ] at hL₁
  -- the right side
  set X : VectorH 3 N := D.profileNonlinearSobolev N +
    NavierStokes.SobolevConvection.profileConvection N (D.velocityWkTop (N + 1)) v +
    mixedConvection N hm (vectorLower 3 N v) v - vectorLaplacian 3 N w with hX
  have hR₁ := baseRepresentative_smul_ae ((a⁻¹) ^ 3) (X j)
  have hR₂ := baseRepresentative_sub_ae (D.profileNonlinearSobolev N j +
    NavierStokes.SobolevConvection.profileConvection N (D.velocityWkTop (N + 1)) v j +
    mixedConvection N hm (vectorLower 3 N v) v j) (vectorLaplacian 3 N w j)
  have hR₃ := baseRepresentative_add_ae (D.profileNonlinearSobolev N j +
    NavierStokes.SobolevConvection.profileConvection N (D.velocityWkTop (N + 1)) v j)
    (mixedConvection N hm (vectorLower 3 N v) v j)
  have hR₄ := baseRepresentative_add_ae (D.profileNonlinearSobolev N j)
    (NavierStokes.SobolevConvection.profileConvection N (D.velocityWkTop (N + 1)) v j)
  simp only [domainMeasure, Measure.restrict_univ] at hR₁ hR₂ hR₃ hR₄
  have hB := NavierStokes.SobolevConvection.profileConvection_vectorWkpOfContDiff_base_ae N D.U
    D.contDiff_U (fun m _ ↦ D.memLp_top_iteratedFDeriv m) v j
  have hM := mixedConvection_base_ae hm (vectorLower 3 N v) v j
  have hv0 := fun i : Fin 3 ↦ baseRepresentative_toLp_vectorWkpOfContDiff_ae (N := N + 1) hψc
    (fun m _ ↦ D.memLp_iteratedFDeriv_dilateField_sub ha m) i
  have hv1 := fun i k : Fin 3 ↦ baseRepresentative_partialDerivCLM_vectorWkpOfContDiff
    (k := N) ψ hψc (fun m _ ↦ D.memLp_iteratedFDeriv_dilateField_sub ha m) k i
  have hw0 := baseRepresentative_toLp_vectorWkpOfContDiff_ae (N := N + 2) hψc
    (fun m _ ↦ D.memLp_iteratedFDeriv_dilateField_sub ha m) j
  have hΔ : baseRepresentative (vectorLaplacian 3 N w j) =ᵐ[volume]
      fun x ↦ ∑ i : Fin 3, iteratedPartialDeriv [i, i] (fun y ↦ ψ y j) x := by
    rw [vectorLaplacian_apply, higherOrderLaplacianCLM, sum_apply]
    have hs := baseRepresentative_sum_ae (fun i : Fin 3 ↦
      (derivativeWordCLM [i, i] (by simp [Nat.add_comm]) (w j) : W^{N,2}(ℝ^3)))
    simp only [domainMeasure, Measure.restrict_univ] at hs
    have hi := fun i : Fin 3 ↦ baseRepresentative_derivativeWordCLM_ae (k := N) isOpen_univ (w j)
      (fun y ↦ ψ y j) [i, i] (by simp [Nat.add_comm])
      ((EuclideanSpace.proj j : ℝ^3 →L[ℝ] ℝ).contDiff.comp (hψc.of_le (by exact_mod_cast le_top)))
      (by simpa only [domainMeasure, Measure.restrict_univ] using hw0)
    simp only [domainMeasure, Measure.restrict_univ] at hi
    filter_upwards [hs, ae_all_iff.mpr hi] with x hx hix
    rw [hx]
    exact Finset.sum_congr rfl fun i _ ↦ hix i
  filter_upwards [hL₁, hL₂, hR₁, hR₂, hR₃, hR₄, hB, hM, ae_all_iff.mpr hv0,
    ae_all_iff.mpr fun i ↦ ae_all_iff.mpr (hv1 i), hΔ, hK] with x l₁ l₂ r₁ r₂ r₃ r₄ rB rM
      e₀ e₁ eΔ eK
  rw [vectorDilation_apply, l₁]
  simp only [Function.comp_apply] at l₂
  have eL : baseRepresentative ((D.profileNonlinearSobolev N) j) (a • x) =
      nonlinearField D.U (a • x) j := l₂
  have eK' : baseRepresentative ((D.profileNonlinearSobolev N) j) x = nonlinearField D.U x j := eK
  have rB' : baseRepresentative
      ((NavierStokes.SobolevConvection.profileConvection N (D.velocityWkTop (N + 1)) v) j) x = _ :=
    rB
  rw [eL, PiLp.smul_apply, r₁, hX, PiLp.sub_apply, PiLp.add_apply, PiLp.add_apply, r₂, r₃, r₄,
    rB', rM, eΔ, eK', smul_eq_mul, D.nonlinearField_smul_component ha.ne' x j]
  congr 1
  simp only [vectorLower_apply, baseRepresentative_lowerOrderCLM, hv, PiLp.toLp_apply, e₀, e₁,
    ← hψ]

/-- **The increment equation.** In vector `Hᴺ`, `N ≥ 2`, the derivative of the increment at
`a > 0` is `2 a⁻³ Π ((Ũ·∇)Ũ - ΔŨ + (Ũ·∇)Ψ + (Ψ·∇)Ũ + (Ψ·∇)Ψ - ΔΨ)`. -/
theorem dilatedScaling_eq (N : ℕ) (hm : (3 : ℝ) < 2 * N) {a : ℝ} (ha : 0 < a) :
    D.dilatedScaling N a = (2 * (a⁻¹) ^ 3) •
      D.incrementNonlinearity N hm (D.profileIncrement (N + 1) a)
        (D.profileIncrement (N + 2) a) := by
  rw [D.dilatedScaling_of_ne N ha.ne', profileScalingSobolev, map_smul,
    ← leraySobolev_vectorDilation, D.vectorDilation_profileNonlinearSobolev N hm ha, map_smul,
    smul_smul, incrementNonlinearity]

/-- **Smoothness of the dilations of the profile.** In every vector `Hᴺ`, `N ≥ 2`, the increment
`a ↦ a Ũ(a ·) - Ũ` is smooth on `a > 0`. -/
theorem contDiffOn_profileIncrement :
    ∀ (j N : ℕ), (3 : ℝ) < 2 * N → ContDiffOn ℝ j (D.profileIncrement N) (Ioi 0) := by
  intro j
  induction j with
  | zero =>
    intro N _
    exact contDiffOn_zero.mpr fun a ha ↦
      (D.hasDerivAt_profileIncrement N ha).continuousAt.continuousWithinAt
  | succ j ih =>
    intro N hm
    have hm₁ := three_lt_two_mul_succ hm
    have hm₂ := three_lt_two_mul_succ hm₁
    rw [show ((j + 1 : ℕ) : WithTop ℕ∞) = (j : WithTop ℕ∞) + 1 by norm_cast,
      contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun a ha ↦ (D.hasDerivAt_profileIncrement N ha).differentiableAt.differentiableWithinAt,
      by simp, ?_⟩
    have h₁ := ih (N + 1) hm₁
    have h₂ := ih (N + 2) hm₂
    have hB := (mixedConvection N hm).isBoundedBilinearMap.contDiff (n := (j : WithTop ℕ∞))
    have hF : ContDiffOn ℝ j (fun a ↦ D.incrementNonlinearity N hm (D.profileIncrement (N + 1) a)
        (D.profileIncrement (N + 2) a)) (Ioi 0) := by
      unfold incrementNonlinearity
      exact (leraySobolev 3 N).contDiff.comp_contDiffOn
        (((contDiffOn_const.add
          ((NavierStokes.SobolevConvection.profileConvection N
            (D.velocityWkTop (N + 1))).contDiff.comp_contDiffOn h₁)).add
          (hB.comp_contDiffOn (((vectorLower 3 N).contDiff.comp_contDiffOn h₁).prodMk h₁))).sub
          ((vectorLaplacian 3 N).contDiff.comp_contDiffOn h₂))
    have hc : ContDiffOn ℝ j (fun a : ℝ ↦ 2 * (a⁻¹) ^ 3) (Ioi 0) :=
      (contDiffOn_const.mul ((contDiffOn_inv ℝ).pow 3)).mono fun a ha ↦ (ne_of_gt ha : a ≠ 0)
    refine (hc.smul hF).congr fun a ha ↦ ?_
    rw [(D.hasDerivAt_profileIncrement N ha).deriv, D.dilatedScaling_eq N hm ha]
    rfl

end UnstableProfile

end NavierStokes.Nonuniqueness
