/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Nonuniqueness.PhysicalCoefficientFields
public import PDE.FDeriv.Calculus.Symmetric
public import PDE.Fluid.NavierStokes.Selfsimilar.VelocityDrift

/-!
# The scaling field of a self-similar profile

The dilations `a ↦ a X(a ·)` of a smooth field have the generator `X + ξ·∇X`, the scaling
field or drift `SpectralProfile.velocityDrift X` (`hasDerivAt_dilateField_apply`). For an
unstable profile `Ũ` the profile equation `-½ (Ũ + ξ·∇Ũ) + (Ũ·∇)Ũ - ΔŨ + ∇P̃ = 0` writes
the scaling field as
`2 ((Ũ·∇)Ũ - ΔŨ + ∇P̃)` (`UnstableProfile.velocityDrift_eq`). The nonlinear field
`(X·∇)X - ΔX` scales with the third power of the dilation factor
(`nonlinearField_dilateField`), the scaling field of a divergence-free field is divergence free
(`divergence_velocityDrift`), and for an unstable profile every derivative of the nonlinear field
is square integrable (`UnstableProfile.memLp_iteratedFDeriv_nonlinearField`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology

namespace NavierStokes.Nonuniqueness

set_option linter.missingDocs true

variable {X Y : ℝ^3 → ℝ^3}

/-- The nonlinear field `(X·∇)X - ΔX`. -/
def nonlinearField (X : ℝ^3 → ℝ^3) (x : ℝ^3) : ℝ^3 :=
  fderiv ℝ X x (X x) - PDE.laplacian X x

/-- The dilations of a smooth field are differentiable in the factor, with the scaling field
as derivative: `∂ₐ (a X(a x)) = (X + ξ·∇X)(a x)`. -/
theorem hasDerivAt_dilateField_apply (hX : ContDiff ℝ (⊤ : ℕ∞) X) (a : ℝ) (x : ℝ^3) :
    HasDerivAt (fun b ↦ dilateField b X x) (SpectralProfile.velocityDrift X (a • x)) a := by
  have h₁ : HasDerivAt (fun b : ℝ ↦ b • x) x a := by
    simpa using (hasDerivAt_id a).smul_const x
  have h₂ : HasDerivAt (fun b : ℝ ↦ X (b • x)) (fderiv ℝ X (a • x) x) a :=
    ((hX.differentiable (by simp)).differentiableAt.hasFDerivAt).comp_hasDerivAt a h₁
  have h₃ := (hasDerivAt_id' a).smul h₂
  unfold dilateField SpectralProfile.velocityDrift
  convert h₃ using 1
  rw [map_smul, one_smul, add_comm]

/-- A partial derivative of `y ↦ g (a y)`. -/
theorem partialDeriv_comp_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ^3 → E} (hg : Differentiable ℝ g) (a : ℝ) (i : Fin 3) (x : ℝ^3) :
    PDE.partialDeriv i (fun y ↦ g (a • y)) x = a • PDE.partialDeriv i g (a • x) := by
  have hd : HasFDerivAt (fun y ↦ g (a • y))
      ((fderiv ℝ g (a • x)).comp (a • ContinuousLinearMap.id ℝ (ℝ^3))) x :=
    (hg (a • x)).hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul a)
  simp only [PDE.partialDeriv, hd.fderiv, ContinuousLinearMap.comp_apply,
    smul_apply, ContinuousLinearMap.id_apply, map_smul]

/-- The partial derivatives of a dilated field: `∂ᵢ(X^a)(x) = a² ∂ᵢX(a x)`. -/
theorem partialDeriv_dilateField (hX : ContDiff ℝ (⊤ : ℕ∞) X) (a : ℝ) (i : Fin 3) :
    PDE.partialDeriv i (dilateField a X) = fun y ↦ (a * a) • PDE.partialDeriv i X (a • y) := by
  funext y
  exact fderiv_dilateField_apply a hX y _

/-- The Laplacian of a dilated field: `Δ(X^a)(x) = a³ ΔX(a x)`. -/
theorem laplacian_dilateField (hX : ContDiff ℝ (⊤ : ℕ∞) X) (a : ℝ) (x : ℝ^3) :
    PDE.laplacian (dilateField a X) x = a ^ 3 • PDE.laplacian X (a • x) := by
  have hd (i : Fin 3) : Differentiable ℝ (PDE.partialDeriv i X) :=
    ((PDE.contDiff_top_partialDeriv (i := i) hX).differentiable (by simp))
  unfold PDE.laplacian
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have h₁ : (fun y ↦ PDE.partialDeriv i (dilateField a X) y) =
      fun y ↦ (a * a) • PDE.partialDeriv i X (a • y) := partialDeriv_dilateField hX a i
  rw [h₁]
  have h₂ : PDE.partialDeriv i (fun y ↦ (a * a) • PDE.partialDeriv i X (a • y)) x =
      (a * a) • PDE.partialDeriv i (fun y ↦ PDE.partialDeriv i X (a • y)) x := by
    have hdi : DifferentiableAt ℝ (fun y ↦ PDE.partialDeriv i X (a • y)) x :=
      (hd i).differentiableAt.comp x ((differentiable_id.const_smul a) x)
    change fderiv ℝ (fun y ↦ (a * a) • PDE.partialDeriv i X (a • y)) x _ =
      (a * a) • fderiv ℝ (fun y ↦ PDE.partialDeriv i X (a • y)) x _
    rw [(hdi.hasFDerivAt.fun_const_smul (a * a)).fderiv]
    rfl
  rw [h₂, partialDeriv_comp_smul (hd i), smul_smul, pow_succ, sq]

/-- The nonlinear field scales with the third power of the dilation factor:
`((X^a·∇)X^a - ΔX^a)(x) = a³ ((X·∇)X - ΔX)(a x)`. -/
theorem nonlinearField_dilateField (hX : ContDiff ℝ (⊤ : ℕ∞) X) (a : ℝ) (x : ℝ^3) :
    nonlinearField (dilateField a X) x = a ^ 3 • nonlinearField X (a • x) := by
  unfold nonlinearField
  rw [fderiv_dilateField_apply a hX, laplacian_dilateField hX, smul_sub]
  congr 1
  simp only [dilateField, map_smul, smul_smul]
  ring_nf

/-! ### Divergence of the scaling field -/

/-- The derivative of a smooth map is smooth. -/
theorem contDiff_fderiv_of_top {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) :=
  hf.fderiv_right (by simp)


/-- The divergence is the trace of the derivative. -/
theorem divergence_eq_sum_fderiv {F : ℝ^3 → ℝ^3} {x : ℝ^3} (hF : DifferentiableAt ℝ F x) :
    PDE.divergence F x = ∑ i : Fin 3, fderiv ℝ F x (EuclideanSpace.single i 1) i := by
  unfold PDE.divergence PDE.partialDeriv
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have h : HasFDerivAt (fun y ↦ (F y) i)
      ((EuclideanSpace.proj i : ℝ^3 →L[ℝ] ℝ).comp (fderiv ℝ F x)) x :=
    (EuclideanSpace.proj i : ℝ^3 →L[ℝ] ℝ).hasFDerivAt.comp x hF.hasFDerivAt
  rw [h.fderiv]
  rfl

/-- The scaling field of a smooth divergence-free field is divergence free:
`div(X + ξ·∇X) = (2 + ξ·∇) div X = 0`. -/
theorem divergence_velocityDrift (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hdiv : ∀ x, PDE.divergence X x = 0) (x : ℝ^3) :
    PDE.divergence (SpectralProfile.velocityDrift X) x = 0 := by
  have hX1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ X) := contDiff_fderiv_of_top hX
  have hdX : Differentiable ℝ X := hX.differentiable (by simp)
  have hdX1 : Differentiable ℝ (fderiv ℝ X) := hX1.differentiable (by simp)
  have hrad : ∀ y, DifferentiableAt ℝ (fun z ↦ fderiv ℝ X z z) y := fun y ↦
    (hdX1 y).clm_apply differentiableAt_id
  have hS : DifferentiableAt ℝ (SpectralProfile.velocityDrift X) x := (hdX x).add (hrad x)
  have hfd : fderiv ℝ (SpectralProfile.velocityDrift X) x =
      fderiv ℝ X x + (fderiv ℝ X x + (fderiv ℝ (fderiv ℝ X) x).flip x) := by
    have h₁ : fderiv ℝ (fun z ↦ fderiv ℝ X z z) x =
        fderiv ℝ X x + (fderiv ℝ (fderiv ℝ X) x).flip x := by
      rw [show (fun z ↦ fderiv ℝ X z z) = fun z ↦ fderiv ℝ X z (id z) from rfl,
        fderiv_clm_apply (hdX1 x) differentiableAt_id, fderiv_id]
      rfl
    have h₂ : SpectralProfile.velocityDrift X = fun z ↦ X z + fderiv ℝ X z z := rfl
    rw [h₂, fderiv_fun_add (hdX x) (hrad x), h₁]
  have hsymm : IsSymmSndFDerivAt ℝ X x := hX.contDiffAt.isSymmSndFDerivAt (by simp)
  -- the derivative of the divergence
  have hdivfun : (fun y ↦ ∑ i : Fin 3, fderiv ℝ X y (EuclideanSpace.single i 1) i) =
      fun _ ↦ (0 : ℝ) := by
    funext y
    rw [← divergence_eq_sum_fderiv (hdX y), hdiv y]
  have hcomp (i : Fin 3) : HasFDerivAt (fun y ↦ fderiv ℝ X y (EuclideanSpace.single i 1) i)
      ((EuclideanSpace.proj i : ℝ^3 →L[ℝ] ℝ).comp
        ((fderiv ℝ (fderiv ℝ X) x).flip (EuclideanSpace.single i 1))) x := by
    have hc : HasFDerivAt (fun y ↦ fderiv ℝ X y (EuclideanSpace.single i 1))
        ((fderiv ℝ (fderiv ℝ X) x).flip (EuclideanSpace.single i 1)) x := by
      have := (hdX1 x).hasFDerivAt.clm_apply (hasFDerivAt_const (EuclideanSpace.single i 1) x)
      simpa using this
    exact (EuclideanSpace.proj i : ℝ^3 →L[ℝ] ℝ).hasFDerivAt.comp x hc
  have hzero : ∑ i : Fin 3, fderiv ℝ (fderiv ℝ X) x x (EuclideanSpace.single i 1) i = 0 := by
    have hsum := HasFDerivAt.fun_sum (u := Finset.univ) fun i _ ↦ hcomp i
    rw [hdivfun] at hsum
    have h0 := (hasFDerivAt_const (0 : ℝ) x).unique hsum
    have h1 := congrArg (fun L : ℝ^3 →L[ℝ] ℝ ↦ L x) h0
    simp only [zero_apply, sum_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply] at h1
    exact h1.symm
  rw [divergence_eq_sum_fderiv hS, hfd]
  simp only [add_apply, ContinuousLinearMap.flip_apply, PiLp.add_apply,
    Finset.sum_add_distrib]
  rw [← divergence_eq_sum_fderiv (hdX x), hdiv x]
  have hsw : ∀ i : Fin 3, fderiv ℝ (fderiv ℝ X) x (EuclideanSpace.single i 1) x =
      fderiv ℝ (fderiv ℝ X) x x (EuclideanSpace.single i 1) := fun i ↦ hsymm _ _
  simp only [hsw, hzero, add_zero]

/-! ### Derivative bounds -/

/-- The derivatives of `y ↦ h y v` are bounded by those of `h`. -/
theorem norm_iteratedFDeriv_clm_apply_const_le {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {h : ℝ^3 → E →L[ℝ] F}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (v : E) (m : ℕ) (x : ℝ^3) :
    ‖iteratedFDeriv ℝ m (fun y ↦ h y v) x‖ ≤ ‖iteratedFDeriv ℝ m h x‖ * ‖v‖ := by
  have heq : (fun y ↦ h y v) = ⇑(ContinuousLinearMap.apply ℝ F v) ∘ h := rfl
  rw [heq, (ContinuousLinearMap.apply ℝ F v).iteratedFDeriv_comp_left hh.contDiffAt
    (i := m) (by exact_mod_cast le_top)]
  refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
  rw [mul_comm]
  gcongr
  exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg v) fun L ↦ by
    rw [ContinuousLinearMap.apply_apply, mul_comm]
    exact L.le_opNorm v

/-- The derivatives of the Laplacian are bounded by derivatives of two more orders. -/
theorem norm_iteratedFDeriv_laplacian_le (hX : ContDiff ℝ (⊤ : ℕ∞) X) (m : ℕ) (x : ℝ^3) :
    ‖iteratedFDeriv ℝ m (PDE.laplacian X) x‖ ≤ 3 * ‖iteratedFDeriv ℝ (m + 2) X x‖ := by
  have hd (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ fderiv ℝ X y (EuclideanSpace.single i 1)) :=
    (contDiff_fderiv_of_top hX).clm_apply contDiff_const
  have hdd (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fderiv ℝ (fun y ↦ fderiv ℝ X y (EuclideanSpace.single i 1))) :=
    contDiff_fderiv_of_top (hd i)
  have hterm (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ fderiv ℝ
      (fun z ↦ fderiv ℝ X z (EuclideanSpace.single i 1)) y (EuclideanSpace.single i 1)) :=
    (hdd i).clm_apply contDiff_const
  have hlap : PDE.laplacian X = ∑ i : Fin 3, fun y ↦ fderiv ℝ
      (fun z ↦ fderiv ℝ X z (EuclideanSpace.single i 1)) y (EuclideanSpace.single i 1) := by
    funext y
    simp [PDE.laplacian, PDE.partialDeriv, Finset.sum_apply]
  rw [hlap, iteratedFDeriv_sum_apply (fun i _ ↦ (hterm i).contDiffAt.of_le
    (by exact_mod_cast le_top))]
  refine (norm_sum_le _ _).trans ?_
  have hb (i : Fin 3) : ‖iteratedFDeriv ℝ m (fun y ↦ fderiv ℝ
      (fun z ↦ fderiv ℝ X z (EuclideanSpace.single i 1)) y (EuclideanSpace.single i 1)) x‖ ≤
      ‖iteratedFDeriv ℝ (m + 2) X x‖ := by
    refine (norm_iteratedFDeriv_clm_apply_const_le (hdd i) _ m x).trans ?_
    rw [PiLp.norm_single, norm_one, mul_one, norm_iteratedFDeriv_fderiv]
    refine (norm_iteratedFDeriv_clm_apply_const_le (contDiff_fderiv_of_top hX) _ (m + 1)
      x).trans ?_
    rw [PiLp.norm_single, norm_one, mul_one, norm_iteratedFDeriv_fderiv]
  calc ∑ i : Fin 3, _ ≤ ∑ _i : Fin 3, ‖iteratedFDeriv ℝ (m + 2) X x‖ :=
        Finset.sum_le_sum fun i _ ↦ hb i
    _ = 3 * ‖iteratedFDeriv ℝ (m + 2) X x‖ := by simp

/-- The derivatives of `y ↦ DX(y) (X y)`, by the Leibniz rule. -/
theorem norm_iteratedFDeriv_advective_le (hX : ContDiff ℝ (⊤ : ℕ∞) X) (m : ℕ) (x : ℝ^3) :
    ‖iteratedFDeriv ℝ m (fun y ↦ fderiv ℝ X y (X y)) x‖ ≤
      ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * ‖iteratedFDeriv ℝ (i + 1) X x‖ *
        ‖iteratedFDeriv ℝ (m - i) X x‖ := by
  have h := (ContinuousLinearMap.id ℝ (ℝ^3 →L[ℝ] ℝ^3)).norm_iteratedFDeriv_le_of_bilinear
    (contDiff_fderiv_of_top hX) hX x (n := m) (by exact_mod_cast le_top)
  simp only [ContinuousLinearMap.id_apply, norm_iteratedFDeriv_fderiv] at h
  refine h.trans ?_
  have h1 : ‖ContinuousLinearMap.id ℝ (ℝ^3 →L[ℝ] ℝ^3)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have h0 : 0 ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
      ‖iteratedFDeriv ℝ (i + 1) X x‖ * ‖iteratedFDeriv ℝ (m - i) X x‖ :=
    Finset.sum_nonneg fun _ _ ↦ by positivity
  nlinarith

/-! ### The profile -/

namespace UnstableProfile

variable (D : UnstableProfile)

/-- The scaling field of the profile through the profile equation:
`Ũ + ξ·∇Ũ = 2 ((Ũ·∇)Ũ - ΔŨ + ∇P̃)`. -/
theorem velocityDrift_eq (ξ : ℝ^3) :
    SpectralProfile.velocityDrift D.U ξ = (2 : ℝ) • (nonlinearField D.U ξ + gradient D.P ξ) := by
  have h := D.profile_eq ξ
  unfold stationaryVelocityOperator PDE.advectiveDerivative at h
  unfold SpectralProfile.velocityDrift nonlinearField
  calc D.U ξ + fderiv ℝ D.U ξ ξ = D.U ξ + fderiv ℝ D.U ξ ξ +
        (2 : ℝ) • ((-(1 / 2) : ℝ) • (D.U ξ + fderiv ℝ D.U ξ ξ) +
          fderiv ℝ D.U ξ (D.U ξ) - PDE.laplacian D.U ξ + gradient D.P ξ) := by
        rw [h, smul_zero, add_zero]
    _ = _ := by module

/-- Every derivative of the nonlinear field `(Ũ·∇)Ũ - ΔŨ` of the profile is square
integrable. -/
theorem memLp_iteratedFDeriv_nonlinearField (m : ℕ) :
    MemLp (iteratedFDeriv ℝ m (nonlinearField D.U)) 2 volume := by
  have hX := D.contDiff_U
  have hadv : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ fderiv ℝ D.U y (D.U y)) :=
    (contDiff_fderiv_of_top hX).clm_apply hX
  have hlap : ContDiff ℝ (⊤ : ℕ∞) (PDE.laplacian D.U) := by
    unfold PDE.laplacian
    exact ContDiff.sum fun i _ ↦ PDE.contDiff_top_partialDeriv (PDE.contDiff_top_partialDeriv hX)
  have heq : iteratedFDeriv ℝ m (nonlinearField D.U) =
      iteratedFDeriv ℝ m (fun y ↦ fderiv ℝ D.U y (D.U y)) -
        iteratedFDeriv ℝ m (PDE.laplacian D.U) := by
    funext x
    exact iteratedFDeriv_sub_apply (hadv.contDiffAt.of_le (by exact_mod_cast le_top))
      (hlap.contDiffAt.of_le (by exact_mod_cast le_top))
  rw [heq]
  refine MemLp.sub ?_ ?_
  · choose C hC using D.bounded_derivatives
    have hg : MemLp (fun x ↦ ∑ i ∈ Finset.range (m + 1), ((m.choose i : ℝ) * C (m - i)) *
        ‖iteratedFDeriv ℝ (i + 1) D.U x‖) 2 volume :=
      by
        have h := memLp_finsetSum' (Finset.range (m + 1)) fun i _ ↦
          ((D.derivatives_memLp_two (i + 1) (by omega)).norm).const_mul
            ((m.choose i : ℝ) * C (m - i))
        convert h using 1
        funext x
        simp only [Finset.sum_apply]
    refine hg.of_le
      ((hadv.continuous_iteratedFDeriv (by exact_mod_cast le_top)).aestronglyMeasurable)
      (Eventually.of_forall fun x ↦ ?_)
    refine (norm_iteratedFDeriv_advective_le hX m x).trans ?_
    rw [Real.norm_eq_abs]
    refine le_trans ?_ (le_abs_self _)
    refine Finset.sum_le_sum fun i _ ↦ ?_
    have := hC (m - i) x
    have h0 : 0 ≤ ‖iteratedFDeriv ℝ (i + 1) D.U x‖ := norm_nonneg _
    have h1 : (0 : ℝ) ≤ m.choose i := Nat.cast_nonneg _
    nlinarith [mul_nonneg h1 h0]
  · have hg : MemLp (fun x ↦ 3 * ‖iteratedFDeriv ℝ (m + 2) D.U x‖) 2 volume :=
      (D.derivatives_memLp_two (m + 2) (by omega)).norm.const_mul 3
    refine hg.of_le
      ((hlap.continuous_iteratedFDeriv (by exact_mod_cast le_top)).aestronglyMeasurable)
      (Eventually.of_forall fun x ↦ ?_)
    rw [Real.norm_eq_abs]
    exact (norm_iteratedFDeriv_laplacian_le hX m x).trans (le_abs_self _)

end UnstableProfile

end NavierStokes.Nonuniqueness
