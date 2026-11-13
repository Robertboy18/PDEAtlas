/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Quasilinear.Boundary.TangentialRegularity
public import PDE.Elliptic.Regularity.Quasilinear.Boundary.NormalRecovery
public import PDE.Elliptic.Regularity.Quasilinear.Boundary.Estimates.NormalGradient

/-!
# Completing the localized gradient by nonlinear normal recovery

The tangential gradient components are Sobolev parameters. Set their normal
coordinate to zero and regard the remaining gradient coordinate as the scalar
unknown in the normal component of the flux. Uniform monotonicity supplies scalar
invertibility estimates even when the Hessian or the transformed Jacobian is not
diagonal. The proof uses inward weak difference quotients, not a classical derivative
of the unknown. In dimension one the parameter family is identically zero.
-/

@[expose] public noncomputable section

open scoped Sobolev

open TopologicalSpace
open scoped Distributions

namespace PDE.Elliptic.Regularity.Quasilinear

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.Composition.Implicit
open scoped ENNReal NNReal RealInnerProductSpace

variable {n : ℕ} [Fact (0 < n)]

/-- Bounds for the tangential weak derivatives and the recovered normal derivative
assemble the cutoff normal gradient into an `H¹` field with a common norm scale. -/
theorem exists_localized_normal_gradient_H1_of_weakDerivative_bounds
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (u : H¹₀(HalfSpace.upper n))
    {B R N : ℝ} (hB : 0 ≤ B) (hR : 0 ≤ R) (hN : 0 ≤ N) (hu : ‖u‖ ≤ N)
    (htransverse : ∀ k : Fin n, k ≠ PDE.Common.lastIndex (n := n) →
      ∃ d : DerivLp n 2 (HalfSpace.upper n), ‖d‖ ≤ B * N ∧
        HasWeakDerivativeOn (HalfSpace.upper n) [k]
          (testFunctionLpTop (Ω := HalfSpace.upper n) η •
            derivCoordCLM (PDE.Common.lastIndex (n := n)) u :
              DerivLp n 2 (HalfSpace.upper n)) (d : ℝ^n → ℝ))
    (g : DerivLp n 2 (HalfSpace.upper n)) (hgnorm : ‖g‖ ≤ R * N)
    (hg : HasWeakDerivativeOn (HalfSpace.upper n) [PDE.Common.lastIndex (n := n)]
      (testFunctionLpTop (Ω := HalfSpace.upper n) η •
        derivCoordCLM (PDE.Common.lastIndex (n := n)) u :
          DerivLp n 2 (HalfSpace.upper n)) (g : ℝ^n → ℝ)) :
    ∃ V : H¹(HalfSpace.upper n), V.val (baseIndex n 1) =
      testFunctionLpTop (Ω := HalfSpace.upper n) η •
        derivCoordCLM (PDE.Common.lastIndex (n := n)) u ∧
      ‖V‖ ≤ (‖testFunctionLpTop (Ω := HalfSpace.upper n) η‖ + n * (B + R)) * N := by
  let normal := PDE.Common.lastIndex (n := n)
  let a := testFunctionLpTop (Ω := HalfSpace.upper n) η
  have hex (k : Fin n) : ∃ d : DerivLp n 2 (HalfSpace.upper n),
      HasWeakDerivativeOn (HalfSpace.upper n) [k]
        (a • derivCoordCLM normal u : DerivLp n 2 (HalfSpace.upper n))
        (d : ℝ^n → ℝ) := by
    by_cases hk : k = normal
    · exact ⟨g, by simpa only [hk] using hg⟩
    · exact (htransverse k hk).imp fun _ h ↦ h.2
  choose d hdf using hex
  obtain ⟨V, hV, _⟩ := exists_of_weakDerivative_coordinates
    (a • derivCoordCLM normal u) d hdf
  have hbase : ‖wkpBaseCoordinateCLM V‖ ≤ ‖a‖ * N := by
    change ‖V.val (baseIndex n 1)‖ ≤ _
    rw [hV]
    exact (Lp.norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left
      ((wkpCoordinateCLM_norm_le (singleDerivIndex n normal)
        (u : H¹(HalfSpace.upper n))).trans hu) (norm_nonneg a))
  have hderivative : ‖V‖ ≤ ‖wkpBaseCoordinateCLM V‖ + ∑ _ : Fin n, (B + R) * N := by
    apply norm_le_base_add_sum_of_weakDerivative_bounds (HalfSpace.isOpen_upper n) V
    intro k
    have hb : baseRepresentative V =
        (a • derivCoordCLM normal u : DerivLp n 2 (HalfSpace.upper n)) :=
      congrArg (fun v : DerivLp n 2 (HalfSpace.upper n) ↦ (v : ℝ^n → ℝ)) hV
    rw [hb]
    by_cases hk : k = normal
    · exact ⟨g, hgnorm.trans (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left hB) hN), by simpa only [hk] using hg⟩
    · obtain ⟨v, hv, hvweak⟩ := htransverse k hk
      exact ⟨v, hv.trans (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right hR) hN), hvweak⟩
  refine ⟨V, hV, hderivative.trans ?_⟩
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  linarith

/-- Quantitative tangential regularity and the normal flux give
first-order regularity of every localized gradient component. The
constant is fixed before the common field norm scale `N`. -/
theorem exists_localized_gradient_H1_of_normal_flux
    (A : ℝ^n → ℝ^n → ℝ^n) (K C : ℝ≥0) {m : ℝ} (hm : 0 < m)
    (hmono : ∀ x ∈ HalfSpace.upper n, ∀ z w : ℝ^n,
      m * ‖z - w‖ * ‖z - w‖ ≤ ⟪A x z - A x w, z - w⟫)
    (hvariation : ∀ x ∈ HalfSpace.upper n, ∀ y ∈ HalfSpace.upper n, ∀ z w : ℝ^n,
      ‖A y w - A x z‖ ≤ K * ‖y - x‖ * ‖z‖ + C * ‖w - z‖)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) {D : ℝ≥0} (hη : LipschitzWith D η.toFun)
    (hηbound : ∀ x ∈ HalfSpace.upper n, |η.toFun x| ≤ 1)
    (u : H¹₀(HalfSpace.upper n))
    (q : Fin n → DerivLp n 2 (HalfSpace.upper n))
    (hrep : ∀ᵐ x ∂domainMeasure n (HalfSpace.upper n),
      A x (Lp.euclideanTuple (fun i ↦ derivCoordCLM i u) x) = Lp.euclideanTuple q x)
    {B R N : ℝ} (hB : 0 ≤ B) (hR : 0 ≤ R) (hN : 0 ≤ N)
    (hu : ‖u‖ ≤ N) (hq : ∀ i, ‖q i‖ ≤ N)
    (hderiv : ∀ k : Fin n, k ≠ PDE.Common.lastIndex (n := n) → ∀ i : Fin n,
      ∃ g : DerivLp n 2 (HalfSpace.upper n), ‖g‖ ≤ B * N ∧
        HasWeakDerivativeOn (HalfSpace.upper n) [k]
          (testFunctionLpTop (Ω := HalfSpace.upper n) η • derivCoordCLM i u :
            DerivLp n 2 (HalfSpace.upper n)) (g : ℝ^n → ℝ))
    (F : H¹(HalfSpace.upper n))
    (hF : F.val (baseIndex n 1) = testFunctionLpTop (Ω := HalfSpace.upper n) η •
      q (PDE.Common.lastIndex (n := n))) (hFnorm : ‖F‖ ≤ R * N) :
    ∀ i : Fin n, ∃ W : H¹(HalfSpace.upper n),
      W.val (baseIndex n 1) =
        testFunctionLpTop (Ω := HalfSpace.upper n) η • derivCoordCLM i u ∧
      ‖W‖ ≤ localizedGradientRecoveryConstant m K C D B R η * N := by
  let normal := PDE.Common.lastIndex (n := n)
  let a := testFunctionLpTop (Ω := HalfSpace.upper n) η
  let T := n * B + localizedDerivativeCutoffConstant (HalfSpace.upper n) η
  let E := (SobolevSpace.Extension.GraphSpace.HalfSpace.operator n 2).toContinuousLinearMap
  have hcut := localizedDerivativeCutoffConstant_nonneg (Ω := HalfSpace.upper n) η
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have hnormal := localizedNormalDerivativeConstant_nonneg
    hm K.coe_nonneg C.coe_nonneg D.coe_nonneg hB hR η
  have hd (i : Fin n) : ‖derivCoordCLM i u‖ ≤ N :=
    (wkpCoordinateCLM_norm_le (singleDerivIndex n i)
      (u : H¹(HalfSpace.upper n))).trans hu
  have ht (i : {i : Fin n // i ≠ normal}) :
      ∃ W : H¹(HalfSpace.upper n), W.val (baseIndex n 1) =
        a • derivCoordCLM i.1 u :=
    exists_localized_tangential_gradient_H1 η u
      (fun k hk j ↦ (hderiv k hk j).imp fun _ h ↦ h.2) i.1 i.2
  choose W hW using ht
  have hWnorm (i : {i : Fin n // i ≠ normal}) : ‖W i‖ ≤ T * N := by
    refine (norm_localized_transverse_derivative_H1_le (HalfSpace.isOpen_upper n) η
      (u : H¹(HalfSpace.upper n)) normal i.1 i.2 hderiv (W i) (hW i)).trans ?_
    dsimp only [T]
    linarith [mul_le_mul_of_nonneg_left (show ‖(u : H¹(HalfSpace.upper n))‖ ≤ N from hu) hcut]
  let P (i : Fin n) : DerivLp n 2 (HalfSpace.upper n) :=
    if i = normal then 0 else derivCoordCLM i u
  let Z (i : Fin n) : H¹(HalfSpace.upper n) :=
    if hi : i = normal then 0 else W ⟨i, hi⟩
  have hPnorm (i : Fin n) : ‖P i‖ ≤ N := by
    by_cases hi : i = normal
    · simpa only [P, ite_eq_left hi, norm_zero] using hN
    · simpa only [P, ite_eq_right hi] using hd i
  have hZnorm (i : Fin n) : ‖Z i‖ ≤ T * N := by
    by_cases hi : i = normal
    · simpa only [Z, dite_eq_left hi, norm_zero] using mul_nonneg hT hN
    · simpa only [Z, dite_eq_right hi] using hWnorm ⟨i, hi⟩
  have hZbase (i : Fin n) : (Z i).val (baseIndex n 1) = a • P i := by
    by_cases hi : i = normal <;> simp [Z, P, hi, hW]
  have hmul (v : DerivLp n 2 (HalfSpace.upper n)) :
      (a • v : DerivLp n 2 (HalfSpace.upper n)) =ᵐ[domainMeasure n (HalfSpace.upper n)]
        fun x ↦ η.toFun x * v x := by
    filter_upwards [Lp.coeFn_lpSMul (r := 2) a v,
      testFunctionLpTop_apply_ae (Ω := HalfSpace.upper n) η] with x hx hy
    change (a • v) x = a x * v x at hx
    exact hx.trans (congrArg (fun t ↦ t * v x) hy)
  have hZ (i : Fin n) : ∀ᵐ x ∂domainMeasure n (HalfSpace.upper n),
      wkpBaseCoordinateCLM (Z i) x = η.toFun x * P i x := by
    change (Z i).val (baseIndex n 1) =ᵐ[domainMeasure n (HalfSpace.upper n)] _
    rw [hZbase]
    exact hmul (P i)
  have hdecomp : ∀ᵐ x ∂domainMeasure n (HalfSpace.upper n),
      parameterValues P x + derivCoordCLM normal u x • EuclideanSpace.single normal 1 =
        Lp.euclideanTuple (fun i ↦ derivCoordCLM i u) x := by
    filter_upwards [Lp.euclideanTuple_apply_ae (fun i ↦ derivCoordCLM i u),
      Lp.coeFn_zero ℝ (2 : ℝ≥0∞) (domainMeasure n (HalfSpace.upper n))] with x hx hz
    change (0 : DerivLp n 2 (HalfSpace.upper n)) x = 0 at hz
    apply PiLp.ext
    intro i
    change P i x + derivCoordCLM normal u x * (EuclideanSpace.single normal 1) i = _
    rw [hx i]
    by_cases hi : i = normal
    · subst i
      rw [show P normal = 0 by simp [P], hz]
      simp
    · simp [P, hi]
  have heq : ∀ᵐ x ∂domainMeasure n (HalfSpace.upper n),
      A x (parameterValues P x + derivCoordCLM normal u x •
        EuclideanSpace.single normal 1) normal = q normal x := by
    filter_upwards [hdecomp, hrep, Lp.euclideanTuple_apply_ae q] with x hd hr hq
    rw [hd, hr, hq]
  have hFae : ∀ᵐ x ∂domainMeasure n (HalfSpace.upper n),
      wkpBaseCoordinateCLM F x = η.toFun x * q normal x := by
    change F.val (baseIndex n 1) =ᵐ[domainMeasure n (HalfSpace.upper n)] _
    rw [hF]
    exact hmul (q normal)
  obtain ⟨g, hgnorm, hg⟩ := exists_localized_normal_derivative_of_flux
    (by norm_num : (1 : ℝ≥0∞) < 2) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    A K C hm hmono hvariation η.toFun hη hηbound (derivCoordCLM normal u) (q normal)
    (a • derivCoordCLM normal u) P Z F hZ heq (hmul _) hFae
  have houtput : ‖wkpCoordinateCLM (singleDerivIndex n normal) (E F)‖ ≤ ‖E‖ * (R * N) :=
    (wkpCoordinateCLM_norm_le _ _).trans
      ((E.le_opNorm F).trans (mul_le_mul_of_nonneg_left hFnorm E.opNorm_nonneg))
  have hg' : ‖g‖ ≤ localizedNormalDerivativeConstant m K C D B R η * N := by
    refine hgnorm.trans ((div_le_div_of_nonneg_right (add_le_add (add_le_add houtput
      (localizedParameterBound_le_of_norm_le K C D _ P Z (hd normal) hPnorm hZnorm))
      (mul_le_mul_of_nonneg_left (add_le_add (hq normal)
        (mul_le_mul_of_nonneg_left (hd normal) hm.le)) D.coe_nonneg)) hm.le).trans_eq ?_)
    unfold localizedNormalDerivativeConstant
    dsimp only [E, T]
    ring
  intro i
  by_cases hi : i = normal
  · subst i
    obtain ⟨V, hV, hVnorm⟩ := exists_localized_normal_gradient_H1_of_weakDerivative_bounds
      η u hB hnormal hN hu (fun k hk ↦ hderiv k hk normal) g hg' hg
    refine ⟨V, hV, hVnorm.trans ?_⟩
    change (‖a‖ + n * (B + localizedNormalDerivativeConstant m K C D B R η)) * N ≤
      (T + ‖a‖ + n * (B + localizedNormalDerivativeConstant m K C D B R η)) * N
    nlinarith only [mul_nonneg hT hN]
  · refine ⟨W ⟨i, hi⟩, hW ⟨i, hi⟩, (hWnorm ⟨i, hi⟩).trans ?_⟩
    apply mul_le_mul_of_nonneg_right _ hN
    change T ≤ T + ‖a‖ + n * (B + localizedNormalDerivativeConstant m K C D B R η)
    exact le_add_of_nonneg_right (norm_nonneg a) |>.trans
      (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) (add_nonneg hB hnormal)))

end PDE.Elliptic.Regularity.Quasilinear
