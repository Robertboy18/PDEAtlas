/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.Localized.InteriorBounds
public import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.Localized.MonotoneFlux
import PDE.Analysis.Scalar.QuadraticBound

/-!
# Interior energy estimates for monotone Lipschitz fluxes

The original weak equation is tested with the interior signed
quotient. Monotonicity controls the localized gradient quotient; the
Lipschitz bound absorbs the cutoff error. The source term uses the sharp
first-derivative bound for the test. Consequently only the original
gradient and source norms enter the estimate, even for nonzero boundary
trace and nonzero constant part of the flux.
-/

@[expose] public noncomputable section

open TopologicalSpace
open scoped Distributions

namespace PDE.Elliptic.Regularity.Quasilinear

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.DifferenceQuotient SobolevSpace.Extension.Lp
open scoped ENNReal RealInnerProductSpace Sobolev

variable {n : ℕ} {Ω S : Set (ℝ^n)}

/-- The constant in the interior quotient estimate, fixed by the cutoff,
monotonicity and Lipschitz constants before the solution is chosen. -/
def interiorQuotientEstimateConstant (m C : ℝ) (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) : ℝ :=
  let M := ‖testFunctionLpTop (Ω := univ) η‖
  let D := ∑ i, ‖partialTestFunctionLpTop (Ω := univ) η i‖
  1 + (M + 2 * C * D + 2 * M * D) / m

/-- The estimate constant is strictly positive for a positive
monotonicity constant and a nonnegative Lipschitz constant. -/
theorem interiorQuotientEstimateConstant_pos {m C : ℝ}
    (hm : 0 < m) (hC : 0 ≤ C) (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    0 < interiorQuotientEstimateConstant m C η := by
  unfold interiorQuotientEstimateConstant
  positivity

private theorem euclideanTuple_zeroExtend_agree {d : ℕ}
    (hΩ : MeasurableSet Ω) (P : Fin d → DerivLp n 2 Ω) :
    (Lp.euclideanTuple (fun i ↦ zeroExtendLp hΩ (P i)) : ℝ^n → ℝ^d)
      =ᵐ[domainMeasure n Ω] Lp.euclideanTuple P := by
  have he : ∀ᵐ x ∂domainMeasure n Ω, ∀ i, zeroExtendLp hΩ (P i) x = P i x :=
    ae_all_iff.mpr fun i ↦ zeroExtendLp_agree_ae hΩ (P i)
  filter_upwards [(Lp.euclideanTuple_apply_ae (fun i ↦ zeroExtendLp hΩ (P i))).filter_mono
    (ae_mono (domainMeasure_le (subset_univ Ω))), Lp.euclideanTuple_apply_ae P, he]
    with x hx hy he
  exact PiLp.ext fun i ↦ (hx i).trans ((he i).trans (hy i).symm)

private theorem principal_pairing
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (P Q : Fin n → DerivLp n 2 univ) :
    (∑ i, ⟪Q i, testFunctionLpTop (Ω := univ) (squaredCutoff η) • P i⟫) =
      ⟪testFunctionLpTop (Ω := univ) η • Lp.euclideanTuple Q,
        testFunctionLpTop (Ω := univ) η • Lp.euclideanTuple P⟫ := by
  simp only [← Lp.euclideanTuple_lpSMul, Lp.inner_euclideanTuple]
  apply Finset.sum_congr rfl
  intro i _
  rw [squaredCutoff, testFunctionLpTop_mul, ← lpSMul_top_top_two_assoc,
    inner_lpSMul_left_eq_right]

private theorem gradient_bound_of_energy {m C M D X F G : ℝ}
    (hm : 0 < m) (hC : 0 ≤ C) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hX : 0 ≤ X) (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hraw : m * X ^ 2 ≤ F * (M * X + 2 * M * D * G) +
      2 * (C * X) * D * G) :
    X ≤ (1 + (M + 2 * C * D + 2 * M * D) / m) * (F + G) := by
  let T := F + G
  have hT : 0 ≤ T := add_nonneg hF hG
  have hFT : F ≤ T := le_add_of_nonneg_right hG
  have hGT : G ≤ T := le_add_of_nonneg_left hF
  have hquad : m * X ^ 2 ≤ (M + 2 * C * D) * T * X + (2 * M * D) * T ^ 2 := by
    apply hraw.trans
    calc
      _ = (M * F + 2 * C * D * G) * X + (2 * M * D) * F * G := by ring
      _ ≤ (M * T + 2 * C * D * T) * X + (2 * M * D) * T * T := by gcongr
      _ = _ := by ring
  exact PDE.Analysis.Scalar.le_linear_of_quadratic_le hm (by positivity)
    (by positivity) hT hquad

/-- A step-uniform interior gradient-quotient estimate for an arbitrary
`H¹` solution of a monotone Lipschitz divergence equation.
Admissibility and the energy identity are derived from the cutoff collar
and the original weak equation. -/
theorem norm_weighted_interior_gradient_le
    (hΩ : IsOpen Ω) (hS : IsOpen S) (hSΩ : S ⊆ Ω)
    (A : ℝ^n → ℝ^n) {m C : ℝ} (hm : 0 < m) (hC : 0 ≤ C)
    (hmono : ∀ z w, m * ‖z - w‖ * ‖z - w‖ ≤ ⟪A z - A w, z - w⟫)
    (hLip : ∀ z w, ‖A z - A w‖ ≤ C * ‖z - w‖)
    (χ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hχ : tsupport χ.toFun ⊆ Ω)
    (hone : ∀ x ∈ S, χ.toFun x = 1)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hη : tsupport η.toFun ⊆ S)
    {ρ : ℝ} (hρ : 0 < ρ) (hρΩ : Metric.thickening ρ (tsupport η.toFun) ⊆ Ω)
    (k : Fin n) {h : ℝ} (hh : h ≠ 0) (hhρ : |h| < ρ)
    (hshift : MapsTo (fun x ↦ x + coordinateStep k h) (tsupport η.toFun) S)
    (u : H¹(Ω)) (q : Fin n → DerivLp n 2 Ω) (f : DerivLp n 2 Ω)
    (hrep : ∀ᵐ x ∂domainMeasure n Ω,
      A (Lp.euclideanTuple (fun i ↦ u.val (singleDerivIndex n i)) x) = Lp.euclideanTuple q x)
    (hweak : ∀ v : H¹₀(Ω),
      (∑ i, ⟪q i, derivCoordCLM i v⟫) = ⟪f, baseCoordCLM v⟫) :
    ‖testFunctionLpTop (Ω := univ) η • Lp.euclideanTuple (fun i ↦
        differenceQuotientLp 2 k h
          (zeroExtendLp hΩ.measurableSet (u.val (singleDerivIndex n i))))‖ ≤
      interiorQuotientEstimateConstant m C η * (‖f‖ + ‖∇ u‖) := by
  let E := zeroExtendLp (p := 2) hΩ.measurableSet
  let P := fun i ↦ E (u.val (singleDerivIndex n i))
  let Q := fun i ↦ E (q i)
  let DP := fun i ↦ differenceQuotientLp 2 k h (P i)
  let DQ := fun i ↦ differenceQuotientLp 2 k h (Q i)
  let b := differenceQuotientLp 2 k h (E (u.val (baseIndex n 1)))
  let a := testFunctionLpTop (Ω := univ) η
  let M := ‖a‖
  let D := ∑ i, ‖partialTestFunctionLpTop (Ω := univ) η i‖
  let X := ‖a • Lp.euclideanTuple DP‖
  let Y := ‖a • Lp.euclideanTuple DQ‖
  let G := ‖∇ u‖
  let err := ∑ i, ⟪DQ i, partialTestFunctionLpTop (Ω := univ) (squaredCutoff η) i • b⟫
  let vbase := -restrictDerivLp (subset_univ Ω)
    (differenceQuotientLp 2 k (-h) (testFunctionLpTop (Ω := univ) (squaredCutoff η) • b))
  have hM : 0 ≤ M := norm_nonneg _
  have hD : 0 ≤ D := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hG : 0 ≤ G := norm_nonneg _
  have hX : 0 ≤ X := norm_nonneg _
  have hrepE : ∀ᵐ x ∂domainMeasure n Ω,
      A (Lp.euclideanTuple P x) = Lp.euclideanTuple Q x := by
    filter_upwards [euclideanTuple_zeroExtend_agree hΩ.measurableSet
      (fun i ↦ u.val (singleDerivIndex n i)),
      euclideanTuple_zeroExtend_agree hΩ.measurableSet q, hrep] with x hp hq hx
    exact (congrArg A hp).trans (hx.trans hq.symm)
  obtain ⟨hcoercive, hflux⟩ := weighted_monotone_flux_differenceQuotient_bounds
    hΩ.measurableSet A hC hmono hLip P Q hrepE η (hη.trans hSΩ) k h
      (fun x hx ↦ hSΩ (hshift hx))
  change m * X ^ 2 ≤ ⟪a • Lp.euclideanTuple DQ, a • Lp.euclideanTuple DP⟫ at hcoercive
  change Y ≤ C * X at hflux
  have hcoordP (i : Fin n) : ‖a • DP i‖ ≤ X := by
    simpa only [Lp.euclideanTuple_lpSMul, X] using
      Lp.norm_coordinate_le_norm_euclideanTuple (fun j ↦ a • DP j) i
  have hcoordQ (i : Fin n) : ‖a • DQ i‖ ≤ Y := by
    simpa only [Lp.euclideanTuple_lpSMul, Y] using
      Lp.norm_coordinate_le_norm_euclideanTuple (fun j ↦ a • DQ j) i
  have hK : MeasurableSet (tsupport η.toFun) := (isClosed_tsupport _).measurableSet
  have hb : ‖restrictDerivLp (subset_univ (tsupport η.toFun)) b‖ ≤ G :=
    (norm_restricted_differenceQuotient_le (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hΩ hK
      (by rw [(isClosed_tsupport _).closure_eq]; exact η.hasCompactSupport) hρ hρΩ u k hh
        hhρ).trans (norm_derivCoordinate_le_wkpGradientCLM u k)
  have hdk : ‖partialTestFunctionLpTop (Ω := univ) η k‖ ≤ D :=
    Finset.single_le_sum (fun i _ ↦ norm_nonneg
      (partialTestFunctionLpTop (Ω := univ) η i)) (Finset.mem_univ k)
  have hpartial :
      ‖partialTestFunctionLpTop (Ω := univ) (squaredCutoff η) k • b‖ ≤ 2 * M * D * G := by
    rw [← partialSquaredCutoff_smul_zeroExtend_restrict hK η (Subset.refl _) k b]
    apply (norm_partialSquaredCutoff_smul_le η k _).trans
    rw [norm_zeroExtendLp]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hdk (mul_nonneg (by norm_num) hM))
      hb (norm_nonneg _) (mul_nonneg (mul_nonneg (by norm_num) hM) hD)
  have hv : ‖vbase‖ ≤ M * X + 2 * M * D * G := by
    apply (norm_interior_backward_test_le hΩ hS hSΩ χ hχ hone η hη k hh hshift u).trans
    apply (norm_add_le _ _).trans
    exact add_le_add
      ((norm_squaredCutoff_smul_le η (DP k)).trans
        (mul_le_mul_of_nonneg_left (hcoordP k) hM)) hpartial
  have herr : |err| ≤ 2 * Y * D * G := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ i, 2 * Y * ‖partialTestFunctionLpTop (Ω := univ) η i‖ * G :=
        Finset.sum_le_sum fun i _ ↦ (abs_inner_partialSquaredCutoff_le_restrict
          η (Subset.refl _) i (DQ i) b).trans (mul_le_mul (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hcoordQ i) (by norm_num)) (norm_nonneg _))
              hb (norm_nonneg _) (by positivity))
      _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]
  have heq : ⟪a • Lp.euclideanTuple DQ, a • Lp.euclideanTuple DP⟫ + err =
      ⟪f, vbase⟫ := by
    simpa only [principal_pairing] using interior_backward_test_identity
      hΩ hS hSΩ χ hχ hone η hη k hh hshift u q f hweak
  have hsource : |⟪f, vbase⟫| ≤ ‖f‖ * (M * X + 2 * M * D * G) :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hv (norm_nonneg _))
  have herr' : |err| ≤ 2 * (C * X) * D * G := herr.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hflux (by norm_num)) hD) hG)
  have hraw : m * X ^ 2 ≤ ‖f‖ * (M * X + 2 * M * D * G) +
      2 * (C * X) * D * G := by
    have hs := le_abs_self ⟪f, vbase⟫
    have he := neg_le_abs err
    linarith only [hcoercive, heq, hsource, herr', hs, he]
  exact gradient_bound_of_energy hm hC hM hD hX (norm_nonneg _) hG hraw

end PDE.Elliptic.Regularity.Quasilinear
