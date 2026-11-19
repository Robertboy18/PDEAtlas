/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Quasilinear.Boundary.LocalizedTestBounds
public import PDE.Elliptic.Regularity.Quasilinear.Boundary.TangentialCoercivity
import PDE.Analysis.MeasureTheory.Lp.NormDomination
import PDE.Analysis.Scalar.QuadraticBound

/-!
# Localized nonlinear tangential energy estimate

Uniform monotonicity absorbs the differentiated gradient. Spatial variation and the
derivative of the cutoff contribute lower-order terms. The resulting constant is fixed
before the solution, source, direction, or positive difference step is chosen.

Only the weak identity for the localized test is needed. This allows a chart
equation valid near the cutoff, without asserting a global equation for a cut-off solution.
-/

@[expose] public noncomputable section

open scoped Sobolev

open TopologicalSpace
open scoped Distributions

namespace PDE.Elliptic.Regularity.Quasilinear

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity SobolevSpace.GraphSpace.DifferenceQuotient
open scoped ENNReal RealInnerProductSpace

variable {n : ℕ} [Fact (0 < n)]

/-- The principal scalar sum is the pairing of the two localized Euclidean tuples. -/
theorem localizedTangential_principal_pairing
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n)) (h : ℝ)
    (P Q : Fin n → DerivLp n 2 (HalfSpace.upper n)) :
    (∑ i, ⟪tangentialDifferenceQuotientLp 2 k hk h (Q i),
      testFunctionLpTop (Ω := HalfSpace.upper n) (squaredCutoff η) •
        tangentialDifferenceQuotientLp 2 k hk h (P i)⟫) =
      ⟪testFunctionLpTop (Ω := HalfSpace.upper n) η •
          tangentialVectorDifference k hk h Q,
        testFunctionLpTop (Ω := HalfSpace.upper n) η •
          tangentialVectorDifference k hk h P⟫ := by
  simp only [tangentialVectorDifference, ← Lp.euclideanTuple_lpSMul,
    Lp.inner_euclideanTuple]
  apply Finset.sum_congr rfl
  intro i _
  rw [squaredCutoff, testFunctionLpTop_mul, ← lpSMul_top_top_two_assoc,
    inner_lpSMul_left_eq_right]

/-- An explicit cutoff-dependent constant for the nonlinear tangential estimate. -/
def localizedTangentialEstimateConstant (m K C : ℝ)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) : ℝ :=
  let M := ‖testFunctionLpTop (Ω := HalfSpace.upper n) η‖
  let D := ∑ i, ‖partialTestFunctionLpTop (Ω := HalfSpace.upper n) η i‖
  1 + (n * M + 2 * D * C + K * M * n +
    (localizedTangentialLowerConstant η + 2 * D * K * M * n)) / m

private theorem localizedScalarBound {m K C M D B N F U P X : ℝ}
    (hm : 0 < m) (hK : 0 ≤ K) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hD : 0 ≤ D) (hB : 0 ≤ B) (hN : 0 ≤ N) (hF : 0 ≤ F) (hU : 0 ≤ U)
    (hX : 0 ≤ X) (hP : P ≤ N * U)
    (hraw : m * X ^ 2 ≤ F * (N * M * X + B * U) +
      2 * (K * M * P + C * X) * D * U + K * M * P * X) :
    X ≤ (1 + (N * M + 2 * D * C + K * M * N +
      (B + 2 * D * K * M * N)) / m) * (F + U) := by
  have hraw' : m * X ^ 2 ≤
      (N * M * F + (2 * D * C + K * M * N) * U) * X +
        (B * F + 2 * D * K * M * N * U) * U := by
    apply hraw.trans
    calc
      _ ≤ F * (N * M * X + B * U) +
          2 * (K * M * (N * U) + C * X) * D * U +
            K * M * (N * U) * X := by gcongr
      _ = _ := by ring
  have hFT : F ≤ F + U := le_add_of_nonneg_right hU
  have hUT : U ≤ F + U := le_add_of_nonneg_left hF
  have hquad : m * X ^ 2 ≤
      (N * M + 2 * D * C + K * M * N) * (F + U) * X +
        (B + 2 * D * K * M * N) * (F + U) ^ 2 := by
    apply hraw'.trans
    calc
      _ ≤ (N * M * (F + U) + (2 * D * C + K * M * N) * (F + U)) * X +
          (B * (F + U) + 2 * D * K * M * N * (F + U)) * (F + U) := by gcongr
      _ = _ := by ring
  exact PDE.Analysis.Scalar.le_linear_of_quadratic_le hm (by positivity)
    (by positivity) (add_nonneg hF hU) hquad

/-- The localized tangential gradient quotient is uniformly bounded in the step.
The conclusion is derived from monotonicity and the weak equation evaluated on its
zero-trace test; no coefficient derivative of the unknown is assumed. -/
theorem norm_weighted_tangential_gradient_le
    (A : ℝ^n → ℝ^n → ℝ^n) {m K C : ℝ}
    (hm : 0 < m) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hmono : ∀ x ∈ HalfSpace.upper n, ∀ z w : ℝ^n,
      m * ‖z - w‖ * ‖z - w‖ ≤ ⟪A x z - A x w, z - w⟫)
    (hvariation : ∀ x ∈ HalfSpace.upper n, ∀ y ∈ HalfSpace.upper n, ∀ z w : ℝ^n,
      ‖A y w - A x z‖ ≤ K * ‖y - x‖ * ‖z‖ + C * ‖w - z‖)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (u : H¹₀(HalfSpace.upper n))
    (Q : Fin n → DerivLp n 2 (HalfSpace.upper n))
    (f : DerivLp n 2 (HalfSpace.upper n))
    (hrep : ∀ᵐ x ∂domainMeasure n (HalfSpace.upper n),
      A x (Lp.euclideanTuple (fun i ↦ derivCoordCLM i u) x) = Lp.euclideanTuple Q x)
    (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    {h : ℝ} (hh : 0 < h)
    (hu : (∑ i, ⟪Q i, derivCoordCLM i (localizedTangentialTest η k hk h u)⟫) =
      ⟪f, baseCoordCLM (localizedTangentialTest η k hk h u)⟫) :
    ‖testFunctionLpTop (Ω := HalfSpace.upper n) η •
        tangentialVectorDifference k hk h (fun i ↦ derivCoordCLM i u)‖ ≤
      localizedTangentialEstimateConstant m K C η * (‖f‖ + ‖u‖) := by
  let a := testFunctionLpTop (Ω := HalfSpace.upper n) η
  let M := ‖a‖
  let D := ∑ i, ‖partialTestFunctionLpTop (Ω := HalfSpace.upper n) η i‖
  let B := localizedTangentialLowerConstant η
  let P := Lp.euclideanTuple (fun i ↦ derivCoordCLM i u)
  let X := ‖a • tangentialVectorDifference k hk h (fun i ↦ derivCoordCLM i u)‖
  let G := ‖a • tangentialVectorDifference k hk h Q‖
  let R := ⟪a • tangentialVectorDifference k hk h Q,
    a • tangentialVectorDifference k hk h (fun i ↦ derivCoordCLM i u)⟫
  let E := ∑ i, ⟪tangentialDifferenceQuotientLp 2 k hk h (Q i),
    partialTestFunctionLpTop (Ω := HalfSpace.upper n) (squaredCutoff η) i •
      tangentialDifferenceQuotientLp 2 k hk h (baseCoordCLM u)⟫
  have hM : 0 ≤ M := norm_nonneg _
  have hD : 0 ≤ D := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hB : 0 ≤ B := by
    change 0 ≤ M ^ 2 + 2 * M * D
    positivity
  have hX : 0 ≤ X := norm_nonneg _
  have ha : ∀ᵐ x ∂domainMeasure n (HalfSpace.upper n), |a x| ≤ M := by
    simpa only [Real.norm_eq_abs] using Lp.norm_apply_ae_le a
  have hspatial : ∀ x ∈ HalfSpace.upper n, ∀ y ∈ HalfSpace.upper n, ∀ z : ℝ^n,
      ‖A y z - A x z‖ ≤ K * ‖y - x‖ * ‖z‖ := by
    intro x hx y hy z
    simpa only [sub_self, norm_zero, mul_zero, add_zero] using hvariation x hx y hy z z
  have hc : m * X ^ 2 ≤ R + K * M * ‖P‖ * X :=
    weighted_tangential_coercivity A hK hM hmono hspatial _ Q hrep a ha k hk hh
  have hG : G ≤ K * M * ‖P‖ + C * X :=
    norm_weighted_tangential_flux_le A hK hC hM hvariation _ Q hrep a ha k hk hh
  have heq : R + E = ⟪f, baseCoordCLM (localizedTangentialTest η k hk h u)⟫ := by
    simpa only [localizedTangential_principal_pairing] using
      localizedTangential_energy_identity η k hk hh.ne' u Q f hu
  have hsource : |⟪f, baseCoordCLM (localizedTangentialTest η k hk h u)⟫| ≤
      ‖f‖ * (n * M * X + B * ‖u‖) :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left
        (norm_baseCoord_localizedTangentialTest_le η k hk hh.ne' u) (norm_nonneg _))
  have hE : |E| ≤ 2 * (K * M * ‖P‖ + C * X) * D * ‖u‖ :=
    (abs_localizedTangential_cutoff_pairing_le η k hk hh.ne' u Q).trans (by gcongr)
  have hP : ‖P‖ ≤ n * ‖u‖ := (Lp.norm_euclideanTuple_le (fun i ↦ derivCoordCLM i u)).trans
    ((Finset.sum_le_sum fun i _ ↦ derivCoordCLM_norm_le i u).trans_eq (by simp))
  have hraw : m * X ^ 2 ≤
      ‖f‖ * (n * M * X + B * ‖u‖) +
        2 * (K * M * ‖P‖ + C * X) * D * ‖u‖ + K * M * ‖P‖ * X := by
    have hs := le_abs_self ⟪f, baseCoordCLM (localizedTangentialTest η k hk h u)⟫
    have he := neg_le_abs E
    linarith only [hc, heq, hsource, hE, hs, he]
  exact localizedScalarBound hm hK hC hM hD hB (Nat.cast_nonneg n)
    (norm_nonneg _) (norm_nonneg _) hX hP hraw

end PDE.Elliptic.Regularity.Quasilinear
