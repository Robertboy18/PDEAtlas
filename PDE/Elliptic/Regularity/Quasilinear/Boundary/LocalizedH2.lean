/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Quasilinear.Boundary.NormalGradient
public import PDE.Elliptic.Regularity.Quasilinear.Boundary.Estimates.LocalizedH2
public import PDE.Spaces.Sobolev.Calculus.Divergence.Cutoff
public import PDE.Spaces.Sobolev.Calculus.Divergence.Bounds
public import PDE.Spaces.Sobolev.Calculus.Product.LocalizedSecondOrder

/-!
# Local second-order regularity for a monotone equation on the upper half-space

Tangential difference quotients first control the localized gradient and flux.
The divergence equation supplies the remaining derivative of the normal flux;
nonlinear scalar recovery then supplies the normal gradient derivative. All these
derivatives are assembled in the second-order Sobolev space.

The equation is required only on the two families of localized tests used
in the argument. Thus a larger localization of a chart pullback can serve as `u`
without asserting that multiplication by a cutoff preserves its nonlinear PDE.
For dimension one the tangential hypotheses are empty.
-/

@[expose] public noncomputable section

open scoped Sobolev

open TopologicalSpace
open scoped Distributions

namespace PDE.Elliptic.Regularity.Quasilinear

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.DifferenceQuotient
open scoped ENNReal NNReal RealInnerProductSpace

variable {n : ℕ} [Fact (0 < n)]

/-- The cutoff divergence equation recovers the normal flux as an `H¹` field.
Its norm is controlled by the load, the flux coordinates, and their tangential derivatives. -/
theorem exists_normal_cutoff_flux_H1_of_weakDivergence
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (q : Fin n → DerivLp n 2 (HalfSpace.upper n))
    (f : DerivLp n 2 (HalfSpace.upper n))
    {B N : ℝ} (hB : 0 ≤ B) (hN : 0 ≤ N)
    (hf : ‖f‖ ≤ N) (hq : ∀ i, ‖q i‖ ≤ N)
    (hflux : ∀ k : Fin n, k ≠ PDE.Common.lastIndex (n := n) → ∀ i : Fin n,
      ∃ g : DerivLp n 2 (HalfSpace.upper n), ‖g‖ ≤ B * N ∧
        HasWeakDerivativeOn (HalfSpace.upper n) [k]
          (testFunctionLpTop (Ω := HalfSpace.upper n) η • q i :
            DerivLp n 2 (HalfSpace.upper n)) (g : ℝ^n → ℝ))
    (hdiv : ∀ φ : TestFunctionOn n (HalfSpace.upper n),
      (∑ i, ⟪q i, derivCoordCLM i
        (cutoffH10 (HalfSpace.isOpen_upper n) η (testFunctionToH10 φ))⟫) =
      ⟪f, baseCoordCLM
        (cutoffH10 (HalfSpace.isOpen_upper n) η (testFunctionToH10 φ))⟫) :
    ∃ F : H¹(HalfSpace.upper n), F.val (baseIndex n 1) =
      testFunctionLpTop (Ω := HalfSpace.upper n) η • q (PDE.Common.lastIndex (n := n)) ∧
      ‖F‖ ≤ (‖testFunctionLpTop (Ω := HalfSpace.upper n) η‖ + n *
        (‖testFunctionLpTop (Ω := HalfSpace.upper n) η‖ +
          ∑ i, ‖partialTestFunctionLpTop (Ω := HalfSpace.upper n) η i‖ + (n + 1) * B)) * N := by
  let M := ‖testFunctionLpTop (Ω := HalfSpace.upper n) η‖
  let S := ∑ i, ‖partialTestFunctionLpTop (Ω := HalfSpace.upper n) η i‖
  let R := M + n * (M + S + (n + 1) * B)
  have hM : 0 ≤ M := norm_nonneg _
  obtain ⟨F, hF⟩ := exists_component_H1_of_weakDivergence
    (PDE.Common.lastIndex (n := n))
    (fun i ↦ testFunctionLpTop (Ω := HalfSpace.upper n) η • q i)
    (divergenceCutoffSource η q f)
    (weakDivergence_cutoff (HalfSpace.isOpen_upper n) η q f hdiv)
    (fun k hk i ↦ (hflux k hk i).imp fun _ h ↦ h.2)
  have hsource : ‖divergenceCutoffSource η q f‖ ≤ (M + S) * N := by
    calc
      _ ≤ M * ‖f‖ + ∑ i, ‖partialTestFunctionLpTop (Ω := HalfSpace.upper n) η i‖ * ‖q i‖ :=
        norm_divergenceCutoffSource_le η q f
      _ ≤ M * N + ∑ i, ‖partialTestFunctionLpTop (Ω := HalfSpace.upper n) η i‖ * N :=
        add_le_add (mul_le_mul_of_nonneg_left hf hM)
          (Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (hq i) (norm_nonneg _))
      _ = _ := by rw [← Finset.sum_mul]; dsimp only [S]; ring
  refine ⟨F, hF, (norm_component_H1_le_of_weakDivergence (HalfSpace.isOpen_upper n)
    (PDE.Common.lastIndex (n := n)) (fun i ↦ testFunctionLpTop (Ω := HalfSpace.upper n) η • q i)
    (divergenceCutoffSource η q f) (weakDivergence_cutoff (HalfSpace.isOpen_upper n) η q f hdiv)
    (mul_nonneg hB hN) hflux F hF).trans ?_⟩
  have hbase : ‖testFunctionLpTop (Ω := HalfSpace.upper n) η •
      q (PDE.Common.lastIndex (n := n))‖ ≤ M * N :=
    (Lp.norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left (hq _) hM)
  change _ ≤ R * N
  dsimp only [R]
  linarith [mul_le_mul_of_nonneg_left hsource (Nat.cast_nonneg (α := ℝ) n)]

/-- The local monotone equation produces an `H²` representative
of `ηu`, with a constant fixed by the coefficients and cutoff. No
differentiability of the gradient or flux is a hypothesis. -/
theorem exists_localized_H2_of_monotone_weakEquation
    (A : ℝ^n → ℝ^n → ℝ^n) (K C : ℝ≥0) {m : ℝ} (hm : 0 < m)
    (hmono : ∀ x ∈ HalfSpace.upper n, ∀ z w : ℝ^n,
      m * ‖z - w‖ * ‖z - w‖ ≤ ⟪A x z - A x w, z - w⟫)
    (hvariation : ∀ x ∈ HalfSpace.upper n, ∀ y ∈ HalfSpace.upper n, ∀ z w : ℝ^n,
      ‖A y w - A x z‖ ≤ K * ‖y - x‖ * ‖z‖ + C * ‖w - z‖)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    {D : ℝ≥0} (hη : LipschitzWith D η.toFun)
    (hηbound : ∀ x ∈ HalfSpace.upper n, |η.toFun x| ≤ 1)
    (u : H¹₀(HalfSpace.upper n))
    (q : Fin n → DerivLp n 2 (HalfSpace.upper n))
    (f : DerivLp n 2 (HalfSpace.upper n))
    (hrep : ∀ᵐ x ∂domainMeasure n (HalfSpace.upper n),
      A x (Lp.euclideanTuple (fun i ↦ derivCoordCLM i u) x) = Lp.euclideanTuple q x)
    {ρ : ℝ} (hρ : 0 < ρ)
    (htest : ∀ (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n)),
      ∀ h : ℝ, 0 < h → h ≤ ρ →
        (∑ i, ⟪q i, derivCoordCLM i (localizedTangentialTest η k hk h u)⟫) =
          ⟪f, baseCoordCLM (localizedTangentialTest η k hk h u)⟫)
    (hdiv : ∀ φ : TestFunctionOn n (HalfSpace.upper n),
      (∑ i, ⟪q i, derivCoordCLM i
        (cutoffH10 (HalfSpace.isOpen_upper n) η (testFunctionToH10 φ))⟫) =
      ⟪f, baseCoordCLM
        (cutoffH10 (HalfSpace.isOpen_upper n) η (testFunctionToH10 φ))⟫) :
    ∃ V : W^{2,2}(HalfSpace.upper n),
      V.val (baseIndex n 2) = baseCoordCLM (cutoffH10 (HalfSpace.isOpen_upper n) η u) ∧
      ‖V‖ ≤ localizedH2EstimateConstant m K C D η * (‖f‖ + ‖u‖ + ∑ i, ‖q i‖) := by
  let N := ‖f‖ + ‖u‖ + ∑ i, ‖q i‖
  let M := ‖testFunctionLpTop (Ω := HalfSpace.upper n) η‖
  let T := |localizedTangentialEstimateConstant m K C η|
  let B := T + D
  let Bq := K * M * n + C * T + D
  let S := ∑ i, ‖partialTestFunctionLpTop (Ω := HalfSpace.upper n) η i‖
  let R := M + n * (M + S + (n + 1) * Bq)
  let G := localizedGradientRecoveryConstant m K C D B R η
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  have hM : 0 ≤ M := norm_nonneg _
  have hT : 0 ≤ T := abs_nonneg _
  have hB : 0 ≤ B := by positivity
  have hBq : 0 ≤ Bq := by positivity
  have hR : 0 ≤ R := by positivity
  have hqsum : 0 ≤ ∑ i, ‖q i‖ := by positivity
  have hfu : ‖f‖ + ‖u‖ ≤ N := le_add_of_nonneg_right hqsum
  have hf : ‖f‖ ≤ N := by linarith [norm_nonneg u]
  have hu : ‖u‖ ≤ N := by linarith [norm_nonneg f]
  have hq (i : Fin n) : ‖q i‖ ≤ N := by
    linarith [norm_nonneg f, norm_nonneg u,
      Finset.single_le_sum (fun j _ ↦ norm_nonneg (q j)) (Finset.mem_univ i)]
  have hd (i : Fin n) : ‖derivCoordCLM i u‖ ≤ N :=
    (wkpCoordinateCLM_norm_le (singleDerivIndex n i)
      (u : H¹(HalfSpace.upper n))).trans hu
  have htangent : localizedTangentialEstimateConstant m K C η * (‖f‖ + ‖u‖) ≤ T * N :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)).trans
      (mul_le_mul_of_nonneg_left hfu hT)
  have htuple : ‖Lp.euclideanTuple (fun i ↦ derivCoordCLM i u)‖ ≤ n * N :=
    (Lp.norm_euclideanTuple_le _).trans ((Finset.sum_le_sum fun i _ ↦ hd i).trans_eq (by simp))
  have hgrad (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n)) (i : Fin n) :
      ∃ g : DerivLp n 2 (HalfSpace.upper n), ‖g‖ ≤ B * N ∧
        HasWeakDerivativeOn (HalfSpace.upper n) [k]
          (testFunctionLpTop (Ω := HalfSpace.upper n) η • derivCoordCLM i u :
            DerivLp n 2 (HalfSpace.upper n)) (g : ℝ^n → ℝ) := by
    obtain ⟨g, hgnorm, hg⟩ := exists_localized_tangential_gradient_derivative
      A hm K.coe_nonneg C.coe_nonneg hmono hvariation η hη u q f hrep k hk hρ
      (htest k hk) i
    refine ⟨g, hgnorm.trans ?_, hg⟩
    dsimp only [B]
    linarith [mul_le_mul_of_nonneg_left (hd i) D.coe_nonneg]
  have hflux (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n)) (i : Fin n) :
      ∃ g : DerivLp n 2 (HalfSpace.upper n), ‖g‖ ≤ Bq * N ∧
        HasWeakDerivativeOn (HalfSpace.upper n) [k]
          (testFunctionLpTop (Ω := HalfSpace.upper n) η • q i :
            DerivLp n 2 (HalfSpace.upper n)) (g : ℝ^n → ℝ) := by
    obtain ⟨g, hgnorm, hg⟩ := exists_localized_tangential_flux_derivative
      A hm K.coe_nonneg C.coe_nonneg hmono hvariation η hη u q f hrep k hk hρ
      (htest k hk) i
    refine ⟨g, hgnorm.trans ?_, hg⟩
    dsimp only [Bq]
    linarith [mul_le_mul_of_nonneg_left htuple (mul_nonneg K.coe_nonneg hM),
      mul_le_mul_of_nonneg_left htangent C.coe_nonneg,
      mul_le_mul_of_nonneg_left (hq i) D.coe_nonneg]
  obtain ⟨F, hF, hFnorm⟩ := exists_normal_cutoff_flux_H1_of_weakDivergence
    η q f hBq hN hf hq hflux hdiv
  have hW := exists_localized_gradient_H1_of_normal_flux
    A K C hm hmono hvariation η hη hηbound u q hrep hB hR hN hu hq hgrad F hF hFnorm
  choose W hWbase hWnorm using hW
  obtain ⟨V, hV, hVnorm⟩ := exists_H2_cutoff_of_localized_gradient_H1 η
    (u : H¹(HalfSpace.upper n)) W hWbase
  refine ⟨V, hV, hVnorm.trans ?_⟩
  calc
    _ ≤ Fintype.card (DerivIndex n 2) *
        (‖cutoffCLM (p := 2) (Ω := HalfSpace.upper n) η‖ * N +
          ∑ i : Fin n, (G * N + ‖cutoffCLM (p := 2) (Ω := HalfSpace.upper n)
            (_root_.TestFunction.lineDerivCLM ℝ (EuclideanSpace.single i 1) η)‖ * N)) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_left hu (ContinuousLinearMap.opNorm_nonneg _))
        (Finset.sum_le_sum fun i _ ↦ add_le_add (hWnorm i)
          (mul_le_mul_of_nonneg_left hu (ContinuousLinearMap.opNorm_nonneg _)))) (Nat.cast_nonneg _)
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      change _ = localizedH2EstimateConstant m K C D η * N
      unfold localizedH2EstimateConstant
      dsimp only [G, R, B, Bq, M, T, S]
      ring

end PDE.Elliptic.Regularity.Quasilinear
