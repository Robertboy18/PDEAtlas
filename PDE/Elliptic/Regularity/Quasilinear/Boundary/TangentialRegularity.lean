/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Quasilinear.Boundary.LocalizedDerivatives
public import PDE.Spaces.Sobolev.Calculus.Product.LocalizedMixed
public import PDE.Spaces.Sobolev.GraphSpace.Representatives.FirstOrder
import PDE.Analysis.MeasureTheory.Lp.NormDomination

/-!
# Tangential regularity from the nonlinear weak equation

Localized tangential energy bounds give all tangential derivatives of both the
gradient and the flux. Commutation of the weak derivatives of `ηu` then supplies
the missing normal derivative of every tangential gradient component. The result
is a family of `H¹` parameters for nonlinear normal-flux recovery.
-/

@[expose] public noncomputable section

open scoped Sobolev

open TopologicalSpace
open scoped Distributions

namespace PDE.Elliptic.Regularity.Quasilinear

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity SobolevSpace.GraphSpace.DifferenceQuotient
open scoped ENNReal NNReal RealInnerProductSpace

variable {n : ℕ} [Fact (0 < n)]

/-- Every localized gradient component has the estimated tangential weak derivative.
Only the localized tests for sufficiently small positive steps are used. -/
theorem exists_localized_tangential_gradient_derivative
    (A : ℝ^n → ℝ^n → ℝ^n) {m K C : ℝ}
    (hm : 0 < m) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hmono : ∀ x ∈ HalfSpace.upper n, ∀ z w : ℝ^n,
      m * ‖z - w‖ * ‖z - w‖ ≤ ⟪A x z - A x w, z - w⟫)
    (hvariation : ∀ x ∈ HalfSpace.upper n, ∀ y ∈ HalfSpace.upper n, ∀ z w : ℝ^n,
      ‖A y w - A x z‖ ≤ K * ‖y - x‖ * ‖z‖ + C * ‖w - z‖)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) {D : ℝ≥0} (hη : LipschitzWith D η.toFun)
    (u : H¹₀(HalfSpace.upper n))
    (Q : Fin n → DerivLp n 2 (HalfSpace.upper n)) (f : DerivLp n 2 (HalfSpace.upper n))
    (hrep : ∀ᵐ x ∂domainMeasure n (HalfSpace.upper n),
      A x (Lp.euclideanTuple (fun i ↦ derivCoordCLM i u) x) = Lp.euclideanTuple Q x)
    (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n)) {ρ : ℝ} (hρ : 0 < ρ)
    (hu : ∀ h : ℝ, 0 < h → h ≤ ρ →
      (∑ i, ⟪Q i, derivCoordCLM i (localizedTangentialTest η k hk h u)⟫) =
        ⟪f, baseCoordCLM (localizedTangentialTest η k hk h u)⟫)
    (i : Fin n) :
    ∃ g : DerivLp n 2 (HalfSpace.upper n),
      ‖g‖ ≤ localizedTangentialEstimateConstant m K C η * (‖f‖ + ‖u‖) +
        D * ‖derivCoordCLM i u‖ ∧
      HasWeakDerivativeOn (HalfSpace.upper n) [k]
        (testFunctionLpTop (Ω := HalfSpace.upper n) η • derivCoordCLM i u :
          DerivLp n 2 (HalfSpace.upper n))
        (g : ℝ^n → ℝ) := by
  apply exists_localized_tangential_weakDerivative k hk _ η.toFun hη
    (testFunctionLpTop_apply_ae η) _ hρ
  intro h hh hsmall
  exact (norm_weighted_tangential_coordinate_le _ k hk h
    (fun j ↦ derivCoordCLM j u) i).trans
      (norm_weighted_tangential_gradient_le A hm hK hC hmono hvariation η u Q f hrep
        k hk hh (hu h hh hsmall))

/-- The nonlinear flux has localized tangential weak derivatives. Its quotient
bound follows from the gradient estimate and the flux's spatial and state bounds. -/
theorem exists_localized_tangential_flux_derivative
    (A : ℝ^n → ℝ^n → ℝ^n) {m K C : ℝ}
    (hm : 0 < m) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hmono : ∀ x ∈ HalfSpace.upper n, ∀ z w : ℝ^n,
      m * ‖z - w‖ * ‖z - w‖ ≤ ⟪A x z - A x w, z - w⟫)
    (hvariation : ∀ x ∈ HalfSpace.upper n, ∀ y ∈ HalfSpace.upper n, ∀ z w : ℝ^n,
      ‖A y w - A x z‖ ≤ K * ‖y - x‖ * ‖z‖ + C * ‖w - z‖)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) {D : ℝ≥0} (hη : LipschitzWith D η.toFun)
    (u : H¹₀(HalfSpace.upper n))
    (Q : Fin n → DerivLp n 2 (HalfSpace.upper n)) (f : DerivLp n 2 (HalfSpace.upper n))
    (hrep : ∀ᵐ x ∂domainMeasure n (HalfSpace.upper n),
      A x (Lp.euclideanTuple (fun i ↦ derivCoordCLM i u) x) = Lp.euclideanTuple Q x)
    (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n)) {ρ : ℝ} (hρ : 0 < ρ)
    (hu : ∀ h : ℝ, 0 < h → h ≤ ρ →
      (∑ i, ⟪Q i, derivCoordCLM i (localizedTangentialTest η k hk h u)⟫) =
        ⟪f, baseCoordCLM (localizedTangentialTest η k hk h u)⟫)
    (i : Fin n) :
    ∃ g : DerivLp n 2 (HalfSpace.upper n),
      ‖g‖ ≤ K * ‖testFunctionLpTop (Ω := HalfSpace.upper n) η‖ *
          ‖Lp.euclideanTuple (fun j ↦ derivCoordCLM j u)‖ +
        C * (localizedTangentialEstimateConstant m K C η * (‖f‖ + ‖u‖)) +
        D * ‖Q i‖ ∧
      HasWeakDerivativeOn (HalfSpace.upper n) [k]
        (testFunctionLpTop (Ω := HalfSpace.upper n) η • Q i : DerivLp n 2 (HalfSpace.upper n))
        (g : ℝ^n → ℝ) := by
  let a := testFunctionLpTop (Ω := HalfSpace.upper n) η
  have ha : ∀ᵐ x ∂domainMeasure n (HalfSpace.upper n), |a x| ≤ ‖a‖ := by
    simpa only [Real.norm_eq_abs] using Lp.norm_apply_ae_le a
  apply exists_localized_tangential_weakDerivative k hk a η.toFun hη
    (testFunctionLpTop_apply_ae η) _ hρ
  intro h hh hsmall
  apply (norm_weighted_tangential_coordinate_le a k hk h Q i).trans
  apply (norm_weighted_tangential_flux_le A hK hC (norm_nonneg a) hvariation
    _ Q hrep a ha k hk hh).trans
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (norm_weighted_tangential_gradient_le A hm hK hC hmono hvariation η u Q f hrep
      k hk hh (hu h hh hsmall)) hC)

/-- All tangential gradient components are `H¹` functions after localization.
The normal derivative is obtained by commuting derivatives of `ηu`, including its
cutoff corrections. This construction also covers an empty tangential family in `n = 1`. -/
theorem exists_localized_tangential_gradient_H1
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (u : H¹₀(HalfSpace.upper n))
    (hderiv : ∀ k : Fin n, k ≠ PDE.Common.lastIndex (n := n) → ∀ i : Fin n,
      ∃ g : DerivLp n 2 (HalfSpace.upper n),
        HasWeakDerivativeOn (HalfSpace.upper n) [k]
          (testFunctionLpTop (Ω := HalfSpace.upper n) η • derivCoordCLM i u :
          DerivLp n 2 (HalfSpace.upper n))
          (g : ℝ^n → ℝ))
    (i : Fin n) (hi : i ≠ PDE.Common.lastIndex (n := n)) :
    ∃ W : H¹(HalfSpace.upper n),
      W.val (baseIndex n 1) = testFunctionLpTop (Ω := HalfSpace.upper n) η • derivCoordCLM i u := by
  have hex (k : Fin n) : ∃ g : DerivLp n 2 (HalfSpace.upper n),
      HasWeakDerivativeOn (HalfSpace.upper n) [k]
        (testFunctionLpTop (Ω := HalfSpace.upper n) η • derivCoordCLM i u :
          DerivLp n 2 (HalfSpace.upper n))
        (g : ℝ^n → ℝ) := by
    by_cases hk : k = PDE.Common.lastIndex (n := n)
    · obtain ⟨g, hg⟩ := hderiv i hi k
      obtain ⟨v, _, hv⟩ := exists_localized_mixed_weakDerivative η
        (u : H¹(HalfSpace.upper n)) i k g hg
      exact ⟨v, hv⟩
    · exact hderiv k hk i
  choose df hdf using hex
  obtain ⟨W, hW, _⟩ := exists_of_weakDerivative_coordinates
    (testFunctionLpTop (Ω := HalfSpace.upper n) η • derivCoordCLM i u) df hdf
  exact ⟨W, hW⟩

end PDE.Elliptic.Regularity.Quasilinear
