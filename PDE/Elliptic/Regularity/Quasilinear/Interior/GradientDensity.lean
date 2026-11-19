/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Elliptic.Regularity.Quasilinear.Interior.H2
public import PDE.Analysis.Calculus.Gradient.HessianBounds
public import PDE.Spaces.Sobolev.Calculus.Composition.Flux.L2

/-!
# Interior H² regularity for autonomous gradient densities

This is the interior assertion of Evans §8.3.1, Theorem 1(i), using
Fréchet derivatives of the density and the literal weak equation
against every `H¹₀` test. The input solution is arbitrary `H¹`.
Only boundedness and openness of the ambient domain are needed.

The Hessian bounds imply strong monotonicity and Lipschitzness of the
gradient. Boundedness of the domain makes its possibly nonzero
constant part square-integrable. No normalization of the density or its
gradient at zero enters either interior estimate.
-/

@[expose] public noncomputable section

namespace PDE.Elliptic.Regularity.Quasilinear

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal NNReal RealInnerProductSpace Sobolev Gradient

variable {n : ℕ} {Ω V : Set (ℝ^n)}

/-- Autonomous `C²` density hypotheses give interior `H²`
regularity of every `H¹` weak solution. The constant precedes the density,
solution and source. All test integrals are integrable, the entire
order-one restriction is preserved, and the second-derivative estimate
uses only the original gradient and source norms. -/
theorem exists_interior_H2_of_gradientDensity
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hV : IsOpen V)
    (hVc : IsCompact (closure V)) (hVΩ : closure V ⊆ Ω)
    {θ : ℝ} (hθ : 0 < θ) (Λ : ℝ≥0) :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : ℝ^n → ℝ),
      ContDiff ℝ 2 L →
      (∀ p, ‖fderiv ℝ (fderiv ℝ L) p‖ ≤ Λ) →
      (∀ p z, θ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ L) p z z) →
      ∀ (u : H¹(Ω)) (f : DerivLp n 2 Ω),
      (∀ v : H¹₀(Ω),
        (∫ x, ⟪∇ L (∇ u x), ∇ (v : H¹(Ω)) x⟫
          ∂domainMeasure n Ω) =
        ∫ x, f x * baseCoordCLM v x ∂domainMeasure n Ω) →
      ∃ W : W^{2,2}(V),
        lowerOrderCLM (by omega : 1 ≤ 2) W =
          restrictCLM hV.measurableSet (subset_closure.trans hVΩ) u ∧
        ‖W‖ ≤ K * (‖u‖ + ‖f‖) ∧
        (∑ i : Fin n, ∑ j : Fin n, ‖W.val (pairDerivIndex n i j)‖) ≤
          K * (‖∇ u‖ + ‖f‖) ∧
        ∀ v : H¹₀(Ω),
          Integrable (fun x ↦
            ⟪∇ L (∇ u x), ∇ (v : H¹(Ω)) x⟫)
            (domainMeasure n Ω) ∧
          Integrable (fun x ↦ f x * baseCoordCLM v x) (domainMeasure n Ω) := by
  obtain ⟨K, hK, hreg⟩ :=
    exists_interior_H2_of_monotone_weakEquation (C := (Λ : ℝ)) hΩ hV hVc hVΩ hθ
  refine ⟨K, hK, ?_⟩
  intro L hL hbound hcoercive u f hweak
  have hLip : LipschitzWith Λ (∇ L) :=
    PDE.Analysis.lipschitzWith_gradient_of_hessian_bound hL hbound
  obtain ⟨q, hq, hpair⟩ := exists_L2_flux_pairing_of_lipschitz hbounded hLip u
  have hweak' (v : H¹₀(Ω)) :
      (∑ i, ⟪q i, derivCoordCLM i v⟫) = ⟪f, baseCoordCLM v⟫ := by
    rw [← (hpair v).2, hweak v, L2.inner_def]
    simp only [RCLike.inner_apply, RCLike.conj_to_real, mul_comm]
  obtain ⟨W, hW, hnorm, hsecond⟩ := hreg (∇ L)
    (PDE.Analysis.strongMonotonicity_gradient_of_hessian_bound hL hcoercive)
    hLip.norm_sub_le u q f hq hweak'
  refine ⟨W, hW, hnorm, hsecond, fun v ↦ ⟨(hpair v).1, ?_⟩⟩
  simpa only [RCLike.inner_apply, RCLike.conj_to_real, mul_comm] using
    L2.integrable_inner (𝕜 := ℝ) f (baseCoordCLM v)

/-- Every compact subset has an open interior neighbourhood on which the
density theorem applies. The neighbourhood and estimate constant are
chosen before the density, solution and source. Empty and disconnected
compact sets require no special convention. -/
theorem exists_H2_near_compact_of_gradientDensity
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    {S : Set (ℝ^n)} (hS : IsCompact S) (hSΩ : S ⊆ Ω)
    {θ : ℝ} (hθ : 0 < θ) (Λ : ℝ≥0) :
    ∃ (V : Set (ℝ^n)) (hV : IsOpen V) (hVΩ : closure V ⊆ Ω),
      S ⊆ V ∧ IsCompact (closure V) ∧
      ∃ K : ℝ, 0 < K ∧ ∀ (L : ℝ^n → ℝ),
        ContDiff ℝ 2 L →
        (∀ p, ‖fderiv ℝ (fderiv ℝ L) p‖ ≤ Λ) →
        (∀ p z, θ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ L) p z z) →
        ∀ (u : H¹(Ω)) (f : DerivLp n 2 Ω),
        (∀ v : H¹₀(Ω),
          (∫ x, ⟪∇ L (∇ u x), ∇ (v : H¹(Ω)) x⟫
            ∂domainMeasure n Ω) =
          ∫ x, f x * baseCoordCLM v x ∂domainMeasure n Ω) →
        ∃ W : W^{2,2}(V),
          lowerOrderCLM (by omega : 1 ≤ 2) W =
            restrictCLM hV.measurableSet (subset_closure.trans hVΩ) u ∧
          ‖W‖ ≤ K * (‖u‖ + ‖f‖) ∧
          (∑ i : Fin n, ∑ j : Fin n, ‖W.val (pairDerivIndex n i j)‖) ≤
            K * (‖∇ u‖ + ‖f‖) := by
  obtain ⟨V, hV, hSV, hVΩ, hVc⟩ :=
    exists_open_between_and_isCompact_closure hS hΩ hSΩ
  obtain ⟨K, hK, hreg⟩ := exists_interior_H2_of_gradientDensity
    hΩ hbounded hV hVc hVΩ hθ Λ
  refine ⟨V, hV, hVΩ, hSV, hVc, K, hK, ?_⟩
  intro L hL hbound hcoercive u f hweak
  obtain ⟨W, hW, hnorm, hsecond, _⟩ := hreg L hL hbound hcoercive u f hweak
  exact ⟨W, hW, hnorm, hsecond⟩

end PDE.Elliptic.Regularity.Quasilinear
