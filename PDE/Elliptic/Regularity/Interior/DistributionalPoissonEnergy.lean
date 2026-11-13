/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.RealDistributionalPoisson
public import PDE.Elliptic.Regularity.Interior.PoissonWeakForm
public import PDE.Elliptic.Regularity.Interior.PoissonEnergy
import PDE.Spaces.Sobolev.Calculus.Differentiation.ClassicalToWeak

/-!
# Energy estimates from locally L² distributional data

The local real Poisson theorem constructs W²,² membership from `Δu = f`
and locally L² data. Its H¹ restriction satisfies the weak equation with
load `-f`; this equation is derived from the original compact-test identity.
Testing with a squared cutoff therefore bounds the local gradient using only
the L² norms of the data. No first derivative or H¹ bound is assumed.
-/

@[expose] public noncomputable section

open scoped Sobolev

open MeasureTheory Set TopologicalSpace
open SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Distributions InnerProductSpace

namespace PDE.Elliptic.Interior

variable {n : ℕ}

/-- Locally L² distributional Poisson data give a W²,² representative
whose H¹ restriction satisfies the energy-test equation. The forcing class
represents the given f; the variational load is its negative. The subdomain
has compact closure inside Ω but no boundary regularity is required. -/
theorem exists_wkpSpaceOn_two_poisson_weakForm
    {Ω : Opens (ℝ^n)} {u f : ℝ^n → ℝ}
    (hu : ∀ K : Set (ℝ^n), IsCompact K → K ⊆ Ω → MemLp u 2 (volume.restrict K))
    (hf : ∀ K : Set (ℝ^n), IsCompact K → K ⊆ Ω → MemLp f 2 (volume.restrict K))
    (hweak : ∀ φ : 𝓓(Ω, ℝ),
      (∫ x, u x * laplacian (φ : ℝ^n → ℝ) x) = ∫ x, f x * φ x)
    {V : Set (ℝ^n)} (hV : IsOpen V) (hcompact : IsCompact (closure V))
    (hVΩ : closure V ⊆ Ω) :
    ∃ U : W^{2,2}(V), ∃ F : DerivLp n 2 V,
      baseRepresentative U =ᵐ[domainMeasure n V] u ∧
      (F : ℝ^n → ℝ) =ᵐ[domainMeasure n V] f ∧
      (∑ i : Fin n, (U : WkpAmbientOn n 2 2 V) (topPureDerivIndex n 2 i)) = F ∧
      ∀ v : H¹₀(V),
        (∑ i : Fin n, ⟪((lowerOrderCLM (by norm_num : 1 ≤ 2) U :
          H¹(V)) : WkpAmbientOn n 1 2 V) (singleDerivIndex n i),
          derivCoordCLM i v⟫_ℝ) = ⟪-F, baseCoordCLM v⟫_ℝ := by
  obtain ⟨U, hU⟩ :=
    exists_wkpSpaceOn_two_ae_eq_of_integral_laplacian_eq hu hf hweak hV hcompact hVΩ
  replace hU : baseRepresentative U =ᵐ[domainMeasure n V] u := by
    simpa only [baseRepresentative] using hU
  have hfV : MemLp f 2 (domainMeasure n V) :=
    (hf (closure V) hcompact hVΩ).mono_measure
      (Measure.restrict_mono subset_closure le_rfl)
  let F : DerivLp n 2 V := hfV.toLp f
  have hF : (F : ℝ^n → ℝ) =ᵐ[domainMeasure n V] f := hfV.coeFn_toLp
  have htest : ∀ φ : TestFunctionOn n V,
      (∫ x, baseRepresentative U x * laplacian φ.1.toFun x ∂domainMeasure n V) =
        ∫ x, (F : ℝ^n → ℝ) x * φ.1.toFun x ∂domainMeasure n V := by
    intro φ
    let ψ : 𝓓(Ω, ℝ) := {
      toFun := φ.1.toFun
      contDiff' := φ.1.contDiff
      hasCompactSupport' := φ.1.hasCompactSupport
      tsupport_subset' := φ.2.trans (subset_closure.trans hVΩ)
    }
    have hΔ : tsupport (laplacian φ.1.toFun) ⊆ V := by
      apply Subset.trans ?_ φ.2
      apply closure_minimal _ (isClosed_tsupport φ.1.toFun)
      intro x hx
      by_contra hxφ
      apply hx
      unfold laplacian
      apply Finset.sum_eq_zero
      intro i _
      apply image_eq_zero_of_notMem_tsupport
      intro hxderiv
      apply hxφ
      exact (show tsupport (∂[i] (∂[i] φ.1.toFun)) ⊆
          tsupport φ.1.toFun by
        simpa only [iteratedPartialDeriv] using
          tsupport_iteratedPartialDeriv_subset_tsupport [i, i] φ.1.toFun) hxderiv
    calc
      _ = ∫ x, u x * laplacian φ.1.toFun x ∂domainMeasure n V := by
        apply integral_congr_ae
        filter_upwards [hU] with x hx
        rw [hx]
      _ = ∫ x, u x * laplacian φ.1.toFun x :=
        integral_mul_eq_global_of_tsupport_subset _ _ hΔ
      _ = ∫ x, f x * φ.1.toFun x := hweak ψ
      _ = ∫ x, f x * φ.1.toFun x ∂domainMeasure n V :=
        (integral_mul_eq_global_of_tsupport_subset _ _ φ.2).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [hF] with x hx
        rw [hx]
  refine ⟨U, F, hU, hF, laplacian_rows_eq_of_integral_laplacian_eq hV U F htest, ?_⟩
  apply poisson_weakForm_of_integral_laplacian_eq
    (lowerOrderCLM (by norm_num : 1 ≤ 2) U) F
  simpa only [baseRepresentative_lowerOrderCLM] using htest

/-- A distributional solution with only local L² data admits a Sobolev
representative satisfying the scaled cutoff energy estimate. The right-hand
side uses exactly the L² seminorms of u and f on V; their finiteness and the
weak gradient are consequences of the hypotheses. -/
theorem exists_wkpSpaceOn_two_cutoff_gradient_sq_le
    {Ω : Opens (ℝ^n)} {u f : ℝ^n → ℝ}
    (hu : ∀ K : Set (ℝ^n), IsCompact K → K ⊆ Ω → MemLp u 2 (volume.restrict K))
    (hf : ∀ K : Set (ℝ^n), IsCompact K → K ⊆ Ω → MemLp f 2 (volume.restrict K))
    (hweak : ∀ φ : 𝓓(Ω, ℝ),
      (∫ x, u x * laplacian (φ : ℝ^n → ℝ) x) = ∫ x, f x * φ x)
    {V : Set (ℝ^n)} (hV : IsOpen V) (hcompact : IsCompact (closure V))
    (hVΩ : closure V ⊆ Ω) :
    ∃ U : W^{2,2}(V),
      baseRepresentative U =ᵐ[domainMeasure n V] u ∧
      ∀ (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)), tsupport η.toFun ⊆ V →
        ‖testFunctionLpTop (Ω := V) η‖ ≤ 1 → ∀ τ : ℝ, 0 < τ →
        (∑ i : Fin n, ‖testFunctionLpTop (Ω := V) η •
          ((lowerOrderCLM (by norm_num : 1 ≤ 2) U : H¹(V)) :
            WkpAmbientOn n 1 2 V) (singleDerivIndex n i)‖ ^ 2) ≤
          τ ^ 2 * (eLpNorm f 2 (domainMeasure n V)).toReal ^ 2 +
          (τ⁻¹ ^ 2 + 4 * (∑ i : Fin n,
            ‖partialTestFunctionLpTop (Ω := V) η i‖ ^ 2)) *
              (eLpNorm u 2 (domainMeasure n V)).toReal ^ 2 := by
  obtain ⟨U, F, hU, hF, _, henergy⟩ :=
    exists_wkpSpaceOn_two_poisson_weakForm hu hf hweak hV hcompact hVΩ
  refine ⟨U, hU, ?_⟩
  intro η hη hηnorm τ hτ
  have h := poisson_cutoff_gradient_sq_le_scaled hV
    (lowerOrderCLM (by norm_num : 1 ≤ 2) U) (-F) henergy η hη hηnorm hτ
  have hFnorm : ‖-F‖ = (eLpNorm f 2 (domainMeasure n V)).toReal := by
    rw [norm_neg, Lp.norm_def, eLpNorm_congr_ae hF]
  have hUnorm :
      ‖((lowerOrderCLM (by norm_num : 1 ≤ 2) U : H¹(V)) :
        WkpAmbientOn n 1 2 V) (baseIndex n 1)‖ =
          (eLpNorm u 2 (domainMeasure n V)).toReal := by
    rw [Lp.norm_def]
    change (eLpNorm (baseRepresentative (lowerOrderCLM (by norm_num : 1 ≤ 2) U))
      2 (domainMeasure n V)).toReal = _
    rw [baseRepresentative_lowerOrderCLM, eLpNorm_congr_ae hU]
  simpa only [hFnorm, hUnorm] using h

end PDE.Elliptic.Interior
