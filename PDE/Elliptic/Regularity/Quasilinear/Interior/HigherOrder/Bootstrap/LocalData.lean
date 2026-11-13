/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Quasilinear.Interior.HigherOrder.Bootstrap.DivergenceForcing
public import PDE.Elliptic.Regularity.Interior.Schauder.HigherOrder.HolderCalculus
public import PDE.Spaces.Sobolev.Calculus.Differentiation.LocalSobolev
import PDE.Spaces.Sobolev.Calculus.Differentiation.Representative

/-!
# Local data for the autonomous bootstrap

On a relatively compact subdomain, C¹ functions give Sobolev elements:
the principal coefficients lie in W¹,∞ and the forcing lies in H¹.
Their classical weak flux equation becomes the bilinear equation required by
the interior estimates. Compactness supplies all Hölder constants locally.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev ENNReal NNReal InnerProductSpace

namespace PDE.Elliptic.Regularity.Quasilinear.Bootstrap

variable {n : ℕ} {Ω V : Set ℝ^n}

/-- Choose a common Hölder constant for a finite family. -/
theorem exists_common_holder_constant {I E F : Type*} [Finite I]
    [PseudoEMetricSpace E] [PseudoEMetricSpace F] {s : Set E} {γ : ℝ≥0}
    {f : I → E → F} (h : ∀ i, ∃ K, HolderOnWith K γ (f i) s) :
    ∃ K, ∀ i, HolderOnWith K γ (f i) s := by
  classical
  let := Fintype.ofFinite I
  choose K hK using h
  refine ⟨∑ i, K i, fun i x hx y hy ↦ ?_⟩
  exact (hK i x hx y hy).trans (mul_le_mul_of_nonneg_right
    (ENNReal.coe_le_coe.mpr (Finset.single_le_sum (fun _ _ ↦ zero_le)
      (Finset.mem_univ i))) zero_le)

/-- Coordinate Hölder estimates give a Hölder estimate for the whole field. -/
theorem exists_holder_pi {I E : Type*} [Fintype I] [PseudoEMetricSpace E]
    {s : Set E} {γ : ℝ≥0} {f : E → I → ℝ}
    (h : ∀ i, ∃ K, HolderOnWith K γ (fun x ↦ f x i) s) :
    ∃ K, HolderOnWith K γ f s := by
  obtain ⟨K, hK⟩ := exists_common_holder_constant h
  exact ⟨K, fun _ hx _ hy ↦ edist_pi_le_iff.mpr fun i ↦ hK i _ hx _ hy⟩

/-- Interior C¹ data have Sobolev realizations satisfying the given equation.
The state receives no boundary condition. -/
theorem exists_sobolev_realization_of_local_flux
    (hΩ : IsOpen Ω) {a : Fin n → Fin n → ℝ^n → ℝ}
    {f : Fin n → ℝ^n → ℝ} {v : ℝ^n → ℝ}
    (ha : ∀ i j, ContDiffOn ℝ 1 (a i j) Ω)
    (hf : ∀ i, ContDiffOn ℝ 1 (f i) Ω) (hv : ContDiffOn ℝ 1 v Ω)
    (heq : HasZeroWeakDivergenceOn Ω
      (fun i x ↦ (∑ j, a i j x * (∂[j] v) x) - f i x))
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVΩ : closure V ⊆ Ω) :
    ∃ (A : Fin n → Fin n → W^{1,∞}(V)) (F : Fin n → H¹(V)) (u : H¹(V)),
      (∀ i j, (wkpBaseCoordinateCLM (A i j) : ℝ^n → ℝ)
        =ᵐ[domainMeasure n V] a i j) ∧
      (∀ i, (wkpBaseCoordinateCLM (F i) : ℝ^n → ℝ)
        =ᵐ[domainMeasure n V] f i) ∧
      (wkpBaseCoordinateCLM u : ℝ^n → ℝ) =ᵐ[domainMeasure n V] v ∧
      ∀ w : H¹₀(V), interiorVariableCoeffForm
        (multiplicationCoefficientOperator (fun i j ↦ wkpBaseCoordinateCLM (A i j)))
        u w = ∑ i, ⟪wkpBaseCoordinateCLM (F i), derivCoordCLM i w⟫_ℝ := by
  choose A hA using fun i j ↦
    isLocallyWkpOn_of_contDiffOn hΩ (ha i j) ∞ V hV hVc hVΩ
  choose F hF using fun i ↦
    isLocallyWkpOn_of_contDiffOn hΩ (hf i) 2 V hV hVc hVΩ
  obtain ⟨u, hu⟩ := isLocallyWkpOn_of_contDiffOn hΩ hv 2 V hV hVc hVΩ
  let hsub : V ⊆ Ω := subset_closure.trans hVΩ
  refine ⟨A, F, u, hA, hF, hu, ?_⟩
  exact interiorVariableCoeffForm_eq_of_local_flux _ u _ a f v hA hF
    (wkpCoordinate_ae_eq_partialDeriv_of_contDiffOn hV u (hv.mono hsub) hu)
    (heq.mono hsub)

/-- Pointwise ellipticity passes to the L∞ representatives. -/
theorem aeUniformlyElliptic_of_representatives
    (hΩ : IsOpen Ω) {A : Fin n → Fin n → DerivLp n ∞ Ω}
    {a : Fin n → Fin n → ℝ^n → ℝ}
    (hA : ∀ i j, (A i j : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] a i j)
    {θ : ℝ} (hθ : 0 < θ)
    (hell : ∀ x ∈ Ω, ∀ ξ : Fin n → ℝ,
      θ * ∑ i, ξ i * ξ i ≤ ∑ i, ∑ j, a i j x * ξ j * ξ i) :
    AEUniformlyElliptic A θ := by
  refine ⟨hθ, ?_⟩
  filter_upwards [ae_all_iff.mpr (fun i ↦ ae_all_iff.mpr (hA i)),
    ae_restrict_mem hΩ.measurableSet] with x hx hmem
  simpa only [hx] using hell x hmem

end PDE.Elliptic.Regularity.Quasilinear.Bootstrap
