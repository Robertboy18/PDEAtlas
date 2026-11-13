/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Integer.ClassicalRepresentation
public import PDE.Spaces.Sobolev.GraphSpace.Topology.Completeness

/-!
# The amplitude embedding at the zero-derivative threshold

Fourier integrability gives a bounded continuous representative when
`n < 2 k`. A closed graph argument makes its dependence on the Sobolev datum
continuous in the uniform norm. In particular H² controls amplitude in
dimensions below four, without requiring the stronger C¹ threshold.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev BoundedContinuousFunction Topology SchwartzMap

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

variable {n k : ℕ}

/-- The zero-moment Fourier construction gives a bounded continuous
representative at the strict zero-derivative Sobolev threshold. -/
theorem exists_bounded_sobolev_representative (hk : (n : ℝ) < 2 * (k : ℝ)) (u : W^{k,2}(ℝ^n)) :
    ∃ v : ℝ^n →ᵇ ℝ, (v : ℝ^n → ℝ) =ᵐ[volume] baseRepresentative u := by
  obtain ⟨g, hg, hmom⟩ := PDE.Analysis.Fourier.exists_fourier_memL1_moments_of_memSobolev
      (r := 0) (by simpa using hk) (Fractional.ofWkpSpace u).memSobolev_toDistr
  obtain ⟨v, _, hv⟩ := PDE.Analysis.Fourier.exists_contDiff_representative_of_fourier_eq g hg hmom
  have hae : (v : ℝ^n → ℂ) =ᵐ[volume]
      Fractional.toL2Fun (Nat.cast_nonneg k) (Fractional.ofWkpSpace u) := by
    apply ae_eq_of_integral_schwartz_smul_eq v.continuous.locallyIntegrable
      ((Lp.memLp _).locallyIntegrable (by norm_num))
    intro φ
    rw [hv, Fractional.toDistr_eq_toL2Fun (Nat.cast_nonneg k), Lp.toTemperedDistribution_apply]
  refine ⟨Complex.reCLM.compLeftContinuousBounded (ℝ^n) v, ?_⟩
  filter_upwards [hae, Fractional.reOfL2_toL2Fun_ofWkpSpace u] with x hx hy
  exact (congrArg Complex.re hx).trans hy

/-- A choice of the unique bounded continuous Sobolev representative. -/
def boundedSobolevRepresentative (hk : (n : ℝ) < 2 * (k : ℝ))
    (u : W^{k,2}(ℝ^n)) : ℝ^n →ᵇ ℝ :=
  (exists_bounded_sobolev_representative hk u).choose

/-- The chosen point values realize the base weak-derivative row. -/
theorem boundedSobolevRepresentative_ae (hk : (n : ℝ) < 2 * (k : ℝ)) (u : W^{k,2}(ℝ^n)) :
    (boundedSobolevRepresentative hk u : ℝ^n → ℝ) =ᵐ[volume] baseRepresentative u :=
  (exists_bounded_sobolev_representative hk u).choose_spec

/-- Uniqueness of continuous representatives makes the choice linear. -/
def boundedSobolevRepresentativeLinearMap (hk : (n : ℝ) < 2 * (k : ℝ)) :
    W^{k,2}(ℝ^n) →ₗ[ℝ] (ℝ^n →ᵇ ℝ) where
  toFun := boundedSobolevRepresentative hk
  map_add' u v := by
    apply DFunLike.coe_injective
    apply map_add_of_continuous_ae_eq
      (fun w ↦ (boundedSobolevRepresentative hk w).continuous)
      (boundedSobolevRepresentative_ae hk)
    simpa only [domainMeasure, Measure.restrict_univ] using baseRepresentative_add_ae u v
  map_smul' c u := by
    apply DFunLike.coe_injective
    apply map_smul_of_continuous_ae_eq
      (fun w ↦ (boundedSobolevRepresentative hk w).continuous)
      (boundedSobolevRepresentative_ae hk)
    simpa only [domainMeasure, Measure.restrict_univ] using baseRepresentative_smul_ae c u

/-- Sobolev convergence and uniform convergence determine the same point values. -/
theorem boundedSobolevRepresentativeLinearMap_seqClosedGraph (hk : (n : ℝ) < 2 * (k : ℝ))
    (u : ℕ → W^{k,2}(ℝ^n)) (U : W^{k,2}(ℝ^n)) (F : ℝ^n →ᵇ ℝ) (hu : Tendsto u atTop (𝓝 U))
    (hF : Tendsto (boundedSobolevRepresentativeLinearMap hk ∘ u) atTop (𝓝 F)) :
    F = boundedSobolevRepresentativeLinearMap hk U := by
  have hbase := tendstoInMeasure_of_tendsto_Lp ((wkpBaseCoordinateCLM.continuous.tendsto U).comp hu)
  obtain ⟨σ, hσ, hlim⟩ := hbase.exists_seq_tendsto_ae
  have hrows : ∀ᵐ x ∂volume, ∀ j : ℕ,
      boundedSobolevRepresentativeLinearMap hk (u j) x = baseRepresentative (u j) x :=
    ae_all_iff.mpr fun j ↦ boundedSobolevRepresentative_ae hk (u j)
  apply DFunLike.coe_injective
  apply Measure.eq_of_ae_eq (μ := volume) _ F.continuous
    (boundedSobolevRepresentativeLinearMap hk U).continuous
  have hlim' := hlim
  simp only [domainMeasure, Measure.restrict_univ] at hlim'
  filter_upwards [hlim', hrows, boundedSobolevRepresentative_ae hk U] with x hx hr hU
  have hFx : Tendsto (fun j ↦ boundedSobolevRepresentativeLinearMap hk (u (σ j)) x)
      atTop (𝓝 (F x)) :=
    (((BoundedContinuousFunction.evalCLM ℝ x).continuous.tendsto F).comp hF).comp hσ.tendsto_atTop
  have heq : F x = baseRepresentative U x :=
    tendsto_nhds_unique hFx (hx.congr (fun j ↦ (hr (σ j)).symm))
  exact heq.trans hU.symm

/-- The amplitude representative depends continuously on the Sobolev datum. -/
def boundedSobolevRepresentativeCLM (hk : (n : ℝ) < 2 * (k : ℝ)) :
    W^{k,2}(ℝ^n) →L[ℝ] (ℝ^n →ᵇ ℝ) :=
  ContinuousLinearMap.ofSeqClosedGraph (boundedSobolevRepresentativeLinearMap_seqClosedGraph hk)

/-- Lowering the Sobolev order preserves the continuous point values. -/
theorem boundedSobolevRepresentativeCLM_lowerOrderCLM {j : ℕ} (hj : (n : ℝ) < 2 * (j : ℝ))
    (hk : (n : ℝ) < 2 * ((k : ℝ) - 1)) (hjk : j ≤ k) (u : W^{k,2}(ℝ^n)) :
    boundedSobolevRepresentativeCLM hj (lowerOrderCLM hjk u) = classicalRepresentativeCLM hk u := by
  apply DFunLike.coe_injective
  apply eq_classicalRepresentativeCLM_of_ae_eq hk u
    (boundedSobolevRepresentativeCLM hj (lowerOrderCLM hjk u)).continuous
  change (boundedSobolevRepresentative hj (lowerOrderCLM hjk u) : ℝ^n → ℝ)
    =ᵐ[volume] baseRepresentative u
  simpa only [baseRepresentative_lowerOrderCLM] using
    boundedSobolevRepresentative_ae hj (lowerOrderCLM hjk u)

end PDE.Hyperbolic.NonlinearWave.Cauchy
