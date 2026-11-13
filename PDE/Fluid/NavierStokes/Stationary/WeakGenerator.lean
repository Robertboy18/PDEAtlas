/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Stationary.WeakRegularity
public import PDE.Parabolic.Heat.WholeSpace.SelfsimilarGenerator

/-!
# Weak solutions of the free shifted equation lie in the generator domain

`WeakShiftedEquation μ u F` states that `u ∈ H¹(ℝ³)³` solves `(μ + L₀) u = Π F` against smooth
compactly supported divergence-free fields, where `L₀ = -1/2 - (1/2) x·∇ - Δ` and
`F ∈ L²(ℝ³)³`. For a divergence-free solution and `ν > 1/2` the free resolvent `R_ν` applied to
`Π((ν - μ) u + F)` is a divergence-free `H¹` field solving the equation shifted to `ν + L₀`, so
it equals `u` by uniqueness of weak solutions. Hence `u` lies in the domain of the generator
`A₀ = -L₀` of the free self-similar evolution on `L²`, with `A₀ u = μ u - Π F`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology SobolevSpace SobolevSpace.GraphSpace HeatEquation.WholeSpace
open PDE.Analysis.Evolution
open scoped ENNReal NNReal Sobolev ContDiff SobolevSpace.WholeSpaceHilbert

namespace NavierStokes.Stationary

/-- `u ∈ H¹(ℝ³)³` solves `(μ + L₀) u = Π F` weakly, where `L₀ = -1/2 - (1/2) x·∇ - Δ` is the free
self-similar operator and `F ∈ L²(ℝ³)³`: for every smooth compactly supported divergence-free
`φ`, `Σᵢ ∫ uᵢ ((μ + 1) φᵢ + ½ (Dφ(x) x)ᵢ - Δφᵢ) = Σᵢ ∫ Fᵢ φᵢ`. -/
def WeakShiftedEquation (μ : ℝ) (u : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))) (F : VectorH 3 0) :
    Prop :=
  ∀ φ : ℝ^3 → ℝ^3, ContDiff ℝ ∞ φ → HasCompactSupport φ → (∀ x, PDE.divergence φ x = 0) →
    ∑ i, ∫ x, (wkpBaseCoordinateCLM (u i) : ℝ^3 → ℝ) x *
        ((μ + 1) * φ x i + (1 / 2) * fderiv ℝ φ x x i - PDE.laplacian (fun y ↦ φ y i) x) =
      ∑ i, ∫ x, (wkpBaseCoordinateCLM (F i) : ℝ^3 → ℝ) x * φ x i

/-- A divergence-free weak solution `u ∈ H¹(ℝ³)³` of `(μ + L₀) u = Π F` is the free resolvent
`R_ν` of `Π((ν - μ) u + F)` for every `ν > 1/2`. -/
theorem vectorLower_eq_vectorSelfsimilarResolvent_of_weak
    (u : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))) (hu : divergenceCLM u = 0) (F : VectorH 3 0)
    {μ : ℝ} (heq : WeakShiftedEquation μ u F) {ν : ℝ} (hν : 1 / 2 < ν) :
    vectorLower 3 0 u = vectorSelfsimilarResolvent 3 (by norm_num) (by linarith : 0 < ν)
      (IncompressibleFlow.leraySobolev 3 0 ((ν - μ) • vectorLower 3 0 u + F)) := by
  set G := IncompressibleFlow.leraySobolev 3 0 ((ν - μ) • vectorLower 3 0 u + F) with hG
  have hGP : IncompressibleFlow.leraySobolev 3 0 G = G :=
    IncompressibleFlow.leraySobolev_idempotent _
  have h23 : 2 ≤ 3 := by norm_num
  set z := vectorSelfsimilarResolventH2 3 h23 hν.le G with hz
  set d := vectorLower 3 1 z - u with hd_def
  have hd : divergenceCLM d = 0 := by
    rw [hd_def, map_sub, hu, sub_zero, divergenceCLM_apply]
    exact sum_partial_vectorLower_vectorSelfsimilarResolventH2 h23 hν.le hGP
  have hzi : ∀ i, wkpBaseCoordinateCLM (vectorLower 3 1 z i) = wkpBaseCoordinateCLM (z i) :=
    fun i ↦ wkpBaseCoordinateCLM_lowerOrderCLM _ (z i)
  have hdz : d = 0 := by
    refine eq_zero_of_weak_shifted_convection d 0 hd (map_zero _) (μ := ν) (by linarith) ?_
    intro φ hφ hc hdiv
    have hcomp : ∀ i, ContDiff ℝ ∞ (fun x ↦ φ x i) := contDiff_component hφ
    have hcompc : ∀ i, HasCompactSupport (fun x ↦ φ x i) := hasCompactSupport_component hc
    have hD : ∀ i {ψ : ℝ^3 → ℝ}, Continuous ψ → HasCompactSupport ψ →
        ∫ x, (wkpBaseCoordinateCLM (d i) : ℝ^3 → ℝ) x * ψ x =
          (∫ x, (wkpBaseCoordinateCLM (z i) : ℝ^3 → ℝ) x * ψ x) -
            ∫ x, (wkpBaseCoordinateCLM (u i) : ℝ^3 → ℝ) x * ψ x := by
      intro i ψ hψ hψc
      rw [show d i = vectorLower 3 1 z i - u i from rfl, integral_base_sub_mul _ _ hψ hψc, hzi]
    have hD1 : ∀ i, ∫ x, (wkpBaseCoordinateCLM (d i) : ℝ^3 → ℝ) x * φ x i =
        (∫ x, (wkpBaseCoordinateCLM (z i) : ℝ^3 → ℝ) x * φ x i) -
          ∫ x, (wkpBaseCoordinateCLM (u i) : ℝ^3 → ℝ) x * φ x i :=
      fun i ↦ hD i (hcomp i).continuous (hcompc i)
    have hD2 : ∀ i, ∫ x, (wkpBaseCoordinateCLM (d i) : ℝ^3 → ℝ) x * fderiv ℝ φ x x i =
        (∫ x, (wkpBaseCoordinateCLM (z i) : ℝ^3 → ℝ) x * fderiv ℝ φ x x i) -
          ∫ x, (wkpBaseCoordinateCLM (u i) : ℝ^3 → ℝ) x * fderiv ℝ φ x x i :=
      fun i ↦ hD i (continuous_fderiv_apply_self_component hφ i)
        (hasCompactSupport_fderiv_apply_self_component hc i)
    have hD3 : ∀ i, ∫ x, (wkpBaseCoordinateCLM (d i) : ℝ^3 → ℝ) x *
        PDE.laplacian (fun y ↦ φ y i) x =
        (∫ x, (wkpBaseCoordinateCLM (z i) : ℝ^3 → ℝ) x * PDE.laplacian (fun y ↦ φ y i) x) -
          ∫ x, (wkpBaseCoordinateCLM (u i) : ℝ^3 → ℝ) x * PDE.laplacian (fun y ↦ φ y i) x :=
      fun i ↦ hD i (PDE.contDiff_laplacian_coord (hcomp i)).continuous
        (hasCompactSupport_laplacian_coord (hcompc i))
    have hlow : ∀ i, wkpBaseCoordinateCLM ((vectorLower 3 0 u) i) =
        wkpBaseCoordinateCLM (u i) := fun i ↦ wkpBaseCoordinateCLM_lowerOrderCLM _ (u i)
    have hGi : ∑ i, ∫ x, (wkpBaseCoordinateCLM (G i) : ℝ^3 → ℝ) x * φ x i =
        (ν - μ) * (∑ i, ∫ x, (wkpBaseCoordinateCLM (u i) : ℝ^3 → ℝ) x * φ x i) +
          ∑ i, ∫ x, (wkpBaseCoordinateCLM (F i) : ℝ^3 → ℝ) x * φ x i := by
      rw [hG, sum_integral_leraySobolev_mul _ hφ hc hdiv, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [PiLp.add_apply, PiLp.smul_apply, map_add, map_smul, hlow i,
        add_comm ((ν - μ) • wkpBaseCoordinateCLM (u i)),
        integral_add_smul_mul _ _ (ν - μ) (hcomp i).continuous (hcompc i), add_comm]
    have hzeq : ∑ i, ∫ x, (wkpBaseCoordinateCLM (z i) : ℝ^3 → ℝ) x *
        ((ν + 1) * φ x i + (1 / 2) * fderiv ℝ φ x x i - PDE.laplacian (fun y ↦ φ y i) x) =
        ∑ i, ∫ x, (wkpBaseCoordinateCLM (G i) : ℝ^3 → ℝ) x * φ x i := by
      have h := sum_integral_vectorSelfsimilarResolventH2_mul_adjoint (n := 3) h23 hν G hφ hc
      have hcoef : (ν + (((3 : ℕ) : ℝ) - 1) / 2) = ν + 1 := by norm_num
      rw [hcoef] at h
      exact h
    rw [hGi] at hzeq
    have hueq := heq φ hφ hc hdiv
    have hzero : ∑ i, ∑ j, ∫ x, (wkpBaseCoordinateCLM
        ((0 : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))) j) : ℝ^3 → ℝ) x *
        (wkpBaseCoordinateCLM (d i) : ℝ^3 → ℝ) x * PDE.partialDeriv j (fun z ↦ φ z i) x = 0 := by
      refine Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun j _ ↦ ?_
      apply integral_eq_zero_of_ae
      have h0 := Lp.coeFn_zero ℝ 2 (domainMeasure 3 univ)
      rw [PiLp.zero_apply, map_zero]
      simp only [domainMeasure, Measure.restrict_univ] at h0
      filter_upwards [h0] with x hx
      rw [hx, Pi.zero_apply, zero_mul, zero_mul]
    rw [hzero]
    simp only [integral_mul_shiftedAdjoint _ _ hφ hc] at hzeq hueq ⊢
    simp only [hD1, hD2, hD3]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hzeq hueq ⊢
    linear_combination hzeq - hueq
  have hzu : vectorLower 3 1 z = u := sub_eq_zero.mp hdz
  rw [← hzu, hz, vectorLower_vectorLower_vectorSelfsimilarResolventH2]

/-- A divergence-free weak solution `u ∈ H¹(ℝ³)³` of `(μ + L₀) u = Π F` lies in the domain of
the generator `A₀ = -L₀` of the free self-similar evolution on `L²`, with `A₀ u = μ u - Π F`. -/
theorem hasGeneratorAt_vectorLower_of_weak
    (u : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))) (hu : divergenceCLM u = 0) (F : VectorH 3 0)
    {μ : ℝ} (heq : WeakShiftedEquation μ u F) :
    (vectorSelfsimilarHeatSemigroup 3 0).HasGeneratorAt (vectorLower 3 0 u)
      (μ • vectorLower 3 0 u - IncompressibleFlow.leraySobolev 3 0 F) := by
  have hR := vectorLower_eq_vectorSelfsimilarResolvent_of_weak u hu F heq
    (by norm_num : (1 / 2 : ℝ) < 1)
  set G := IncompressibleFlow.leraySobolev 3 0 ((1 - μ) • vectorLower 3 0 u + F) with hG
  have hP := IncompressibleFlow.leraySobolev_vectorLower_of_sum_firstDerivatives_eq_zero u
    ((divergenceCLM_apply u).symm.trans hu)
  have h := hasGeneratorAt_vectorSelfsimilarResolvent (n := 3) (by norm_num) one_pos G
  rw [← hR] at h
  convert h using 1
  rw [hG, map_add, map_smul, hP, one_smul]
  module

end NavierStokes.Stationary
