/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Stationary.WeakExistence
public import PDE.Fluid.NavierStokes.Stationary.Linearization
public import PDE.Analysis.Integration.CompactByPartsCoordinates
public import PDE.DistributionTheory.TestFunction.IntegrationByParts

/-!
# `H²` regularity of weak solutions of the linearized profile equation

Let `w ∈ H¹(ℝ³)³` be divergence free and `G ∈ L²(ℝ³)³`. A divergence-free `u ∈ H¹(ℝ³)³` with
`L₀ u + Π((w·∇) u) = Π G` against smooth compactly supported divergence-free fields, where
`L₀ = -1/2 - (1/2) x·∇ - Δ`, lies in `H²(ℝ³)³`. For large `μ` the shifted equation with data
`G + μ u` has a solution `z ∈ H²(ℝ³)³`, and `z - u` solves the homogeneous shifted equation, so
it vanishes by uniqueness.

For a smooth divergence-free background field `W` the weak profile pairing is the pairing of the
stationary operator `F = stationaryVelocityOperator W`: for smooth compactly supported `φ`,
`∫ Wᵢ (φᵢ + ½ (x·∇φ)ᵢ - Δφᵢ) - ∑ⱼ ∫ Wᵢ Wⱼ ∂ⱼφᵢ = ∫ Fᵢ φᵢ`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology SobolevSpace SobolevSpace.GraphSpace HeatEquation.WholeSpace
open PDE.Analysis
open scoped ENNReal NNReal Sobolev ContDiff SobolevSpace.WholeSpaceHilbert

namespace NavierStokes.Stationary

variable {n : ℕ}

theorem integral_base_sub_mul (a b : H¹(ℝ^3)) {ψ : ℝ^3 → ℝ} (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) :
    ∫ x, (wkpBaseCoordinateCLM (a - b) : ℝ^3 → ℝ) x * ψ x =
      (∫ x, (wkpBaseCoordinateCLM a : ℝ^3 → ℝ) x * ψ x) -
        ∫ x, (wkpBaseCoordinateCLM b : ℝ^3 → ℝ) x * ψ x := by
  have hsub : (wkpBaseCoordinateCLM (a - b) : ℝ^3 → ℝ) =ᵐ[volume]
      ⇑(wkpBaseCoordinateCLM a) - ⇑(wkpBaseCoordinateCLM b) := by
    have h := Lp.coeFn_sub (wkpBaseCoordinateCLM a) (wkpBaseCoordinateCLM b)
    rw [← map_sub] at h
    simpa [domainMeasure] using h
  rw [← integral_sub (integrable_base_mul a hψ hc) (integrable_base_mul b hψ hc)]
  apply integral_congr_ae
  filter_upwards [hsub] with x hx
  rw [hx, Pi.sub_apply]
  ring

theorem integrable_mulH1_mul (W U : H¹(ℝ^3)) {ψ : ℝ^3 → ℝ} (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) :
    Integrable (fun x ↦ (wkpBaseCoordinateCLM W : ℝ^3 → ℝ) x *
      (wkpBaseCoordinateCLM U : ℝ^3 → ℝ) x * ψ x) volume :=
  (memLp_mul_H1 W U).integrable_mul (q := 2) (hψ.memLp_of_hasCompactSupport hc)

theorem integral_mulH1_sub_mul (W a b : H¹(ℝ^3)) {ψ : ℝ^3 → ℝ} (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) :
    ∫ x, (wkpBaseCoordinateCLM W : ℝ^3 → ℝ) x * (wkpBaseCoordinateCLM (a - b) : ℝ^3 → ℝ) x * ψ x =
      (∫ x, (wkpBaseCoordinateCLM W : ℝ^3 → ℝ) x * (wkpBaseCoordinateCLM a : ℝ^3 → ℝ) x * ψ x) -
        ∫ x, (wkpBaseCoordinateCLM W : ℝ^3 → ℝ) x * (wkpBaseCoordinateCLM b : ℝ^3 → ℝ) x * ψ x := by
  have hsub : (wkpBaseCoordinateCLM (a - b) : ℝ^3 → ℝ) =ᵐ[volume]
      ⇑(wkpBaseCoordinateCLM a) - ⇑(wkpBaseCoordinateCLM b) := by
    have h := Lp.coeFn_sub (wkpBaseCoordinateCLM a) (wkpBaseCoordinateCLM b)
    rw [← map_sub] at h
    simpa [domainMeasure] using h
  rw [← integral_sub (integrable_mulH1_mul W a hψ hc) (integrable_mulH1_mul W b hψ hc)]
  apply integral_congr_ae
  filter_upwards [hsub] with x hx
  rw [hx, Pi.sub_apply]
  ring

theorem integral_add_smul_mul (f g : DerivLp 3 2 univ) (c : ℝ) {ψ : ℝ^3 → ℝ}
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    ∫ x, (⇑(f + c • g) : ℝ^3 → ℝ) x * ψ x =
      (∫ x, (f : ℝ^3 → ℝ) x * ψ x) + c * ∫ x, (g : ℝ^3 → ℝ) x * ψ x := by
  have hm : MemLp ψ 2 (domainMeasure 3 univ) := by
    simpa [domainMeasure] using hψ.memLp_of_hasCompactSupport (μ := volume) hc
  have hΨ : ⇑(hm.toLp ψ) =ᵐ[volume] ψ := by simpa [domainMeasure] using hm.coeFn_toLp
  rw [← inner_eq_integral_mul_of_ae (Filter.EventuallyEq.refl _ _) hΨ,
    ← inner_eq_integral_mul_of_ae (Filter.EventuallyEq.refl _ _) hΨ,
    ← inner_eq_integral_mul_of_ae (Filter.EventuallyEq.refl _ _) hΨ, inner_add_left,
    real_inner_smul_left]

/-- `H²` regularity for the linearized self-similar equation. A divergence-free `u ∈ H¹(ℝ³)³`
solving `L₀ u + Π((w·∇) u) = Π G` weakly, with `w ∈ H¹(ℝ³)³` divergence free and
`G ∈ L²(ℝ³)³`, is the first-order part of a field in `H²(ℝ³)³`. -/
theorem exists_vectorH2_of_weak_convection (w : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3)))
    (hw : divergenceCLM w = 0) (u : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3)))
    (hu : divergenceCLM u = 0) (G : VectorH 3 0)
    (heq : ∀ φ : ℝ^3 → ℝ^3, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∀ x, PDE.divergence φ x = 0) →
      ∑ i, ∫ x, (wkpBaseCoordinateCLM (u i) : ℝ^3 → ℝ) x *
        (φ x i + (1 / 2) * fderiv ℝ φ x x i - PDE.laplacian (fun y ↦ φ y i) x) =
      (∑ i, ∫ x, (wkpBaseCoordinateCLM (G i) : ℝ^3 → ℝ) x * φ x i) +
        ∑ i, ∑ j, ∫ x, (wkpBaseCoordinateCLM (w j) : ℝ^3 → ℝ) x *
          (wkpBaseCoordinateCLM (u i) : ℝ^3 → ℝ) x * PDE.partialDeriv j (fun y ↦ φ y i) x) :
    ∃ z : VectorH 3 2, vectorLower 3 1 z = u := by
  obtain ⟨μ, hμ1, hex⟩ := exists_vectorH2_weak_shifted_convection w hw
  set uL2 : VectorH 3 0 := ContinuousLinearMap.piLpMap 2
    (fun _ : Fin 3 ↦ lowerOrderCLM (n := 3) (p := 2) (Ω := univ) (by norm_num : 0 ≤ 1)) u
  obtain ⟨z, hzdiv, hzeq⟩ := hex μ le_rfl (G + μ • uL2)
  refine ⟨z, ?_⟩
  set d := vectorLower 3 1 z - u with hd_def
  have hd : divergenceCLM d = 0 := by rw [hd_def, map_sub, hzdiv, hu, sub_zero]
  have key := eq_zero_of_weak_shifted_convection d w hd hw (μ := μ) (by linarith) ?_
  · exact sub_eq_zero.mp key
  intro φ hφ hc hdiv
  have hcomp : ∀ i, ContDiff ℝ ∞ (fun x ↦ φ x i) := contDiff_component hφ
  have hcompc : ∀ i, HasCompactSupport (fun x ↦ φ x i) := hasCompactSupport_component hc
  have hX : ∀ i, Continuous (fun x ↦ fderiv ℝ φ x x i) :=
    continuous_fderiv_apply_self_component hφ
  have hXc : ∀ i, HasCompactSupport (fun x ↦ fderiv ℝ φ x x i) :=
    hasCompactSupport_fderiv_apply_self_component hc
  set B : Fin 3 → ℝ^3 → ℝ := fun i x ↦
    (1 / 2) * fderiv ℝ φ x x i - PDE.laplacian (fun y ↦ φ y i) x with hB_def
  have hB : ∀ i, Continuous (B i) := fun i ↦
    (continuous_const.mul (hX i)).sub (PDE.contDiff_laplacian_coord (hcomp i)).continuous
  have hBc : ∀ i, HasCompactSupport (B i) := fun i ↦
    ((hXc i).mul_left).sub (hasCompactSupport_laplacian_coord (hcompc i))
  have hDφ : ∀ i j, Continuous (fun x ↦ PDE.partialDeriv j (fun y ↦ φ y i) x) := fun i j ↦
    (PDE.contDiff_top_partialDeriv (i := j) (hcomp i)).continuous
  have hDφc : ∀ i j, HasCompactSupport (fun x ↦ PDE.partialDeriv j (fun y ↦ φ y i) x) :=
    fun i j ↦ (hcompc i).partialDeriv j
  have hsplit : ∀ (v : H¹(ℝ^3)) (c : ℝ) (i : Fin 3),
      ∫ x, (wkpBaseCoordinateCLM v : ℝ^3 → ℝ) x * (c * φ x i + (1 / 2) * fderiv ℝ φ x x i -
        PDE.laplacian (fun y ↦ φ y i) x) =
      c * (∫ x, (wkpBaseCoordinateCLM v : ℝ^3 → ℝ) x * φ x i) +
        ∫ x, (wkpBaseCoordinateCLM v : ℝ^3 → ℝ) x * B i x := by
    intro v c i
    rw [← integral_const_mul, ← integral_add ((integrable_base_mul v (hcomp i).continuous
      (hcompc i)).const_mul c) (integrable_base_mul v (hB i) (hBc i))]
    congr 1
    funext x
    simp only [B]
    ring
  have hsplit1 : ∀ (v : H¹(ℝ^3)) (i : Fin 3),
      ∫ x, (wkpBaseCoordinateCLM v : ℝ^3 → ℝ) x * (φ x i + (1 / 2) * fderiv ℝ φ x x i -
        PDE.laplacian (fun y ↦ φ y i) x) =
      (∫ x, (wkpBaseCoordinateCLM v : ℝ^3 → ℝ) x * φ x i) +
        ∫ x, (wkpBaseCoordinateCLM v : ℝ^3 → ℝ) x * B i x := fun v i ↦ by
    simpa only [one_mul] using hsplit v 1 i
  have hz := hzeq φ hφ hc hdiv
  have hu' := heq φ hφ hc hdiv
  have hdi : ∀ i, d i = lowerOrderCLM (n := 3) (p := 2) (Ω := univ) (by norm_num : 1 ≤ 2) (z i) -
      u i := fun i ↦ rfl
  have hzi : ∀ i, wkpBaseCoordinateCLM (lowerOrderCLM (n := 3) (p := 2) (Ω := univ)
      (by norm_num : 1 ≤ 2) (z i)) = wkpBaseCoordinateCLM (z i) := fun i ↦
    wkpBaseCoordinateCLM_lowerOrderCLM _ (z i)
  have hui : ∀ i, wkpBaseCoordinateCLM (uL2 i) = wkpBaseCoordinateCLM (u i) := fun i ↦
    wkpBaseCoordinateCLM_lowerOrderCLM _ (u i)
  have hGi : ∀ i, ∫ x, (wkpBaseCoordinateCLM ((G + μ • uL2) i) : ℝ^3 → ℝ) x * φ x i =
      (∫ x, (wkpBaseCoordinateCLM (G i) : ℝ^3 → ℝ) x * φ x i) +
        μ * ∫ x, (wkpBaseCoordinateCLM (u i) : ℝ^3 → ℝ) x * φ x i := fun i ↦ by
    rw [PiLp.add_apply, PiLp.smul_apply, map_add, map_smul, ← hui i]
    exact integral_add_smul_mul _ _ μ (hcomp i).continuous (hcompc i)
  have hD1 : ∀ i, ∫ x, (wkpBaseCoordinateCLM (d i) : ℝ^3 → ℝ) x * φ x i =
      (∫ x, (wkpBaseCoordinateCLM (z i) : ℝ^3 → ℝ) x * φ x i) -
        ∫ x, (wkpBaseCoordinateCLM (u i) : ℝ^3 → ℝ) x * φ x i := fun i ↦ by
    rw [hdi, integral_base_sub_mul _ _ (hcomp i).continuous (hcompc i), hzi]
  have hD2 : ∀ i, ∫ x, (wkpBaseCoordinateCLM (d i) : ℝ^3 → ℝ) x * B i x =
      (∫ x, (wkpBaseCoordinateCLM (z i) : ℝ^3 → ℝ) x * B i x) -
        ∫ x, (wkpBaseCoordinateCLM (u i) : ℝ^3 → ℝ) x * B i x := fun i ↦ by
    rw [hdi, integral_base_sub_mul _ _ (hB i) (hBc i), hzi]
  have hD3 : ∀ i j, ∫ x, (wkpBaseCoordinateCLM (w j) : ℝ^3 → ℝ) x *
      (wkpBaseCoordinateCLM (d i) : ℝ^3 → ℝ) x * PDE.partialDeriv j (fun y ↦ φ y i) x =
      (∫ x, (wkpBaseCoordinateCLM (w j) : ℝ^3 → ℝ) x *
        (wkpBaseCoordinateCLM (z i) : ℝ^3 → ℝ) x * PDE.partialDeriv j (fun y ↦ φ y i) x) -
      ∫ x, (wkpBaseCoordinateCLM (w j) : ℝ^3 → ℝ) x *
        (wkpBaseCoordinateCLM (u i) : ℝ^3 → ℝ) x * PDE.partialDeriv j (fun y ↦ φ y i) x :=
    fun i j ↦ by rw [hdi, integral_mulH1_sub_mul _ _ _ (hDφ i j) (hDφc i j), hzi]
  have hsplitz : ∀ (c : ℝ) (i : Fin 3),
      ∫ x, (wkpBaseCoordinateCLM (z i) : ℝ^3 → ℝ) x * (c * φ x i + (1 / 2) * fderiv ℝ φ x x i -
        PDE.laplacian (fun y ↦ φ y i) x) =
      c * (∫ x, (wkpBaseCoordinateCLM (z i) : ℝ^3 → ℝ) x * φ x i) +
        ∫ x, (wkpBaseCoordinateCLM (z i) : ℝ^3 → ℝ) x * B i x := fun c i ↦ by
    rw [← hzi i]
    exact hsplit _ c i
  simp only [hsplit, hsplitz, hsplit1, hGi] at hz hu' ⊢
  simp only [hD1, hD2, hD3]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hz hu' ⊢
  linear_combination hz - hu'

/-- The components of the stationary self-similar operator of a `C²` field. -/
theorem stationaryVelocityOperator_apply_component {W : ℝ^n → ℝ^n} (hW : ContDiff ℝ 2 W)
    (x : ℝ^n) (i : Fin n) :
    stationaryVelocityOperator W x i =
      -(1 / 2) * (W x i + ∑ j, x j * (∂[j] (fun y ↦ W y i)) x) +
        ∑ j, W x j * (∂[j] (fun y ↦ W y i)) x - PDE.laplacian (fun y ↦ W y i) x := by
  have hd : DifferentiableAt ℝ W x := hW.differentiable (by norm_num) x
  simp only [stationaryVelocityOperator, PDE.advectiveDerivative, PiLp.sub_apply,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, fderiv_apply_component hd,
    PDE.laplacian_apply_of_contDiff hW]

/-- The weak profile pairing of a smooth divergence-free background field `W` in three
dimensions is the pairing of its stationary operator: for every smooth compactly supported `φ`
and every component `i`,
`∫ Wᵢ (φᵢ + ½ (x·∇φ)ᵢ - Δφᵢ) - ∑ⱼ ∫ Wᵢ Wⱼ ∂ⱼφᵢ = ∫ (stationaryVelocityOperator W)ᵢ φᵢ`. -/
theorem integral_background_profile_eq {W φ : ℝ^3 → ℝ^3} (hW : ContDiff ℝ ∞ W)
    (hWdiv : ∀ x, PDE.divergence W x = 0) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (i : Fin 3) :
    (∫ x, W x i * φ x i) + (1 / 2) * (∫ x, W x i * fderiv ℝ φ x x i) -
        (∫ x, W x i * PDE.laplacian (fun y ↦ φ y i) x) -
        ∑ j, ∫ x, W x i * W x j * (∂[j] (fun y ↦ φ y i)) x =
      ∫ x, stationaryVelocityOperator W x i * φ x i := by
  have hWi : ContDiff ℝ ∞ (fun x ↦ W x i) := contDiff_component hW i
  have hφi : ContDiff ℝ ∞ (fun x ↦ φ x i) := contDiff_component hφ i
  have hφc : HasCompactSupport (fun x ↦ φ x i) := hasCompactSupport_component hc i
  have hcoord : ∀ j : Fin 3, Continuous (fun x : ℝ^3 ↦ x j) := fun j ↦
    (EuclideanSpace.proj j : ℝ^3 →L[ℝ] ℝ).continuous
  have hWj : ∀ j : Fin 3, Continuous (fun x ↦ W x j) := fun j ↦
    (contDiff_component hW j).continuous
  have hDW : ∀ j : Fin 3, Continuous (fun x ↦ (∂[j] (fun y ↦ W y i)) x) := fun j ↦
    (PDE.contDiff_top_partialDeriv hWi).continuous
  -- the three integrations by parts
  have h1 : ∫ x, W x i * fderiv ℝ φ x x i =
      -(∫ x, (∑ j, x j * (∂[j] (fun y ↦ W y i)) x) * φ x i) - 3 * ∫ x, W x i * φ x i := by
    have h := integral_mul_sum_coord_mul_partialDeriv hφi hWi hφc
    have hfd : ∀ x, fderiv ℝ φ x x i = ∑ j, x j * (∂[j] (fun y ↦ φ y i)) x := fun x ↦
      fderiv_apply_component (hφ.differentiable (by simp) x) x i
    simp only [hfd]
    rw [h]
    norm_num
  have h2 : ∫ x, W x i * PDE.laplacian (fun y ↦ φ y i) x =
      ∫ x, PDE.laplacian (fun y ↦ W y i) x * φ x i := by
    simp only [mul_comm (W _ i), mul_comm (PDE.laplacian (fun y ↦ W y i) _)]
    exact (PDE.DistributionTheory.integral_mul_laplacian_eq _ (hφi.of_le (by simp))
      (hWi.of_le (by simp)) hφc).symm
  have h3 : ∑ j, ∫ x, W x i * W x j * (∂[j] (fun y ↦ φ y i)) x =
      -∫ x, (∑ j, W x j * (∂[j] (fun y ↦ W y i)) x) * φ x i :=
    sum_integral_mul_mul_partialDeriv_eq_neg hWi hW hWdiv hφi hφc
  -- the stationary operator, split
  have iA : Integrable (fun x ↦ W x i * φ x i) volume :=
    integrable_mul_of_hasCompactSupport_right (hWj i) hφi.continuous hφc
  have iB : Integrable (fun x ↦ (∑ j, x j * (∂[j] (fun y ↦ W y i)) x) * φ x i) volume :=
    integrable_mul_of_hasCompactSupport_right
      (continuous_finsetSum _ fun j _ ↦ (hcoord j).mul (hDW j)) hφi.continuous hφc
  have iC : Integrable (fun x ↦ (∑ j, W x j * (∂[j] (fun y ↦ W y i)) x) * φ x i) volume :=
    integrable_mul_of_hasCompactSupport_right
      (continuous_finsetSum _ fun j _ ↦ (hWj j).mul (hDW j)) hφi.continuous hφc
  have iD : Integrable (fun x ↦ PDE.laplacian (fun y ↦ W y i) x * φ x i) volume :=
    integrable_mul_of_hasCompactSupport_right (PDE.contDiff_laplacian_coord hWi).continuous
      hφi.continuous hφc
  have hF : ∫ x, stationaryVelocityOperator W x i * φ x i =
      -(1 / 2) * (∫ x, W x i * φ x i) -
        (1 / 2) * (∫ x, (∑ j, x j * (∂[j] (fun y ↦ W y i)) x) * φ x i) +
        (∫ x, (∑ j, W x j * (∂[j] (fun y ↦ W y i)) x) * φ x i) -
        ∫ x, PDE.laplacian (fun y ↦ W y i) x * φ x i := by
    have hpt : ∀ x, stationaryVelocityOperator W x i * φ x i =
        -(1 / 2) * (W x i * φ x i) -
          (1 / 2) * ((∑ j, x j * (∂[j] (fun y ↦ W y i)) x) * φ x i) +
          (∑ j, W x j * (∂[j] (fun y ↦ W y i)) x) * φ x i -
          PDE.laplacian (fun y ↦ W y i) x * φ x i := by
      intro x
      rw [stationaryVelocityOperator_apply_component (hW.of_le (by simp))]
      ring
    simp only [hpt]
    set A : ℝ^3 → ℝ := fun x ↦ W x i * φ x i
    set B : ℝ^3 → ℝ := fun x ↦ (∑ j, x j * (∂[j] (fun y ↦ W y i)) x) * φ x i
    set C : ℝ^3 → ℝ := fun x ↦ (∑ j, W x j * (∂[j] (fun y ↦ W y i)) x) * φ x i
    set D : ℝ^3 → ℝ := fun x ↦ PDE.laplacian (fun y ↦ W y i) x * φ x i
    rw [integral_sub (f := fun x ↦ -(1 / 2) * A x - (1 / 2) * B x + C x) (g := D)
      (((iA.const_mul _).sub (iB.const_mul _)).add iC) iD,
      integral_add (f := fun x ↦ -(1 / 2) * A x - (1 / 2) * B x) (g := C)
        ((iA.const_mul _).sub (iB.const_mul _)) iC,
      integral_sub (f := fun x ↦ -(1 / 2) * A x) (g := fun x ↦ (1 / 2) * B x)
        (iA.const_mul _) (iB.const_mul _), integral_const_mul, integral_const_mul]
  rw [h1, h2, h3, hF]
  ring

end NavierStokes.Stationary
