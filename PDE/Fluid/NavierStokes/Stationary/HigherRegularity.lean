/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Stationary.WeakRegularity
public import PDE.Spaces.Sobolev.GraphSpace.Representatives.WholeSpaceRegularity

/-!
# Higher regularity for the self-similar Stokes system

A divergence-free field `v ∈ H¹(ℝ³)³` solves the self-similar Stokes system
`-½ v - ½ x·∇v - Δv + ∇p = g` weakly if
`∑ᵢ ∫ vᵢ (φᵢ + ½ (x·∇φ)ᵢ - Δφᵢ) = ∑ᵢ ∫ gᵢ φᵢ`
for every smooth compactly supported divergence-free field `φ`. For `g ∈ H^m(ℝ³)³` every
component of `v` lies in `H^{m+2}(ℝ³)` (`exists_wkpSpace_of_weak_selfsimilarStokes`).

The case `m = 0` is the `H²` regularity of the linearized profile equation without transport.
For the induction, `∂ₖφ` is again a divergence-free test field, and `∂ₖ` commutes with the
Euler operator up to `∂ₖ(x·∇f) = ∂ₖf + x·∇(∂ₖf)`. Testing with `∂ₖφ` and integrating by parts
shows that `∂ₖv` solves the system with data `∂ₖg + ½ ∂ₖv ∈ H^m(ℝ³)³`, so by induction
`∂ₖv ∈ H^{m+2}(ℝ³)³` for every `k`, and `v ∈ H^{m+3}(ℝ³)³`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter SobolevSpace SobolevSpace.GraphSpace PDE.Analysis
open scoped ENNReal Sobolev ContDiff SobolevSpace.WholeSpaceHilbert

namespace NavierStokes.Stationary

variable {n : ℕ}

/-- A coordinate derivative commutes with the Euler operator `x·∇` up to itself:
`∂ₖ(x·∇f) = ∂ₖf + x·∇(∂ₖf)`. -/
theorem partialDeriv_sum_coord_mul_partialDeriv {f : ℝ^n → ℝ} (hf : ContDiff ℝ ∞ f)
    (k : Fin n) (x : ℝ^n) :
    ∂[k] (fun y ↦ ∑ j, y j * ∂[j] f y) x =
      ∂[k] f x + ∑ j, x j * ∂[j] (fun y ↦ ∂[k] f y) x := by
  have hcoord (j : Fin n) : Differentiable ℝ (fun y : ℝ^n ↦ y j) :=
    (EuclideanSpace.proj j : ℝ^n →L[ℝ] ℝ).differentiable
  have hdf (j : Fin n) : Differentiable ℝ (fun y ↦ ∂[j] f y) :=
    (PDE.contDiff_top_partialDeriv hf).differentiable (by simp)
  rw [PDE.partialDeriv_sum (f := fun j y ↦ y j * ∂[j] f y) _
    (fun j _ ↦ (hcoord j x).mul (hdf j x))]
  have hterm (j : Fin n) : ∂[k] (fun y ↦ y j * ∂[j] f y) x =
      (if k = j then 1 else 0) * ∂[j] f x + x j * ∂[j] (fun y ↦ ∂[k] f y) x := by
    rw [PDE.partialDeriv_mul (hcoord j x) (hdf j x), PDE.partialDeriv_coord,
      PDE.partialDeriv_partialDeriv_comm k j (hf.of_le (by simp)) x]
  rw [Finset.sum_congr rfl fun j _ ↦ hterm j, Finset.sum_add_distrib]
  simp [ite_mul]

/-- The components of a coordinate derivative of a smooth field. -/
theorem partialDeriv_component_eq {φ : ℝ^n → ℝ^n} (hφ : ContDiff ℝ ∞ φ) (k i : Fin n) :
    (fun y ↦ ∂[k] φ y i) = fun y ↦ ∂[k] (fun z ↦ φ z i) y :=
  funext fun y ↦ PDE.partialDeriv_apply k i (hφ.differentiable (by simp) y)

/-- A coordinate derivative of a smooth divergence-free field is divergence free. -/
theorem divergence_partialDeriv_eq_zero {φ : ℝ^n → ℝ^n} (hφ : ContDiff ℝ ∞ φ)
    (hdiv : ∀ x, PDE.divergence φ x = 0) (k : Fin n) (x : ℝ^n) :
    PDE.divergence (fun y ↦ ∂[k] φ y) x = 0 := by
  have hφi (i : Fin n) : ContDiff ℝ ∞ (fun y ↦ φ y i) := contDiff_component hφ i
  rw [PDE.divergence_eq_sum]
  have hcomm (i : Fin n) : ∂[i] (fun y ↦ ∂[k] φ y i) x =
      ∂[k] (fun y ↦ ∂[i] (fun z ↦ φ z i) y) x := by
    rw [partialDeriv_component_eq hφ k i]
    exact PDE.partialDeriv_partialDeriv_comm i k ((hφi i).of_le (by simp)) x
  rw [Finset.sum_congr rfl fun i _ ↦ hcomm i, ← PDE.partialDeriv_sum _ (fun i _ ↦
    ((PDE.contDiff_top_partialDeriv (hφi i)).differentiable (by simp)).differentiableAt)]
  have h0 : (fun y ↦ ∑ i, ∂[i] (fun z ↦ φ z i) y) = fun _ ↦ (0 : ℝ) :=
    funext fun y ↦ (PDE.divergence_eq_sum φ y).symm.trans (hdiv y)
  rw [h0, PDE.partialDeriv_const]

/-- The self-similar adjoint `φᵢ + ½ (x·∇φ)ᵢ - Δφᵢ` of a coordinate derivative `∂ₖφ` is the
coordinate derivative of the self-similar adjoint of `φ` minus `½ ∂ₖφᵢ`. -/
theorem selfsimilarAdjoint_partialDeriv {φ : ℝ^n → ℝ^n} (hφ : ContDiff ℝ ∞ φ) (k i : Fin n)
    (x : ℝ^n) :
    ∂[k] φ x i + (1 / 2) * fderiv ℝ (fun y ↦ ∂[k] φ y) x x i -
        PDE.laplacian (fun y ↦ ∂[k] φ y i) x =
      ∂[k] (fun y ↦ φ y i + (1 / 2) * fderiv ℝ φ y y i -
        PDE.laplacian (fun z ↦ φ z i) y) x - (1 / 2) * ∂[k] (fun y ↦ φ y i) x := by
  have hf : ContDiff ℝ ∞ (fun y ↦ φ y i) := contDiff_component hφ i
  have hψ : ContDiff ℝ ∞ (fun y ↦ ∂[k] φ y) := PDE.contDiff_top_partialDeriv hφ
  have hcomp := partialDeriv_component_eq hφ k i
  have hE (y : ℝ^n) : fderiv ℝ φ y y i = ∑ j, y j * ∂[j] (fun z ↦ φ z i) y :=
    fderiv_apply_component (hφ.differentiable (by simp) y) y i
  have hEψ : fderiv ℝ (fun y ↦ ∂[k] φ y) x x i =
      ∑ j, x j * ∂[j] (fun y ↦ ∂[k] (fun z ↦ φ z i) y) x := by
    rw [fderiv_apply_component (hψ.differentiable (by simp) x) x i, hcomp]
  have hcoord (j : Fin n) : Differentiable ℝ (fun y : ℝ^n ↦ y j) :=
    (EuclideanSpace.proj j : ℝ^n →L[ℝ] ℝ).differentiable
  have hd1 : Differentiable ℝ (fun y ↦ φ y i) := hf.differentiable (by simp)
  have hd2 : Differentiable ℝ (fun y ↦ ∑ j, y j * ∂[j] (fun z ↦ φ z i) y) :=
    Differentiable.fun_sum fun j _ ↦
      (hcoord j).mul ((PDE.contDiff_top_partialDeriv hf).differentiable (by simp))
  have hd3 : Differentiable ℝ (fun y ↦ PDE.laplacian (fun z ↦ φ z i) y) :=
    (PDE.contDiff_laplacian_coord hf).differentiable (by simp)
  simp only [hE]
  rw [PDE.partialDeriv_sub ((hd1 x).fun_add ((hd2 x).const_mul _)) (hd3 x),
    PDE.partialDeriv_add (hd1 x) ((hd2 x).const_mul _)]
  have hc : ∂[k] (fun y ↦ (1 / 2 : ℝ) * ∑ j, y j * ∂[j] (fun z ↦ φ z i) y) x =
      (1 / 2) * ∂[k] (fun y ↦ ∑ j, y j * ∂[j] (fun z ↦ φ z i) y) x := by
    simpa [smul_eq_mul] using PDE.partialDeriv_const_smul (i := k) (1 / 2 : ℝ)
      (f := fun y ↦ ∑ j, y j * ∂[j] (fun z ↦ φ z i) y) (x := x)
  rw [hc, partialDeriv_sum_coord_mul_partialDeriv hf, hEψ, hcomp, PDE.laplacian_partialDeriv_eq hf,
    congrFun hcomp x]
  ring

/-- A field in `H¹(ℝⁿ)ⁿ` orthogonal to all gradients of smooth compactly supported functions is
divergence free. -/
theorem divergenceCLM_eq_zero_of_forall_integral (y : PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n)))
    (h : ∀ ψ : ℝ^n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∑ i, ∫ x, baseRepresentative (y i) x * ∂[i] ψ x = 0) :
    divergenceCLM y = 0 := by
  have hd : MemLp (divergenceCLM y : ℝ^n → ℝ) 2 volume := by
    have h0 := Lp.memLp (divergenceCLM y)
    simp only [domainMeasure, Measure.restrict_univ] at h0
    exact h0
  have hint (ψ : ℝ^n → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
      ∫ x, ψ x • (divergenceCLM y : ℝ^n → ℝ) x = 0 := by
    have hmem : MemLp ψ 2 (domainMeasure n univ) := by
      simpa [domainMeasure] using hψ.continuous.memLp_of_hasCompactSupport (μ := volume) hc
    have hΨ : ⇑(hmem.toLp ψ) =ᵐ[volume] ψ := by simpa [domainMeasure] using hmem.coeFn_toLp
    have hpair (i : Fin n) : inner ℝ (wkpCoordinateCLM (singleDerivIndex n i) (y i))
        (hmem.toLp ψ) = -∫ x, baseRepresentative (y i) x * ∂[i] ψ x := by
      rw [inner_eq_integral_mul_of_ae (Filter.EventuallyEq.refl _ _) hΨ]
      exact (neg_eq_iff_eq_neg.mpr (integral_base_mul_partialDeriv (y i) i hψ hc)).symm
    have hsum : inner ℝ (divergenceCLM y) (hmem.toLp ψ) = 0 := by
      rw [divergenceCLM_apply, sum_inner, Finset.sum_congr rfl fun i _ ↦ hpair i,
        Finset.sum_neg_distrib, h ψ hψ hc, neg_zero]
    rw [inner_eq_integral_mul_of_ae (Filter.EventuallyEq.refl _ _) hΨ] at hsum
    simpa [smul_eq_mul, mul_comm] using hsum
  have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero (hd.locallyIntegrable (by norm_num))
    hint
  refine (Lp.eq_zero_iff_ae_eq_zero).2 ?_
  simp only [domainMeasure, Measure.restrict_univ]
  filter_upwards [hae] with x hx
  exact hx

/-- Testing the self-similar Stokes system of `V` with data `g` against `∂ₖφ` and integrating by
parts: the derivative `∂ₖV` solves the system with data `∂ₖg + ½ ∂ₖV`. -/
theorem sum_integral_partialDeriv_selfsimilarStokes {a b : ℕ} (V : Fin 3 → W^{a + 1,2}(ℝ^3))
    (g : Fin 3 → W^{b + 1,2}(ℝ^3))
    (heq : ∀ φ : ℝ^3 → ℝ^3, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∀ x, PDE.divergence φ x = 0) →
      ∑ i, ∫ x, baseRepresentative (V i) x *
        (φ x i + (1 / 2) * fderiv ℝ φ x x i - PDE.laplacian (fun y ↦ φ y i) x) =
      ∑ i, ∫ x, baseRepresentative (g i) x * φ x i)
    (k : Fin 3) {φ : ℝ^3 → ℝ^3} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hdiv : ∀ x, PDE.divergence φ x = 0) :
    ∑ i, ∫ x, baseRepresentative (partialDerivCLM k (V i)) x *
        (φ x i + (1 / 2) * fderiv ℝ φ x x i - PDE.laplacian (fun y ↦ φ y i) x) =
      (∑ i, ∫ x, baseRepresentative (partialDerivCLM k (g i)) x * φ x i) +
        (1 / 2) * ∑ i, ∫ x, baseRepresentative (partialDerivCLM k (V i)) x * φ x i := by
  have hψ : ContDiff ℝ ∞ (fun x ↦ ∂[k] φ x) := PDE.contDiff_top_partialDeriv hφ
  have h : ∑ i, ∫ x, baseRepresentative (V i) x * (∂[k] φ x i +
        (1 / 2) * fderiv ℝ (fun y ↦ ∂[k] φ y) x x i - PDE.laplacian (fun y ↦ ∂[k] φ y i) x) =
      ∑ i, ∫ x, baseRepresentative (g i) x * ∂[k] φ x i :=
    heq _ hψ (hc.partialDeriv k) (divergence_partialDeriv_eq_zero hφ hdiv k)
  have hφi (i : Fin 3) : ContDiff ℝ ∞ (fun y ↦ φ y i) := contDiff_component hφ i
  have hφic (i : Fin 3) : HasCompactSupport (fun y ↦ φ y i) := hasCompactSupport_component hc i
  have hΦ (i : Fin 3) : ContDiff ℝ ∞ (fun y ↦ φ y i + (1 / 2) * fderiv ℝ φ y y i -
      PDE.laplacian (fun z ↦ φ z i) y) :=
    ((hφi i).add (contDiff_const.mul (contDiff_component
      ((hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_id) i))).sub
      (PDE.contDiff_laplacian_coord (hφi i))
  have hΦc (i : Fin 3) : HasCompactSupport (fun y ↦ φ y i + (1 / 2) * fderiv ℝ φ y y i -
      PDE.laplacian (fun z ↦ φ z i) y) :=
    ((hφic i).add (hasCompactSupport_fderiv_apply_self_component hc i).mul_left).sub
      (hasCompactSupport_laplacian_coord (hφic i))
  have hl (i : Fin 3) : ∫ x, baseRepresentative (V i) x * (∂[k] φ x i +
        (1 / 2) * fderiv ℝ (fun y ↦ ∂[k] φ y) x x i - PDE.laplacian (fun y ↦ ∂[k] φ y i) x) =
      -(∫ x, baseRepresentative (partialDerivCLM k (V i)) x *
        (φ x i + (1 / 2) * fderiv ℝ φ x x i - PDE.laplacian (fun y ↦ φ y i) x)) +
        (1 / 2) * ∫ x, baseRepresentative (partialDerivCLM k (V i)) x * φ x i := by
    have hpt (x : ℝ^3) : baseRepresentative (V i) x * (∂[k] φ x i +
        (1 / 2) * fderiv ℝ (fun y ↦ ∂[k] φ y) x x i - PDE.laplacian (fun y ↦ ∂[k] φ y i) x) =
        baseRepresentative (V i) x * ∂[k] (fun y ↦ φ y i + (1 / 2) * fderiv ℝ φ y y i -
          PDE.laplacian (fun z ↦ φ z i) y) x -
        (1 / 2) * (baseRepresentative (V i) x * ∂[k] (fun y ↦ φ y i) x) := by
      rw [selfsimilarAdjoint_partialDeriv hφ k i x]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
      integral_sub (integrable_baseRepresentative_mul (V i)
        (PDE.contDiff_top_partialDeriv (hΦ i)).continuous ((hΦc i).partialDeriv k))
        ((integrable_baseRepresentative_mul (V i) (PDE.contDiff_top_partialDeriv (hφi i)).continuous
          ((hφic i).partialDeriv k)).const_mul _),
      integral_const_mul, integral_baseRepresentative_mul_partialDeriv (V i) k (hΦ i) (hΦc i),
      integral_baseRepresentative_mul_partialDeriv (V i) k (hφi i) (hφic i)]
    ring
  have hr (i : Fin 3) : ∫ x, baseRepresentative (g i) x * ∂[k] φ x i =
      -∫ x, baseRepresentative (partialDerivCLM k (g i)) x * φ x i := by
    rw [← integral_baseRepresentative_mul_partialDeriv (g i) k (hφi i) (hφic i)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦ by
      dsimp only
      rw [congrFun (partialDeriv_component_eq hφ k i) x])
  simp only [hl, hr, Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum] at h
  linarith

/-- **Higher regularity for the self-similar Stokes system.** Let `v ∈ H¹(ℝ³)³` be divergence
free and `g` a vector field with components in `H^m(ℝ³)`. If
`∑ᵢ ∫ vᵢ (φᵢ + ½ (x·∇φ)ᵢ - Δφᵢ) = ∑ᵢ ∫ gᵢ φᵢ`
for every smooth compactly supported divergence-free `φ`, that is
`-½ v - ½ x·∇v - Δv + ∇p = g` weakly, then every component of `v` lies in `H^{m+2}(ℝ³)`. -/
theorem exists_wkpSpace_of_weak_selfsimilarStokes (m : ℕ)
    (v : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))) (hv : divergenceCLM v = 0)
    (g : Fin 3 → W^{m,2}(ℝ^3))
    (heq : ∀ φ : ℝ^3 → ℝ^3, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∀ x, PDE.divergence φ x = 0) →
      ∑ i, ∫ x, baseRepresentative (v i) x *
        (φ x i + (1 / 2) * fderiv ℝ φ x x i - PDE.laplacian (fun y ↦ φ y i) x) =
      ∑ i, ∫ x, baseRepresentative (g i) x * φ x i) :
    ∀ i, ∃ V : W^{m + 2,2}(ℝ^3), baseRepresentative V =ᵐ[volume] baseRepresentative (v i) := by
  induction m generalizing v with
  | zero =>
    obtain ⟨z, hz⟩ := exists_vectorH2_of_weak_convection 0 (map_zero _) v hv
      (WithLp.toLp 2 g) fun φ hφ hc hdiv ↦ by
        have h0 (i j : Fin 3) : ∫ x, (wkpBaseCoordinateCLM
            ((0 : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))) j) : ℝ^3 → ℝ) x *
            (wkpBaseCoordinateCLM (v i) : ℝ^3 → ℝ) x * PDE.partialDeriv j (fun y ↦ φ y i) x =
            0 := by
          have hz : (wkpBaseCoordinateCLM ((0 : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))) j) :
              ℝ^3 → ℝ) =ᵐ[volume] 0 := by
            rw [PiLp.zero_apply, map_zero]
            simpa [domainMeasure] using Lp.coeFn_zero ℝ 2 (domainMeasure 3 univ)
          exact integral_eq_zero_of_ae (hz.mono fun x hx ↦ by
            simp only [hx, Pi.zero_apply, zero_mul])
        simp only [h0, Finset.sum_const_zero, add_zero]
        exact heq φ hφ hc hdiv
    intro i
    refine ⟨z i, Filter.EventuallyEq.of_eq ?_⟩
    rw [← hz, vectorLower_apply, baseRepresentative_lowerOrderCLM]
  | succ m ih =>
    obtain ⟨V, hV⟩ : ∃ V : Fin 3 → W^{m + 2,2}(ℝ^3),
        ∀ i, baseRepresentative (V i) =ᵐ[volume] baseRepresentative (v i) := by
      refine Classical.axiomOfChoice (ih v hv (fun i ↦ lowerOrderCLM (Nat.le_succ m) (g i))
        fun φ hφ hc hdiv ↦ ?_)
      simp only [baseRepresentative_lowerOrderCLM]
      exact heq φ hφ hc hdiv
    have heqV (φ : ℝ^3 → ℝ^3) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
        (hdiv : ∀ x, PDE.divergence φ x = 0) :
        ∑ i, ∫ x, baseRepresentative (V i) x *
          (φ x i + (1 / 2) * fderiv ℝ φ x x i - PDE.laplacian (fun y ↦ φ y i) x) =
        ∑ i, ∫ x, baseRepresentative (g i) x * φ x i := by
      rw [← heq φ hφ hc hdiv]
      exact Finset.sum_congr rfl fun i _ ↦ integral_congr_ae ((hV i).mono fun x hx ↦ by
        beta_reduce
        rw [hx])
    have hk (k : Fin 3) (i : Fin 3) : ∃ Y : W^{m + 2,2}(ℝ^3),
        baseRepresentative Y =ᵐ[volume] baseRepresentative (partialDerivCLM k (V i)) := by
      set vk : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3)) := WithLp.toLp 2 fun i ↦
        lowerOrderCLM (by omega : 1 ≤ m + 1) (partialDerivCLM k (V i)) with hvk_def
      have hbase (i : Fin 3) : baseRepresentative (vk i) =
          baseRepresentative (partialDerivCLM k (V i)) :=
        baseRepresentative_lowerOrderCLM _ _
      have hvk : divergenceCLM vk = 0 := by
        refine divergenceCLM_eq_zero_of_forall_integral vk fun ψ hψ hc ↦ ?_
        have h1 (i : Fin 3) : ∫ x, baseRepresentative (vk i) x * ∂[i] ψ x =
            -∫ x, baseRepresentative (v i) x * ∂[i] (fun y ↦ ∂[k] ψ y) x := by
          have h3 := integral_baseRepresentative_mul_partialDeriv (V i) k
            (PDE.contDiff_top_partialDeriv (i := i) hψ) (hc.partialDeriv i)
          have h4 : ∫ x, baseRepresentative (V i) x * ∂[k] (fun y ↦ ∂[i] ψ y) x =
              ∫ x, baseRepresentative (v i) x * ∂[i] (fun y ↦ ∂[k] ψ y) x :=
            integral_congr_ae ((hV i).mono fun x hx ↦ by
              beta_reduce
              rw [hx, PDE.partialDeriv_partialDeriv_comm k i (hψ.of_le (by simp)) x])
          rw [hbase, ← h4, h3, neg_neg]
        rw [Finset.sum_congr rfl fun i _ ↦ h1 i, Finset.sum_neg_distrib]
        have h2 := sum_integral_base_mul_partialDeriv_eq_zero v hv
          (PDE.contDiff_top_partialDeriv (i := k) hψ) (hc.partialDeriv k)
        change ∑ i, ∫ x, baseRepresentative (v i) x * ∂[i] (fun y ↦ ∂[k] ψ y) x = 0 at h2
        rw [h2, neg_zero]
      set gk : Fin 3 → W^{m,2}(ℝ^3) := fun i ↦ partialDerivCLM k (g i) +
        (1 / 2 : ℝ) • lowerOrderCLM (Nat.le_succ m) (partialDerivCLM k (V i)) with hgk_def
      have hgk (i : Fin 3) {ψ : ℝ^3 → ℝ} (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
          ∫ x, baseRepresentative (gk i) x * ψ x =
            (∫ x, baseRepresentative (partialDerivCLM k (g i)) x * ψ x) +
              (1 / 2) * ∫ x, baseRepresentative (partialDerivCLM k (V i)) x * ψ x := by
        have hae : ∀ᵐ x ∂volume, baseRepresentative (gk i) x =
            baseRepresentative (partialDerivCLM k (g i)) x +
              (1 / 2) * baseRepresentative (partialDerivCLM k (V i)) x := by
          have h1 := baseRepresentative_add_ae (partialDerivCLM k (g i))
            ((1 / 2 : ℝ) • lowerOrderCLM (Nat.le_succ m) (partialDerivCLM k (V i)))
          have h2 := baseRepresentative_smul_ae (1 / 2 : ℝ)
            (lowerOrderCLM (Nat.le_succ m) (partialDerivCLM k (V i)))
          simp only [domainMeasure, Measure.restrict_univ] at h1 h2
          filter_upwards [h1, h2] with x hx1 hx2
          rw [hx1, hx2, baseRepresentative_lowerOrderCLM, smul_eq_mul]
        rw [← integral_const_mul, ← integral_add
          (integrable_baseRepresentative_mul _ hψ hc)
          ((integrable_baseRepresentative_mul _ hψ hc).const_mul _)]
        exact integral_congr_ae (hae.mono fun x hx ↦ by beta_reduce; rw [hx]; ring)
      have heqk (φ : ℝ^3 → ℝ^3) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
          (hdiv : ∀ x, PDE.divergence φ x = 0) :
          ∑ i, ∫ x, baseRepresentative (vk i) x *
            (φ x i + (1 / 2) * fderiv ℝ φ x x i - PDE.laplacian (fun y ↦ φ y i) x) =
          ∑ i, ∫ x, baseRepresentative (gk i) x * φ x i := by
        simp only [hbase]
        rw [sum_integral_partialDeriv_selfsimilarStokes V g heqV k hφ hc hdiv,
          Finset.sum_congr rfl fun i _ ↦ hgk i (contDiff_component hφ i).continuous
            (hasCompactSupport_component hc i), Finset.sum_add_distrib, Finset.mul_sum]
      obtain ⟨Y, hY⟩ := ih vk hvk gk heqk i
      exact ⟨Y, hY.trans (Filter.EventuallyEq.of_eq (hbase i))⟩
    intro i
    obtain ⟨Z, hZ⟩ := exists_wkpSpace_succ_of_partialDerivCLM (V i) fun k ↦ hk k i
    exact ⟨Z, hZ.trans (hV i)⟩

end NavierStokes.Stationary
