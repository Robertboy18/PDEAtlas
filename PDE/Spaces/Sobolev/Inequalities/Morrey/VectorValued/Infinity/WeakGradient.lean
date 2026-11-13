/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.VectorValued.Mollification.WeakDerivatives
public import PDE.Spaces.Sobolev.Inequalities.Morrey.Endpoint.WeakGradient
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Banach-valued Lipschitz representatives from bounded weak gradients

Norming functionals transfer the scalar Lipschitz estimate to Banach-valued
mollifications. Lebesgue differentiation identifies their limit almost everywhere.
That full-measure set is dense, so completeness of the target extends the limit
uniquely to the whole space without changing its Lipschitz constant.

Only local Bochner integrability and bounded weak derivatives are assumed.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open scoped Convolution NNReal Topology

namespace SobolevSpace.VectorValued

open Approximation

variable {n : ℕ} {F : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Bounds on the weak derivative rows control every positive-scale mollification.
A norming functional for each difference reduces the estimate to the scalar theorem. -/
theorem lipschitzWith_mollifyVector_of_weak_derivative_bound
    (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    {f : ℝ^n → F} (hf : LocallyIntegrable f volume)
    (g : Fin n → ℝ^n → F)
    (hg : ∀ j, HasWeakDerivativeOn ⊤ [j] f (g j))
    (C : Fin n → ℝ≥0)
    (hC : ∀ j, ∀ᵐ x ∂volume, ‖g j x‖ ≤ C j) :
    LipschitzWith (∑ j, C j) (mollifyVector μ ε f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  obtain ⟨L, hL, hxy⟩ := exists_dual_vector'' ℝ
    (mollifyVector μ ε f x - mollifyVector μ ε f y)
  have hgL (j : Fin n) : SobolevSpace.HasWeakDerivativeOn univ [j] (L ∘ f) (L ∘ g j) :=
    hasWeakDerivativeOn_real_iff.mp ((hg j).map L)
  have hCL (j : Fin n) : ∀ᵐ z ∂volume, ‖(L ∘ g j) z‖ ≤ C j := by
    filter_upwards [hC j] with z hz
    exact (L.le_opNorm _).trans ((mul_le_mul_of_nonneg_right hL (norm_nonneg _)).trans
      (by simpa using hz))
  have hLip := Approximation.lipschitzWith_mollify_of_weak_derivative_bound
    μ (ε := ε) (fun j ↦ L ∘ g j) hgL C hCL
  have hmap : L ∘ mollifyVector μ ε f = mollify μ ε (L ∘ f) := by
    rw [mollifyVector_map μ hε L hf, mollifyVector_real]
  calc
    dist (mollifyVector μ ε f x) (mollifyVector μ ε f y) =
        dist (mollify μ ε (L ∘ f) x) (mollify μ ε (L ∘ f) y) := by
      rw [dist_eq_norm, dist_eq_norm, ← congrFun hmap x, ← congrFun hmap y]
      simp only [Function.comp_apply, ← map_sub, hxy]
      simp
    _ ≤ _ := hLip.dist_le_mul x y

/-- Local Bochner integrability and bounded weak coordinate derivatives give a globally
Lipschitz representative in any complete real normed target, including when `n = 0`. -/
theorem exists_lipschitzWith_ae_eq_of_weak_derivative_bound
    {f : ℝ^n → F} (hf : LocallyIntegrable f volume)
    (g : Fin n → ℝ^n → F)
    (hg : ∀ j, HasWeakDerivativeOn ⊤ [j] f (g j))
    (C : Fin n → ℝ≥0)
    (hC : ∀ j, ∀ᵐ x ∂volume, ‖g j x‖ ≤ C j) :
    ∃ v : ℝ^n → F, LipschitzWith (∑ j, C j) v ∧ v =ᵐ[volume] f := by
  let r : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1)
  have hr (k : ℕ) : 0 < r k := by dsimp only [r]; positivity
  have hr0 : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let φ : ℕ → ContDiffBump (0 : ℝ^n) := fun k ↦
    { rIn := r k
      rOut := 2 * r k
      rIn_pos := hr k
      rIn_lt_rOut := by linarith [hr k] }
  let μ : ℕ → Mollifier n := fun k ↦
    { ρ := (φ k).normed volume
      smooth := (φ k).contDiff_normed
      compactSupport := (φ k).hasCompactSupport_normed
      nonneg := (φ k).nonneg_normed
      integral_one := (φ k).integral_normed }
  let u : ℕ → ℝ^n → F := fun k ↦
    ((φ k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f)
  have hu (k : ℕ) : u k = mollifyVector (μ k) 1 f := by
    have hscaled : scaled (μ k) 1 = (φ k).normed volume := by
      rw [scaled_of_pos (μ k) zero_lt_one]
      simp only [inv_one, one_pow, one_smul, one_mul, μ]
    simp only [u, mollifyVector, hscaled]
  have hLip (k : ℕ) : LipschitzWith (∑ j, C j) (u k) := by
    rw [hu k]
    exact lipschitzWith_mollifyVector_of_weak_derivative_bound
      (μ k) zero_lt_one hf g hg C hC
  have hout : Tendsto (fun k ↦ (φ k).rOut) atTop (𝓝 0) := by
    simpa only [φ, mul_zero] using tendsto_const_nhds.mul hr0
  have hae : ∀ᵐ x ∂volume, Tendsto (fun k ↦ u k x) atTop (𝓝 (f x)) :=
    ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hout
      (Eventually.of_forall fun _ ↦ le_rfl : ∀ᶠ k in atTop, (φ k).rOut ≤ 2 * (φ k).rIn) hf
  let good : Set (ℝ^n) := {x | Tendsto (fun k ↦ u k x) atTop (𝓝 (f x))}
  have hgood : LipschitzOnWith (∑ j, C j) f good := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    exact le_of_tendsto (hx.dist hy)
      (Eventually.of_forall fun k ↦ (hLip k).dist_le_mul x y)
  have hdense : Dense good := (volume : Measure (ℝ^n)).dense_of_ae hae
  let v : ℝ^n → F := hdense.extend (good.domRestrict f)
  have hv : Continuous v := hdense.uniformContinuous_extend
    hgood.to_restrict.uniformContinuous |>.continuous
  have heq (x : ℝ^n) (hx : x ∈ good) : v x = f x :=
    hdense.extend_of_ind hgood.to_restrict.uniformContinuous ⟨x, hx⟩
  refine ⟨v, ?_, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    have hclosed : IsClosed {z : (ℝ^n) × (ℝ^n) |
        dist (v z.1) (v z.2) ≤ (∑ j, C j : ℝ≥0) * dist z.1 z.2} :=
      isClosed_le ((hv.comp continuous_fst).dist (hv.comp continuous_snd))
        (continuous_const.mul (continuous_fst.dist continuous_snd))
    apply hclosed.closure_subset_iff.mpr ?_ ((hdense.prod hdense) (x, y))
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    change dist (v a) (v b) ≤ _
    rw [heq a ha, heq b hb]
    exact hgood.dist_le_mul a ha b hb
  · filter_upwards [hae] with x hx
    exact heq x hx

end SobolevSpace.VectorValued
