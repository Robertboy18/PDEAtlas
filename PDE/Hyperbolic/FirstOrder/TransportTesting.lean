/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.FirstOrder.SobolevEnergy
public import PDE.Spaces.Sobolev.Variational.Spaces.WholeSpaceHilbert

/-!
# Testing transport without derivatives of the state

For a fixed H1 test, whole-space integration by parts moves the spatial derivative from
the state to the test and the W1,infinity coefficient. The resulting functional acts on
L2 states. This identity needs neither symmetry nor time regularity of the coefficients.

The Cauchy construction in `L2Cauchy` uses this functional to pass to a uniform L2 limit.
The tested approximant equations supply time measurability; the norm bound controls the limit.

## Implementation notes

The state space `L²(ℝⁿ; ℝᵐ)` is the `PiLp 2` product of `m` copies of the scalar space
`DerivLp n 2 univ`, and the test space `H¹(ℝⁿ; ℝᵐ)` is the `PiLp 2` product of `m` copies of
`H¹(ℝ^n)`. The modules of the first-order `L²` theory write these spaces `H` and `V`. The
coefficient `A j p q` is the `(p, q)` entry of the matrix `Aʲ` in `u_t + ∑ⱼ Aʲ ∂ⱼu = f`.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

namespace PDE.Hyperbolic.FirstOrder

open SobolevSpace SobolevSpace.GraphSpace

open scoped SobolevSpace.WholeSpaceHilbert

variable {n m : ℕ}

local notation "D" => DerivLp n 2 univ
local notation "H" => PiLp 2 (fun _ : Fin m ↦ D)
local notation "V" => PiLp 2 (fun _ : Fin m ↦ H¹(ℝ^n))

/-- The zeroth Sobolev coordinates, with the L2 norm on the finite component product. -/
def transportBaseCLM : V →L[ℝ] H :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m ↦ D)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun p ↦
      (wkpCoordinateCLM (baseIndex n 1)).comp
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m ↦ H¹(ℝ^n)) p))

/-- Evaluation of the product base map is its indicated Sobolev coordinate. -/
@[simp]
theorem transportBaseCLM_apply (U : V) (p : Fin m) :
    transportBaseCLM U p = wkpCoordinateCLM (baseIndex n 1) (U p) := rfl

/-- The original transport drift, evaluated on H1 states using their weak derivatives. -/
def transportDrift
    (A : Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n)))) (U : V) : H :=
  WithLp.toLp 2 (fun p ↦ -(∑ j, ∑ q, ((A j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) •
      wkpCoordinateCLM (singleDerivIndex n j) (U q)))

/-- The original linear transport operator annihilates the zero H1 state. -/
@[simp]
theorem transportDrift_zero (A : Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n)))) :
    transportDrift A (0 : V) = 0 := by
  classical
  refine PiLp.ext fun p ↦ ?_
  change -(∑ j, ∑ q, mulLpLeft ((A j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1))
      (wkpCoordinateCLM (singleDerivIndex n j) (0 : H¹(ℝ^n)))) = 0
  simp only [map_zero, Finset.sum_const_zero, neg_zero]

/-- The spatial term in `u_t = -A^j ∂_j u + f`, after integration by parts.
The coefficient derivative is its weak Sobolev coordinate. This is a functional
of the L2 state; the spatial test remains in H1. -/
def transportTestFunctional
    (A : Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n)))) (φ : V) :
    H →L[ℝ] ℝ :=
  ∑ p, ∑ j, ∑ q,
    (innerSL ℝ
      (((A j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) •
          wkpCoordinateCLM (singleDerivIndex n j) (φ p) +
        ((A j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)) •
          wkpCoordinateCLM (baseIndex n 1) (φ p))).comp
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m ↦ D) q)

/-- Evaluation displays both the differentiated-test and differentiated-coefficient terms. -/
theorem transportTestFunctional_apply
    (A : Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n)))) (φ : V) (u : H) :
    transportTestFunctional A φ u =
      ∑ p, ∑ j, ∑ q, ⟪u q,
        ((A j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) •
            wkpCoordinateCLM (singleDerivIndex n j) (φ p) +
          ((A j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)) •
            wkpCoordinateCLM (baseIndex n 1) (φ p)⟫_ℝ := by
  classical
  simp only [transportTestFunctional, sum_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, PiLp.proj_apply]
  exact Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun j _ ↦
    Finset.sum_congr rfl fun q _ ↦ real_inner_comm _ _

/-- Whole-space H1 integration by parts identifies the original drift with its L2 test
functional. There is no boundary term and no extra decay hypothesis. -/
theorem inner_transportDrift_eq
    (A : Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n)))) (U φ : V) :
    ⟪transportDrift A U, transportBaseCLM φ⟫_ℝ =
      transportTestFunctional A φ (transportBaseCLM U) := by
  classical
  rw [transportTestFunctional_apply]
  simp only [transportDrift, PiLp.inner_apply, transportBaseCLM_apply,
    inner_neg_left, sum_inner, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun j _ ↦
    Finset.sum_congr rfl fun q _ ↦ ?_
  simp only [wkpCoordinateCLM_apply]
  have h := inner_mul_deriv_add_inner_mul_deriv_univ (A j p q) j (U q) (φ p)
  rw [Lp.inner_lpSMul_left ((A j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j))
    ((U q : WkpAmbientOn n 1 2 univ) (baseIndex n 1))
    ((φ p : WkpAmbientOn n 1 2 univ) (baseIndex n 1))] at h
  rw [inner_add_right]
  rw [← real_inner_comm (((A j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) •
      ((φ p : WkpAmbientOn n 1 2 univ) (singleDerivIndex n j)))] at h
  linarith only [h]

private theorem norm_transportTestRow_le (a da : DerivLp n ∞ univ) (v dv : D) (q : Fin m) {M C : ℝ}
    (hM : 0 ≤ M) (hC : 0 ≤ C) (ha : ‖a‖ ≤ M) (hda : ‖da‖ ≤ C) :
    ‖(innerSL ℝ (a • dv + da • v)).comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m ↦ D) q)‖ ≤
      M * ‖dv‖ + C * ‖v‖ := by
  have hnonneg : 0 ≤ M * ‖dv‖ + C * ‖v‖ :=
    add_nonneg (mul_nonneg hM (norm_nonneg _)) (mul_nonneg hC (norm_nonneg _))
  have hterm : ‖a • dv + da • v‖ ≤ M * ‖dv‖ + C * ‖v‖ := (norm_add_le _ _).trans (add_le_add
      ((Lp.norm_smul_le a dv).trans (mul_le_mul_of_nonneg_right ha (norm_nonneg _)))
      ((Lp.norm_smul_le da v).trans (mul_le_mul_of_nonneg_right hda (norm_nonneg _))))
  refine ContinuousLinearMap.opNorm_le_bound _ hnonneg fun u ↦ ?_
  change ‖⟪a • dv + da • v, u q⟫_ℝ‖ ≤ (M * ‖dv‖ + C * ‖v‖) * ‖u‖
  exact (norm_inner_le_norm _ _).trans
    (mul_le_mul hterm (PiLp.norm_apply_le u q) (norm_nonneg _) hnonneg)

/-- Entrywise bounds on the coefficients and their divergence derivatives bound the
spatial test functional. The test contributes its fixed H1 coordinates. -/
theorem norm_transportTestFunctional_le (A : Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n))))
    (φ : V) {M C : ℝ} (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hA : ∀ j p q, ‖(A j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)‖ ≤ M)
    (hdA : ∀ j p q, ‖(A j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)‖ ≤ C) :
    ‖transportTestFunctional A φ‖ ≤ ∑ p : Fin m, ∑ j : Fin n, ∑ _q : Fin m,
      (M * ‖wkpCoordinateCLM (singleDerivIndex n j) (φ p)‖ + C *
      ‖wkpCoordinateCLM (baseIndex n 1) (φ p)‖) := by
  classical
  unfold transportTestFunctional
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ ↦ (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun j _ ↦ (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ ↦ ?_)))
  exact norm_transportTestRow_le ((A j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1))
    ((A j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j))
    (wkpCoordinateCLM (baseIndex n 1) (φ p))
    (wkpCoordinateCLM (singleDerivIndex n j) (φ p)) q hM hC (hA j p q) (hdA j p q)

private theorem entry_le_triple_sum {ι κ η : Type*} [Fintype ι] [Fintype κ] [Fintype η]
    (f : ι → κ → η → ℝ) (hf : ∀ i j k, 0 ≤ f i j k) (i : ι) (j : κ) (k : η) :
    f i j k ≤ ∑ i', ∑ j', ∑ k', f i' j' k' := by
  classical
  exact (Finset.single_le_sum (fun k' _ ↦ hf i j k') (Finset.mem_univ k)).trans
    ((Finset.single_le_sum (fun j' _ ↦ Finset.sum_nonneg fun k' _ ↦ hf i j' k')
      (Finset.mem_univ j)).trans (Finset.single_le_sum (fun i' _ ↦ Finset.sum_nonneg fun j' _ ↦
          Finset.sum_nonneg fun k' _ ↦ hf i' j' k') (Finset.mem_univ i)))

/-- Base-coefficient continuity on a compact time interval and a bound on the
divergence derivatives bound each fixed spatial test. -/
theorem exists_bound_transportTestFunctional
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n)))) {a b C : ℝ}
    (hA : ∀ j p q,
      ContinuousOn (fun t ↦ (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) (Icc a b))
    (hC : 0 ≤ C)
    (hdiv : ∀ t ∈ Icc a b,
      (∑ j, ∑ p, ∑ q, ‖(A t j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)‖) ≤ C)
    (φ : V) :
    ∃ K ≥ 0, ∀ t ∈ Icc a b, ‖transportTestFunctional (A t) φ‖ ≤ K := by
  classical
  let total := fun t ↦ ∑ j, ∑ p, ∑ q, ‖(A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)‖
  have htotal : ContinuousOn total (Icc a b) :=
    continuousOn_finsetSum _ fun j _ ↦ continuousOn_finsetSum _ fun p _ ↦
      continuousOn_finsetSum _ fun q _ ↦ (hA j p q).norm
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn htotal
  refine ⟨∑ p : Fin m, ∑ j : Fin n, ∑ _q : Fin m,
    (max 0 M * ‖wkpCoordinateCLM (singleDerivIndex n j) (φ p)‖ +
      C * ‖wkpCoordinateCLM (baseIndex n 1) (φ p)‖), by positivity, ?_⟩
  intro t ht
  apply norm_transportTestFunctional_le _ _ (le_max_left _ _) hC
  · exact fun j p q ↦ (entry_le_triple_sum
      (fun j p q ↦ ‖(A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)‖)
      (fun _ _ _ ↦ norm_nonneg _) j p q).trans
      ((le_abs_self (total t)).trans ((hM t ht).trans (le_max_right _ _)))
  · exact fun j p q ↦ (entry_le_triple_sum (fun j p q ↦ ‖(A t j p q : WkpAmbientOn n 1 ∞ univ)
        (singleDerivIndex n j)‖) (fun _ _ _ ↦ norm_nonneg _) j p q).trans (hdiv t ht)

end PDE.Hyperbolic.FirstOrder
