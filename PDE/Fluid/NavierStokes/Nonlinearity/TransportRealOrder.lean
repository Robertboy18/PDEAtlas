/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.Incompressible.LerayProjection.OrderLowering
public import PDE.Fluid.NavierStokes.Nonlinearity.SobolevTransport
public import PDE.Spaces.Sobolev.Fractional.Integer.RealOrders

/-!
# The linear transport operator between Sobolev spaces of real order

The linearization of the convective term around a velocity field `b` is the first-order operator
`v ↦ (b·∇)v + c v`, with `c = ∇b`, followed by the Leray projection. Does it map `H^{σ+1}` to
`H^σ` for every real `σ ≥ 0`, with a bound that is small when `b` and `c` are small? A fixed
point argument for a perturbation with a small coefficient field rests on the second half of
the question. This module answers both, in every dimension `n`, for coefficients in
`W^{k+1,∞}` with `k ≤ σ ≤ k + 1`: the bound is a constant times the sum of the norms of the
coefficients. The coefficients have `⌊σ⌋ + 1` bounded derivatives here. Coefficients of less
regularity, and the bilinear dependence on a coefficient in a Sobolev space of real order, are
not treated.

## Main results

* `besselEnergy_comp_transport_le`: for every dimension `n`, every `k ≥ 0`, all coefficients
  `b`, `c` in `W^{k+1,∞}`, every additive map `P` with lifts of norm at most one at the orders
  `k` and `k + 1`, every real `k ≤ σ ≤ k + 1` and every `v ∈ H¹`,
  `E_σ(P((b·∇)v + c v)) ≤ (C ∑ (‖b‖ + ‖c‖))² E_{σ+1}(v)`.
* `besselEnergy_transport_le`: the case `P = 1`.
* `besselEnergy_leraySobolev_transport_le`: the case of the Leray projection, the linearized
  convection `v ↦ Π((b·∇)v + c v)`.

## How it works

At every integer order `k` the operator is `linearTransport k b c`, from `H^{k+1}` to `H^k`,
with norm at most a constant times the sum of the `W^{k,∞}` norms of the coefficients, and the
operators at different orders agree on common fields
(`vectorLowerOrderCLM_zero_linearTransport`). An operator of order one with such lifts at the
orders `k` and `k + 1` is bounded from `H^{σ+1}` to `H^σ` for `k ≤ σ ≤ k + 1`, with a constant
linear in the norms of the lifts (`besselEnergy_le_of_lift_pair`). A map of order zero after it,
such as the Leray projection, changes nothing as long as its lifts have norm at most one. The
operator at the bottom is `BoundedTransport.transport` on `H¹` fields.
-/

@[expose] public noncomputable section

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Fractional IncompressibleFlow
open scoped ENNReal NNReal Sobolev

namespace NavierStokes.SobolevConvection

variable {n : ℕ}

/-- The constant of the transport operator between the real orders `σ + 1` and `σ`,
`k ≤ σ ≤ k + 1`. -/
def transportOrderConst (n k : ℕ) : ℝ :=
  orderConst n (k + 1) k *
    (wkTopMultiplierNormBound n k + wkTopMultiplierNormBound n (k + 1) + 1)

/-- The transport operator on `H¹` fields is bounded by the sum of the norms of its
coefficients, taken at any order. -/
theorem norm_transport_base_le (k : ℕ) (b : Fin n → W^{k,∞}(ℝ^n))
    (c : Fin n → Fin n → W^{k,∞}(ℝ^n)) :
    ‖BoundedTransport.transport (fun i ↦ wkpBaseCoordinateCLM (b i))
      (fun j i ↦ wkpBaseCoordinateCLM (c j i))‖ ≤ transportCoefficientBound k b c :=
  (BoundedTransport.norm_transport_le _ _).trans
    (Finset.sum_le_sum fun j _ ↦ Finset.sum_le_sum fun i _ ↦
      add_le_add (wkpBaseCoordinateCLM_norm_le (b i)) (wkpBaseCoordinateCLM_norm_le (c j i)))

/-- Lowering the order of the coefficients does not increase their bound. -/
theorem transportCoefficientBound_lowerOrderCLM_le (k : ℕ) (b : Fin n → W^{k + 1,∞}(ℝ^n))
    (c : Fin n → Fin n → W^{k + 1,∞}(ℝ^n)) :
    transportCoefficientBound k (fun i ↦ lowerOrderCLM (Nat.le_succ k) (b i))
      (fun j i ↦ lowerOrderCLM (Nat.le_succ k) (c j i)) ≤ transportCoefficientBound (k + 1) b c :=
  Finset.sum_le_sum fun j _ ↦ Finset.sum_le_sum fun i _ ↦
    add_le_add (norm_lowerOrderCLM_apply_le _ (b i)) (norm_lowerOrderCLM_apply_le _ (c j i))

/-- A contraction after the transport of order `k` has the norm bound of the transport. -/
theorem norm_comp_linearTransport_le {k : ℕ} {P : VectorH n k →L[ℝ] VectorH n k} (hP : ‖P‖ ≤ 1)
    (b : Fin n → W^{k,∞}(ℝ^n)) (c : Fin n → Fin n → W^{k,∞}(ℝ^n)) :
    ‖P ∘L linearTransport k b c‖ ≤
      wkTopMultiplierNormBound n k * transportCoefficientBound k b c := by
  refine (ContinuousLinearMap.opNorm_comp_le P (linearTransport k b c)).trans ?_
  have h := mul_le_mul hP (norm_linearTransport_le k b c) (norm_nonneg _) zero_le_one
  rwa [one_mul] at h

/-- **The transport operator between real orders, followed by a map of order zero.** Let the
coefficients `b`, `c` be in `W^{k+1,∞}(ℝⁿ)`, and let `P` be an additive map on vector fields in
`L²` with lifts `P₀`, `P₁` of norm at most one at the orders `k` and `k + 1`. Then, for every
real `k ≤ σ ≤ k + 1` and every `v ∈ H¹`,

`E_σ(P((b·∇)v + c v)) ≤ (transportOrderConst n k · ∑ⱼᵢ (‖bᵢ‖ + ‖cⱼᵢ‖))² E_{σ+1}(v)`,

with the norms of the coefficients in `W^{k+1,∞}`. -/
theorem besselEnergy_comp_transport_le (k : ℕ) (b : Fin n → W^{k + 1,∞}(ℝ^n))
    (c : Fin n → Fin n → W^{k + 1,∞}(ℝ^n)) {P : VectorH n 0 → VectorH n 0}
    (hP : ∀ x y, P (x + y) = P x + P y) {P₀ : VectorH n k →L[ℝ] VectorH n k}
    {P₁ : VectorH n (k + 1) →L[ℝ] VectorH n (k + 1)}
    (hP₀ : ∀ u, vectorLowerOrderCLM (Nat.zero_le k) (P₀ u) =
      P (vectorLowerOrderCLM (Nat.zero_le k) u))
    (hP₁ : ∀ u, vectorLowerOrderCLM (Nat.zero_le (k + 1)) (P₁ u) =
      P (vectorLowerOrderCLM (Nat.zero_le (k + 1)) u))
    (h₀ : ‖P₀‖ ≤ 1) (h₁ : ‖P₁‖ ≤ 1) {σ : ℝ} (hk : (k : ℝ) ≤ σ) (hk1 : σ ≤ k + 1)
    (v : VectorH n 1) :
    besselEnergy σ (vectorBaseL2 (P (BoundedTransport.transport
        (fun i ↦ wkpBaseCoordinateCLM (b i)) (fun j i ↦ wkpBaseCoordinateCLM (c j i)) v))) ≤
      ENNReal.ofReal ((transportOrderConst n k * transportCoefficientBound (k + 1) b c) ^ 2) *
        besselEnergy (σ + 1) (vectorBaseL2 v) := by
  set B : ℝ := transportCoefficientBound (k + 1) b c with hB
  have hB0 : 0 ≤ B := transportCoefficientBound_nonneg (k + 1) b c
  set T : VectorH n 1 → VectorH n 0 := fun v ↦ P (BoundedTransport.transport
    (fun i ↦ wkpBaseCoordinateCLM (b i)) (fun j i ↦ wkpBaseCoordinateCLM (c j i)) v) with hT
  rcases hB0.eq_or_lt with hzero | hpos
  · -- no coefficients: the operator vanishes
    have hP0 : P 0 = 0 := by
      have h := hP 0 0
      rw [add_zero] at h
      exact left_eq_add.mp h
    have hv : BoundedTransport.transport (fun i ↦ wkpBaseCoordinateCLM (b i))
        (fun j i ↦ wkpBaseCoordinateCLM (c j i)) v = 0 := by
      have h := (ContinuousLinearMap.le_opNorm _ v).trans
        (mul_le_mul_of_nonneg_right (norm_transport_base_le (k + 1) b c) (norm_nonneg v))
      rw [← hB, ← hzero, zero_mul] at h
      exact norm_le_zero_iff.mp h
    rw [hv, hP0, vectorBaseL2_zero, besselEnergy_fun_zero]
    exact zero_le
  -- the lifts at the orders `k` and `k + 1`
  have hG₀ (u : VectorH n (k + 1)) : vectorLowerOrderCLM (Nat.zero_le k)
      ((P₀ ∘L linearTransport k (fun i ↦ lowerOrderCLM (Nat.le_succ k) (b i))
        (fun j i ↦ lowerOrderCLM (Nat.le_succ k) (c j i))) u) =
      T (vectorLowerOrderCLM (Nat.le_add_left 1 k) u) := by
    rw [ContinuousLinearMap.comp_apply, hP₀, vectorLowerOrderCLM_zero_linearTransport]
    simp only [wkpBaseCoordinateCLM_lowerOrderCLM]
    rfl
  have hG₁ (u : VectorH n (k + 1 + 1)) : vectorLowerOrderCLM (Nat.zero_le (k + 1))
      ((P₁ ∘L linearTransport (k + 1) b c) u) =
      T (vectorLowerOrderCLM (Nat.le_add_left 1 (k + 1)) u) := by
    rw [ContinuousLinearMap.comp_apply, hP₁, vectorLowerOrderCLM_zero_linearTransport]
  have hw₀ := wkTopMultiplierNormBound_nonneg n k
  have hw₁ := wkTopMultiplierNormBound_nonneg n (k + 1)
  have hlow := transportCoefficientBound_lowerOrderCLM_le k b c
  set K : ℝ := (wkTopMultiplierNormBound n k + wkTopMultiplierNormBound n (k + 1) + 1) * B
    with hK
  have hK0 : 0 < K := by positivity
  have hn₀ : ‖P₀ ∘L linearTransport k (fun i ↦ lowerOrderCLM (Nat.le_succ k) (b i))
      (fun j i ↦ lowerOrderCLM (Nat.le_succ k) (c j i))‖ ≤ K := by
    refine (norm_comp_linearTransport_le h₀ _ _).trans ?_
    rw [hK]
    nlinarith [mul_le_mul_of_nonneg_left hlow hw₀, mul_nonneg hw₁ hB0]
  have hn₁ : ‖P₁ ∘L linearTransport (k + 1) b c‖ ≤ K := by
    refine (norm_comp_linearTransport_le h₁ b c).trans ?_
    rw [hK, ← hB]
    nlinarith [mul_nonneg hw₀ hB0]
  have hTadd (x y : VectorH n 1) : T (x + y) = T x + T y := by
    rw [hT]
    simp only [map_add, hP]
  have h := besselEnergy_le_of_lift_pair rfl rfl hTadd hG₀ hG₁ hK0 hn₀ hn₁ hk hk1 v
  have e : orderConst n (k + 1) k * K = transportOrderConst n k * B := by
    rw [hK, transportOrderConst]
    ring
  have e' : σ + ((k + 1 : ℕ) : ℝ) - (k : ℝ) = σ + 1 := by
    push_cast
    ring
  rwa [e, e'] at h

/-- **The transport operator from `H^{σ+1}` to `H^σ`**, for real `k ≤ σ ≤ k + 1` and
coefficients in `W^{k+1,∞}(ℝⁿ)`:
`E_σ((b·∇)v + c v) ≤ (transportOrderConst n k · ∑ⱼᵢ (‖bᵢ‖ + ‖cⱼᵢ‖))² E_{σ+1}(v)`. -/
theorem besselEnergy_transport_le (k : ℕ) (b : Fin n → W^{k + 1,∞}(ℝ^n))
    (c : Fin n → Fin n → W^{k + 1,∞}(ℝ^n)) {σ : ℝ} (hk : (k : ℝ) ≤ σ) (hk1 : σ ≤ k + 1)
    (v : VectorH n 1) :
    besselEnergy σ (vectorBaseL2 (BoundedTransport.transport
        (fun i ↦ wkpBaseCoordinateCLM (b i)) (fun j i ↦ wkpBaseCoordinateCLM (c j i)) v)) ≤
      ENNReal.ofReal ((transportOrderConst n k * transportCoefficientBound (k + 1) b c) ^ 2) *
        besselEnergy (σ + 1) (vectorBaseL2 v) :=
  besselEnergy_comp_transport_le k b c (P := id) (fun _ _ ↦ rfl)
    (P₀ := ContinuousLinearMap.id ℝ _) (P₁ := ContinuousLinearMap.id ℝ _) (fun _ ↦ rfl)
    (fun _ ↦ rfl) ContinuousLinearMap.norm_id_le ContinuousLinearMap.norm_id_le hk hk1 v

/-- **The linearized convection from `H^{σ+1}` to `H^σ`**, for real `k ≤ σ ≤ k + 1` and
coefficients in `W^{k+1,∞}(ℝⁿ)`:
`E_σ(Π((b·∇)v + c v)) ≤ (transportOrderConst n k · ∑ⱼᵢ (‖bᵢ‖ + ‖cⱼᵢ‖))² E_{σ+1}(v)`, where `Π` is
the Leray projection. -/
theorem besselEnergy_leraySobolev_transport_le (k : ℕ) (b : Fin n → W^{k + 1,∞}(ℝ^n))
    (c : Fin n → Fin n → W^{k + 1,∞}(ℝ^n)) {σ : ℝ} (hk : (k : ℝ) ≤ σ) (hk1 : σ ≤ k + 1)
    (v : VectorH n 1) :
    besselEnergy σ (vectorBaseL2 (leraySobolev n 0 (BoundedTransport.transport
        (fun i ↦ wkpBaseCoordinateCLM (b i)) (fun j i ↦ wkpBaseCoordinateCLM (c j i)) v))) ≤
      ENNReal.ofReal ((transportOrderConst n k * transportCoefficientBound (k + 1) b c) ^ 2) *
        besselEnergy (σ + 1) (vectorBaseL2 v) :=
  besselEnergy_comp_transport_le k b c (P := fun x ↦ leraySobolev n 0 x)
    (fun x y ↦ map_add _ x y) (P₀ := leraySobolev n k) (P₁ := leraySobolev n (k + 1))
    (fun u ↦ vectorLowerOrderCLM_leraySobolev (Nat.zero_le k) u)
    (fun u ↦ vectorLowerOrderCLM_leraySobolev (Nat.zero_le (k + 1)) u)
    norm_leraySobolev_operator_le norm_leraySobolev_operator_le hk hk1 v

end NavierStokes.SobolevConvection
