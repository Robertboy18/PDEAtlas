/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Pullback.Dilation.FirstOrder
public import PDE.Spaces.Sobolev.Calculus.Slicing.HigherOrder
public import PDE.Spaces.Sobolev.Foundations.Representatives.Algebra

/-!
# Scalar dilation on whole-space Sobolev graphs of every integer order

Each derivative word acquires one scalar factor per derivative. Apply the
proved first-order dilation rule to each derivative prefix, then concatenate
the weak derivative steps. The resulting bounded map acts on the actual graph
coordinates, with no regularity or dilation-preservation hypothesis supplied.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace
open scoped ENNReal Sobolev

namespace SobolevSpace.GraphSpace

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

local notation "μ" => domainMeasure n univ

private def dilationWord (a : ℝ) (ha : a ≠ 0) (u : W^{k,p}(ℝ^n))
    (α : List (Fin n)) : ℝ^n → ℝ :=
  if hα : α.length ≤ k then dilationWkpAmbientCLM a ha u (derivIndexOfList α hα) else 0

private theorem dilationWord_step (hp : p ≠ ∞) (a : ℝ) (ha : a ≠ 0)
    (u : W^{k,p}(ℝ^n)) (α : List (Fin n)) (i : Fin n) (hα : α.length < k) :
    HasWeakDerivativeOn univ [i] (dilationWord a ha u α)
      (dilationWord a ha u (α ++ [i])) := by
  have hαi : (α ++ [i]).length ≤ k := by simpa using hα
  have hlength : α.length + 1 ≤ k := by omega
  let v := dilationW1pCLM hp a ha (derivativeWordCLM α hlength u)
  have hweak : HasWeakDerivativeOn univ [i]
      (wkpBaseCoordinateCLM v : ℝ^n → ℝ)
      (wkpCoordinateCLM (singleDerivIndex n i) v : ℝ^n → ℝ) := by
    simpa only [singleDerivIndex_toList, wkpBaseCoordinateCLM_apply, wkpCoordinateCLM_apply]
      using v.property (singleDerivIndex n i)
  have hlen : (derivIndexOfList α hα.le : DerivIndex n k).toList.length = α.length :=
    (derivIndexOfList_toList_perm α hα.le).length_eq
  have hleni : (derivIndexOfList (α ++ [i]) hαi : DerivIndex n k).toList.length =
      (α ++ [i]).length := (derivIndexOfList_toList_perm (α ++ [i]) hαi).length_eq
  have hdBase : wkpBaseCoordinateCLM v =
      Lp.compSMul μ p a ha (wkpCoordinateCLM (derivIndexOfList α hα.le) u) := by
    change wkpCoordinateCLM (baseIndex n 1)
      (dilationW1pCLM hp a ha (derivativeWordCLM α hlength u)) = _
    rw [dilationW1pCLM_coordinate]
    simp only [baseIndex_toList, List.length_nil, pow_zero, one_smul,
      wkpCoordinateCLM_apply, derivativeWordCLM_apply, derivativeWordIndex_baseIndex]
  have hdRow : wkpCoordinateCLM (singleDerivIndex n i) v =
      a • Lp.compSMul μ p a ha (wkpCoordinateCLM (derivIndexOfList (α ++ [i]) hαi) u) := by
    change wkpCoordinateCLM (singleDerivIndex n i)
      (dilationW1pCLM hp a ha (derivativeWordCLM α hlength u)) = _
    rw [dilationW1pCLM_coordinate]
    simp only [singleDerivIndex_toList, List.length_singleton, pow_one,
      wkpCoordinateCLM_apply, derivativeWordCLM_apply, derivativeWordIndex_singleDerivIndex]
  have hbaseEq : dilationWkpAmbientCLM a ha u (derivIndexOfList α hα.le) =
      a ^ α.length • wkpBaseCoordinateCLM v := by
    rw [dilationWkpAmbientCLM_coordinate, hlen, hdBase]
  have hrowEq : dilationWkpAmbientCLM a ha u (derivIndexOfList (α ++ [i]) hαi) =
      a ^ α.length • wkpCoordinateCLM (singleDerivIndex n i) v := by
    rw [dilationWkpAmbientCLM_coordinate, hleni, hdRow, smul_smul,
      List.length_append, List.length_singleton, pow_succ]
  have hbase : dilationWord a ha u α =ᵐ[μ]
      fun x ↦ a ^ α.length * wkpBaseCoordinateCLM v x := by
    simp only [dilationWord, dite_eq_left hα.le, hbaseEq]
    exact Lp.coeFn_smul _ _
  have hrow : dilationWord a ha u (α ++ [i]) =ᵐ[μ]
      fun x ↦ a ^ α.length * wkpCoordinateCLM (singleDerivIndex n i) v x := by
    simp only [dilationWord, dite_eq_left hαi, hrowEq]
    exact Lp.coeFn_smul _ _
  exact (hasWeakDerivativeOn_smul (a ^ α.length) hweak).congr_ae hbase.symm hrow.symm

/-- All scaled derivative rows satisfy the actual finite-order weak graph identities. -/
theorem dilationWkpAmbientCLM_mem (hp : p ≠ ∞) (a : ℝ) (ha : a ≠ 0)
    (u : W^{k,p}(ℝ^n)) : dilationWkpAmbientCLM a ha u ∈ wkpSubmoduleOn n k p univ := by
  intro α
  have hnil : dilationWord a ha u [] = dilationWkpAmbientCLM a ha u (baseIndex n k) := by
    simp only [dilationWord, List.length_nil, dite_eq_left (Nat.zero_le k), derivIndexOfList_nil]
  have hloc : LocallyIntegrableOn (dilationWord a ha u []) univ volume := by
    rw [hnil]
    exact memLp_locallyIntegrableOn_domain (Lp.memLp _) Fact.out
  have h := hasWeakDerivativeOn_of_append_single_chain_order k (dilationWord a ha u)
    hloc (fun β i hβ ↦ dilationWord_step hp a ha u β i hβ) α.toList α.toList_length_le
  rw [hnil] at h
  simpa only [dilationWord, dite_eq_left α.toList_length_le, derivIndexOfList_toList] using h

/-- Nonzero scalar dilation on actual whole-space Sobolev graphs of every order. -/
def dilationWkpCLM (hp : p ≠ ∞) (a : ℝ) (ha : a ≠ 0) :
    W^{k,p}(ℝ^n) →L[ℝ] W^{k,p}(ℝ^n) :=
  (dilationWkpAmbientCLM a ha).codRestrict (wkpSubmoduleOn n k p univ)
    (dilationWkpAmbientCLM_mem hp a ha)

/-- Every weak derivative row has the correct spatial scale and scalar power. -/
theorem dilationWkpCLM_coordinate (hp : p ≠ ∞) (a : ℝ) (ha : a ≠ 0)
    (u : W^{k,p}(ℝ^n)) (α : DerivIndex n k) :
    wkpCoordinateCLM α (dilationWkpCLM hp a ha u) =
      a ^ α.toList.length • Lp.compSMul μ p a ha (wkpCoordinateCLM α u) := rfl

/-- The physical base function is the literal scalar dilation of the input. -/
theorem dilationWkpCLM_base_ae (hp : p ≠ ∞) (a : ℝ) (ha : a ≠ 0) (u : W^{k,p}(ℝ^n)) :
    baseRepresentative (dilationWkpCLM hp a ha u) =ᵐ[μ]
      fun x ↦ baseRepresentative u (a • x) :=
  dilationWkpAmbientCLM_base_ae a ha u

/-- Exact change of variables and derivative scaling in every Sobolev coordinate. -/
theorem norm_dilationWkpCLM_coordinate (hp : p ≠ ∞) (a : ℝ) (ha : a ≠ 0)
    (u : W^{k,p}(ℝ^n)) (α : DerivIndex n k) :
    ‖wkpCoordinateCLM α (dilationWkpCLM hp a ha u)‖ =
      |a| ^ α.toList.length * |(a ^ n)⁻¹| ^ (1 / p).toReal * ‖wkpCoordinateCLM α u‖ := by
  rw [dilationWkpCLM_coordinate, norm_smul, Lp.norm_compSMul]
  simp only [Real.norm_eq_abs, abs_pow, finrank_euclideanSpace_fin, mul_assoc]

@[simp]
theorem dilationWkpCLM_one (hp : p ≠ ∞) (u : W^{k,p}(ℝ^n)) :
    dilationWkpCLM hp 1 one_ne_zero u = u := by
  apply Subtype.ext
  apply PiLp.ext
  intro α
  change wkpCoordinateCLM α (dilationWkpCLM hp 1 one_ne_zero u) = wkpCoordinateCLM α u
  rw [dilationWkpCLM_coordinate]
  simp only [one_pow, one_smul, Lp.compSMul_one]

/-- Composition of actual Sobolev dilations multiplies their spatial factors. -/
theorem dilationWkpCLM_mul (hp : p ≠ ∞) (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (u : W^{k,p}(ℝ^n)) :
    dilationWkpCLM hp (a * b) (mul_ne_zero ha hb) u =
      dilationWkpCLM hp a ha (dilationWkpCLM hp b hb u) := by
  apply Subtype.ext
  apply PiLp.ext
  intro α
  change wkpCoordinateCLM α (dilationWkpCLM hp (a * b) (mul_ne_zero ha hb) u) =
    wkpCoordinateCLM α (dilationWkpCLM hp a ha (dilationWkpCLM hp b hb u))
  simp only [dilationWkpCLM_coordinate, map_smul, smul_smul,
    ← Lp.compSMul_mul, ← mul_pow]

/-- A dilation factor at least one gives an explicit whole-graph Hilbert norm bound. -/
theorem norm_dilationWkpCLM_le_of_one_le (hp : (2 : ℝ≥0∞) ≠ ∞) {a : ℝ} (ha : 1 ≤ a)
    (u : W^{k,2}(ℝ^n)) :
    ‖dilationWkpCLM hp a (by linarith) u‖ ≤
      a ^ k * |(a ^ n)⁻¹| ^ (1 / (2 : ℝ≥0∞)).toReal * ‖u‖ := by
  let C := a ^ k * |(a ^ n)⁻¹| ^ (1 / (2 : ℝ≥0∞)).toReal
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hrow (α : DerivIndex n k) :
      ‖wkpCoordinateCLM α (dilationWkpCLM hp a (by linarith) u)‖ ≤
        C * ‖wkpCoordinateCLM α u‖ := by
    rw [norm_dilationWkpCLM_coordinate, abs_of_nonneg (by linarith : 0 ≤ a)]
    dsimp [C]
    gcongr
    exact α.toList_length_le
  have hsum : ∑ α : DerivIndex n k,
      ‖wkpCoordinateCLM α (dilationWkpCLM hp a (by linarith) u)‖ ^ 2 ≤
        C ^ 2 * ∑ α : DerivIndex n k, ‖wkpCoordinateCLM α u‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun α _ ↦ by
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (hrow α) 2
  change ‖(dilationWkpCLM hp a (by linarith) u).val‖ ≤ C * ‖u.val‖
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  calc
    _ ≤ Real.sqrt (C ^ 2 * ∑ α : DerivIndex n k, ‖wkpCoordinateCLM α u‖ ^ 2) :=
      Real.sqrt_le_sqrt hsum
    _ = _ := by rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC]; rfl

/-- Reciprocal dilation recovers every weak derivative coordinate. -/
@[simp]
theorem dilationWkpCLM_inv_dilationWkpCLM (hp : p ≠ ∞) (a : ℝ) (ha : a ≠ 0)
    (u : W^{k,p}(ℝ^n)) :
    dilationWkpCLM hp a⁻¹ (inv_ne_zero ha) (dilationWkpCLM hp a ha u) = u := by
  apply Subtype.ext
  apply PiLp.ext
  intro α
  change wkpCoordinateCLM α (dilationWkpCLM hp a⁻¹ (inv_ne_zero ha)
    (dilationWkpCLM hp a ha u)) = wkpCoordinateCLM α u
  rw [dilationWkpCLM_coordinate, dilationWkpCLM_coordinate, map_smul,
    Lp.compSMul_inv_compSMul, smul_smul, inv_pow,
    inv_mul_cancel₀ (pow_ne_zero _ ha), one_smul]

end SobolevSpace.GraphSpace
