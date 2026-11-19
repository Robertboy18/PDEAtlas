/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Slicing.HigherOrder
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Higher Sobolev recovery from first weak derivatives

An `L²` function whose first weak derivatives lie in `Hᵏ` belongs to `H^{k+1}`.
The construction takes each nonempty derivative word from the corresponding
first-derivative bundle. Its norm is controlled by the `L²` base norm and the
sum of the `Hᵏ` norms of the first derivatives.

This form of recovery needs no initial `Hᵏ` representative of the base function.
It applies, for example, to a locally `L²` potential gradient once its Hessian
has been recovered in a Sobolev space.
-/

@[expose] public noncomputable section
set_option linter.missingDocs true

namespace SobolevSpace.GraphSpace

open MeasureTheory
open scoped ENNReal Sobolev

variable {n k : ℕ} {Ω : Set ℝ^n}

private def firstDerivativeWord (f : ℝ^n → ℝ) (V : Fin n → W^{k,2}(Ω))
    (α : List (Fin n)) (hα : α.length ≤ k + 1) : ℝ^n → ℝ :=
  match α with
  | [] => f
  | i :: β => ((V i : WkpAmbientOn n k 2 Ω)
      (derivIndexOfList β (by simp only [List.length_cons] at hα; omega)) : ℝ^n → ℝ)

private theorem firstDerivativeWord_memLp
    (f : ℝ^n → ℝ) (hf : MemLp f 2 (domainMeasure n Ω))
    (V : Fin n → W^{k,2}(Ω)) (α : List (Fin n)) (hα : α.length ≤ k + 1) :
    MemLp (firstDerivativeWord f V α hα) 2 (domainMeasure n Ω) := by
  cases α with
  | nil => exact hf
  | cons i β => exact Lp.memLp _

private theorem firstDerivativeWord_hasWeakDerivativeOn
    (f : ℝ^n → ℝ) (hf : MemLp f 2 (domainMeasure n Ω))
    (V : Fin n → W^{k,2}(Ω))
    (hV : ∀ i, HasWeakDerivativeOn Ω [i] f (baseRepresentative (V i)))
    (α : List (Fin n)) (hα : α.length ≤ k + 1) :
    HasWeakDerivativeOn Ω α f (firstDerivativeWord f V α hα) := by
  cases α with
  | nil => exact hasWeakDerivativeOn_nil (memLp_locallyIntegrableOn_domain hf (by norm_num))
  | cons i β =>
      exact HasWeakDerivativeOn.append_from_wkp (V i) [i] β
        (by simp only [List.length_cons] at hα; omega) (hV i)

private theorem firstDerivativeWord_lpNorm_le
    (f : ℝ^n → ℝ) (V : Fin n → W^{k,2}(Ω))
    (α : List (Fin n)) (hα : α.length ≤ k + 1) :
    lpNorm (firstDerivativeWord f V α hα) 2 (domainMeasure n Ω) ≤
      lpNorm f 2 (domainMeasure n Ω) + ∑ i, ‖V i‖ := by
  classical
  cases α with
  | nil => exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
  | cons i β =>
      change ‖((V i : WkpAmbientOn n k 2 Ω) (derivIndexOfList β _))‖ ≤ _
      exact (PiLp.norm_apply_le (V i : WkpAmbientOn n k 2 Ω) _).trans
        ((Finset.single_le_sum (fun j _ ↦ norm_nonneg (V j)) (Finset.mem_univ i)).trans
          (le_add_of_nonneg_left lpNorm_nonneg))

/-- An L2 base with Hk first weak derivatives has an H(k+1) representative.
The graph norm is bounded by the L2 base norm and the first-derivative graph
norms, with the finite row-count factor. No preliminary Hk base is required. -/
theorem exists_succOrder_of_memLp_of_firstDerivatives
    (f : ℝ^n → ℝ) (hf : MemLp f 2 (domainMeasure n Ω))
    (V : Fin n → W^{k,2}(Ω))
    (hV : ∀ i, HasWeakDerivativeOn Ω [i] f (baseRepresentative (V i))) :
    ∃ W : W^{k + 1,2}(Ω),
      baseRepresentative W =ᵐ[domainMeasure n Ω] f ∧
      ‖W‖ ≤ succOrderAssemblyNormBound n k *
        (lpNorm f 2 (domainMeasure n Ω) + ∑ i, ‖V i‖) := by
  classical
  let d (a : DerivIndex n (k + 1)) := firstDerivativeWord f V a.toList a.toList_length_le
  have hbase : d (baseIndex n (k + 1)) = f := by
    suffices ∀ (α : List (Fin n)) (hα : α.length ≤ k + 1), α = [] →
        firstDerivativeWord f V α hα = f from this _ _ baseIndex_toList
    rintro α hα rfl
    rfl
  have hm (a : DerivIndex n (k + 1)) : MemLp (d a) 2 (domainMeasure n Ω) :=
    firstDerivativeWord_memLp f hf V a.toList a.toList_length_le
  have hw (a : DerivIndex n (k + 1)) : HasWeakDerivativeOn Ω a.toList f (d a) :=
    firstDerivativeWord_hasWeakDerivativeOn f hf V hV a.toList a.toList_length_le
  let W := mkWkpSpaceOnOfWeakDerivatives f d hbase hm hw
  have hcoord (a : DerivIndex n (k + 1)) :
      ((W : WkpAmbientOn n (k + 1) 2 Ω) a : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] d a :=
    mkWkpSpaceOnOfWeakDerivatives_apply_ae f d hbase hm hw a
  let B := lpNorm f 2 (domainMeasure n Ω) + ∑ i, ‖V i‖
  have hB : 0 ≤ B := add_nonneg lpNorm_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
  have hrow (a : DerivIndex n (k + 1)) :
      ‖((W : WkpAmbientOn n (k + 1) 2 Ω) a)‖ ≤ B := by
    rw [Lp.norm_def, eLpNorm_congr_ae (hcoord a)]
    exact firstDerivativeWord_lpNorm_le f V a.toList a.toList_length_le
  have hsum : ∑ a : DerivIndex n (k + 1), ‖((W : WkpAmbientOn n (k + 1) 2 Ω) a)‖ ^ 2 ≤
      (Fintype.card (DerivIndex n (k + 1)) : ℝ) * B ^ 2 := by
    calc
      _ ≤ ∑ _a : DerivIndex n (k + 1), B ^ 2 := Finset.sum_le_sum fun a _ ↦
        pow_le_pow_left₀ (norm_nonneg _) (hrow a) 2
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  refine ⟨W, ?_, ?_⟩
  · exact (hcoord (baseIndex n (k + 1))).trans (Filter.EventuallyEq.of_eq hbase)
  · change ‖(W : WkpAmbientOn n (k + 1) 2 Ω)‖ ≤ _
    rw [PiLp.norm_eq_of_L2, succOrderAssemblyNormBound]
    apply (Real.sqrt_le_sqrt hsum).trans_eq
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hB]

end SobolevSpace.GraphSpace
