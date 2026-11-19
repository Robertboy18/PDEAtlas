/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.SolutionOperator.FullLoad
public import PDE.Spaces.Sobolev.Calculus.Product.HigherOrderOperator

/-!
# The full divergence operator on higher Sobolev spaces

The flux formula defines the bounded spatial operator
`L : H^{r+2}(Ω) → H^r(Ω)` for every natural order `r`, including zero.
Multiplication is performed in order `r+1` before taking the divergence.
Thus one construction treats the principal, drift and potential terms and
does not require a boundary condition on its input.

These maps supply the spatial loads in the compatibility conditions for
higher parabolic and wave regularity. Their operator norms are fixed before
the initial or forcing data are chosen.
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace SobolevSpace.GraphSpace.BoundaryRegularity

open scoped ENNReal InnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The full spatial load `-∑ i,j Dᵢ(aᵢⱼ Dⱼ U) + ∑ i bᵢ Dᵢ U + c U`
as a bounded map from `H^{r+2}` to `H^r`. -/
def higherFullLoadCLM (r : ℕ) (hopen : IsOpen Ω)
    (A : Fin n → Fin n → W^{r + 1,∞}(Ω))
    (b : Fin n → W^{r + 1,∞}(Ω))
    (c : W^{r + 1,∞}(Ω)) :
    W^{r + 2,2}(Ω) →L[ℝ] W^{r,2}(Ω) :=
  -(∑ i, ∑ j,
    (derivativeWordCLM [i] (show [i].length + r ≤ r + 1 by simp; omega)).comp
      ((wkTopMultiplierCLM (Nat.succ_pos r) hopen (A i j)).comp
        (derivativeWordCLM [j] (show [j].length + (r + 1) ≤ r + 2 by simp; omega)))) +
    (lowerOrderCLM (show r ≤ r + 1 by omega)).comp
      ((∑ i, (wkTopMultiplierCLM (Nat.succ_pos r) hopen (b i)).comp
        (derivativeWordCLM [i] (show [i].length + (r + 1) ≤ r + 2 by simp; omega))) +
      (wkTopMultiplierCLM (Nat.succ_pos r) hopen c).comp
        (lowerOrderCLM (show r + 1 ≤ r + 2 by omega)))

/-- The spatial load is bounded by a constant depending only on its fixed
coefficients, domain and Sobolev order. -/
theorem norm_higherFullLoadCLM_apply_le (r : ℕ) (hopen : IsOpen Ω)
    (A : Fin n → Fin n → W^{r + 1,∞}(Ω))
    (b : Fin n → W^{r + 1,∞}(Ω))
    (c : W^{r + 1,∞}(Ω)) (U : W^{r + 2,2}(Ω)) :
    ‖higherFullLoadCLM r hopen A b c U‖ ≤ ‖higherFullLoadCLM r hopen A b c‖ * ‖U‖ :=
  (higherFullLoadCLM r hopen A b c).le_opNorm U

/-- The higher full spatial operators commute with Sobolev order restriction,
including restriction to order zero. -/
theorem lowerOrderCLM_higherFullLoadCLM {r s : ℕ} (hsr : s ≤ r)
    (hopen : IsOpen Ω)
    (A : Fin n → Fin n → W^{r + 1,∞}(Ω))
    (b : Fin n → W^{r + 1,∞}(Ω))
    (c : W^{r + 1,∞}(Ω)) (U : W^{r + 2,2}(Ω)) :
    lowerOrderCLM hsr (higherFullLoadCLM r hopen A b c U) =
      higherFullLoadCLM s hopen
        (fun i j ↦ lowerOrderCLM (Nat.add_le_add_right hsr 1) (A i j))
        (fun i ↦ lowerOrderCLM (Nat.add_le_add_right hsr 1) (b i))
        (lowerOrderCLM (Nat.add_le_add_right hsr 1) c)
        (lowerOrderCLM (Nat.add_le_add_right hsr 2) U) := by
  have hderiv (i : Fin n) :
      lowerOrderCLM (Nat.add_le_add_right hsr 1)
          (derivativeWordCLM [i] (show [i].length + (r + 1) ≤ r + 2 by simp; omega) U) =
        derivativeWordCLM [i] (show [i].length + (s + 1) ≤ s + 2 by simp; omega)
          (lowerOrderCLM (Nat.add_le_add_right hsr 2) U) := by
    rw [lowerOrderCLM_derivativeWordCLM_apply, derivativeWordCLM_lowerOrderCLM_apply]
  have hflux (i j : Fin n) :
      lowerOrderCLM hsr
          (derivativeWordCLM [i] (show [i].length + r ≤ r + 1 by simp; omega)
            (wkTopProduct (Nat.succ_pos r) hopen (A i j)
              (derivativeWordCLM [j]
                (show [j].length + (r + 1) ≤ r + 2 by simp; omega) U))) =
        derivativeWordCLM [i] (show [i].length + s ≤ s + 1 by simp; omega)
          (wkTopProduct (Nat.succ_pos s) hopen
            (lowerOrderCLM (Nat.add_le_add_right hsr 1) (A i j))
            (derivativeWordCLM [j]
              (show [j].length + (s + 1) ≤ s + 2 by simp; omega)
              (lowerOrderCLM (Nat.add_le_add_right hsr 2) U))) := by
    rw [lowerOrderCLM_derivativeWordCLM_apply]
    rw [← derivativeWordCLM_lowerOrderCLM_apply (Nat.add_le_add_right hsr 1)
      [i] (show [i].length + s ≤ s + 1 by simp; omega)]
    rw [lowerOrderCLM_wkTopProduct (Nat.succ_pos s), hderiv]
  have hproduct (B : W^{r + 1,∞}(Ω))
      (V : W^{r + 1,2}(Ω)) :
      lowerOrderCLM hsr (lowerOrderCLM (Nat.le_succ r)
          (wkTopProduct (Nat.succ_pos r) hopen B V)) =
        lowerOrderCLM (Nat.le_succ s) (wkTopProduct (Nat.succ_pos s) hopen
          (lowerOrderCLM (Nat.add_le_add_right hsr 1) B)
          (lowerOrderCLM (Nat.add_le_add_right hsr 1) V)) := by
    rw [← lowerOrderCLM_wkTopProduct (Nat.succ_pos s)
      (Nat.add_le_add_right hsr 1) (Nat.succ_pos r) hopen B V]
    rw [lowerOrderCLM_trans_apply, lowerOrderCLM_trans_apply]
  simp only [higherFullLoadCLM, add_apply, neg_apply, sum_apply,
    ContinuousLinearMap.comp_apply, wkTopMultiplierCLM_apply, map_add, map_neg, map_sum]
  simp only [hflux, hproduct, hderiv, lowerOrderCLM_trans_apply]

/-- At order zero, the flux construction agrees with the full `H²`
load, including the first-order coefficient derivatives in its principal part. -/
theorem wkpBaseCoordinate_higherFullLoadCLM_zero (hopen : IsOpen Ω)
    (A : Fin n → Fin n → W^{1,∞}(Ω))
    (b : Fin n → W^{1,∞}(Ω)) (c : W^{1,∞}(Ω))
    (U : W^{2,2}(Ω)) :
    wkpBaseCoordinateCLM (higherFullLoadCLM 0 hopen A b c U) =
      fullStrongLoad A (fun i ↦ wkpBaseCoordinateCLM (b i))
        (wkpBaseCoordinateCLM c) U := by
  have hflux (i j : Fin n) :
      wkpBaseCoordinateCLM
          (derivativeWordCLM [i] (show [i].length + 0 ≤ 1 by simp)
            (wkTopProduct (by omega) hopen (A i j)
              (derivativeWordCLM [j] (show [j].length + 1 ≤ 2 by simp) U))) =
        (A i j : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) •
            (U : WkpAmbientOn n 2 2 Ω) (pairDerivIndex n j i) +
          (A i j : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n i) •
            (U : WkpAmbientOn n 2 2 Ω) (firstDerivIndex n 2 (by omega) j) := by
    rw [wkpBaseCoordinateCLM_apply, derivativeWordCLM_apply,
      derivativeWordIndex_singleton_baseIndex, firstDerivIndex_one,
      wkTopProduct_one_eq_w1TopMultiplierCLM, w1TopMultiplierCLM_apply_coe,
      w1TopMultiplierAmbient_singleDeriv]
    simp only [derivativeWordCLM_apply, derivativeWordIndex_singleDerivIndex,
      List.singleton_append, derivIndexOfList_pair, secondDerivIndex_two,
      derivativeWordIndex_singleton_baseIndex]
  have hproduct (B : W^{1,∞}(Ω)) (V : W^{1,2}(Ω)) :
      wkpBaseCoordinateCLM (lowerOrderCLM (show 0 ≤ 1 by omega)
          (wkTopProduct (by omega) hopen B V)) =
        wkpBaseCoordinateCLM B • wkpBaseCoordinateCLM V := by
    change wkpBaseCoordinateCLM (wkTopProduct (by omega) hopen B V) = _
    rw [wkpBaseCoordinate_wkTopProduct, mulLpLeft_apply]
  simp only [higherFullLoadCLM, add_apply, neg_apply, sum_apply,
    ContinuousLinearMap.comp_apply, map_add, map_neg, map_sum,
    wkTopMultiplierCLM_apply, hflux, hproduct, fullStrongLoad, strongLoad,
    wkpBaseCoordinateCLM_apply, derivativeWordCLM_apply,
    derivativeWordIndex_singleton_baseIndex, lowerOrderCLM_apply,
    DerivIndex.castOrder_baseIndex, add_assoc]

/-- Every higher load has the same base coordinate as the full `H²` load
of its input. Thus the hierarchy represents a single spatial operator. -/
theorem wkpBaseCoordinate_higherFullLoadCLM (r : ℕ) (hopen : IsOpen Ω)
    (A : Fin n → Fin n → W^{r + 1,∞}(Ω))
    (b : Fin n → W^{r + 1,∞}(Ω))
    (c : W^{r + 1,∞}(Ω)) (U : W^{r + 2,2}(Ω)) :
    wkpBaseCoordinateCLM (higherFullLoadCLM r hopen A b c U) =
      fullStrongLoad
        (fun i j ↦ lowerOrderCLM (show 1 ≤ r + 1 by omega) (A i j))
        (fun i ↦ wkpBaseCoordinateCLM (b i)) (wkpBaseCoordinateCLM c)
        (lowerOrderCLM (show 2 ≤ r + 2 by omega) U) := by
  have h := congrArg (wkpBaseCoordinateCLM (n := n) (m := 0) (p := 2) (Ω := Ω))
    (lowerOrderCLM_higherFullLoadCLM (Nat.zero_le r) hopen A b c U)
  rw [wkpBaseCoordinate_higherFullLoadCLM_zero] at h
  simpa only [wkpBaseCoordinateCLM_apply, lowerOrderCLM_apply,
    DerivIndex.castOrder_baseIndex] using h

/-- The full variational form is represented by the base coordinate of
every higher spatial load on inputs with zero boundary trace. -/
theorem fullDivergenceForm_eq_higherFullLoad (r : ℕ) (hopen : IsOpen Ω)
    (A : Fin n → Fin n → W^{r + 1,∞}(Ω))
    (b : Fin n → W^{r + 1,∞}(Ω))
    (c : W^{r + 1,∞}(Ω)) (U : W^{r + 2,2}(Ω))
    (u : H¹₀(Ω)) (hbase : wkpBaseCoordinateCLM U = baseCoordCLM u)
    (v : H¹₀(Ω)) :
    fullDivergenceForm
        (multiplicationCoefficientOperator (fun i j ↦ wkpBaseCoordinateCLM (A i j)))
        (multiplicationFirstOrderOperator (fun i ↦ wkpBaseCoordinateCLM (b i)))
        (multiplicationZeroOrderOperator (wkpBaseCoordinateCLM c)) u v =
      ⟪wkpBaseCoordinateCLM (higherFullLoadCLM r hopen A b c U), baseCoordCLM v⟫_ℝ := by
  have hbase₂ : wkpBaseCoordinateCLM
      (lowerOrderCLM (show 2 ≤ r + 2 by omega) U) = baseCoordCLM u := by
    simpa only [wkpBaseCoordinateCLM_apply, lowerOrderCLM_apply,
      DerivIndex.castOrder_baseIndex] using hbase
  have h := fullDivergenceForm_eq_fullStrongLoad hopen
    (fun i j ↦ lowerOrderCLM (show 1 ≤ r + 1 by omega) (A i j))
    (fun i ↦ wkpBaseCoordinateCLM (b i)) (wkpBaseCoordinateCLM c)
    (lowerOrderCLM (show 2 ≤ r + 2 by omega) U) u hbase₂ v
  rw [← wkpBaseCoordinate_higherFullLoadCLM r hopen A b c U] at h
  have hcoeff : coefficientBase
      (fun i j ↦ lowerOrderCLM (show 1 ≤ r + 1 by omega) (A i j)) =
        fun i j ↦ wkpBaseCoordinateCLM (A i j) := by
    funext i j
    simp only [coefficientBase, wkpBaseCoordinateCLM_apply, lowerOrderCLM_apply,
      DerivIndex.castOrder_baseIndex]
  rwa [hcoeff] at h

/-- A zero-boundary higher Sobolev field solves the full shift-zero weak
elliptic equation for its constructed spatial load. -/
theorem higherFullLoad_isWeakShiftedFullDivergenceSolution (r : ℕ) (hopen : IsOpen Ω)
    (A : Fin n → Fin n → W^{r + 1,∞}(Ω))
    (b : Fin n → W^{r + 1,∞}(Ω))
    (c : W^{r + 1,∞}(Ω)) (U : W^{r + 2,2}(Ω))
    (u : H¹₀(Ω)) (hbase : wkpBaseCoordinateCLM U = baseCoordCLM u) :
    IsWeakShiftedFullDivergenceSolution
      (fun i j ↦ wkpBaseCoordinateCLM (A i j))
      (fun i ↦ wkpBaseCoordinateCLM (b i)) (wkpBaseCoordinateCLM c) 0
      (wkpBaseCoordinateCLM (higherFullLoadCLM r hopen A b c U)) 0 u := by
  apply (isWeakSolution_iff_isWeakShiftedFullDivergenceSolution hopen _ _ _ _ _ _ _).1
  intro v
  simpa only [shiftedDivergenceForm_apply, zero_mul, add_zero,
    generalizedLoad_apply, Pi.zero_apply, inner_zero_left, Finset.sum_const_zero] using
    fullDivergenceForm_eq_higherFullLoad r hopen A b c U u hbase v

end SobolevSpace.GraphSpace.BoundaryRegularity
