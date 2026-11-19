/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.Vector.FirstOrder
public import PDE.Spaces.Sobolev.Calculus.Product.Operator
public import PDE.Spaces.Sobolev.GraphSpace.Operators.PartialDerivatives

/-!
# Matrix transport on Sobolev graphs

Bounded matrix coefficients act on first weak derivatives from H¹ to L².
For W¹,∞ coefficients the same expression maps H² to H¹ by the weak
Leibniz rule. The base coordinates of the two operators agree. Operator-norm
continuity follows from Mathlib's bounded bilinear Lp multiplication and
the Sobolev multiplier.

The sign convention is the evolution drift `-∑ⱼ Aʲ ∂ⱼ`.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal Sobolev

variable {n m : ℕ} {Ω : Set ℝ^n}

/-- Matrix transport from the finite family of H¹ graphs to L². -/
def vectorTransportCLM (A : Fin n → Fin m → Fin m → DerivLp n ∞ Ω) :
    (Fin m → W^{1,2}(Ω)) →L[ℝ] (Fin m → DerivLp n 2 Ω) :=
  ContinuousLinearMap.pi fun p ↦ -(∑ j, ∑ q,
    (mulLpLeft (A j p q)).comp
      ((wkpCoordinateCLM (singleDerivIndex n j)).comp (ContinuousLinearMap.proj q)))

/-- The drift is the full matrix contraction with all weak first derivatives. -/
theorem vectorTransportCLM_apply
    (A : Fin n → Fin m → Fin m → DerivLp n ∞ Ω)
    (U : Fin m → W^{1,2}(Ω)) (p : Fin m) :
    vectorTransportCLM A U p =
      -(∑ j, ∑ q, A j p q • wkpCoordinateCLM (singleDerivIndex n j) (U q)) := by
  simp [vectorTransportCLM, sum_apply]

/-- The representative is the literal full matrix contraction with the
first weak-derivative coordinates, on one common full-measure set. -/
theorem vectorTransportCLM_apply_ae
    (A : Fin n → Fin m → Fin m → DerivLp n ∞ Ω)
    (U : Fin m → W^{1,2}(Ω)) :
    ∀ᵐ x ∂domainMeasure n Ω, ∀ p,
      vectorTransportCLM A U p x =
        -(∑ j, ∑ q, A j p q x * wkpCoordinateCLM (singleDerivIndex n j) (U q) x) := by
  apply ae_all_iff.mpr
  intro p
  let v (j : Fin n) (q : Fin m) :=
    A j p q • wkpCoordinateCLM (singleDerivIndex n j) (U q)
  have hmul (j : Fin n) (q : Fin m) :
      (v j q : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] fun x ↦
        A j p q x * wkpCoordinateCLM (singleDerivIndex n j) (U q) x :=
    mulLpLeft_apply_ae _ _
  rw [vectorTransportCLM_apply]
  filter_upwards [Lp.coeFn_neg (∑ j, ∑ q, v j q),
    Lp.coeFn_fun_finsetSum Finset.univ (fun j ↦ ∑ q, v j q),
    ae_all_iff.mpr (fun j ↦ Lp.coeFn_fun_finsetSum Finset.univ (v j)),
    ae_all_iff.mpr (fun j ↦ ae_all_iff.mpr (hmul j))] with x hn hj hq hm
  change (-(∑ j, ∑ q, v j q)) x = _
  simp only [hn, Pi.neg_apply, hj, hq, hm]

/-- Bounded coefficients determine the transport operator continuously in
operator norm. No coefficient derivatives are used here. -/
theorem continuous_vectorTransportCLM :
    Continuous (vectorTransportCLM (n := n) (m := m) (Ω := Ω)) := by
  have hmul : Continuous (fun A : DerivLp n ∞ Ω ↦
      (mulLpLeft A : DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)) := by
    have heq (A : DerivLp n ∞ Ω) :
        (mulLpLeft A : DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω) =
          (ContinuousLinearMap.mul ℝ ℝ).holderL (domainMeasure n Ω) ∞ 2 2 A := by
      ext1 u
      apply Lp.ext
      filter_upwards [mulLpLeft_apply_ae A u,
        (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 2) A u] with x hx hy
      exact hx.trans hy.symm
    simp_rw [heq]
    exact ((ContinuousLinearMap.mul ℝ ℝ).holderL (domainMeasure n Ω) ∞ 2 2).continuous
  unfold vectorTransportCLM
  apply (ContinuousLinearMap.piEquivL ℝ
    (Fin m → W^{1,2}(Ω)) (fun _ : Fin m ↦ DerivLp n 2 Ω)).continuous.comp
  apply continuous_pi
  intro p
  apply Continuous.neg
  apply continuous_finsetSum
  intro j _
  apply continuous_finsetSum
  intro q _
  exact (hmul.comp ((continuous_apply q).comp
    ((continuous_apply p).comp (continuous_apply j)))).clm_comp continuous_const

/-- Matrix transport retaining one derivative, using the weak product
rule on H² states. -/
def vectorTransportH1CLM (hΩ : IsOpen Ω)
    (A : Fin n → Fin m → Fin m → W^{1,∞}(Ω)) :
    (Fin m → W^{2,2}(Ω)) →L[ℝ] (Fin m → W^{1,2}(Ω)) :=
  ContinuousLinearMap.pi fun p ↦ -(∑ j, ∑ q,
    (w1TopMultiplierCLM hΩ (A j p q)).comp
      ((partialDerivCLM j).comp (ContinuousLinearMap.proj q)))

/-- Each row of the H¹-valued operator is the Sobolev product with the first
derivative graph, so all first derivatives of that row are retained. -/
theorem vectorTransportH1CLM_apply (hΩ : IsOpen Ω)
    (A : Fin n → Fin m → Fin m → W^{1,∞}(Ω))
    (U : Fin m → W^{2,2}(Ω)) (p : Fin m) :
    vectorTransportH1CLM hΩ A U p =
      -(∑ j, ∑ q, w1TopMultiplierCLM hΩ (A j p q)
        (∂[j] (U q))) := by
  simp [vectorTransportH1CLM, sum_apply]

/-- Essentially bounded coefficient paths carry an L²(H²) family to its
L²(H¹) matrix transport term. The parameter measure is arbitrary. -/
theorem memLp_vectorTransportH1CLM {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (hΩ : IsOpen Ω) (A : α → Fin n → Fin m → Fin m → W^{1,∞}(Ω))
    (hA : ∀ j p q, MemLp (fun t ↦ A t j p q) ∞ μ)
    (u : Fin m → Lp (W^{2,2}(Ω)) 2 μ) (i : Fin m) :
    MemLp (fun t ↦ vectorTransportH1CLM hΩ (A t) (fun j ↦ u j t) i) 2 μ := by
  have hterm (j : Fin n) (p q : Fin m) : MemLp (fun t ↦
      w1TopMultiplierCLM hΩ (A t j p q)
        (∂[j] (u q t))) 2 μ := by
    let D : W^{2,2}(Ω) →L[ℝ] W^{1,2}(Ω) :=
      partialDerivCLM j
    have hd : MemLp (fun t ↦ D (u q t)) 2 μ := D.comp_memLp (u q)
    exact (w1TopMultiplicationCLM hΩ).memLp_of_bilin
      (p := ∞) (q := 2) 2 (hA j p q) hd
  simp only [vectorTransportH1CLM_apply]
  apply MemLp.neg
  exact memLp_finsetSum _ fun j _ ↦ memLp_finsetSum _ fun q _ ↦ hterm j i q

/-- W¹,∞ coefficient convergence gives operator-norm convergence from H² to H¹. -/
theorem continuous_vectorTransportH1CLM (hΩ : IsOpen Ω) :
    Continuous (vectorTransportH1CLM (n := n) (m := m) hΩ) := by
  have hmul : Continuous (fun A : W^{1,∞}(Ω) ↦ w1TopMultiplierCLM hΩ A) :=
    (w1TopMultiplicationCLM hΩ).continuous
  unfold vectorTransportH1CLM
  apply (ContinuousLinearMap.piEquivL ℝ
    (Fin m → W^{2,2}(Ω)) (fun _ : Fin m ↦ W^{1,2}(Ω))).continuous.comp
  apply continuous_pi
  intro p
  apply Continuous.neg
  apply continuous_finsetSum
  intro j _
  apply continuous_finsetSum
  intro q _
  exact (hmul.comp ((continuous_apply q).comp
    ((continuous_apply p).comp (continuous_apply j)))).clm_comp continuous_const

/-- Forgetting the derivative of the transport output recovers precisely
the H¹-to-L² matrix transport of the same state. -/
theorem vectorTransportH1CLM_base (hΩ : IsOpen Ω)
    (A : Fin n → Fin m → Fin m → W^{1,∞}(Ω))
    (U : Fin m → W^{2,2}(Ω)) (p : Fin m) :
    wkpBaseCoordinateCLM (vectorTransportH1CLM hΩ A U p) =
      vectorTransportCLM (fun j p q ↦ wkpBaseCoordinateCLM (A j p q))
        (fun q ↦ lowerOrderCLM (by decide : 1 ≤ 2) (U q)) p := by
  rw [vectorTransportH1CLM_apply, vectorTransportCLM_apply, map_neg, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro q _
  simp only [partialDerivCLM,
    wkpBaseCoordinateCLM_apply, w1TopMultiplierCLM_apply_coe,
    w1TopMultiplierAmbient_base, wkpCoordinateCLM_apply, derivativeWordCLM_apply,
    derivativeWordIndex_baseIndex, derivIndexOfList_singleton, lowerOrderCLM_apply,
    DerivIndex.castOrder_singleDerivIndex]

/-- Differentiating matrix transport produces the transport of the derivative
and the coefficient commutator. Mixed weak derivatives commute in the
H² graph. -/
theorem vectorTransportH1CLM_derivative (hΩ : IsOpen Ω)
    (A : Fin n → Fin m → Fin m → W^{1,∞}(Ω))
    (U : Fin m → W^{2,2}(Ω)) (p : Fin m) (l : Fin n) :
    wkpCoordinateCLM (singleDerivIndex n l) (vectorTransportH1CLM hΩ A U p) =
      vectorTransportCLM (fun j p q ↦ wkpBaseCoordinateCLM (A j p q))
        (fun q ↦ ∂[l] (U q)) p -
      ∑ j, ∑ q, wkpCoordinateCLM (singleDerivIndex n l) (A j p q) •
        wkpBaseCoordinateCLM
          (∂[j] (U q)) := by
  have hcomm (j : Fin n) (q : Fin m) :
      wkpCoordinateCLM (singleDerivIndex n l)
        (∂[j] (U q)) =
      wkpCoordinateCLM (singleDerivIndex n j)
        (∂[l] (U q)) := by
    simp only [partialDerivCLM,
      wkpCoordinateCLM_apply, derivativeWordCLM_apply,
      derivativeWordIndex_singleDerivIndex_comm j l (by decide : 2 ≤ 2)]
  rw [vectorTransportH1CLM_apply, vectorTransportCLM_apply, map_neg, map_sum]
  simp only [map_sum, wkpCoordinateCLM_apply, w1TopMultiplierCLM_apply_coe,
    w1TopMultiplierAmbient_singleDeriv, Finset.sum_add_distrib, neg_add, ← sub_eq_add_neg]
  change -(∑ j, ∑ q, wkpBaseCoordinateCLM (A j p q) •
    wkpCoordinateCLM (singleDerivIndex n l)
      (∂[j] (U q))) -
    (∑ j, ∑ q, wkpCoordinateCLM (singleDerivIndex n l) (A j p q) •
      wkpBaseCoordinateCLM (∂[j] (U q))) = _
  simp only [hcomm, wkpCoordinateCLM_apply, wkpBaseCoordinateCLM_apply]

end SobolevSpace.GraphSpace
