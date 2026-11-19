/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.BochnerConsistency
import PDE.Analysis.MeasureTheory.Lp.MultiplierPairing
import PDE.Spaces.Sobolev.Calculus.Product.FirstOrder

/-!
# Mollified transport on L² and cancellation on H¹

Write `Jε` for convolution with a mollifier and `Dεⱼ` for convolution with its
coordinate derivative. For `a ∈ W¹,∞`, mollifying the distribution `-a ∂ⱼu` gives
`-Dεⱼ(a u) + Jε((∂ⱼa) u)`. The inner-product identity below identifies this expression
on arbitrary L² input by testing against the mollified H¹ function.

The difference from the principal term `-a Dεⱼu` is the operator
`Rεu = a Dεⱼu - Dεⱼ(a u) + Jε((∂ⱼa) u)`. For H¹ input, the weak product rule cancels
the differentiated-coefficient terms and gives
`Rεu = a Jε(∂ⱼu) - Jε(a ∂ⱼu)`, which converges to zero in L².

The boundedness of `Rε` here is at each fixed positive scale. Extending this convergence
to arbitrary L² inputs requires an estimate uniform as `ε → 0`; see
`TransportCommutatorBound`.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace Topology Sobolev

namespace SobolevSpace.Approximation

open GraphSpace

variable {n : ℕ}

local notation "L2" => DerivLp n 2 univ

/-- The derivative of the standard mollifier is skew-adjoint on L². Integration by
parts proves the identity first on H¹₀ tests, whose base coordinates are dense in L². -/
theorem inner_standardMollifierDerivativeRowCLM_left
    {ε : ℝ} (hε : 0 < ε) (j : Fin n) (u v : L2) :
    ⟪mollifierDerivativeRowCLM (standardMollifier n) hε j u, v⟫_ℝ =
      -⟪u, mollifierDerivativeRowCLM (standardMollifier n) hε j v⟫_ℝ := by
  let J := mollifierRowCLM (standardMollifier n) hε
  let D := mollifierDerivativeRowCLM (standardMollifier n) hε j
  let F : L2 →L[ℝ] ℝ := innerSL ℝ (D u)
  let G : L2 →L[ℝ] ℝ := -((innerSL ℝ u).comp D)
  have hweak : HasWeakDerivativeOn univ [j]
      ((J u : L2) : ℝ^n → ℝ) ((D u : L2) : ℝ^n → ℝ) := by
    have h := (mollifierH1CLM (standardMollifier n) hε u).property
      (singleDerivIndex n j)
    change HasWeakDerivativeOn univ (singleDerivIndex n j).toList
      (wkpCoordinateCLM (baseIndex n 1)
        (mollifierH1CLM (standardMollifier n) hε u))
      (wkpCoordinateCLM (singleDerivIndex n j)
        (mollifierH1CLM (standardMollifier n) hε u)) at h
    simpa only [singleDerivIndex_toList, mollifierH1CLM_base,
      mollifierH1CLM_derivative] using h
  have htest :
      (F : L2 → ℝ) ∘ baseCoordCLM (n := n) (Ω := univ) =
        (G : L2 → ℝ) ∘ baseCoordCLM (n := n) (Ω := univ) := by
    funext V
    have h := weakDerivative_integrationByParts_H10 j (J u) (D u) hweak V
    have hcomm : D (baseCoordCLM V) = J (derivCoordCLM j V) := by
      simpa only [D, J, baseCoordCLM_apply, derivCoordCLM_apply,
        wkpCoordinateCLM_apply] using
        mollifierDerivativeRowCLM_base (standardMollifier n) hε j V.1
    change ⟪D u, baseCoordCLM V⟫_ℝ = -⟪u, D (baseCoordCLM V)⟫_ℝ
    rw [hcomm, ← inner_standardMollifierRowCLM_left hε]
    linarith only [h]
  have hall := (baseCoordCLM_denseRange (n := n) isOpen_univ).equalizer
    F.continuous G.continuous htest
  exact congrFun hall v

/-- The mollified distribution `-a ∂ⱼu`, for L² input and a W¹,∞ coefficient, acts on an
L² test exactly as the original distribution acts on its mollified H¹ test. The sign
comes from differentiating the kernel, not from assuming a derivative of the input. -/
theorem inner_mollified_transport_row
    {ε : ℝ} (hε : 0 < ε) (A : W^{1,∞}(ℝ^n)) (j : Fin n)
    (u v : L2) :
    ⟪-mollifierDerivativeRowCLM (standardMollifier n) hε j
          (((A : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) • u) +
        mollifierRowCLM (standardMollifier n) hε
          (((A : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)) • u), v⟫_ℝ =
      ⟪u, ((A : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) •
          mollifierDerivativeRowCLM (standardMollifier n) hε j v +
        ((A : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)) •
          mollifierRowCLM (standardMollifier n) hε v⟫_ℝ := by
  rw [inner_add_left, inner_neg_left,
    inner_standardMollifierDerivativeRowCLM_left, neg_neg,
    inner_standardMollifierRowCLM_left, Lp.inner_lpSMul_left,
    Lp.inner_lpSMul_left, inner_add_right]

/-- The transport commutator `a Dεⱼu - Dεⱼ(a u) + Jε((∂ⱼa) u)`. Every term is a
bounded operator on L² at fixed positive scale; the coefficient derivative is the
Sobolev coordinate of `A`. -/
def mollifierTransportCommutatorCLM
    (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) (A : W^{1,∞}(ℝ^n))
    (j : Fin n) : L2 →L[ℝ] L2 :=
  (mulLpLeft ((A : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1))).comp
      (mollifierDerivativeRowCLM μ hε j) -
    (mollifierDerivativeRowCLM μ hε j).comp
      (mulLpLeft ((A : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1))) +
    (mollifierRowCLM μ hε).comp
      (mulLpLeft ((A : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)))

/-- Evaluation records the principal term and both terms from the distributional
product rule, including the positive differentiated-coefficient term. -/
theorem mollifierTransportCommutatorCLM_apply
    (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) (A : W^{1,∞}(ℝ^n))
    (j : Fin n) (u : L2) :
    mollifierTransportCommutatorCLM μ hε A j u =
      ((A : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) •
          mollifierDerivativeRowCLM μ hε j u -
        mollifierDerivativeRowCLM μ hε j
          (((A : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) • u) +
        mollifierRowCLM μ hε
          (((A : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)) • u) := rfl

/-- On H¹ input, the weak Leibniz rule cancels the differentiated-coefficient terms.
Only the failure of multiplication by `a` to commute with mollification remains. -/
theorem mollifierTransportCommutatorCLM_base
    (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) (A : W^{1,∞}(ℝ^n))
    (j : Fin n) (U : H¹(ℝ^n)) :
    mollifierTransportCommutatorCLM μ hε A j (wkpCoordinateCLM (baseIndex n 1) U) =
      ((A : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) •
          mollifierRowCLM μ hε (wkpCoordinateCLM (singleDerivIndex n j) U) -
        mollifierRowCLM μ hε
          (((A : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) •
            wkpCoordinateCLM (singleDerivIndex n j) U) := by
  have hprod := mollifierDerivativeRowCLM_base μ hε j
    (w1TopMultiplierCLM isOpen_univ A U)
  simp only [wkpCoordinateCLM_apply, w1TopMultiplierCLM_apply_coe,
    w1TopMultiplierAmbient_base, w1TopMultiplierAmbient_singleDeriv] at hprod
  change mollifierDerivativeRowCLM μ hε j
      (((A : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) •
        wkpCoordinateCLM (baseIndex n 1) U) =
    mollifierRowCLM μ hε
      (((A : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) •
          wkpCoordinateCLM (singleDerivIndex n j) U +
        ((A : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)) •
          wkpCoordinateCLM (baseIndex n 1) U) at hprod
  rw [mollifierTransportCommutatorCLM_apply, mollifierDerivativeRowCLM_base,
    hprod, map_add]
  abel

/-- Along any positive scales tending to zero, the transport commutator converges
strongly to zero on an H¹ input. No rate or uniform operator-norm bound is assumed. -/
theorem tendsto_mollifierTransportCommutatorCLM_base
    (μ : Mollifier n) (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k)
    (hε0 : Tendsto ε atTop (𝓝 0)) (A : W^{1,∞}(ℝ^n))
    (j : Fin n) (U : H¹(ℝ^n)) :
    Tendsto (fun k ↦ mollifierTransportCommutatorCLM μ (hε k) A j
      (wkpCoordinateCLM (baseIndex n 1) U)) atTop (𝓝 (0 : L2)) := by
  let a := (A : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)
  let v := wkpCoordinateCLM (singleDerivIndex n j) U
  have hleft := (mulLpLeft (p := (2 : ℝ≥0∞)) a).continuous.continuousAt.tendsto.comp
    (tendsto_mollifierRowCLM μ ε hε hε0 v)
  have hright := tendsto_mollifierRowCLM μ ε hε hε0 (a • v)
  simpa only [Function.comp_def, mulLpLeft_apply, sub_self,
    mollifierTransportCommutatorCLM_base] using hleft.sub hright

end SobolevSpace.Approximation
