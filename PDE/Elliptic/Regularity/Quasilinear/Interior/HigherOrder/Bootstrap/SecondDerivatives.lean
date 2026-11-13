/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Quasilinear.Interior.HigherOrder.Bootstrap.HolderDerivatives
public import PDE.Elliptic.Regularity.Interior.Schauder.HigherOrder.Commutator
import PDE.Spaces.Sobolev.Calculus.Differentiation.Representative
import PDE.FDeriv.Calculus

/-!
# A second classical derivative from the differentiated weak equation

The H² representative supplies H¹ first derivatives. Differentiating its
weak equation gives the coefficient commutator, with no assumed
equation for those derivatives. When that explicit forcing is Hölder,
Schauder makes each first derivative C¹, hence the original representative C².
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev ENNReal NNReal InnerProductSpace

namespace PDE.Elliptic.Regularity.Quasilinear.Bootstrap

variable {n : ℕ} [Fact (0 < n)] {Ω : Set ℝ^n}

/-- The explicit coefficient commutator suffices for the C¹ to C² step.
The differentiated equation follows from the given weak equation by the weak
product rule. All Hölder hypotheses concern functions, not certificates
asserting the conclusion. -/
theorem contDiffOn_two_of_holder_commutator
    {q : ℝ≥0∞} (hq2 : 2 < q)
    (hq : q ≤ (if 2 < n then Inequalities.pStar n 2 else 4 : ℝ≥0))
    (hΩ : IsOpen Ω) (A : Fin n → Fin n → W^{1,∞}(Ω))
    (a : Fin n → Fin n → ℝ^n → ℝ)
    (ha : ∀ i j, ContDiffOn ℝ 1 (a i j) Ω)
    (hArep : ∀ i j, (wkpBaseCoordinateCLM (A i j) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] a i j)
    {θ Λ : ℝ} (hθ : 0 < θ) (hΛ : 0 ≤ Λ)
    (hbound : ∀ x ∈ Ω, ∀ i j, ‖a i j x‖ ≤ Λ)
    (hell : ∀ x ∈ Ω, ∀ ξ : Fin n → ℝ,
      θ * ∑ i, ξ i * ξ i ≤ ∑ i, ∑ j, a i j x * ξ j * ξ i)
    (W : W^{2,2}(Ω)) (F : Fin n → H¹(Ω)) (f : Fin n → ℝ^n → ℝ)
    (hf : ∀ i, ContDiffOn ℝ 1 (f i) Ω)
    (hFrep : ∀ i, (wkpBaseCoordinateCLM (F i) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] f i)
    (hu : ∀ w : H¹₀(Ω),
      interiorVariableCoeffForm
        (multiplicationCoefficientOperator (fun i j ↦ wkpBaseCoordinateCLM (A i j)))
        (lowerOrderCLM (by omega : 1 ≤ 2) W) w =
          ∑ i, ⟪wkpBaseCoordinateCLM (F i), derivCoordCLM i w⟫_ℝ)
    {v : ℝ^n → ℝ} (hv : ContDiffOn ℝ 1 v Ω)
    (hvW : v =ᵐ[domainMeasure n Ω] wkpBaseCoordinateCLM W)
    {K M γ : ℝ≥0} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hah : ∀ i j, HolderOnWith K γ (a i j) Ω)
    (hcomm : ∀ k i, HolderOnWith M γ
      (fun x ↦ (∂[k] (f i)) x - ∑ j, (∂[k] (a i j)) x * (∂[j] v) x) Ω) :
    ContDiffOn ℝ 2 v Ω := by
  let U : H¹(Ω) := lowerOrderCLM (by omega : 1 ≤ 2) W
  have hbase : (wkpBaseCoordinateCLM U : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] v := hvW.symm
  have hdu (j : Fin n) := wkpCoordinate_ae_eq_partialDeriv_of_contDiffOn hΩ U hv hbase j
  have hda (i j k : Fin n) :=
    wkpCoordinate_ae_eq_partialDeriv_of_contDiffOn hΩ (A i j) (ha i j) (hArep i j) k
  have hdf (i k : Fin n) :=
    wkpCoordinate_ae_eq_partialDeriv_of_contDiffOn hΩ (F i) (hf i) (hFrep i) k
  have hpartial (k : Fin n) : ContDiffOn ℝ 1 (∂[k] v) Ω := by
    let C (i : Fin n) : DerivLp n 2 Ω :=
      wkpCoordinateCLM (singleDerivIndex n k) (F i) -
        ∑ j, wkpCoordinateCLM (singleDerivIndex n k) (A i j) •
          wkpCoordinateCLM (singleDerivIndex n j) U
    have hC (i : Fin n) : (C i : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        fun x ↦ (∂[k] (f i)) x - ∑ j, (∂[k] (a i j)) x * (∂[j] v) x := by
      have hmul := ae_all_iff.mpr fun j ↦
        Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞))
          (wkpCoordinateCLM (singleDerivIndex n k) (A i j))
          (wkpCoordinateCLM (singleDerivIndex n j) U)
      filter_upwards [Lp.coeFn_sub
        (wkpCoordinateCLM (singleDerivIndex n k) (F i))
        (∑ j, wkpCoordinateCLM (singleDerivIndex n k) (A i j) •
          wkpCoordinateCLM (singleDerivIndex n j) U),
        Lp.coeFn_fun_finsetSum Finset.univ (fun j ↦
          wkpCoordinateCLM (singleDerivIndex n k) (A i j) •
            wkpCoordinateCLM (singleDerivIndex n j) U),
        hmul, hdf i k, ae_all_iff.mpr (fun j ↦ hda i j k),
        ae_all_iff.mpr hdu] with x hs hsum hm hfx hax hvx
      change (_ - _ : DerivLp n 2 Ω) x = _
      rw [hs, Pi.sub_apply, hsum, hfx]
      congr 1
      exact Finset.sum_congr rfl fun j _ ↦ by rw [hm j, Pi.smul_apply', hax j, hvx j, smul_eq_mul]
    have hWk : (wkpBaseCoordinateCLM (∂[k] W) : ℝ^n → ℝ)
        =ᵐ[domainMeasure n Ω] ∂[k] v := by
      have heq : wkpBaseCoordinateCLM (∂[k] W) =
          wkpCoordinateCLM (singleDerivIndex n k) U := by
        simp only [U, wkpBaseCoordinateCLM_apply, partialDerivCLM,
          derivativeWordCLM_apply, derivativeWordIndex_baseIndex, wkpCoordinateCLM_apply,
          lowerOrderCLM_apply, DerivIndex.castOrder_singleDerivIndex]
        rfl
      rw [heq]
      exact hdu k
    exact contDiffOn_one_of_holder_coefficients_continuousOn hq2 hq hθ hΛ hΩ
      (fun i j ↦ wkpBaseCoordinateCLM (A i j)) a hγ0 hγ1 hah hArep hbound hell
      (∂[k] W) C _ (hcomm k) hC
      (interiorVariableCoeffForm_partialDeriv_eq_commutator hΩ A W F hu k)
      (fun x hx ↦ (contDiffAt_partialDeriv 0
        (hv.contDiffAt (hΩ.mem_nhds hx)) k).continuousAt.continuousWithinAt) hWk.symm
  apply (contDiffOn_succ_iff_fderiv_of_isOpen (n := (1 : WithTop ℕ∞)) hΩ).mpr
  refine ⟨hv.differentiableOn (by norm_num), by simp, ?_⟩
  have heq : fderiv ℝ v =
      fun x ↦ ∑ k, (∂[k] v) x • (EuclideanSpace.proj k : ℝ^n →L[ℝ] ℝ) :=
    funext fun x ↦ fderiv_eq_sum_partialDeriv_smul_proj _ x
  rw [heq]
  exact ContDiffOn.sum fun k _ ↦ (hpartial k).smul contDiffOn_const

end PDE.Elliptic.Regularity.Quasilinear.Bootstrap
