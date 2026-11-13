/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Quasilinear.Interior.HigherOrder.Bootstrap.WeakFlux
public import PDE.Elliptic.Regularity.Interior.H2Compactness
import PDE.Spaces.Sobolev.Calculus.Product.FirstOrder

/-!
# Sobolev realizations of the local differentiated equation

An H¹ divergence forcing has an L² divergence. Integration by parts therefore
puts the equation in the form required by the interior H² theorem.
This constructs the H¹ derivatives needed for the next Schauder application.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev ENNReal InnerProductSpace

namespace PDE.Elliptic.Regularity.Quasilinear.Bootstrap

variable {n : ℕ} {Ω V : Set ℝ^n}

/-- A local classical flux identity gives the usual weak bilinear equation
whenever its coefficients, state and forcing have Sobolev realizations. -/
theorem interiorVariableCoeffForm_eq_of_local_flux
    (A : Fin n → Fin n → DerivLp n ∞ Ω) (u : H¹(Ω))
    (F : Fin n → DerivLp n 2 Ω)
    (a : Fin n → Fin n → ℝ^n → ℝ) (f : Fin n → ℝ^n → ℝ) (v : ℝ^n → ℝ)
    (hA : ∀ i j, (A i j : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] a i j)
    (hF : ∀ i, (F i : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] f i)
    (hdu : ∀ j, (wkpCoordinateCLM (singleDerivIndex n j) u : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] ∂[j] v)
    (hu : HasZeroWeakDivergenceOn Ω
      (fun i x ↦ (∑ j, a i j x * (∂[j] v) x) - f i x))
    (w : H¹₀(Ω)) :
    interiorVariableCoeffForm (multiplicationCoefficientOperator A) u w =
      ∑ i, ⟪F i, derivCoordCLM i w⟫_ℝ := by
  let Q (i : Fin n) : DerivLp n 2 Ω :=
    (∑ j, A i j • wkpCoordinateCLM (singleDerivIndex n j) u) - F i
  have hQ (i : Fin n) : (Q i : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      fun x ↦ (∑ j, a i j x * (∂[j] v) x) - f i x := by
    filter_upwards [Lp.coeFn_sub
      (∑ j, A i j • wkpCoordinateCLM (singleDerivIndex n j) u) (F i),
      Lp.coeFn_fun_finsetSum Finset.univ
        (fun j ↦ A i j • wkpCoordinateCLM (singleDerivIndex n j) u),
      ae_all_iff.mpr (fun j ↦ Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞))
        (A i j) (wkpCoordinateCLM (singleDerivIndex n j) u)),
      ae_all_iff.mpr (hA i), ae_all_iff.mpr hdu, hF i] with x hs hsum hm ha hd hf
    change (_ - _ : DerivLp n 2 Ω) x = _
    rw [hs, Pi.sub_apply, hsum, hf]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [hm j, Pi.smul_apply', ha j, hd j, smul_eq_mul]
  have hz := hu.pairing Q hQ w
  rw [interiorVariableCoeffForm_apply]
  simp only [multiplicationCoefficientOperator_apply]
  simpa only [Q, inner_sub_left, sum_inner, Finset.sum_sub_distrib,
    sub_eq_zero] using hz

/-- H¹ divergence forcing gives an H² representative on any relatively
compact interior open set. No boundary condition is imposed on the state. -/
theorem exists_interior_h2_of_divergence_forcing
    (hΩ : IsOpen Ω)
    (A : Fin n → Fin n → DerivLp n ∞ Ω)
    (a : Fin n → Fin n → ℝ^n → ℝ)
    (ha : ∀ i j, LocallyLipschitzOn Ω (a i j))
    (hrep : ∀ i j, (A i j : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] a i j)
    {θ : ℝ} (hA : AEUniformlyElliptic A θ) (u : H¹(Ω))
    (F : Fin n → H¹(Ω))
    (hu : ∀ w : H¹₀(Ω),
      interiorVariableCoeffForm (multiplicationCoefficientOperator A) u w =
        ∑ i, ⟪wkpBaseCoordinateCLM (F i), derivCoordCLM i w⟫_ℝ)
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVΩ : closure V ⊆ Ω) :
    ∃ W : W^{2,2}(V),
      wkpBaseCoordinateCLM W =
        restrictDerivLp (subset_closure.trans hVΩ) (wkpBaseCoordinateCLM u) := by
  let g : DerivLp n 2 Ω := -∑ i, wkpCoordinateCLM (singleDerivIndex n i) (F i)
  have heq : IsInteriorWeakDivergenceSolution A g u := by
    refine ⟨hΩ, fun w ↦ ?_⟩
    rw [hu]
    have hp (i : Fin n) :
        ⟪wkpBaseCoordinateCLM (F i), derivCoordCLM i w⟫_ℝ =
          -⟪wkpCoordinateCLM (singleDerivIndex n i) (F i), baseCoordCLM w⟫_ℝ := by
      apply weakDerivative_integrationByParts_H10
      simpa only [firstDerivIndex_one, wkpBaseCoordinateCLM_apply, wkpCoordinateCLM_apply]
        using (F i).property.hasWeakDerivativeOn_first (by norm_num) i
    simp only [hp, g, loadFunctional_apply, inner_neg_left, sum_inner,
      Finset.sum_neg_distrib]
  obtain ⟨N, hN, hVN, _, W, hW⟩ := exists_local_h2_of_locallyLipschitzOn
    hΩ A a ha hrep hA g u heq (closure V) hVc hVΩ
  let hsub : V ⊆ N := subset_closure.trans hVN
  refine ⟨restrictCLM hV.measurableSet hsub W, Lp.ext ?_⟩
  filter_upwards [restrictCLM_apply_ae hV.measurableSet hsub W (baseIndex n 2),
    ae_mono (domainMeasure_le hsub) hW,
    restrictDerivLp_apply_ae (subset_closure.trans hVΩ) (wkpBaseCoordinateCLM u)]
    with x hx hy hz
  exact hx.trans (hy.trans hz.symm)

end PDE.Elliptic.Regularity.Quasilinear.Bootstrap
