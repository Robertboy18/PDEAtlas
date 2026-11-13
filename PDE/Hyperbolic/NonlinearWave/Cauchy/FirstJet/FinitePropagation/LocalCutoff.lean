/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.FinitePropagation.LocalReaction
public import PDE.Spaces.Sobolev.Localization.Cutoff.ZeroBoundary
import PDE.Spaces.Sobolev.Calculus.Product.LocalizedMixed
import PDE.Spaces.Sobolev.Calculus.Product.FirstOrder
import PDE.DistributionTheory.TestFunction.Derivative.Commutation

/-!
# Compactly localizing an energy weak wave

Cutoff multiplication followed by zero extension maps local energy data to
whole-space energy data. The weak Laplacian acquires an L² commutator,
expressed through first derivatives of localized fields. This form does not
require second derivatives of the unknown.
-/

@[expose] public noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal InnerProductSpace Sobolev SobolevSpace.WholeSpaceHilbert

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet

open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.GraphSpace.ZeroTrace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- Cutoff displacement extended by zero to the whole space. -/
def localCutoffDisplacementCLM (hΩ : IsOpen Ω)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hη : tsupport η.toFun ⊆ Ω) :
    H¹(Ω) →L[ℝ] H¹(ℝ^n) :=
  (zeroExtendH10 hΩ.measurableSet).comp (cutoffH1ToH10 hΩ η hη)

/-- Cutoff velocity extended by zero to the whole space. -/
def localCutoffVelocityCLM (hΩ : MeasurableSet Ω)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) : DerivLp n 2 Ω →L[ℝ] DerivLp n 2 univ :=
  (Extension.Lp.zeroExtendLp hΩ).comp (mulLpLeft (testFunctionLpTop (Ω := Ω) η))

/-- Whole-space spatial tests are restricted and localized inside the domain. -/
def localCutoffTestCLM (hΩ : IsOpen Ω)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hη : tsupport η.toFun ⊆ Ω) :
    H¹(ℝ^n) →L[ℝ] H¹₀(Ω) :=
  (cutoffH1ToH10 hΩ η hη).comp (restrictCLM hΩ.measurableSet (subset_univ Ω))

private theorem cutoff_base (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (U : H¹(Ω)) :
    (cutoffCLM η U).val (baseIndex n 1) = testFunctionLpTop (Ω := Ω) η • U.val (baseIndex n 1) := by
  change cutoffLpAt (p := 2) (Ω := Ω) η (baseIndex n 1) U.val = _
  simp only [cutoffLpAt, firstOrderRows_baseIndex, ContinuousLinearMap.comp_apply,
    PiLp.proj_apply, mulLpLeft_apply]

/-- The displacement and velocity cutoffs have the same base operator. -/
theorem localCutoffDisplacementCLM_base (hΩ : IsOpen Ω) (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hη : tsupport η.toFun ⊆ Ω) (U : H¹(Ω)) :
    wkpBaseCoordinateCLM (localCutoffDisplacementCLM hΩ η hη U) =
      localCutoffVelocityCLM hΩ.measurableSet η (wkpBaseCoordinateCLM U) := by
  change Extension.Lp.zeroExtendLp hΩ.measurableSet ((cutoffCLM η U).val (baseIndex n 1)) = _
  rw [cutoff_base]
  rfl

/-- The cutoff and restriction operations are adjoint in the L² base pairing. -/
theorem inner_localCutoffVelocityCLM (hΩ : IsOpen Ω) (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hη : tsupport η.toFun ⊆ Ω) (p : DerivLp n 2 Ω) (φ : H¹(ℝ^n)) :
    ⟪localCutoffVelocityCLM hΩ.measurableSet η p, wkpBaseCoordinateCLM φ⟫_ℝ = ⟪p,
      wkpBaseCoordinateCLM (localCutoffTestCLM hΩ η hη φ : H¹(Ω))⟫_ℝ := by
  simp only [localCutoffVelocityCLM, ContinuousLinearMap.comp_apply, mulLpLeft_apply]
  rw [Extension.Lp.inner_zeroExtendLp_eq_inner_restrict, Lp.inner_lpSMul_left]
  change _ = ⟪p, (cutoffCLM η
    (restrictCLM hΩ.measurableSet (subset_univ Ω) φ)).val (baseIndex n 1)⟫_ℝ
  rw [cutoff_base]
  rfl

/-- A spatial derivative of a test cutoff has no larger closed support. -/
theorem tsupport_cutoff_deriv_subset (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (i : Fin n) :
    tsupport (_root_.TestFunction.lineDerivCLM (k := ⊤) ℝ (EuclideanSpace.single i 1) η).toFun ⊆
      tsupport η.toFun := by
  change closure (Function.support _) ⊆ closure (Function.support _)
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hnot
  have hz : fderiv ℝ η x = 0 := fderiv_of_notMem_tsupport ℝ hnot
  apply hx
  change (_root_.TestFunction.lineDerivCLM (k := ⊤) ℝ (EuclideanSpace.single i 1) η) x = 0
  rw [_root_.TestFunction.lineDerivCLM_apply_eq_fderiv, hz, zero_apply]

/-- The first derivative of a localized displacement has the usual two terms. -/
theorem localCutoffDisplacementCLM_singleDeriv (hΩ : IsOpen Ω) (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hη : tsupport η.toFun ⊆ Ω) (U : H¹(Ω)) (i : Fin n) :
    wkpCoordinateCLM (singleDerivIndex n i) (localCutoffDisplacementCLM hΩ η hη U) =
      localCutoffVelocityCLM hΩ.measurableSet η (wkpCoordinateCLM (singleDerivIndex n i) U) +
        localCutoffVelocityCLM hΩ.measurableSet
          (_root_.TestFunction.lineDerivCLM (k := ⊤) ℝ (EuclideanSpace.single i 1) η)
          (wkpBaseCoordinateCLM U) := by
  change Extension.Lp.zeroExtendLp hΩ.measurableSet ((cutoffCLM η U).val (singleDerivIndex n i)) = _
  rw [cutoffCLM_singleDeriv_eq, map_add, cutoff_base]
  rfl

/-- The commutator `2 Dη · DU + Δη U`, realized in spatial L² using only H¹ data. -/
def localCutoffCommutatorCLM (hΩ : IsOpen Ω)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hη : tsupport η.toFun ⊆ Ω) :
    H¹(Ω) →L[ℝ] DerivLp n 2 univ :=
  ∑ i : Fin n,
    ((wkpCoordinateCLM (singleDerivIndex n i)).comp
      (localCutoffDisplacementCLM hΩ
        (_root_.TestFunction.lineDerivCLM (k := ⊤) ℝ (EuclideanSpace.single i 1) η)
        ((tsupport_cutoff_deriv_subset η i).trans hη)) +
    (localCutoffVelocityCLM hΩ.measurableSet
      (_root_.TestFunction.lineDerivCLM (k := ⊤) ℝ (EuclideanSpace.single i 1) η)).comp
      (wkpCoordinateCLM (singleDerivIndex n i)))

private theorem inner_base_deriv (U V : H¹(ℝ^n)) (i : Fin n) :
    ⟪wkpBaseCoordinateCLM U, wkpCoordinateCLM (singleDerivIndex n i) V⟫_ℝ =
      -⟪wkpCoordinateCLM (singleDerivIndex n i) U, wkpBaseCoordinateCLM V⟫_ℝ := by
  have hw : HasWeakDerivativeOn univ [i] (wkpBaseCoordinateCLM U : ℝ^n → ℝ)
      (wkpCoordinateCLM (singleDerivIndex n i) U : ℝ^n → ℝ) := by
    simpa only [singleDerivIndex_toList, wkpBaseCoordinateCLM_apply,
      wkpCoordinateCLM_apply] using U.property (singleDerivIndex n i)
  exact weakDerivative_integrationByParts_H10 i _ _ hw
    ⟨V, DifferenceQuotient.h1Space_mem_H10_univ V⟩

/-- The cutoff weak Laplacian identity keeps its commutator in L². -/
theorem gradientForm_localCutoffDisplacementCLM (hΩ : IsOpen Ω) (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hη : tsupport η.toFun ⊆ Ω) (U : H¹(Ω)) (φ : H¹(ℝ^n)) :
    gradientForm n (localCutoffDisplacementCLM hΩ η hη U) φ =
      (∑ i : Fin n, ⟪wkpCoordinateCLM (singleDerivIndex n i) U,
        wkpCoordinateCLM (singleDerivIndex n i)
          (localCutoffTestCLM hΩ η hη φ : H¹(Ω))⟫_ℝ) -
        ⟪localCutoffCommutatorCLM hΩ η hη U, wkpBaseCoordinateCLM φ⟫_ℝ := by
  classical
  rw [gradientForm_apply]
  simp only [localCutoffCommutatorCLM, sum_apply, add_apply,
    ContinuousLinearMap.comp_apply, sum_inner, inner_add_left, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  let β := _root_.TestFunction.lineDerivCLM (k := ⊤) ℝ (EuclideanSpace.single i 1) η
  have hβ : tsupport β.toFun ⊆ Ω := (tsupport_cutoff_deriv_subset η i).trans hη
  have hi := inner_base_deriv (localCutoffDisplacementCLM hΩ β hβ U) φ i
  rw [localCutoffDisplacementCLM_base] at hi
  change ⟪wkpCoordinateCLM (singleDerivIndex n i) (localCutoffDisplacementCLM hΩ η hη U),
    wkpCoordinateCLM (singleDerivIndex n i) φ⟫_ℝ = _
  rw [localCutoffDisplacementCLM_singleDeriv, inner_add_left]
  change _ = ⟪U.val (singleDerivIndex n i),
    (cutoffCLM η (restrictCLM hΩ.measurableSet (subset_univ Ω) φ)).val (singleDerivIndex n i)⟫_ℝ - _
  rw [cutoffCLM_singleDeriv_eq, inner_add_right]
  have hm (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (p : DerivLp n 2 Ω) (z : DerivLp n 2 univ) :
      ⟪localCutoffVelocityCLM hΩ.measurableSet ψ p, z⟫_ℝ =
        ⟪p, testFunctionLpTop (Ω := Ω) ψ • restrictDerivLp (subset_univ Ω) z⟫_ℝ := by
    change ⟪Extension.Lp.zeroExtendLp hΩ.measurableSet (testFunctionLpTop (Ω := Ω) ψ • p), z⟫_ℝ = _
    rw [Extension.Lp.inner_zeroExtendLp_eq_inner_restrict, Lp.inner_lpSMul_left]
  simp only [hm] at hi ⊢
  rw [cutoff_base]
  simp only [wkpCoordinateCLM_apply, wkpBaseCoordinateCLM_apply,
    restrictCLM_apply_coe, restrictAmbient_apply] at hi ⊢
  dsimp only [β] at hi
  linarith only [hi]

end PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet
