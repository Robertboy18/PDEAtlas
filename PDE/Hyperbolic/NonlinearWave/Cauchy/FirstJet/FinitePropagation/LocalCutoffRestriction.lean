/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.FinitePropagation.LocalCutoff
import PDE.DistributionTheory.TestFunction.Derivative.Commutation

/-!
# Interior agreement for compact wave localization

On an open region where the spatial cutoff is constant, localization acts by
that constant and its commutator vanishes. Restriction also preserves the full
first-jet reaction. These identities locate the cutoff error outside the
region where a local weak wave is being compared.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal Sobolev SobolevSpace.WholeSpaceHilbert Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet

open SobolevSpace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω S : Set (ℝ^n)}

/-- A velocity cutoff restricts to scalar multiplication wherever the cutoff is constant. -/
theorem restrict_localCutoffVelocityCLM (hΩ : MeasurableSet Ω) (hS : MeasurableSet S) (hSΩ : S ⊆ Ω)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) {c : ℝ} (hη : ∀ y ∈ S, η y = c) (v : DerivLp n 2 Ω) :
    restrictDerivLp (subset_univ S) (localCutoffVelocityCLM hΩ η v) =
      c • restrictDerivLp hSΩ v := by
  apply Lp.ext
  have hz := (Extension.Lp.zeroExtendLp_agree_ae hΩ
    (mulLpLeft (testFunctionLpTop (Ω := Ω) η) v)).filter_mono (ae_mono (domainMeasure_le hSΩ))
  have hm := (mulLpLeft_apply_ae (testFunctionLpTop (Ω := Ω) η) v).filter_mono
    (ae_mono (domainMeasure_le hSΩ))
  have he := (testFunctionLpTop_apply_ae (Ω := Ω) η).filter_mono (ae_mono (domainMeasure_le hSΩ))
  filter_upwards [restrictDerivLp_apply_ae (subset_univ S)
    (localCutoffVelocityCLM hΩ η v), hz, hm, he,
    restrictDerivLp_apply_ae hSΩ v, Lp.coeFn_smul c (restrictDerivLp hSΩ v),
    ae_restrict_mem hS] with y hr hz hm he hv hc hy
  change (localCutoffVelocityCLM hΩ η v : ℝ^n → ℝ) y = _ at hz
  rw [hr, hz, hm, he, hc, Pi.smul_apply, smul_eq_mul, hv]
  exact congrArg (fun r : ℝ ↦ r * v y) (hη y hy)

/-- A displacement cutoff restricts to scalar multiplication on its constant region. -/
theorem restrict_localCutoffDisplacementCLM (hΩ : IsOpen Ω) (hS : IsOpen S)
    (hSΩ : S ⊆ Ω) (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hηΩ : tsupport η.toFun ⊆ Ω) {c : ℝ} (hη : ∀ y ∈ S, η y = c) (U : H¹(Ω)) :
    restrictCLM hS.measurableSet (subset_univ S) (localCutoffDisplacementCLM hΩ η hηΩ U) =
      c • restrictCLM hS.measurableSet hSΩ U := by
  apply wkpBaseCoordinateCLM_injective hS
  change restrictDerivLp (subset_univ S)
    (wkpBaseCoordinateCLM (localCutoffDisplacementCLM hΩ η hηΩ U)) = _
  rw [localCutoffDisplacementCLM_base, map_smul]
  exact restrict_localCutoffVelocityCLM hΩ.measurableSet hS.measurableSet hSΩ η hη _

/-- Spatial derivatives of a test cutoff vanish on every open constant region. -/
theorem cutoff_deriv_eq_zero_on (hS : IsOpen S) (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) {c : ℝ}
    (hη : ∀ y ∈ S, η y = c) (i : Fin n) {y : ℝ^n} (hy : y ∈ S) :
    (_root_.TestFunction.lineDerivCLM (k := ⊤) ℝ (EuclideanSpace.single i 1) η) y = 0 := by
  have he : (η : ℝ^n → ℝ) =ᶠ[𝓝 y] fun _ ↦ c := by
    filter_upwards [hS.mem_nhds hy] with z hz using hη z hz
  rw [_root_.TestFunction.lineDerivCLM_apply_eq_fderiv, he.fderiv_eq,
    fderiv_const_apply, zero_apply]

/-- The cutoff commutator vanishes on an open constant region, using only H¹ regularity. -/
theorem restrict_localCutoffCommutatorCLM (hΩ : IsOpen Ω) (hS : IsOpen S)
    (hSΩ : S ⊆ Ω) (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hηΩ : tsupport η.toFun ⊆ Ω) {c : ℝ} (hη : ∀ y ∈ S, η y = c) (U : H¹(Ω)) :
    restrictDerivLp (subset_univ S) (localCutoffCommutatorCLM hΩ η hηΩ U) = 0 := by
  simp only [localCutoffCommutatorCLM, sum_apply, add_apply,
    ContinuousLinearMap.comp_apply, map_sum, map_add]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  let β := _root_.TestFunction.lineDerivCLM (k := ⊤) ℝ (EuclideanSpace.single i 1) η
  have hβ : ∀ y ∈ S, β y = 0 := fun y hy ↦ cutoff_deriv_eq_zero_on hS η hη i hy
  have hv := restrict_localCutoffVelocityCLM hΩ.measurableSet hS.measurableSet hSΩ β hβ
    (wkpCoordinateCLM (singleDerivIndex n i) U)
  have hq := restrict_localCutoffDisplacementCLM hΩ hS hSΩ β
    ((tsupport_cutoff_deriv_subset η i).trans hηΩ) hβ U
  have hd := congrArg (wkpCoordinateCLM (singleDerivIndex n i)) hq
  simp only [zero_smul, map_zero] at hv hd
  change _ + restrictDerivLp (subset_univ S) (localCutoffVelocityCLM hΩ.measurableSet β
    (wkpCoordinateCLM (singleDerivIndex n i) U)) = 0
  rw [hv, add_zero]
  exact hd

/-- Restriction between arbitrary subdomains preserves the weak gradient representative. -/
theorem gradient_restrict_between_ae (hS : MeasurableSet S) (hSΩ : S ⊆ Ω) (U : H¹(Ω)) :
    (∇ (restrictCLM hS hSΩ U) : ℝ^n → ℝ^n) =ᵐ[domainMeasure n S] (∇ U : ℝ^n → ℝ^n) := by
  have hbig := (wkpGradientCLM_apply_ae U).filter_mono (ae_mono (domainMeasure_le hSΩ))
  have hcoord := ae_all_iff.mpr (fun i : Fin n ↦
    restrictCLM_apply_ae hS hSΩ U (singleDerivIndex n i))
  filter_upwards [wkpGradientCLM_apply_ae (restrictCLM hS hSΩ U), hbig, hcoord] with y hy hz hc
  exact PiLp.ext fun i ↦ (hy i).trans ((hc i).trans (hz i).symm)

/-- Local first-jet reaction commutes with restriction between arbitrary subdomains. -/
theorem localReaction_restrict_between {f : (ℝ^n × ℝ × ℝ) → ℝ} {L : NNReal} (hf : LipschitzWith L f)
    (hf0 : f 0 = 0) (hS : MeasurableSet S) (hSΩ : S ⊆ Ω) (z : H¹(Ω) × DerivLp n 2 Ω) :
    localReaction hf hf0 (restrictCLM hS hSΩ z.1, restrictDerivLp hSΩ z.2) =
      restrictDerivLp hSΩ (localReaction hf hf0 z) := by
  apply Lp.ext
  have hr := (localReaction_apply_ae hf hf0 z).filter_mono (ae_mono (domainMeasure_le hSΩ))
  filter_upwards [localReaction_apply_ae hf hf0 (restrictCLM hS hSΩ z.1, restrictDerivLp hSΩ z.2),
    restrictDerivLp_apply_ae hSΩ (localReaction hf hf0 z), hr,
    gradient_restrict_between_ae hS hSΩ z.1, restrictDerivLp_apply_ae hSΩ z.2,
    restrictCLM_apply_ae hS hSΩ z.1 (baseIndex n 1)] with y hy hz hload hg hv hq
  exact hy.trans ((congrArg f (Prod.ext hg (Prod.ext hv hq))).trans (hload.symm.trans hz.symm))

end PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet
