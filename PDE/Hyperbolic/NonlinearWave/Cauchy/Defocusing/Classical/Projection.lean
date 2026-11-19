/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Cubic
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.General.LocalEvolution

/-!
# Identifying higher cubic waves with the energy evolution

The high reaction and the energy cubic agree almost everywhere. Projection
commutes with the constructed linear semigroup and its Duhamel integral.
Consequently every finite higher mild trajectory is the unique cubic energy
trajectory on that interval, and inherits its conserved-energy estimates.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace PDE.Analysis.Evolution
open scoped NNReal Sobolev SobolevSpace.WholeSpaceHilbert Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing

/-- The ordinary H¹ × L² coordinates of higher Sobolev wave data. -/
def energyProjectionCLM (k : ℕ) :
    (W^{k + 1,2}(ℝ^3) × W^{k,2}(ℝ^3)) →L[ℝ] H¹(ℝ^3) × DerivLp 3 2 univ :=
  (lowerOrderCLM (by omega : 1 ≤ k + 1)).prodMap wkpBaseCoordinateCLM

/-- The product projection is the coordinate form of the constructed energy inclusion. -/
theorem energyProjectionCLM_eq_coordinates (k : ℕ) (x : W^{k + 1,2}(ℝ^3) × W^{k,2}(ℝ^3)) :
    energyProjectionCLM k x = coordinates 3 (higherEnergyInclusionCLM 3 k x) :=
  (coordinates_higherEnergyInclusionCLM 3 k x).symm

/-- Forgetting higher regularity commutes with the linear wave evolution. -/
theorem energyProjectionCLM_semigroup (k : ℕ) (t : ℝ≥0) (x : W^{k + 1,2}(ℝ^3) × W^{k,2}(ℝ^3)) :
    energyProjectionCLM k (higherLinearSemigroup 3 k t x) =
      productSemigroup 3 t (energyProjectionCLM k x) := by
  rw [energyProjectionCLM_eq_coordinates, higherEnergyInclusionCLM_higherLinearSemigroup]
  change coordinates 3 (linearSemigroup 3 t (higherEnergyInclusionCLM 3 k x)) =
    coordinates 3 (linearSemigroup 3 t ((coordinates 3).symm (energyProjectionCLM k x)))
  rw [energyProjectionCLM_eq_coordinates, ContinuousLinearEquiv.symm_apply_apply]

/-- Projection commutes with higher Duhamel forcing in product energy coordinates. -/
theorem energyProjectionCLM_duhamel (k : ℕ)
    {F : ℝ → W^{k + 1,2}(ℝ^3) × W^{k,2}(ℝ^3)} (hF : Continuous F) (t : ℝ) :
    energyProjectionCLM k ((higherLinearSemigroup 3 k).duhamel F t) =
      (productSemigroup 3).duhamel (fun s ↦ energyProjectionCLM k (F s)) t := by
  unfold StronglyContinuousSemigroup.duhamel
  rw [← (energyProjectionCLM k).intervalIntegral_comp_comm
    (((higherLinearSemigroup 3 k).continuous_duhamelIntegrand hF t).intervalIntegrable 0 t)]
  refine intervalIntegral.integral_congr fun s _ ↦ ?_
  exact energyProjectionCLM_semigroup k (t - s).toNNReal (F s)

/-- The high Sobolev cube has exactly the energy cubic as its L² coordinate. -/
theorem wkpBaseCoordinateCLM_higherComposition_cubic {k : ℕ}
    (hk : (3 : ℝ) < 2 * ((k : ℝ) - 1)) (h1 : 1 ≤ k) (u : W^{k,2}(ℝ^3)) :
    wkpBaseCoordinateCLM (higherComposition hk (contDiff_id.pow 3) (by simp) u) =
      cubicNonlinearity.source (lowerOrderCLM h1 u) := by
  apply Lp.ext
  have hn := higherComposition_ae hk (contDiff_id.pow 3) (by simp) u
  have hc := Power.source_three_ae (lowerOrderCLM h1 u)
  simp only [domainMeasure, Measure.restrict_univ] at hc ⊢
  exact hn.trans hc.symm

/-- Projection of the higher cubic source is the sealed energy vector field. -/
theorem energyProjectionCLM_higherSmoothMap {k : ℕ}
    (hk : (3 : ℝ) < 2 * ((k : ℝ) - 1)) (h1 : 1 ≤ k)
    (z : W^{k + 1,2}(ℝ^3) × W^{k,2}(ℝ^3)) :
    energyProjectionCLM k (higherSmoothMap hk (contDiff_id.pow 3) (by simp) z) =
      cubicNonlinearity.vectorField (energyProjectionCLM k z) := by
  change (lowerOrderCLM _ 0, wkpBaseCoordinateCLM (lowerOrderCLM (Nat.le_succ k) z.1 -
      higherComposition hk (contDiff_id.pow 3) (by simp) (lowerOrderCLM (Nat.le_succ k) z.1))) = _
  rw [map_zero, map_sub, wkpBaseCoordinateCLM_higherComposition_cubic hk h1,
    lowerOrderCLM_trans_apply]
  rfl

/-- Every finite high Sobolev cubic trajectory solves the original energy evolution. -/
theorem energyProjection_isMildSolutionOn {k : ℕ}
    (hk : (3 : ℝ) < 2 * ((k : ℝ) - 1)) (h1 : 1 ≤ k)
    {x : W^{k + 1,2}(ℝ^3) × W^{k,2}(ℝ^3)} {τ : ℝ≥0}
    {u : C(Icc (0 : ℝ) (τ : ℝ), W^{k + 1,2}(ℝ^3) × W^{k,2}(ℝ^3))}
    (hu : (higherLinearSemigroup 3 k).IsMildSolutionOn
      (higherSmoothMap hk (contDiff_id.pow 3) (by simp)) x τ u) :
    (productSemigroup 3).IsMildSolutionOn cubicNonlinearity.vectorField (energyProjectionCLM k x) τ
      ⟨fun t ↦ energyProjectionCLM k (u t),
        (energyProjectionCLM k).continuous.comp u.continuous⟩ := by
  let v : C(Icc (0 : ℝ) (τ : ℝ), H¹(ℝ^3) × DerivLp 3 2 univ) :=
    ⟨fun t ↦ energyProjectionCLM k (u t), (energyProjectionCLM k).continuous.comp u.continuous⟩
  intro t
  have he := congrArg (energyProjectionCLM k) (hu t)
  rw [map_add, energyProjectionCLM_semigroup] at he
  have hd := energyProjectionCLM_duhamel k
    ((higherSmoothMap hk (contDiff_id.pow 3) (by simp)).continuous.comp
      (u.continuous.Icc_extend' (h := τ.coe_nonneg))) t
  erw [hd] at he
  change v t = _ at he ⊢
  rw [he]
  congr 1
  refine (productSemigroup 3).duhamel_congr t.property.1 fun s _ ↦ ?_
  dsimp only [Function.comp_apply]
  rw [energyProjectionCLM_higherSmoothMap hk h1]
  rfl

/-- The projected high trajectory agrees with the already constructed global energy solution. -/
theorem energyProjection_eq_globalSolution {k : ℕ}
    (hk : (3 : ℝ) < 2 * ((k : ℝ) - 1)) (h1 : 1 ≤ k)
    {x : W^{k + 1,2}(ℝ^3) × W^{k,2}(ℝ^3)} {τ : ℝ≥0}
    {u : C(Icc (0 : ℝ) (τ : ℝ), W^{k + 1,2}(ℝ^3) × W^{k,2}(ℝ^3))}
    (hu : (higherLinearSemigroup 3 k).IsMildSolutionOn
      (higherSmoothMap hk (contDiff_id.pow 3) (by simp)) x τ u)
    (t : Icc (0 : ℝ) (τ : ℝ)) :
    energyProjectionCLM k (u t) = cubicNonlinearity.globalSolution (energyProjectionCLM k x) t := by
  have he := (energyProjection_isMildSolutionOn hk h1 hu).eq_of_locallyLipschitz
    cubicNonlinearity.locallyLipschitz_vectorField
    (cubicNonlinearity.globalTrace_isMildSolutionOn (energyProjectionCLM k x) τ)
  exact congrArg (fun v ↦ v t) he

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing
