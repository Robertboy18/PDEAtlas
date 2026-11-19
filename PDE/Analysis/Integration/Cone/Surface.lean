/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean.SpaceTime
public import PDE.Analysis.MeasureTheory.AreaFormula.C1
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Analysis.Normed.Module.Normalize

/-!
# The area factor of a backward light cone

The lateral cone is the graph of `x ↦ T - ‖x - c‖`. Its derivative sends a
spatial vector `h` to `(-⟪ν,h⟫, h)`, where `ν` is the unit radial vector.
The Gram determinant is `1 + ‖ν‖² = 2`, giving the area factor `√2` for normalized
Euclidean Hausdorff measure. This is the factor `1/√2` in Evans's flux identity (3), which he
attributes to the tilt of the cone at the constant angle `π/4` (§12.1.2, Theorem 2(i)).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.1.2, Theorem 2(i), (3), and step 1 of its proof,
  p. 661. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set MeasureTheory PDE.Common
open scoped RealInnerProductSpace

namespace WaveEquation

variable {n : ℕ}

/-- The differential of the cone graph with radial normal `v`. -/
def coneGraphDifferential (v : ℝ^n) : ℝ^n →L[ℝ] ℝ^(n + 1) :=
  (timeSpaceContinuousLinearEquiv n).symm.toContinuousLinearMap.comp
    ((-innerSL ℝ v).prod (ContinuousLinearMap.id ℝ (ℝ^n)))

/-- The cone graph differential keeps the spatial component unchanged. -/
@[simp]
theorem coneGraphDifferential_apply (v h : ℝ^n) :
    coneGraphDifferential v h = timeSpaceCons (-⟪v, h⟫) h := rfl

/-- The cone graph is an immersion for every radial covector. -/
theorem coneGraphDifferential_injective (v : ℝ^n) :
    Function.Injective (coneGraphDifferential v) := by
  intro x y h
  simpa using congrArg spatialPart h

/-- The induced metric on the cone graph is the spatial metric plus the square
of the radial covector. -/
theorem inner_coneGraphDifferential (v x y : ℝ^n) :
    ⟪coneGraphDifferential v x, coneGraphDifferential v y⟫ =
      ⟪x, y⟫ + ⟪v, x⟫ * ⟪v, y⟫ := by
  simp [PiLp.inner_apply, Fin.sum_univ_succ, mul_comm, add_comm]

/-- The area factor of a graph with radial covector `v`. -/
theorem normDet_coneGraphDifferential (v : ℝ^n) :
    (coneGraphDifferential v).toLinearMap.normDet = Real.sqrt (1 + ‖v‖ ^ 2) := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hgram : Matrix.gram ℝ (fun i ↦ (coneGraphDifferential v).toLinearMap (b i)) =
      1 + Matrix.replicateCol Unit (fun i ↦ v i) *
        Matrix.replicateRow Unit (fun i ↦ v i) := by
    ext i j
    change ⟪coneGraphDifferential v (b i), coneGraphDifferential v (b j)⟫ = _
    rw [inner_coneGraphDifferential, b.inner_eq_ite]
    simp only [b, EuclideanSpace.inner_basisFun_real]
    simp [Matrix.mul_apply, Matrix.one_apply]
  have hs := (coneGraphDifferential v).toLinearMap.normDet_sq_eq_det_gram b
  change (coneGraphDifferential v).toLinearMap.normDet ^ 2 = _ at hs
  rw [hgram, Matrix.det_one_add_replicateCol_mul_replicateRow] at hs
  have hnorm : (fun i ↦ v i) ⬝ᵥ (fun i ↦ v i) = ‖v‖ ^ 2 := by
    simpa only [dotProduct, pow_two] using (EuclideanSpace.real_norm_sq_eq v).symm
  rw [hnorm] at hs
  rw [← hs, Real.sqrt_sq (LinearMap.normDet_nonneg _)]

/-- A unit radial normal gives the light-cone area factor `√2`. -/
theorem normDet_coneGraphDifferential_of_norm_eq_one {v : ℝ^n} (hv : ‖v‖ = 1) :
    (coneGraphDifferential v).toLinearMap.normDet = Real.sqrt 2 := by
  simpa only [hv, one_pow, one_add_one_eq_two] using normDet_coneGraphDifferential v

/-- The spatial parametrization of the backward light cone. -/
def backwardConeGraph (c : ℝ^n) (T : ℝ) (x : ℝ^n) : ℝ^(n + 1) :=
  timeSpaceCons (T - ‖x - c‖) x

/-- Spatial projection is a left inverse of the cone parametrization. -/
theorem backwardConeGraph_injective (c : ℝ^n) (T : ℝ) :
    Function.Injective (backwardConeGraph c T) := by
  intro x y h
  simpa [backwardConeGraph] using congrArg spatialPart h

/-- The cone parametrization is smooth away from its vertex. -/
theorem contDiffOn_backwardConeGraph (c : ℝ^n) (T : ℝ) :
    ContDiffOn ℝ 1 (backwardConeGraph c T) ({c}ᶜ : Set (ℝ^n)) := by
  intro x hx
  have hne : x - c ≠ 0 := sub_ne_zero.mpr hx
  exact ((timeSpaceContinuousLinearEquiv n).symm.contDiff.contDiffAt.comp x
    ((contDiffAt_const.sub ((contDiffAt_id.sub contDiffAt_const).norm ℝ hne)).prodMk
      contDiffAt_id)).contDiffWithinAt

/-- Away from the vertex, the radial normal determines the cone derivative. -/
theorem hasFDerivAt_backwardConeGraph (c : ℝ^n) (T : ℝ) {x : ℝ^n} (hx : x ≠ c) :
    HasFDerivAt (backwardConeGraph c T)
      (coneGraphDifferential (NormedSpace.normalize (x - c))) x := by
  have hn : HasFDerivAt (fun y : ℝ^n ↦ ‖y - c‖)
      (innerSL ℝ (NormedSpace.normalize (x - c))) x := by
    convert ((hasFDerivAt_id x).sub_const c).norm_sq.sqrt
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx))) using 1
    · ext y
      exact (Real.sqrt_sq (norm_nonneg _)).symm
    · ext h
      simp [NormedSpace.normalize, Real.sqrt_sq (norm_nonneg _)]
      field_simp
  exact (timeSpaceContinuousLinearEquiv n).symm.toContinuousLinearMap.hasFDerivAt.comp x
    ((hn.const_sub T).prodMk (hasFDerivAt_id x))

/-- The normalized Hausdorff area factor of the cone graph is `√2`. -/
theorem normDet_fderiv_backwardConeGraph (c : ℝ^n) (T : ℝ) {x : ℝ^n} (hx : x ≠ c) :
    (fderiv ℝ (backwardConeGraph c T) x).toLinearMap.normDet = Real.sqrt 2 := by
  rw [(hasFDerivAt_backwardConeGraph c T hx).fderiv]
  exact normDet_coneGraphDifferential_of_norm_eq_one
    (NormedSpace.norm_normalize (sub_ne_zero.mpr hx))

/-- On any open part of the cone away from its vertex, normalized Hausdorff
integration is `√2` times spatial integration of the graph pullback. -/
theorem integral_backwardConeGraph_image
    (c : ℝ^n) (T : ℝ) {U : Set (ℝ^n)} (hU : IsOpen U) (hc : c ∉ U)
    (g : ℝ^(n + 1) → ℝ)
    (hg : AEStronglyMeasurable g
      ((Measure.euclideanHausdorffMeasure n).restrict (backwardConeGraph c T '' U))) :
    (∫ p in backwardConeGraph c T '' U, g p ∂Measure.euclideanHausdorffMeasure n) =
      Real.sqrt 2 * ∫ x in U, g (backwardConeGraph c T x) := by
  have hne : ∀ x ∈ U, x ≠ c := fun x hx h ↦ hc (h ▸ hx)
  have hf := (contDiffOn_backwardConeGraph c T).mono (fun x hx ↦ hne x hx)
  have hd : ∀ x ∈ U, Function.Injective (fderiv ℝ (backwardConeGraph c T) x) := by
    intro x hx
    rw [(hasFDerivAt_backwardConeGraph c T (hne x hx)).fderiv]
    exact coneGraphDifferential_injective _
  have harea := integral_image_eq_integral_normDet_smul_of_contDiffOn hU hf
    (backwardConeGraph_injective c T).injOn hd g (by simpa using hg)
  simp only [finrank_euclideanSpace_fin] at harea
  rw [harea, ← integral_const_mul]
  apply setIntegral_congr_fun hU.measurableSet
  intro x hx
  change (fderiv ℝ (backwardConeGraph c T) x).toLinearMap.normDet *
    g (backwardConeGraph c T x) = _
  rw [normDet_fderiv_backwardConeGraph c T (hne x hx)]

/-- The cone parametrization is globally Lipschitz, including at the vertex. -/
theorem exists_lipschitzWith_backwardConeGraph (c : ℝ^n) (T : ℝ) :
    ∃ K, LipschitzWith K (backwardConeGraph c T) := by
  have ht := (LipschitzWith.const T).sub (LipschitzWith.dist_left c)
  have hp := (timeSpaceContinuousLinearEquiv n).symm.toContinuousLinearMap.lipschitzWith.comp
    (ht.prodMk LipschitzWith.id)
  change LipschitzWith _ (fun x : ℝ^n ↦ timeSpaceCons (T - dist x c) x) at hp
  refine ⟨‖(timeSpaceContinuousLinearEquiv n).symm.toContinuousLinearMap‖₊ *
    max (0 + 1) 1, ?_⟩
  change LipschitzWith _ (fun x : ℝ^n ↦ timeSpaceCons (T - ‖x - c‖) x)
  simpa only [dist_eq_norm] using hp

/-- Spatial null sets parametrize null sets for the normalized surface measure. -/
theorem euclideanHausdorffMeasure_backwardConeGraph_image_null
    (c : ℝ^n) (T : ℝ) {s : Set (ℝ^n)} (hs : volume s = 0) :
    Measure.euclideanHausdorffMeasure n (backwardConeGraph c T '' s) = 0 := by
  obtain ⟨K, hK⟩ := exists_lipschitzWith_backwardConeGraph c T
  have h := hK.lipschitzOnWith.euclideanHausdorffMeasure_image_le (s := s) n
  rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume, hs, mul_zero] at h
  exact le_antisymm h bot_le

/-- Almost-everywhere equal spatial domains give almost-everywhere equal cone surfaces. -/
theorem backwardConeGraph_image_ae_eq (c : ℝ^n) (T : ℝ)
    {s t : Set (ℝ^n)} (h : s =ᵐ[volume] t) :
    backwardConeGraph c T '' s =ᵐ[Measure.euclideanHausdorffMeasure n]
      backwardConeGraph c T '' t := by
  rw [ae_eq_set] at h ⊢
  constructor
  · rw [← image_sdiff (backwardConeGraph_injective c T)]
    exact euclideanHausdorffMeasure_backwardConeGraph_image_null c T h.1
  · rw [← image_sdiff (backwardConeGraph_injective c T)]
    exact euclideanHausdorffMeasure_backwardConeGraph_image_null c T h.2

/-- The closed lateral surface of the backward cone, including its rim and vertex. -/
def backwardConeLateralSurface (c : ℝ^n) (T : ℝ) : Set (ℝ^(n + 1)) :=
  {p | 0 ≤ p 0 ∧ p 0 ≤ T ∧ ‖spatialPart p - c‖ = T - p 0}

/-- The closed spatial ball parametrizes the entire closed lateral cone surface. -/
theorem backwardConeLateralSurface_eq_image (c : ℝ^n) (T : ℝ) :
    backwardConeLateralSurface c T = backwardConeGraph c T '' Metric.closedBall c T := by
  ext p
  constructor
  · rintro ⟨ht, _, hx⟩
    refine ⟨spatialPart p, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_eq_norm, hx]
      exact sub_le_self T ht
    · unfold backwardConeGraph
      rw [hx, sub_sub_cancel, timeSpaceCons_spatialPart]
  · rintro ⟨x, hx, rfl⟩
    change 0 ≤ T - ‖x - c‖ ∧ T - ‖x - c‖ ≤ T ∧ ‖x - c‖ = T - (T - ‖x - c‖)
    exact ⟨sub_nonneg.mpr (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx),
      sub_le_self T (norm_nonneg _), (sub_sub_cancel T _).symm⟩

/-- Removing the spatial rim and vertex changes neither the volume integral nor
its normalized Hausdorff image integral. -/
theorem closedBall_ae_eq_coneGraph_domain [Fact (0 < n)] (c : ℝ^n) (T : ℝ) :
    Metric.closedBall c T =ᵐ[volume] Metric.ball c T \ {c} := by
  let : Nontrivial (ℝ^n) := Module.nontrivial_of_finrank_pos (R := ℝ)
    (by simpa only [finrank_euclideanSpace_fin] using (Fact.out : 0 < n))
  have hball : Metric.closedBall c T =ᵐ[volume] Metric.ball c T := by
    apply ae_eq_set.mpr
    constructor
    · rw [Metric.closedBall_sdiff_ball]
      exact Measure.addHaar_sphere volume c T
    · rw [sdiff_eq_empty.mpr Metric.ball_subset_closedBall]
      exact measure_empty
  exact hball.trans (sdiff_null_ae_eq_self (measure_singleton c)).symm

/-- The normalized Hausdorff surface integral on the closed cone has area factor
`√2`; the initial rim and vertex are included in the statement. -/
theorem integral_backwardConeLateralSurface [Fact (0 < n)]
    (c : ℝ^n) (T : ℝ) (g : ℝ^(n + 1) → ℝ)
    (hg : AEStronglyMeasurable g
      ((Measure.euclideanHausdorffMeasure n).restrict (backwardConeLateralSurface c T))) :
    (∫ p in backwardConeLateralSurface c T, g p ∂Measure.euclideanHausdorffMeasure n) =
      Real.sqrt 2 * ∫ x in Metric.ball c T, g (backwardConeGraph c T x) := by
  let U := Metric.ball c T \ {c}
  have hU : IsOpen U := Metric.isOpen_ball.sdiff isClosed_singleton
  have hsub : U ⊆ Metric.closedBall c T := fun _ hx ↦ Metric.ball_subset_closedBall hx.1
  have heq := backwardConeGraph_image_ae_eq c T (closedBall_ae_eq_coneGraph_domain c T)
  rw [backwardConeLateralSurface_eq_image] at hg ⊢
  rw [setIntegral_congr_set heq]
  rw [integral_backwardConeGraph_image c T hU (by simp [U]) g
    (hg.mono_set (image_mono hsub))]
  congr 1
  let : Nontrivial (ℝ^n) := Module.nontrivial_of_finrank_pos (R := ℝ)
    (by simpa only [finrank_euclideanSpace_fin] using (Fact.out : 0 < n))
  exact setIntegral_congr_set (sdiff_null_ae_eq_self (measure_singleton c))

end WaveEquation
