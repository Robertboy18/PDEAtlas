/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Time.WeakDerivative.RealLine
public import PDE.Spaces.Sobolev.GraphSpace.Evolution.RealLine
public import PDE.Spaces.Sobolev.Inequalities.Morrey.FiniteExponent.OneDimensional.WeakBound

/-!
# The real continuous representative of an H¹ graph element

Each Euclidean `L²` coordinate returns to the real line by a fixed linear
isometry. The stored weak derivative becomes a real weak pair, whose
mean-normalized primitive is a continuous representative.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set PDE.Analysis.Evolution SobolevSpace.Slices
open scoped ENNReal Topology Sobolev

namespace SobolevSpace.GraphSpace

/-- Returning a Euclidean coordinate to the real line is an `L²` isometry. -/
def oneDimensionalPushforwardL2 :
    DerivLp 1 2 univ →ₗᵢ[ℝ] Lp ℝ 2 (volume : Measure ℝ) :=
  Lp.compMeasurePreservingₗᵢ ℝ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm (by
    rw [domainMeasure, Measure.restrict_univ]
    exact measurePreserving_equivOfUnique_symm)

/-- The returned `L²` class has the expected real-coordinate representative. -/
theorem oneDimensionalPushforwardL2_ae (f : DerivLp 1 2 univ) :
    (oneDimensionalPushforwardL2 f : ℝ → ℝ) =ᵐ[volume]
      (f : ℝ^1 → ℝ) ∘ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm :=
  Lp.coeFn_compMeasurePreserving _ _

/-- Returning a pulled-back real `L²` class recovers that class exactly. -/
@[simp] theorem oneDimensionalPushforwardL2_pullback
    (f : Lp ℝ 2 (volume : Measure ℝ)) :
    oneDimensionalPushforwardL2 (oneDimensionalPullbackL2 f) = f := by
  change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f) = f
  rw [← Lp.compMeasurePreserving_comp_apply]
  have he : ((PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)) : ℝ^1 → ℝ) ∘
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm = id := by
    funext x
    exact (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).apply_symm_apply x
  simp only [he, Lp.compMeasurePreserving_id_apply]

/-- A Sobolev coordinate read as an ordinary real `L²` class. -/
def realLineCoordinateCLM (a : DerivIndex 1 1) :
    W^{1,2}(ℝ^1) →L[ℝ] Lp ℝ 2 (volume : Measure ℝ) :=
  oneDimensionalPushforwardL2.toContinuousLinearMap.comp (wkpCoordinateCLM a)

/-- Real-coordinate extraction is bounded by the graph norm. -/
theorem norm_realLineCoordinateCLM_le (a : DerivIndex 1 1) (U : W^{1,2}(ℝ^1)) :
    ‖realLineCoordinateCLM a U‖ ≤ ‖U‖ := by
  change ‖oneDimensionalPushforwardL2 (wkpCoordinateCLM a U)‖ ≤ ‖U‖
  rw [oneDimensionalPushforwardL2.norm_map]
  exact wkpCoordinateCLM_norm_le a U

/-- The real coordinates of every graph element form a weak pair. -/
theorem hasWeakTimeDerivativeOn_realLineCoordinates (U : W^{1,2}(ℝ^1)) :
    HasWeakTimeDerivativeOn univ
      (realLineCoordinateCLM (baseIndex 1 1) U)
      (realLineCoordinateCLM (singleDerivIndex 1 0) U) := by
  have h := U.property (singleDerivIndex 1 0)
  simp only [singleDerivIndex_toList] at h
  exact (hasWeakTimeDerivativeOn_of_euclidean h).congr_ae
    (oneDimensionalPushforwardL2_ae _).symm (oneDimensionalPushforwardL2_ae _).symm

/-- The explicit normalized primitive of the real weak pair. -/
def realLineRepresentative (U : W^{1,2}(ℝ^1)) : ℝ → ℝ :=
  lineRepresentative (realLineCoordinateCLM (baseIndex 1 1) U)
    (realLineCoordinateCLM (singleDerivIndex 1 0) U)

/-- The normalized primitive is continuous for every H¹ element. -/
theorem continuous_realLineRepresentative (U : W^{1,2}(ℝ^1)) :
    Continuous (realLineRepresentative U) :=
  continuous_lineRepresentative (locallyIntegrableOn_univ.mp
    (hasWeakTimeDerivativeOn_realLineCoordinates U).locallyIntegrable_g)

/-- The primitive represents the real base coordinate almost everywhere. -/
theorem realLineCoordinate_ae_representative (U : W^{1,2}(ℝ^1)) :
    (realLineCoordinateCLM (baseIndex 1 1) U : ℝ → ℝ) =ᵐ[volume]
      realLineRepresentative U :=
  (hasWeakTimeDerivativeOn_realLineCoordinates U).ae_eq_lineRepresentative

/-- The continuous representative retains the real weak derivative. -/
theorem hasWeakTimeDerivativeOn_realLineRepresentative (U : W^{1,2}(ℝ^1)) :
    HasWeakTimeDerivativeOn univ (realLineRepresentative U)
      (realLineCoordinateCLM (singleDerivIndex 1 0) U) :=
  (hasWeakTimeDerivativeOn_realLineCoordinates U).congr_ae
    (realLineCoordinate_ae_representative U) EventuallyEq.rfl

/-- The continuous representative is square integrable. -/
theorem memLp_realLineRepresentative (U : W^{1,2}(ℝ^1)) :
    MemLp (realLineRepresentative U) 2 volume :=
  (Lp.memLp (realLineCoordinateCLM (baseIndex 1 1) U)).ae_eq
    (realLineCoordinate_ae_representative U)

/-- The constructor's real base coordinate recovers the supplied `L²` class. -/
@[simp] theorem realLineCoordinateCLM_mkW12_base {f g : ℝ → ℝ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (hweak : HasWeakTimeDerivativeOn univ f g) :
    realLineCoordinateCLM (baseIndex 1 1) (mkW12OfWeakDerivative hf hg hweak) =
      hf.toLp f := by
  change oneDimensionalPushforwardL2 (realLineH1Jet (hf.toLp f) (hg.toLp g) _) = _
  rw [realLineH1Jet_base, oneDimensionalPushforwardL2_pullback]

/-- The constructor's real derivative coordinate recovers the supplied class. -/
@[simp] theorem realLineCoordinateCLM_mkW12_single {f g : ℝ → ℝ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (hweak : HasWeakTimeDerivativeOn univ f g) (i : Fin 1) :
    realLineCoordinateCLM (singleDerivIndex 1 i) (mkW12OfWeakDerivative hf hg hweak) =
      hg.toLp g := by
  change oneDimensionalPushforwardL2 (realLineH1Jet (hf.toLp f) (hg.toLp g) _) = _
  rw [realLineH1Jet_single, oneDimensionalPushforwardL2_pullback]

/-- A continuous weak pair is recovered pointwise by the normalized primitive. -/
theorem realLineRepresentative_mkW12 {f g : ℝ → ℝ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (hweak : HasWeakTimeDerivativeOn univ f g) (hcont : Continuous f) :
    realLineRepresentative (mkW12OfWeakDerivative hf hg hweak) = f := by
  apply (Continuous.ae_eq_iff_eq volume
    (continuous_realLineRepresentative _) hcont).mp
  have hrep := (realLineCoordinate_ae_representative
    (mkW12OfWeakDerivative hf hg hweak)).symm
  rw [realLineCoordinateCLM_mkW12_base] at hrep
  exact hrep.trans (MemLp.coeFn_toLp hf)

/-- Continuous representatives commute with subtraction. -/
theorem realLineRepresentative_sub (U V : W^{1,2}(ℝ^1)) :
    realLineRepresentative (U - V) = realLineRepresentative U - realLineRepresentative V := by
  apply (Continuous.ae_eq_iff_eq volume (continuous_realLineRepresentative _)
    ((continuous_realLineRepresentative U).sub (continuous_realLineRepresentative V))).mp
  have hsub := Lp.coeFn_sub (realLineCoordinateCLM (baseIndex 1 1) U)
    (realLineCoordinateCLM (baseIndex 1 1) V)
  rw [← map_sub] at hsub
  filter_upwards [realLineCoordinate_ae_representative (U - V),
    realLineCoordinate_ae_representative U, realLineCoordinate_ae_representative V,
    hsub] with x hUV hU hV hx
  exact hUV.symm.trans (hx.trans (congrArg₂ (· - ·) hU hV))

/-- Evaluation of the continuous representative is bounded in the
H¹ graph norm. The constant two comes from bounding each of the two rows. -/
theorem norm_realLineRepresentative_le (U : W^{1,2}(ℝ^1)) (x : ℝ) :
    ‖realLineRepresentative U x‖ ≤ 2 * ‖U‖ := by
  have h := (hasWeakTimeDerivativeOn_realLineRepresentative U).norm_apply_le_eLpNorm_toReal_add
    (continuous_realLineRepresentative U) (by norm_num : (1 : ℝ≥0∞) < 2)
    (memLp_realLineRepresentative U)
    (Lp.memLp (realLineCoordinateCLM (singleDerivIndex 1 0) U)) x
  rw [← eLpNorm_congr_ae (realLineCoordinate_ae_representative U),
    ← Lp.norm_def, ← Lp.norm_def] at h
  calc
    _ ≤ _ := h
    _ ≤ ‖U‖ + ‖U‖ := add_le_add
      (norm_realLineCoordinateCLM_le _ U) (norm_realLineCoordinateCLM_le _ U)
    _ = _ := by ring

/-- At every real point, evaluation of the continuous representative is
Lipschitz with respect to the H¹ graph norm. -/
theorem lipschitzWith_realLineRepresentative_eval (x : ℝ) :
    LipschitzWith 2 (fun U : W^{1,2}(ℝ^1) ↦ realLineRepresentative U x) := by
  apply LipschitzWith.of_dist_le_mul
  intro U V
  have h := norm_realLineRepresentative_le (U - V) x
  rw [realLineRepresentative_sub] at h
  simpa only [dist_eq_norm, Pi.sub_apply, NNReal.coe_ofNat] using h

/-- Pointwise trace values shared eventually by an H¹ convergent family
pass to its constructed continuous limiting representative. -/
theorem realLineRepresentative_limit_value
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {u : ι → W^{1,2}(ℝ^1)} {U : W^{1,2}(ℝ^1)} {x c : ℝ}
    (hu : Tendsto u l (𝓝 U))
    (htrace : ∀ᶠ i in l, realLineRepresentative (u i) x = c) :
    realLineRepresentative U x = c := by
  have hlim := ((lipschitzWith_realLineRepresentative_eval x).continuous.tendsto U).comp hu
  exact tendsto_nhds_unique hlim
    (tendsto_const_nhds.congr' (Filter.EventuallyEq.symm htrace))

/-- The continuous real representative defines the graph's base L² class. -/
@[simp] theorem toLp_realLineRepresentative (U : W^{1,2}(ℝ^1)) :
    (memLp_realLineRepresentative U).toLp (realLineRepresentative U) =
      realLineCoordinateCLM (baseIndex 1 1) U := by
  apply Lp.ext
  exact (memLp_realLineRepresentative U).coeFn_toLp.trans
    (realLineCoordinate_ae_representative U).symm

/-- Pulling a Euclidean L² class back after reading it on the real line
recovers the original class. -/
@[simp] theorem oneDimensionalPullbackL2_pushforward (f : DerivLp 1 2 univ) :
    oneDimensionalPullbackL2 (oneDimensionalPushforwardL2 f) = f := by
  apply oneDimensionalPushforwardL2.injective
  exact oneDimensionalPushforwardL2_pullback _

/-- Continuous real representatives commute with addition. -/
theorem realLineRepresentative_add (U V : W^{1,2}(ℝ^1)) :
    realLineRepresentative (U + V) = realLineRepresentative U + realLineRepresentative V := by
  have h := realLineRepresentative_sub (U + V) V
  rw [add_sub_cancel_right] at h
  exact eq_add_of_sub_eq h.symm

/-- Continuous real representatives commute with real scalar multiplication. -/
theorem realLineRepresentative_smul (c : ℝ) (U : W^{1,2}(ℝ^1)) :
    realLineRepresentative (c • U) = c • realLineRepresentative U := by
  apply (Continuous.ae_eq_iff_eq volume (continuous_realLineRepresentative _)
    ((continuous_realLineRepresentative U).const_smul c)).mp
  have hsmul := Lp.coeFn_smul c (realLineCoordinateCLM (baseIndex 1 1) U)
  rw [← map_smul] at hsmul
  filter_upwards [realLineCoordinate_ae_representative (c • U),
    realLineCoordinate_ae_representative U, hsmul] with x hc hU hx
  exact hc.symm.trans (hx.trans (congrArg (c • ·) hU))

/-- Evaluation of the continuous H¹ representative is a bounded linear functional. -/
def realLineRepresentativeEvalCLM (x : ℝ) : W^{1,2}(ℝ^1) →L[ℝ] ℝ where
  toFun U := realLineRepresentative U x
  map_add' U V := congrFun (realLineRepresentative_add U V) x
  map_smul' c U := congrFun (realLineRepresentative_smul c U) x
  cont := (lipschitzWith_realLineRepresentative_eval x).continuous

/-- The continuous representative of the zero graph is zero. -/
@[simp] theorem realLineRepresentative_zero : realLineRepresentative (0 : W^{1,2}(ℝ^1)) = 0 :=
  funext fun x ↦ (realLineRepresentativeEvalCLM x).map_zero

end SobolevSpace.GraphSpace
