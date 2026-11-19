/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Evolution.TimeConvergence
public import PDE.Analysis.Evolution.Time.WeakDerivative.Euclidean
public import PDE.Spaces.Sobolev.Calculus.Slicing.OneDimensionalConstructor
import PDE.Spaces.Sobolev.GraphSpace.Norms

/-!
# Real weak H¹ trajectories in the Sobolev graph space

The real-line `L²` coordinates are transported by a measure-preserving linear
isometry to the Euclidean coordinate model. A real weak-derivative pair then
defines an element of the `WkpSpace 1 1 2`. Differentiation of the
two real `L²` trajectories gives a derivative in this graph norm.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set PDE.Analysis.Evolution
open scoped ENNReal Topology Sobolev

namespace SobolevSpace.GraphSpace

/-- Pullback from the real line to its one-dimensional Euclidean model is an
isometry on `L²`. -/
def oneDimensionalPullbackL2 :
    Lp ℝ 2 (volume : Measure ℝ) →ₗᵢ[ℝ] DerivLp 1 2 univ :=
  Lp.compMeasurePreservingₗᵢ ℝ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)) (by
    rw [domainMeasure, Measure.restrict_univ]
    exact MeasurePreserving.symm
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm.toHomeomorph.toMeasurableEquiv
      ((PiLp.volume_preserving_toLp (Fin 1)).comp
        ((volume_preserving_funUnique (Fin 1) ℝ).symm _)))

/-- Pullback of an `L²` class represented by `f` is represented by the
ordinary Euclidean pullback of `f`. -/
theorem oneDimensionalPullbackL2_toLp_ae {f : ℝ → ℝ}
    (hf : MemLp f 2 volume) :
    (oneDimensionalPullbackL2 (hf.toLp f) : ℝ^1 → ℝ)
      =ᵐ[domainMeasure 1 univ] oneDimensionalPullback f := by
  change (Lp.compMeasurePreserving _ _ (hf.toLp f) : ℝ^1 → ℝ)
    =ᵐ[domainMeasure 1 univ] oneDimensionalPullback f
  rw [Lp.toLp_compMeasurePreserving]
  exact MemLp.coeFn_toLp _

/-- The two real `L²` rows, placed in the Sobolev ambient product.
This tuple imposes no weak-derivative identity. -/
def realLineH1Jet (f g : Lp ℝ 2 (volume : Measure ℝ)) :
    WkpAmbientOn 1 1 2 univ :=
  WithLp.toLp 2 (firstOrderRows (oneDimensionalPullbackL2 f)
    (fun _ ↦ oneDimensionalPullbackL2 g))

/-- The base coordinate of the real-line tuple. -/
@[simp] theorem realLineH1Jet_base (f g : Lp ℝ 2 (volume : Measure ℝ)) :
    realLineH1Jet f g (baseIndex 1 1) = oneDimensionalPullbackL2 f :=
  firstOrderRows_baseIndex _ _

/-- The derivative coordinate of the real-line tuple. -/
@[simp] theorem realLineH1Jet_single (f g : Lp ℝ 2 (volume : Measure ℝ)) (i : Fin 1) :
    realLineH1Jet f g (singleDerivIndex 1 i) = oneDimensionalPullbackL2 g :=
  firstOrderRows_singleDerivIndex _ _ _

/-- A real weak pair satisfies the graph relations after the
measure-preserving identification with the Euclidean line. -/
theorem isWkpOn_realLineH1Jet {f g : ℝ → ℝ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (hweak : HasWeakTimeDerivativeOn univ f g) :
    IsWkpOn (realLineH1Jet (hf.toLp f) (hg.toLp g)) := by
  have hfirst : HasWeakDerivativeOn (n := 1) univ [0]
      (oneDimensionalPullback f) (oneDimensionalPullback g) :=
    hweak.to_hasWeakDerivativeOn (ContinuousLinearMap.id ℝ ℝ)
  have hbase := oneDimensionalPullbackL2_toLp_ae hf
  have hderiv := oneDimensionalPullbackL2_toLp_ae hg
  intro a
  rcases a.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
  · simp only [baseIndex_toList, realLineH1Jet_base]
    exact (hasWeakDerivativeOn_congr_ae hbase hbase).mpr
      (hasWeakDerivativeOn_nil hfirst.locallyIntegrable_f)
  · have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    simp only [singleDerivIndex_toList, realLineH1Jet_base, realLineH1Jet_single]
    exact (hasWeakDerivativeOn_congr_ae hbase hderiv).mpr hfirst

/-- Construct an element of the global `W^{1,2}` graph space from
real `L²` data and their weak-derivative identity. -/
def mkW12OfWeakDerivative {f g : ℝ → ℝ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (hweak : HasWeakTimeDerivativeOn univ f g) : W^{1,2}(ℝ^1) :=
  ⟨realLineH1Jet (hf.toLp f) (hg.toLp g), isWkpOn_realLineH1Jet hf hg hweak⟩

/-- The constructed Sobolev element has precisely the supplied two `L²` rows. -/
theorem mkW12OfWeakDerivative_val {f g : ℝ → ℝ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (hweak : HasWeakTimeDerivativeOn univ f g) :
    (mkW12OfWeakDerivative hf hg hweak).val =
      realLineH1Jet (hf.toLp f) (hg.toLp g) :=
  rfl

/-- The ambient two-row norm is bounded by the sum of the real `L²` norms. -/
theorem norm_realLineH1Jet_le (f g : Lp ℝ 2 (volume : Measure ℝ)) :
    ‖realLineH1Jet f g‖ ≤ ‖f‖ + ‖g‖ := by
  simpa using ambient_norm_le_base_add_sum_deriv (realLineH1Jet f g)

/-- The sum of the two coordinate norms equals the sum of the real `L²` norms. -/
theorem sum_norm_realLineH1Jet (f g : Lp ℝ 2 (volume : Measure ℝ)) :
    (∑ i, ‖realLineH1Jet f g i‖) = ‖f‖ + ‖g‖ := by
  rw [sum_derivIndex_one]
  simp

/-- Placing the two real `L²` rows in the Sobolev ambient product is continuous. -/
theorem continuous_realLineH1Jet :
    Continuous (fun z : Lp ℝ 2 (volume : Measure ℝ) × Lp ℝ 2 (volume : Measure ℝ) ↦
      realLineH1Jet z.1 z.2) := by
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : DerivIndex 1 1 ↦ DerivLp 1 2 univ)
  have hc : Continuous
      (fun z : Lp ℝ 2 (volume : Measure ℝ) × Lp ℝ 2 (volume : Measure ℝ) ↦
        fun a ↦ realLineH1Jet z.1 z.2 a) := by
    apply continuous_pi
    intro a
    rcases a.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
    · simp only [realLineH1Jet_base]
      exact oneDimensionalPullbackL2.continuous.comp continuous_fst
    · simp only [realLineH1Jet_single]
      exact oneDimensionalPullbackL2.continuous.comp continuous_snd
  exact e.symm.continuous.comp hc

/-- Differentiation of the two real `L²` rows differentiates each Euclidean
Sobolev coordinate, through the fixed linear isometry. -/
theorem hasDerivAt_realLineH1Jet_coordinates
    {f g : ℝ → Lp ℝ 2 (volume : Measure ℝ)}
    {f' g' : Lp ℝ 2 (volume : Measure ℝ)} {t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    ∀ a, HasDerivAt (fun s ↦ realLineH1Jet (f s) (g s) a)
      (realLineH1Jet f' g' a) t := by
  intro a
  rcases a.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
  · simp only [realLineH1Jet_base]
    exact oneDimensionalPullbackL2.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hf
  · simp only [realLineH1Jet_single]
    exact oneDimensionalPullbackL2.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hg

/-- Real weak H¹ trajectories with two `L²` time derivatives have a
Sobolev derivative with those two rows. The spatial weak-derivative
identity for the velocity is proved by closedness, not assumed. -/
theorem exists_hasDerivAt_mkW12OfWeakDerivative
    {f g : ℝ → ℝ → ℝ} (hf : ∀ t, MemLp (f t) 2 volume)
    (hg : ∀ t, MemLp (g t) 2 volume)
    (hweak : ∀ t, HasWeakTimeDerivativeOn univ (f t) (g t))
    {f' g' : Lp ℝ 2 (volume : Measure ℝ)} {t : ℝ}
    (hf' : HasDerivAt (fun s ↦ (hf s).toLp (f s)) f' t)
    (hg' : HasDerivAt (fun s ↦ (hg s).toLp (g s)) g' t) :
    ∃ V : W^{1,2}(ℝ^1),
      V.val = realLineH1Jet f' g' ∧
        HasDerivAt (fun s ↦ mkW12OfWeakDerivative (hf s) (hg s) (hweak s)) V t := by
  apply WkpSpaceOn.exists_hasDerivAt_of_coordinates
  exact hasDerivAt_realLineH1Jet_coordinates hf' hg'

/-- Exponentially decaying real `L²` time derivatives of a weak H¹ trajectory
give convergence in the Sobolev norm, with an explicit rate. -/
theorem exists_limit_mkW12OfWeakDerivative_of_norm_le_exp
    {f g : ℝ → ℝ → ℝ} (hf : ∀ t, MemLp (f t) 2 volume)
    (hg : ∀ t, MemLp (g t) 2 volume)
    (hweak : ∀ t, HasWeakTimeDerivativeOn univ (f t) (g t))
    {F G : ℝ → Lp ℝ 2 (volume : Measure ℝ)} {a C γ : ℝ} (hγ : 0 < γ)
    (hF : ∀ t ∈ Ici a, HasDerivAt (fun s ↦ (hf s).toLp (f s)) (F t) t)
    (hG : ∀ t ∈ Ici a, HasDerivAt (fun s ↦ (hg s).toLp (g s)) (G t) t)
    (hFm : AEStronglyMeasurable F (volume.restrict (Ioi a)))
    (hGm : AEStronglyMeasurable G (volume.restrict (Ioi a)))
    (hbound : ∀ t ∈ Ioi a, ‖F t‖ + ‖G t‖ ≤ C * Real.exp (-γ * t)) :
    ∃ limit : W^{1,2}(ℝ^1),
      Tendsto (fun t ↦ mkW12OfWeakDerivative (hf t) (hg t) (hweak t))
        atTop (𝓝 limit) ∧
      ∀ t ∈ Ici a, ‖limit - mkW12OfWeakDerivative (hf t) (hg t) (hweak t)‖ ≤
        C * Real.exp (-γ * t) / γ := by
  apply WkpSpaceOn.exists_limit_of_coordinate_deriv_norm_le_exp
    (v := fun t ↦ realLineH1Jet (F t) (G t)) hγ
  · intro t ht
    exact hasDerivAt_realLineH1Jet_coordinates (hF t ht) (hG t ht)
  · exact continuous_realLineH1Jet.comp_aestronglyMeasurable (hFm.prodMk hGm)
  · intro t ht
    simpa only [sum_norm_realLineH1Jet] using hbound t ht

end SobolevSpace.GraphSpace
