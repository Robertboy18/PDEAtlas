/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.Primitive
public import PDE.Analysis.Fourier.HilbertTransform.RealL2
public import PDE.Analysis.Evolution.ODE.GlobalCharacteristics
public import PDE.Analysis.Fourier.HilbertTransform.RealPair.Sobolev.ContinuousRepresentative
public import PDE.Spaces.Sobolev.GraphSpace.RealLine.Representative
public import PDE.Spaces.Sobolev.GraphSpace.Topology.SupportedBall
import Mathlib.Analysis.ODE.ExistUnique
import CAS.ExactTactic

/-!
# Characteristics driven by the complete H² iteration class

An L²-continuous curve in the bounded H² class determines a normalized
Hilbert velocity. The weak H¹ coordinates give a spatial Lipschitz constant
depending only on the graph bound. Continuity in time follows from the L²
continuity of interval integration.

The finite-interval ODE construction therefore gives the position flow on the
whole interval `[0, T]`. The vorticity transported along this flow is constructed
in `Iteration.Transport`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PDE.Analysis PDE.Analysis.Evolution
open scoped Topology Sobolev

open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

private theorem ae_norm_hilbert_of_hkBaseBall {f : DerivLp 1 2 univ} {B : ℝ}
    (hf : f ∈ hkBaseBall 1 2 univ B) :
    ∀ᵐ x ∂volume, ‖realHilbertTransformL2 (oneDimensionalPushforwardL2 f) x‖ ≤ 2 * B := by
  obtain ⟨U, hU, hbase⟩ := hf
  let V : W^{1,2}((Set.univ : Set (ℝ^1))) := lowerOrderCLM (by decide : 1 ≤ 2) U
  have hV : ‖V‖ ≤ B := (norm_lowerOrderCLM_apply_le _ U).trans hU
  have hb : realLineCoordinateCLM (baseIndex 1 1) V = oneDimensionalPushforwardL2 f := by
    apply congrArg oneDimensionalPushforwardL2
    change (V : WkpAmbientOn 1 1 2 univ) (baseIndex 1 1) = f
    simpa only [V, lowerOrderCLM_apply, DerivIndex.castOrder_baseIndex,
      wkpBaseCoordinateCLM_apply] using hbase
  have hweak := hasWeakTimeDerivativeOn_realLineCoordinates V
  rw [hb] at hweak
  have hbound := (isHilbertPair_realHilbertTransformL2
    (oneDimensionalPushforwardL2 f)).ae_norm_le_eLpNorm_add_weakDerivative
      (Lp.memLp (realLineCoordinateCLM (singleDerivIndex 1 0) V)) hweak
  filter_upwards [hbound] with x hx
  simp only [← Lp.norm_def] at hx
  have h₀ := (norm_realLineCoordinateCLM_le (baseIndex 1 1) V).trans hV
  rw [hb] at h₀
  have h₁ := (norm_realLineCoordinateCLM_le (singleDerivIndex 1 0) V).trans hV
  have hBB : B + B = 2 * B := by cas
  exact hx.trans ((add_le_add h₀ h₁).trans_eq hBB)

/-- The normalized spectral Hilbert velocity of a curve in the complete
bounded H² class. Time is clamped to the given interval. -/
def hkCurveHilbertVelocity {A : Set (ℝ^1)} {B : NNReal} {T : ℝ} (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, supportedHkBaseBall 1 2 univ A B)) (x t : ℝ) : ℝ :=
  l2Primitive (realHilbertTransformL2
    (oneDimensionalPushforwardL2 (f (projIcc 0 T hT t)).val)) x

/-- The velocity's spatial Lipschitz constant follows from the two weak H¹
coordinates and the Hilbert Sobolev estimate. -/
theorem lipschitzWith_hkCurveHilbertVelocity
    {A : Set (ℝ^1)} {B : NNReal} {T : ℝ} (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, supportedHkBaseBall 1 2 univ A B)) (t : ℝ) :
    LipschitzWith (2 * B) (fun x ↦ hkCurveHilbertVelocity hT f x t) := by
  apply lipschitzWith_l2Primitive_of_ae_bound
  exact ae_norm_hilbert_of_hkBaseBall (f (projIcc 0 T hT t)).property.1

/-- L² continuity of the input curve in time gives joint continuity of the
normalized velocity. -/
theorem continuous_hkCurveHilbertVelocity
    {A : Set (ℝ^1)} {B : NNReal} {T : ℝ} (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, supportedHkBaseBall 1 2 univ A B)) :
    Continuous (Function.uncurry (hkCurveHilbertVelocity hT f)) := by
  apply continuous_prod_of_continuous_lipschitzWith _ (2 * B)
  · intro x
    exact (continuous_l2Primitive_apply x).comp
      (realHilbertTransformL2.continuous.comp
        (oneDimensionalPushforwardL2.continuous.comp
          (continuous_subtype_val.comp (f.continuous.comp continuous_projIcc))))
  · exact lipschitzWith_hkCurveHilbertVelocity hT f

/-- Every curve in the complete H² class generates a position flow on the
entire prescribed interval. Grönwall gives dependence on the initial label
and the explicit enclosure `|X(x,t)| ≤ |x| exp(2 B t)`, which depends only on `B`.

The flow is jointly continuous for labels and times in the interval and
unique there among classical paths. -/
theorem exists_hkCurve_hilbert_flow
    {A : Set (ℝ^1)} {B : NNReal} {T : ℝ} (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, supportedHkBaseBall 1 2 univ A B)) :
    ∃ X : ℝ → ℝ → ℝ,
      (∀ x, Continuous (X x)) ∧
      (∀ x, X x 0 = x) ∧
      (∀ x t, t ∈ Icc (0 : ℝ) T →
        HasDerivAt (X x) (hkCurveHilbertVelocity hT f (X x t) t) t) ∧
      (∀ x y t, t ∈ Icc (0 : ℝ) T →
        dist (X x t) (X y t) ≤ dist x y * Real.exp (2 * (B : ℝ) * t)) ∧
      (∀ x t, t ∈ Icc (0 : ℝ) T →
        |X x t| ≤ |x| * Real.exp (2 * (B : ℝ) * t)) ∧
      Continuous (fun p : ℝ × Icc (0 : ℝ) T ↦ X p.1 p.2) ∧
      (∀ x (q : ℝ → ℝ), ContinuousOn q (Icc (0 : ℝ) T) →
        (∀ t ∈ Icc (0 : ℝ) T,
          HasDerivAt q (hkCurveHilbertVelocity hT f (q t) t) t) →
        q 0 = x → EqOn q (X x) (Icc (0 : ℝ) T)) := by
  have hcont := continuous_hkCurveHilbertVelocity hT f
  have hLip := lipschitzWith_hkCurveHilbertVelocity hT f
  have hex (x : ℝ) := exists_characteristic_Icc hT
    (hkCurveHilbertVelocity hT f) hcont (2 * B) (fun t _ ↦ hLip t) x
  choose X hX hX₀ hX' using hex
  have hdist (x y t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      dist (X x t) (X y t) ≤ dist x y * Real.exp (2 * (B : ℝ) * t) := by
    have h := dist_le_of_trajectories_ODE
      (v := fun t x ↦ hkCurveHilbertVelocity hT f x t) hLip
      (hX x).continuousOn
      (fun t ht ↦ (hX' x t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
      (hX y).continuousOn
      (fun t ht ↦ (hX' y t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
      (by simp only [hX₀]; exact le_rfl) t ht
    simpa only [NNReal.coe_mul, NNReal.coe_ofNat, sub_zero] using h
  have hzero (t : ℝ) : hkCurveHilbertVelocity hT f 0 t = 0 := by
    simp only [hkCurveHilbertVelocity, l2Primitive, intervalIntegral.integral_same]
  have hnorm (x t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      |X x t| ≤ |x| * Real.exp (2 * (B : ℝ) * t) := by
    have h := dist_le_of_trajectories_ODE
      (v := fun t x ↦ hkCurveHilbertVelocity hT f x t) hLip
      (hX x).continuousOn
      (fun t ht ↦ (hX' x t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
      (g := fun _ ↦ 0) continuousOn_const
      (fun t _ ↦ by simpa only [hzero] using (hasDerivAt_const t (0 : ℝ)).hasDerivWithinAt)
      (δ := |x|) (by simp only [hX₀, Real.dist_eq, sub_zero]; exact le_rfl) t ht
    simpa only [Real.dist_eq, sub_zero, NNReal.coe_mul, NNReal.coe_ofNat] using h
  refine ⟨X, hX, hX₀, hX', hdist, hnorm, ?_, ?_⟩
  · apply continuous_prod_of_continuous_lipschitzWith _
      ⟨Real.exp (2 * (B : ℝ) * T), (Real.exp_pos _).le⟩
    · intro x
      exact (hX x).comp continuous_subtype_val
    · intro t
      apply LipschitzWith.of_dist_le_mul
      intro x y
      calc
        dist (X x t) (X y t) ≤ dist x y * Real.exp (2 * (B : ℝ) * t) :=
          hdist x y t t.property
        _ ≤ Real.exp (2 * (B : ℝ) * T) * dist x y := by
          rw [mul_comm]
          gcongr
          exact t.property.2
  · intro x q hq hq' hq₀
    exact ODE_solution_unique_of_mem_Icc_right
      (v := fun t x ↦ hkCurveHilbertVelocity hT f x t) (s := fun _ ↦ univ)
      (fun t _ ↦ (hLip t).lipschitzOnWith) hq
      (fun t ht ↦ (hq' t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
      (fun _ _ ↦ mem_univ _) (hX x).continuousOn
      (fun t ht ↦ (hX' x t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
      (fun _ _ ↦ mem_univ _) (hq₀.trans (hX₀ x).symm)

end DeGregorio.Iteration
