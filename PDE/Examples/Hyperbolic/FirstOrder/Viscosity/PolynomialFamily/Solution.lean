/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Examples.Hyperbolic.FirstOrder.Viscosity.PolynomialFamily
public import PDE.Parabolic.Systems.Transport.Solution
import PDE.Spaces.Sobolev.GraphSpace.Operators.BaseInjectivity
import CAS.ExactTactic

/-!
# A polynomial transport–diffusion solution

The curve `u(t,x) = t*q(x)` has forcing `q - ε*t*Δq` and zero initial data. As a curve
in `W^{3,2}` with weak time derivative `q` in `W^{1,2}`, it is a strong solution of the
transport–diffusion system with zero transport
(`isStrongTransportDiffusionSolution_vectorState`).
-/

@[expose] public noncomputable section

namespace PDE.Examples.Hyperbolic.Viscosity.PolynomialFamily

open MeasureTheory Set TopologicalSpace PDE.Common
open PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Distributions Sobolev

attribute [local instance] profileNormedAddCommGroup profileNormedSpace

/-- The order restriction `W^{3,2} → W^{1,2}` maps `profile 3` to `profile 1`. -/
theorem lowerOrder_profile :
    lowerOrderCLM (by decide : 1 ≤ 3) (profile 3) = profile 1 := by
  apply wkpBaseCoordinateCLM_injective isOpen_univ
  apply Lp.ext
  simpa only [wkpBaseCoordinateCLM_apply, lowerOrderCLM_apply,
    DerivIndex.castOrder_baseIndex, profile] using
    (globalTestFunctionToWkpOn_coordinate_ae (k := 3) (p := 2) (Ω := univ)
      spatialTest (baseIndex 1 3)).trans
      (globalTestFunctionToWkpOn_coordinate_ae (k := 1) (p := 2) (Ω := univ)
        spatialTest (baseIndex 1 1)).symm

/-- The one-component profile. -/
def vectorProfile (k : ℕ) : PiLp 2 (fun _ : Fin 1 ↦ W^{k,2}(ℝ^1)) :=
  WithLp.toLp 2 fun _ ↦ profile k

/-- The one-component state curve `t ↦ t q`. -/
def vectorState (k : ℕ) (t : ℝ) : PiLp 2 (fun _ : Fin 1 ↦ W^{k,2}(ℝ^1)) :=
  t • vectorProfile k

/-- The state belongs to the required Bochner space on every finite interval. -/
theorem vectorState_memLp (k : ℕ) (T : ℝ) :
    MemLp (vectorState k) 2 (volume.restrict (Ioc 0 T)) :=
  memLp_restrict_Ioc_of_continuousOn (by unfold vectorState; fun_prop)

/-- The state as an element of `L²(0, T; H³)`. -/
def strongState (T : ℝ) :
    Lp (PiLp 2 (fun _ : Fin 1 ↦ W^{3,2}(ℝ^1))) 2 (volume.restrict (Ioc 0 T)) :=
  (vectorState_memLp 3 T).toLp _

/-- Its constant time derivative `q`, in `L²(0, T; H¹)`. -/
def strongVelocity (T : ℝ) :
    Lp (PiLp 2 (fun _ : Fin 1 ↦ W^{1,2}(ℝ^1))) 2 (volume.restrict (Ioc 0 T)) :=
  (memLp_const (vectorProfile 1)).toLp _

/-- Order restriction maps the `H³` state to the `H¹` state. -/
theorem vectorState_lowerOrder (t : ℝ) :
    ContinuousLinearMap.piLpMap 2
      (fun _ : Fin 1 ↦ lowerOrderCLM (by decide : 1 ≤ 3)) (vectorState 3 t) =
        vectorState 1 t := by
  apply PiLp.ext
  intro p
  change lowerOrderCLM (by decide : 1 ≤ 3) (t • profile 3) = t • profile 1
  rw [map_smul, lowerOrder_profile]

/-- The `H¹` state curve has strong time derivative `q`. -/
theorem vectorState_hasDerivAt (t : ℝ) :
    HasDerivAt (vectorState 1) (vectorProfile 1) t := by
  convert! (hasDerivAt_id t).smul_const (vectorProfile 1) using 1
  simp

/-- The polynomial curve is a strong solution with zero transport, zero initial data and
forcing `q - ε t Δq`. -/
theorem isStrongTransportDiffusionSolution_vectorState (T ε : ℝ) :
    PDE.Parabolic.Systems.IsStrongTransportDiffusionSolution ε 0 T
      (fun _ _ _ _ ↦ 0) (fun _ y ↦ forcing ε y.1 y.2) 0
      (strongState T) (strongVelocity T) (vectorState 1) := by
  have hU := (vectorState_memLp 3 T).coeFn_toLp
  have hG := (memLp_const (μ := volume.restrict (Ioc 0 T))
    (p := (2 : ℝ≥0∞)) (vectorProfile 1)).coeFn_toLp
  have hr : vectorState 1 =ᵐ[volume.restrict (Ioc 0 T)] fun t ↦
      ContinuousLinearMap.piLpMap 2
        (fun _ : Fin 1 ↦ lowerOrderCLM (by decide : 1 ≤ 3)) (strongState T t) := by
    filter_upwards [hU] with t ht
    rw [show strongState T t = vectorState 3 t from ht, vectorState_lowerOrder]
  refine ⟨by unfold vectorState; fun_prop, by simp [vectorState], hr, ?_, ?_⟩
  · have hd := hasWeakTimeDerivativeOn_of_continuousOn_hasDerivAt
      (a := 0) (b := T) (by unfold vectorState; fun_prop)
      (continuousOn_const : ContinuousOn (fun _ ↦ vectorProfile 1) (Icc 0 T))
      (fun t _ ↦ vectorState_hasDerivAt t)
    exact hd.congr_ae_restrict measurableSet_Ioo
      (hr.filter_mono (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self)))
      (hG.symm.filter_mono (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self)))
  · filter_upwards [hU, hG] with t ht hgt
    have hbase := globalTestFunctionToWkpOn_coordinate_ae (k := 1) (p := 2) (Ω := univ)
      spatialTest (baseIndex 1 1)
    have hsecond := globalTestFunctionToWkpOn_coordinate_ae (k := 3) (p := 2) (Ω := univ)
      spatialTest ((pairDerivIndex 1 0 0).castOrder (by decide : 2 ≤ 3))
    simp only [domainMeasure, Measure.restrict_univ, TestFunction.toFun_eq_coe,
      ← wkpCoordinateCLM_apply] at hbase hsecond
    rw [← profile] at hbase hsecond
    have hlist : (pairDerivIndex 1 0 0).toList = [0, 0] := by
      apply (List.perm_replicate (n := 2) (a := (0 : Fin 1))).mp
      simpa using pairDerivIndex_toList_perm (0 : Fin 1) 0
    have hsmul := Lp.coeFn_smul t
      (wkpCoordinateCLM ((pairDerivIndex 1 0 0).castOrder (by decide : 2 ≤ 3))
        (profile 3))
    simp only [domainMeasure, Measure.restrict_univ] at hsmul
    filter_upwards [hbase, hsecond, hsmul] with x hx hd hs
    intro p
    rw [show strongState T t = vectorState 3 t from ht,
      show strongVelocity T t = vectorProfile 1 from hgt]
    simp only [zero_mul, Finset.sum_const_zero, add_zero, Fin.sum_univ_one]
    change wkpBaseCoordinateCLM (profile 1) x -
      ε * wkpCoordinateCLM
        ((pairDerivIndex 1 0 0).castOrder (by decide : 2 ≤ 3)) (t • profile 3) x = _
    rw [map_smul]
    rw [hs, show wkpBaseCoordinateCLM (profile 1) x = spatialTest x from
      by simpa only [wkpBaseCoordinateCLM, baseIndex_toList, iteratedPartialDeriv] using hx]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hd]
    simp only [DerivIndex.castOrder_toList, hlist, iteratedPartialDeriv,
      forcing, laplacian, Fin.sum_univ_one]
    cas

end PDE.Examples.Hyperbolic.Viscosity.PolynomialFamily
