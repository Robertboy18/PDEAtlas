/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Operators
public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Scalar

/-!
# Reconstructing Sobolev vector fields from scalar components

A finite family of scalar Sobolev functions determines a Euclidean-valued Sobolev function.
Each scalar component is mapped into its coordinate line and the resulting fields are added
in the original vector Sobolev graph. This retains every derivative coordinate and uses the
vector graph norm, for both normed exponent endpoints and also for zero-dimensional
source or target.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal Sobolev

namespace SobolevSpace.VectorValued

open GraphSpace

variable {n m k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens ℝ^n}

/-- Select one scalar component of a Euclidean-valued Sobolev function. -/
def componentCLM (i : Fin m) : W^{k,p}(Ω; ℝ^m) →L[ℝ] W^{k,p}(Ω) :=
  scalarEquiv.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (mapCLM (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m ↦ ℝ) i))

/-- Component extraction preserves the corresponding representatives of every derivative. -/
theorem componentCLM_apply_ae (i : Fin m) (u : W^{k,p}(Ω; ℝ^m))
    (a : DerivIndex n k) :
    ((componentCLM i u).val a : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      fun x ↦ u.val a x i :=
  mapCLM_apply_ae _ u a

/-- Selecting a scalar component does not increase the Sobolev norm. -/
theorem norm_componentCLM_apply_le (i : Fin m) (u : W^{k,p}(Ω; ℝ^m)) :
    ‖componentCLM i u‖ ≤ ‖u‖ := by
  have hproj : ‖PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m ↦ ℝ) i‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    simpa only [PiLp.proj_apply, one_mul] using PiLp.norm_apply_le v i
  change ‖scalarEquiv (mapCLM _ u)‖ ≤ ‖u‖
  rw [scalarEquiv.norm_map]
  exact (norm_mapCLM_apply_le _ u).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hproj (norm_nonneg u))

/-- Assemble scalar Sobolev components into a Euclidean-valued Sobolev function.
The scalar family is unrestricted; no component has to vanish on the boundary. -/
def ofComponentsCLM : (Fin m → W^{k,p}(Ω)) →L[ℝ] W^{k,p}(Ω; ℝ^m) :=
  ∑ i : Fin m,
    (mapCLM (ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single i (1 : ℝ)))).comp
      (scalarEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (ContinuousLinearMap.proj i))

/-- Every derivative row of the assembled field is the vector of scalar derivative rows. -/
theorem ofComponentsCLM_coordinate_ae (Q : Fin m → W^{k,p}(Ω))
    (a : DerivIndex n k) :
    ((ofComponentsCLM Q).val a : ℝ^n → ℝ^m) =ᵐ[domainMeasure n Ω]
      fun x ↦ WithLp.toLp 2 (fun i ↦ (Q i).val a x) := by
  let L (i : Fin m) : ℝ →L[ℝ] ℝ^m :=
    ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single i (1 : ℝ))
  let U (i : Fin m) : W^{k,p}(Ω; ℝ^m) := mapCLM (L i) (scalarEquiv.symm (Q i))
  have hsum : ofComponentsCLM Q = ∑ i, U i := by
    simp only [ofComponentsCLM, sum_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, U, L]
    rfl
  change (coordinateCLM a (ofComponentsCLM Q) : ℝ^n → ℝ^m) =ᵐ[domainMeasure n Ω] _
  rw [hsum, map_sum]
  have hrows := ae_all_iff.mpr fun i : Fin m ↦
    mapCLM_apply_ae (L i) (scalarEquiv.symm (Q i)) a
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i ↦ coordinateCLM a (U i)),
    hrows] with x hx hrow
  rw [hx]
  change (∑ i, (U i).val a x) = _
  simp_rw [show ∀ i, (U i).val a x = L i ((Q i).val a x) from hrow]
  ext j
  simp [L, EuclideanSpace.single, Pi.single_apply]

/-- Extracting a component after assembly recovers the original scalar Sobolev function. -/
@[simp] theorem componentCLM_ofComponentsCLM (Q : Fin m → W^{k,p}(Ω)) (i : Fin m) :
    componentCLM i (ofComponentsCLM Q) = Q i := by
  apply scalarEquiv.symm.injective
  apply WkpSpaceOn.ext_of_base_ae
  exact (componentCLM_apply_ae i (ofComponentsCLM Q) (baseIndex n k)).trans
    ((ofComponentsCLM_coordinate_ae Q (baseIndex n k)).fun_comp (fun v : ℝ^m ↦ v i))

/-- Reassembling all scalar components recovers the original vector Sobolev function. -/
@[simp] theorem ofComponentsCLM_componentCLM (U : W^{k,p}(Ω; ℝ^m)) :
    ofComponentsCLM (fun i ↦ componentCLM i U) = U := by
  apply WkpSpaceOn.ext_of_base_ae
  have hcomponents := ae_all_iff.mpr fun i : Fin m ↦
    componentCLM_apply_ae i U (baseIndex n k)
  filter_upwards [ofComponentsCLM_coordinate_ae (fun i ↦ componentCLM i U) (baseIndex n k),
    hcomponents] with x hx hi
  exact hx.trans (PiLp.ext fun i ↦ hi i)

/-- Assembly is bounded by the sum of the component norms in the original Sobolev graph. -/
theorem norm_ofComponentsCLM_le (Q : Fin m → W^{k,p}(Ω)) :
    ‖ofComponentsCLM Q‖ ≤ ∑ i, ‖Q i‖ := by
  have hsum : ofComponentsCLM Q =
      ∑ i : Fin m, mapCLM (ContinuousLinearMap.toSpanSingleton ℝ
        (EuclideanSpace.single i (1 : ℝ))) (scalarEquiv.symm (Q i)) := by
    simp only [ofComponentsCLM, sum_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply]
    rfl
  rw [hsum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  calc
    _ ≤ ‖ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single i (1 : ℝ))‖ *
        ‖scalarEquiv.symm (Q i)‖ := norm_mapCLM_apply_le _ _
    _ = ‖Q i‖ := by
      rw [ContinuousLinearMap.norm_toSpanSingleton, scalarEquiv.symm.norm_map]
      simp

/-- Euclidean-valued Sobolev functions and their unrestricted scalar components are
continuously linearly equivalent. The scalar family has its usual maximum norm, and the
equivalence need not be an isometry. -/
def componentsEquiv : W^{k,p}(Ω; ℝ^m) ≃L[ℝ] (Fin m → W^{k,p}(Ω)) where
  toFun U i := componentCLM i U
  invFun := ofComponentsCLM
  left_inv := ofComponentsCLM_componentCLM
  right_inv Q := funext (componentCLM_ofComponentsCLM Q)
  map_add' U V := funext fun i ↦ (componentCLM i).map_add U V
  map_smul' c U := funext fun i ↦ (componentCLM i).map_smul c U
  continuous_toFun := continuous_pi fun i ↦ (componentCLM i).continuous
  continuous_invFun := ofComponentsCLM.continuous

end SobolevSpace.VectorValued
