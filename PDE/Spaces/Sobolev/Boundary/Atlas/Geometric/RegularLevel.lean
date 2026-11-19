/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Atlas.Geometric.GraphBoundary
public import PDE.Analysis.Calculus.ImplicitFunction.Superlevel

/-!
# Graph boundaries from regular levels

A regular defining function supplies both a smooth graph and its local side.
Permuting and, when necessary, reversing Euclidean coordinates makes a nonzero
partial derivative positive. The implicit graph is smooth on one open neighborhood,
also when the requested order is infinite.
-/

@[expose] public section

open Filter Set
open scoped Topology ContDiff
open SobolevSpace.Trace.HalfSpace

namespace SobolevSpace.Boundary

private theorem exists_positive_normal_coordinates {n : ℕ}
    (ℓ : ℝ^(n + 1) →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) :
    ∃ e : ℝ^(n + 1) ≃L[ℝ] (ℝ^n × ℝ), 0 < ℓ (e.symm (0, 1)) := by
  classical
  obtain ⟨j, hj⟩ : ∃ j : Fin (n + 1), ℓ (EuclideanSpace.single j 1) ≠ 0 := by
    by_contra! h
    apply hℓ
    have hz : ℓ.toLinearMap = 0 :=
      (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis.ext fun j ↦ by
        simpa only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
          ContinuousLinearMap.coe_coe, LinearMap.zero_apply] using h j
    apply ContinuousLinearMap.ext
    intro x
    exact LinearMap.congr_fun hz x
  let P := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap j (Fin.last n))
  let e := P.toContinuousLinearEquiv.trans tangentialNormalContinuousLinearEquiv
  have haxis : e.symm (0, 1) = EuclideanSpace.single j 1 := by
    have hlast : joinTangentialNormal (0, 1) =
        EuclideanSpace.single (Fin.last n) 1 := by
      ext i
      refine Fin.lastCases ?_ (fun k ↦ ?_) i <;> simp
    change P.symm (joinTangentialNormal (0, 1)) = _
    rw [hlast]
    simp [P]
  by_cases hpos : 0 < ℓ (EuclideanSpace.single j 1)
  · exact ⟨e, haxis ▸ hpos⟩
  · refine ⟨(LinearIsometryEquiv.neg ℝ : ℝ^(n + 1) ≃ₗᵢ[ℝ] ℝ^(n + 1)
      ).toContinuousLinearEquiv.trans e, ?_⟩
    change 0 < ℓ (-e.symm (0, 1))
    rw [map_neg, haxis]
    exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hpos) hj)

/-- A smooth regular defining function gives the graph-boundary predicate,
with the strict superlevel side and one open tangential neighborhood. -/
theorem hasContDiffGraphBoundary_of_regular_level
    {n : ℕ} [Fact (0 < n)] {m : ℕ∞}
    {Ω U : Set (ℝ^n)} {f : ℝ^n → ℝ} {c : ℝ}
    (hf : ContDiffOn ℝ m f U) (hU : IsOpen U) (hm : 1 ≤ m)
    (hfront : ∀ x ∈ frontier Ω, x ∈ U ∧ f x = c)
    (hregular : ∀ x ∈ frontier Ω, fderiv ℝ f x ≠ 0)
    (hside : ∀ x ∈ U, x ∈ Ω ↔ c < f x) :
    HasContDiffGraphBoundary m Ω := by
  cases n with
  | zero => exact False.elim (Nat.lt_irrefl 0 (Fact.out : 0 < 0))
  | succ n =>
    intro x hx
    obtain ⟨hxU, hlevel⟩ := hfront x hx
    obtain ⟨e, he⟩ := exists_positive_normal_coordinates (fderiv ℝ f x) (hregular x hx)
    let F : ℝ^n × ℝ → ℝ := fun y ↦ f (e.symm y)
    let T := e.symm ⁻¹' U
    have hT : IsOpen T := hU.preimage e.symm.continuous
    have hex : e x ∈ T := by simpa only [T, mem_preimage, e.symm_apply_apply] using hxU
    have hF : ContDiffOn ℝ m F T :=
      hf.comp e.symm.contDiff.contDiffOn (fun _ hy ↦ hy)
    have hpartial : 0 < fderiv ℝ F (e x) (0, 1) := by
      have hd := ((hf.contDiffAt (hU.mem_nhds hxU)).of_le
        (show (1 : ℕ∞ω) ≤ m by exact_mod_cast hm)).differentiableAt one_ne_zero
      have hdf : HasFDerivAt F
          ((fderiv ℝ f x).comp e.symm.toContinuousLinearMap) (e x) := by
        have hd' : HasFDerivAt f (fderiv ℝ f x) (e.symm (e x)) := by
          simpa only [e.symm_apply_apply] using hd.hasFDerivAt
        simpa only [Function.comp_def, e.symm_apply_apply] using
          hd'.comp (e x) e.symm.hasFDerivAt
      rw [hdf.fderiv]
      exact he
    obtain ⟨g, s, hs, hxs, hg, hgx, hlocal⟩ :=
      hF.exists_implicit_superlevel_graph hT hm hex hpartial
    refine ⟨e, g, s, hs, hxs, hg, hgx.symm, ?_⟩
    filter_upwards [e.continuous.continuousAt hlocal, hU.mem_nhds hxU] with y hy hyU
    change F (e x) < F (e y) ↔ g (e y).1 < (e y).2 at hy
    simpa only [F, e.symm_apply_apply, hlevel, ← hside y hyU] using hy

end SobolevSpace.Boundary
