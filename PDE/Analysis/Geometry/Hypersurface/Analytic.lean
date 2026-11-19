/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import PDE.Analysis.Geometry.Hypersurface.Conormal
public import PDE.Common.Euclidean

/-!
# Analytic charts for regular scalar levels

A regular level is flattened by replacing one original coordinate with its
defining function. This keeps the coordinate labels explicit when transporting
mixed partials and normal Cauchy data.
-/

@[expose] public noncomputable section

open scoped Gradient

open Filter
open scoped Topology ContDiff

namespace PDE.Analysis.Hypersurface

variable {n : ℕ}

/-- Replace coordinate `i` by the value of the defining function, centering the
remaining coordinates at `p`. -/
def levelCoordinates (φ : ℝ^n → ℝ) (p : ℝ^n) (i : Fin n) (x : ℝ^n) : ℝ^n :=
  x - p + (φ x - (x - p) i) • EuclideanSpace.basisFun (Fin n) ℝ i

/-- The distinguished coordinate is exactly the defining function. -/
@[simp]
theorem levelCoordinates_apply_self (φ : ℝ^n → ℝ) (p : ℝ^n) (i : Fin n) (x : ℝ^n) :
    levelCoordinates φ p i x i = φ x := by
  simp [levelCoordinates]

/-- A zero of the defining function maps to the origin. -/
theorem levelCoordinates_base {φ : ℝ^n → ℝ} {p : ℝ^n} (hφ : φ p = 0) (i : Fin n) :
    levelCoordinates φ p i p = 0 := by
  simp [levelCoordinates, hφ]

/-- The derivative of coordinate replacement is an isomorphism when the
replaced coordinate detects the defining covector. -/
def levelCoordinateEquiv (ℓ : ℝ^n →L[ℝ] ℝ) (i : Fin n)
    (hi : ℓ (EuclideanSpace.basisFun (Fin n) ℝ i) ≠ 0) : ℝ^n ≃L[ℝ] ℝ^n :=
  let e := EuclideanSpace.basisFun (Fin n) ℝ i
  let A : ℝ^n →L[ℝ] ℝ^n :=
    ContinuousLinearMap.id ℝ _ + (ℓ - EuclideanSpace.proj i).smulRight e
  let B : ℝ^n →L[ℝ] ℝ^n :=
    ContinuousLinearMap.id ℝ _ +
      ((ℓ e)⁻¹ • (EuclideanSpace.proj i - ℓ)).smulRight e
  have he : ℓ e ≠ 0 := hi
  ContinuousLinearEquiv.equivOfInverse A B (by
    intro x
    change x + (ℓ x - x i) • e +
      ((ℓ e)⁻¹ * ((x + (ℓ x - x i) • e) i -
        ℓ (x + (ℓ x - x i) • e))) • e = x
    have hei : e i = 1 := by simp [e]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hei, mul_one, map_add,
      map_smul]
    rw [add_assoc, ← add_smul]
    have hz : ℓ x - x i +
        (ℓ e)⁻¹ * (x i + (ℓ x - x i) - (ℓ x + (ℓ x - x i) * ℓ e)) = 0 := by
      field_simp [he]
      ring
    rw [hz, zero_smul, add_zero]) (by
    intro x
    change x + ((ℓ e)⁻¹ * (x i - ℓ x)) • e +
      (ℓ (x + ((ℓ e)⁻¹ * (x i - ℓ x)) • e) -
        (x + ((ℓ e)⁻¹ * (x i - ℓ x)) • e) i) • e = x
    have hei : e i = 1 := by simp [e]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hei, mul_one, map_add,
      map_smul]
    rw [add_assoc, ← add_smul]
    have hz : (ℓ e)⁻¹ * (x i - ℓ x) +
        (ℓ x + (ℓ e)⁻¹ * (x i - ℓ x) * ℓ e -
          (x i + (ℓ e)⁻¹ * (x i - ℓ x))) = 0 := by
      field_simp [he]
      ring
    rw [hz, zero_smul, add_zero])

/-- The coordinate isomorphism acts by the same replacement as the chart's
linearization. -/
theorem levelCoordinateEquiv_apply (ℓ : ℝ^n →L[ℝ] ℝ) (i : Fin n)
    (hi : ℓ (EuclideanSpace.basisFun (Fin n) ℝ i) ≠ 0) (x : ℝ^n) :
    levelCoordinateEquiv ℓ i hi x =
      x + (ℓ x - x i) • EuclideanSpace.basisFun (Fin n) ℝ i := rfl

/-- Analyticity of the coordinate replacement is inherited from the defining
function. -/
theorem analyticAt_levelCoordinates {φ : ℝ^n → ℝ} {p : ℝ^n}
    (hφ : AnalyticAt ℝ φ p) (i : Fin n) :
    AnalyticAt ℝ (levelCoordinates φ p i) p := by
  have hsub : AnalyticAt ℝ (fun x : ℝ^n ↦ x - p) p :=
    analyticAt_id.sub analyticAt_const
  exact hsub.add ((hφ.sub (((EuclideanSpace.proj i).analyticAt (p - p)).comp
    (f := fun x : ℝ^n ↦ x - p)
    hsub)).smul analyticAt_const)

/-- The strict derivative of the level chart. -/
theorem hasStrictFDerivAt_levelCoordinates {φ : ℝ^n → ℝ} {p : ℝ^n}
    (hφ : AnalyticAt ℝ φ p) (i : Fin n)
    (hi : fderiv ℝ φ p (EuclideanSpace.basisFun (Fin n) ℝ i) ≠ 0) :
    HasStrictFDerivAt (levelCoordinates φ p i)
      (levelCoordinateEquiv (fderiv ℝ φ p) i hi : ℝ^n →L[ℝ] ℝ^n) p := by
  have hsub := (hasStrictFDerivAt_id (𝕜 := ℝ) p).sub_const p
  have hp := (EuclideanSpace.proj i).hasStrictFDerivAt.comp p hsub
  convert! hsub.add ((hφ.hasStrictFDerivAt.sub hp).smul_const
    (EuclideanSpace.basisFun (Fin n) ℝ i)) using 1

/-- A nonzero covector detects at least one original coordinate direction. -/
theorem exists_coordinate_ne_zero {ℓ : ℝ^n →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) :
    ∃ i : Fin n, ℓ (EuclideanSpace.basisFun (Fin n) ℝ i) ≠ 0 := by
  by_contra! h
  apply hℓ
  apply ContinuousLinearMap.coe_injective
  exact (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext fun i ↦ by simpa using h i

/-- An analytic regular level has an analytic chart and analytic
inverse germ. The selected coordinate of the chart is the defining function,
so the level is flattened without changing its original coordinate labels. -/
theorem exists_analytic_level_chart {φ : ℝ^n → ℝ} {p : ℝ^n}
    (hφ : AnalyticAt ℝ φ p) (hp : φ p = 0) (hreg : fderiv ℝ φ p ≠ 0) :
    ∃ i : Fin n, ∃ c : OpenPartialHomeomorph (ℝ^n) (ℝ^n),
      (c : ℝ^n → ℝ^n) = levelCoordinates φ p i ∧
      p ∈ c.source ∧ c p = 0 ∧
      AnalyticAt ℝ c p ∧ AnalyticAt ℝ c.symm 0 ∧
      (∀ x, c x i = φ x) := by
  obtain ⟨i, hi⟩ := exists_coordinate_ne_zero hreg
  have hd := hasStrictFDerivAt_levelCoordinates hφ i hi
  let c := hd.toOpenPartialHomeomorph (levelCoordinates φ p i)
  have hc : (c : ℝ^n → ℝ^n) = levelCoordinates φ p i := rfl
  have hcp : c p = 0 := levelCoordinates_base hp i
  have ha : AnalyticAt ℝ c p := analyticAt_levelCoordinates hφ i
  refine ⟨i, c, hc, hd.mem_toOpenPartialHomeomorph_source, hcp, ha, ?_, ?_⟩
  · rw [← hcp]
    exact c.analyticAt_symm' hd.mem_toOpenPartialHomeomorph_source ha hd.hasFDerivAt.fderiv
  · exact levelCoordinates_apply_self φ p i

/-- Reindexing the selected coordinate gives a level chart whose coordinate
zero is the defining function. This includes a one-dimensional ambient space. -/
theorem exists_analytic_level_chart_zero {d : ℕ} {φ : ℝ^(d + 1) → ℝ}
    {p : ℝ^(d + 1)} (hφ : AnalyticAt ℝ φ p) (hp : φ p = 0)
    (hreg : fderiv ℝ φ p ≠ 0) :
    ∃ c : OpenPartialHomeomorph (ℝ^(d + 1)) (ℝ^(d + 1)),
      p ∈ c.source ∧ c p = 0 ∧
      AnalyticAt ℝ c p ∧ AnalyticAt ℝ c.symm 0 ∧
      (∀ x, c x 0 = φ x) := by
  obtain ⟨i, c, _, hps, hcp, hc, hci, hlevel⟩ :=
    exists_analytic_level_chart hφ hp hreg
  let e := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i 0)
  let c' := c.trans e.toHomeomorph.toOpenPartialHomeomorph
  refine ⟨c', ?_, ?_, ?_, ?_, ?_⟩
  · simpa [c', OpenPartialHomeomorph.trans_source] using hps
  · change e (c p) = 0
    rw [hcp, map_zero]
  · exact (e.toContinuousLinearEquiv.analyticAt _).comp hc
  · have hi : AnalyticAt ℝ c.symm (e.symm 0) := by simpa only [map_zero] using hci
    exact hi.comp (e.symm.toContinuousLinearEquiv.analyticAt _)
  · intro x
    change (e (c x)) 0 = φ x
    simpa [e, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'] using hlevel x

/-- An analytic function on a flattened hypersurface has an ambient analytic
extension, obtained by projecting to the flattened level. The input is only
analyticity of the surface pullback; no ambient regularity of `g` is assumed. -/
theorem exists_analytic_extension_of_pullback {d : ℕ}
    (c : OpenPartialHomeomorph (ℝ^(d + 1)) (ℝ^(d + 1)))
    {p : ℝ^(d + 1)} (hps : p ∈ c.source) (hcp : c p = 0)
    (hc : AnalyticAt ℝ c p) (g : ℝ^(d + 1) → ℝ)
    (hg : AnalyticAt ℝ
      (fun y : ℝ^d ↦ g (c.symm (PDE.Common.timeSpaceCons 0 y))) 0) :
    ∃ G : ℝ^(d + 1) → ℝ, AnalyticAt ℝ G p ∧
      ∀ᶠ x in 𝓝 p, c x 0 = 0 → G x = g x := by
  let G := fun x ↦ g (c.symm
    (PDE.Common.timeSpaceCons 0 (PDE.Common.spatialPartCLM d (c x))))
  refine ⟨G, ?_, ?_⟩
  · have hproj : AnalyticAt ℝ
        (fun x ↦ PDE.Common.spatialPartCLM d (c x)) p :=
      ((PDE.Common.spatialPartCLM d).analyticAt _).comp hc
    have hbase : PDE.Common.spatialPartCLM d (c p) = 0 := by rw [hcp, map_zero]
    exact (hbase ▸ hg).comp
      (f := fun x ↦ PDE.Common.spatialPartCLM d (c x)) hproj
  · filter_upwards [c.open_source.mem_nhds hps] with x hx hz
    have he : PDE.Common.timeSpaceCons 0 (PDE.Common.spatialPartCLM d (c x)) = c x := by
      rw [← hz]
      exact PDE.Common.timeSpaceCons_spatialPartCLM (c x)
    dsimp [G]
    rw [he, c.left_inv hx]

/-- The canonical oriented unit normal to a regular scalar level. -/
def levelNormal (φ : ℝ^n → ℝ) (x : ℝ^n) : ℝ^n :=
  ‖∇ φ x‖⁻¹ • ∇ φ x

/-- Regularity of the defining differential is exactly nonvanishing of its
Riesz representative. -/
theorem gradient_ne_zero {φ : ℝ^n → ℝ} {x : ℝ^n}
    (hreg : fderiv ℝ φ x ≠ 0) : ∇ φ x ≠ 0 := by
  intro h
  apply hreg
  rw [← toDual_gradient, h, map_zero]

/-- The normal has unit length at every regular point. -/
theorem norm_levelNormal {φ : ℝ^n → ℝ} {x : ℝ^n}
    (hreg : fderiv ℝ φ x ≠ 0) : ‖levelNormal φ x‖ = 1 := by
  simp only [levelNormal, norm_smul, norm_inv, Real.norm_eq_abs,
    abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr (gradient_ne_zero hreg))]

/-- The canonical normal is analytic wherever the defining function is
analytic and regular. -/
theorem analyticAt_levelNormal {φ : ℝ^n → ℝ} {x : ℝ^n}
    (hφ : AnalyticAt ℝ φ x) (hreg : fderiv ℝ φ x ≠ 0) :
    AnalyticAt ℝ (levelNormal φ) x := by
  have hg : AnalyticAt ℝ (∇ φ) x :=
    ((InnerProductSpace.toDual ℝ (ℝ^n)).symm.toContinuousLinearEquiv.analyticAt _).comp
      hφ.fderiv
  have hn : AnalyticAt ℝ (fun y ↦ ‖∇ φ y‖) x :=
    ((hg.contDiffAt : ContDiffAt ℝ ω (∇ φ) x).norm ℝ
      (gradient_ne_zero hreg)).analyticAt
  exact (hn.inv (norm_ne_zero_iff.mpr (gradient_ne_zero hreg))).smul hg

/-- The defining covector is the positive gradient norm times the unit
normal covector. -/
theorem fderiv_eq_norm_mul_inner_levelNormal {φ : ℝ^n → ℝ} {x : ℝ^n}
    (hreg : fderiv ℝ φ x ≠ 0) (v : ℝ^n) :
    fderiv ℝ φ x v = ‖∇ φ x‖ * inner ℝ (levelNormal φ x) v := by
  rw [levelNormal, real_inner_smul_left, ← mul_assoc,
    mul_inv_cancel₀ (norm_ne_zero_iff.mpr (gradient_ne_zero hreg)), one_mul]
  exact inner_gradient_left.symm

/-- An analytic regular level has local parametrizations with the
canonical unit conormal. Each point uses its own analytic chart germ; no
regularity of one chart on the whole neighborhood is assumed. -/
theorem hasConormalParametrizations_levelNormal {d : ℕ}
    {φ : ℝ^(d + 1) → ℝ} {U : Set (ℝ^(d + 1))}
    (hU : IsOpen U) (hφ : AnalyticOnNhd ℝ φ U)
    (hreg : ∀ x ∈ U, fderiv ℝ φ x ≠ 0) :
    HasConormalParametrizations (ℝ^d) (U ∩ {x | φ x = 0})
      (fun x ↦ (innerSL ℝ (levelNormal φ x)).toLinearMap) := by
  intro x hx
  obtain ⟨c, hxs, hcx, hc, hci, hlevel⟩ :=
    exists_analytic_level_chart_zero (hφ x hx.1) hx.2 (hreg x hx.1)
  let D := fderiv ℝ c x
  let Dinv := fderiv ℝ c.symm (0 : ℝ^(d + 1))
  let I := PDE.Common.embedWithTimeZeroCLM d
  have hix : c.symm 0 = x := by rw [← hcx, c.left_inv hxs]
  have ht : (0 : ℝ^(d + 1)) ∈ c.target := hcx ▸ c.map_source hxs
  have hD : HasFDerivAt c D x := hc.differentiableAt.hasFDerivAt
  have hDi : HasFDerivAt c.symm Dinv 0 := hci.differentiableAt.hasFDerivAt
  have hleft : Dinv.comp D = ContinuousLinearMap.id ℝ _ := by
    have hi : HasFDerivAt c.symm Dinv (c x) := by simpa only [hcx] using hDi
    have he : id =ᶠ[𝓝 x] c.symm ∘ c := by
      filter_upwards [c.open_source.mem_nhds hxs] with y hy
      exact (c.left_inv hy).symm
    exact ((hi.comp x hD).congr_of_eventuallyEq he).unique (hasFDerivAt_id x)
  have hright : D.comp Dinv = ContinuousLinearMap.id ℝ _ := by
    have hd : HasFDerivAt c D (c.symm 0) := by simpa only [hix] using hD
    have he : id =ᶠ[𝓝 (0 : ℝ^(d + 1))] c ∘ c.symm := by
      filter_upwards [c.open_target.mem_nhds ht] with y hy
      exact (c.right_inv hy).symm
    exact ((hd.comp 0 hDi).congr_of_eventuallyEq he).unique (hasFDerivAt_id 0)
  have hcoord (v : ℝ^(d + 1)) : D v 0 = fderiv ℝ φ x v := by
    have he : φ =ᶠ[𝓝 x] fun y ↦ c y 0 :=
      Filter.Eventually.of_forall fun y ↦ (hlevel y).symm
    exact congrArg (fun A ↦ A v)
      (((EuclideanSpace.proj 0).hasFDerivAt.comp x hD).congr_of_eventuallyEq he).fderiv.symm
  let ψ : ℝ^d → ℝ^(d + 1) := c.symm ∘ I
  have hψx : ψ 0 = x := by simp only [ψ, Function.comp_apply, map_zero, hix]
  have hψ : HasFDerivAt ψ (Dinv.comp I) 0 := by
    have hi : HasFDerivAt c.symm Dinv (I 0) := by simpa only [map_zero] using hDi
    exact hi.comp 0 I.hasFDerivAt
  refine ⟨ψ, 0, Dinv.comp I, hψx, hψ, ?_, ?_⟩
  · have hn : ‖∇ φ x‖ ≠ 0 := norm_ne_zero_iff.mpr (gradient_ne_zero (hreg x hx.1))
    have hleft_apply (v : ℝ^(d + 1)) : Dinv (D v) = v :=
      congrArg (fun A ↦ A v) hleft
    have hright_apply (v : ℝ^(d + 1)) : D (Dinv v) = v :=
      congrArg (fun A ↦ A v) hright
    ext v
    constructor
    · rintro ⟨y, rfl⟩
      change inner ℝ (levelNormal φ x) (Dinv (I y)) = 0
      apply (mul_eq_zero.mp ?_).resolve_left hn
      rw [← fderiv_eq_norm_mul_inner_levelNormal (hreg x hx.1), ← hcoord,
        hright_apply]
      exact PDE.Common.embedWithTimeZeroCLM_zero y
    · intro hv
      change inner ℝ (levelNormal φ x) v = 0 at hv
      have hz : D v 0 = 0 := by
        rw [hcoord, fderiv_eq_norm_mul_inner_levelNormal (hreg x hx.1), hv, mul_zero]
      refine ⟨PDE.Common.spatialPartCLM d (D v), ?_⟩
      change Dinv (I (PDE.Common.spatialPartCLM d (D v))) = v
      have he : I (PDE.Common.spatialPartCLM d (D v)) = D v := by
        change PDE.Common.timeSpaceCons 0 (PDE.Common.spatialPartCLM d (D v)) = D v
        rw [← hz, PDE.Common.timeSpaceCons_spatialPartCLM]
      rw [he, hleft_apply]
  · have hnear : ∀ᶠ y in 𝓝 (0 : ℝ^d), ψ y ∈ U := by
      apply hψ.continuousAt.preimage_mem_nhds
      rw [hψx]
      exact hU.mem_nhds hx.1
    have htarget : ∀ᶠ y in 𝓝 (0 : ℝ^d), I y ∈ c.target := by
      apply I.continuous.continuousAt.preimage_mem_nhds
      rw [map_zero]
      exact c.open_target.mem_nhds ht
    filter_upwards [hnear, htarget] with y hy hyt
    refine ⟨hy, ?_⟩
    change φ (c.symm (I y)) = 0
    rw [← hlevel, c.right_inv hyt]
    exact PDE.Common.embedWithTimeZeroCLM_zero y

/-- Analyticity and regularity at one point suffice to construct conormal
parametrizations on an open piece of the level near that point. -/
theorem exists_hasConormalParametrizations_levelNormal {d : ℕ}
    {φ : ℝ^(d + 1) → ℝ} {p : ℝ^(d + 1)}
    (hφ : AnalyticAt ℝ φ p) (hreg : fderiv ℝ φ p ≠ 0) :
    ∃ U : Set (ℝ^(d + 1)), IsOpen U ∧ p ∈ U ∧
      HasConormalParametrizations (ℝ^d) (U ∩ {x | φ x = 0})
        (fun x ↦ (innerSL ℝ (levelNormal φ x)).toLinearMap) := by
  have ha : ∀ᶠ x in 𝓝 p, AnalyticAt ℝ φ x := (isOpen_analyticAt ℝ φ).mem_nhds hφ
  have hnear : ∀ᶠ x in 𝓝 p, AnalyticAt ℝ φ x ∧ fderiv ℝ φ x ≠ 0 :=
    ha.and (hφ.fderiv.continuousAt.eventually_ne hreg)
  obtain ⟨U, hsub, hU, hp⟩ := mem_nhds_iff.mp hnear
  exact ⟨U, hU, hp, hasConormalParametrizations_levelNormal hU
    (fun x hx ↦ (hsub hx).1) (fun x hx ↦ (hsub hx).2)⟩

end PDE.Analysis.Hypersurface
