/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.HalfPlane.Construction
public import PDE.Analysis.Calculus.HalfSpaceGluingWithin
import PDE.FDeriv.Laplacian.Congruence

/-!
# Canonical whole-plane representatives of half-plane Boussinesq solutions

The equations of the classical class hold on the open upper half-plane and the fields below the
boundary are classical extensions, so a solution is determined only on the closed half-plane.
The canonical representative `canonical sol` replaces the fields below the boundary by the
weighted reflections of their values on the closed half-plane: of order one for the vorticity and
the temperature (which the class asks to be jointly `C¹`) and of order two for the stream
function (which it asks to be `C²` at every time). It is again a solution, regular if `sol` is
(`IsSolutionOn.canonical`, `IsRegularSolutionOn.canonical`), and two solutions that agree on the
closed half-plane at a time have the same canonical representative at that time
(`IsSolutionOn.canonical_eq`). Canonical representatives of different solutions can therefore
be glued in time.

## Main definitions

* `canonical sol`: the canonical representative.

## Main results

* `IsClassicalVorticityStreamSolutionOn.canonical`, `IsSolutionOn.canonical`,
  `IsRegularSolutionOn.canonical`: the classes are preserved; the times must have unique
  derivatives.
* `canonical_eq_of_eqOn`, `IsSolutionOn.canonical_eq`: the representative depends only on the
  values on the closed half-plane.
* `IsHolderData.congr`, `IsHolderData.mono`: the data class depends only on the values on the
  closed half-plane and is monotone in the radius and the bound.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology
open GreenFunction IncompressibleFlow SobolevSpace.GraphSpace.HigherOrderReflection

namespace Boussinesq.HalfPlane

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

/-- The canonical representative of the fields: below the boundary, the vorticity and the
temperature are the weighted reflections of order one, and the stream function the weighted
reflection of order two, of their values on the closed half-plane. -/
def canonical (sol : VorticityStreamFields) : VorticityStreamFields where
  vorticity x t := weightedReflectionFun 1 1 (fun y ↦ sol.vorticity y t) x
  temperature x t := weightedReflectionFun 1 1 (fun y ↦ sol.temperature y t) x
  streamFunction x t := weightedReflectionFun 1 2 (fun y ↦ sol.streamFunction y t) x

variable {sol sol' : VorticityStreamFields} {I : Set ℝ}

/-- On the closed half-plane the canonical representative has the vorticity of the fields. -/
@[simp]
theorem canonical_vorticity_of_nonneg {x : ℝ^2} (hx : 0 ≤ x 1) (t : ℝ) :
    (canonical sol).vorticity x t = sol.vorticity x t :=
  weightedReflectionFun_eq_of_nonneg 1 1 (fun y ↦ sol.vorticity y t) x hx

/-- On the closed half-plane the canonical representative has the temperature of the fields. -/
@[simp]
theorem canonical_temperature_of_nonneg {x : ℝ^2} (hx : 0 ≤ x 1) (t : ℝ) :
    (canonical sol).temperature x t = sol.temperature x t :=
  weightedReflectionFun_eq_of_nonneg 1 1 (fun y ↦ sol.temperature y t) x hx

/-- On the closed half-plane the canonical representative has the stream function of the fields. -/
@[simp]
theorem canonical_streamFunction_of_nonneg {x : ℝ^2} (hx : 0 ≤ x 1) (t : ℝ) :
    (canonical sol).streamFunction x t = sol.streamFunction x t :=
  weightedReflectionFun_eq_of_nonneg 1 2 (fun y ↦ sol.streamFunction y t) x hx

/-- Near a point of the open half-plane a canonical slice agrees with the original one. -/
theorem eventuallyEq_canonical {f : ℝ^2 → ℝ} (K : ℕ) {x : ℝ^2} (hx : x ∈ upperHalfPlane) :
    weightedReflectionFun 1 K f =ᶠ[𝓝 x] f := by
  filter_upwards [isOpen_upperHalfPlane.mem_nhds hx] with y hy
  exact weightedReflectionFun_eq_of_nonneg 1 K f y (le_of_lt hy)

/-- On the open half-plane the velocity of the canonical representative is the velocity. -/
theorem vorticityStreamVelocity_canonical {x : ℝ^2} (hx : x ∈ upperHalfPlane) (t : ℝ) :
    vorticityStreamVelocity (canonical sol) x t = vorticityStreamVelocity sol x t := by
  have h := (eventuallyEq_canonical (f := fun y ↦ sol.streamFunction y t) 2 hx).fderiv_eq
    (𝕜 := ℝ)
  simp only [vorticityStreamVelocity, planarStreamVelocity]
  change WithLp.toLp 2 ![-(fderiv ℝ (weightedReflectionFun 1 2
      (fun y ↦ sol.streamFunction y t)) x (EuclideanSpace.single 1 1)),
      fderiv ℝ (weightedReflectionFun 1 2 (fun y ↦ sol.streamFunction y t)) x
        (EuclideanSpace.single 0 1)] = _
  rw [h]
  rfl

/-- The classical class is preserved by the canonical representative. -/
theorem _root_.Boussinesq.IsClassicalVorticityStreamSolutionOn.canonical
    (h : IsClassicalVorticityStreamSolutionOn sol I) (hI : UniqueDiffOn ℝ I) :
    IsClassicalVorticityStreamSolutionOn (HalfPlane.canonical sol) I where
  regularity :=
    { vorticity_contDiffOn := PDE.Analysis.contDiffOn_weightedReflectionFun_slice
        (F := fun p : ℝ^2 × ℝ ↦ sol.vorticity p.1 p.2) 1 le_rfl hI
        h.regularity.vorticity_contDiffOn
      temperature_contDiffOn := PDE.Analysis.contDiffOn_weightedReflectionFun_slice
        (F := fun p : ℝ^2 × ℝ ↦ sol.temperature p.1 p.2) 1 le_rfl hI
        h.regularity.temperature_contDiffOn
      vorticity_differentiableAt_time := fun ht ↦
        PDE.Analysis.differentiableAt_weightedReflectionFun_slice
          (F := fun p : ℝ^2 × ℝ ↦ sol.vorticity p.1 p.2) 1 1
          fun _ ↦ h.regularity.vorticity_differentiableAt_time ht
      temperature_differentiableAt_time := fun ht ↦
        PDE.Analysis.differentiableAt_weightedReflectionFun_slice
          (F := fun p : ℝ^2 × ℝ ↦ sol.temperature p.1 p.2) 1 1
          fun _ ↦ h.regularity.temperature_differentiableAt_time ht
      streamFunction_spatial_contDiff := fun ht ↦
        PDE.Analysis.contDiff_weightedReflectionFun (k := 2) 1 (by norm_num)
          (by exact_mod_cast (h.regularity.streamFunction_spatial_contDiff ht).contDiffOn) }
  vorticity_equation := by
    intro x t hx ht
    have hω := eventuallyEq_canonical (f := fun y ↦ sol.vorticity y t) 1 hx
    have hθ := eventuallyEq_canonical (f := fun y ↦ sol.temperature y t) 1 hx
    have htime : (fun s ↦ (HalfPlane.canonical sol).vorticity x s) = fun s ↦ sol.vorticity x s :=
      funext fun s ↦ canonical_vorticity_of_nonneg (le_of_lt hx) s
    have h0 := h.vorticity_equation hx ht
    simp only [PDE.advectiveDerivative] at h0 ⊢
    change deriv (fun s ↦ (HalfPlane.canonical sol).vorticity x s) t +
        fderiv ℝ (weightedReflectionFun 1 1 (fun y ↦ sol.vorticity y t)) x
          (vorticityStreamVelocity (HalfPlane.canonical sol) x t) =
      (∂[(0 : Fin 2)] (weightedReflectionFun 1 1 (fun y ↦ sol.temperature y t))) x
    rw [htime, hω.fderiv_eq, vorticityStreamVelocity_canonical hx,
      PDE.partialDeriv_congr_nhds 0 hθ]
    exact h0
  temperature_equation := by
    intro x t hx ht
    have hθ := eventuallyEq_canonical (f := fun y ↦ sol.temperature y t) 1 hx
    have htime :
        (fun s ↦ (HalfPlane.canonical sol).temperature x s) = fun s ↦ sol.temperature x s :=
      funext fun s ↦ canonical_temperature_of_nonneg (le_of_lt hx) s
    have h0 := h.temperature_equation hx ht
    simp only [PDE.advectiveDerivative] at h0 ⊢
    change deriv (fun s ↦ (HalfPlane.canonical sol).temperature x s) t +
        fderiv ℝ (weightedReflectionFun 1 1 (fun y ↦ sol.temperature y t)) x
          (vorticityStreamVelocity (HalfPlane.canonical sol) x t) = 0
    rw [htime, hθ.fderiv_eq, vorticityStreamVelocity_canonical hx]
    exact h0
  streamFunction_equation := by
    intro x t hx ht
    have hψ := eventuallyEq_canonical (f := fun y ↦ sol.streamFunction y t) 2 hx
    change -PDE.laplacian (weightedReflectionFun 1 2 (fun y ↦ sol.streamFunction y t)) x =
      (HalfPlane.canonical sol).vorticity x t
    rw [EuclideanLaplacian.laplacian_congr_nhds hψ, canonical_vorticity_of_nonneg (le_of_lt hx)]
    exact h.streamFunction_equation hx ht
  zero_streamFunction_boundary := by
    intro x₁ t ht
    rw [canonical_streamFunction_of_nonneg (by simp)]
    exact h.zero_streamFunction_boundary x₁ ht

/-- The Green potential of a canonical vorticity slice is that of the original slice. -/
theorem halfSpaceGreenPotential_canonical (t : ℝ) :
    halfSpaceGreenPotential (fun y ↦ (canonical sol).vorticity y t) =
      halfSpaceGreenPotential (fun y ↦ sol.vorticity y t) :=
  halfSpaceGreenPotential_congr fun _ hy ↦ canonical_vorticity_of_nonneg (le_of_lt hy) t

/-- Solutions are preserved by the canonical representative. -/
theorem IsSolutionOn.canonical (h : IsSolutionOn sol I) (hI : UniqueDiffOn ℝ I) :
    IsSolutionOn (canonical sol) I where
  classical := h.classical.canonical hI
  stream t ht x hx := by
    rw [canonical_streamFunction_of_nonneg hx, halfSpaceGreenPotential_canonical]
    exact h.stream t ht x hx
  support a b hab := by
    obtain ⟨R, hR⟩ := h.support a b hab
    exact ⟨R, fun t ht x hx hxR ↦ by
      rw [canonical_vorticity_of_nonneg hx, canonical_temperature_of_nonneg hx]
      exact hR t ht x hx hxR⟩

/-- The data class depends only on the values on the closed half-plane. -/
theorem IsHolderData.congr {ω₀ θ₀ ω₁ θ₁ : ℝ^2 → ℝ} {α R N : ℝ}
    (h : IsHolderData ω₀ θ₀ α R N) (hω : ∀ x : ℝ^2, 0 ≤ x 1 → ω₁ x = ω₀ x)
    (hθ : ∀ x : ℝ^2, 0 ≤ x 1 → θ₁ x = θ₀ x) : IsHolderData ω₁ θ₁ α R N := by
  have hω' : EqOn ω₁ ω₀ H̄ := fun x hx ↦ hω x hx
  have hθ' : EqOn θ₁ θ₀ H̄ := fun x hx ↦ hθ x hx
  have dω {x : ℝ^2} (hx : 0 ≤ x 1) : fderivWithin ℝ ω₁ H̄ x = fderivWithin ℝ ω₀ H̄ x :=
    fderivWithin_congr hω' (hω x hx)
  have dθ {x : ℝ^2} (hx : 0 ≤ x 1) : fderivWithin ℝ θ₁ H̄ x = fderivWithin ℝ θ₀ H̄ x :=
    fderivWithin_congr hθ' (hθ x hx)
  have dθ' : EqOn (fderivWithin ℝ θ₁ H̄) (fderivWithin ℝ θ₀ H̄) H̄ := fun x hx ↦ dθ hx
  have d2θ {x : ℝ^2} (hx : 0 ≤ x 1) :
      fderivWithin ℝ (fderivWithin ℝ θ₁ H̄) H̄ x = fderivWithin ℝ (fderivWithin ℝ θ₀ H̄) H̄ x :=
    fderivWithin_congr dθ' (dθ hx)
  exact
    { vorticity_contDiffOn := h.vorticity_contDiffOn.congr hω'
      temperature_contDiffOn := h.temperature_contDiffOn.congr hθ'
      eq_zero := fun x hx hxR ↦ by
        rw [hω x hx, hθ x hx]
        exact h.eq_zero x hx hxR
      abs_vorticity_le := fun x hx ↦ by rw [hω x hx]; exact h.abs_vorticity_le x hx
      norm_fderivWithin_vorticity_le := fun x hx ↦ by
        rw [dω hx]; exact h.norm_fderivWithin_vorticity_le x hx
      holder_vorticity := fun x y hx hy ↦ by
        rw [dω hx, dω hy]; exact h.holder_vorticity x y hx hy
      abs_temperature_le := fun x hx ↦ by rw [hθ x hx]; exact h.abs_temperature_le x hx
      norm_fderivWithin_temperature_le := fun x hx ↦ by
        rw [dθ hx]; exact h.norm_fderivWithin_temperature_le x hx
      norm_fderivWithin_fderivWithin_temperature_le := fun x hx ↦ by
        rw [d2θ hx]; exact h.norm_fderivWithin_fderivWithin_temperature_le x hx
      holder_temperature := fun x y hx hy ↦ by
        rw [d2θ hx, d2θ hy]; exact h.holder_temperature x y hx hy }

/-- The data class is monotone in the support radius and in the bound. -/
theorem IsHolderData.mono {ω₀ θ₀ : ℝ^2 → ℝ} {α R N R' N' : ℝ} (h : IsHolderData ω₀ θ₀ α R N)
    (hR : R ≤ R') (hN : N ≤ N') : IsHolderData ω₀ θ₀ α R' N' where
  vorticity_contDiffOn := h.vorticity_contDiffOn
  temperature_contDiffOn := h.temperature_contDiffOn
  eq_zero x hx hxR := h.eq_zero x hx (hR.trans_lt hxR)
  abs_vorticity_le x hx := (h.abs_vorticity_le x hx).trans hN
  norm_fderivWithin_vorticity_le x hx := (h.norm_fderivWithin_vorticity_le x hx).trans hN
  holder_vorticity x y hx hy := (h.holder_vorticity x y hx hy).trans
    (mul_le_mul_of_nonneg_right hN (Real.rpow_nonneg (norm_nonneg _) _))
  abs_temperature_le x hx := (h.abs_temperature_le x hx).trans hN
  norm_fderivWithin_temperature_le x hx := (h.norm_fderivWithin_temperature_le x hx).trans hN
  norm_fderivWithin_fderivWithin_temperature_le x hx :=
    (h.norm_fderivWithin_fderivWithin_temperature_le x hx).trans hN
  holder_temperature x y hx hy := (h.holder_temperature x y hx hy).trans
    (mul_le_mul_of_nonneg_right hN (Real.rpow_nonneg (norm_nonneg _) _))

/-- Regular solutions are preserved by the canonical representative. -/
theorem IsRegularSolutionOn.canonical {α : ℝ} (h : IsRegularSolutionOn sol I α)
    (hI : UniqueDiffOn ℝ I) : IsRegularSolutionOn (canonical sol) I α where
  toIsSolutionOn := h.toIsSolutionOn.canonical hI
  holderData a b hab := by
    obtain ⟨R, N, hRN⟩ := h.holderData a b hab
    exact ⟨R, N, fun t ht ↦ (hRN t ht).congr (fun x hx ↦ canonical_vorticity_of_nonneg hx t)
      (fun x hx ↦ canonical_temperature_of_nonneg hx t)⟩

/-- **The canonical representative depends only on the values on the closed half-plane.** -/
theorem canonical_eq_of_eqOn {t : ℝ}
    (hω : ∀ x : ℝ^2, 0 ≤ x 1 → sol.vorticity x t = sol'.vorticity x t)
    (hθ : ∀ x : ℝ^2, 0 ≤ x 1 → sol.temperature x t = sol'.temperature x t)
    (hψ : ∀ x : ℝ^2, 0 ≤ x 1 → sol.streamFunction x t = sol'.streamFunction x t) (x : ℝ^2) :
    (canonical sol).vorticity x t = (canonical sol').vorticity x t ∧
      (canonical sol).temperature x t = (canonical sol').temperature x t ∧
      (canonical sol).streamFunction x t = (canonical sol').streamFunction x t := by
  refine ⟨?_, ?_, ?_⟩
  · exact congrFun (PDE.Analysis.weightedReflectionFun_congr 1 1 hω) x
  · exact congrFun (PDE.Analysis.weightedReflectionFun_congr 1 1 hθ) x
  · exact congrFun (PDE.Analysis.weightedReflectionFun_congr 1 2 hψ) x

/-- Two solutions that agree on the closed half-plane at a time have the same canonical
representative at that time. -/
theorem IsSolutionOn.canonical_eq {I' : Set ℝ} (h : IsSolutionOn sol I)
    (h' : IsSolutionOn sol' I') {t : ℝ} (ht : t ∈ I) (ht' : t ∈ I')
    (heq : ∀ x : ℝ^2, 0 ≤ x 1 →
      sol.vorticity x t = sol'.vorticity x t ∧ sol.temperature x t = sol'.temperature x t)
    (x : ℝ^2) :
    (HalfPlane.canonical sol).vorticity x t = (HalfPlane.canonical sol').vorticity x t ∧
      (HalfPlane.canonical sol).temperature x t = (HalfPlane.canonical sol').temperature x t ∧
      (HalfPlane.canonical sol).streamFunction x t =
        (HalfPlane.canonical sol').streamFunction x t := by
  have hG : halfSpaceGreenPotential (fun y ↦ sol.vorticity y t) =
      halfSpaceGreenPotential (fun y ↦ sol'.vorticity y t) :=
    halfSpaceGreenPotential_congr fun y hy ↦ (heq y (le_of_lt hy)).1
  refine canonical_eq_of_eqOn (fun y hy ↦ (heq y hy).1) (fun y hy ↦ (heq y hy).2)
    (fun y hy ↦ ?_) x
  rw [h.stream t ht y hy, h'.stream t ht' y hy, hG]

end Boussinesq.HalfPlane
