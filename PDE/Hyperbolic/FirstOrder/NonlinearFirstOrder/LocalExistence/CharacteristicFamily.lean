/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import
  PDE.Hyperbolic.FirstOrder.NonlinearFirstOrder.LocalExistence.AutomaticCharacteristicFlow
public import PDE.Hyperbolic.FirstOrder.NonlinearFirstOrder.LocalExistence.CharacteristicFlow
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Contact transport for C¹ characteristic families

A C¹ characteristic family has contact defect `D_y z - ⟨p, D_y x⟩`.
When its boundary derivative solves the variational equation,
differentiating this defect in time and using preservation of `F = 0`
gives the homogeneous equation `C' = -F_z C`. Compatible initial data
make the initial defect zero.

The variational equation is a hypothesis here; `SmoothConstruction` obtains
it from the derivative of the constructed ODE flow. A local bound on `F_z` gives the contact
uniqueness and inverse coordinates.

This is step 3 of the proof of Theorem 2 in Evans, §3.2.4, where the defect is `r^i` of (44)
and solves the linear equation (48).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.2.4, proof of Theorem 2, equations (42)-(48).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (SpaceTime)

noncomputable section

open Filter Metric Set
open scoped NNReal RealInnerProductSpace Topology

namespace NonlinearFirstOrder

variable {k : ℕ}

/-- Contact transport for a C¹ characteristic family whose boundary
variation satisfies the linearized ODE.

The linearized equation is supplied by the constructed ODE flow in the final
existence theorem. Preservation of the PDE residual gives its zero boundary
derivative, which cancels the inhomogeneous term in the contact equation. -/
theorem contact_evolution_ofContDiffOneCharacteristicFamily
    (F : SpaceTime k → ℝ → SpaceTime k → ℝ) (boundary : ℝ^k → SpaceTime k) (data : ℝ^k → ℝ)
    (initialGradient : ℝ^k → SpaceTime k) (W : Set (ℝ^k)) (hW : IsOpen W)
    (ε : Set.Ioi (0 : ℝ)) (curve : (ℝ^k × ℝ) → (SpaceTime k × (ℝ × SpaceTime k)))
    (hF : ContDiff ℝ 2 (phaseFunction (n := k + 1) F))
    (hcurve : ContDiffOn ℝ 1 curve (W ×ˢ Ioo (-(ε : ℝ)) (ε : ℝ)))
    (hinitial : ∀ y ∈ W, curve (y, 0) = characteristicInitialState boundary data initialGradient y)
    (hode : ∀ y ∈ W, ∀ s ∈ Ioo (-(ε : ℝ)) (ε : ℝ),
      HasDerivAt (fun τ ↦ curve (y, τ)) (characteristicVectorField F (curve (y, s))) s)
    (hvariation : ∀ y ∈ W, ∀ dy : ℝ^k, ∀ s ∈ Ioo (-(ε : ℝ)) (ε : ℝ),
      HasDerivAt (fun τ ↦ fderiv ℝ curve (y, τ) (dy, 0))
        (fderiv ℝ (characteristicVectorField F) (curve (y, s)) (fderiv ℝ curve (y, s) (dy, 0))) s)
    (hcompat : ∀ y ∈ W, IsCompatibleInitialGradientAt F boundary data y (initialGradient y)) :
    ∀ y ∈ W, ∀ dy : ℝ^k, ∀ s ∈ Ioo (-(ε : ℝ)) (ε : ℝ),
      HasDerivAt
        (fun τ ↦ contactDefect (fun r ↦ (curve r).2.2) (fun r ↦ (curve r).1)
          (fun r ↦ (curve r).2.1) y τ dy)
        (-valueDerivative (n := k + 1) F (curve (y, s)).1 (curve (y, s)).2.1 (curve (y, s)).2.2 *
          contactDefect (fun r ↦ (curve r).2.2) (fun r ↦ (curve r).1) (fun r ↦ (curve r).2.1)
            y s dy) s := by
  intro y hy dy s hs
  have hbox : IsOpen (W ×ˢ Ioo (-(ε : ℝ)) ε) := hW.prod isOpen_Ioo
  have hd : ∀ τ ∈ Ioo (-(ε : ℝ)) ε, HasFDerivAt curve (fderiv ℝ curve (y, τ)) (y, τ) := fun τ hτ ↦
    ((hcurve.contDiffAt (hbox.mem_nhds ⟨hy, hτ⟩)).differentiableAt one_ne_zero).hasFDerivAt
  -- The contact defect, read off the full boundary variation `D_y curve`.
  have hdefect : ∀ τ ∈ Ioo (-(ε : ℝ)) ε,
      contactDefect (fun r ↦ (curve r).2.2) (fun r ↦ (curve r).1) (fun r ↦ (curve r).2.1)
        y τ dy = (fderiv ℝ curve (y, τ) (dy, 0)).2.1 -
          ⟪(curve (y, τ)).1, (fderiv ℝ curve (y, τ) (dy, 0)).2.2⟫ := fun τ hτ ↦ by
    rw [contactDefect, (hd τ hτ).snd.fst.fderiv, (hd τ hτ).snd.snd.fderiv]
    rfl
  have hF1 : Differentiable ℝ (phaseFunction (n := k + 1) F) := hF.differentiable (by norm_num)
  set c := curve (y, s)
  set D := fderiv ℝ curve (y, s) (dy, 0)
  set V := fderiv ℝ (characteristicVectorField F) c D
  -- `F = 0` along the family, so its derivative along the variation vanishes.
  have hres : fderiv ℝ (phaseFunction (n := k + 1) F) c D = 0 := by
    have hzero : (fun _ ↦ (0 : ℝ)) =ᶠ[𝓝 (y, s)] phaseFunction (n := k + 1) F ∘ curve := by
      filter_upwards [hbox.eventually_mem ⟨hy, hs⟩] with r hr
      refine (residual_eq_zero_of_characteristic F (hF.of_le (by norm_num))
        (fun τ ↦ curve (r.1, τ)) ε ε.2 (fun τ hτ ↦ hode r.1 hr.1 τ hτ) ?_ hr.2).symm
      rw [hinitial r.1 hr.1]
      exact (hcompat r.1 hr.1).1
    simpa using congrArg (· (dy, 0)) ((((hF1 c).hasFDerivAt.comp (y, s)
      (hd s hs)).congr_of_eventuallyEq hzero).unique (hasFDerivAt_const (0 : ℝ) (y, s)))
  -- The `z` component of the variation of the vector field.
  have hV : V.2.1 = ⟪characteristicDp F c, D.1⟫ + ⟪V.2.2, c.1⟫ := by
    have hvf := ((contDiff_characteristicVectorField F hF).differentiable one_ne_zero c).hasFDerivAt
    have hdp : HasFDerivAt (characteristicDp F) _ c := hvf.snd.snd
    simpa using congrArg (· D) (hvf.snd.fst.unique (hdp.inner ℝ hasFDerivAt_fst))
  have hvar := hvariation y hy dy s hs
  have hp : HasDerivAt (fun τ ↦ (curve (y, τ)).1) (characteristicVectorField F c).1 s :=
    (hasFDerivAt_fst.comp_hasDerivAt s (hode y hy s hs) :)
  have hz : HasDerivAt (fun τ ↦ (fderiv ℝ curve (y, τ) (dy, 0)).2.1) V.2.1 s :=
    ((hasFDerivAt_fst.comp D hasFDerivAt_snd).comp_hasDerivAt s hvar :)
  have hx : HasDerivAt (fun τ ↦ (fderiv ℝ curve (y, τ) (dy, 0)).2.2) V.2.2 s :=
    ((hasFDerivAt_snd.comp D hasFDerivAt_snd).comp_hasDerivAt s hvar :)
  rw [hdefect s hs]
  refine ((hz.sub (hp.inner ℝ hx)).congr_deriv ?_).congr_of_eventuallyEq ?_
  · rw [hV, real_inner_comm V.2.2]
    simp only [characteristicVectorField, characteristicDp_eq_DpF F hF1,
      characteristicDx_eq_DxF F hF1, characteristicDz_eq_DzF F hF1, inner_sub_left,
      inner_neg_left, real_inner_smul_left]
    linear_combination (fderiv_phaseFunction_apply_eq_characteristic_components F c.1 D.1 c.2.1
      D.2.1 c.2.2 D.2.2 (hF1 c)).symm.trans hres
  · filter_upwards [isOpen_Ioo.mem_nhds hs] with τ hτ using hdefect τ hτ

/-- Combine a C¹ characteristic family with its variational equation
and a local coefficient bound. The contact equation is derived from these
data and compatibility by `contact_evolution_ofContDiffOneCharacteristicFamily`. -/
noncomputable def LocalCharacteristicFlow.ofContDiffOneCharacteristicFamily
    (F : SpaceTime k → ℝ → SpaceTime k → ℝ) (boundary : ℝ^k → SpaceTime k) (data : ℝ^k → ℝ)
    (initialGradient : ℝ^k → SpaceTime k) (W : Set (ℝ^k)) (hW : IsOpen W)
    (ε : Set.Ioi (0 : ℝ)) (curve : (ℝ^k × ℝ) → (SpaceTime k × (ℝ × SpaceTime k)))
    (hF : ContDiff ℝ 2 (phaseFunction (n := k + 1) F))
    (hcurve : ContDiffOn ℝ 1 curve (W ×ˢ Ioo (-(ε : ℝ)) (ε : ℝ)))
    (hinitial : ∀ y ∈ W, curve (y, 0) = characteristicInitialState boundary data initialGradient y)
    (hode : ∀ y ∈ W, ∀ s ∈ Ioo (-(ε : ℝ)) (ε : ℝ),
      HasDerivAt (fun τ ↦ curve (y, τ)) (characteristicVectorField F (curve (y, s))) s)
    (hvariation : ∀ y ∈ W, ∀ dy : ℝ^k, ∀ s ∈ Ioo (-(ε : ℝ)) (ε : ℝ),
      HasDerivAt (fun τ ↦ fderiv ℝ curve (y, τ) (dy, 0))
        (fderiv ℝ (characteristicVectorField F) (curve (y, s)) (fderiv ℝ curve (y, s) (dy, 0))) s)
    (hcompat : ∀ y ∈ W, IsCompatibleInitialGradientAt F boundary data y (initialGradient y))
    (contactBound : ℝ≥0)
    (hDzBound : ∀ y ∈ W, ∀ s ∈ Ioo (-(ε : ℝ)) (ε : ℝ),
      ‖valueDerivative (n := k + 1) F (curve (y, s)).1 (curve (y, s)).2.1 (curve (y, s)).2.2‖ ≤
        contactBound) :
    LocalCharacteristicFlow F boundary data initialGradient :=
  have hbox : IsOpen (W ×ˢ Ioo (-(ε : ℝ)) ε) := hW.prod isOpen_Ioo
  have hF1 : Differentiable ℝ (phaseFunction (n := k + 1) F) := hF.differentiable (by norm_num)
  -- The time derivative of a component of `curve` is the matching characteristic equation.
  have htime {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] (g : ℝ^k × ℝ → G)
      (hg : ContDiffOn ℝ 1 g (W ×ˢ Ioo (-(ε : ℝ)) ε)) {y s g'} (hy : y ∈ W)
      (hs : s ∈ Ioo (-(ε : ℝ)) ε) (h : HasDerivAt (fun τ ↦ g (y, τ)) g' s) :
      fderiv ℝ g (y, s) (0, 1) = g' := by
    rw [← deriv_time_slice g y s
      ((hg.contDiffAt (hbox.mem_nhds ⟨hy, hs⟩)).differentiableAt one_ne_zero), h.deriv]
  have hchar {y s} (hy : y ∈ W) (hs : s ∈ Ioo (-(ε : ℝ)) ε) :=
    characteristic_equations_of_hasDerivAt F hF1 (fun τ ↦ curve (y, τ)) s (hode y hy s hs)
  { W := W
    isOpen_W := hW
    ε := ε
    xmap := fun r ↦ (curve r).2.2
    pmap := fun r ↦ (curve r).1
    zmap := fun r ↦ (curve r).2.1
    x_contDiff := hcurve.snd.snd
    p_contDiff := hcurve.fst
    z_contDiff := hcurve.snd.fst
    x_initial := fun y hy ↦ congrArg (·.2.2) (hinitial y hy)
    p_initial := fun y hy ↦ congrArg (·.1) (hinitial y hy)
    z_initial := fun y hy ↦ congrArg (·.2.1) (hinitial y hy)
    x_time := fun _ hy _ hs ↦ htime _ hcurve.snd.snd hy hs (hchar hy hs).2.2
    z_time := fun _ hy _ hs ↦ htime _ hcurve.snd.fst hy hs (hchar hy hs).2.1
    p_time := fun _ hy _ hs ↦ htime _ hcurve.fst hy hs (hchar hy hs).1
    contact_evolution := contact_evolution_ofContDiffOneCharacteristicFamily
      F boundary data initialGradient W hW ε curve hF hcurve hinitial hode hvariation hcompat
    contactBound := contactBound
    norm_DzF_le := hDzBound }

end NonlinearFirstOrder

end
