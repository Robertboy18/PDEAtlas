/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Convex.Proximal.Yosida.Basic
import PDE.Analysis.Convex.Differentiable.Supporting
public import PDE.Elliptic.Semilinear.Resolvent.ConvexGradient.Basic

/-!
# Agreement of the general subdifferential and smooth resolvents

For a differentiable real convex potential, the extended-energy subdifferential is the
singleton containing its Riesz gradient. The general resolvent of
`PDE.Analysis.Convex.resolvent` therefore agrees with `convexGradientResolvent`, and the
Yosida approximation, the proximal-energy inequalities and the pointwise estimates of the
smooth theory follow from the general ones.

The differentiability assumption belongs to this specialization. It is absent from the
general construction, which allows infinite energies and multivalued subdifferentials.
-/

@[expose] public section

noncomputable section

open PDE.Analysis.Convex

namespace PDE.Elliptic.Semilinear

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A real differentiable convex potential has exactly its Riesz gradient as subgradient. -/
theorem subdifferential_coe_eq_singleton {Phi : H → ℝ}
    (hconvex : ConvexOn ℝ Set.univ Phi) {u : H} {D : H →L[ℝ] ℝ}
    (hD : HasFDerivAt Phi D u) :
    subdifferential (fun x ↦ (Phi x : EReal)) u =
      {(InnerProductSpace.toDual ℝ H).symm D} := by
  ext v
  constructor
  · intro hv
    have hs := (mem_subdifferential_iff (isProper_coeReal Phi)).1 hv
    have hmin : IsLocalMin (fun x ↦ Phi x - InnerProductSpace.toDual ℝ H v x) u := by
      apply Filter.Eventually.of_forall
      intro w
      have h := hs.2 w (EReal.coe_ne_top _)
      simp only [EReal.toReal_coe, inner_sub_right] at h
      simp only [InnerProductSpace.toDual_apply_apply]
      linarith
    have hzero := hmin.hasFDerivAt_eq_zero
      (hD.sub (InnerProductSpace.toDual ℝ H v).hasFDerivAt)
    change v = (InnerProductSpace.toDual ℝ H).symm D
    apply (InnerProductSpace.toDual ℝ H).injective
    simpa only [LinearIsometryEquiv.apply_symm_apply] using (sub_eq_zero.1 hzero).symm
  · intro hv
    rcases hv with rfl
    apply (mem_subdifferential_iff (isProper_coeReal Phi)).2
    refine ⟨EReal.coe_ne_top _, fun w _ ↦ ?_⟩
    have hs := PDE.Analysis.fderiv_apply_sub_le_sub_of_convex hconvex hD w
      (Set.mem_univ u) (Set.mem_univ w)
    have hinner : inner ℝ ((InnerProductSpace.toDual ℝ H).symm D) (w - u) = D (w - u) := by
      rw [← InnerProductSpace.toDual_apply_apply, LinearIsometryEquiv.apply_symm_apply]
    simp only [EReal.toReal_coe, hinner]
    linarith

/-- The gradient of a differentiable real convex potential is a subgradient of its coercion. -/
theorem gradient_mem_subdifferential_coe {Phi : H → ℝ}
    (hconvex : ConvexOn ℝ Set.univ Phi) {u : H} {D : H →L[ℝ] ℝ}
    (hD : HasFDerivAt Phi D u) :
    gradient Phi u ∈ subdifferential (fun x ↦ (Phi x : EReal)) u := by
  rw [subdifferential_coe_eq_singleton hconvex hD, gradient, hD.fderiv]
  exact Set.mem_singleton _

variable (Phi : H → ℝ) (hconvex : ConvexOn ℝ Set.univ Phi)
  (D : H → StrongDual ℝ H) (hD : ∀ u, HasFDerivAt Phi (D u) u)

include D hD in
omit [CompleteSpace H] in
/-- Differentiability supplies the lower semicontinuity needed for the general construction. -/
theorem lowerSemicontinuous_coe_of_hasFDerivAt :
    LowerSemicontinuous (fun x ↦ (Phi x : EReal)) :=
  (continuous_coe_real_ereal.comp
    (continuous_iff_continuousAt.2 fun x ↦ (hD x).continuousAt)).lowerSemicontinuous

/-- The nonsmooth construction specializes to the convex-gradient resolvent. -/
theorem subdifferentialResolvent_eq_convexGradientResolvent
    {lambda : ℝ} (hlambda : 0 < lambda) (w : H) :
    resolvent (fun x ↦ (Phi x : EReal)) (isProper_coeReal Phi)
        (convex_realEpigraph_coeReal hconvex)
        (lowerSemicontinuous_coe_of_hasFDerivAt Phi D hD) lambda hlambda w =
      convexGradientResolvent Phi hconvex D hD lambda hlambda.le w := by
  let u := convexGradientResolvent Phi hconvex D hD lambda hlambda.le w
  have hv : (InnerProductSpace.toDual ℝ H).symm (D u) ∈
      subdifferential (fun x ↦ (Phi x : EReal)) u := by
    rw [subdifferential_coe_eq_singleton hconvex (hD u)]
    exact Set.mem_singleton _
  apply resolvent_eq_of_mem_subdifferential (isProper_coeReal Phi)
    (convex_realEpigraph_coeReal hconvex)
    (lowerSemicontinuous_coe_of_hasFDerivAt Phi D hD) hlambda hv
  apply (InnerProductSpace.toDual ℝ H).injective
  rw [map_add, map_smul, LinearIsometryEquiv.apply_symm_apply]
  exact convexGradientResolvent_equation Phi hconvex D hD lambda hlambda.le w

end PDE.Elliptic.Semilinear
