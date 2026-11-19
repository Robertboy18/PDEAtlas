/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Prod.ParameterDerivative
public import PDE.Analysis.Calculus.SpaceTime.TimeFirst

/-!
# The variational equation of a supplied smooth family

The parameter derivative of an actual solution family satisfies the differentiated
ODE. The mixed-derivative theorem for product slices supplies time differentiation;
the ODE identity on a parameter neighborhood and the chain rule identify its value.
The vector field may depend on the parameter as well as the state.

The ODE conclusion is an ordinary time derivative at interior times. Parameter
variations remain smooth relative to the closed time interval, including its
endpoints. Local agreement with the initial map identifies the initial derivative.
The family and its time equation are the inputs to each derivative formula.
-/

@[expose] public noncomputable section

open Filter Set
open scoped ContDiff Topology

namespace PDE.Analysis.ODE

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A jointly `C²` solution germ has the actual variational derivative. The
original time equation is required near the parameter at the fixed time; its
parameter derivative is obtained from this identity, rather than assumed. -/
theorem hasDerivAt_parameterVariation_of_contDiffAt
    {F : ℝ → P → E} {v : P × E → E} {t : ℝ} {p : P}
    (hF : ContDiffAt ℝ 2 F.uncurry (t, p))
    (hv : DifferentiableAt ℝ v (p, F t p))
    (hode : ∀ᶠ q in 𝓝 p, HasDerivAt (fun s ↦ F s q) (v (q, F t q)) t)
    (ξ : P) :
    HasDerivAt (fun s ↦ fderiv ℝ (F s) p ξ)
      (fderiv ℝ v (p, F t p) (ξ, fderiv ℝ (F t) p ξ)) t := by
  have hslice : DifferentiableAt ℝ (F t) p :=
    ((hF.differentiableAt two_ne_zero).hasFDerivAt.comp p
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) t p)).differentiableAt
  have hfield := hv.hasFDerivAt.comp p
    ((hasFDerivAt_id (𝕜 := ℝ) p).prodMk hslice.hasFDerivAt)
  have heq : (fun q ↦ deriv (fun s ↦ F s q) t) =ᶠ[𝓝 p]
      (fun q ↦ v (q, F t q)) := hode.mono (fun q hq ↦ hq.deriv)
  apply (PDE.Analysis.hasDerivAt_fderiv_space (U := F) hF ξ).congr_deriv
  rw [heq.fderiv_eq]
  simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply] using
    congrArg (fun A : P →L[ℝ] E ↦ A ξ) hfield.fderiv

/-- A supplied family smooth on a closed time strip satisfies the variational
ODE at each interior time. The original ODE holds for every nearby parameter;
only differentiability of the vector field at the displayed point is needed. -/
theorem hasDerivAt_parameterVariation_of_contDiffOn_Icc
    {F : ℝ → P → E} {v : P × E → E} {U : Set P} {a b t : ℝ} {p : P}
    (hU : IsOpen U) (hp : p ∈ U)
    (hF : ContDiffOn ℝ 2 F.uncurry (Icc a b ×ˢ U))
    (hode : ∀ q ∈ U, ∀ s ∈ Ioo a b,
      HasDerivAt (fun r ↦ F r q) (v (q, F s q)) s)
    (ht : t ∈ Ioo a b) (hv : DifferentiableAt ℝ v (p, F t p)) (ξ : P) :
    HasDerivAt (fun s ↦ fderiv ℝ (F s) p ξ)
      (fderiv ℝ v (p, F t p) (ξ, fderiv ℝ (F t) p ξ)) t := by
  refine hasDerivAt_parameterVariation_of_contDiffAt
    (hF.contDiffAt (prod_mem_nhds (Icc_mem_nhds ht.1 ht.2) (hU.mem_nhds hp)))
    hv ?_ ξ
  filter_upwards [hU.mem_nhds hp] with q hq using hode q hq t ht

/-- The actual parameter variation is smooth relative to the time set,
including a closed interval's endpoints. The time set may also be degenerate. -/
theorem contDiffOn_parameterVariation
    {F : ℝ → P → E} {I : Set ℝ} {U : Set P} {p : P}
    (hF : ContDiffOn ℝ ∞ F.uncurry (I ×ˢ U)) (hU : IsOpen U) (hp : p ∈ U)
    (ξ : P) : ContDiffOn ℝ ∞ (fun t ↦ fderiv ℝ (F t) p ξ) I := by
  have hD : ContDiffOn ℝ ∞
      (fun z : ℝ × P ↦ fderiv ℝ (F z.1) z.2) (I ×ˢ U) :=
    hF.fderiv_snd hU (by simp)
  exact (hD.contDiffOn_prodMk_left hp).clm_apply contDiffOn_const

/-- Local agreement with an initial map gives the actual initial parameter
derivative, also when zero is a time endpoint. The family's regularity supplies
differentiability; no separate derivative of the initial map is assumed. -/
theorem hasFDerivAt_initial_of_contDiffOn
    {F : ℝ → P → E} {initial : P → E} {I : Set ℝ} {U : Set P} {p : P}
    (hU : IsOpen U) (hp : p ∈ U) (hzero : (0 : ℝ) ∈ I)
    (hF : ContDiffOn ℝ 1 F.uncurry (I ×ˢ U))
    (hinit : F 0 =ᶠ[𝓝 p] initial) :
    HasFDerivAt (F 0) (fderiv ℝ initial p) p := by
  have hslice : ContDiffOn ℝ 1 (F 0) U := hF.contDiffOn_prodMk_right hzero
  rw [← hinit.fderiv_eq]
  exact ((hslice.contDiffAt (hU.mem_nhds hp)).differentiableAt one_ne_zero).hasFDerivAt

end PDE.Analysis.ODE
