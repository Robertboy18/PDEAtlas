/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Normed.Operator.Prod

/-!
# A continuously differentiable radial lift

For `f(r,z)`, the map `(y,z) ↦ f(‖y‖,z)` loses the ordinary norm chain rule at
`y = 0`. A zero radial derivative removes that obstruction. The derivative of
the norm has operator norm at most one, so its contribution tends to zero
as the radial derivative does. This only needs C¹ regularity of `f`.
The parameter `z` and the values of `f` may lie in arbitrary real normed spaces,
so the result also applies to joint space-time profiles and derivative-valued maps.
-/

@[expose] public section

noncomputable section

open Filter Asymptotics
open scoped Topology

namespace PDE.Analysis

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

private def normProdDerivative (x : E × F) : E × F →L[ℝ] ℝ × F :=
  ((fderiv ℝ (fun y : E ↦ ‖y‖) x.1).comp
    (ContinuousLinearMap.fst ℝ E F)).prod (ContinuousLinearMap.snd ℝ E F)

private theorem norm_normProdDerivative_le (x : E × F) :
    ‖normProdDerivative x‖ ≤ 1 := by
  rw [normProdDerivative, ContinuousLinearMap.opNorm_prod, Prod.norm_def]
  refine max_le ?_ (ContinuousLinearMap.norm_snd_le ℝ E F)
  have hnorm : ‖fderiv ℝ (fun y : E ↦ ‖y‖) x.1‖ ≤ 1 :=
    norm_fderiv_le_of_lipschitz ℝ (x₀ := x.1) (C := 1) lipschitzWith_one_norm
  calc
    _ ≤ ‖fderiv ℝ (fun y : E ↦ ‖y‖) x.1‖ *
        ‖ContinuousLinearMap.fst ℝ E F‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 :=
      mul_le_mul hnorm (ContinuousLinearMap.norm_fst_le ℝ E F)
        (ContinuousLinearMap.opNorm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

private theorem map_pair_eq_of_radial_zero (L : ℝ × F →L[ℝ] G)
    (hL : L (1, 0) = 0) (r : ℝ) (z : F) :
    L (r, z) = L (0, z) := by
  have hsplit : (r, z) = r • ((1, 0) : ℝ × F) + (0, z) := by
    ext <;> simp
  rw [hsplit, map_add, map_smul, hL, smul_zero, zero_add]

private theorem hasFDerivAt_norm_prod_axis
    {f : ℝ × F → G} {x : E × F} (hx : x.1 = 0)
    (hf : DifferentiableAt ℝ f (0, x.2))
    (hzero : fderiv ℝ f (0, x.2) (1, 0) = 0) :
    HasFDerivAt (fun y : E × F ↦ f (‖y.1‖, y.2))
      ((fderiv ℝ f (0, x.2)).comp (normProdDerivative x)) x := by
  let q : E × F → ℝ × F := fun y ↦ (‖y.1‖, y.2)
  have hq : Continuous q := continuous_fst.norm.prodMk continuous_snd
  have hqx : q x = (0, x.2) := by simp [q, hx]
  have hbound : (fun y ↦ q y - (0, x.2)) =O[𝓝 x] (fun y ↦ y - x) := by
    apply isBigO_of_le
    intro y
    simp [q, Prod.norm_def, hx]
  have hsmall := (hf.hasFDerivAt.isLittleO.comp_tendsto
    (hqx ▸ hq.continuousAt.tendsto)).trans_isBigO hbound
  apply HasFDerivAt.of_isLittleO
  convert hsmall using 1
  funext y
  simp only [Function.comp_def, ContinuousLinearMap.comp_apply]
  have hleft : fderiv ℝ f (0, x.2) (q y - (0, x.2)) =
      fderiv ℝ f (0, x.2) (0, y.2 - x.2) :=
    map_pair_eq_of_radial_zero _ hzero _ _
  have hright : fderiv ℝ f (0, x.2) (normProdDerivative x (y - x)) =
      fderiv ℝ f (0, x.2) (0, y.2 - x.2) :=
    map_pair_eq_of_radial_zero _ hzero _ _
  rw [hleft, hright]
  simp [q, hx]

private theorem continuousAt_normProdDerivative {x : E × F} (hx : x.1 ≠ 0) :
    ContinuousAt (normProdDerivative (E := E)) x := by
  have hnorm : ContDiffAt ℝ 1 (fun v : E ↦ ‖v‖) x.1 := contDiffAt_norm ℝ hx
  have hn : ContinuousAt (fun y : E × F ↦
      fderiv ℝ (fun v : E ↦ ‖v‖) y.1) x :=
    (hnorm.continuousAt_fderiv one_ne_zero).comp continuousAt_fst
  exact (ContinuousLinearMap.prodₗᵢ ℝ
    (𝕜 := ℝ) (E := E × F) (F := ℝ) (G := F)).continuous.continuousAt.comp
      ((hn.clm_comp continuousAt_const).prodMk continuousAt_const)

private theorem continuousAt_radial_derivative_axis
    {f : ℝ × F → G} (hf : ContDiff ℝ 1 f) {x : E × F}
    (hx : x.1 = 0) (hzero : fderiv ℝ f (0, x.2) (1, 0) = 0) :
    ContinuousAt (fun y : E × F ↦
      (fderiv ℝ f (‖y.1‖, y.2)).comp (normProdDerivative y)) x := by
  let L := fderiv ℝ f (0, x.2)
  have hconstant (y : E × F) :
      L.comp (normProdDerivative y) = L.comp (normProdDerivative x) := by
    apply ContinuousLinearMap.ext
    intro v
    change L (normProdDerivative y v) = L (normProdDerivative x v)
    exact (map_pair_eq_of_radial_zero L hzero _ _).trans
      (map_pair_eq_of_radial_zero L hzero _ _).symm
  have hL : Tendsto (fun y : E × F ↦ fderiv ℝ f (‖y.1‖, y.2))
      (𝓝 x) (𝓝 L) := by
    simpa [Function.comp_def, L, hx] using ((hf.continuous_fderiv one_ne_zero).comp
      (continuous_fst.norm.prodMk continuous_snd)).continuousAt.tendsto (x := x)
  have hsmall : Tendsto (fun y : E × F ↦
      ((fderiv ℝ f (‖y.1‖, y.2)) - L).comp (normProdDerivative y))
      (𝓝 x) (𝓝 0) := by
    apply squeeze_zero_norm (E := E × F →L[ℝ] G)
      (a := fun y : E × F ↦ ‖fderiv ℝ f (‖y.1‖, y.2) - L‖)
    · intro y
      calc
        _ ≤ ‖fderiv ℝ f (‖y.1‖, y.2) - L‖ * ‖normProdDerivative y‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖fderiv ℝ f (‖y.1‖, y.2) - L‖ :=
          mul_le_of_le_one_right (ContinuousLinearMap.opNorm_nonneg _)
            (norm_normProdDerivative_le y)
    · simpa using (hL.sub (tendsto_const_nhds (x := L))).norm
  have hsum := hsmall.add
    (tendsto_const_nhds (x := L.comp (normProdDerivative x)))
  change Tendsto _ (𝓝 x) _
  convert hsum using 1
  · funext y
    rw [ContinuousLinearMap.sub_comp, ← hconstant y, sub_add_cancel]
  · simp [L, hx]

/-- A C¹ profile has a C¹ radial lift when its radial derivative vanishes on
the axis. No derivative of the lifted function is assumed. -/
theorem contDiff_norm_prod_of_radial_derivative_zero
    {f : ℝ × F → G} (hf : ContDiff ℝ 1 f)
    (haxis : ∀ z : F, fderiv ℝ f (0, z) (1, 0) = 0) :
    ContDiff ℝ 1 (fun x : E × F ↦ f (‖x.1‖, x.2)) := by
  apply contDiff_one_iff_hasFDerivAt.mpr
  refine ⟨fun x ↦ (fderiv ℝ f (‖x.1‖, x.2)).comp (normProdDerivative x), ?_, ?_⟩
  · apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hx : x.1 = 0
    · exact continuousAt_radial_derivative_axis hf hx (haxis x.2)
    · exact (((hf.continuous_fderiv one_ne_zero).comp
        (continuous_fst.norm.prodMk continuous_snd)).continuousAt).clm_comp
          (continuousAt_normProdDerivative hx)
  · intro x
    by_cases hx : x.1 = 0
    · simpa only [hx, norm_zero] using hasFDerivAt_norm_prod_axis hx
        (hf.differentiable one_ne_zero _) (haxis x.2)
    · have hnorm : ContDiffAt ℝ 1 (fun v : E ↦ ‖v‖) x.1 := contDiffAt_norm ℝ hx
      exact (hf.differentiable one_ne_zero _).hasFDerivAt.comp x
        (((hnorm.differentiableAt one_ne_zero).hasFDerivAt.comp x hasFDerivAt_fst).prodMk
          hasFDerivAt_snd)

end PDE.Analysis
