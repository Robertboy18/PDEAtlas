/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.ODE.ExistUnique

/-!
# Rigidity of trajectories converging to a repelling equilibrium

A nonnegative radial derivative near an equilibrium makes squared distance nondecreasing
on any trajectory tail that converges to that equilibrium. The squared distance tends to
zero, so the trajectory is eventually constant. Local ODE uniqueness then propagates
constancy to every time.

A coercive derivative `c ‖z‖² ≤ ⟪z, DF(p) z⟫` with `c > 0` supplies the radial
inequality, so a strict source is not the forward limit of a nonconstant trajectory.
By time reversal, a strict sink is not the backward limit of one. The field need
only be `C¹` near the equilibrium.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology RealInnerProductSpace

namespace PDE.Analysis.Evolution

section Uniqueness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A classical trajectory through an equilibrium is constant if the field is C¹ near
that equilibrium. The field need not be regular away from the equilibrium. -/
theorem eq_const_of_hasDerivAt_of_eq_of_contDiffAt
    {F : E → E} {p : E} {v : ℝ → E} {t₀ : ℝ}
    (hF : ContDiffAt ℝ 1 F p) (hp : F p = 0)
    (hv : ∀ t, HasDerivAt v (F (v t)) t) (hzero : v t₀ = p) :
    v = fun _ ↦ p := by
  obtain ⟨K, U, hU, hLip⟩ := hF.exists_lipschitzOnWith
  have hc : Continuous v := continuous_iff_continuousAt.mpr fun t ↦ (hv t).continuousAt
  have hopen : IsOpen {t | v t = p} := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    change v t = p at ht
    have hnear : ∀ᶠ s in 𝓝 t, v s ∈ U := by
      apply (hc.continuousAt.tendsto).eventually
      simpa only [ht, eventually_mem_set] using hU
    exact ODE_solution_unique_of_eventually
      (v := fun _ ↦ F) (s := fun _ ↦ U) (g := fun _ ↦ p)
      (Eventually.of_forall fun _ ↦ hLip)
      (hnear.mono fun s hs ↦ ⟨hv s, hs⟩)
      (Eventually.of_forall fun s ↦ ⟨by simpa only [hp] using hasDerivAt_const s p,
        mem_of_mem_nhds hU⟩) ht
  have hclosed : IsClosed {t | v t = p} := isClosed_eq hc continuous_const
  have hall : {t | v t = p} = univ := (IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨t₀, hzero⟩)
  funext t
  exact show t ∈ {t | v t = p} from hall.symm ▸ mem_univ t

end Uniqueness

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A trajectory converging forward to an equilibrium with nonnegative radial field
nearby is constant. The sign is needed only in a neighborhood of the equilibrium. -/
theorem eq_const_of_tendsto_atTop_of_inner_nonneg
    {F : E → E} {p : E} {v : ℝ → E}
    (hF : ContDiffAt ℝ 1 F p) (hp : F p = 0)
    (hv : ∀ t, HasDerivAt v (F (v t)) t)
    (hlim : Tendsto v atTop (𝓝 p))
    (hradial : ∀ᶠ x in 𝓝 p, 0 ≤ ⟪x - p, F x⟫) :
    v = fun _ ↦ p := by
  obtain ⟨T, hT⟩ := eventually_atTop.1 (hlim.eventually hradial)
  let W : ℝ → ℝ := fun t ↦ ‖v t - p‖ ^ 2
  have hW (t : ℝ) : HasDerivAt W (2 * ⟪v t - p, F (v t)⟫) t :=
    ((hv t).sub_const p).norm_sq
  have hmono : MonotoneOn W (Ici T) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici T)
      (continuous_iff_continuousAt.mpr fun t ↦ (hW t).continuousAt).continuousOn
      (fun t _ ↦ (hW t).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(hW t).deriv]
    exact mul_nonneg (by norm_num) (hT t (interior_subset ht))
  have hWlim : Tendsto W atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] using
      (hlim.sub_const p).norm.pow 2
  have hWT : W T ≤ 0 := by
    apply ge_of_tendsto hWlim
    filter_upwards [eventually_ge_atTop T] with t ht
    exact hmono le_rfl ht ht
  have hzero : v T = p := by
    have : ‖v T - p‖ ^ 2 = 0 := le_antisymm hWT (sq_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp this))
  exact eq_const_of_hasDerivAt_of_eq_of_contDiffAt hF hp hv hzero

/-- A coercive linearization makes the nonlinear radial field nonnegative near its
zero. Differentiability controls the remainder by half the coercivity constant. -/
theorem eventually_inner_nonneg_of_hasFDerivAt_of_coercive
    {F : E → E} {p : E} {A : E →L[ℝ] E} {c : ℝ}
    (hD : HasFDerivAt F A p) (hp : F p = 0) (hc : 0 < c)
    (hA : ∀ z, c * ‖z‖ ^ 2 ≤ ⟪z, A z⟫) :
    ∀ᶠ x in 𝓝 p, 0 ≤ ⟪x - p, F x⟫ := by
  filter_upwards [hD.isLittleO.bound (half_pos hc)] with x hx
  simp only [hp, sub_zero] at hx
  have hbound := (abs_real_inner_le_norm (x - p) (F x - A (x - p))).trans
    (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
  have hlower := neg_le_of_abs_le hbound
  rw [inner_sub_right] at hlower
  nlinarith [hA (x - p), sq_nonneg ‖x - p‖]

/-- A strict source cannot be the forward limit of a nonconstant classical trajectory:
if `c ‖z‖² ≤ ⟪z, DF(p) z⟫` with `c > 0`, every trajectory with `v t → p` as `t → ∞`
is constant. -/
theorem eq_const_of_tendsto_atTop_of_fderiv_coercive
    {F : E → E} {p : E} {v : ℝ → E} {c : ℝ}
    (hF : ContDiffAt ℝ 1 F p) (hp : F p = 0) (hc : 0 < c)
    (hA : ∀ z, c * ‖z‖ ^ 2 ≤ ⟪z, fderiv ℝ F p z⟫)
    (hv : ∀ t, HasDerivAt v (F (v t)) t) (hlim : Tendsto v atTop (𝓝 p)) :
    v = fun _ ↦ p := by
  exact eq_const_of_tendsto_atTop_of_inner_nonneg hF hp hv hlim
    (eventually_inner_nonneg_of_hasFDerivAt_of_coercive
      (hF.differentiableAt one_ne_zero).hasFDerivAt hp hc hA)

/-- A strict sink cannot be the backward limit of a nonconstant classical trajectory.
The conclusion follows by reversing time and negating the field. -/
theorem eq_const_of_tendsto_atBot_of_fderiv_neg_coercive
    {F : E → E} {p : E} {v : ℝ → E} {c : ℝ}
    (hF : ContDiffAt ℝ 1 F p) (hp : F p = 0) (hc : 0 < c)
    (hA : ∀ z, c * ‖z‖ ^ 2 ≤ -⟪z, fderiv ℝ F p z⟫)
    (hv : ∀ t, HasDerivAt v (F (v t)) t) (hlim : Tendsto v atBot (𝓝 p)) :
    v = fun _ ↦ p := by
  have hD : HasFDerivAt (fun x ↦ -F x) (-fderiv ℝ F p) p :=
    (hF.differentiableAt one_ne_zero).hasFDerivAt.neg
  have hneg : (fun t ↦ v (-t)) = fun _ : ℝ ↦ p := by
    apply eq_const_of_tendsto_atTop_of_fderiv_coercive hF.neg
      (by simp only [hp, neg_zero]) hc
    · intro z
      simpa only [hD.fderiv, neg_apply, inner_neg_right] using hA z
    · intro t
      simpa only [Function.comp_def, neg_one_smul] using (hv (-t)).scomp t (hasDerivAt_neg t)
    · exact hlim.comp tendsto_neg_atTop_atBot
  funext t
  simpa only [neg_neg] using congrFun hneg (-t)

end InnerProduct

end PDE.Analysis.Evolution
