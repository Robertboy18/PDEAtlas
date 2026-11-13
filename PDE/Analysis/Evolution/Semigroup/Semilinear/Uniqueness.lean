/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Core.Gronwall
public import PDE.Analysis.Evolution.Semigroup.Semilinear.LocalLipschitz
public import PDE.Analysis.Evolution.Semigroup.Semilinear.Restart

/-!
# Uniqueness among continuous semilinear mild solutions

An integral estimate for the difference of two Duhamel terms gives uniqueness
by Grönwall when the nonlinearity is Lipschitz on the union of the solution
traces. Local Lipschitz continuity supplies this bound because those traces
are compact, even in an infinite-dimensional Banach space.

Combining uniqueness with local existence removes the prescribed-ball
restriction on competing solutions. The comparison holds on the whole common
finite interval, without a smallness condition on its length.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Interval

namespace PDE.Analysis.Evolution.StronglyContinuousSemigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A Lipschitz estimate on the union of two solution traces suffices for uniqueness
on their entire common interval. There is no small-time or prescribed-ball restriction. -/
theorem IsMildSolutionOn.eq_of_lipschitzOn_range {T : StronglyContinuousSemigroup E}
    {F : C(E, E)} {x₀ : E} {τ : NNReal}
    {u v : C(Icc (0 : ℝ) (τ : ℝ), E)}
    (hu : T.IsMildSolutionOn F x₀ τ u) (hv : T.IsMildSolutionOn F x₀ τ v)
    {L : NNReal} (hF : LipschitzOnWith L F (range u ∪ range v)) :
    u = v := by
  obtain ⟨C, hC, hbound⟩ := T.exists_norm_le_on_Icc τ
  let M : NNReal := .mk C hC
  let e : ℝ → ℝ := fun t ↦ dist (IccExtend τ.coe_nonneg u t) (IccExtend τ.coe_nonneg v t)
  have he : Continuous e := u.continuous.Icc_extend'.dist v.continuous.Icc_extend'
  have hzero : ∀ t ∈ Icc (0 : ℝ) τ, e t = 0 := by
    apply PDE.Analysis.Evolution.eq_zero_on_of_nonneg_le_mul_intervalIntegral
      (K := C * (L : ℝ)) τ.coe_nonneg he.continuousOn (fun _ _ ↦ dist_nonneg)
    intro t ht
    have hfg : ∀ s ∈ Icc (0 : ℝ) t,
        ‖F (IccExtend τ.coe_nonneg u s) - F (IccExtend τ.coe_nonneg v s)‖ ≤
          (L : ℝ) * e s := by
      intro s _
      rw [← dist_eq_norm]
      exact hF.dist_le_mul _
        (Or.inl ⟨projIcc 0 (τ : ℝ) τ.coe_nonneg s, rfl⟩) _
        (Or.inr ⟨projIcc 0 (τ : ℝ) τ.coe_nonneg s, rfl⟩)
    have hnorm := T.norm_duhamel_sub_le_integral
      (f := fun s ↦ F (IccExtend τ.coe_nonneg u s))
      (g := fun s ↦ F (IccExtend τ.coe_nonneg v s))
      (D := fun s ↦ (L : ℝ) * e s)
      (F.continuous.comp u.continuous.Icc_extend')
      (F.continuous.comp v.continuous.Icc_extend')
      (M := M) hbound ht (continuous_const.mul he) hfg
    have heq : e t =
        ‖T.duhamel (fun s ↦ F (IccExtend τ.coe_nonneg u s)) t -
          T.duhamel (fun s ↦ F (IccExtend τ.coe_nonneg v s)) t‖ := by
      calc
        e t = dist (u ⟨t, ht⟩) (v ⟨t, ht⟩) := by
          dsimp only [e]
          rw [IccExtend_of_mem τ.coe_nonneg u ht, IccExtend_of_mem τ.coe_nonneg v ht]
        _ = dist
            (T t.toNNReal x₀ + T.duhamel (fun s ↦ F (IccExtend τ.coe_nonneg u s)) t)
            (T t.toNNReal x₀ + T.duhamel (fun s ↦ F (IccExtend τ.coe_nonneg v s)) t) :=
          congrArg₂ dist (hu ⟨t, ht⟩) (hv ⟨t, ht⟩)
        _ = _ := by rw [dist_add_left, dist_eq_norm]
    rw [heq]
    simpa only [M, NNReal.coe_mk, intervalIntegral.integral_const_mul, mul_assoc] using hnorm
  ext t
  apply dist_eq_zero.mp
  simpa only [e, IccExtend_val τ.coe_nonneg u t, IccExtend_val τ.coe_nonneg v t] using
    hzero t t.property

/-- Locally Lipschitz nonlinearities give uniqueness among all continuous mild
solutions, since each pair of finite-interval traces has compact union. -/
theorem IsMildSolutionOn.eq_of_locallyLipschitz {T : StronglyContinuousSemigroup E}
    {F : C(E, E)} (hF : LocallyLipschitz F) {x₀ : E} {τ : NNReal}
    {u v : C(Icc (0 : ℝ) (τ : ℝ), E)}
    (hu : T.IsMildSolutionOn F x₀ τ u) (hv : T.IsMildSolutionOn F x₀ τ v) :
    u = v := by
  have hcompact : IsCompact (range u ∪ range v) :=
    (isCompact_range u.continuous).union (isCompact_range v.continuous)
  obtain ⟨L, hL⟩ :=
    LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hcompact hF.locallyLipschitzOn
  exact hu.eq_of_lipschitzOn_range hv hL

/-- The local existence theorem is unique among all continuous mild curves on its
interval, without requiring competitors to stay in the construction's closed ball. -/
theorem exists_pos_existsUnique_mildSolutionOn_of_locallyLipschitz_unrestricted
    (T : StronglyContinuousSemigroup E) {F : C(E, E)}
    (hF : LocallyLipschitz F) (x₀ : E) :
    ∃ τ : NNReal, 0 < τ ∧
      ∃! u : C(Icc (0 : ℝ) (τ : ℝ), E), T.IsMildSolutionOn F x₀ τ u := by
  obtain ⟨_, _, τ, hτ, u, hu, _⟩ :=
    T.exists_pos_existsUnique_mildSolutionOn_of_locallyLipschitz hF x₀
  exact ⟨τ, hτ, u, hu.2, fun v hv ↦ hv.eq_of_locallyLipschitz hF hu.2⟩

end PDE.Analysis.Evolution.StronglyContinuousSemigroup
