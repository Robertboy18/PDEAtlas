/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Semilinear.Basic

/-!
# Restarting and gluing semilinear mild solutions

Splitting the Duhamel integral at an intermediate time gives restriction,
restart, and gluing for continuous mild solutions. The forcing outside the
integration interval is irrelevant, so these identities respect the continuous
extensions used to write the equation.

The semigroup is strongly continuous on a real Banach space. No Lipschitz
hypothesis on the nonlinearity is needed for these identities.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Interval

namespace PDE.Analysis.Evolution.StronglyContinuousSemigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Restrict a continuous curve to a shorter initial interval. -/
def restrictMildCurve {τ σ : NNReal} (hστ : σ ≤ τ)
    (u : C(Icc (0 : ℝ) (τ : ℝ), E)) : C(Icc (0 : ℝ) (σ : ℝ), E) where
  toFun t := u ⟨t, t.property.1, t.property.2.trans hστ⟩
  continuous_toFun := u.continuous.comp
    (continuous_subtype_val.subtype_mk
      (fun t ↦ ⟨t.property.1, t.property.2.trans hστ⟩))

omit [CompleteSpace E] in
/-- Restriction preserves the mild equation and its initial state. -/
theorem IsMildSolutionOn.restrict {T : StronglyContinuousSemigroup E}
    {F : C(E, E)} {x₀ : E} {τ σ : NNReal}
    {u : C(Icc (0 : ℝ) (τ : ℝ), E)}
    (hu : T.IsMildSolutionOn F x₀ τ u) (hστ : σ ≤ τ) :
    T.IsMildSolutionOn F x₀ σ (restrictMildCurve hστ u) := by
  intro t
  have htτ : (t : ℝ) ∈ Icc (0 : ℝ) τ :=
    ⟨t.property.1, t.property.2.trans hστ⟩
  change u ⟨t, htτ⟩ = _
  rw [hu ⟨t, htτ⟩]
  congr 1
  apply T.duhamel_congr t.property.1
  intro s hs
  have hsσ : s ∈ Icc (0 : ℝ) σ := ⟨hs.1, hs.2.trans t.property.2⟩
  have hsτ : s ∈ Icc (0 : ℝ) τ := ⟨hs.1, hsσ.2.trans hστ⟩
  change F (IccExtend τ.coe_nonneg u s) =
    F (IccExtend σ.coe_nonneg (restrictMildCurve hστ u) s)
  rw [IccExtend_of_mem τ.coe_nonneg u hsτ,
    IccExtend_of_mem σ.coe_nonneg (restrictMildCurve hστ u) hsσ]
  rfl

omit [CompleteSpace E] in
/-- View the segment starting at `a` as a curve whose initial time is zero. -/
def restartMildCurve {τ : NNReal} (u : C(Icc (0 : ℝ) (τ : ℝ), E))
    (a σ : NNReal) : C(Icc (0 : ℝ) (σ : ℝ), E) where
  toFun t := IccExtend τ.coe_nonneg u ((a : ℝ) + t)
  continuous_toFun := u.continuous.Icc_extend'.comp
    (continuous_const.add continuous_subtype_val)

/-- A later segment solves the same autonomous mild equation, with initial state
equal to the earlier solution at the restart time. -/
theorem IsMildSolutionOn.restart {T : StronglyContinuousSemigroup E}
    {F : C(E, E)} {x₀ : E} {τ : NNReal}
    {u : C(Icc (0 : ℝ) (τ : ℝ), E)}
    (hu : T.IsMildSolutionOn F x₀ τ u)
    (a σ : NNReal) (haσ : a + σ ≤ τ) :
    T.IsMildSolutionOn F (IccExtend τ.coe_nonneg u a) σ (restartMildCurve u a σ) := by
  have ha : (a : ℝ) ∈ Icc (0 : ℝ) τ :=
    ⟨a.coe_nonneg, (le_add_of_nonneg_right σ.coe_nonneg).trans haσ⟩
  let f : ℝ → E := fun s ↦ F (IccExtend τ.coe_nonneg u s)
  have hf : Continuous f := F.continuous.comp u.continuous.Icc_extend'
  have hua : IccExtend τ.coe_nonneg u a = T a x₀ + T.duhamel f a := by
    have h := hu ⟨(a : ℝ), ha⟩
    change u ⟨(a : ℝ), ha⟩ =
      T (a : ℝ).toNNReal x₀ + T.duhamel f (a : ℝ) at h
    rw [Real.toNNReal_coe] at h
    exact (IccExtend_of_mem τ.coe_nonneg u ha).trans h
  intro t
  have hat : (a : ℝ) + t ∈ Icc (0 : ℝ) τ :=
    ⟨add_nonneg a.coe_nonneg t.property.1,
      (add_le_add le_rfl t.property.2).trans haσ⟩
  have hforcing :
      T.duhamel (fun s ↦ f ((a : ℝ) + s)) t =
        T.duhamel (fun s ↦ F (IccExtend σ.coe_nonneg (restartMildCurve u a σ) s)) t := by
    apply T.duhamel_congr t.property.1
    intro s hs
    have hsσ : s ∈ Icc (0 : ℝ) σ := ⟨hs.1, hs.2.trans t.property.2⟩
    change f ((a : ℝ) + s) = F (IccExtend σ.coe_nonneg (restartMildCurve u a σ) s)
    rw [IccExtend_of_mem σ.coe_nonneg (restartMildCurve u a σ) hsσ]
    rfl
  change IccExtend τ.coe_nonneg u ((a : ℝ) + t) = _
  rw [IccExtend_of_mem τ.coe_nonneg u hat, hu ⟨(a : ℝ) + t, hat⟩]
  change T ((a : ℝ) + t).toNNReal x₀ + T.duhamel f ((a : ℝ) + t) = _
  rw [T.duhamel_add hf a.coe_nonneg t.property.1, hforcing, hua,
    (T (t : ℝ).toNNReal).map_add]
  rw [Real.toNNReal_add a.coe_nonneg t.property.1, Real.toNNReal_coe,
    T.map_add_apply, T.map_apply_comm]
  abel

omit [CompleteSpace E] in
/-- Concatenate two continuous curves whose values agree at the joining time. -/
def glueMildCurves {τ σ : NNReal}
    (u : C(Icc (0 : ℝ) (τ : ℝ), E))
    (v : C(Icc (0 : ℝ) (σ : ℝ), E))
    (hmatch : u ⟨τ, τ.coe_nonneg, le_rfl⟩ = v ⟨0, le_rfl, σ.coe_nonneg⟩) :
    C(Icc (0 : ℝ) ((τ + σ : NNReal) : ℝ), E) := by
  classical
  let f := IccExtend τ.coe_nonneg u
  let g : ℝ → E := fun t ↦ IccExtend σ.coe_nonneg v (t - τ)
  have hf : Continuous f := u.continuous.Icc_extend'
  have hg : Continuous g :=
    v.continuous.Icc_extend'.comp (continuous_id.sub continuous_const)
  have hfg : ∀ t ∈ frontier (Iic (τ : ℝ)), f t = g t := by
    intro t ht
    have htτ : t = τ := by simpa only [frontier_Iic, mem_singleton_iff] using ht
    subst t
    change IccExtend τ.coe_nonneg u τ = IccExtend σ.coe_nonneg v ((τ : ℝ) - τ)
    rw [sub_self, IccExtend_right τ.coe_nonneg u, IccExtend_left σ.coe_nonneg v]
    exact hmatch
  exact {
    toFun := fun t ↦ (Iic (τ : ℝ)).piecewise f g t
    continuous_toFun := (Continuous.piecewise hfg hf hg).comp continuous_subtype_val }

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- Before the joining time, concatenation agrees with the first curve. -/
theorem glueMildCurves_apply_left {τ σ : NNReal}
    (u : C(Icc (0 : ℝ) (τ : ℝ), E))
    (v : C(Icc (0 : ℝ) (σ : ℝ), E))
    (hmatch : u ⟨τ, τ.coe_nonneg, le_rfl⟩ = v ⟨0, le_rfl, σ.coe_nonneg⟩)
    (t : Icc (0 : ℝ) ((τ + σ : NNReal) : ℝ)) (ht : (t : ℝ) ≤ τ) :
    glueMildCurves u v hmatch t = IccExtend τ.coe_nonneg u t := by
  classical
  change (Iic (τ : ℝ)).piecewise (IccExtend τ.coe_nonneg u)
    (fun s ↦ IccExtend σ.coe_nonneg v (s - τ)) (t : ℝ) = _
  exact piecewise_eq_of_mem (Iic (τ : ℝ)) _ _ ht

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- At and after the joining time, concatenation agrees with the translated second curve. -/
theorem glueMildCurves_apply_right {τ σ : NNReal}
    (u : C(Icc (0 : ℝ) (τ : ℝ), E))
    (v : C(Icc (0 : ℝ) (σ : ℝ), E))
    (hmatch : u ⟨τ, τ.coe_nonneg, le_rfl⟩ = v ⟨0, le_rfl, σ.coe_nonneg⟩)
    (t : Icc (0 : ℝ) ((τ + σ : NNReal) : ℝ)) (ht : (τ : ℝ) ≤ t) :
    glueMildCurves u v hmatch t = IccExtend σ.coe_nonneg v ((t : ℝ) - τ) := by
  classical
  rcases ht.eq_or_lt with h | h
  · have heq : (t : ℝ) = τ := h.symm
    rw [glueMildCurves_apply_left u v hmatch t heq.le, heq]
    rw [sub_self, IccExtend_right τ.coe_nonneg u, IccExtend_left σ.coe_nonneg v]
    exact hmatch
  · change (Iic (τ : ℝ)).piecewise (IccExtend τ.coe_nonneg u)
      (fun s ↦ IccExtend σ.coe_nonneg v (s - τ)) (t : ℝ) = _
    exact piecewise_eq_of_notMem (Iic (τ : ℝ)) _ _ (not_le.mpr h)

/-- Concatenating a mild solution with a solution starting at its terminal state
gives a mild solution on the combined interval. -/
theorem IsMildSolutionOn.glue {T : StronglyContinuousSemigroup E}
    {F : C(E, E)} {x₀ : E} {τ σ : NNReal}
    {u : C(Icc (0 : ℝ) (τ : ℝ), E)}
    {v : C(Icc (0 : ℝ) (σ : ℝ), E)}
    (hu : T.IsMildSolutionOn F x₀ τ u)
    (hv : T.IsMildSolutionOn F (u ⟨τ, τ.coe_nonneg, le_rfl⟩) σ v) :
    T.IsMildSolutionOn F x₀ (τ + σ)
      (glueMildCurves u v hv.initial_value.symm) := by
  let w := glueMildCurves u v hv.initial_value.symm
  let f : ℝ → E := fun s ↦ F (IccExtend (τ + σ).coe_nonneg w s)
  let fu : ℝ → E := fun s ↦ F (IccExtend τ.coe_nonneg u s)
  let fv : ℝ → E := fun s ↦ F (IccExtend σ.coe_nonneg v s)
  have hf : Continuous f := F.continuous.comp w.continuous.Icc_extend'
  have hleft (s : ℝ) (hs : s ∈ Icc (0 : ℝ) τ) : f s = fu s := by
    have hsall : s ∈ Icc (0 : ℝ) ((τ + σ : NNReal) : ℝ) :=
      ⟨hs.1, hs.2.trans (le_add_of_nonneg_right σ.coe_nonneg)⟩
    dsimp only [f, fu]
    rw [IccExtend_of_mem (τ + σ).coe_nonneg w hsall]
    rw [glueMildCurves_apply_left u v hv.initial_value.symm _ hs.2]
  have hright (s : ℝ) (hs : s ∈ Icc (0 : ℝ) σ) :
      f ((τ : ℝ) + s) = fv s := by
    have hsall : (τ : ℝ) + s ∈ Icc (0 : ℝ) ((τ + σ : NNReal) : ℝ) :=
      ⟨add_nonneg τ.coe_nonneg hs.1, add_le_add le_rfl hs.2⟩
    dsimp only [f, fv]
    rw [IccExtend_of_mem (τ + σ).coe_nonneg w hsall,
      glueMildCurves_apply_right u v hv.initial_value.symm _
        (le_add_of_nonneg_right hs.1)]
    simp only [add_sub_cancel_left]
  have hJτ : T.duhamel f τ = T.duhamel fu τ :=
    T.duhamel_congr τ.coe_nonneg fun s hs ↦ hleft s hs
  intro t
  change w t = T (t : ℝ).toNNReal x₀ + T.duhamel f t
  by_cases ht : (t : ℝ) ≤ τ
  · have htτ : (t : ℝ) ∈ Icc (0 : ℝ) τ := ⟨t.property.1, ht⟩
    have hJt : T.duhamel f t = T.duhamel fu t :=
      T.duhamel_congr t.property.1 fun s hs ↦
        hleft s ⟨hs.1, hs.2.trans ht⟩
    rw [glueMildCurves_apply_left u v hv.initial_value.symm _ ht,
      IccExtend_of_mem τ.coe_nonneg u htτ, hJt]
    exact hu ⟨t, htτ⟩
  · have hτt : (τ : ℝ) ≤ t := (not_le.mp ht).le
    have hdelay : (t : ℝ) - τ ∈ Icc (0 : ℝ) σ :=
      ⟨sub_nonneg.mpr hτt, by exact sub_le_iff_le_add.mpr (by
        simpa only [NNReal.coe_add, add_comm] using t.property.2)⟩
    have htadd : (t : ℝ) = τ + ((t : ℝ) - τ) := by ring
    have hJlate :
        T.duhamel (fun s ↦ f ((τ : ℝ) + s)) ((t : ℝ) - τ) =
          T.duhamel fv ((t : ℝ) - τ) :=
      T.duhamel_congr hdelay.1 fun s hs ↦
        hright s ⟨hs.1, hs.2.trans hdelay.2⟩
    have hJt :
        T.duhamel f t =
          T ((t : ℝ) - τ).toNNReal (T.duhamel fu τ) +
            T.duhamel fv ((t : ℝ) - τ) := by
      conv_lhs => rw [htadd]
      rw [T.duhamel_add hf τ.coe_nonneg hdelay.1, hJτ, hJlate]
    have hS :
        T (t : ℝ).toNNReal x₀ =
          T ((t : ℝ) - τ).toNNReal (T τ x₀) := by
      conv_lhs => rw [htadd]
      rw [Real.toNNReal_add τ.coe_nonneg hdelay.1, Real.toNNReal_coe,
        T.map_add_apply, T.map_apply_comm]
    rw [glueMildCurves_apply_right u v hv.initial_value.symm _ hτt,
      IccExtend_of_mem σ.coe_nonneg v hdelay, hv ⟨(t : ℝ) - τ, hdelay⟩,
      hu ⟨τ, τ.coe_nonneg, le_rfl⟩, hJt, hS]
    simp only [Real.toNNReal_coe, (T ((t : ℝ) - τ).toNNReal).map_add]
    change
      T ((t : ℝ) - τ).toNNReal (T τ x₀) +
          T ((t : ℝ) - τ).toNNReal (T.duhamel fu τ) +
            T.duhamel fv ((t : ℝ) - τ) =
        T ((t : ℝ) - τ).toNNReal (T τ x₀) +
          (T ((t : ℝ) - τ).toNNReal (T.duhamel fu τ) +
            T.duhamel fv ((t : ℝ) - τ))
    exact add_assoc _ _ _

end PDE.Analysis.Evolution.StronglyContinuousSemigroup
