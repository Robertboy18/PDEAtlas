/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.FaaDiBrunoBounds
public import PDE.Analysis.ODE.Flow.HigherVariation
public import PDE.Analysis.ODE.Flow.IntegralEstimates
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Higher-order estimates for flows of fields smooth in space

For a field `v` that is `C¹` with bounded derivative and a smooth family of order `m` in space
(`PDE.Analysis.IsSmoothFamilyOn`), the derivatives of order `j ≤ m` of the flow maps
`X(s) = flowOn v a b s t` solve `∂ₛ D^j X(s) x = D^j (v s ∘ X(s)) x` within `[a, b]`
(`IsC1FieldOn.hasDerivWithinAt_iteratedFDeriv_flowOn`). The proof writes the flow map as the
identity plus the integral of the field along the flow and differentiates under the integral sign
(`iteratedFDeriv_integral_of_isSmoothFamilyOn`).

With the Faà di Bruno bounds in which the top-order terms are separated
(`norm_iteratedFDeriv_comp_le_add`, `norm_iteratedFDeriv_comp_sub_le_add`) and Grönwall's
inequality, this gives the estimates below on a set `S` preserved by the flows, on both sides
of the base time.

## Main definitions

* `flowDerivBound`: explicit bounds of all orders of the derivatives of the flow maps from
  constant bounds of the derivatives of the field.
* `flowHolderRate`: the rate of growth of the `α`-Hölder constant of the top-order derivative
  `D^m X(s)`.

## Main results

* `IsC1FieldOn.norm_iteratedFDeriv_flowOn_le`: a bound of `D^j X(s)` linear in the integral of a
  time-dependent bound of `D^j v`.
* `IsC1FieldOn.norm_iteratedFDeriv_flowOn_le_flowDerivBound`: if the derivatives of `v` of orders
  `1 ≤ i ≤ m` are at most `K i`, then `‖D^j X(s) x‖ ≤ flowDerivBound K (b - a) j` for `1 ≤ j ≤ m`.
* `IsC1FieldOn.norm_iteratedFDeriv_flowOn_le_of_top`: the bound of the top order, linear in a
  time-dependent bound of `D^m v`.
* `IsC1FieldOn.norm_iteratedFDeriv_flowOn_sub_le_rpow`: an `α`-Hölder bound of `D^m X(s)` at
  points at distance at most one, linear in the integrals of the bound and of the Hölder constant
  of `D^m v`.
* `IsC1FieldOn.norm_iteratedFDeriv_flowOn_sub_le_max_rpow`: the `α`-Hölder bound of `D^m X(s)`
  for all points of `S`.
* `IsC1FieldOn.norm_iteratedFDeriv_flowOn_sub_flowOn_le`: if `D^j (v r ∘ X(r)) x` is at most `B`,
  then `D^j X(s) x` is `B`-Lipschitz in the final time `s`.
* `IsC1FieldOn.norm_iteratedFDeriv_flowOn_sub_flowOn_le_of_bounds`: the same Lipschitz bound in
  the final time from constant bounds of the derivatives of the field.
-/

@[expose] public section

open Set Filter Metric ContinuousLinearMap MeasureTheory
open scoped NNReal Topology Interval

noncomputable section

namespace PDE.Analysis.ODE

universe u

section Integral

variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {G : ℝ → E → F} {a b t r : ℝ}

omit [FiniteDimensional ℝ E] in
/-- For a smooth family of order `m`, the derivatives of order `j ≤ m` at a fixed point are
continuous in time. -/
theorem continuousOn_iteratedFDeriv_slice {m j : ℕ} (hG : IsSmoothFamilyOn m G (Icc a b))
    (hj : j ≤ m) (x : E) : ContinuousOn (fun ρ ↦ iteratedFDeriv ℝ j (G ρ) x) (Icc a b) :=
  (hG.continuousOn_iteratedFDeriv hj).comp (continuous_id.prodMk continuous_const).continuousOn
    fun _ hρ ↦ ⟨hρ, mem_univ _⟩

omit [FiniteDimensional ℝ E] in
/-- A smooth family is continuous in time at a fixed point. -/
theorem continuousOn_slice {m : ℕ} (hG : IsSmoothFamilyOn m G (Icc a b)) (x : E) :
    ContinuousOn (fun ρ ↦ G ρ x) (Icc a b) :=
  hG.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
    fun _ hρ ↦ ⟨hρ, mem_univ _⟩

/-- **Differentiation under the integral sign** for a smooth family of order one. -/
theorem hasFDerivAt_integral_of_isSmoothFamilyOn
    (hG : IsSmoothFamilyOn 1 G (Icc a b)) (ht : t ∈ Icc a b) (hr : r ∈ Icc a b) (x : E) :
    HasFDerivAt (fun y ↦ ∫ ρ in t..r, G ρ y) (∫ ρ in t..r, fderiv ℝ (G ρ) x) x := by
  have hsub : uIcc t r ⊆ Icc a b := uIcc_subset_Icc ht hr
  have hD : IsSmoothFamilyOn 0 (fun ρ y ↦ fderiv ℝ (G ρ) y) (Icc a b) :=
    (isSmoothFamilyOn_succ_iff.mp hG).2.2
  have hDc := isSmoothFamilyOn_zero_iff.mp hD
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_closedBall x 1)).exists_bound_of_continuousOn
    (hDc.mono fun (p : ℝ × E) (hp : p ∈ Icc a b ×ˢ closedBall x 1) ↦ ⟨hp.1, mem_univ _⟩)
  have hmeas {f : ℝ → F} (hf : ContinuousOn f (Icc a b)) :
      AEStronglyMeasurable f (volume.restrict (Ι t r)) :=
    (hf.aestronglyMeasurable measurableSet_Icc).mono_set (uIoc_subset_uIcc.trans hsub)
  have hmeas' {f : ℝ → E →L[ℝ] F} (hf : ContinuousOn f (Icc a b)) :
      AEStronglyMeasurable f (volume.restrict (Ι t r)) :=
    (hf.aestronglyMeasurable measurableSet_Icc).mono_set (uIoc_subset_uIcc.trans hsub)
  have hDx : ContinuousOn (fun ρ ↦ fderiv ℝ (G ρ) x) (Icc a b) :=
    hDc.comp (continuous_id.prodMk continuous_const).continuousOn fun _ hρ ↦ ⟨hρ, mem_univ _⟩
  exact intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := volume) (a := t) (b := r) (F := fun y ρ ↦ G ρ y) (F' := fun y ρ ↦ fderiv ℝ (G ρ) y)
    (x₀ := x) (bound := fun _ ↦ C) (ball_mem_nhds x one_pos)
    (Eventually.of_forall fun z ↦ hmeas (continuousOn_slice hG z))
    ((continuousOn_slice hG x).mono hsub).intervalIntegrable
    (hmeas' hDx)
    (Eventually.of_forall fun ρ hρ z hz ↦
      hC (ρ, z) ⟨hsub (uIoc_subset_uIcc hρ), ball_subset_closedBall hz⟩)
    intervalIntegrable_const
    (Eventually.of_forall fun ρ hρ z _ ↦
      ((hG.contDiff (hsub (uIoc_subset_uIcc hρ))).differentiable one_ne_zero z).hasFDerivAt)

/-- **Iterated differentiation under the integral sign.** For a smooth family of order `m`, the
derivatives of order `j ≤ m` of `y ↦ ∫ₜʳ G ρ y dρ` are the integrals of the derivatives. -/
theorem iteratedFDeriv_integral_of_isSmoothFamilyOn [CompleteSpace F] {m : ℕ}
    (hG : IsSmoothFamilyOn m G (Icc a b)) (ht : t ∈ Icc a b) (hr : r ∈ Icc a b) {j : ℕ}
    (hj : j ≤ m) (x : E) :
    iteratedFDeriv ℝ j (fun y ↦ ∫ ρ in t..r, G ρ y) x =
      ∫ ρ in t..r, iteratedFDeriv ℝ j (G ρ) x := by
  induction j generalizing F m with
  | zero =>
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
    exact ((continuousMultilinearCurryFin0 ℝ E F).symm.toLinearIsometry.intervalIntegral_comp_comm
      fun ρ ↦ G ρ x).symm
  | succ j ih =>
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hG1 : IsSmoothFamilyOn 1 G (Icc a b) := hG.mono (by omega)
    have hD : IsSmoothFamilyOn m (fun ρ y ↦ fderiv ℝ (G ρ) y) (Icc a b) :=
      (isSmoothFamilyOn_succ_iff.mp hG).2.2
    have hfd : (fun y ↦ fderiv ℝ (fun z ↦ ∫ ρ in t..r, G ρ z) y) =
        fun y ↦ ∫ ρ in t..r, fderiv ℝ (G ρ) y :=
      funext fun y ↦ (hasFDerivAt_integral_of_isSmoothFamilyOn hG1 ht hr y).fderiv
    rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply, hfd,
      ih hD (by omega)]
    have h := ((continuousMultilinearCurryRightEquiv' ℝ j E F).symm.toLinearIsometry
      ).intervalIntegral_comp_comm (a := t) (b := r) (μ := volume)
      (fun ρ ↦ iteratedFDeriv ℝ j (fun y ↦ fderiv ℝ (G ρ) y) x)
    simp only [LinearIsometryEquiv.coe_toLinearIsometry] at h
    rw [← h]
    refine intervalIntegral.integral_congr fun ρ _ ↦ ?_
    rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply]

end Integral

/-! ### The equations of the derivatives of the flow maps -/

section Flow

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {v : ℝ → E → E} {Dv : ℝ → E → E →L[ℝ] E} {a b t : ℝ} {K : ℝ≥0} {m : ℕ}

omit [FiniteDimensional ℝ E] in
/-- The derivatives of order at least two of the identity vanish. -/
theorem iteratedFDeriv_id_eq_zero {j : ℕ} (hj : 2 ≤ j) (x : E) :
    iteratedFDeriv ℝ j (fun y : E ↦ y) x = 0 := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 + 1 := ⟨j - 2, by omega⟩
  rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply]
  have hfd : (fun y : E ↦ fderiv ℝ (fun z : E ↦ z) y) = fun _ ↦ ContinuousLinearMap.id ℝ E :=
    funext fun y ↦ fderiv_fun_id
  rw [hfd, iteratedFDeriv_const_of_ne (Nat.succ_ne_zero i), Pi.zero_apply, map_zero]

/-- A flow line is its initial point plus the integral of the field along it. -/
theorem IsLipschitzFieldOn.flowOn_eq_add_integral (hv : IsLipschitzFieldOn v a b K)
    (ht : t ∈ Icc a b) {r : ℝ} (hr : r ∈ Icc a b) (y : E) :
    flowOn v a b r t y = y + ∫ ρ in t..r, v ρ (flowOn v a b ρ t y) := by
  have hsub : uIcc t r ⊆ Icc a b := uIcc_subset_Icc ht hr
  have hc : ContinuousOn (fun ρ ↦ v ρ (flowOn v a b ρ t y)) (Icc a b) :=
    hv.continuousOn.comp (continuousOn_id.prodMk (hv.continuousOn_flowOn_time ht y))
      fun ρ hρ ↦ ⟨hρ, mem_univ _⟩
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun ρ hρ ↦ hv.hasDerivAt_flowOn (hsub hρ) ht y) ((hc.mono hsub).intervalIntegrable),
    hv.flowOn_self ht]
  abel

/-- The field along the flow, `(ρ, y) ↦ v ρ (flowOn v a b ρ t y)`, is a smooth family. -/
theorem IsC1FieldOn.isSmoothFamilyOn_comp_flowOn (hv : IsC1FieldOn v Dv a b K)
    (hsm : IsSmoothFamilyOn m v (Icc a b)) (ht : t ∈ Icc a b) :
    IsSmoothFamilyOn m (fun ρ y ↦ v ρ (flowOn v a b ρ t y)) (Icc a b) :=
  hsm.comp (hv.isSmoothFamilyOn_flowOn hsm ht)

/-- **The equation of the derivatives of the flow maps.** For `j ≤ m` the derivative of order `j`
of the flow map solves `∂ᵣ D^j X(r) = D^j (v r ∘ X(r))` within `[a, b]`. -/
theorem IsC1FieldOn.hasDerivWithinAt_iteratedFDeriv_flowOn (hv : IsC1FieldOn v Dv a b K)
    (hsm : IsSmoothFamilyOn m v (Icc a b)) (ht : t ∈ Icc a b) {j : ℕ} (hj : j ≤ m) (x : E)
    {r : ℝ} (hr : r ∈ Icc a b) :
    HasDerivWithinAt (fun s ↦ iteratedFDeriv ℝ j (flowOn v a b s t) x)
      (iteratedFDeriv ℝ j (fun y ↦ v r (flowOn v a b r t y)) x) (Icc a b) r := by
  have hL := hv.isLipschitzFieldOn
  have hG := hv.isSmoothFamilyOn_comp_flowOn hsm ht
  have hX := hv.isSmoothFamilyOn_flowOn hsm ht
  have heq (s : ℝ) (hs : s ∈ Icc a b) :
      iteratedFDeriv ℝ j (flowOn v a b s t) x = iteratedFDeriv ℝ j (fun y : E ↦ y) x +
        ∫ ρ in t..s, iteratedFDeriv ℝ j (fun y ↦ v ρ (flowOn v a b ρ t y)) x := by
    have hfun : flowOn v a b s t =
        (fun y : E ↦ y) + fun y ↦ ∫ ρ in t..s, v ρ (flowOn v a b ρ t y) :=
      funext fun y ↦ hL.flowOn_eq_add_integral ht hs y
    have hI : ContDiff ℝ j (fun y ↦ ∫ ρ in t..s, v ρ (flowOn v a b ρ t y)) := by
      simpa only [hfun, Pi.add_apply, id_eq, add_sub_cancel_left] using ((hX.contDiff hs).of_le
        (show ((j : ℕ) : WithTop ℕ∞) ≤ (m : WithTop ℕ∞) by exact_mod_cast hj)).sub contDiff_id
    rw [hfun, iteratedFDeriv_add_apply (f := fun y : E ↦ y) contDiff_id.contDiffAt
      hI.contDiffAt,
      iteratedFDeriv_integral_of_isSmoothFamilyOn hG ht hs hj x]
  have hφ := continuousOn_iteratedFDeriv_slice hG hj x
  have : Fact (r ∈ Icc a b) := ⟨hr⟩
  have h := (intervalIntegral.integral_hasDerivWithinAt_right (s := Icc a b)
    (hφ.mono (uIcc_subset_Icc ht hr)).intervalIntegrable
    (hφ.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc r) (hφ r hr)).const_add
    (iteratedFDeriv ℝ j (fun y : E ↦ y) x)
  exact h.congr (fun s hs ↦ heq s hs) (heq r hr)

end Flow

/-! ### Compositions with the top-order terms separated, for global derivatives -/

section Composition

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] {g : F → G} {f : E → F} {n : ℕ}

/-- **Faà di Bruno with separated top terms**, for global derivatives:
`‖D^n (g ∘ f)‖ ≤ ‖Dg(f x)‖ ‖D^n f x‖ + ‖D^n g(f x)‖ ‖D f x‖^n + c_n M max(1, F)^n` when the
derivatives of `g` of orders `2 ≤ i < n` at `f x` are at most `M` and those of `f` of orders
`1 ≤ i < n` at `x` at most `F`. -/
theorem norm_iteratedFDeriv_comp_le_add (hg : ContDiff ℝ n g) (hf : ContDiff ℝ n f)
    (hn : 2 ≤ n) (x : E) {M F₀ : ℝ} (hM : 0 ≤ M)
    (hgb : ∀ i, 2 ≤ i → i < n → ‖iteratedFDeriv ℝ i g (f x)‖ ≤ M)
    (hfb : ∀ i, 1 ≤ i → i < n → ‖iteratedFDeriv ℝ i f x‖ ≤ F₀) :
    ‖iteratedFDeriv ℝ n (fun y ↦ g (f y)) x‖ ≤
      ‖fderiv ℝ g (f x)‖ * ‖iteratedFDeriv ℝ n f x‖ +
        ‖iteratedFDeriv ℝ n g (f x)‖ * ‖fderiv ℝ f x‖ ^ n +
          Fintype.card (OrderedFinpartition n) * (M * max 1 F₀ ^ n) := by
  have h := PDE.Analysis.norm_iteratedFDerivWithin_comp_le_add hg.contDiffOn hf.contDiffOn
    uniqueDiffOn_univ uniqueDiffOn_univ (mapsTo_univ _ _) (mem_univ x) hn hM
    (by simpa only [iteratedFDerivWithin_univ] using hgb)
    (by simpa only [iteratedFDerivWithin_univ] using hfb)
  simpa only [iteratedFDerivWithin_univ, fderivWithin_univ, Function.comp_def] using h

/-- **Faà di Bruno at two points with separated top terms**, for global derivatives. -/
theorem norm_iteratedFDeriv_comp_sub_le_add (hg : ContDiff ℝ n g) (hf : ContDiff ℝ n f)
    (hn : 2 ≤ n) (x y : E) {Mg Mf δg δf : ℝ} (hMg : 0 ≤ Mg) (hMf : 0 ≤ Mf) (hδg : 0 ≤ δg)
    (hδf : 0 ≤ δf) (hgb : ∀ i, 2 ≤ i → i < n → ‖iteratedFDeriv ℝ i g (f x)‖ ≤ Mg)
    (hgd : ∀ i, 2 ≤ i → i < n →
      ‖iteratedFDeriv ℝ i g (f x) - iteratedFDeriv ℝ i g (f y)‖ ≤ δg)
    (hfx : ∀ j, 1 ≤ j → j < n → ‖iteratedFDeriv ℝ j f x‖ ≤ Mf)
    (hfy : ∀ j, 1 ≤ j → j < n → ‖iteratedFDeriv ℝ j f y‖ ≤ Mf)
    (hfd : ∀ j, 1 ≤ j → j < n → ‖iteratedFDeriv ℝ j f x - iteratedFDeriv ℝ j f y‖ ≤ δf) :
    ‖iteratedFDeriv ℝ n (fun z ↦ g (f z)) x - iteratedFDeriv ℝ n (fun z ↦ g (f z)) y‖ ≤
      ‖fderiv ℝ g (f x)‖ * ‖iteratedFDeriv ℝ n f x - iteratedFDeriv ℝ n f y‖ +
        ‖fderiv ℝ g (f x) - fderiv ℝ g (f y)‖ * ‖iteratedFDeriv ℝ n f y‖ +
        (‖iteratedFDeriv ℝ n g (f x)‖ * n * max ‖fderiv ℝ f x‖ ‖fderiv ℝ f y‖ ^ (n - 1) *
            ‖fderiv ℝ f x - fderiv ℝ f y‖ +
          ‖iteratedFDeriv ℝ n g (f x) - iteratedFDeriv ℝ n g (f y)‖ * ‖fderiv ℝ f y‖ ^ n) +
        Fintype.card (OrderedFinpartition n) * ((Mg * n * δf + δg) * max 1 Mf ^ n) := by
  have h := PDE.Analysis.norm_iteratedFDerivWithin_comp_sub_le_add hg.contDiffOn hf.contDiffOn
    uniqueDiffOn_univ uniqueDiffOn_univ (mapsTo_univ _ _) (mem_univ x) (mem_univ y) hn hMg hMf
    hδg hδf (by simpa only [iteratedFDerivWithin_univ] using hgb)
    (by simpa only [iteratedFDerivWithin_univ] using hgd)
    (by simpa only [iteratedFDerivWithin_univ] using hfx)
    (by simpa only [iteratedFDerivWithin_univ] using hfy)
    (by simpa only [iteratedFDerivWithin_univ] using hfd)
  simpa only [iteratedFDerivWithin_univ, fderivWithin_univ, Function.comp_def] using h

/-- On a convex set, a bound `B` of the derivative of order `i + 1` makes the derivative of order
`i` `B`-Lipschitz. -/
theorem norm_iteratedFDeriv_sub_le_of_convex {S : Set E} (hS : Convex ℝ S) {i : ℕ}
    (hf : ContDiff ℝ (i + 1) f) {B : ℝ} (hB : ∀ z ∈ S, ‖iteratedFDeriv ℝ (i + 1) f z‖ ≤ B)
    {z z' : E} (hz : z ∈ S) (hz' : z' ∈ S) :
    ‖iteratedFDeriv ℝ i f z - iteratedFDeriv ℝ i f z'‖ ≤ B * ‖z - z'‖ := by
  have hd : Differentiable ℝ (iteratedFDeriv ℝ i f) :=
    hf.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self i)
  exact hS.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun w _ ↦ (hd w).hasFDerivAt.hasFDerivWithinAt)
    (fun w hw ↦ by rw [norm_fderiv_iteratedFDeriv]; exact hB w hw) hz' hz

/-- The first derivatives differ by as much as the derivatives of order one. -/
theorem norm_fderiv_sub_eq (f : E → F) (z z' : E) :
    ‖fderiv ℝ f z - fderiv ℝ f z'‖ = ‖iteratedFDeriv ℝ 1 f z - iteratedFDeriv ℝ 1 f z'‖ := by
  have h := PDE.Analysis.norm_iteratedFDerivWithin_one_sub (f := f) (s := univ) (x := z) (y := z')
    uniqueDiffWithinAt_univ uniqueDiffWithinAt_univ
  simp only [iteratedFDerivWithin_univ, fderivWithin_univ] at h
  exact h.symm

end Composition

/-! ### Bounds of the derivatives of the flow maps on an invariant set -/

section Bounds

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {v : ℝ → E → E} {Dv : ℝ → E → E →L[ℝ] E} {a b t : ℝ} {K : ℝ≥0} {m : ℕ} {S : Set E}

/-- At the base time the flow map is the identity. -/
theorem IsLipschitzFieldOn.flowOn_self_eq (hv : IsLipschitzFieldOn v a b K) (ht : t ∈ Icc a b) :
    flowOn v a b t t = fun y ↦ y :=
  funext fun y ↦ hv.flowOn_self ht y

/-- **Grönwall's inequality from an interior base time with zero initial value.** If
`‖f'‖ ≤ K₁ ‖f‖ + g` on `[a, b]` with `g ≥ 0` continuous and `f t = 0`, then
`‖f s‖ ≤ |∫ₜˢ g| exp (K₁ |s - t|)` on both sides of `t`. -/
theorem norm_le_abs_integral_mul_exp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f f' : ℝ → F} {g : ℝ → ℝ} {K₁ : ℝ} (ht : t ∈ Icc a b)
    (hf : ∀ r ∈ Icc a b, HasDerivWithinAt f (f' r) (Icc a b) r) (hK₁ : 0 ≤ K₁)
    (hg : ContinuousOn g (Icc a b)) (hg0 : ∀ r ∈ Icc a b, 0 ≤ g r) (h0 : ‖f t‖ ≤ 0)
    (bound : ∀ r ∈ Icc a b, ‖f' r‖ ≤ K₁ * ‖f r‖ + g r) {s : ℝ} (hs : s ∈ Icc a b) :
    ‖f s‖ ≤ |∫ r in t..s, g r| * Real.exp (K₁ * |s - t|) := by
  rcases le_total t s with hts | hst
  · have h := norm_le_mul_exp_integral (a := t) (b := b) (A := fun _ ↦ K₁) (g := g)
      (fun r hr ↦ (hf r ⟨ht.1.trans hr.1, hr.2⟩).mono (Icc_subset_Icc ht.1 le_rfl))
      continuousOn_const (fun _ _ ↦ hK₁) (hg.mono (Icc_subset_Icc ht.1 le_rfl))
      (fun r hr ↦ hg0 r ⟨ht.1.trans hr.1, hr.2⟩) h0
      (fun r hr ↦ bound r ⟨ht.1.trans hr.1, hr.2⟩) s ⟨hts, hs.2⟩
    have hI : 0 ≤ ∫ r in t..s, g r :=
      intervalIntegral.integral_nonneg hts fun r hr ↦ hg0 r ⟨ht.1.trans hr.1, hr.2.trans hs.2⟩
    rw [intervalIntegral.integral_const, smul_eq_mul, zero_add] at h
    rw [abs_of_nonneg hI, abs_of_nonneg (sub_nonneg.mpr hts), mul_comm K₁]
    exact h
  · have h := norm_le_mul_exp_integral_left (a := a) (b := t) (A := fun _ ↦ K₁) (g := g)
      (fun r hr ↦ (hf r ⟨hr.1, hr.2.trans ht.2⟩).mono (Icc_subset_Icc le_rfl ht.2))
      continuousOn_const (fun _ _ ↦ hK₁) (hg.mono (Icc_subset_Icc le_rfl ht.2))
      (fun r hr ↦ hg0 r ⟨hr.1, hr.2.trans ht.2⟩) h0
      (fun r hr ↦ bound r ⟨hr.1, hr.2.trans ht.2⟩) s ⟨hs.1, hst⟩
    have hI : 0 ≤ ∫ r in s..t, g r :=
      intervalIntegral.integral_nonneg hst fun r hr ↦ hg0 r ⟨hs.1.trans hr.1, hr.2.trans ht.2⟩
    rw [intervalIntegral.integral_const, smul_eq_mul, zero_add] at h
    rw [intervalIntegral.integral_symm, abs_neg, abs_of_nonneg hI, abs_sub_comm,
      abs_of_nonneg (sub_nonneg.mpr hst), mul_comm K₁]
    exact h

/-- Interval integral of `L * k r + c`. -/
private theorem integral_mul_add_const {k : ℝ → ℝ} {L c t s : ℝ}
    (hk : IntervalIntegrable k MeasureTheory.volume t s) :
    ∫ r in t..s, (L * k r + c) = L * (∫ r in t..s, k r) + (s - t) * c := by
  rw [intervalIntegral.integral_add (hk.const_mul L) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]

/-- **Bound of a derivative of the flow map, linear in the top-order derivative of the field.**
On a set `S` preserved by the flows, with `‖Dv‖ ≤ K₁`, the derivatives of `v` of orders
`2 ≤ i < j` at most `M`, the derivative of order `j` at most `Kj r` (continuous in time), and with
`‖D X(r) x‖ ≤ L` and `‖D^i X(r) x‖ ≤ F` for `1 ≤ i < j` along the time interval, the derivative of
order `j ≥ 2` of the flow map satisfies
`‖D^j X(s) x‖ ≤ (L^j |∫ₜˢ Kj| + |s - t| c_j M max(1, F)^j) exp (K₁ |s - t|)`. -/
theorem IsC1FieldOn.norm_iteratedFDeriv_flowOn_le (hv : IsC1FieldOn v Dv a b K)
    (hsm : IsSmoothFamilyOn m v (Icc a b)) (ht : t ∈ Icc a b)
    (hS : ∀ s ∈ Icc a b, MapsTo (flowOn v a b s t) S S) {j : ℕ} (hj : 2 ≤ j) (hjm : j ≤ m)
    {x : E} (hx : x ∈ S) {K₁ M L F₀ : ℝ} {Kj : ℝ → ℝ}
    (hK₁ : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖fderiv ℝ (v r) y‖ ≤ K₁) (hM0 : 0 ≤ M)
    (hM : ∀ r ∈ Icc a b, ∀ y ∈ S, ∀ i, 2 ≤ i → i < j → ‖iteratedFDeriv ℝ i (v r) y‖ ≤ M)
    (hKj : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖iteratedFDeriv ℝ j (v r) y‖ ≤ Kj r)
    (hKjc : ContinuousOn Kj (Icc a b))
    (hL : ∀ r ∈ Icc a b, ‖fderiv ℝ (flowOn v a b r t) x‖ ≤ L)
    (hF : ∀ r ∈ Icc a b, ∀ i, 1 ≤ i → i < j → ‖iteratedFDeriv ℝ i (flowOn v a b r t) x‖ ≤ F₀)
    {s : ℝ} (hs : s ∈ Icc a b) :
    ‖iteratedFDeriv ℝ j (flowOn v a b s t) x‖ ≤
      (L ^ j * |∫ r in t..s, Kj r| +
        |s - t| * (Fintype.card (OrderedFinpartition j) * (M * max 1 F₀ ^ j))) *
        Real.exp (K₁ * |s - t|) := by
  have hX := hv.isSmoothFamilyOn_flowOn hsm ht
  have hjm' : ((j : ℕ) : WithTop ℕ∞) ≤ (m : WithTop ℕ∞) := by exact_mod_cast hjm
  set c : ℝ := Fintype.card (OrderedFinpartition j) * (M * max 1 F₀ ^ j)
  have hc : 0 ≤ c := by positivity
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL t ht)
  have hKj0 : ∀ r ∈ Icc a b, 0 ≤ Kj r := fun r hr ↦
    (norm_nonneg _).trans (hKj r hr _ (hS r hr hx))
  refine (norm_le_abs_integral_mul_exp (g := fun r ↦ L ^ j * Kj r + c) ht
    (fun r hr ↦ hv.hasDerivWithinAt_iteratedFDeriv_flowOn hsm ht hjm x hr)
    ((norm_nonneg _).trans (hK₁ t ht x hx)) (by fun_prop)
    (fun r hr ↦ by have := hKj0 r hr; positivity)
    (by simp only [hv.isLipschitzFieldOn.flowOn_self_eq ht, iteratedFDeriv_id_eq_zero hj,
      norm_zero, le_refl]) (fun r hr ↦ ?_) hs).trans ?_
  · have hy := hS r hr hx
    have := hKj0 r hr
    have h₁ := hK₁ r hr _ hy
    have h₂ := hKj r hr _ hy
    have h₃ := hL r hr
    refine (norm_iteratedFDeriv_comp_le_add ((hsm.contDiff hr).of_le hjm')
      ((hX.contDiff hr).of_le hjm') hj x hM0 (hM r hr _ hy) (hF r hr)).trans ?_
    calc _ ≤ K₁ * ‖iteratedFDeriv ℝ j (flowOn v a b r t) x‖ + Kj r * L ^ j + c := by gcongr
      _ = _ := by ring
  · gcongr
    rw [integral_mul_add_const ((hKjc.mono (uIcc_subset_Icc ht hs)).intervalIntegrable)]
    refine (abs_add_le _ _).trans_eq ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hL0 _), abs_of_nonneg hc]

/-- The sum `∑_{i < j} K i`, a bound of the derivatives of orders below `j` when `K ≥ 0`. -/
def lowerFieldBound (K : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range j, K i

/-- Bounds of the derivatives of the flow maps over a time interval of length `τ`, for a field
whose derivatives of order `i ≥ 1` are at most `K i` on an invariant set. The bound of order one
is `exp (K 1 τ)`; the bound of order `j + 2` is the maximum of the previous one and the bound of
`norm_iteratedFDeriv_flowOn_le` with the lower orders bounded by the previous one, which is
linear in `K (j + 2)`. -/
def flowDerivBound (K : ℕ → ℝ) (τ : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => Real.exp (K 1 * τ)
  | j + 2 => max (flowDerivBound K τ (j + 1))
      ((Real.exp (K 1 * τ) ^ (j + 2) * (K (j + 2) * τ) +
        τ * (Fintype.card (OrderedFinpartition (j + 2)) *
          (lowerFieldBound K (j + 2) * max 1 (flowDerivBound K τ (j + 1)) ^ (j + 2)))) *
        Real.exp (K 1 * τ))

/-- The bound of order one. -/
theorem flowDerivBound_one (K : ℕ → ℝ) (τ : ℝ) :
    flowDerivBound K τ 1 = Real.exp (K 1 * τ) := by
  rw [flowDerivBound]

/-- The recursion of the bounds. -/
theorem flowDerivBound_add_two (K : ℕ → ℝ) (τ : ℝ) (j : ℕ) :
    flowDerivBound K τ (j + 2) = max (flowDerivBound K τ (j + 1))
      ((Real.exp (K 1 * τ) ^ (j + 2) * (K (j + 2) * τ) +
        τ * (Fintype.card (OrderedFinpartition (j + 2)) *
          (lowerFieldBound K (j + 2) * max 1 (flowDerivBound K τ (j + 1)) ^ (j + 2)))) *
        Real.exp (K 1 * τ)) := by
  rw [flowDerivBound]

/-- The bounds increase with the order. -/
theorem flowDerivBound_mono (K : ℕ → ℝ) (τ : ℝ) {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) :
    flowDerivBound K τ i ≤ flowDerivBound K τ j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    refine ih.trans ?_
    rw [show k + 1 + 1 = k + 2 from rfl, flowDerivBound_add_two]
    exact le_max_left _ _

/-- The lower field bound dominates each lower derivative bound. -/
theorem le_lowerFieldBound {K : ℕ → ℝ} (hK0 : ∀ i, 0 ≤ K i) {i j : ℕ} (hij : i < j) :
    K i ≤ lowerFieldBound K j :=
  Finset.single_le_sum (fun l _ ↦ hK0 l) (Finset.mem_range.mpr hij)

/-- **Bounds of all the derivatives of the flow maps from constant bounds of the field.** On a set
preserved by all the flow maps, if the derivatives of `v` of orders `1 ≤ i ≤ m` are at most `K i`,
then `‖D^j X(s) x‖ ≤ flowDerivBound K (b - a) j` for `1 ≤ j ≤ m`. -/
theorem IsC1FieldOn.norm_iteratedFDeriv_flowOn_le_flowDerivBound (hv : IsC1FieldOn v Dv a b K)
    (hsm : IsSmoothFamilyOn m v (Icc a b)) (ht : t ∈ Icc a b)
    (hS : ∀ s ∈ Icc a b, ∀ t' ∈ Icc a b, MapsTo (flowOn v a b s t') S S) {B : ℕ → ℝ}
    (hB0 : ∀ i, 0 ≤ B i)
    (hB : ∀ i, 1 ≤ i → i ≤ m → ∀ r ∈ Icc a b, ∀ y ∈ S, ‖iteratedFDeriv ℝ i (v r) y‖ ≤ B i)
    {j : ℕ} (hj : 1 ≤ j) (hjm : j ≤ m) {x : E} (hx : x ∈ S) {s : ℝ} (hs : s ∈ Icc a b) :
    ‖iteratedFDeriv ℝ j (flowOn v a b s t) x‖ ≤ flowDerivBound B (b - a) j := by
  have hK₁ : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖fderiv ℝ (v r) y‖ ≤ B 1 := fun r hr y hy ↦ by
    simpa only [norm_iteratedFDeriv_one] using hB 1 le_rfl (hj.trans hjm) r hr y hy
  have hDv : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖Dv r y‖ ≤ B 1 := fun r hr y hy ↦
    (hv.hasFDerivAt r hr y).fderiv ▸ hK₁ r hr y hy
  induction j using Nat.strong_induction_on generalizing x s with
  | _ j ih =>
  have hab : |s - t| ≤ b - a :=
    abs_sub_le_iff.mpr ⟨by linarith [hs.2, ht.1], by linarith [hs.1, ht.2]⟩
  rcases Nat.lt_or_ge j 2 with hj2 | hj2
  · obtain rfl : j = 1 := by omega
    rw [norm_iteratedFDeriv_one, (hv.hasFDerivAt_flowOn hs ht x).fderiv, flowDerivBound_one]
    exact (hv.norm_variationOn_le_of_invariant hS hDv hs ht hx).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hab (hB0 1)))
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
  have hL : ∀ r ∈ Icc a b, ‖fderiv ℝ (flowOn v a b r t) x‖ ≤ flowDerivBound B (b - a) 1 :=
    fun r hr ↦ by
      simpa only [norm_iteratedFDeriv_one] using ih 1 (by omega) le_rfl (by omega) hx hr
  have hM : 0 ≤ lowerFieldBound B (k + 2) := Finset.sum_nonneg fun l _ ↦ hB0 l
  have h := hv.norm_iteratedFDeriv_flowOn_le hsm ht (fun s hs ↦ hS s hs t ht) (by omega) hjm hx
    (F₀ := flowDerivBound B (b - a) (k + 1)) hK₁ hM
    (fun r hr y hy i hi hik ↦ (hB i (by omega) (by omega) r hr y hy).trans
      (le_lowerFieldBound hB0 hik)) (fun r hr y hy ↦ hB (k + 2) (by omega) hjm r hr y hy)
    continuousOn_const hL (fun r hr i hi hik ↦ (ih i hik hi (by omega) hx hr).trans
      (flowDerivBound_mono B (b - a) hi (by omega))) hs
  rw [intervalIntegral.integral_const, smul_eq_mul, abs_mul, abs_of_nonneg (hB0 (k + 2)),
    mul_comm |s - t|, flowDerivBound_one] at h
  rw [flowDerivBound_add_two]
  refine h.trans (le_max_of_le_right ?_)
  have := hB0 1
  have := hB0 (k + 2)
  have : 0 ≤ b - a := by linarith [ht.1, ht.2]
  gcongr

/-- **The top-order bound with a time-dependent top-order bound of the field.** With constant bounds
`B i` of the derivatives of `v` of orders `1 ≤ i < m` and a continuous bound `Km r` of the
derivative of order `m ≥ 2`, the derivative of order `m` of the flow map is bounded linearly in
`∫ Km`: `‖D^m X(s) x‖ ≤ (L^m |∫ₜˢ Km| + |s - t| c_m M_m max(1, F)^m) exp (B 1 |s - t|)` with
`L = flowDerivBound B (b - a) 1`, `F = flowDerivBound B (b - a) (m - 1)` and
`M_m = lowerFieldBound B m`. -/
theorem IsC1FieldOn.norm_iteratedFDeriv_flowOn_le_of_top (hv : IsC1FieldOn v Dv a b K)
    (hsm : IsSmoothFamilyOn m v (Icc a b)) (ht : t ∈ Icc a b) (hm : 2 ≤ m)
    (hS : ∀ s ∈ Icc a b, ∀ t' ∈ Icc a b, MapsTo (flowOn v a b s t') S S) {B : ℕ → ℝ}
    (hB0 : ∀ i, 0 ≤ B i)
    (hB : ∀ i, 1 ≤ i → i < m → ∀ r ∈ Icc a b, ∀ y ∈ S, ‖iteratedFDeriv ℝ i (v r) y‖ ≤ B i)
    {Km : ℝ → ℝ} (hKm : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖iteratedFDeriv ℝ m (v r) y‖ ≤ Km r)
    (hKmc : ContinuousOn Km (Icc a b)) {x : E} (hx : x ∈ S) {s : ℝ} (hs : s ∈ Icc a b) :
    ‖iteratedFDeriv ℝ m (flowOn v a b s t) x‖ ≤
      (flowDerivBound B (b - a) 1 ^ m * |∫ r in t..s, Km r| +
        |s - t| * (Fintype.card (OrderedFinpartition m) *
          (lowerFieldBound B m * max 1 (flowDerivBound B (b - a) (m - 1)) ^ m))) *
        Real.exp (B 1 * |s - t|) := by
  have hsm' : IsSmoothFamilyOn (m - 1) v (Icc a b) := hsm.mono (Nat.sub_le m 1)
  have hlow (r : ℝ) (hr : r ∈ Icc a b) (i : ℕ) (hi : 1 ≤ i) (him : i ≤ m - 1) :
      ‖iteratedFDeriv ℝ i (flowOn v a b r t) x‖ ≤ flowDerivBound B (b - a) i :=
    hv.norm_iteratedFDeriv_flowOn_le_flowDerivBound hsm' ht hS hB0
      (fun l hl hlm ↦ hB l hl (by omega)) hi him hx hr
  have hK₁ : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖fderiv ℝ (v r) y‖ ≤ B 1 := fun r hr y hy ↦ by
    have h := hB 1 le_rfl (by omega) r hr y hy
    rwa [norm_iteratedFDeriv_one] at h
  refine hv.norm_iteratedFDeriv_flowOn_le hsm ht (fun s hs ↦ hS s hs t ht) hm le_rfl hx hK₁
    (Finset.sum_nonneg fun l _ ↦ hB0 l)
    (fun r hr y hy i hi him ↦ (hB i (by omega) him r hr y hy).trans (le_lowerFieldBound hB0 him))
    hKm hKmc (fun r hr ↦ ?_) (fun r hr i hi him ↦ (hlow r hr i hi (by omega)).trans
      (flowDerivBound_mono B (b - a) hi (by omega))) hs
  have h := hlow r hr 1 le_rfl (by omega)
  rwa [norm_iteratedFDeriv_one] at h

end Bounds

/-! ### Hölder bound of the top-order derivative of the flow maps -/

section Holder

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {v : ℝ → E → E} {Dv : ℝ → E → E →L[ℝ] E} {a b t : ℝ} {K : ℝ≥0} {m : ℕ} {S : Set E}

/-- The rate of growth of the `α`-Hölder constant of the derivative of order `m` of the flow maps,
`K₂ L Fm + k m L^(m-1) L₂ + h L^α L^m + c_m (M m Λ + M' L) max(1, F)^m`. Here `k` and `h` are the
bound and the Hölder constant of the derivative of order `m` of the field at the time, `K₂` the
Lipschitz constant of its first derivative, `M` and `M'` the bound and the Lipschitz constant of
its derivatives of orders `2 ≤ i < m`; `Fm` is the bound of the derivative of order `m` of the flow
map, `L` and `L₂` the bound and the Lipschitz constant of its first derivative, `F` and `Λ` the
bound and the Lipschitz constant of its derivatives of orders `1 ≤ i < m`. For `m ≥ 3` the
quantities `K₂, L, L₂, M, F` are of lower order, and the rate is linear in the top-order
quantities `k, h, Fm, M', Λ`. -/
def flowHolderRate (m : ℕ) (α K₂ M M' L L₂ F₀ Fm Λ k h : ℝ) : ℝ :=
  K₂ * L * Fm + k * m * L ^ (m - 1) * L₂ + h * L ^ α * L ^ m +
    Fintype.card (OrderedFinpartition m) * ((M * m * Λ + M' * L) * max 1 F₀ ^ m)

/-- **Hölder bound of the top-order derivative of the flow maps at nearby points.** On a convex set
`S` preserved by the flows from the base time, with the bounds of the field and of the flow maps
listed in the hypotheses, for `x, y ∈ S` with `‖x - y‖ ≤ 1`,
`‖D^m X(s) x - D^m X(s) y‖ ≤ |∫ₜˢ ρ(r)| exp (K₁ |s - t|) ‖x - y‖^α`, with the rate
`ρ(r) = flowHolderRate m α K₂ M M' L L₂ F Fm Λ (Km r) (Hm r)`. -/
theorem IsC1FieldOn.norm_iteratedFDeriv_flowOn_sub_le_rpow (hv : IsC1FieldOn v Dv a b K)
    (hsm : IsSmoothFamilyOn m v (Icc a b)) (ht : t ∈ Icc a b)
    (hS : ∀ s ∈ Icc a b, MapsTo (flowOn v a b s t) S S) (hm : 2 ≤ m) {α : ℝ} (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) {K₁ K₂ M M' L L₂ F₀ Fm Λ : ℝ} {Km Hm : ℝ → ℝ}
    (hK₁ : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖fderiv ℝ (v r) y‖ ≤ K₁) (hM0 : 0 ≤ M)
    (hM : ∀ r ∈ Icc a b, ∀ y ∈ S, ∀ i, 2 ≤ i → i < m → ‖iteratedFDeriv ℝ i (v r) y‖ ≤ M)
    (hKm : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖iteratedFDeriv ℝ m (v r) y‖ ≤ Km r)
    (hKmc : ContinuousOn Km (Icc a b)) (hK₂ : 0 ≤ K₂) (hM'0 : 0 ≤ M')
    (hLip1 : ∀ r ∈ Icc a b, ∀ y ∈ S, ∀ z ∈ S,
      ‖fderiv ℝ (v r) y - fderiv ℝ (v r) z‖ ≤ K₂ * ‖y - z‖)
    (hLip : ∀ r ∈ Icc a b, ∀ y ∈ S, ∀ z ∈ S, ∀ i, 2 ≤ i → i < m →
      ‖iteratedFDeriv ℝ i (v r) y - iteratedFDeriv ℝ i (v r) z‖ ≤ M' * ‖y - z‖)
    (hHm0 : ∀ r ∈ Icc a b, 0 ≤ Hm r)
    (hHm : ∀ r ∈ Icc a b, ∀ y ∈ S, ∀ z ∈ S,
      ‖iteratedFDeriv ℝ m (v r) y - iteratedFDeriv ℝ m (v r) z‖ ≤ Hm r * ‖y - z‖ ^ α)
    (hHmc : ContinuousOn Hm (Icc a b))
    (hL : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖fderiv ℝ (flowOn v a b r t) y‖ ≤ L)
    (hXL : ∀ r ∈ Icc a b, ∀ y ∈ S, ∀ z ∈ S,
      ‖flowOn v a b r t y - flowOn v a b r t z‖ ≤ L * ‖y - z‖)
    (hF : ∀ r ∈ Icc a b, ∀ y ∈ S, ∀ i, 1 ≤ i → i < m →
      ‖iteratedFDeriv ℝ i (flowOn v a b r t) y‖ ≤ F₀)
    (hFm : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖iteratedFDeriv ℝ m (flowOn v a b r t) y‖ ≤ Fm)
    (hΛ0 : 0 ≤ Λ) (hL₂0 : 0 ≤ L₂)
    (hXd1 : ∀ r ∈ Icc a b, ∀ y ∈ S, ∀ z ∈ S,
      ‖fderiv ℝ (flowOn v a b r t) y - fderiv ℝ (flowOn v a b r t) z‖ ≤ L₂ * ‖y - z‖)
    (hXd : ∀ r ∈ Icc a b, ∀ y ∈ S, ∀ z ∈ S, ∀ i, 1 ≤ i → i < m →
      ‖iteratedFDeriv ℝ i (flowOn v a b r t) y - iteratedFDeriv ℝ i (flowOn v a b r t) z‖ ≤
        Λ * ‖y - z‖)
    {x y : E} (hx : x ∈ S) (hy : y ∈ S) (hxy : ‖x - y‖ ≤ 1) {s : ℝ} (hs : s ∈ Icc a b) :
    ‖iteratedFDeriv ℝ m (flowOn v a b s t) x - iteratedFDeriv ℝ m (flowOn v a b s t) y‖ ≤
      |∫ r in t..s, flowHolderRate m α K₂ M M' L L₂ F₀ Fm Λ (Km r) (Hm r)| *
        Real.exp (K₁ * |s - t|) * ‖x - y‖ ^ α := by
  have hX := hv.isSmoothFamilyOn_flowOn hsm ht
  set d := ‖x - y‖
  have hd0 : 0 ≤ d := norm_nonneg _
  have hdα : d ≤ d ^ α := Real.self_le_rpow_of_le_one hd0 hxy hα1
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL t ht x hx)
  have hFm0 : 0 ≤ Fm := (norm_nonneg _).trans (hFm t ht x hx)
  have hKm0 : ∀ r ∈ Icc a b, 0 ≤ Km r := fun r hr ↦
    (norm_nonneg _).trans (hKm r hr _ (hS r hr hx))
  set ρ : ℝ → ℝ := fun r ↦ flowHolderRate m α K₂ M M' L L₂ F₀ Fm Λ (Km r) (Hm r)
  have hρ0 : ∀ r ∈ Icc a b, 0 ≤ ρ r := fun r hr ↦ by
    have := hKm0 r hr
    have := hHm0 r hr
    simp only [ρ, flowHolderRate]
    positivity
  have hρc : ContinuousOn ρ (Icc a b) := by simp only [ρ, flowHolderRate]; fun_prop
  -- the difference of the derivatives of order `m` at `x` and `y` along the time interval
  set e : ℝ → (E [×m]→L[ℝ] E) := fun r ↦
    iteratedFDeriv ℝ m (flowOn v a b r t) x - iteratedFDeriv ℝ m (flowOn v a b r t) y
  have hbound : ∀ r ∈ Icc a b,
      ‖iteratedFDeriv ℝ m (fun z ↦ v r (flowOn v a b r t z)) x -
        iteratedFDeriv ℝ m (fun z ↦ v r (flowOn v a b r t z)) y‖ ≤
        K₁ * ‖e r‖ + ρ r * d ^ α := by
    intro r hr
    have hxr := hS r hr hx
    have hyr := hS r hr hy
    have hgg : ‖flowOn v a b r t x - flowOn v a b r t y‖ ≤ L * d := hXL r hr x hx y hy
    have hpow : ‖flowOn v a b r t x - flowOn v a b r t y‖ ^ α ≤ L ^ α * d ^ α := by
      rw [← Real.mul_rpow hL0 hd0]
      exact Real.rpow_le_rpow (norm_nonneg _) hgg hα0
    -- the bounds of the terms of the Faà di Bruno estimate at the two points
    have := hKm0 r hr
    have := hHm0 r hr
    have h₁ := hK₁ r hr _ hxr
    have h₂ := (hLip1 r hr _ hxr _ hyr).trans (mul_le_mul_of_nonneg_left hgg hK₂)
    have h₃ := hFm r hr y hy
    have h₄ := hKm r hr _ hxr
    have h₅ := max_le (hL r hr x hx) (hL r hr y hy)
    have h₆ := hXd1 r hr x hx y hy
    have h₇ := (hHm r hr _ hxr _ hyr).trans (mul_le_mul_of_nonneg_left hpow (hHm0 r hr))
    have h₈ := hL r hr y hy
    refine (norm_iteratedFDeriv_comp_sub_le_add (hsm.contDiff hr) (hX.contDiff hr) hm x y hM0
      ((norm_nonneg _).trans (hF r hr x hx 1 le_rfl (by omega))) (by positivity) (by positivity)
      (hM r hr _ hxr) (fun i hi him ↦ (hLip r hr _ hxr _ hyr i hi him).trans
        (mul_le_mul_of_nonneg_left hgg hM'0)) (hF r hr x hx) (hF r hr y hy)
      (hXd r hr x hx y hy)).trans ?_
    have hA : 0 ≤ K₂ * L * Fm + Km r * m * L ^ (m - 1) * L₂ +
        Fintype.card (OrderedFinpartition m) * ((M * m * Λ + M' * L) * max 1 F₀ ^ m) := by
      positivity
    calc _ ≤ K₁ * ‖e r‖ + K₂ * (L * d) * Fm +
          (Km r * m * L ^ (m - 1) * (L₂ * d) + Hm r * (L ^ α * d ^ α) * L ^ m) +
          Fintype.card (OrderedFinpartition m) * ((M * m * (Λ * d) + M' * (L * d)) *
            max 1 F₀ ^ m) := by gcongr
      _ ≤ K₁ * ‖e r‖ + ρ r * d ^ α := by
        simp only [ρ, flowHolderRate]
        linarith [mul_le_mul_of_nonneg_left hdα hA]
  have he : ∀ r ∈ Icc a b, HasDerivWithinAt e
      (iteratedFDeriv ℝ m (fun z ↦ v r (flowOn v a b r t z)) x -
        iteratedFDeriv ℝ m (fun z ↦ v r (flowOn v a b r t z)) y) (Icc a b) r := fun r hr ↦
    (hv.hasDerivWithinAt_iteratedFDeriv_flowOn hsm ht le_rfl x hr).sub
      (hv.hasDerivWithinAt_iteratedFDeriv_flowOn hsm ht le_rfl y hr)
  have he0 : ‖e t‖ ≤ 0 := by
    simp only [e, hv.isLipschitzFieldOn.flowOn_self_eq ht, iteratedFDeriv_id_eq_zero hm, sub_zero,
      norm_zero, le_refl]
  have hdα0 : 0 ≤ d ^ α := Real.rpow_nonneg hd0 α
  have h := norm_le_abs_integral_mul_exp (g := fun r ↦ ρ r * d ^ α) ht he
    ((norm_nonneg _).trans (hK₁ t ht x hx)) (hρc.mul continuousOn_const)
    (fun r hr ↦ mul_nonneg (hρ0 r hr) hdα0) he0 hbound hs
  rw [intervalIntegral.integral_mul_const, abs_mul, abs_of_nonneg hdα0] at h
  exact h.trans_eq (mul_right_comm _ _ _)

/-- **Hölder bound of the top-order derivative of the flow maps on `S`.** Under the hypotheses of
`norm_iteratedFDeriv_flowOn_sub_le_rpow`, for all `x, y ∈ S`,
`‖D^m X(s) x - D^m X(s) y‖ ≤ max (|∫ₜˢ ρ| exp (K₁ |s - t|)) (2 Fm) ‖x - y‖^α`. -/
theorem IsC1FieldOn.norm_iteratedFDeriv_flowOn_sub_le_max_rpow (hv : IsC1FieldOn v Dv a b K)
    (hsm : IsSmoothFamilyOn m v (Icc a b)) (ht : t ∈ Icc a b)
    (hS : ∀ s ∈ Icc a b, MapsTo (flowOn v a b s t) S S) (hm : 2 ≤ m) {α : ℝ} (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) {K₁ K₂ M M' L L₂ F₀ Fm Λ : ℝ} {Km Hm : ℝ → ℝ}
    (hK₁ : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖fderiv ℝ (v r) y‖ ≤ K₁) (hM0 : 0 ≤ M)
    (hM : ∀ r ∈ Icc a b, ∀ y ∈ S, ∀ i, 2 ≤ i → i < m → ‖iteratedFDeriv ℝ i (v r) y‖ ≤ M)
    (hKm : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖iteratedFDeriv ℝ m (v r) y‖ ≤ Km r)
    (hKmc : ContinuousOn Km (Icc a b)) (hK₂ : 0 ≤ K₂) (hM'0 : 0 ≤ M')
    (hLip1 : ∀ r ∈ Icc a b, ∀ y ∈ S, ∀ z ∈ S,
      ‖fderiv ℝ (v r) y - fderiv ℝ (v r) z‖ ≤ K₂ * ‖y - z‖)
    (hLip : ∀ r ∈ Icc a b, ∀ y ∈ S, ∀ z ∈ S, ∀ i, 2 ≤ i → i < m →
      ‖iteratedFDeriv ℝ i (v r) y - iteratedFDeriv ℝ i (v r) z‖ ≤ M' * ‖y - z‖)
    (hHm0 : ∀ r ∈ Icc a b, 0 ≤ Hm r)
    (hHm : ∀ r ∈ Icc a b, ∀ y ∈ S, ∀ z ∈ S,
      ‖iteratedFDeriv ℝ m (v r) y - iteratedFDeriv ℝ m (v r) z‖ ≤ Hm r * ‖y - z‖ ^ α)
    (hHmc : ContinuousOn Hm (Icc a b))
    (hL : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖fderiv ℝ (flowOn v a b r t) y‖ ≤ L)
    (hXL : ∀ r ∈ Icc a b, ∀ y ∈ S, ∀ z ∈ S,
      ‖flowOn v a b r t y - flowOn v a b r t z‖ ≤ L * ‖y - z‖)
    (hF : ∀ r ∈ Icc a b, ∀ y ∈ S, ∀ i, 1 ≤ i → i < m →
      ‖iteratedFDeriv ℝ i (flowOn v a b r t) y‖ ≤ F₀)
    (hFm : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖iteratedFDeriv ℝ m (flowOn v a b r t) y‖ ≤ Fm)
    (hΛ0 : 0 ≤ Λ) (hL₂0 : 0 ≤ L₂)
    (hXd1 : ∀ r ∈ Icc a b, ∀ y ∈ S, ∀ z ∈ S,
      ‖fderiv ℝ (flowOn v a b r t) y - fderiv ℝ (flowOn v a b r t) z‖ ≤ L₂ * ‖y - z‖)
    (hXd : ∀ r ∈ Icc a b, ∀ y ∈ S, ∀ z ∈ S, ∀ i, 1 ≤ i → i < m →
      ‖iteratedFDeriv ℝ i (flowOn v a b r t) y - iteratedFDeriv ℝ i (flowOn v a b r t) z‖ ≤
        Λ * ‖y - z‖)
    {x y : E} (hx : x ∈ S) (hy : y ∈ S) {s : ℝ} (hs : s ∈ Icc a b) :
    ‖iteratedFDeriv ℝ m (flowOn v a b s t) x - iteratedFDeriv ℝ m (flowOn v a b s t) y‖ ≤
      max (|∫ r in t..s, flowHolderRate m α K₂ M M' L L₂ F₀ Fm Λ (Km r) (Hm r)| *
        Real.exp (K₁ * |s - t|)) (2 * Fm) * ‖x - y‖ ^ α := by
  rcases le_or_gt ‖x - y‖ 1 with hxy | hxy
  · refine (hv.norm_iteratedFDeriv_flowOn_sub_le_rpow hsm ht hS hm hα0 hα1 hK₁ hM0 hM hKm hKmc
      hK₂ hM'0 hLip1 hLip hHm0 hHm hHmc hL hXL hF hFm hΛ0 hL₂0 hXd1 hXd hx hy hxy hs).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (norm_nonneg _) α)
  · have h1 : 1 ≤ ‖x - y‖ ^ α := Real.one_le_rpow hxy.le hα0
    have hFm0 : 0 ≤ Fm := (norm_nonneg _).trans (hFm t ht x hx)
    calc _ ≤ ‖iteratedFDeriv ℝ m (flowOn v a b s t) x‖ +
          ‖iteratedFDeriv ℝ m (flowOn v a b s t) y‖ := norm_sub_le _ _
      _ ≤ 2 * Fm := by linarith [hFm s hs x hx, hFm s hs y hy]
      _ ≤ 2 * Fm * ‖x - y‖ ^ α := le_mul_of_one_le_right (by linarith) h1
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)

end Holder

/-! ### Time moduli of the derivatives of the flow maps -/

section Time

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {v : ℝ → E → E} {Dv : ℝ → E → E →L[ℝ] E} {a b t : ℝ} {K : ℝ≥0} {m : ℕ} {S : Set E}

/-- **Lipschitz continuity in the final time.** If the derivative of order `j ≤ m` of the field
along the flow, `D^j (v r ∘ X(r)) x`, is at most `B` on `[a, b]`, then the derivative of order `j`
of the flow map at `x` is `B`-Lipschitz in the final time. -/
theorem IsC1FieldOn.norm_iteratedFDeriv_flowOn_sub_flowOn_le (hv : IsC1FieldOn v Dv a b K)
    (hsm : IsSmoothFamilyOn m v (Icc a b)) (ht : t ∈ Icc a b) {j : ℕ} (hj : j ≤ m) (x : E)
    {B : ℝ} (hB : ∀ r ∈ Icc a b,
      ‖iteratedFDeriv ℝ j (fun y ↦ v r (flowOn v a b r t y)) x‖ ≤ B)
    {s s' : ℝ} (hs : s ∈ Icc a b) (hs' : s' ∈ Icc a b) :
    ‖iteratedFDeriv ℝ j (flowOn v a b s t) x - iteratedFDeriv ℝ j (flowOn v a b s' t) x‖ ≤
      B * |s - s'| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun r ↦ iteratedFDeriv ℝ j (flowOn v a b r t) x)
    (fun r hr ↦ hv.hasDerivWithinAt_iteratedFDeriv_flowOn hsm ht hj x hr) hB
    (convex_Icc a b) hs' hs
  simpa [Real.norm_eq_abs] using h

/-- **The time modulus from constant bounds of the field.** With the bounds `B i` of the
derivatives of `v` of orders `1 ≤ i ≤ m` on a set `S` preserved by all the flow maps, for
`2 ≤ j ≤ m` and `x ∈ S` the derivative of order `j` of the flow map is Lipschitz in the final
time with constant `B 1 Fj + B j L^j + c_j M_j max(1, F_{j-1})^j`, where `L`, `F_{j-1}` and `Fj`
are the bounds `flowDerivBound B (b - a)` of orders `1`, `j - 1` and `j` and
`M_j = lowerFieldBound B j`. -/
theorem IsC1FieldOn.norm_iteratedFDeriv_flowOn_sub_flowOn_le_of_bounds
    (hv : IsC1FieldOn v Dv a b K) (hsm : IsSmoothFamilyOn m v (Icc a b)) (ht : t ∈ Icc a b)
    (hS : ∀ s ∈ Icc a b, ∀ t' ∈ Icc a b, MapsTo (flowOn v a b s t') S S) {B : ℕ → ℝ}
    (hB0 : ∀ i, 0 ≤ B i)
    (hB : ∀ i, 1 ≤ i → i ≤ m → ∀ r ∈ Icc a b, ∀ y ∈ S, ‖iteratedFDeriv ℝ i (v r) y‖ ≤ B i)
    {j : ℕ} (hj : 2 ≤ j) (hjm : j ≤ m) {x : E} (hx : x ∈ S) {s s' : ℝ} (hs : s ∈ Icc a b)
    (hs' : s' ∈ Icc a b) :
    ‖iteratedFDeriv ℝ j (flowOn v a b s t) x - iteratedFDeriv ℝ j (flowOn v a b s' t) x‖ ≤
      (B 1 * flowDerivBound B (b - a) j + B j * flowDerivBound B (b - a) 1 ^ j +
        Fintype.card (OrderedFinpartition j) *
          (lowerFieldBound B j * max 1 (flowDerivBound B (b - a) (j - 1)) ^ j)) * |s - s'| := by
  have hX := hv.isSmoothFamilyOn_flowOn hsm ht
  refine hv.norm_iteratedFDeriv_flowOn_sub_flowOn_le hsm ht hjm x (fun r hr ↦ ?_) hs hs'
  have hcast : ((j : ℕ) : WithTop ℕ∞) ≤ (m : WithTop ℕ∞) := by exact_mod_cast hjm
  have hxr : flowOn v a b r t x ∈ S := hS r hr t ht hx
  have hD (i : ℕ) (hi : 1 ≤ i) (him : i ≤ m) :
      ‖iteratedFDeriv ℝ i (flowOn v a b r t) x‖ ≤ flowDerivBound B (b - a) i :=
    hv.norm_iteratedFDeriv_flowOn_le_flowDerivBound hsm ht hS hB0 hB hi him hx hr
  have h := norm_iteratedFDeriv_comp_le_add ((hsm.contDiff hr).of_le hcast)
    ((hX.contDiff hr).of_le hcast) hj x (M := lowerFieldBound B j)
    (F₀ := flowDerivBound B (b - a) (j - 1)) (Finset.sum_nonneg fun l _ ↦ hB0 l)
    (fun i hi hij ↦ (hB i (by omega) (by omega) r hr _ hxr).trans (le_lowerFieldBound hB0 hij))
    (fun i hi hij ↦ (hD i hi (by omega)).trans (flowDerivBound_mono B (b - a) hi (by omega)))
  have h1 : ‖fderiv ℝ (v r) (flowOn v a b r t x)‖ ≤ B 1 := by
    simpa only [norm_iteratedFDeriv_one] using hB 1 le_rfl (by omega) r hr _ hxr
  have h2 : ‖fderiv ℝ (flowOn v a b r t) x‖ ≤ flowDerivBound B (b - a) 1 := by
    simpa only [norm_iteratedFDeriv_one] using hD 1 le_rfl (by omega)
  have h3 := hD j (by omega) hjm
  have h4 := hB j (by omega) hjm r hr _ hxr
  have := hB0 1
  have := hB0 j
  exact h.trans (by gcongr)

end Time

end PDE.Analysis.ODE
