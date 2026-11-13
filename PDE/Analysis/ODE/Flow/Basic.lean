/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.ODE.Gronwall
import PDE.Analysis.Evolution.ODE.Nonautonomous.Lipschitz
import PDE.Hyperbolic.Transport.QuadrantFlow

/-!
# Flows of time-dependent Lipschitz fields

Let `v : ℝ → E → E` be a field on a finite-dimensional real normed space that is jointly
continuous on `[a, b] × E` and `K`-Lipschitz in space at every time of `[a, b]`. Through every
point `x` at every time `t ∈ [a, b]` passes a unique solution of `γ' = v(r, γ)` on the whole
interval, and `flowOn v a b s t x` is its value at time `s`. The flow satisfies the cocycle law,
each map `flowOn v a b s t` is a homeomorphism with inverse `flowOn v a b t s`, it is
`exp (K |s - t|)`-Lipschitz, and it is jointly continuous in `(s, t, x)`.

For `E = EuclideanSpace ℝ ι`, a field whose `j`-th component vanishes on the hyperplane
`x j = 0` has a flow that maps each of `{x j ≥ 0}`, `{x j > 0}` and `{x j = 0}` bijectively onto
itself. This covers fields on a closed half-space that are tangent to its boundary.

## Main results

* `norm_le_gronwallBound_of_hasDerivWithinAt`: Grönwall's inequality forward and backward from an
  interior base time.
* `hasDerivAt_flowOn`, `flowOn_self`: the flow solves the equation and starts at the identity.
* `eq_flowOn_of_hasDerivWithinAt`: every solution on a subinterval is a flow line.
* `flowOn_flowOn`, `flowOn_flowOn_self`: the cocycle law and the inverse.
* `dist_flowOn_le`, `continuousOn_flowOn`: Lipschitz dependence and joint continuity.
* `bijOn_flowOn_nonneg`, `bijOn_flowOn_pos`, `bijOn_flowOn_eq_zero`: invariance of half-spaces
  and of their boundary hyperplanes.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped NNReal Topology

namespace PDE.Analysis.ODE

/-- If some time lies in `[-T, T]`, so does `0`. -/
theorem zero_mem_Icc_neg_of_mem {T t : ℝ} (ht : t ∈ Icc (-T) T) : (0 : ℝ) ∈ Icc (-T) T :=
  ⟨by linarith [ht.1, ht.2], by linarith [ht.1, ht.2]⟩

/-! ### Grönwall's inequality in both time directions -/

section Gronwall

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Grönwall's inequality from an interior base time.** If `‖e'‖ ≤ K ‖e‖ + A` on `[a, b]`
(with derivatives within `[a, b]`) and `‖e t‖ ≤ δ`, then `‖e s‖ ≤ gronwallBound δ K A |s - t|`
for every `s ∈ [a, b]`, on both sides of `t`. -/
theorem norm_le_gronwallBound_of_hasDerivWithinAt {e e' : ℝ → F} {a b t δ K A : ℝ}
    (ht : t ∈ Icc a b) (he : ∀ r ∈ Icc a b, HasDerivWithinAt e (e' r) (Icc a b) r)
    (he₀ : ‖e t‖ ≤ δ) (hbound : ∀ r ∈ Icc a b, ‖e' r‖ ≤ K * ‖e r‖ + A)
    {s : ℝ} (hs : s ∈ Icc a b) : ‖e s‖ ≤ gronwallBound δ K A |s - t| := by
  rcases le_total t s with hts | hst
  · have hsub : Icc t s ⊆ Icc a b := Icc_subset_Icc ht.1 hs.2
    have hright (r : ℝ) (hr : r ∈ Ico t s) : HasDerivWithinAt e (e' r) (Ici r) r :=
      (he r (hsub (Ico_subset_Icc_self hr))).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ⟨(ht.1.trans hr.1), hr.2.trans_le hs.2⟩)
    have h := norm_le_gronwallBound_of_norm_deriv_right_le (f := e) (f' := e') (δ := δ)
      (K := K) (ε := A) (a := t) (b := s)
      (fun r hr ↦ (he r (hsub hr)).continuousWithinAt.mono hsub) hright he₀
      (fun r hr ↦ hbound r (hsub (Ico_subset_Icc_self hr))) s ⟨hts, le_rfl⟩
    rwa [abs_of_nonneg (sub_nonneg.mpr hts)]
  · have hneg (q : ℝ) (hq : q ∈ Icc (-b) (-a)) : -q ∈ Icc a b :=
      ⟨le_neg.mp hq.2, neg_le.mp hq.1⟩
    have hmaps : MapsTo (fun q : ℝ ↦ -q) (Icc (-b) (-a)) (Icc a b) := fun q hq ↦ hneg q hq
    have hrev (q : ℝ) (hq : q ∈ Icc (-b) (-a)) :
        HasDerivWithinAt (fun q ↦ e (-q)) (-e' (-q)) (Icc (-b) (-a)) q := by
      have h := (he (-q) (hneg q hq)).scomp q (hasDerivAt_neg q).hasDerivWithinAt hmaps
      simpa [Function.comp_def] using h
    have hsub : Icc (-t) (-s) ⊆ Icc (-b) (-a) :=
      Icc_subset_Icc (neg_le_neg ht.2) (neg_le_neg hs.1)
    have hright (q : ℝ) (hq : q ∈ Ico (-t) (-s)) :
        HasDerivWithinAt (fun q ↦ e (-q)) (-e' (-q)) (Ici q) q :=
      (hrev q (hsub (Ico_subset_Icc_self hq))).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ⟨(neg_le_neg ht.2).trans hq.1,
          hq.2.trans_le (neg_le_neg hs.1)⟩)
    have h := norm_le_gronwallBound_of_norm_deriv_right_le (f := fun q ↦ e (-q))
      (f' := fun q ↦ -e' (-q)) (δ := δ) (K := K) (ε := A) (a := -t) (b := -s)
      (fun q hq ↦ (hrev q (hsub hq)).continuousWithinAt.mono hsub) hright
      (by simpa using he₀)
      (fun q hq ↦ by
        simpa only [norm_neg] using hbound (-q) (hneg q (hsub (Ico_subset_Icc_self hq))))
      (-s) ⟨neg_le_neg hst, le_rfl⟩
    rw [abs_of_nonpos (sub_nonpos.mpr hst), neg_sub]
    have h' : ‖e (-(-s))‖ ≤ gronwallBound δ K A (-s - -t) := h
    rwa [neg_neg, show -s - -t = t - s by ring] at h'

/-- Two solutions of `γ' = v(r, γ)` on `[c, d]` with `K`-Lipschitz `v(r, ·)` that agree at one
time agree on `[c, d]`. -/
theorem eqOn_of_hasDerivWithinAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : ℝ → E → E} {K : ℝ≥0} {c d t : ℝ} (hv : ∀ r ∈ Icc c d, LipschitzWith K (v r))
    (ht : t ∈ Icc c d) {γ γ' : ℝ → E}
    (hγ : ∀ r ∈ Icc c d, HasDerivWithinAt γ (v r (γ r)) (Icc c d) r)
    (hγ' : ∀ r ∈ Icc c d, HasDerivWithinAt γ' (v r (γ' r)) (Icc c d) r)
    (heq : γ t = γ' t) : EqOn γ γ' (Icc c d) := by
  intro s hs
  have h := norm_le_gronwallBound_of_hasDerivWithinAt (e := fun r ↦ γ r - γ' r) (δ := 0)
    (K := K) (A := 0) ht (fun r hr ↦ (hγ r hr).sub (hγ' r hr)) (by simp [heq])
    (fun r hr ↦ by simpa using (hv r hr).norm_sub_le (γ r) (γ' r)) hs
  rw [gronwallBound_ε0_δ0] at h
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h)

end Gronwall

/-! ### The flow -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The field `v` is jointly continuous on `[a, b] × E` and `K`-Lipschitz in space at every time
of `[a, b]`. Nothing is assumed outside `[a, b]`. -/
structure IsLipschitzFieldOn (v : ℝ → E → E) (a b : ℝ) (K : ℝ≥0) : Prop where
  /-- Joint continuity on `[a, b] × E`. -/
  continuousOn : ContinuousOn (Function.uncurry v) (Icc a b ×ˢ univ)
  /-- A uniform Lipschitz bound in space. -/
  lipschitzWith : ∀ t ∈ Icc a b, LipschitzWith K (v t)

/-- The flow of `v` on `[a, b]`: the value at time `s` of the solution of `γ' = v(r, γ)` on
`[a, b]` with `γ t = x`. When no such solution exists the value is `x`. Under
`IsLipschitzFieldOn v a b K` the solution exists and is unique for `t ∈ [a, b]`. -/
def flowOn (v : ℝ → E → E) (a b s t : ℝ) (x : E) : E := by
  classical
  exact if h : ∃ γ : ℝ → E, γ t = x ∧ ∀ r ∈ Icc a b, HasDerivAt γ (v r (γ r)) r then h.choose s
    else x

variable {v : ℝ → E → E} {a b : ℝ} {K : ℝ≥0}

namespace IsLipschitzFieldOn

variable [FiniteDimensional ℝ E]

/-- Through every point at every time of `[a, b]` passes a solution with a classical derivative
at every time of `[a, b]`. -/
theorem exists_solution (hv : IsLipschitzFieldOn v a b K) {t : ℝ} (ht : t ∈ Icc a b) (x : E) :
    ∃ γ : ℝ → E, γ t = x ∧ ∀ r ∈ Icc a b, HasDerivAt γ (v r (γ r)) r := by
  have hab : a ≤ b := ht.1.trans ht.2
  let w : ℝ → E → E := fun r y ↦ v (projIcc a b hab r) y
  have hw : Continuous (Function.uncurry w) :=
    hv.continuousOn.comp_continuous
      (((continuous_subtype_val.comp (continuous_projIcc (h := hab))).comp continuous_fst).prodMk
        continuous_snd)
      (fun p ↦ ⟨(projIcc a b hab p.1).2, mem_univ p.2⟩)
  obtain ⟨γ, -, hγt, hγ⟩ := PDE.Analysis.Evolution.exists_eq_hasDerivAt_on_Icc_of_lipschitz hw
    (fun r _ ↦ hv.lipschitzWith _ (projIcc a b hab r).2) ⟨t, ht⟩ x
  refine ⟨γ, hγt, fun r hr ↦ ?_⟩
  simpa only [w, projIcc_of_mem hab hr] using hγ r hr

/-- The flow line through `x` at time `t` starts at `x` and solves the equation at every time of
`[a, b]`. -/
theorem flowOn_spec (hv : IsLipschitzFieldOn v a b K) {t : ℝ} (ht : t ∈ Icc a b) (x : E) :
    flowOn v a b t t x = x ∧
      ∀ r ∈ Icc a b, HasDerivAt (fun q ↦ flowOn v a b q t x) (v r (flowOn v a b r t x)) r := by
  have h := hv.exists_solution ht x
  simp only [flowOn, h, dite_true]
  exact h.choose_spec

/-- The flow at the initial time is the identity. -/
theorem flowOn_self (hv : IsLipschitzFieldOn v a b K) {t : ℝ} (ht : t ∈ Icc a b) (x : E) :
    flowOn v a b t t x = x :=
  (hv.flowOn_spec ht x).1

/-- Flow lines solve the equation, with a classical derivative at every time of `[a, b]`. -/
theorem hasDerivAt_flowOn (hv : IsLipschitzFieldOn v a b K) {s t : ℝ} (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) (x : E) :
    HasDerivAt (fun r ↦ flowOn v a b r t x) (v s (flowOn v a b s t x)) s :=
  (hv.flowOn_spec ht x).2 s hs

/-- Flow lines solve the equation within `[a, b]`. -/
theorem hasDerivWithinAt_flowOn (hv : IsLipschitzFieldOn v a b K) {s t : ℝ} (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) (x : E) :
    HasDerivWithinAt (fun r ↦ flowOn v a b r t x) (v s (flowOn v a b s t x)) (Icc a b) s :=
  (hv.hasDerivAt_flowOn hs ht x).hasDerivWithinAt

/-- Flow lines are continuous on `[a, b]`. -/
theorem continuousOn_flowOn_time (hv : IsLipschitzFieldOn v a b K) {t : ℝ} (ht : t ∈ Icc a b)
    (x : E) : ContinuousOn (fun r ↦ flowOn v a b r t x) (Icc a b) := fun _ hr ↦
  (hv.hasDerivAt_flowOn hr ht x).continuousAt.continuousWithinAt

/-- **Uniqueness.** A solution on a subinterval `[c, d] ⊆ [a, b]` through `x` at a time
`t ∈ [c, d]` is the flow line through `(t, x)` on `[c, d]`. -/
theorem eq_flowOn_of_hasDerivWithinAt (hv : IsLipschitzFieldOn v a b K) {c d t : ℝ}
    (hcd : Icc c d ⊆ Icc a b) (ht : t ∈ Icc c d) {γ : ℝ → E} {x : E} (hγt : γ t = x)
    (hγ : ∀ r ∈ Icc c d, HasDerivWithinAt γ (v r (γ r)) (Icc c d) r) :
    ∀ r ∈ Icc c d, γ r = flowOn v a b r t x := by
  have heq := eqOn_of_hasDerivWithinAt (fun r hr ↦ hv.lipschitzWith r (hcd hr)) ht hγ
    (fun r hr ↦ (hv.hasDerivAt_flowOn (hcd hr) (hcd ht) x).hasDerivWithinAt)
    (by rw [hγt, hv.flowOn_self (hcd ht)])
  exact fun r hr ↦ heq hr

/-- **The cocycle law.** -/
theorem flowOn_flowOn (hv : IsLipschitzFieldOn v a b K) {s r t : ℝ} (hs : s ∈ Icc a b)
    (hr : r ∈ Icc a b) (ht : t ∈ Icc a b) (x : E) :
    flowOn v a b s r (flowOn v a b r t x) = flowOn v a b s t x :=
  (hv.eq_flowOn_of_hasDerivWithinAt subset_rfl hr rfl
    (fun _ hq ↦ hv.hasDerivWithinAt_flowOn hq ht x) s hs).symm

/-- `flowOn v a b t s` inverts `flowOn v a b s t`. -/
theorem flowOn_flowOn_self (hv : IsLipschitzFieldOn v a b K) {s t : ℝ} (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) (x : E) : flowOn v a b t s (flowOn v a b s t x) = x := by
  rw [hv.flowOn_flowOn ht hs ht, hv.flowOn_self ht]

/-- **Lipschitz dependence on the initial point.** -/
theorem norm_flowOn_sub_le (hv : IsLipschitzFieldOn v a b K) {s t : ℝ} (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) (x y : E) :
    ‖flowOn v a b s t x - flowOn v a b s t y‖ ≤ Real.exp (K * |s - t|) * ‖x - y‖ := by
  have h := norm_le_gronwallBound_of_hasDerivWithinAt
    (e := fun r ↦ flowOn v a b r t x - flowOn v a b r t y) (δ := ‖x - y‖) (K := K) (A := 0) ht
    (fun r hr ↦ (hv.hasDerivWithinAt_flowOn hr ht x).sub (hv.hasDerivWithinAt_flowOn hr ht y))
    (by simp [hv.flowOn_self ht])
    (fun r hr ↦ by simpa using (hv.lipschitzWith r hr).norm_sub_le _ _) hs
  rw [gronwallBound_ε0] at h
  linarith [h]

/-- **Lipschitz dependence on the initial point**, distance form. -/
theorem dist_flowOn_le (hv : IsLipschitzFieldOn v a b K) {s t : ℝ} (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) (x y : E) :
    dist (flowOn v a b s t x) (flowOn v a b s t y) ≤ Real.exp (K * |s - t|) * dist x y := by
  simpa only [dist_eq_norm] using hv.norm_flowOn_sub_le hs ht x y

/-- A Lipschitz bound uniform over `[a, b]`. -/
theorem dist_flowOn_le_of_mem (hv : IsLipschitzFieldOn v a b K) {s t : ℝ} (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) (x y : E) :
    dist (flowOn v a b s t x) (flowOn v a b s t y) ≤ Real.exp (K * (b - a)) * dist x y := by
  refine (hv.dist_flowOn_le hs ht x y).trans (mul_le_mul_of_nonneg_right ?_ dist_nonneg)
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ K.coe_nonneg
  rw [abs_le]
  constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]

/-- **Joint continuity** of the flow in the final time, the initial time and the initial
point. -/
theorem continuousOn_flowOn (hv : IsLipschitzFieldOn v a b K) :
    ContinuousOn (fun p : ℝ × ℝ × E ↦ flowOn v a b p.1 p.2.1 p.2.2)
      (Icc a b ×ˢ Icc a b ×ˢ univ) := by
  rintro ⟨s₀, t₀, x₀⟩ ⟨hs₀, ht₀, -⟩
  set L := Real.exp (K * (b - a))
  let g : ℝ × ℝ × E → ℝ := fun p ↦ L * L * (dist p.2.2 x₀ + dist (flowOn v a b p.2.1 t₀ x₀) x₀) +
    dist (flowOn v a b p.1 t₀ x₀) (flowOn v a b s₀ t₀ x₀)
  have hg : ContinuousAt g (s₀, t₀, x₀) := by
    have h₁ : ContinuousAt (fun p : ℝ × ℝ × E ↦ flowOn v a b p.2.1 t₀ x₀) (s₀, t₀, x₀) :=
      ((hv.hasDerivAt_flowOn ht₀ ht₀ x₀).continuousAt).comp (f := fun p : ℝ × ℝ × E ↦ p.2.1)
        (x := (s₀, t₀, x₀)) continuous_snd.fst.continuousAt
    have h₂ : ContinuousAt (fun p : ℝ × ℝ × E ↦ flowOn v a b p.1 t₀ x₀) (s₀, t₀, x₀) :=
      ((hv.hasDerivAt_flowOn hs₀ ht₀ x₀).continuousAt).comp (f := fun p : ℝ × ℝ × E ↦ p.1)
        (x := (s₀, t₀, x₀)) continuous_fst.continuousAt
    exact ((continuousAt_const.mul ((continuous_snd.snd.dist continuous_const).continuousAt.add
      (h₁.dist continuousAt_const))).add (h₂.dist continuousAt_const))
  have hg₀ : g (s₀, t₀, x₀) = 0 := by simp [g, hv.flowOn_self ht₀]
  rw [ContinuousWithinAt, tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg) ?_ (hg₀ ▸ hg.tendsto.mono_left
    nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with p hp
  obtain ⟨hs, ht, -⟩ := hp
  obtain ⟨s, t, x⟩ := p
  change dist (flowOn v a b s t x) (flowOn v a b s₀ t₀ x₀) ≤ _
  have hL : 0 ≤ L := (Real.exp_pos _).le
  have hcoc : flowOn v a b s t x = flowOn v a b s t₀ (flowOn v a b t₀ t x) :=
    (hv.flowOn_flowOn hs ht₀ ht x).symm
  have hback : x₀ = flowOn v a b t₀ t (flowOn v a b t t₀ x₀) :=
    (hv.flowOn_flowOn ht₀ ht ht₀ x₀).trans (hv.flowOn_self ht₀ x₀) |>.symm
  have h₁ : dist (flowOn v a b t₀ t x) x₀ ≤
      L * (dist x x₀ + dist (flowOn v a b t t₀ x₀) x₀) := by
    calc dist (flowOn v a b t₀ t x) x₀
        = dist (flowOn v a b t₀ t x) (flowOn v a b t₀ t (flowOn v a b t t₀ x₀)) := by
          rw [← hback]
      _ ≤ L * dist x (flowOn v a b t t₀ x₀) := hv.dist_flowOn_le_of_mem ht₀ ht _ _
      _ ≤ L * (dist x x₀ + dist (flowOn v a b t t₀ x₀) x₀) := by
          gcongr
          rw [dist_comm (flowOn v a b t t₀ x₀) x₀]
          exact dist_triangle _ _ _
  calc dist (flowOn v a b s t x) (flowOn v a b s₀ t₀ x₀)
      ≤ dist (flowOn v a b s t x) (flowOn v a b s t₀ x₀) +
          dist (flowOn v a b s t₀ x₀) (flowOn v a b s₀ t₀ x₀) := dist_triangle _ _ _
    _ ≤ L * dist (flowOn v a b t₀ t x) x₀ +
          dist (flowOn v a b s t₀ x₀) (flowOn v a b s₀ t₀ x₀) := by
        gcongr
        rw [hcoc]
        exact hv.dist_flowOn_le_of_mem hs ht₀ _ _
    _ ≤ L * (L * (dist x x₀ + dist (flowOn v a b t t₀ x₀) x₀)) +
          dist (flowOn v a b s t₀ x₀) (flowOn v a b s₀ t₀ x₀) := by gcongr
    _ = g (s, t, x) := by simp only [g]; ring

end IsLipschitzFieldOn

/-! ### Half-spaces tangent to the field -/

section HalfSpace

variable {ι : Type*} [Fintype ι] {v : ℝ → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {j : ι}

/-- If `v(r, ·)` is `K`-Lipschitz and its `j`-th component vanishes on `x j = 0`, then
`|v(r, y) j| ≤ K |y j|`. -/
theorem abs_apply_le_of_tangent {w : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    (hw : LipschitzWith K w) (htan : ∀ x, x j = 0 → w x j = 0) (y : EuclideanSpace ℝ ι) :
    |w y j| ≤ K * |y j| := by
  classical
  let p : EuclideanSpace ℝ ι := y - EuclideanSpace.single j (y j)
  have hp : p j = 0 := by simp [p]
  have hyp : y - p = EuclideanSpace.single j (y j) := by simp [p]
  calc |w y j| = |(w y - w p) j| := by simp [htan p hp]
    _ ≤ ‖w y - w p‖ := by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (w y - w p) j
    _ ≤ K * ‖y - p‖ := hw.norm_sub_le y p
    _ = K * |y j| := by
        rw [hyp, EuclideanSpace.single, PiLp.norm_single (p := 2), Real.norm_eq_abs]

/-- Along a flow line, the `j`-th coordinate satisfies `|y'| ≤ K |y|`. -/
private theorem coordinate_bounds (hv : IsLipschitzFieldOn v a b K)
    (htan : ∀ r ∈ Icc a b, ∀ x, x j = 0 → v r x j = 0) {t : ℝ} (ht : t ∈ Icc a b)
    (x : EuclideanSpace ℝ ι) :
    (∀ r ∈ Icc a b, HasDerivAt (fun q ↦ flowOn v a b q t x j)
      (v r (flowOn v a b r t x) j) r) ∧
      ∀ r ∈ Icc a b, |v r (flowOn v a b r t x) j| ≤ K * |flowOn v a b r t x j| := by
  refine ⟨fun r hr ↦ ?_, fun r hr ↦ abs_apply_le_of_tangent (hv.lipschitzWith r hr)
    (htan r hr) _⟩
  exact (EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt.comp_hasDerivAt r
    (hv.hasDerivAt_flowOn hr ht x)

/-- The flow of a field tangent to `x j = 0` preserves `{x j ≥ 0}`. -/
theorem IsLipschitzFieldOn.mapsTo_flowOn_nonneg (hv : IsLipschitzFieldOn v a b K)
    (htan : ∀ r ∈ Icc a b, ∀ x, x j = 0 → v r x j = 0) {s t : ℝ} (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) :
    MapsTo (flowOn v a b s t) {x | 0 ≤ x j} {x | 0 ≤ x j} := fun x hx ↦ by
  obtain ⟨hd, hK⟩ := coordinate_bounds hv htan ht x
  have h0 : 0 ≤ flowOn v a b t t x j := by rw [hv.flowOn_self ht]; exact hx
  exact PDE.Hyperbolic.Transport.nonneg_of_abs_deriv_le hd hK ht h0 s hs

/-- The flow of a field tangent to `x j = 0` preserves `{x j > 0}`. -/
theorem IsLipschitzFieldOn.mapsTo_flowOn_pos (hv : IsLipschitzFieldOn v a b K)
    (htan : ∀ r ∈ Icc a b, ∀ x, x j = 0 → v r x j = 0) {s t : ℝ} (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) :
    MapsTo (flowOn v a b s t) {x | 0 < x j} {x | 0 < x j} := fun x hx ↦ by
  obtain ⟨hd, hK⟩ := coordinate_bounds hv htan ht x
  have h0 : 0 < flowOn v a b t t x j := by rw [hv.flowOn_self ht]; exact hx
  exact PDE.Hyperbolic.Transport.pos_of_abs_deriv_le hd hK ht h0 s hs

/-- The flow of a field tangent to `x j = 0` preserves the hyperplane `{x j = 0}`. -/
theorem IsLipschitzFieldOn.mapsTo_flowOn_eq_zero (hv : IsLipschitzFieldOn v a b K)
    (htan : ∀ r ∈ Icc a b, ∀ x, x j = 0 → v r x j = 0) {s t : ℝ} (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) :
    MapsTo (flowOn v a b s t) {x | x j = 0} {x | x j = 0} := fun x hx ↦ by
  obtain ⟨hd, hK⟩ := coordinate_bounds hv htan ht x
  have h0 : flowOn v a b t t x j = 0 := by rw [hv.flowOn_self ht]; exact hx
  exact PDE.Hyperbolic.Transport.eqOn_zero_of_abs_deriv_le hd hK ht h0 hs

/-- `flowOn v a b s t` and `flowOn v a b t s` are inverse to each other on every set mapped into
itself by both. -/
theorem IsLipschitzFieldOn.bijOn_flowOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {v : ℝ → E → E} (hv : IsLipschitzFieldOn v a b K) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) {S : Set E} (hst : MapsTo (flowOn v a b s t) S S)
    (hts : MapsTo (flowOn v a b t s) S S) : BijOn (flowOn v a b s t) S S :=
  InvOn.bijOn ⟨fun x _ ↦ hv.flowOn_flowOn_self hs ht x, fun x _ ↦ hv.flowOn_flowOn_self ht hs x⟩
    hst hts

/-- The flow of a field tangent to `x j = 0` maps `{x j ≥ 0}` bijectively onto itself. -/
theorem IsLipschitzFieldOn.bijOn_flowOn_nonneg (hv : IsLipschitzFieldOn v a b K)
    (htan : ∀ r ∈ Icc a b, ∀ x, x j = 0 → v r x j = 0) {s t : ℝ} (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) : BijOn (flowOn v a b s t) {x | 0 ≤ x j} {x | 0 ≤ x j} :=
  hv.bijOn_flowOn hs ht (hv.mapsTo_flowOn_nonneg htan hs ht) (hv.mapsTo_flowOn_nonneg htan ht hs)

/-- The flow of a field tangent to `x j = 0` maps `{x j > 0}` bijectively onto itself. -/
theorem IsLipschitzFieldOn.bijOn_flowOn_pos (hv : IsLipschitzFieldOn v a b K)
    (htan : ∀ r ∈ Icc a b, ∀ x, x j = 0 → v r x j = 0) {s t : ℝ} (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) : BijOn (flowOn v a b s t) {x | 0 < x j} {x | 0 < x j} :=
  hv.bijOn_flowOn hs ht (hv.mapsTo_flowOn_pos htan hs ht) (hv.mapsTo_flowOn_pos htan ht hs)

/-- The flow of a field tangent to `x j = 0` maps `{x j = 0}` bijectively onto itself. -/
theorem IsLipschitzFieldOn.bijOn_flowOn_eq_zero (hv : IsLipschitzFieldOn v a b K)
    (htan : ∀ r ∈ Icc a b, ∀ x, x j = 0 → v r x j = 0) {s t : ℝ} (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) : BijOn (flowOn v a b s t) {x | x j = 0} {x | x j = 0} :=
  hv.bijOn_flowOn hs ht (hv.mapsTo_flowOn_eq_zero htan hs ht)
    (hv.mapsTo_flowOn_eq_zero htan ht hs)

end HalfSpace

end PDE.Analysis.ODE
