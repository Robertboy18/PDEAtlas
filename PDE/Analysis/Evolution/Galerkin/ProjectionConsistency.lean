/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Galerkin.TrialProjection
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.Ascoli

/-!
# Consistency of pivot-orthogonal Galerkin projections

A weak trial-space equation identifies the included coefficient derivative with the
pivot-orthogonal projection of the ambient drift. Comparing two such equations leaves
projection errors. Orthogonality expresses these errors using the other trajectory's state
tail, so a difference estimate does not require small projection tails of the drift itself.

The approximation theorem proves uniform convergence on compact pivot-space sets,
using their contractivity and mathlib's equicontinuity theorem. This applies, for example, to
the compact image of a continuous test path. For a family of trial states lying in one compact
set and bounded ambient drifts, the projected comparison work converges uniformly to
the ambient comparison work as both trial indices tend to infinity. Compact containment is a
hypothesis.

The ambient drift must take values in the pivot space at the trial states being compared.
The energy-space projection bounds may vary with the approximation index.
-/

@[expose] public section

noncomputable section


open Filter Set
open scoped InnerProductSpace Topology

namespace PDE.Analysis.Evolution.StableTrialProjection

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {T : GelfandTriple (V := V) (H := H)}

private theorem inner_pivotProjection_left
    {S : Submodule ℝ V} {K : NNReal} (P : StableTrialProjection T S K) (x y : H) :
    ⟪P.pivotProjection x, y⟫_ℝ = ⟪x, P.pivotProjection y⟫_ℝ := by
  have hx := P.pivotOrthogonal (P.projection x) y
  have hy := P.pivotOrthogonal (P.projection y) x
  change ⟪P.pivotProjection x, y - P.pivotProjection y⟫_ℝ = 0 at hx
  change ⟪P.pivotProjection y, x - P.pivotProjection x⟫_ℝ = 0 at hy
  rw [inner_sub_right] at hx hy
  rw [real_inner_comm x (P.pivotProjection y),
    real_inner_comm (P.pivotProjection x) (P.pivotProjection y)] at hy
  linarith

/-- If `⟪ι d, ι w⟫_H = ⟪f, ι w⟫_H` for every `w ∈ S`, then `ι d` is the pivot projection
`P f`. -/
theorem inclusion_eq_pivotProjection_of_inner_eq
    {S : Submodule ℝ V} {K : NNReal} (P : StableTrialProjection T S K)
    (d : S) (f : H)
    (heq : ∀ w : S, ⟪T.inclusion (d : V), T.inclusion (w : V)⟫_ℝ =
      ⟪f, T.inclusion (w : V)⟫_ℝ) :
    T.inclusion (d : V) = P.pivotProjection f := by
  let w : S := d - P.projection f
  have hw : T.inclusion (w : V) = T.inclusion (d : V) - P.pivotProjection f := by
    simp only [w, Submodule.coe_sub, map_sub, pivotProjection_apply]
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  rw [← hw]
  have htest := heq w
  have horth := P.pivotOrthogonal w f
  change ⟪T.inclusion (w : V), f - P.pivotProjection f⟫_ℝ = 0 at horth
  rw [inner_sub_right, real_inner_comm f (T.inclusion (w : V)),
    real_inner_comm (P.pivotProjection f) (T.inclusion (w : V))] at horth
  calc
    ⟪T.inclusion (w : V), T.inclusion (w : V)⟫_ℝ =
        ⟪T.inclusion (d : V), T.inclusion (w : V)⟫_ℝ -
          ⟪P.pivotProjection f, T.inclusion (w : V)⟫_ℝ := by
      conv_lhs => rw [hw]
      rw [inner_sub_left]
      rw [← hw]
    _ = 0 := by linarith

/-- Comparing different trial projections produces two state-tail pairings. The spaces
need not be nested and the drifts need not belong to either trial space. -/
theorem inner_projected_sub_eq
    {S R : Submodule ℝ V} {K L : NNReal}
    (P : StableTrialProjection T S K) (Q : StableTrialProjection T R L)
    (u : S) (v : R) (f g : H) :
    ⟪P.pivotProjection f - Q.pivotProjection g,
        T.inclusion (u : V) - T.inclusion (v : V)⟫_ℝ =
      ⟪f - g, T.inclusion (u : V) - T.inclusion (v : V)⟫_ℝ +
        ⟪f, T.inclusion (v : V) - P.pivotProjection (T.inclusion (v : V))⟫_ℝ +
        ⟪g, T.inclusion (u : V) - Q.pivotProjection (T.inclusion (u : V))⟫_ℝ := by
  rw [inner_sub_left, P.inner_pivotProjection_left, Q.inner_pivotProjection_left]
  simp only [map_sub, pivotProjection_apply, P.fixes, Q.fixes,
    inner_sub_left, inner_sub_right]
  ring

/-- If `ι du = P f` and `ι dv = Q g` in the weak sense and
`2 ⟪f - g, ι u - ι v⟫ ≤ C ‖ι u - ι v‖²`, then `2 ⟪ι du - ι dv, ι u - ι v⟫` is at most
`C ‖ι u - ι v‖² + 2 ‖f‖ ‖ι v - P(ι v)‖ + 2 ‖g‖ ‖ι u - Q(ι u)‖`. -/
theorem two_mul_inner_sub_le_of_weak_equations
    {S R : Submodule ℝ V} {K L : NNReal}
    (P : StableTrialProjection T S K) (Q : StableTrialProjection T R L)
    (u du : S) (v dv : R) (f g : H) {C : ℝ}
    (hu : ∀ w : S, ⟪T.inclusion (du : V), T.inclusion (w : V)⟫_ℝ =
      ⟪f, T.inclusion (w : V)⟫_ℝ)
    (hv : ∀ w : R, ⟪T.inclusion (dv : V), T.inclusion (w : V)⟫_ℝ =
      ⟪g, T.inclusion (w : V)⟫_ℝ)
    (hfg : 2 * ⟪f - g, T.inclusion (u : V) - T.inclusion (v : V)⟫_ℝ ≤
      C * ‖T.inclusion (u : V) - T.inclusion (v : V)‖ ^ 2) :
    2 * ⟪T.inclusion (du : V) - T.inclusion (dv : V),
        T.inclusion (u : V) - T.inclusion (v : V)⟫_ℝ ≤
      C * ‖T.inclusion (u : V) - T.inclusion (v : V)‖ ^ 2 +
        2 * ‖f‖ *
          ‖T.inclusion (v : V) - P.pivotProjection (T.inclusion (v : V))‖ +
        2 * ‖g‖ *
          ‖T.inclusion (u : V) - Q.pivotProjection (T.inclusion (u : V))‖ := by
  rw [P.inclusion_eq_pivotProjection_of_inner_eq du f hu,
    Q.inclusion_eq_pivotProjection_of_inner_eq dv g hv,
    P.inner_projected_sub_eq Q u v f g]
  have hf := real_inner_le_norm f
    (T.inclusion (v : V) - P.pivotProjection (T.inclusion (v : V)))
  have hg := real_inner_le_norm g
    (T.inclusion (u : V) - Q.pivotProjection (T.inclusion (u : V)))
  linarith

/-- If every `h ∈ H` is eventually approximated by the trial spaces, the pivot projections
converge to the identity uniformly on every compact subset of `H`. The energy bounds `K n`
may depend on `n`. -/
theorem tendstoUniformlyOn_pivotProjection_of_eventually_approximable
    {S : ℕ → Submodule ℝ V} {K : ℕ → NNReal}
    (P : ∀ n, StableTrialProjection T (S n) (K n))
    (hdense : ∀ h : H, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∃ w : S n, ‖h - T.inclusion (w : V)‖ < ε)
    {A : Set H} (hA : IsCompact A) :
    TendstoUniformlyOn (fun n h ↦ (P n).pivotProjection h) id atTop A := by
  let : CompactSpace A := isCompact_iff_compactSpace.mp hA
  have hlip (n : ℕ) : LipschitzWith 1 (fun h : A ↦ (P n).pivotProjection h) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [NNReal.coe_one, one_mul, dist_eq_norm, ← map_sub,
      Subtype.dist_eq] using (P n).norm_pivotProjection_apply_le ((x : H) - y)
  have hequi := (LipschitzWith.uniformEquicontinuous
    (fun n (h : A) ↦ (P n).pivotProjection h) 1 hlip).equicontinuous
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  apply UniformFun.tendsto_iff_tendstoUniformly.mp
  apply (hequi.tendsto_uniformFun_iff_pi atTop _).mpr
  apply tendsto_pi_nhds.mpr
  intro h
  refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
  filter_upwards [hdense h ε hε] with n hn
  obtain ⟨w, hw⟩ := hn
  rw [dist_eq_norm, norm_sub_rev]
  exact ((P n).norm_sub_inclusion_projection_le h w).trans_lt hw

/-- The two-projection comparison defect tends uniformly to zero when all trial
states lie in one compact pivot set and their ambient drifts are uniformly bounded there.
The limit is joint in the two trial indices and uniform over the parameter set `I`. -/
theorem tendstoUniformlyOn_inner_projected_sub_sub_of_isCompact
    {ι : Type*} {I : Set ι} {S : ℕ → Submodule ℝ V} {K : ℕ → NNReal}
    (P : ∀ n, StableTrialProjection T (S n) (K n))
    (hdense : ∀ h : H, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∃ w : S n, ‖h - T.inclusion (w : V)‖ < ε)
    (u : ∀ n, ι → S n) (f : ℕ → ι → H)
    {A : Set H} (hA : IsCompact A)
    (hu : ∀ n t, t ∈ I → T.inclusion (u n t : V) ∈ A)
    {M : ℝ} (hM : 0 ≤ M) (hf : ∀ n t, t ∈ I → ‖f n t‖ ≤ M) :
    TendstoUniformlyOn
      (fun p : ℕ × ℕ ↦ fun t ↦
        ⟪(P p.1).pivotProjection (f p.1 t) - (P p.2).pivotProjection (f p.2 t),
          T.inclusion (u p.1 t : V) - T.inclusion (u p.2 t : V)⟫_ℝ -
        ⟪f p.1 t - f p.2 t,
          T.inclusion (u p.1 t : V) - T.inclusion (u p.2 t : V)⟫_ℝ)
      (fun _ ↦ 0) atTop I := by
  have hproj := tendstoUniformlyOn_pivotProjection_of_eventually_approximable P hdense hA
  refine Metric.tendstoUniformlyOn_iff.mpr fun ε hε ↦ ?_
  have hpos : 0 < M + 1 := by positivity
  let δ : ℝ := ε / (2 * (M + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (Metric.tendstoUniformlyOn_iff.mp hproj δ hδ)
  filter_upwards [eventually_ge_atTop (N, N)] with p hp
  intro t ht
  have htail (m n : ℕ) (hm : N ≤ m) :
      ‖T.inclusion (u n t : V) -
        (P m).pivotProjection (T.inclusion (u n t : V))‖ < δ := by
    simpa only [id_eq, dist_eq_norm] using hN m hm _ (hu n t ht)
  have hwork (m n : ℕ) (hm : N ≤ m) :
      |⟪f m t, T.inclusion (u n t : V) -
        (P m).pivotProjection (T.inclusion (u n t : V))⟫_ℝ| < (M + 1) * δ := by
    calc
      _ ≤ ‖f m t‖ * ‖T.inclusion (u n t : V) -
          (P m).pivotProjection (T.inclusion (u n t : V))‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ (M + 1) * ‖T.inclusion (u n t : V) -
          (P m).pivotProjection (T.inclusion (u n t : V))‖ :=
        mul_le_mul_of_nonneg_right ((hf m t ht).trans (by linarith)) (norm_nonneg _)
      _ < (M + 1) * δ := mul_lt_mul_of_pos_left (htail m n hm) hpos
  rw [dist_eq_norm, zero_sub, norm_neg, Real.norm_eq_abs,
    (P p.1).inner_projected_sub_eq (P p.2) (u p.1 t) (u p.2 t)]
  have hcancel (a b c : ℝ) : a + b + c - a = b + c := by ring
  rw [hcancel]
  calc
    _ ≤ _ := abs_add_le _ _
    _ < (M + 1) * δ + (M + 1) * δ :=
      add_lt_add (hwork p.1 p.2 hp.1) (hwork p.2 p.1 hp.2)
    _ = ε := by
      dsimp [δ]
      field_simp
      ring

end PDE.Analysis.Evolution.StableTrialProjection
