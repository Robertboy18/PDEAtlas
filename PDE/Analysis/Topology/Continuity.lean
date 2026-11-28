/-
Authors: Levent Alpöge, Tristan Buckmaster

The lemmas of this file come from modules of the Lean package of the paper
"Finite-time blow-up for the Navier–Stokes equations"
(https://github.com/tristanbuckmaster/navier-stokes, folder lean/, commit ad53419),
where they were steps of longer proofs. They were included in BlowupZoo
(https://github.com/lean-dojo/BlowupZoo, folder AtlasCandidates/) with the permission of the
authors (20 November 2026) and moved here from there; the file NOTICE of this repository records it.
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Normed.Affine.Convex
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Data.List.GetD
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Linarith.NNRealPreprocessor
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Topology.Metrizable.ContinuousMap
public import Mathlib.Topology.PartitionOfUnity
public import PDE.Analysis.Complex.Numbers
public import PDE.Analysis.Order.MinMax
public import PDE.Analysis.Scalar.Inequalities.Basic
public import PDE.Analysis.Scalar.Powers.Basic

set_option linter.style.header false

/-!
# Continuity of composed functions

The lemmas state continuity, continuity on a set and Lipschitz bounds for products, compositions and
restrictions of particular shapes. The proofs use `fun_prop`, `Continuous.comp` and the lemmas of
Mathlib on Lipschitz maps.

## Main results

* `PDE.Analysis.continuous_cexp_neg_pair_mul_I`: For `κ : ℤ × ℤ`, the function
  `p ↦ Complex.exp (-(((2 * π * κ.1 * p.1 + κ.2 * p.2 : ℝ) : ℂ) * Complex.I))` is continuous on
  `ℝ × ℝ`.
* `PDE.Analysis.apply_zero_eq_zero_of_continuousOn_Ici`: If `ψ : ℝ → ℝ` is continuous on `Ici 0` and
  `ψ τ = 0` for all `τ > 0`, then `ψ 0 = 0`.
* `PDE.Analysis.continuousOn_of_eps_delta_norm_sub`: Criterion with ε and δ for continuity in
  operator norm: for a family `T : (Fin k → ℝ) → E →L[ℝ] F` of continuous linear maps and a set `S`,
  if for every `p ∈ S` and `ε > 0` there is `δ > 0` with `‖T q - T p‖ < ε` for all `q ∈ S` with
  `dist q p < δ`, then `T` is continuous on `S`.
* `PDE.Analysis.continuous_derivative_sq_add_div_sq_mul`: For a real polynomial `p` and a natural
  number `i ≤ 1`, with `X ∣ p` when `i = 1`, the function
  `r ↦ ((derivative p).eval r ^ 2 + (i : ℝ) ^ 2 * p.eval r ^ 2 / r ^ 2) * r` is continuous on `ℝ`.
* `PDE.Analysis.continuous_glue_of_eq_at_breakpoints`: Let `φ : Z → ℝ` be continuous on a
  topological space, `m` a strictly increasing list of reals, and `g : ℕ → Z → ℂ` with `g k`
  continuous for `k ≤ m.length` and `g k z = g (k + 1) z` whenever `k < m.length` and `φ z = m[k]`.
  Then `z ↦ g (m.filter (· ≤ φ z)).length z` is continuous: this function uses `g k` at the points
  where exactly `k` entries of `m` are `≤ φ z`.
* `PDE.Analysis.continuous_of_continuous_uncurry_left`: If `F : ℝ → ℝ → ℝ` is jointly continuous,
  that is, `p ↦ F p.1 p.2` is continuous on `ℝ × ℝ`, then for every `r` the slice `z ↦ F r z` is
  continuous.
* `PDE.Analysis.exists_fixedPoint_norm_le_two_mul`: Let `Y` be a complete normed additive group,
  `A ≥ 0` and `q ≥ 0` reals with `8 * q * A ≤ 1`, and `Φ : Y → Y` a map with
  `‖Φ z‖ ≤ A + q * ‖z‖ ^ 2` and `‖Φ z - Φ z'‖ ≤ q * (‖z‖ + ‖z'‖) * ‖z - z'‖` for all `z`, `z'`. Then
  `Φ` has a fixed point `z` with `‖z‖ ≤ 2 * A`.
* `PDE.Analysis.exists_sum_smul_sub_le_of_dense`: Let `K` be a compact Hausdorff space, `E` a real
  normed space, `f : C(K, E)`, `S` a dense subset of `E` and `ε > 0`. Then there are a natural `m`,
  continuous functions `ρ l : C(K, ℝ)` with values in `[0, 1]` and vectors `x l ∈ S`, for
  `l : Fin m`, such that `‖∑ l, ρ l t • x l - f t‖ ≤ ε` for every `t`.

There are 46 further lemmas of the same kind.

## References

* Levent Alpöge and Tristan Buckmaster, the Lean package of the paper "Finite-time blow-up for the
  Navier–Stokes equations", <https://github.com/tristanbuckmaster/navier-stokes>, folder `lean/`,
  commit `ad53419`: the lemmas of this module and their proofs, adapted to this library. See
  `NOTICE` for attribution and permission.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Topology Filter Polynomial
open scoped NNReal

namespace PDE.Analysis

/-- If `g : ℝ × ℝ → ℝ` is Lipschitz with constant `K` and `g (0, z) = 0` for all `z`, then
`|g p| ≤ K * |p.1|` for every `p`. -/
theorem abs_le_mul_abs_fst_of_lipschitzWith {g : ℝ × ℝ → ℝ} {K : NNReal} (hK : LipschitzWith K g)
    (h0 : ∀ z, g (0, z) = 0) (p : ℝ × ℝ) : |g p| ≤ K * |p.1| := by
  have := hK.dist_le_mul p (0, p.2)
  rw [h0, Prod.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq] at this
  simpa using this

/-- If `g : ℝ × ℝ → ℝ` is Lipschitz with constant `K` and `g (x, 0) = 0` for all `x`, then
`|g p| ≤ K * |p.2|` for every `p`. -/
theorem abs_le_mul_abs_snd_of_lipschitzWith {g : ℝ × ℝ → ℝ} {K : NNReal} (hK : LipschitzWith K g)
    (h0 : ∀ x, g (x, 0) = 0) (p : ℝ × ℝ) : |g p| ≤ K * |p.2| := by
  have := hK.dist_le_mul p (p.1, 0)
  rw [h0, Prod.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq] at this
  simpa using this

/-- Gluing Lipschitz pieces along a strictly increasing list `m` of real breakpoints. If every `g k`
with `k ≤ m.length` satisfies `|g k u - g k v| ≤ M * |u - v|` for `u`, `v` in `Set.Icc lo hi`, and
`g k m[k] = g (k + 1) m[k]` for every `k < m.length`, then the glued function, whose value at `u` is
`g n u` with `n` the number of breakpoints `≤ u`, satisfies the same bound for `u`, `v` in
`Set.Icc lo hi`. The proof is by induction on the list: two points on different sides of the first
breakpoint are compared through that breakpoint, where the two pieces agree. -/
theorem abs_sub_le_mul_of_piecewise_list (lo hi M : ℝ) :
    ∀ (m : List ℝ), m.Pairwise (· < ·) → ∀ (g : ℕ → ℝ → ℝ),
      (∀ k ≤ m.length, ∀ u ∈ Set.Icc lo hi, ∀ v ∈ Set.Icc lo hi, |g k u - g k v| ≤ M * |u - v|) →
      (∀ k (hk : k < m.length), g k m[k] = g (k + 1) m[k]) →
      ∀ u ∈ Set.Icc lo hi, ∀ v ∈ Set.Icc lo hi,
        |g ((m.filter (fun b ↦ decide (b ≤ u))).length) u -
          g ((m.filter (fun b ↦ decide (b ≤ v))).length) v| ≤ M * |u - v|
  | [], _, g, hg, _ => by
    intro u hu v hv
    simpa using hg 0 le_rfl u hu v hv
  | b :: m', hm, g, hg, hj => by
    rw [List.pairwise_cons] at hm
    have ih := abs_sub_le_mul_of_piecewise_list lo hi M m' hm.2 (fun k ↦ g (k + 1))
      (fun k hk ↦ hg (k + 1) (by simp; omega))
      (fun k hk ↦ hj (k + 1) (by simp; omega))
    have hnil : ∀ z, z ≤ b → m'.filter (fun c ↦ decide (c ≤ z)) = [] := by
      intro z hz
      rw [List.filter_eq_nil_iff]
      intro c hc
      have := hm.1 c hc
      simp only [decide_eq_true_eq, not_le]
      linarith
    have e : ∀ z, g (((b :: m').filter (fun c ↦ decide (c ≤ z))).length) z =
        if b ≤ z then g ((m'.filter (fun c ↦ decide (c ≤ z))).length + 1) z else g 0 z := by
      intro z
      by_cases h : b ≤ z
      · simp [h]
      · simp [h, hnil z (le_of_lt (not_le.1 h))]
    have hjb : g ((m'.filter (fun c ↦ decide (c ≤ b))).length + 1) b = g 0 b := by
      rw [hnil b le_rfl]
      have := hj 0 (by simp)
      simpa using this.symm
    have cross : ∀ u ∈ Set.Icc lo hi, ∀ v ∈ Set.Icc lo hi, b ≤ u → v < b →
        |g ((m'.filter (fun c ↦ decide (c ≤ u))).length + 1) u - g 0 v| ≤ M * |u - v| := by
      intro u hu v hv hbu hvb
      have hb : b ∈ Set.Icc lo hi := ⟨by linarith [hv.1], by linarith [hu.2]⟩
      have h1 := ih u hu b hb
      have h2 := hg 0 (Nat.zero_le _) b hb v hv
      rw [hjb] at h1
      calc _ ≤ |g ((m'.filter (fun c ↦ decide (c ≤ u))).length + 1) u - g 0 b| + |g 0 b - g 0 v| :=
            abs_sub_le _ _ _
        _ ≤ M * |u - b| + M * |b - v| := add_le_add h1 h2
        _ = M * |u - v| := by
          rw [abs_of_nonneg (by
            linarith : (0 : ℝ) ≤ u - b), abs_of_nonneg (by linarith : (0 : ℝ) ≤ b - v),
            abs_of_nonneg (by linarith : (0 : ℝ) ≤ u - v)]
          ring
    intro u hu v hv
    rw [e u, e v]
    split_ifs with h1 h2 h2
    · exact ih u hu v hv
    · exact cross u hu v hv h1 (not_le.1 h2)
    · rw [abs_sub_comm, abs_sub_comm u]
      exact cross v hv u hu h2 (not_le.1 h1)
    · exact hg 0 (Nat.zero_le _) u hu v hv

/-- If `ψ : ℝ → ℝ` is continuous on `Ici 0` and `ψ τ = 0` for all `τ > 0`, then `ψ 0 = 0`. -/
theorem apply_zero_eq_zero_of_continuousOn_Ici {ψ : ℝ → ℝ} (hc : ContinuousOn ψ (Ici 0))
    (h : ∀ τ > 0, ψ τ = 0) :
    ψ 0 = 0 := by
  have hψ : ContinuousWithinAt ψ (Ioi 0) 0 := (hc 0 (le_refl (0 : ℝ))).mono Ioi_subset_Ici_self
  refine tendsto_nhds_unique hψ.tendsto (tendsto_const_nhds.congr' ?_)
  exact eventually_nhdsWithin_of_forall fun τ hτ ↦ (h τ hτ).symm

/-- For real `L`, `r` and `s₀` with `s₀ * r + L ≠ 0`, the function `s ↦ s * r / (s * r + L)` is
continuous at `s₀`. -/
theorem continuousAt_mul_div_mul_add (L r s₀ : ℝ) (hne : s₀ * r + L ≠ 0) :
    ContinuousAt (fun s : ℝ ↦ s * r / (s * r + L)) s₀ :=
  (continuousAt_id.mul continuousAt_const).div ((continuousAt_id.mul continuousAt_const).add
      continuousAt_const) hne

/-- Let `T : ℝ → E →L[ℝ] E` be a family of continuous linear maps on a real Hilbert space with
`‖T τ‖ ≤ exp (-(τ / 4))` for `τ ≥ 0` and with `τ ↦ T τ y` continuous on `Set.Ici 0` for every `y`.
Then for every continuous `g : ℝ → E` the function `τ ↦ T τ (g τ)` is continuous on `Set.Ici 0`. The
proof writes `T τ (g τ) = T τ (g τ - g τ₀) + T τ (g τ₀)` and bounds the first term by
`‖g τ - g τ₀‖`. -/
theorem continuousOn_apply_of_norm_le_exp_neg {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (T : ℝ → E →L[ℝ] E)
    (hnorm : ∀ τ, 0 ≤ τ → ‖T τ‖ ≤ Real.exp (-(τ / 4)))
    (hcont : ∀ y, ContinuousOn (fun τ ↦ T τ y) (Ici 0))
    (g : ℝ → E) (hg : Continuous g) : ContinuousOn (fun τ ↦ T τ (g τ)) (Ici 0) := by
  intro τ₀ hτ₀
  have h1 : Tendsto (fun τ ↦ T τ (g τ - g τ₀)) (𝓝[Ici 0] τ₀) (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun τ ↦ ‖g τ - g τ₀‖)
    · filter_upwards [self_mem_nhdsWithin] with τ hτ
      have hτ' : (0 : ℝ) ≤ τ := hτ
      have he : Real.exp (-(τ / 4)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
      calc ‖T τ (g τ - g τ₀)‖ ≤ ‖T τ‖ * ‖g τ - g τ₀‖ := (T τ).le_opNorm _
        _ ≤ 1 * ‖g τ - g τ₀‖ :=
          mul_le_mul_of_nonneg_right ((hnorm τ hτ').trans he) (norm_nonneg _)
        _ = ‖g τ - g τ₀‖ := one_mul _
    · have h : Tendsto (fun τ ↦ ‖g τ - g τ₀‖) (𝓝 τ₀) (𝓝 ‖g τ₀ - g τ₀‖) :=
        ((hg.sub continuous_const).norm).tendsto τ₀
      rw [sub_self, norm_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun τ ↦ T τ (g τ₀)) (𝓝[Ici 0] τ₀) (𝓝 (T τ₀ (g τ₀))) := hcont (g τ₀) τ₀ hτ₀
  have h3 := h1.add h2
  rw [zero_add] at h3
  exact Tendsto.congr (fun τ ↦ by rw [← map_add, sub_add_cancel]) h3

/-- Let `dil heat : ℝ → E →L[ℝ] E` be families of continuous linear maps on a real normed space such
that `μ ↦ dil μ z` is continuous on `Set.Ioi 0` for every `z`, `‖dil μ z‖ ≤ ‖z‖` whenever
`0 < μ ≤ 1`, and `t ↦ heat t z` is continuous on `Set.Ici 0` for every `z`. Then for every `y` the
curve `τ ↦ ((dil (exp (-τ))).comp (heat (1 - exp (-τ)))) y` is continuous on `Set.Ici 0`. The proof
splits the increment into `dil (exp (-τ))` applied to the increment of `heat`, which the bound on
`dil` controls, and the increment of `dil` at a fixed vector. -/
theorem continuousOn_comp_apply_exp_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (dil heat : ℝ → E →L[ℝ] E)
    (hDc : ∀ z, ContinuousOn (fun μ ↦ dil μ z) (Ioi 0))
    (hDle : ∀ μ, 0 < μ → μ ≤ 1 → ∀ z, ‖dil μ z‖ ≤ ‖z‖)
    (hHc : ∀ z, ContinuousOn (fun t ↦ heat t z) (Ici 0)) (y : E) :
    ContinuousOn (fun τ ↦ (dil (Real.exp (-τ))).comp (heat (1 - Real.exp (-τ))) y) (Ici 0) := by
  simp only [ContinuousLinearMap.comp_apply]
  have hmapH : MapsTo (fun τ : ℝ ↦ 1 - Real.exp (-τ)) (Ici 0) (Ici 0) := fun τ hτ ↦ by
    have := Real.exp_le_one_iff.2 (neg_nonpos.2 (mem_Ici.1 hτ))
    simp only [mem_Ici]
    linarith
  have hb : ContinuousOn (fun τ : ℝ ↦ heat (1 - Real.exp (-τ)) y) (Ici 0) :=
    (hHc y).comp (by fun_prop : Continuous fun τ : ℝ ↦ 1 - Real.exp (-τ)).continuousOn hmapH
  have hmapD : MapsTo (fun τ : ℝ ↦ Real.exp (-τ)) (Ici 0) (Ioi 0) := fun τ _ ↦ Real.exp_pos _
  intro τ₀ hτ₀
  have hA : ContinuousWithinAt
      (fun τ ↦ dil (Real.exp (-τ)) (heat (1 - Real.exp (-τ₀)) y)) (Ici 0) τ₀ :=
    ((hDc _).comp (by fun_prop : Continuous fun τ : ℝ ↦ Real.exp (-τ)).continuousOn hmapD) τ₀ hτ₀
  have hB := hb τ₀ hτ₀
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero] at hA hB ⊢
  have hAB := hA.add hB
  rw [zero_add] at hAB
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hAB
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  have e : dil (Real.exp (-τ)) (heat (1 - Real.exp (-τ)) y) -
      dil (Real.exp (-τ₀)) (heat (1 - Real.exp (-τ₀)) y) =
      dil (Real.exp (-τ)) (heat (1 - Real.exp (-τ)) y - heat (1 - Real.exp (-τ₀)) y) +
      (dil (Real.exp (-τ)) (heat (1 - Real.exp (-τ₀)) y) -
        dil (Real.exp (-τ₀)) (heat (1 - Real.exp (-τ₀)) y)) := by
    rw [map_sub]
    abel
  rw [e]
  have h1 := norm_add_le (dil (Real.exp (-τ)) (heat (1 - Real.exp (-τ)) y -
      heat (1 - Real.exp (-τ₀)) y)) (dil (Real.exp (-τ)) (heat (1 - Real.exp (-τ₀)) y) -
        dil (Real.exp (-τ₀)) (heat (1 - Real.exp (-τ₀)) y))
  have h2 := hDle (Real.exp (-τ)) (Real.exp_pos _)
    (Real.exp_le_one_iff.2 (neg_nonpos.2 (mem_Ici.1 hτ)))
    (heat (1 - Real.exp (-τ)) y - heat (1 - Real.exp (-τ₀)) y)
  linarith

/-- For continuous `wt t : ℝ → ℝ` and any set `s ⊆ ℝ × ℝ`, the function
`p ↦ ((wt p.1 * t p.1 : ℝ) : ℂ)` is continuous on `s`. -/
theorem continuousOn_ofReal_mul_comp_fst {wt t : ℝ → ℝ} (hwt : Continuous wt) (ht : Continuous t)
    (s : Set (ℝ × ℝ)) :
    ContinuousOn (fun p : ℝ × ℝ ↦ ((wt p.1 * t p.1 : ℝ) : ℂ)) s :=
  (Complex.continuous_ofReal.comp ((hwt.comp continuous_fst).mul
      (ht.comp continuous_fst))).continuousOn

/-- Criterion with ε and δ for continuity in operator norm: for a family
`T : (Fin k → ℝ) → E →L[ℝ] F` of continuous linear maps and a set `S`, if for every `p ∈ S` and
`ε > 0` there is `δ > 0` with `‖T q - T p‖ < ε` for all `q ∈ S` with `dist q p < δ`, then `T` is
continuous on `S`. -/
theorem continuousOn_of_eps_delta_norm_sub {k : ℕ} {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {S : Set (Fin k → ℝ)} {T : (Fin k → ℝ) → E →L[ℝ] F}
    (hT : ∀ p ∈ S, ∀ ε > 0, ∃ δ > 0, ∀ q ∈ S, dist q p < δ → ‖T q - T p‖ < ε) :
    ContinuousOn T S := by
  intro p hp
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hT p hp ε hε
  exact ⟨δ, hδ, fun {q} hq hqp ↦ by rw [dist_eq_norm]; exact h q hq hqp⟩

/-- Joint continuity for a strongly continuous family of contractions: let `T : ℝ → E →L[ℝ] E` on a
real normed space satisfy `‖T τ‖ ≤ 1` for `τ ≥ 0`, with `τ ↦ T τ y` continuous on `Set.Ici 0` for
every `y`. If `a : Y → ℝ` is continuous and nonnegative and `v : Y → E` is continuous on a
topological space `Y`, then `y ↦ T (a y) (v y)` is continuous. The proof writes
`T (a y) (v y) = (T (a y) (v y) - T (a y) (v y₀)) + T (a y) (v y₀)` and bounds the first term by
`‖v y - v y₀‖`. -/
theorem continuous_apply_of_norm_le_one {E Y : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace Y] (T : ℝ → E →L[ℝ] E)
    (hnorm : ∀ τ, 0 ≤ τ → ‖T τ‖ ≤ 1) (hcont : ∀ y, ContinuousOn (fun τ ↦ T τ y) (Ici 0))
    (a : Y → ℝ) (ha : Continuous a) (ha0 : ∀ y, 0 ≤ a y) (v : Y → E) (hv : Continuous v) :
    Continuous (fun y ↦ T (a y) (v y)) := by
  refine continuous_iff_continuousAt.2 fun y₀ ↦ ?_
  have h2 : Continuous (fun y ↦ T (a y) (v y₀)) :=
    (hcont (v y₀)).comp_continuous ha (fun y ↦ ha0 y)
  have h1 : Tendsto (fun y ↦ T (a y) (v y) - T (a y) (v y₀)) (𝓝 y₀) (𝓝 0) := by
    refine squeeze_zero_norm (fun y ↦ ?_) (?_ : Tendsto (fun y ↦ ‖v y - v y₀‖) (𝓝 y₀) (𝓝 0))
    · rw [← map_sub]
      exact ((T (a y)).le_opNorm _).trans
        (by simpa using mul_le_mul_of_nonneg_right (hnorm _ (ha0 y)) (norm_nonneg (v y - v y₀)))
    · have := ((hv.sub (continuous_const (y := v y₀))).norm).tendsto y₀
      simpa using this
  have := h1.add (h2.tendsto y₀)
  change Tendsto _ _ _
  simpa using this

/-- For `n : ℤ`, the function `θ ↦ Complex.exp (-(((n * θ : ℝ) : ℂ) * Complex.I))` is continuous on
`ℝ`. -/
theorem continuous_cexp_neg_int_mul_mul_I (n : ℤ) :
    Continuous (fun θ : ℝ ↦ Complex.exp (-(((n * θ : ℝ) : ℂ) * Complex.I))) := by
  fun_prop

/-- For `κ : ℤ × ℤ`, the function
`p ↦ Complex.exp (-(((2 * π * κ.1 * p.1 + κ.2 * p.2 : ℝ) : ℂ) * Complex.I))` is continuous on
`ℝ × ℝ`. -/
theorem continuous_cexp_neg_pair_mul_I (κ : ℤ × ℤ) :
    Continuous fun p : ℝ × ℝ ↦ Complex.exp (-(((2 * Real.pi * κ.1 * p.1 + κ.2 * p.2 : ℝ) : ℂ) *
        Complex.I)) := by
  fun_prop

/-- For `a : ℤ`, the function `τ ↦ Complex.exp (((2 * π * (a : ℝ) * τ : ℝ) : ℂ) * Complex.I)` is
continuous on `ℝ`. -/
theorem continuous_cexp_two_pi_int_mul_I (a : ℤ) :
    Continuous (fun τ : ℝ ↦ Complex.exp (((2 * Real.pi * (a : ℝ) * τ : ℝ) : ℂ) * Complex.I)) := by
  fun_prop

/-- If `χ : ℝ → ℝ` and all `u j : ℝ → ℝ` are continuous, then for every real `R` and every `q : ℕ`
the function `p ↦ χ (p.1 / R) * ∑ j ∈ Finset.range (q + 1), p.1 ^ j * u j p.2` is continuous on
`ℝ × ℝ`. -/
theorem continuous_comp_div_mul_sum_pow_mul (χ : ℝ → ℝ) (hχ : Continuous χ) (R : ℝ) (q : ℕ)
    (u : ℕ → ℝ → ℝ)
    (hu : ∀ j, Continuous (u j)) :
    Continuous (fun p : ℝ × ℝ ↦ χ (p.1 / R) * ∑ j ∈ Finset.range (q + 1), p.1 ^ j * u j p.2) := by
  refine (hχ.comp (continuous_fst.div_const R)).mul (continuous_finsetSum _ fun j _ ↦ ?_)
  exact (continuous_fst.pow j).mul ((hu j).comp continuous_snd)

/-- If `a ≤ b` and `u : ℝ → X` is continuous on `Icc a b`, with `X` a real Banach space, then
`s ↦ u (max a (min b s))` is continuous on `ℝ`. -/
theorem continuous_comp_max_min_of_continuousOn_Icc {X : Type} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X] {a b : ℝ} (hab : a ≤ b) {u : ℝ → X}
    (hu : ContinuousOn u (Icc a b)) :
    Continuous (fun s ↦ u (max a (min b s))) :=
  hu.comp_continuous (continuous_const.max (continuous_const.min continuous_id))
      (max_min_mem_Icc hab)

/-- For a real polynomial `p` and a natural number `i ≤ 1`, with `X ∣ p` when `i = 1`, the function
`r ↦ ((derivative p).eval r ^ 2 + (i : ℝ) ^ 2 * p.eval r ^ 2 / r ^ 2) * r` is continuous on `ℝ`.
Proof idea: for `i = 0` the second term vanishes, and for `i = 1` writing `p = X * s` turns that
term into `s.eval r ^ 2 * r`, also at `r = 0`. -/
theorem continuous_derivative_sq_add_div_sq_mul (i : ℕ) (hi : i ≤ 1) (p : ℝ[X])
    (hdiv : i = 1 → X ∣ p) :
    Continuous fun r : ℝ ↦ ((derivative p).eval r ^ 2 + (i : ℝ) ^ 2 * p.eval r ^ 2 / r ^ 2) * r :=
        by
  obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
  · simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
      zero_div, add_zero]
    fun_prop
  · obtain ⟨s, rfl⟩ := hdiv rfl
    have e : (fun r : ℝ ↦ ((derivative (X * s)).eval r ^ 2 + ((1 : ℕ) : ℝ) ^ 2 *
        (X * s).eval r ^ 2 / r ^ 2) * r)
        = fun r ↦ (derivative (X * s)).eval r ^ 2 * r + s.eval r ^ 2 * r := by
      funext r
      by_cases hr : r = 0
      · subst hr; simp
      · simp only [eval_mul, eval_X, Nat.cast_one, one_pow, one_mul]
        field_simp
    rw [e]
    fun_prop

/-- If `α : ℝ → ℝ` is continuous and every point of `tsupport α` is positive, then `r ↦ α r / r` is
continuous on `ℝ`. Proof idea: `α` vanishes near `0`, so the quotient is `0` there, and away from
`0` it is a quotient of continuous functions. -/
theorem continuous_div_id_of_tsupport_pos {α : ℝ → ℝ} (hα : Continuous α)
    (hs : ∀ x ∈ tsupport α, 0 < x) :
    Continuous (fun r ↦ α r / r) := by
  rw [continuous_iff_continuousAt]
  intro r
  by_cases hr : r = 0
  · subst hr
    have h0 : (0 : ℝ) ∉ tsupport α := fun h ↦ lt_irrefl (0 : ℝ) (hs 0 h)
    have e : (fun _ : ℝ ↦ (0 : ℝ)) =ᶠ[𝓝 0] fun r ↦ α r / r := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 h0] with x hx
      simp only [Pi.zero_apply] at hx
      simp [hx]
    exact continuousAt_const.congr e
  · exact hα.continuousAt.div continuousAt_id hr

/-- Let `Y` be a topological space and `F : Y → ℝ → ℝ → ℂ` jointly continuous, that is,
`q ↦ F q.1.1 q.1.2 q.2` is continuous on `(Y × ℝ) × ℝ`. Then
`y ↦ ∫ τ in 0..1, ∫ φ in 0..2 * π, F y τ φ` is continuous. -/
theorem continuous_double_integral {Y : Type*} [TopologicalSpace Y] {F : Y → ℝ → ℝ → ℂ}
    (hF : Continuous (fun q : (Y × ℝ) × ℝ ↦ F q.1.1 q.1.2 q.2)) :
    Continuous (fun y ↦ ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi), F y τ φ) := by
  have h1 : Continuous (Function.uncurry fun (x : Y × ℝ) (φ : ℝ) ↦ F x.1 x.2 φ) := hF
  have h2 := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := volume) h1 0
    (2 * Real.pi)
  have h3 : Continuous (Function.uncurry fun (y : Y) (τ : ℝ) ↦
      ∫ φ in (0 : ℝ)..(2 * Real.pi), F y τ φ) := h2
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume) h3 0 1

/-- Let `φ : Z → ℝ` be continuous on a topological space, `m` a strictly increasing list of reals,
and `g : ℕ → Z → ℂ` with `g k` continuous for `k ≤ m.length` and `g k z = g (k + 1) z` whenever
`k < m.length` and `φ z = m[k]`. Then `z ↦ g (m.filter (· ≤ φ z)).length z` is continuous: this
function uses `g k` at the points where exactly `k` entries of `m` are `≤ φ z`. Proof idea:
induction on the list, splitting at its first entry with `Continuous.if_le`. -/
theorem continuous_glue_of_eq_at_breakpoints {Z : Type*} [TopologicalSpace Z] (φ : Z → ℝ)
    (hφ : Continuous φ) :
    ∀ (m : List ℝ), m.Pairwise (· < ·) → ∀ (g : ℕ → Z → ℂ), (∀ k ≤ m.length, Continuous (g k)) →
      (∀ k (hk : k < m.length), ∀ z, φ z = m[k] → g k z = g (k + 1) z) →
      Continuous (fun z ↦ g ((m.filter (fun b ↦ decide (b ≤ φ z))).length) z)
  | [], _, g, hg, _ => by simpa using hg 0 le_rfl
  | b :: m', hm, g, hg, hj => by
    rw [List.pairwise_cons] at hm
    have ih := continuous_glue_of_eq_at_breakpoints φ hφ m' hm.2 (fun k ↦ g (k + 1))
      (fun k hk ↦ hg (k + 1) (by simp; omega))
      (fun k hk z hz ↦ hj (k + 1) (by simp; omega) z (by simpa using hz))
    have hnil : ∀ z, φ z ≤ b → m'.filter (fun c ↦ decide (c ≤ φ z)) = [] := by
      intro z hz
      rw [List.filter_eq_nil_iff]
      intro c hc
      have := hm.1 c hc
      simp only [decide_eq_true_eq, not_le]
      linarith
    have e : (fun z ↦ g (((b :: m').filter (fun c ↦ decide (c ≤ φ z))).length) z) =
        fun z ↦ if b ≤ φ z then g ((m'.filter (fun c ↦ decide (c ≤ φ z))).length + 1) z else
            g 0 z := by
      funext z
      by_cases h : b ≤ φ z
      · simp [h]
      · simp [h, hnil z (le_of_lt (not_le.1 h))]
    rw [e]
    refine Continuous.if_le ih (hg 0 (Nat.zero_le _)) continuous_const hφ ?_
    intro z hz
    simp only [hnil z hz.symm.le, List.length_nil, zero_add]
    exact (hj 0 (by simp) z (by simpa using hz.symm)).symm

/-- Let `X` be a topological space, `F : (X × ℝ) × ℝ → ℝ` continuous and `ι : ℤ × ℤ`. Then
`x ↦ (1 / (2 * π)) * ∫ τ in 0..1, ∫ φ in 0..2 * π, exp (-((2 * π * ι.1 * τ + ι.2 * φ) * I)) * F ((x,
τ), φ)` is a continuous function from `X` to `ℂ`. The proof applies the continuity of parametric
interval integrals twice, first for the integral in `φ` and then for the integral in `τ`. -/
theorem continuous_integral_integral_exp_mul {X : Type*} [TopologicalSpace X] (ι : ℤ × ℤ)
    (F : (X × ℝ) × ℝ → ℝ)
    (hF : Continuous F) :
    Continuous (fun x ↦ (1 / (2 * Real.pi) : ℂ) * ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
      Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I)) *
          ((F ((x, τ), φ) : ℝ) : ℂ)) := by
  have hlin : Continuous (fun p : (X × ℝ) × ℝ ↦ 2 * Real.pi * (ι.1 : ℝ) * p.1.2 + (ι.2 : ℝ) *
      p.2) := by
    fun_prop
  have hg : Continuous (fun p : (X × ℝ) × ℝ ↦
      Complex.exp (-(((2 * Real.pi * ι.1 * p.1.2 + ι.2 * p.2 : ℝ) : ℂ) * Complex.I)) *
          ((F p : ℝ) : ℂ)) :=
    (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp hlin).mul
        continuous_const).neg).mul
      (Complex.continuous_ofReal.comp hF)
  have h1 : Continuous (fun q : X × ℝ ↦ ∫ φ in (0 : ℝ)..(2 * Real.pi),
      Complex.exp (-(((2 * Real.pi * ι.1 * q.2 + ι.2 * φ : ℝ) : ℂ) * Complex.I)) *
          ((F (q, φ) : ℝ) : ℂ)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
      (f := fun q φ ↦ Complex.exp (-(((2 * Real.pi * ι.1 * q.2 + ι.2 * φ : ℝ) : ℂ) * Complex.I))
        * ((F (q, φ) : ℝ) : ℂ)) hg 0 (2 * Real.pi)
  have h2 := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
    (f := fun x τ ↦ ∫ φ in (0 : ℝ)..(2 * Real.pi),
      Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I)) *
          ((F ((x, τ), φ) : ℝ) : ℂ))
    h1 0 1
  exact continuous_const.mul h2

/-- For a decidable proposition `P`, which does not depend on the point, and a continuous
`f : ℝ × ℝ → ℂ`, the function `p ↦ if P then f p else 0` is continuous. -/
theorem continuous_ite_const {P : Prop} [Decidable P] {f : ℝ × ℝ → ℂ} (hf : Continuous f) :
    Continuous fun p ↦ if P then f p else 0 := by
  by_cases hP : P
  · simp only [ite_eq_left hP]; exact hf
  · simp only [ite_eq_right hP]; exact continuous_const

/-- If `g : ℝ × ℝ → ℝ` is continuous, then the complex-valued function `p ↦ (g p : ℂ)` is
continuous. -/
theorem continuous_ofReal_comp {g : ℝ × ℝ → ℝ} (hg : Continuous g) : Continuous
    (fun p ↦ ((g p : ℝ) : ℂ)) :=
  Complex.continuous_ofReal.comp hg

/-- For a real polynomial `q`, the map `p ↦ (q.eval p.2 : ℂ)` is continuous on `ℝ × ℝ`. -/
theorem continuous_ofReal_eval_snd (q : Polynomial ℝ) : Continuous
    (fun p : ℝ × ℝ ↦ ((q.eval p.2 : ℝ) : ℂ)) :=
  Complex.continuous_ofReal.comp (q.continuous.comp continuous_snd)

/-- If `F : ℝ → ℝ → ℝ` is jointly continuous, that is, `p ↦ F p.1 p.2` is continuous on `ℝ × ℝ`,
then for every `r` the slice `z ↦ F r z` is continuous. -/
theorem continuous_of_continuous_uncurry_left {F : ℝ → ℝ → ℝ}
    (hF : Continuous fun p : ℝ × ℝ ↦ F p.1 p.2) (r : ℝ) :
    Continuous fun z ↦ F r z :=
  hF.comp (continuous_const.prodMk continuous_id)

/-- If `F : ℝ → ℂ` is integrable on `Icc a b`, then
`fun u : C(ℝ, ℝ) ↦ ∫ z in Icc a b, F z * (u z : ℂ)` is continuous on `C(ℝ, ℝ)` with the
compact-open topology. The proof uses dominated convergence: functions near `u0` are bounded on
`Icc a b` by `C + 1`, where `C` bounds `u0` there. -/
theorem continuous_setIntegral_Icc_mul_continuousMap {F : ℝ → ℂ} {a b : ℝ}
    (hF : IntegrableOn F (Icc a b)) :
    Continuous (fun u : C(ℝ, ℝ) ↦ ∫ z in Icc a b, F z * (u z : ℂ)) := by
  refine continuous_iff_continuousAt.2 fun u0 ↦ ?_
  have hloc : TendstoLocallyUniformly (fun (u : C(ℝ, ℝ)) (z : ℝ) ↦ u z) u0 (𝓝 u0) :=
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.1 tendsto_id
  have hunif := (tendstoLocallyUniformly_iff_forall_isCompact.1 hloc) _
      (isCompact_Icc (a := a) (b := b))
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
      u0.continuous.continuousOn
  have hev : ∀ᶠ u in 𝓝 u0, ∀ z ∈ Icc a b, dist (u0 z) (u z) < 1 :=
    Metric.tendstoUniformlyOn_iff.1 hunif 1 one_pos
  refine tendsto_integral_filter_of_dominated_convergence (fun z ↦ ‖F z‖ * (C + 1)) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun u ↦
      hF.1.mul (Complex.continuous_ofReal.comp u.continuous).aestronglyMeasurable
  · filter_upwards [hev] with u hu
    refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun z hz ↦ ?_)
    rw [norm_mul, Complex.norm_real]
    have h1 := hC z hz
    have h2 := hu z hz
    rw [Real.dist_eq] at h2
    gcongr
    rw [Real.norm_eq_abs] at h1 ⊢
    linarith [abs_sub_abs_le_abs_sub (u z) (u0 z), abs_sub_comm (u0 z) (u z)]
  · exact hF.norm.mul_const _
  · exact Eventually.of_forall fun z ↦ tendsto_const_nhds.mul
      ((Complex.continuous_ofReal.comp (continuous_eval_const z : Continuous fun u : C(ℝ, ℝ) ↦
          u z)).tendsto u0)

/-- Let `S` be a compact set of reals and `F : ℝ → ℂ` integrable on `S`. Then
`fun u : C(ℝ, ℝ) ↦ ∫ x in S, F x * (u x : ℂ)` is continuous on `C(ℝ, ℝ)` with the compact-open
topology. The proof uses dominated convergence: functions near `u0` are bounded on `S` by `C + 1`,
where `C` bounds `u0` on `S`. -/
theorem continuous_setIntegral_mul_continuousMap {F : ℝ → ℂ} {S : Set ℝ} (hS : IsCompact S)
    (hF : IntegrableOn F S) :
    Continuous (fun u : C(ℝ, ℝ) ↦ ∫ x in S, F x * ((u x : ℝ) : ℂ)) := by
  refine continuous_iff_continuousAt.2 fun u0 ↦ ?_
  have hunif : TendstoUniformlyOn (fun (u : C(ℝ, ℝ)) (x : ℝ) ↦ u x) u0 (𝓝 u0) S :=
    (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.1 tendsto_id) S hS
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn u0.continuous.continuousOn
  have hnear : ∀ᶠ u in 𝓝 u0, ∀ x ∈ S, dist (u0 x) (u x) < 1 :=
    Metric.tendstoUniformlyOn_iff.1 hunif 1 one_pos
  refine tendsto_integral_filter_of_dominated_convergence (fun x ↦ ‖F x‖ * (C + 1)) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun u ↦
      hF.1.mul (Complex.continuous_ofReal.comp u.continuous).aestronglyMeasurable
  · filter_upwards [hnear] with u hu
    refine (ae_restrict_iff' hS.measurableSet).2 (Eventually.of_forall fun x hx ↦ ?_)
    rw [norm_mul, Complex.norm_real]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have h1 := hC x hx
    have h2 := hu x hx
    rw [Real.dist_eq] at h2
    rw [Real.norm_eq_abs] at h1 ⊢
    have h3 : |u x| ≤ |u0 x| + |u0 x - u x| := by
      calc |u x| = |u0 x - (u0 x - u x)| := by ring_nf
        _ ≤ |u0 x| + |u0 x - u x| := abs_sub _ _
    linarith
  · exact hF.norm.mul_const _
  · exact Eventually.of_forall fun x ↦ tendsto_const_nhds.mul
      ((Complex.continuous_ofReal.comp
        (continuous_eval_const x : Continuous fun u : C(ℝ, ℝ) ↦ u x)).tendsto u0)

/-- The function `U ↦ ∑ j, ‖U j‖ ^ 2` on `Fin 12 → ℂ` is continuous. -/
theorem continuous_sum_norm_sq : Continuous (fun U : Fin 12 → ℂ ↦ ∑ j, ‖U j‖ ^ 2) := by
  fun_prop

/-- The map from `ℝ × ℝ` to `Fin 2 → ℂ` that sends `p` to the vector `![(p.1 : ℂ), (p.2 : ℂ)]` is
continuous. -/
theorem continuous_vec_ofReal_fst_snd : Continuous
    (fun p : ℝ × ℝ ↦ (![(p.1 : ℂ), (p.2 : ℂ)] : Fin 2 → ℂ)) := by
  refine continuous_pi fun i ↦ ?_
  fin_cases i
  · exact Complex.continuous_ofReal.comp continuous_fst
  · exact Complex.continuous_ofReal.comp continuous_snd

/-- A Lipschitz-type bound for two points whose norms are far apart. For `g : E → F` between normed
additive commutative groups and `δ > 0`, if `‖x‖ < δ / 2`, `δ < ‖y‖`, `‖g x‖ ≤ M` and `‖g y‖ ≤ M`,
then `dist (g x) (g y) ≤ 4 * M / δ * dist x y`. The proof uses `dist (g x) (g y) ≤ 2 * M` and
`δ / 2 ≤ dist x y`. -/
theorem dist_le_mul_dist_of_far {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {g : E → F} {δ M : ℝ} (hδ : 0 < δ) {x y : E} (hx : ‖x‖ < δ / 2) (hy : δ < ‖y‖)
    (hgx : ‖g x‖ ≤ M) (hgy : ‖g y‖ ≤ M) :
    dist (g x) (g y) ≤ 4 * M / δ * dist x y := by
  have hM : 0 ≤ M := le_trans (norm_nonneg _) hgx
  have hxy : δ / 2 ≤ dist x y := by
    rw [dist_eq_norm]
    have := norm_sub_norm_le y x
    rw [norm_sub_rev] at this
    linarith
  have h1 : dist (g x) (g y) ≤ 2 * M := by
    rw [dist_eq_norm]
    calc ‖g x - g y‖ ≤ ‖g x‖ + ‖g y‖ := norm_sub_le _ _
      _ ≤ 2 * M := by linarith
  calc dist (g x) (g y) ≤ 2 * M := h1
    _ = 4 * M / δ * (δ / 2) := by field_simp; ring
    _ ≤ 4 * M / δ * dist x y := by
      apply mul_le_mul_of_nonneg_left hxy
      positivity

/-- Let `a ≤ b` be points of a set `S` of real numbers that contains a point strictly between `u`
and `v` whenever `a ≤ u`, `u < v` and `v ≤ b`, and let `0 ≤ C` and `0 < δ`. If `H : ℝ → ℝ` satisfies
`|H q - H p| ≤ C * (q - p) ^ 2` for all `p` and `q` in `S` with `a ≤ p`, `p ≤ q`, `q ≤ b` and
`q - p ≤ δ`, then `H b = H a`. The proof joins `a` to `b` by `N` steps through points of `S` with
gaps at most `3 / 2 * ((b - a) / N)`, which gives
`|H b - H a| ≤ C * (3 / 2 * ((b - a) / N)) * (b - a)`, and lets `N` tend to infinity. -/
theorem eq_endpoints_of_abs_sub_le_sq {S : Set ℝ} {a b : ℝ} (hab : a ≤ b) (ha : a ∈ S) (hb : b ∈ S)
    (hS : ∀ u v, a ≤ u → u < v → v ≤ b → ∃ z ∈ S, u < z ∧ z < v) (H : ℝ → ℝ) {C δ : ℝ}
    (hC : 0 ≤ C) (hδ : 0 < δ)
    (hH : ∀ p ∈ S, ∀ q ∈ S, a ≤ p → p ≤ q → q ≤ b → q - p ≤ δ → |H q - H p| ≤ C * (q - p) ^ 2) :
    H b = H a := by
  rcases hab.eq_or_lt with h | hlt
  · rw [h]
  have key : ∀ N : ℕ, 0 < N → 3 * (b - a) ≤ 2 * δ * N → |H b - H a| ≤ C * (3 / 2 * ((b - a) / N)) *
      (b - a) := by
    intro N hN hNδ
    have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
    set h := (b - a) / N with hh
    have hpos : 0 < h := div_pos (sub_pos.2 hlt) hNr
    have hbN : a + N * h = b := by rw [hh]; field_simp; ring
    have hex : ∀ k : ℕ, ∃ z : ℝ, 1 ≤ k → k ≤ N → z ∈ S ∧ a + k * h - h / 2 < z ∧ z < a + k * h := by
      intro k
      by_cases hk : 1 ≤ k ∧ k ≤ N
      · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk.1
        have hkN : (k : ℝ) ≤ N := by exact_mod_cast hk.2
        obtain ⟨z, hz, h1, h2⟩ := hS (a + k * h - h / 2) (a + k * h) (by nlinarith) (by linarith)
          (by rw [← hbN]; nlinarith)
        exact ⟨z, fun _ _ ↦ ⟨hz, h1, h2⟩⟩
      · exact ⟨0, fun h1 h2 ↦ absurd ⟨h1, h2⟩ hk⟩
    choose z hz using hex
    set p : ℕ → ℝ := fun k ↦ if k = 0 then a else if k = N then b else z k with hp
    have hprop : ∀ k, k ≤ N → p k ∈ S ∧ a + k * h - h / 2 ≤ p k ∧ p k ≤ a + k * h ∧ a ≤ p k ∧ p k ≤
        b := by
      intro k hk
      by_cases h0 : k = 0
      · subst h0
        simp only [hp, ite_true, Nat.cast_zero, zero_mul, add_zero]
        exact ⟨ha, by linarith, le_rfl, le_rfl, hab⟩
      by_cases hN' : k = N
      · subst hN'
        simp only [hp, h0, ite_false, ite_true]
        exact ⟨hb, by linarith, by linarith, hab, le_rfl⟩
      have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 h0
      have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      have hkN : (k : ℝ) ≤ N := by exact_mod_cast hk
      obtain ⟨hzS, hz1, hz2⟩ := hz k hk1 hk
      simp only [hp, h0, hN', ite_false]
      refine ⟨hzS, hz1.le, hz2.le, by nlinarith, ?_⟩
      rw [← hbN]; nlinarith
    have hstep : ∀ k, k < N → |H (p (k + 1)) - H (p k)| ≤ C * (3 / 2 * h) * (p (k + 1) - p k) := by
      intro k hk
      obtain ⟨s1, l1, u1, a1, b1⟩ := hprop k hk.le
      obtain ⟨s2, l2, u2, a2, b2⟩ := hprop (k + 1) hk
      push_cast at l2 u2
      have hle : p k ≤ p (k + 1) := by linarith
      have hgap : p (k + 1) - p k ≤ 3 / 2 * h := by linarith
      refine (hH _ s1 _ s2 a1 hle b2 (hgap.trans ?_)).trans ?_
      · have e : (N : ℝ) * h = b - a := by linarith
        have h3 : 3 * h * N ≤ 2 * δ * N := by nlinarith
        have := le_of_mul_le_mul_right h3 hNr
        linarith
      · rw [sq]
        have h0 : 0 ≤ p (k + 1) - p k := by linarith
        calc C * ((p (k + 1) - p k) * (p (k + 1) - p k)) = C * (p (k + 1) - p k) *
                 (p (k + 1) - p k) := by ring
          _ ≤ C * (3 / 2 * h) * (p (k + 1) - p k) := by
              apply mul_le_mul_of_nonneg_right _ h0
              exact mul_le_mul_of_nonneg_left hgap hC
    have htel : H b - H a = ∑ k ∈ Finset.range N, (H (p (k + 1)) - H (p k)) := by
      rw [Finset.sum_range_sub (fun k ↦ H (p k))]
      have e0 : p 0 = a := by simp [hp]
      have eN : p N = b := by simp [hp, hN.ne']
      rw [e0, eN]
    have htel2 : ∑ k ∈ Finset.range N, (p (k + 1) - p k) = b - a := by
      rw [Finset.sum_range_sub p]
      have e0 : p 0 = a := by simp [hp]
      have eN : p N = b := by simp [hp, hN.ne']
      rw [e0, eN]
    rw [htel]
    calc |∑ k ∈ Finset.range N, (H (p (k + 1)) - H (p k))| ≤ ∑ k ∈ Finset.range N, |H (p (k + 1)) -
             H (p k)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range N, C * (3 / 2 * h) * (p (k + 1) - p k) :=
          Finset.sum_le_sum fun k hk ↦ hstep k (Finset.mem_range.1 hk)
      _ = C * (3 / 2 * h) * (b - a) := by rw [← Finset.mul_sum, htel2]
  by_contra hne
  have hd : 0 < |H b - H a| := abs_pos.2 (sub_ne_zero.2 hne)
  obtain ⟨N, hN⟩ := exists_nat_gt (max (3 * (b - a) / (2 * δ))
      ((C * (3 / 2) * (b - a) ^ 2) / |H b - H a|))
  have hN1 : (3 * (b - a) / (2 * δ)) < N := (le_max_left _ _).trans_lt hN
  have hN2 : (C * (3 / 2) * (b - a) ^ 2) / |H b - H a| < N := (le_max_right _ _).trans_lt hN
  have hN0 : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hN1
  have hk := key N (Nat.cast_pos.1 hN0) (by rw [div_lt_iff₀ (by positivity)] at hN1; linarith)
  rw [div_lt_iff₀ hd] at hN2
  have e : C * (3 / 2 * ((b - a) / N)) * (b - a) = C * (3 / 2) * (b - a) ^ 2 / N := by
    field_simp
  rw [e, le_div_iff₀ hN0] at hk
  linarith

/-- For every `Q : MvPolynomial (Fin 2) ℂ` there are real constants `0 ≤ K` and `0 ≤ B` such that,
for all `v w : Fin 2 → ℂ` with `‖v i‖ ≤ 1` and `‖w i‖ ≤ 1` for all `i`,
`‖MvPolynomial.eval v Q‖ ≤ B` and
`‖MvPolynomial.eval v Q - MvPolynomial.eval w Q‖ ≤ K * (‖v 0 - w 0‖ + ‖v 1 - w 1‖)`. The proof is by
induction on `Q`: constants, sums, and multiplication by a variable. -/
theorem exists_bound_lipschitz_mvPolynomial_eval (Q : MvPolynomial (Fin 2) ℂ) :
    ∃ K B : ℝ, 0 ≤ K ∧
      0 ≤ B ∧ ∀ v w : Fin 2 → ℂ, (∀ i, ‖v i‖ ≤ 1) → (∀ i, ‖w i‖ ≤ 1) → ‖MvPolynomial.eval v Q‖ ≤ B ∧
      ‖MvPolynomial.eval v Q - MvPolynomial.eval w Q‖ ≤ K * (‖v 0 - w 0‖ + ‖v 1 - w 1‖) := by
  induction Q using MvPolynomial.induction_on with
  | C a => exact ⟨0, ‖a‖, le_rfl, norm_nonneg _, fun v w _ _ ↦ ⟨by simp, by simp⟩⟩
  | add p q hp hq =>
    obtain ⟨K1, B1, hK1, hB1, h1⟩ := hp
    obtain ⟨K2, B2, hK2, hB2, h2⟩ := hq
    refine ⟨K1 + K2, B1 + B2, by positivity, by positivity, fun v w hv hw ↦ ?_⟩
    obtain ⟨a1, b1⟩ := h1 v w hv hw
    obtain ⟨a2, b2⟩ := h2 v w hv hw
    simp only [map_add]
    constructor
    · exact (norm_add_le _ _).trans (add_le_add a1 a2)
    · calc _ = ‖(MvPolynomial.eval v p - MvPolynomial.eval w p) +
            (MvPolynomial.eval v q - MvPolynomial.eval w q)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
        _ ≤ _ := add_le_add b1 b2
        _ = _ := by ring
  | mul_X p n hp =>
    obtain ⟨K, B, hK, hB, h⟩ := hp
    refine ⟨K + B, B, by positivity, hB, fun v w hv hw ↦ ?_⟩
    obtain ⟨a, b⟩ := h v w hv hw
    have aw := (h w w hw hw).1
    simp only [map_mul, MvPolynomial.eval_X]
    have hd : ‖v n - w n‖ ≤ ‖v 0 - w 0‖ + ‖v 1 - w 1‖ := by
      fin_cases n
      · exact le_add_of_nonneg_right (norm_nonneg _)
      · exact le_add_of_nonneg_left (norm_nonneg _)
    have hD : 0 ≤ ‖v 0 - w 0‖ + ‖v 1 - w 1‖ := by positivity
    constructor
    · rw [norm_mul]
      calc _ ≤ B * 1 := mul_le_mul a (hv n) (norm_nonneg _) hB
        _ = B := mul_one B
    · calc ‖MvPolynomial.eval v p * v n - MvPolynomial.eval w p * w n‖
          = ‖(MvPolynomial.eval v p - MvPolynomial.eval w p) * v n + MvPolynomial.eval w p *
              (v n - w n)‖ := by
            ring_nf
        _ ≤ ‖MvPolynomial.eval v p - MvPolynomial.eval w p‖ * ‖v n‖ +
            ‖MvPolynomial.eval w p‖ * ‖v n - w n‖ := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_mul, norm_mul]
        _ ≤ (K * (‖v 0 - w 0‖ + ‖v 1 - w 1‖)) * 1 + B * (‖v 0 - w 0‖ + ‖v 1 - w 1‖) := by
            gcongr
            · exact hv n
        _ = (K + B) * (‖v 0 - w 0‖ + ‖v 1 - w 1‖) := by ring

/-- Let `Y` be a complete normed additive group, `A ≥ 0` and `q ≥ 0` reals with `8 * q * A ≤ 1`, and
`Φ : Y → Y` a map with `‖Φ z‖ ≤ A + q * ‖z‖ ^ 2` and `‖Φ z - Φ z'‖ ≤ q * (‖z‖ + ‖z'‖) * ‖z - z'‖`
for all `z`, `z'`. Then `Φ` has a fixed point `z` with `‖z‖ ≤ 2 * A`. The proof shows that `Φ` maps
the closed ball of radius `2 * A` around `0` into itself and is a contraction with constant `1 / 2`
there, and applies the Banach fixed point theorem. -/
theorem exists_fixedPoint_norm_le_two_mul {Y : Type*} [NormedAddCommGroup Y] [CompleteSpace Y]
    (Φ : Y → Y) (A q : ℝ)
    (hA : 0 ≤ A) (hq : 0 ≤ q) (hqA : 8 * q * A ≤ 1)
    (hb : ∀ z, ‖Φ z‖ ≤ A + q * ‖z‖ ^ 2)
    (hl : ∀ z z', ‖Φ z - Φ z'‖ ≤ q * (‖z‖ + ‖z'‖) * ‖z - z'‖) :
    ∃ z, Φ z = z ∧ ‖z‖ ≤ 2 * A := by
  have hmaps : ∀ z ∈ Metric.closedBall (0 : Y) (2 * A), Φ z ∈ Metric.closedBall (0 : Y) (2 * A) :=
      by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz ⊢
    exact le_two_mul_of_le_add_sq hA hq hqA (norm_nonneg _) hz (hb z)
  have : CompleteSpace (Metric.closedBall (0 : Y) (2 * A)) :=
    (Metric.isClosed_closedBall).completeSpace_coe
  have : Nonempty (Metric.closedBall (0 : Y) (2 * A)) :=
    ⟨⟨0, by rw [Metric.mem_closedBall, dist_self]; linarith⟩⟩
  let Ψ : Metric.closedBall (0 : Y) (2 * A) → Metric.closedBall (0 : Y) (2 * A) :=
    fun z ↦ ⟨Φ z, hmaps z z.2⟩
  have hc : ContractingWith (1 / 2 : NNReal) Ψ := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun z z' ↦ ?_⟩
    change dist (Φ z) (Φ z') ≤ ((1 / 2 : NNReal) : ℝ) * dist (z : Y) z'
    have hz := z.2
    have hz' := z'.2
    rw [Metric.mem_closedBall, dist_zero_right] at hz hz'
    rw [dist_eq_norm, dist_eq_norm]
    have h1 : q * (‖(z : Y)‖ + ‖(z' : Y)‖) ≤ 1 / 2 := by
      nlinarith [mul_le_mul_of_nonneg_left (add_le_add hz hz') hq]
    calc ‖Φ z - Φ z'‖ ≤ q * (‖(z : Y)‖ + ‖(z' : Y)‖) * ‖(z : Y) - z'‖ := hl _ _
      _ ≤ 1 / 2 * ‖(z : Y) - z'‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = ((1 / 2 : NNReal) : ℝ) * ‖(z : Y) - z'‖ := by norm_num
  have hfix : Ψ (ContractingWith.fixedPoint Ψ hc) = ContractingWith.fixedPoint Ψ hc :=
    hc.fixedPoint_isFixedPt
  refine ⟨(ContractingWith.fixedPoint Ψ hc).1, congrArg Subtype.val hfix, ?_⟩
  have h := (ContractingWith.fixedPoint Ψ hc).2
  rwa [Metric.mem_closedBall, dist_zero_right] at h

/-- Let `E`, `F`, `G` be real normed spaces, `H` a normed additive commutative group, and let
`Φ : F → G → H` satisfy `‖Φ x y - Φ x' y'‖ ≤ ‖x‖ * ‖y - y'‖ + ‖x - x'‖ * ‖y'‖` for all arguments. If
`a : E → F` and `b : E → G` are Lipschitz on a set `s` (`LipschitzOnWith La a s` and
`LipschitzOnWith Lb b s`) with `‖a q‖ ≤ A` and `‖b q‖ ≤ B` for `q ∈ s`, then
`fun q ↦ Φ (a q) (b q)` is Lipschitz on `s` with some constant `K : NNReal`. The proof takes
`K = Real.toNNReal (A * Lb + La * B)`. -/
theorem exists_lipschitzOnWith_of_bilinear_bound {E : Type*} {F : Type*} {G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {s : Set E} {a : E → F} {b : E → G} {H : Type*}
    [NormedAddCommGroup H] (Φ : F → G → H)
    (hΦ : ∀ x x' y y', ‖Φ x y - Φ x' y'‖ ≤ ‖x‖ * ‖y - y'‖ + ‖x - x'‖ * ‖y'‖) {A B : ℝ}
        {La Lb : NNReal}
    (hA : ∀ q ∈ s, ‖a q‖ ≤ A) (hB : ∀ q ∈ s, ‖b q‖ ≤ B) (ha : LipschitzOnWith La a s)
    (hb : LipschitzOnWith Lb b s) : ∃ K : NNReal, LipschitzOnWith K (fun q ↦ Φ (a q) (b q)) s := by
  refine ⟨Real.toNNReal (A * Lb + La * B), LipschitzOnWith.of_dist_le_mul fun q hq w hw ↦ ?_⟩
  have h1 := hb.dist_le_mul q hq w hw
  have h2 := ha.dist_le_mul q hq w hw
  rw [dist_eq_norm] at h1 h2 ⊢
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA q hq)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB w hw)
  have hd : 0 ≤ dist q w := dist_nonneg
  calc ‖Φ (a q) (b q) - Φ (a w) (b w)‖ ≤ ‖a q‖ * ‖b q - b w‖ + ‖a q - a w‖ * ‖b w‖ := hΦ _ _ _ _
    _ ≤ A * (Lb * dist q w) + (La * dist q w) * B :=
        add_le_add (mul_le_mul (hA q hq) h1 (norm_nonneg _) hA0)
            (mul_le_mul h2 (hB w hw) (norm_nonneg _)
          (by positivity))
    _ = (A * Lb + La * B) * dist q w := by ring
    _ ≤ (Real.toNNReal (A * Lb + La * B) : ℝ) * dist q w :=
        mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) hd

/-- A `C^1` map `f : E → F` between real normed spaces is Lipschitz on every compact convex set `s`:
there is `L : ℝ≥0` with `LipschitzOnWith L f s`. The norm of `fderiv ℝ f` is continuous, hence
bounded on `s`, and a bound on the derivative on a convex set gives a Lipschitz constant. -/
theorem exists_lipschitzOnWith_of_contDiff_isCompact {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (hf : ContDiff ℝ 1 f) {s : Set E}
    (hs : IsCompact s) (hc : Convex ℝ s) : ∃ L : ℝ≥0, LipschitzOnWith L f s := by
  obtain ⟨M, hM⟩ := hs.exists_bound_of_continuousOn
    ((hf.continuous_fderiv one_ne_zero).norm.continuousOn)
  refine ⟨Real.toNNReal M, hc.lipschitzOnWith_of_nnNorm_fderiv_le
    (fun x _ ↦ hf.differentiable one_ne_zero x) (fun x hx ↦ ?_)⟩
  have h := hM x hx
  rw [norm_norm] at h
  rw [← NNReal.coe_le_coe, coe_nnNorm]
  exact h.trans (Real.le_coe_toNNReal M)

/-- If `f g : ℝ × ℝ → ℂ` are Lipschitz with constants `Kf`, `Kg` and satisfy `‖f x‖ ≤ Mf` and
`‖g x‖ ≤ Mg` for all `x`, then the pointwise product `fun x ↦ f x * g x` is Lipschitz with some
constant. The proof writes `f x * g x - f y * g y = f x * (g x - g y) + g y * (f x - f y)` and
obtains the constant `Mf * Kg + Mg * Kf`. -/
theorem exists_lipschitzWith_mul_of_bounded {f g : ℝ × ℝ → ℂ} {Kf Kg : NNReal} {Mf Mg : ℝ}
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hMf : ∀ x, ‖f x‖ ≤ Mf) (hMg : ∀ x, ‖g x‖ ≤ Mg) :
    ∃ K : NNReal, LipschitzWith K (fun x ↦ f x * g x) := by
  have hMf0 : 0 ≤ Mf := (norm_nonneg _).trans (hMf 0)
  have hMg0 : 0 ≤ Mg := (norm_nonneg _).trans (hMg 0)
  refine ⟨⟨Mf * Kg + Mg * Kf, by positivity⟩, LipschitzWith.of_dist_le_mul fun x y ↦ ?_⟩
  simp only [dist_eq_norm]
  have e : f x * g x - f y * g y = f x * (g x - g y) + g y * (f x - f y) := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have h1 := hf.dist_le_mul x y
  have h2 := hg.dist_le_mul x y
  simp only [dist_eq_norm] at h1 h2
  calc ‖f x‖ * ‖g x - g y‖ + ‖g y‖ * ‖f x - f y‖ ≤ Mf * (Kg * ‖x - y‖) + Mg * (Kf * ‖x - y‖) :=
        add_le_add (mul_le_mul (hMf x) h2 (norm_nonneg _) hMf0)
            (mul_le_mul (hMg y) h1 (norm_nonneg _) hMg0)
    _ = (Mf * Kg + Mg * Kf) * ‖x - y‖ := by ring

/-- Let `φ : Fin N → ℝ × ℝ → ℝ` be functions that are all Lipschitz with the same constant `K`, let
`c : Fin N → ℂ` and let `s` be a finite set of indices. Then
`fun p ↦ ∑ i ∈ s, conj (c i) * (φ i p : ℂ)` is Lipschitz with some constant `K'`. The proof is by
induction on `s`, adding one Lipschitz term at a time. -/
theorem exists_lipschitzWith_sum_conj_mul_ofReal {N : ℕ} (φ : Fin N → ℝ × ℝ → ℝ) {K : NNReal}
    (hφ : ∀ i, LipschitzWith K (φ i))
    (c : Fin N → ℂ) (s : Finset (Fin N)) :
    ∃ K' : NNReal, LipschitzWith K' (fun p ↦ ∑ i ∈ s, (starRingEnd ℂ) (c i) * (φ i p : ℂ)) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp [LipschitzWith.const (0 : ℂ)]⟩
  | insert a s ha ih =>
    obtain ⟨K1, h1⟩ := ih
    have h2 : LipschitzWith (‖(starRingEnd ℂ) (c a)‖₊ * (1 * K))
        (fun p ↦ (starRingEnd ℂ) (c a) • ((φ a p : ℝ) : ℂ)) :=
      (lipschitzWith_smul ((starRingEnd ℂ) (c a))).comp
        (Complex.isometry_ofReal.lipschitzWith.comp (hφ a))
    have e : (fun p ↦ ∑ i ∈ insert a s, (starRingEnd ℂ) (c i) * (φ i p : ℂ)) =
        fun p ↦ (starRingEnd ℂ) (c a) • ((φ a p : ℝ) : ℂ) + ∑ i ∈ s,
            (starRingEnd ℂ) (c i) * (φ i p : ℂ) := by
      funext p
      simp only [Finset.sum_insert ha, smul_eq_mul]
    rw [e]
    exact ⟨_, h2.add h1⟩

/-- Let `K` be a compact Hausdorff space, `E` a real normed space, `f : C(K, E)`, `S` a dense subset
of `E` and `ε > 0`. Then there are a natural `m`, continuous functions `ρ l : C(K, ℝ)` with values
in `[0, 1]` and vectors `x l ∈ S`, for `l : Fin m`, such that `‖∑ l, ρ l t • x l - f t‖ ≤ ε` for
every `t`. The proof covers `K` by finitely many open sets on which `f` stays within `ε / 2` of one
of its values, takes a partition of unity subordinate to this cover, and picks each `x l` in `S`
within `ε / 2` of the corresponding value. -/
theorem exists_sum_smul_sub_le_of_dense {K E : Type*} [TopologicalSpace K] [CompactSpace K]
    [T2Space K]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : C(K, E)) {S : Set E} (hS : Dense S)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (m : ℕ) (ρ : Fin m → C(K, ℝ)) (x : Fin m → E), (∀ l, x l ∈ S) ∧
      (∀ l t, 0 ≤ ρ l t ∧ ρ l t ≤ 1) ∧ ∀ t, ‖∑ l, ρ l t • x l - f t‖ ≤ ε := by
  have hε2 : 0 < ε / 2 := half_pos hε
  let U : K → Set K := fun s ↦ f ⁻¹' Metric.ball (f s) (ε / 2)
  have hUo : ∀ s, IsOpen (U s) := fun s ↦ Metric.isOpen_ball.preimage f.continuous
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover U hUo
    (fun t _ ↦ mem_iUnion.2 ⟨t, by simp [U, Metric.mem_ball, hε2]⟩)
  let e := T.equivFin
  let pts : Fin T.card → K := fun l ↦ (e.symm l).1
  have hcov : (univ : Set K) ⊆ ⋃ l, U (pts l) := by
    intro t ht
    obtain ⟨s, hs, hts⟩ := mem_iUnion₂.1 (hT ht)
    exact mem_iUnion.2 ⟨e ⟨s, hs⟩, by simpa [pts] using hts⟩
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ (fun l ↦ U (pts l))
    (fun l ↦ hUo _) hcov
  have hx : ∀ l, ∃ y, y ∈ S ∧ dist (f (pts l)) y < ε / 2 := by
    intro l
    obtain ⟨y, hy1, hy2⟩ := Metric.dense_iff.1 hS (f (pts l)) (ε / 2) hε2
    exact ⟨y, hy2, by rw [dist_comm]; exact hy1⟩
  choose x hxS hxd using hx
  refine ⟨T.card, fun l ↦ ρ l, x, hxS, fun l t ↦ ⟨ρ.nonneg l t, ρ.le_one l t⟩, fun t ↦ ?_⟩
  have h1 : ∑ l, ρ l t = 1 := by
    rw [← finsum_eq_sum_of_fintype]
    exact ρ.sum_eq_one (mem_univ t)
  have h2 : ∑ l, ρ l t • x l - f t = ∑ l, ρ l t • (x l - f t) := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, h1, one_smul]
  rw [h2]
  calc ‖∑ l, ρ l t • (x l - f t)‖ ≤ ∑ l, ‖ρ l t • (x l - f t)‖ := norm_sum_le _ _
    _ ≤ ∑ l, ρ l t * ε := by
        refine Finset.sum_le_sum fun l _ ↦ ?_
        rw [norm_smul, Real.norm_of_nonneg (ρ.nonneg l t)]
        by_cases h0 : ρ l t = 0
        · simp [h0]
        · refine mul_le_mul_of_nonneg_left ?_ (ρ.nonneg l t)
          have hts : t ∈ U (pts l) := hρ l (subset_tsupport _ (Function.mem_support.2 h0))
          have h3 : dist (f t) (f (pts l)) < ε / 2 := hts
          have h4 := hxd l
          rw [← dist_eq_norm]
          linarith [dist_triangle (x l) (f (pts l)) (f t), dist_comm (x l) (f (pts l)),
            dist_comm (f t) (f (pts l))]
    _ = ε := by rw [← Finset.sum_mul, h1, one_mul]

/-- Let `A` and `B` be `K`-Lipschitz on a convex set `U` of `ℝ × ℝ`, with values in a real normed
space, and let `π` be a continuous linear functional with `B p = A p` whenever `π p = c`. Then
`fun q ↦ if c ≤ π q then B q else A q` is `K`-Lipschitz on `U`. For two points on opposite sides,
the segment between them lies in `U` and meets the level set `π = c` at a point where `A` and `B`
agree, and the triangle inequality through that point gives the bound. -/
theorem lipschitzOnWith_ite_of_convex_of_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A B : ℝ × ℝ → E}
    (π : ℝ × ℝ →L[ℝ] ℝ) (c : ℝ) {U : Set (ℝ × ℝ)} (hU : Convex ℝ U) {K : NNReal}
    (hA : LipschitzOnWith K A U) (hB : LipschitzOnWith K B U) (h : ∀ p, c = π p → B p = A p) :
    LipschitzOnWith K (fun q ↦ if c ≤ π q then B q else A q) U := by
  have key : ∀ p ∈ U, ∀ q ∈ U, π p < c → c ≤ π q → dist (A p) (B q) ≤ K * dist p q := by
    intro p hp q hq h1 h2
    have hpos : 0 < π q - π p := by linarith
    set s : ℝ := (c - π p) / (π q - π p) with hs
    have s0 : 0 ≤ s := div_nonneg (by linarith) hpos.le
    have s1 : s ≤ 1 := (div_le_one hpos).2 (by linarith)
    set r := AffineMap.lineMap p q s with hr
    have hrU : r ∈ U := hU.lineMap_mem hp hq ⟨s0, s1⟩
    have hπr : c = π r := by
      rw [hr, AffineMap.lineMap_apply_module', map_add, map_smul, map_sub, smul_eq_mul, hs]
      field_simp
      ring
    have e := h r hπr
    calc dist (A p) (B q) ≤ dist (A p) (A r) + dist (A r) (B q) := dist_triangle _ _ _
      _ = dist (A p) (A r) + dist (B r) (B q) := by rw [e]
      _ ≤ K * dist p r + K * dist r q := add_le_add (hA.dist_le_mul p hp r hrU)
          (hB.dist_le_mul r hrU q hq)
      _ = K * dist p q := by
        rw [dist_comm p r, hr, dist_lineMap_left, dist_lineMap_right, Real.norm_eq_abs,
            Real.norm_eq_abs,
          abs_of_nonneg s0, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - s)]
        ring
  refine LipschitzOnWith.of_dist_le_mul fun p hp q hq ↦ ?_
  by_cases h1 : c ≤ π p <;> by_cases h2 : c ≤ π q <;> simp only [h1, h2, ite_true, ite_false]
  · exact hB.dist_le_mul p hp q hq
  · rw [dist_comm, dist_comm p q]
    exact key q hq p hp (not_le.1 h2) h1
  · exact key p hp q hq (not_le.1 h1) h2
  · exact hA.dist_le_mul p hp q hq

/-- Gluing of Lipschitz bounds on a convex set: let `s` be a convex set in a real normed space with
`s ⊆ A ∪ B`, where `A` and `B` are closed. If `g` is `K`-Lipschitz on `A` and on `B`, with values in
a pseudometric space, then `g` is `K`-Lipschitz on `s`. For `x ∈ A` and `y ∈ B` in `s`, the proof
finds a point of `A ∩ B` on the segment from `x` to `y`, which is connected, and adds the two
bounds. -/
theorem lipschitzOnWith_of_closed_cover_of_convex {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [PseudoMetricSpace F] {g : E → F} {s A B : Set E} {K : NNReal}
    (hs : Convex ℝ s) (hA : IsClosed A) (hB : IsClosed B) (hcover : s ⊆ A ∪ B)
    (hgA : LipschitzOnWith K g A) (hgB : LipschitzOnWith K g B) : LipschitzOnWith K g s := by
  have key : ∀ x ∈ s, ∀ y ∈ s, x ∈ A → y ∈ B → dist (g x) (g y) ≤ K * dist x y := by
    intro x hx y hy hxA hyB
    have hseg : segment ℝ x y ⊆ s := hs.segment_subset hx hy
    obtain ⟨z, hz, hzA, hzB⟩ := (isPreconnected_closed_iff.mp (convex_segment x y).isPreconnected)
        A B hA hB
      (hseg.trans hcover) ⟨x, left_mem_segment ℝ x y, hxA⟩ ⟨y, right_mem_segment ℝ x y, hyB⟩
    calc dist (g x) (g y) ≤ dist (g x) (g z) + dist (g z) (g y) := dist_triangle _ _ _
      _ ≤ K * dist x z + K * dist z y := add_le_add (hgA.dist_le_mul x hxA z hzA)
          (hgB.dist_le_mul z hzB y hyB)
      _ = K * dist x y := by rw [← mul_add, dist_add_dist_of_mem_segment hz]
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_
  rcases hcover hx with hxA | hxB <;> rcases hcover hy with hyA | hyB
  · exact hgA.dist_le_mul x hxA y hyA
  · exact key x hx y hy hxA hyB
  · rw [dist_comm (g x), dist_comm x]
    exact key y hy x hx hyA hxB
  · exact hgB.dist_le_mul x hxB y hyB

/-- For real `b` and `d`, the map `x ↦ (b - x) / d` on the real line is Lipschitz with constant
`|1 / d|`. -/
theorem lipschitzWith_const_sub_div (b d : ℝ) : LipschitzWith (Real.toNNReal |1 / d|)
    (fun x : ℝ ↦ (b - x) / d) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  rw [Real.coe_toNNReal _ (abs_nonneg _), Real.dist_eq, Real.dist_eq,
    show (b - x) / d - (b - y) / d = 1 / d * (y - x) by ring, abs_mul, abs_sub_comm y x]

/-- Let `g : E → G` be a continuous map between real normed spaces that is differentiable at every
`z ≠ 0` with `‖fderiv ℝ g z‖ ≤ K` there. Then `g` is `K`-Lipschitz on the whole space. The mean
value inequality along the ray from `u` to `0` gives `dist (g u) (g 0) ≤ K * dist u 0`, and two
points are compared through `0` when `0` lies on their segment and along the segment otherwise. -/
theorem lipschitzWith_of_fderiv_le_of_ne_zero {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {g : E → G} {K : NNReal} (hc : Continuous g)
    (hd : ∀ z, z ≠ 0 → DifferentiableAt ℝ g z) (hb : ∀ z, z ≠ 0 → ‖fderiv ℝ g z‖ ≤ K) :
        LipschitzWith K g := by
  have hrad : ∀ u : E, dist (g u) (g 0) ≤ K * dist u 0 := by
    intro u
    rw [dist_eq_norm, dist_eq_norm, sub_zero]
    by_cases hu : u = 0
    · simp [hu]
    have hφ : ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt (fun s : ℝ ↦ g ((1 - s) • u))
        (fderiv ℝ g ((1 - t) • u) ((-1 : ℝ) • u)) (Ici t) t := by
      intro t ht
      have hne : (1 - t) • u ≠ 0 := smul_ne_zero (by linarith [ht.2]) hu
      have h1 : HasDerivAt (fun s : ℝ ↦ (1 - s) • u) ((-1 : ℝ) • u) t :=
        ((hasDerivAt_id' t).const_sub 1).smul_const u
      exact ((hd _ hne).hasFDerivAt.comp_hasDerivAt t h1).hasDerivWithinAt
    have hcont : ContinuousOn (fun s : ℝ ↦ g ((1 - s) • u)) (Icc 0 1) :=
      (hc.comp ((continuous_const.sub continuous_id).smul continuous_const)).continuousOn
    have hbound : ∀ t ∈ Ico (0 : ℝ) 1, ‖fderiv ℝ g ((1 - t) • u) ((-1 : ℝ) • u)‖ ≤ K * ‖u‖ := by
      intro t ht
      have hne : (1 - t) • u ≠ 0 := smul_ne_zero (by linarith [ht.2]) hu
      calc ‖fderiv ℝ g ((1 - t) • u) ((-1 : ℝ) • u)‖ ≤ ‖fderiv ℝ g ((1 - t) • u)‖ * ‖(-1 : ℝ) •
               u‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ K * ‖u‖ := by
            rw [neg_one_smul, norm_neg]
            exact mul_le_mul_of_nonneg_right (hb _ hne) (norm_nonneg _)
    have := norm_image_sub_le_of_norm_deriv_right_le_segment hcont hφ hbound 1 ⟨zero_le_one, le_rfl⟩
    simp only [sub_self, zero_smul, sub_zero, one_smul, mul_one] at this
    rw [norm_sub_rev]
    exact this
  refine LipschitzWith.of_dist_le_mul fun u v ↦ ?_
  by_cases h0 : (0 : E) ∈ segment ℝ u v
  · have hs := dist_add_dist_of_mem_segment h0
    calc dist (g u) (g v) ≤ dist (g u) (g 0) + dist (g 0) (g v) := dist_triangle _ _ _
      _ ≤ K * dist u 0 + K * dist 0 v := by
          rw [dist_comm (g 0), dist_comm (0 : E)]
          exact add_le_add (hrad u) (hrad v)
      _ = K * dist u v := by rw [← mul_add, hs]
  · have hs : ∀ x ∈ segment ℝ u v, x ≠ 0 := fun x hx h ↦ h0 (by rw [← h]; exact hx)
    have := (convex_segment u v).norm_image_sub_le_of_norm_fderiv_le (fun x hx ↦ hd x (hs x hx))
      (fun x hx ↦ hb x (hs x hx)) (left_mem_segment ℝ u v) (right_mem_segment ℝ u v)
    rw [dist_eq_norm, dist_eq_norm, norm_sub_rev, norm_sub_rev u]
    exact this

/-- For real `a` and `d`, the map `x ↦ (x - a) / d` on the real line is Lipschitz with constant
`|1 / d|`. -/
theorem lipschitzWith_sub_const_div (a d : ℝ) : LipschitzWith (Real.toNNReal |1 / d|)
    (fun x : ℝ ↦ (x - a) / d) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  rw [Real.coe_toNNReal _ (abs_nonneg _), Real.dist_eq, Real.dist_eq,
    show (x - a) / d - (y - a) / d = 1 / d * (x - y) by ring, abs_mul]

/-- If `u : E → F` and `v : E → G` are locally Lipschitz on a set `s` and `B : F →L[ℝ] G →L[ℝ] H` is
a continuous bilinear map between real normed spaces, then `fun y ↦ B (u y) (v y)` is locally
Lipschitz on `s`. Near a point `x` of `s` both `u` and `v` are bounded, and the identity
`B (u a) (v a) - B (u b) (v b) = B (u a - u b) (v a) + B (u b) (v a - v b)` gives the Lipschitz
bound. -/
theorem locallyLipschitzOn_bilin_apply {E : Type*} {F : Type*} {G : Type*} {H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (B : F →L[ℝ] G →L[ℝ] H) {s : Set E} {u : E → F} {v : E → G}
    (hu : LocallyLipschitzOn s u) (hv : LocallyLipschitzOn s v) :
    LocallyLipschitzOn s (fun y ↦ B (u y) (v y)) := by
  intro x hx
  obtain ⟨Ku, tu, htu, hKu⟩ := hu hx
  obtain ⟨Kv, tv, htv, hKv⟩ := hv hx
  have ht : tu ∩ tv ∩ Metric.ball x 1 ∈ 𝓝[s] x :=
    inter_mem (inter_mem htu htv) (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x one_pos))
  have hxu : x ∈ tu := mem_of_mem_nhdsWithin hx htu
  have hxv : x ∈ tv := mem_of_mem_nhdsWithin hx htv
  have bu : ∀ y ∈ tu ∩ tv ∩ Metric.ball x 1, ‖u y‖ ≤ ‖u x‖ + Ku := by
    intro y hy
    have h1 := hKu.dist_le_mul y hy.1.1 x hxu
    have h2 : dist y x < 1 := hy.2
    have h3 : ‖u y‖ - ‖u x‖ ≤ dist (u y) (u x) := by rw [dist_eq_norm]; exact norm_sub_norm_le _ _
    have h4 : (Ku : ℝ) * dist y x ≤ Ku := by
      have := Ku.2
      nlinarith [dist_nonneg (x := y) (y := x)]
    linarith
  have bv : ∀ y ∈ tu ∩ tv ∩ Metric.ball x 1, ‖v y‖ ≤ ‖v x‖ + Kv := by
    intro y hy
    have h1 := hKv.dist_le_mul y hy.1.2 x hxv
    have h2 : dist y x < 1 := hy.2
    have h3 : ‖v y‖ - ‖v x‖ ≤ dist (v y) (v x) := by rw [dist_eq_norm]; exact norm_sub_norm_le _ _
    have h4 : (Kv : ℝ) * dist y x ≤ Kv := by
      have := Kv.2
      nlinarith [dist_nonneg (x := y) (y := x)]
    linarith
  refine ⟨‖B‖₊ * (Ku * (‖v x‖₊ + Kv) + (‖u x‖₊ + Ku) * Kv), _, ht, ?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro a ha b hb
  have e : B (u a) (v a) - B (u b) (v b) = B (u a - u b) (v a) + B (u b) (v a - v b) := by
    simp only [map_sub, sub_apply]
    abel
  have hua : ‖u a - u b‖ ≤ Ku * dist a b := by
    rw [← dist_eq_norm]; exact hKu.dist_le_mul a ha.1.1 b hb.1.1
  have hva : ‖v a - v b‖ ≤ Kv * dist a b := by
    rw [← dist_eq_norm]; exact hKv.dist_le_mul a ha.1.2 b hb.1.2
  have h1 : ‖B‖ * ‖u a - u b‖ * ‖v a‖ ≤ ‖B‖ * (Ku * dist a b) * (‖v x‖ + Kv) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hua (norm_nonneg B)) (bv a ha) (norm_nonneg _)
      (by positivity)
  have h2 : ‖B‖ * ‖u b‖ * ‖v a - v b‖ ≤ ‖B‖ * (‖u x‖ + Ku) * (Kv * dist a b) :=
    mul_le_mul (mul_le_mul_of_nonneg_left (bu b hb) (norm_nonneg B)) hva (norm_nonneg _) (by
      positivity)
  rw [dist_eq_norm (B (u a) (v a)), e]
  calc ‖B (u a - u b) (v a) + B (u b) (v a - v b)‖
      ≤ ‖B (u a - u b) (v a)‖ + ‖B (u b) (v a - v b)‖ := norm_add_le _ _
    _ ≤ ‖B‖ * ‖u a - u b‖ * ‖v a‖ + ‖B‖ * ‖u b‖ * ‖v a - v b‖ :=
        add_le_add (B.le_opNorm₂ _ _) (B.le_opNorm₂ _ _)
    _ ≤ ‖B‖ * (Ku * dist a b) * (‖v x‖ + Kv) + ‖B‖ * (‖u x‖ + Ku) * (Kv * dist a b) :=
        add_le_add h1 h2
    _ = ((‖B‖₊ * (Ku * (‖v x‖₊ + Kv) + (‖u x‖₊ + Ku) * Kv) : NNReal) : ℝ) * dist a b := by
        push_cast
        ring

/-- For maps between real normed spaces, if `φ` is Lipschitz with constant `K` and `u` is locally
Lipschitz on a set `s`, then `fun y ↦ φ (u y)` is locally Lipschitz on `s`. -/
theorem locallyLipschitzOn_comp_of_lipschitzWith {E : Type*} {F : Type*} {G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {s : Set E} {u : E → F} {φ : F → G} {K : NNReal}
    (hφ : LipschitzWith K φ)
    (hu : LocallyLipschitzOn s u) : LocallyLipschitzOn s (fun y ↦ φ (u y)) := by
  intro x hx
  obtain ⟨Ku, t, ht, hK⟩ := hu hx
  exact ⟨K * Ku, t, ht, hφ.comp_lipschitzOnWith hK⟩

/-- Composition of locally Lipschitz maps between real normed spaces: if `g` is locally Lipschitz on
`t`, `c` is locally Lipschitz on `s` and `c` maps `s` into `t`, then `fun y ↦ g (c y)` is locally
Lipschitz on `s`. The proof uses the continuity of `c` on `s` to find, near each point of `s`, a
neighbourhood within `s` on which `c` is Lipschitz and which `c` maps into a set where `g` is
Lipschitz. -/
theorem locallyLipschitzOn_comp_of_mapsTo {E : Type*} {F : Type*} {G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] {s : Set E} {t : Set F} {g : F → G} {c : E → F} (hg : LocallyLipschitzOn t g)
    (hc : LocallyLipschitzOn s c) (hst : MapsTo c s t) : LocallyLipschitzOn s (fun y ↦ g (c y)) :=
        by
  intro x hx
  obtain ⟨Kg, u, hu, hKg⟩ := hg (hst hx)
  obtain ⟨Kc, w, hw, hKc⟩ := hc hx
  have hT : Tendsto c (𝓝[s] x) (𝓝[t] (c x)) :=
    tendsto_nhdsWithin_iff.2 ⟨hc.continuousOn x hx, eventually_nhdsWithin_of_forall fun y hy ↦
        hst hy⟩
  refine ⟨Kg * Kc, w ∩ (s ∩ c ⁻¹' u), inter_mem hw (inter_mem self_mem_nhdsWithin (hT hu)), ?_⟩
  exact hKg.comp (hKc.mono inter_subset_left) (fun y hy ↦ hy.2.2)

/-- For maps `u v : E → F` between real normed spaces, if `u` is locally Lipschitz on a set `s` and
`u y = v y` for all `y ∈ s`, then `v` is locally Lipschitz on `s`. -/
theorem locallyLipschitzOn_congr {E : Type*} {F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {s : Set E} {u v : E → F} (hu : LocallyLipschitzOn s u)
    (h : ∀ y ∈ s, u y = v y) : LocallyLipschitzOn s v := by
  intro x hx
  obtain ⟨K, t, ht, hK⟩ := hu hx
  refine ⟨K, t ∩ s, inter_mem ht self_mem_nhdsWithin, ?_⟩
  intro a ha b hb
  rw [← h a ha.2, ← h b hb.2]
  exact hK ha.1 hb.1

/-- A map `f : E → F` between real normed spaces that is `C^1` on an open set `s` is locally
Lipschitz on `s`: `LocallyLipschitzOn s f`. -/
theorem locallyLipschitzOn_of_contDiffOn_of_isOpen {E : Type*} {F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {s : Set E} (hs : IsOpen s)
    {f : E → F} (hf : ContDiffOn ℝ 1 f s) :
    LocallyLipschitzOn s f := by
  intro x hx
  obtain ⟨K, t, ht, hK⟩ := (hf.contDiffAt (hs.mem_nhds hx)).exists_lipschitzOnWith
  exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, hK⟩

/-- Let `g : E → F` be a continuous map from a proper real normed space into a normed group. If `g`
is Lipschitz on every compact set that does not contain `0`, and on some closed ball
`Metric.closedBall 0 δ` with `δ > 0`, then for every real `R` it is Lipschitz on
`Metric.closedBall 0 R`. The proof takes the largest of the constant on `closedBall 0 δ`, the
constant on the compact set `closedBall 0 R \ ball 0 (δ / 2)`, and `4 * M / δ`, where `M` bounds
`‖g‖` on `closedBall 0 R`; the last constant serves for pairs with `‖x‖ < δ / 2` and `δ < ‖y‖`. -/
theorem exists_lipschitzOnWith_closedBall_of_off_zero {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [ProperSpace E] [NormedAddCommGroup F] {g : E → F} (hcont : Continuous g)
    (hK : ∀ K : Set E, IsCompact K → K ⊆ {0}ᶜ → ∃ L : NNReal, LipschitzOnWith L g K)
    (hball : ∃ δ > 0, ∃ L : NNReal, LipschitzOnWith L g (Metric.closedBall 0 δ)) (R : ℝ) :
    ∃ L : NNReal, LipschitzOnWith L g (Metric.closedBall 0 R) := by
  obtain ⟨δ, hδ, L₁, hL₁⟩ := hball
  obtain ⟨L₂, hL₂⟩ := hK (Metric.closedBall 0 R \ Metric.ball 0 (δ / 2))
    ((isCompact_closedBall 0 R).diff Metric.isOpen_ball) (by
      intro y hy hy0
      apply hy.2
      rw [Set.mem_singleton_iff.1 hy0]
      exact Metric.mem_ball_self (by linarith))
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn hcont.continuousOn
  set M := max C 0 with hMdef
  have hCM : ∀ x ∈ Metric.closedBall (0 : E) R, ‖g x‖ ≤ M :=
      fun x hx ↦ le_trans (hC x hx) (le_max_left _ _)
  refine ⟨_, LipschitzOnWith.of_dist_le' (K := max (L₁ : ℝ) (max (L₂ : ℝ) (4 * M / δ))) ?_⟩
  intro x hx y hy
  have hd := dist_nonneg (x := x) (y := y)
  have hA : ∀ u : E, u ∈ Metric.closedBall (0 : E) δ ↔ ‖u‖ ≤ δ := fun u ↦ by
    rw [Metric.mem_closedBall, dist_zero_right]
  have hB : ∀ u : E, u ∈ Metric.closedBall (0 : E) R \ Metric.ball 0 (δ / 2) ↔
      u ∈ Metric.closedBall (0 : E) R ∧ δ / 2 ≤ ‖u‖ := fun u ↦ by
    rw [Set.mem_sdiff, Metric.mem_ball, dist_zero_right, not_lt]
  have c1 : ‖x‖ ≤ δ → ‖y‖ ≤ δ → dist (g x) (g y) ≤ max (L₁ : ℝ) (max (L₂ : ℝ) (4 * M / δ)) *
      dist x y :=
    fun h1 h2 ↦ le_trans (hL₁.dist_le_mul x ((hA x).2 h1) y ((hA y).2 h2))
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hd)
  have c2 : δ / 2 ≤ ‖x‖ → δ / 2 ≤ ‖y‖ →
      dist (g x) (g y) ≤ max (L₁ : ℝ) (max (L₂ : ℝ) (4 * M / δ)) * dist x y :=
    fun h1 h2 ↦ le_trans (hL₂.dist_le_mul x ((hB x).2 ⟨hx, h1⟩) y ((hB y).2 ⟨hy, h2⟩))
      (mul_le_mul_of_nonneg_right (le_trans (le_max_left _ _) (le_max_right _ _)) hd)
  have c3 : ‖x‖ < δ / 2 → δ < ‖y‖ →
      dist (g x) (g y) ≤ max (L₁ : ℝ) (max (L₂ : ℝ) (4 * M / δ)) * dist x y :=
    fun h1 h2 ↦ le_trans (dist_le_mul_dist_of_far hδ h1 h2 (hCM x hx) (hCM y hy))
      (mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) (le_max_right _ _)) hd)
  have c4 : ‖y‖ < δ / 2 → δ < ‖x‖ →
      dist (g x) (g y) ≤ max (L₁ : ℝ) (max (L₂ : ℝ) (4 * M / δ)) * dist x y := by
    intro h1 h2
    rw [dist_comm (g x), dist_comm x]
    exact le_trans (dist_le_mul_dist_of_far hδ h1 h2 (hCM y hy) (hCM x hx))
      (mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) (le_max_right _ _)) dist_nonneg)
  by_cases h1 : ‖x‖ ≤ δ <;> by_cases h2 : ‖y‖ ≤ δ
  · exact c1 h1 h2
  · by_cases h3 : δ / 2 ≤ ‖x‖
    · exact c2 h3 (by linarith)
    · exact c3 (by linarith) (by linarith)
  · by_cases h3 : δ / 2 ≤ ‖y‖
    · exact c2 (by linarith) h3
    · exact c4 (by linarith) (by linarith)
  · exact c2 (by linarith) (by linarith)

/-- For every `Q : MvPolynomial (Fin 2) ℂ` there is a real `0 ≤ K` such that, for all real `t`,
`t'`, `x`, `x'` of absolute value at most `1`,
`|(MvPolynomial.eval ![(t : ℂ), (x : ℂ)] Q).re - (MvPolynomial.eval ![(t' : ℂ), (x' : ℂ)] Q).re| ≤
K * (|t - t'| + |x - x'|)`. -/
theorem exists_lipschitz_re_mvPolynomial_eval (Q : MvPolynomial (Fin 2) ℂ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ t t' x x' : ℝ, |t| ≤ 1 → |t'| ≤ 1 → |x| ≤ 1 → |x'| ≤
      1 → |(MvPolynomial.eval ![(t : ℂ), (x : ℂ)] Q).re -
      (MvPolynomial.eval ![(t' : ℂ), (x' : ℂ)] Q).re| ≤ K * (|t - t'| + |x - x'|) := by
  obtain ⟨K, B, hK, _, h⟩ := exists_bound_lipschitz_mvPolynomial_eval Q
  refine ⟨K, hK, fun t t' x x' ht ht' hx hx' ↦ ?_⟩
  have hd := (h _ _ (norm_pair_ofReal_apply_le_one ht hx) (norm_pair_ofReal_apply_le_one ht' hx')).2
  rw [norm_pair_ofReal_sub_add_eq_abs] at hd
  rw [← Complex.sub_re]
  exact (Complex.abs_re_le_norm _).trans hd

/-- For every real `g`, the function `τ ↦ (1 - Real.exp (-τ)) ^ (-g)` is continuous on `Ioi 0`. -/
theorem continuousOn_one_sub_exp_neg_rpow (g : ℝ) : ContinuousOn
    (fun τ : ℝ ↦ (1 - Real.exp (-τ)) ^ (-g)) (Ioi 0) := by
  refine ContinuousOn.rpow_const (by fun_prop) fun τ hτ ↦ Or.inl (one_sub_exp_neg_pos hτ).ne'

/-- For reals `g`, `s`, `b` and `y` with `0 ≤ y`, the function
`τ ↦ Real.exp (-(g * s * τ)) * (1 - Real.exp (-τ)) ^ (-g) * (1 + Real.exp (-(g * τ)) * y) ^
(-b)` is continuous on `Ioi 0`. -/
theorem continuousOn_exp_mul_rpow_mul_rpow_Ioi (g s b y : ℝ) (hy : 0 ≤ y) : ContinuousOn
    (fun τ : ℝ ↦ Real.exp (-(g * s * τ)) *
    (1 - Real.exp (-τ)) ^ (-g) * (1 + Real.exp (-(g * τ)) * y) ^ (-b)) (Ioi 0) := by
  refine ((by fun_prop : Continuous fun τ : ℝ ↦ Real.exp (-(g * s * τ))).continuousOn.mul
    (continuousOn_one_sub_exp_neg_rpow g)).mul ?_
  refine ContinuousOn.rpow_const (by fun_prop) fun τ _ ↦ Or.inl ?_
  have := Real.exp_pos (-(g * τ)); positivity

/-- For every index `i`, the map `x ↦ EuclideanSpace.single i x` from `ℝ` to `ℝ³`, which puts `x` in
coordinate `i` and zero elsewhere, is continuous. It equals `x ↦ x • EuclideanSpace.single i 1`. -/
theorem continuous_euclideanSpace_single (i : Fin 3) :
    Continuous (fun x : ℝ ↦ (EuclideanSpace.single i x : EuclideanSpace ℝ (Fin 3))) := by
  have e : (fun x : ℝ ↦ (EuclideanSpace.single i x : EuclideanSpace ℝ (Fin 3))) =
      fun x ↦ x • (EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin 3)) := by
    funext x
    ext j
    simp
  rw [e]
  exact continuous_id.smul continuous_const

/-- Let `B : E →L[ℝ] F →L[ℝ] G` be a continuous bilinear map of real normed spaces and let
`f : X → E`, `h : X → F` be locally Lipschitz on a pseudometric space `X`. Then
`x ↦ B (f x) (h x)` is locally Lipschitz. On a small ball `f`, `h` are Lipschitz and bounded,
and `B (f a) (h a) - B (f b) (h b) = B (f a - f b) (h a) + B (f b) (h a - h b)`. -/
theorem locallyLipschitz_bilin_apply {X E F G : Type*} [PseudoMetricSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E →L[ℝ] F →L[ℝ] G) {f : X → E} {h : X → F} (hf : LocallyLipschitz f)
        (hh : LocallyLipschitz h) :
    LocallyLipschitz (fun x ↦ B (f x) (h x)) := by
  intro x
  obtain ⟨K1, t1, ht1, hf1⟩ := hf x
  obtain ⟨K2, t2, ht2, hh2⟩ := hh x
  obtain ⟨r, hr, hrt⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem ht1 ht2)
  have hf' : LipschitzOnWith K1 f (Metric.ball x r) := hf1.mono fun z hz ↦ (hrt hz).1
  have hh' : LipschitzOnWith K2 h (Metric.ball x r) := hh2.mono fun z hz ↦ (hrt hz).2
  have hx : x ∈ Metric.ball x r := Metric.mem_ball_self hr
  set M1 : ℝ := ‖f x‖ + K1 * r
  set M2 : ℝ := ‖h x‖ + K2 * r
  have hb1 : ∀ z ∈ Metric.ball x r, ‖f z‖ ≤ M1 := by
    intro z hz
    have h1 := hf'.dist_le_mul z hz x hx
    have h2 : dist z x < r := hz
    have h3 : ‖f z‖ ≤ ‖f x‖ + dist (f z) (f x) := by
      rw [dist_eq_norm]
      have := norm_le_insert' (f z) (f x)
      linarith [norm_sub_rev (f z) (f x)]
    nlinarith [K1.2]
  have hb2 : ∀ z ∈ Metric.ball x r, ‖h z‖ ≤ M2 := by
    intro z hz
    have h1 := hh'.dist_le_mul z hz x hx
    have h2 : dist z x < r := hz
    have h3 : ‖h z‖ ≤ ‖h x‖ + dist (h z) (h x) := by
      rw [dist_eq_norm]
      have := norm_le_insert' (h z) (h x)
      linarith [norm_sub_rev (h z) (h x)]
    nlinarith [K2.2]
  have hStrain : 0 ≤ M1 := le_trans (norm_nonneg _) (hb1 x hx)
  have hM2 : 0 ≤ M2 := le_trans (norm_nonneg _) (hb2 x hx)
  refine ⟨Real.toNNReal (‖B‖ * (K1 * M2 + M1 * K2)), Metric.ball x r, Metric.ball_mem_nhds x hr, ?_⟩
  refine LipschitzOnWith.of_dist_le_mul fun a ha b hb ↦ ?_
  rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm]
  have hsplit : B (f a) (h a) - B (f b) (h b) = B (f a - f b) (h a) + B (f b) (h a - h b) := by
    simp only [map_sub, sub_apply]
    abel
  rw [hsplit]
  have e1 : ‖B (f a - f b) (h a)‖ ≤ ‖B‖ * ‖f a - f b‖ * ‖h a‖ := B.le_opNorm₂ _ _
  have e2 : ‖B (f b) (h a - h b)‖ ≤ ‖B‖ * ‖f b‖ * ‖h a - h b‖ := B.le_opNorm₂ _ _
  have d1 : ‖f a - f b‖ ≤ K1 * dist a b := by rw [← dist_eq_norm]; exact hf'.dist_le_mul a ha b hb
  have d2 : ‖h a - h b‖ ≤ K2 * dist a b := by rw [← dist_eq_norm]; exact hh'.dist_le_mul a ha b hb
  have n1 := hb2 a ha
  have n2 := hb1 b hb
  have hB := norm_nonneg B
  calc ‖B (f a - f b) (h a) + B (f b) (h a - h b)‖ ≤ ‖B (f a - f b) (h a)‖ +
           ‖B (f b) (h a - h b)‖ :=
        norm_add_le _ _
    _ ≤ ‖B‖ * (K1 * dist a b) * M2 + ‖B‖ * M1 * (K2 * dist a b) := by
        gcongr
        · exact e1.trans (by gcongr)
        · exact e2.trans (by gcongr)
    _ = ‖B‖ * (K1 * M2 + M1 * K2) * dist a b := by ring

/-- For every polynomial `p` in two variables with complex coefficients there is `B ≥ 0` with
`‖MvPolynomial.eval ![t, u] p‖ ≤ B` for all real `t`, `u` such that `|t| ≤ 1` and `|u| ≤ 1`.
By induction on `p`: constants, sums, and products with a variable of modulus at most one. -/
theorem exists_norm_mvPolynomial_eval_le (p : MvPolynomial (Fin 2) ℂ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ t u : ℝ, |t| ≤ 1 → |u| ≤ 1 → ‖MvPolynomial.eval ![(t : ℂ), (u : ℂ)] p‖ ≤ B := by
  induction p using MvPolynomial.induction_on with
  | C a => exact ⟨‖a‖, norm_nonneg _, fun t u _ _ ↦ by simp⟩
  | add p q hp hq =>
    obtain ⟨B1, h1, hB1⟩ := hp
    obtain ⟨B2, h2, hB2⟩ := hq
    refine ⟨B1 + B2, by positivity, fun t u ht hu ↦ ?_⟩
    rw [map_add]
    exact (norm_add_le _ _).trans (add_le_add (hB1 t u ht hu) (hB2 t u ht hu))
  | mul_X p n hp =>
    obtain ⟨B, h0, hB⟩ := hp
    refine ⟨B, h0, fun t u ht hu ↦ ?_⟩
    rw [map_mul, norm_mul, MvPolynomial.eval_X]
    have hn : ‖(![(t : ℂ), (u : ℂ)] : Fin 2 → ℂ) n‖ ≤ 1 := by
      fin_cases n <;> simpa [Complex.norm_real, Real.norm_eq_abs]
    calc ‖MvPolynomial.eval ![(t : ℂ), (u : ℂ)] p‖ * ‖(![(t : ℂ), (u : ℂ)] : Fin 2 → ℂ) n‖ ≤ B *
             1 :=
          mul_le_mul (hB t u ht hu) hn (norm_nonneg _) h0
      _ = B := mul_one B

end PDE.Analysis
