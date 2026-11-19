/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Operators
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import PDE.Analysis.Integration.CompactByParts
import PDE.FDeriv.Calculus
import PDE.Analysis.Calculus.SmoothTransitionGlobalBounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Divergence integrals over the open quadrant

On the open quadrant `Q = {y | 0 < y₀, 0 < y₁}` of the plane, a vector field `Φ` that is `C¹`
on `Q` has `∫_Q div Φ = 0` as soon as `div Φ` is integrable on `Q` and each component satisfies
`|Φⱼ(y)| ≤ yⱼ m(y)` on `Q` for one function `m` integrable on `Q`. The single bound removes the
boundary terms on the two axes, at the corner and at infinity: the proof multiplies `Φ` by the
plateau cutoffs `ζ_N(y) = c_N(y₀) c_N(y₁)` with `c_N = 1` on `[2/N, N]` and `c_N = 0` off
`(1/N, 2N)`, for which `|∂ⱼζ_N(y)| yⱼ` is bounded and supported where `yⱼ ≤ 2/N` or `yⱼ ≥ N`.

## Main results

* `integral_quadrant_divergence_eq_zero`: `∫_Q (∂₀Φ₀ + ∂₁Φ₁) = 0`.
* `integral_quadrant_mul_advectiveDerivative_eq_neg`: the transport form
  `∫_Q h (V·∇g) = -∫_Q g div(h V)`.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open MeasureTheory Set Filter
open scoped Topology

/-! ### The one-dimensional plateau -/

/-- The plateau `c_N(t) = s(N t - 1) (1 - s(t / N - 1))`, `s` the smooth transition: it is `0`
for `t ≤ 1/N` and for `t ≥ 2N`, and `1` on `[2/N, N]`. -/
private def plateau (N t : ℝ) : ℝ :=
  Real.smoothTransition (N * t - 1) * (1 - Real.smoothTransition (t / N - 1))

/-- The plateau is differentiable at every `t`, with
`c_N'(t) = N s'(N t - 1) (1 - s(t / N - 1)) - s(N t - 1) s'(t / N - 1) / N`. -/
private theorem hasDerivAt_plateau (N t : ℝ) :
    HasDerivAt (plateau N)
      (deriv Real.smoothTransition (N * t - 1) * N * (1 - Real.smoothTransition (t / N - 1)) +
        Real.smoothTransition (N * t - 1) *
          -(deriv Real.smoothTransition (t / N - 1) * (1 / N))) t := by
  have hd : ∀ u, HasDerivAt Real.smoothTransition (deriv Real.smoothTransition u) u :=
    fun u ↦ (Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero u |>.hasDerivAt
  have h1 : HasDerivAt (fun t ↦ Real.smoothTransition (N * t - 1))
      (deriv Real.smoothTransition (N * t - 1) * N) t := by
    have := (hd (N * t - 1)).comp t (((hasDerivAt_id t).const_mul N).sub_const 1)
    simpa [Function.comp_def] using this
  have h2 : HasDerivAt (fun t ↦ 1 - Real.smoothTransition (t / N - 1))
      (-(deriv Real.smoothTransition (t / N - 1) * (1 / N))) t := by
    have := (hd (t / N - 1)).comp t (((hasDerivAt_id t).div_const N).sub_const 1)
    simpa [Function.comp_def] using this.const_sub 1
  exact h1.mul h2

/-- The plateau `c_N` is `C¹`. -/
private theorem contDiff_plateau (N : ℝ) : ContDiff ℝ 1 (plateau N) := by
  unfold plateau
  have hs := Real.smoothTransition.contDiff (n := 1)
  exact (hs.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)).mul
    (contDiff_const.sub (hs.comp ((contDiff_id.div_const N).sub contDiff_const)))

/-- The plateau takes its values in `[0, 1]`. -/
private theorem plateau_mem_Icc (N t : ℝ) : plateau N t ∈ Icc (0 : ℝ) 1 := by
  unfold plateau
  have a := Real.smoothTransition.nonneg (N * t - 1)
  have b := Real.smoothTransition.le_one (N * t - 1)
  have c := Real.smoothTransition.nonneg (t / N - 1)
  have d := Real.smoothTransition.le_one (t / N - 1)
  constructor
  · exact mul_nonneg a (by linarith)
  · calc Real.smoothTransition (N * t - 1) * (1 - Real.smoothTransition (t / N - 1))
        ≤ 1 * 1 := by gcongr; linarith
      _ = 1 := by ring

/-- For `N > 0` the plateau vanishes on `t ≤ 1/N`. -/
private theorem plateau_eq_zero_of_le {N t : ℝ} (hN : 0 < N) (ht : t ≤ 1 / N) :
    plateau N t = 0 := by
  unfold plateau
  rw [Real.smoothTransition.zero_of_nonpos, zero_mul]
  rw [le_div_iff₀ hN] at ht
  linarith

/-- For `N > 0` the plateau vanishes on `t ≥ 2N`. -/
private theorem plateau_eq_zero_of_ge {N t : ℝ} (hN : 0 < N) (ht : 2 * N ≤ t) :
    plateau N t = 0 := by
  have h : Real.smoothTransition (t / N - 1) = 1 := by
    refine Real.smoothTransition.one_of_one_le ?_
    rw [le_sub_iff_add_le, le_div_iff₀ hN]
    linarith
  unfold plateau
  rw [h, sub_self, mul_zero]

/-- For `N > 0` the plateau equals `1` on `[2/N, N]`. -/
private theorem plateau_eq_one {N t : ℝ} (hN : 0 < N) (h1 : 2 / N ≤ t) (h2 : t ≤ N) :
    plateau N t = 1 := by
  unfold plateau
  rw [Real.smoothTransition.one_of_one_le, Real.smoothTransition.zero_of_nonpos]
  · ring
  · rw [sub_nonpos, div_le_one hN]; exact h2
  · rw [div_le_iff₀ hN] at h1
    linarith

/-- `|c_N'(t)| t ≤ 2 S (1_{t ≤ 2/N} + 1_{N ≤ t})` for `t > 0`, `N > 0`. -/
private theorem abs_deriv_plateau_mul_le {N t S : ℝ} (hN : 0 < N) (ht : 0 < t)
    (hS : ∀ u, |deriv Real.smoothTransition u| ≤ S) :
    |deriv (plateau N) t| * t ≤
      (if t ≤ 2 / N then 2 * S else 0) + (if N ≤ t then 2 * S else 0) := by
  have hS0 : 0 ≤ S := (abs_nonneg _).trans (hS 0)
  rw [(hasDerivAt_plateau N t).deriv]
  set a := deriv Real.smoothTransition (N * t - 1)
  set b := deriv Real.smoothTransition (t / N - 1)
  have hs1 := plateau_mem_Icc N t
  have e1 := Real.smoothTransition.nonneg (N * t - 1)
  have e2 := Real.smoothTransition.le_one (N * t - 1)
  have e3 := Real.smoothTransition.nonneg (t / N - 1)
  have e4 := Real.smoothTransition.le_one (t / N - 1)
  have hA : |a * N * (1 - Real.smoothTransition (t / N - 1))| * t ≤
      if t ≤ 2 / N then 2 * S else 0 := by
    split_ifs with h
    · rw [abs_mul, abs_mul, abs_of_pos hN,
        abs_of_nonneg (show (0 : ℝ) ≤ 1 - Real.smoothTransition (t / N - 1) by linarith)]
      have hNt : N * t ≤ 2 := by rw [le_div_iff₀ hN] at h; linarith
      calc |a| * N * (1 - Real.smoothTransition (t / N - 1)) * t
          ≤ S * N * 1 * t := by
            gcongr
            · exact hS _
            · linarith
        _ = S * (N * t) := by ring
        _ ≤ S * 2 := by gcongr
        _ = 2 * S := by ring
    · push Not at h
      have : 1 < N * t - 1 := by rw [div_lt_iff₀ hN] at h; linarith
      simp [a, deriv_smoothTransition_zero_of_one_le this.le]
  have hB : |Real.smoothTransition (N * t - 1) * -(b * (1 / N))| * t ≤
      if N ≤ t then 2 * S else 0 := by
    split_ifs with h
    · by_cases h2 : t ≤ 2 * N
      · rw [abs_mul, abs_neg, abs_mul, abs_of_nonneg e1, abs_of_pos (by positivity : 0 < 1 / N)]
        calc Real.smoothTransition (N * t - 1) * (|b| * (1 / N)) * t
            ≤ 1 * (S * (1 / N)) * t := by gcongr; exact hS _
          _ = S * (t / N) := by ring
          _ ≤ S * 2 := by gcongr; rw [div_le_iff₀ hN]; linarith
          _ = 2 * S := by ring
      · push Not at h2
        have : 1 < t / N - 1 := by rw [lt_sub_iff_add_lt, lt_div_iff₀ hN]; linarith
        simp only [b, deriv_smoothTransition_zero_of_one_le this.le, zero_mul, neg_zero, mul_zero,
          abs_zero]
        positivity
    · push Not at h
      have : t / N - 1 < 0 := by rw [sub_neg, div_lt_one hN]; exact h
      simp [b, deriv_smoothTransition_zero_of_nonpos this.le]
  calc |a * N * (1 - Real.smoothTransition (t / N - 1)) +
        Real.smoothTransition (N * t - 1) * -(b * (1 / N))| * t
      ≤ (|a * N * (1 - Real.smoothTransition (t / N - 1))| +
          |Real.smoothTransition (N * t - 1) * -(b * (1 / N))|) * t := by
        gcongr; exact abs_add_le _ _
    _ = |a * N * (1 - Real.smoothTransition (t / N - 1))| * t +
          |Real.smoothTransition (N * t - 1) * -(b * (1 / N))| * t := by ring
    _ ≤ _ := add_le_add hA hB

/-! ### The cutoffs of the quadrant -/

/-- The derivative of `y ↦ c_N(y_k)` on the plane is `c_N'(y_k)` times the `k`-th coordinate
projection. -/
private theorem hasFDerivAt_plateau_coord (N : ℝ) (k : Fin 2) (y : ℝ^2) :
    HasFDerivAt (fun y : ℝ^2 ↦ plateau N (y k))
      (deriv (plateau N) (y k) • (EuclideanSpace.proj k : ℝ^2 →L[ℝ] ℝ)) y := by
  have hc : HasFDerivAt (fun y : ℝ^2 ↦ y k) (EuclideanSpace.proj k : ℝ^2 →L[ℝ] ℝ) y :=
    (EuclideanSpace.proj k : ℝ^2 →L[ℝ] ℝ).hasFDerivAt
  exact ((contDiff_plateau N).differentiable one_ne_zero (y k)).hasDerivAt.comp_hasFDerivAt y hc

/-- `∂ⱼ` of `y ↦ c_N(y_k)` is `c_N'(y_k)` for `k = j` and `0` otherwise. -/
private theorem partialDeriv_plateau_coord (N : ℝ) (j k : Fin 2) (y : ℝ^2) :
    ∂[j] (fun y : ℝ^2 ↦ plateau N (y k)) y =
      deriv (plateau N) (y k) * if k = j then 1 else 0 := by
  unfold partialDeriv
  rw [(hasFDerivAt_plateau_coord N k y).fderiv]
  simp [EuclideanSpace.proj, eq_comm]

/-- The cutoff `ζ_N(y) = c_N(y₀) c_N(y₁)` of the quadrant is `C¹`. -/
private theorem contDiff_cutoff (N : ℝ) :
    ContDiff ℝ 1 (fun y : ℝ^2 ↦ plateau N (y 0) * plateau N (y 1)) :=
  ((contDiff_plateau N).comp (EuclideanSpace.proj (0 : Fin 2) : ℝ^2 →L[ℝ] ℝ).contDiff).mul
    ((contDiff_plateau N).comp (EuclideanSpace.proj (1 : Fin 2) : ℝ^2 →L[ℝ] ℝ).contDiff)

/-- `|∂ⱼζ_N(y)| ≤ |c_N'(yⱼ)|`, the other factor of `ζ_N` lying in `[0, 1]`. -/
private theorem abs_partialDeriv_cutoff_le (N : ℝ) (j : Fin 2) (y : ℝ^2) :
    |∂[j] (fun y : ℝ^2 ↦ plateau N (y 0) * plateau N (y 1)) y| ≤ |deriv (plateau N) (y j)| := by
  have hd : ∀ k : Fin 2, DifferentiableAt ℝ (fun y : ℝ^2 ↦ plateau N (y k)) y :=
    fun k ↦ (hasFDerivAt_plateau_coord N k y).differentiableAt
  rw [partialDeriv_mul (hd 0) (hd 1), partialDeriv_plateau_coord, partialDeriv_plateau_coord]
  have h0 := plateau_mem_Icc N (y 0)
  have h1 := plateau_mem_Icc N (y 1)
  fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, ite_true, mul_one, one_ne_zero, ite_false, mul_zero,
      add_zero]
    rw [abs_mul, abs_of_nonneg h1.1]
    exact mul_le_of_le_one_right (abs_nonneg _) h1.2
  · simp only [Fin.mk_one, Fin.isValue, zero_ne_one, ite_false, mul_zero, zero_mul, ite_true,
      mul_one, zero_add]
    rw [abs_mul, abs_of_nonneg h0.1, mul_comm]
    exact mul_le_of_le_one_right (abs_nonneg _) h0.2

/-- For `N > 0`, `ζ_N(y) = 0` as soon as one coordinate of `y` is at most `1/N` or at least `2N`. -/
private theorem cutoff_eq_zero {N : ℝ} (hN : 0 < N) {y : ℝ^2}
    (hy : y 0 ≤ 1 / N ∨ y 1 ≤ 1 / N ∨ 2 * N ≤ y 0 ∨ 2 * N ≤ y 1) :
    plateau N (y 0) * plateau N (y 1) = 0 := by
  rcases hy with h | h | h | h
  · rw [plateau_eq_zero_of_le hN h, zero_mul]
  · rw [plateau_eq_zero_of_le hN h, mul_zero]
  · rw [plateau_eq_zero_of_ge hN h, zero_mul]
  · rw [plateau_eq_zero_of_ge hN h, mul_zero]

/-- For `N > 0` the topological support of `ζ_N` lies in `{y | 1/N ≤ y₀ ∧ 1/N ≤ y₁}`. -/
private theorem tsupport_cutoff_subset {N : ℝ} (hN : 0 < N) :
    tsupport (fun y : ℝ^2 ↦ plateau N (y 0) * plateau N (y 1)) ⊆
      {y : ℝ^2 | 1 / N ≤ y 0 ∧ 1 / N ≤ y 1} := by
  refine closure_minimal (fun y hy ↦ ?_) ?_
  · by_contra h
    simp only [mem_ofPred_eq, not_and_or, not_le] at h
    exact hy (cutoff_eq_zero hN
      (by rcases h with h | h; exacts [Or.inl h.le, Or.inr (Or.inl h.le)]))
  · exact (isClosed_le continuous_const (EuclideanSpace.proj (0 : Fin 2)).continuous).inter
      (isClosed_le continuous_const (EuclideanSpace.proj (1 : Fin 2)).continuous)

/-- For `N > 0` the cutoff `ζ_N` has compact support. -/
private theorem hasCompactSupport_cutoff {N : ℝ} (hN : 0 < N) :
    HasCompactSupport (fun y : ℝ^2 ↦ plateau N (y 0) * plateau N (y 1)) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ^2) (4 * N + 4 / N)) fun y hy ↦ ?_
  refine cutoff_eq_zero hN ?_
  by_contra h
  simp only [not_or, not_le] at h
  obtain ⟨h0, h1, h2, h3⟩ := h
  apply hy
  rw [Metric.mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  have hp : 0 < 1 / N := by positivity
  have a0 : |y 0| ≤ 2 * N := by rw [abs_le]; constructor <;> linarith
  have a1 : |y 1| ≤ 2 * N := by rw [abs_le]; constructor <;> linarith
  calc √(‖y 0‖ ^ 2 + ‖y 1‖ ^ 2) ≤ √((2 * N) ^ 2 + (2 * N) ^ 2) := by
        gcongr <;> simp only [Real.norm_eq_abs] <;> nlinarith [abs_nonneg (y 0), abs_nonneg (y 1)]
    _ ≤ √((4 * N) ^ 2) := by gcongr; nlinarith
    _ = 4 * N := Real.sqrt_sq (by positivity)
    _ ≤ 4 * N + 4 / N := le_add_of_nonneg_right (by positivity)

/-- At each point `y` of the open quadrant, `ζ_{n+1}(y) = 1` for all large `n`. -/
private theorem tendsto_cutoff_eventually_eq_one {y : ℝ^2} (hy : 0 < y 0 ∧ 0 < y 1) :
    ∀ᶠ n : ℕ in atTop, plateau ((n : ℝ) + 1) (y 0) * plateau ((n : ℝ) + 1) (y 1) = 1 := by
  filter_upwards [(tendsto_atTop_add_const_right atTop (1 : ℝ)
    tendsto_natCast_atTop_atTop).eventually_gt_atTop
      (max (max (2 / y 0) (2 / y 1)) (max (y 0) (y 1)))] with n hmax
  have hN : 0 < (n : ℝ) + 1 := by positivity
  simp only [max_lt_iff] at hmax
  obtain ⟨⟨a, b⟩, c, d⟩ := hmax
  have ha : 2 / ((n : ℝ) + 1) ≤ y 0 := by
    rw [div_le_iff₀ hN]; rw [div_lt_iff₀ hy.1] at a; linarith
  have hb : 2 / ((n : ℝ) + 1) ≤ y 1 := by
    rw [div_le_iff₀ hN]; rw [div_lt_iff₀ hy.2] at b; linarith
  rw [plateau_eq_one hN ha c.le, plateau_eq_one hN hb d.le, mul_one]

/-! ### The divergence theorem on the quadrant -/

/-- **Divergence integrals over the open quadrant vanish.** If `Φ = (Φ₀, Φ₁)` is `C¹` on the
open quadrant `Q`, `∂₀Φ₀ + ∂₁Φ₁` is integrable on `Q`, and `|Φⱼ(y)| ≤ yⱼ m(y)` on `Q` for a
function `m` integrable on `Q`, then `∫_Q (∂₀Φ₀ + ∂₁Φ₁) = 0`. The bound makes the flux through the
two axes, the corner and the far field vanish. -/
theorem integral_quadrant_divergence_eq_zero {Φ : Fin 2 → ℝ^2 → ℝ} {m : ℝ^2 → ℝ}
    (hΦ : ∀ j, ContDiffOn ℝ 1 (Φ j) {y : ℝ^2 | 0 < y 0 ∧ 0 < y 1})
    (hdiv : IntegrableOn (fun y ↦ ∑ j, ∂[j] (Φ j) y) {y : ℝ^2 | 0 < y 0 ∧ 0 < y 1})
    (hm : IntegrableOn m {y : ℝ^2 | 0 < y 0 ∧ 0 < y 1})
    (hbound : ∀ j, ∀ y ∈ {y : ℝ^2 | 0 < y 0 ∧ 0 < y 1}, |Φ j y| ≤ y j * m y) :
    ∫ y in {y : ℝ^2 | 0 < y 0 ∧ 0 < y 1}, ∑ j, ∂[j] (Φ j) y = 0 := by
  set Q : Set (ℝ^2) := {y | 0 < y 0 ∧ 0 < y 1} with hQ
  have hQo : IsOpen Q :=
    (isOpen_lt continuous_const (EuclideanSpace.proj (0 : Fin 2)).continuous).inter
      (isOpen_lt continuous_const (EuclideanSpace.proj (1 : Fin 2)).continuous)
  have hQm : MeasurableSet Q := hQo.measurableSet
  obtain ⟨S, hS0, hS⟩ : ∃ S : ℝ, 0 ≤ S ∧ ∀ u, |deriv Real.smoothTransition u| ≤ S :=
    ⟨36, by norm_num, abs_deriv_smoothTransition_le⟩
  set ζ : ℕ → ℝ^2 → ℝ := fun n y ↦ plateau ((n : ℝ) + 1) (y 0) * plateau ((n : ℝ) + 1) (y 1)
    with hζ
  have hNpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n ↦ by positivity
  have hsub : ∀ n, tsupport (ζ n) ⊆ Q := fun n ↦ (tsupport_cutoff_subset (hNpos n)).trans
    fun y hy ↦ ⟨(by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)).trans_le hy.1,
      (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)).trans_le hy.2⟩
  have hzero : ∀ n, ∀ y ∉ Q, ζ n y = 0 := fun n y hy ↦
    image_eq_zero_of_notMem_tsupport fun h ↦ hy (hsub n h)
  have hcont : ∀ j, ContinuousOn (∂[j] (Φ j)) Q := fun j ↦
    ((hΦ j).continuousOn_fderiv_of_isOpen hQo le_rfl).clm_apply continuousOn_const
  -- integration by parts against the cutoffs
  have hA : ∀ n, ∫ y in Q, ζ n y * ∑ j, ∂[j] (Φ j) y =
      -∑ j, ∫ y in Q, ∂[j] (ζ n) y * Φ j y := by
    intro n
    have hint : ∀ j, Integrable (fun y ↦ ζ n y * ∂[j] (Φ j) y) := fun j ↦
      (hasCompactSupport_cutoff (hNpos n)).integrable_of_continuousOn_tsupport
        (((contDiff_cutoff _).continuous.continuousOn).mul ((hcont j).mono (hsub n)))
        fun y hy ↦ by simp only [hζ]; rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ by rw [hzero n y hy, zero_mul]]
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum _ fun j _ ↦ hint j, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [integral_mul_partialDeriv_eq_neg_of_contDiffAt j (contDiff_cutoff _)
      (fun y hy ↦ (hΦ j).contDiffAt (hQo.mem_nhds (hsub n hy)))
      (hasCompactSupport_cutoff (hNpos n))]
    congr 1
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ ?_).symm
    have hy' : y ∉ tsupport (ζ n) := fun h ↦ hy (hsub n h)
    simp only [hζ] at hy'
    simp only [partialDeriv, fderiv_of_notMem_tsupport ℝ hy', zero_apply,
      zero_mul]
  -- the cutoffs converge to one
  have hB : Tendsto (fun n ↦ ∫ y in Q, ζ n y * ∑ j, ∂[j] (Φ j) y) atTop
      (𝓝 (∫ y in Q, ∑ j, ∂[j] (Φ j) y)) := by
    refine tendsto_integral_of_dominated_convergence (fun y ↦ ‖∑ j, ∂[j] (Φ j) y‖)
      (fun n ↦ (contDiff_cutoff _).continuous.aestronglyMeasurable.mul hdiv.aestronglyMeasurable)
      hdiv.norm (fun n ↦ Eventually.of_forall fun y ↦ ?_) ?_
    · rw [norm_mul]
      refine mul_le_of_le_one_left (norm_nonneg _) ?_
      have h0 := plateau_mem_Icc ((n : ℝ) + 1) (y 0)
      have h1 := plateau_mem_Icc ((n : ℝ) + 1) (y 1)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0.1 h1.1)]
      exact (mul_le_of_le_one_left h1.1 h0.2).trans h1.2
    · refine (ae_restrict_iff' hQm).2 (Eventually.of_forall fun y hy ↦ ?_)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [tendsto_cutoff_eventually_eq_one hy] with n hn
      simp only [hζ, hn, one_mul]
  -- the boundary terms vanish
  have hC : ∀ j, Tendsto (fun n ↦ ∫ y in Q, ∂[j] (ζ n) y * Φ j y) atTop (𝓝 0) := by
    intro j
    have hm0 : ∀ y ∈ Q, 0 ≤ m y := fun y hy ↦
      nonneg_of_mul_nonneg_right ((abs_nonneg _).trans (hbound j y hy))
        (by fin_cases j; exacts [hy.1, hy.2])
    have hderiv : ∀ n y, y ∈ Q → |∂[j] (ζ n) y * Φ j y| ≤
        ((if y j ≤ 2 / ((n : ℝ) + 1) then 2 * S else 0) +
          (if (n : ℝ) + 1 ≤ y j then 2 * S else 0)) * m y := by
      intro n y hy
      have hyj : 0 < y j := by fin_cases j; exacts [hy.1, hy.2]
      have h1 := abs_partialDeriv_cutoff_le ((n : ℝ) + 1) j y
      have h2 := abs_deriv_plateau_mul_le (hNpos n) hyj hS
      rw [abs_mul]
      calc |∂[j] (ζ n) y| * |Φ j y| ≤ |deriv (plateau ((n : ℝ) + 1)) (y j)| * (y j * m y) :=
            mul_le_mul h1 (hbound j y hy) (abs_nonneg _) (abs_nonneg _)
        _ = |deriv (plateau ((n : ℝ) + 1)) (y j)| * y j * m y := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right h2 (hm0 y hy)
    refine (tendsto_integral_of_dominated_convergence (fun y ↦ 4 * S * m y)
      (fun n ↦ ((contDiff_cutoff _).continuous_fderiv one_ne_zero |>.clm_apply
        continuous_const).aestronglyMeasurable.mul
          (((hΦ j).continuousOn).aestronglyMeasurable hQm)) (hm.const_mul _)
      (fun n ↦ (ae_restrict_iff' hQm).2 (Eventually.of_forall fun y hy ↦ ?_)) ?_).trans
      (by rw [integral_zero])
    · rw [Real.norm_eq_abs]
      refine (hderiv n y hy).trans (mul_le_mul_of_nonneg_right ?_ (hm0 y hy))
      split_ifs <;> linarith
    · refine (ae_restrict_iff' hQm).2 (Eventually.of_forall fun y hy ↦ ?_)
      have hyj : 0 < y j := by fin_cases j; exacts [hy.1, hy.2]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [(tendsto_atTop_add_const_right atTop (1 : ℝ)
        tendsto_natCast_atTop_atTop).eventually_gt_atTop (max (2 / y j) (y j))] with n hmax
      rw [max_lt_iff, div_lt_iff₀ hyj] at hmax
      have ha : ¬ y j ≤ 2 / ((n : ℝ) + 1) := by
        rw [not_le, div_lt_iff₀ (hNpos n)]; linarith [hmax.1]
      have hb : ¬ (n : ℝ) + 1 ≤ y j := not_le.2 hmax.2
      have := hderiv n y hy
      rw [ite_eq_right ha, ite_eq_right hb, add_zero, zero_mul] at this
      exact (abs_nonpos_iff.1 this).symm
  have hC' := (tendsto_finsetSum (Finset.univ : Finset (Fin 2)) fun j _ ↦ hC j).neg
  simp only [Finset.sum_const_zero, neg_zero] at hC'
  exact tendsto_nhds_unique hB (by simpa only [hA] using hC')

/-- **Integration by parts of a transport term over the open quadrant**:
`∫_Q h (V·∇g) = -∫_Q g div(h V)` for `g`, `h` and `V` that are `C¹` on `Q`, when both integrands
are integrable on `Q` and `|g h Vⱼ| ≤ yⱼ m` on `Q` with `m` integrable on `Q`. -/
theorem integral_quadrant_mul_advectiveDerivative_eq_neg {g h : ℝ^2 → ℝ} {V : ℝ^2 → ℝ^2}
    {m : ℝ^2 → ℝ} (hg : ContDiffOn ℝ 1 g {y : ℝ^2 | 0 < y 0 ∧ 0 < y 1})
    (hh : ContDiffOn ℝ 1 h {y : ℝ^2 | 0 < y 0 ∧ 0 < y 1})
    (hV : ContDiffOn ℝ 1 V {y : ℝ^2 | 0 < y 0 ∧ 0 < y 1})
    (h₁ : IntegrableOn (fun y ↦ h y * advectiveDerivative V g y) {y : ℝ^2 | 0 < y 0 ∧ 0 < y 1})
    (h₂ : IntegrableOn (fun y ↦ g y * divergence (fun z ↦ h z • V z) y)
      {y : ℝ^2 | 0 < y 0 ∧ 0 < y 1})
    (hm : IntegrableOn m {y : ℝ^2 | 0 < y 0 ∧ 0 < y 1})
    (hbound : ∀ j, ∀ y ∈ {y : ℝ^2 | 0 < y 0 ∧ 0 < y 1}, |g y * h y * V y j| ≤ y j * m y) :
    ∫ y in {y : ℝ^2 | 0 < y 0 ∧ 0 < y 1}, h y * advectiveDerivative V g y =
      -∫ y in {y : ℝ^2 | 0 < y 0 ∧ 0 < y 1}, g y * divergence (fun z ↦ h z • V z) y := by
  set Q : Set (ℝ^2) := {y | 0 < y 0 ∧ 0 < y 1} with hQ
  have hQo : IsOpen Q :=
    (isOpen_lt continuous_const (EuclideanSpace.proj (0 : Fin 2)).continuous).inter
      (isOpen_lt continuous_const (EuclideanSpace.proj (1 : Fin 2)).continuous)
  have hVj : ∀ j : Fin 2, ContDiffOn ℝ 1 (fun y ↦ V y j) Q := fun j ↦
    (EuclideanSpace.proj j : ℝ^2 →L[ℝ] ℝ).contDiff.comp_contDiffOn hV
  have hΦ : ∀ j : Fin 2, ContDiffOn ℝ 1 (fun y ↦ g y * (h y * V y j)) Q := fun j ↦
    hg.mul (hh.mul (hVj j))
  have hpt : ∀ y ∈ Q, ∑ j : Fin 2, ∂[j] (fun y ↦ g y * (h y * V y j)) y =
      h y * advectiveDerivative V g y + g y * divergence (fun z ↦ h z • V z) y := by
    intro y hy
    have hn : Q ∈ 𝓝 y := hQo.mem_nhds hy
    have dg : DifferentiableAt ℝ g y := (hg.contDiffAt hn).differentiableAt one_ne_zero
    have dh : DifferentiableAt ℝ h y := (hh.contDiffAt hn).differentiableAt one_ne_zero
    have dV : ∀ j : Fin 2, DifferentiableAt ℝ (fun y ↦ V y j) y := fun j ↦
      ((hVj j).contDiffAt hn).differentiableAt one_ne_zero
    have hsplit : ∀ j : Fin 2, ∂[j] (fun y ↦ g y * (h y * V y j)) y =
        V y j * ∂[j] g y * h y + g y * ∂[j] (fun z ↦ h z * V z j) y := fun j ↦ by
      rw [partialDeriv_mul dg
        (show DifferentiableAt ℝ (fun z ↦ h z * V z j) y from dh.mul (dV j))]
      ring
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib, advectiveDerivative_eq_sum_mul_partialDeriv, Finset.mul_sum,
      divergence, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  have hdiv : IntegrableOn (fun y ↦ ∑ j : Fin 2, ∂[j] (fun y ↦ g y * (h y * V y j)) y) Q :=
    (h₁.add h₂).congr_fun (fun y hy ↦ (hpt y hy).symm) hQo.measurableSet
  have hzero := integral_quadrant_divergence_eq_zero (Φ := fun j y ↦ g y * (h y * V y j))
    hΦ hdiv hm fun j y hy ↦ by rw [← mul_assoc]; exact hbound j y hy
  rw [setIntegral_congr_fun hQo.measurableSet hpt, integral_add h₁ h₂] at hzero
  linarith

end PDE.Analysis
