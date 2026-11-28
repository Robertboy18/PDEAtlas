/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Analysis.Calculus.Radial.TruncatedSquare
public import PDE.Analysis.Integration.WeightedEstimate
public import PDE.Analysis.MeasureTheory.Integral.NonnegativeLimit
public import PDE.FDeriv.PartialDeriv.Transport
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import PDE.FDeriv.Laplacian.Continuity
import PDE.FDeriv.PartialDeriv.Regularity

/-!
# Second and fourth moments of solutions of the self-similar equation

Let a divergence-free field `v` on `ℝⁿ`, square integrable with its gradient, solve
`c v - ½ x·∇v + W·∇v - Δv = G - ∇Q`. Are `|x| v` and `|x| ∇v` square integrable? Are `|x|² v`
and `|x|² ∇v`? The drift `-½ x·∇v` produces moments, and this module turns that into theorems.
The second moments follow when `c + n/4 > 3/16`, and the fourth moments when
`c + n/4 + ½ > 3/16` and the second moments are known. The moment of `∇v` needs no sign
condition once the moment of `v` is known. Hou, Wang and Yang use these moments for the near
field of their profile, to prove its decay at infinity. Higher moments, with the weights
`φ_L |x|^{2m}` for `m ≥ 2`, are not treated.

All the results are for data `(v, W, G, Q)` as in `integral_weight_mul_energy_le`: `v` of class
`C²` and divergence free, `W` of class `C¹`, divergence free and bounded, `Q` of class `C¹`, `G`
continuous, and the equation in the paired form
`similarityPairing c v W x = ⟪G x, v x⟫ - DQ(x) v(x)`.

## Main results

* `integrable_norm_sq_mul_of_similarityPairing`: if `v`, `∇v`, `|x| G` and `Q` are square
  integrable and `c + n/4 > 3/16`, then `|x| v` and `|x| ∇v` are square integrable.
* `integrable_norm_sq_mul_sum_of_similarityPairing`: if moreover `|x| v` is square integrable,
  then `|x| ∇v` is, for every `c`.
* `integrable_norm_pow_four_mul_of_similarityPairing`: if `v`, `|x| v`, `|x| ∇v`, `|x|² G` and
  `|x| Q` are square integrable and `c + n/4 + ½ > 3/16`, then `|x|² v` and `|x|² ∇v` are square
  integrable.
* `exists_integral_truncatedNormSq_mul_energy_le` and
  `exists_integral_truncatedNormSq_mul_normSq_mul_energy_le`: the weighted energy estimates with
  the truncated weights `φ_L` and `φ_L |x|²`, uniformly in `L`.
* `integrable_norm_sq_mul_of_forall_truncatedNormSq`: for every nonnegative integrable `g`, a
  bound `∫ φ_L g ≤ C` for all `L` gives `∫ |x|² g ≤ C`.
* `memLp_two_smul_of_sq_mul_le`, `integrable_sum_norm_partialDeriv_sq_of_memLp` and
  `norm_fderiv_fderiv_sq_le_sum`: the passage between these integrals and `L²` membership of
  `w f`, `∇f` and `∇²f`.

## How it works

Pair the equation with `ω v`. The drift gives `(n/4) ∫ ω |v|²` plus `¼ ∫ (x·∇ω) |v|²`, and
`x·∇ω` is `2ω` for `ω = |x|²` and `4ω` for `ω = |x|⁴`. The pairing with `|x|² v` need not
converge, so the weight is the bounded `φ_L = truncatedNormSq L`, for which only `x·∇φ_L ≥ 0`
holds, or `φ_L |x|²`, for which `x·∇(φ_L |x|²) ≥ 2 φ_L |x|²`. The weighted energy estimate
`integral_weight_mul_energy_le` then gives a bound that does not depend on `L`, and Fatou's
lemma gives the moment as `L → ∞`. The coefficient of `∫ ω |v|²` that survives is
`c + n/4 - 3/16` for `φ_L` and `c + n/4 + ½ - 3/16` for `φ_L |x|²`. If it is positive, the
moments of `v` and of `∇v` both follow. If it is not, the moment of `∇v` still follows once the
moment of `v` is known.

## References

* T. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Section 2.1, the sketch of
  the proof of Proposition 4, pp. 10-11, and Appendix F, steps 1 and 2 of the proof of
  Proposition 4, (F.11)-(F.15), pp. 69-70. <https://arxiv.org/abs/2509.25116v2>
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter SobolevSpace.Approximation
open scoped InnerProductSpace Topology

namespace PDE.Analysis

variable {n : ℕ}

/-! ### Passing between integrals and `L²` membership -/

/-- `w f` is square integrable when `w² |f|²` is dominated by an integrable function. -/
theorem memLp_two_smul_of_sq_mul_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {w : α → ℝ} {f : α → E} {g : α → ℝ}
    (hwf : AEStronglyMeasurable (fun x ↦ w x • f x) μ) (hg : Integrable g μ)
    (h : ∀ x, w x ^ 2 * ‖f x‖ ^ 2 ≤ g x) : MemLp (fun x ↦ w x • f x) 2 μ := by
  refine (memLp_two_iff_integrable_sq_norm hwf).mpr
    (hg.mono' (hwf.norm.pow 2) (.of_forall fun x ↦ ?_))
  rw [Real.norm_of_nonneg (by positivity), norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  exact h x

/-- `Σᵢ |∂ᵢf|²` is integrable when `f` is of class `C¹` and `∇f` is square integrable. -/
theorem integrable_sum_norm_partialDeriv_sq_of_memLp {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ^n → E} (hf : ContDiff ℝ 1 f) (h : MemLp (fderiv ℝ f) 2 volume) :
    Integrable fun x ↦ ∑ i : Fin n, ‖∂[i] f x‖ ^ 2 := by
  refine integrable_finsetSum _ fun i _ ↦ ?_
  have hc : Continuous (∂[i] f) := hf.continuous_partialDeriv i
  exact (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mp
    (h.of_le hc.aestronglyMeasurable
      (.of_forall fun x ↦ PDE.norm_partialDeriv_le_norm_fderiv i f x))

/-- The second derivative is controlled by the second coordinate derivatives:
`|∇²f|² ≤ Σₖ Σᵢ |∂ᵢ∂ₖf|²` at a point where `f` is of class `C²`. -/
theorem norm_fderiv_fderiv_sq_le_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ^n → E} {x : ℝ^n} (hf : ContDiffAt ℝ 2 f x) :
    ‖fderiv ℝ (fderiv ℝ f) x‖ ^ 2 ≤ ∑ k : Fin n, ∑ i : Fin n, ‖∂[i] (∂[k] f) x‖ ^ 2 := by
  refine (norm_fderiv_sq_le_sum_norm_partialDeriv_sq (fderiv ℝ f) x).trans
    (Finset.sum_le_sum fun k _ ↦ ?_)
  rw [PDE.partialDeriv_fderiv k hf]
  exact norm_fderiv_sq_le_sum_norm_partialDeriv_sq (∂[k] f) x

/-! ### The limit `L → ∞` -/

/-- **The limit `L → ∞` of the truncated weight.** If `g` is nonnegative and integrable and
`∫ φ_L g ≤ C` for every `L > 0`, then `|x|² g` is integrable and `∫ |x|² g ≤ C`. This is Fatou's
lemma, since `φ_L(x) = |x|²` once `L ≥ |x|`. -/
theorem integrable_norm_sq_mul_of_forall_truncatedNormSq {g : ℝ^n → ℝ} {C : ℝ}
    (hg : Integrable g) (hg0 : ∀ x, 0 ≤ g x)
    (hC : ∀ L : ℝ, 0 < L → ∫ x, truncatedNormSq L x * g x ≤ C) :
    Integrable (fun x ↦ ‖x‖ ^ 2 * g x) ∧ ∫ x, ‖x‖ ^ 2 * g x ≤ C := by
  have hLk : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 1 := fun k ↦ by positivity
  refine integrable_and_integral_le_of_nonnegative_limit
    (F := fun (k : ℕ) (x : ℝ^n) ↦ truncatedNormSq ((k : ℝ) + 1) x * g x)
    (fun k ↦ integrable_truncatedNormSq_mul (hLk k) hg)
    (fun k ↦ .of_forall fun x ↦ mul_nonneg (truncatedNormSq_nonneg (hLk k) x) (hg0 x))
    (.of_forall fun k ↦ hC _ (hLk k)) (.of_forall fun x ↦ ?_)
  obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop N] with k hk
  have hx : ‖x‖ ≤ (k : ℝ) + 1 := by
    have : (N : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  rw [truncatedNormSq_of_norm_le (hLk k) hx]

/-! ### Second moments: the weight `φ_L` -/

section Similarity

variable {v W G : ℝ^n → ℝ^n} {Q : ℝ^n → ℝ} {c M : ℝ}

/-- **The weighted energy estimate with the weight `φ_L`, uniformly in `L`.** For data
`(v, W, G, Q)` of the self-similar equation with `v`, `∇v`, `|x| G` and `Q` square integrable,
`∫ φ_L Σᵢ|∂ᵢv|² + (c + n/4 - 3/16) ∫ φ_L |v|²` is bounded by a constant that does not depend on
`L`. The weight increases along rays, so the drift keeps the coefficient `c + n/4`. -/
theorem exists_integral_truncatedNormSq_mul_energy_le (hv : ContDiff ℝ 2 v)
    (hdivv : ∀ x, ∇· v x = 0) (hW : ContDiff ℝ 1 W) (hdivW : ∀ x, ∇· W x = 0)
    (hWb : ∀ x, ‖W x‖ ≤ M) (hQ : ContDiff ℝ 1 Q) (hG : Continuous G)
    (heq : ∀ x, similarityPairing c v W x = ⟪G x, v x⟫_ℝ - fderiv ℝ Q x (v x))
    (h₁ : Integrable fun x ↦ ∑ i : Fin n, ‖∂[i] v x‖ ^ 2) (h₂ : Integrable fun x ↦ ‖v x‖ ^ 2)
    (h₅ : Integrable fun x ↦ ‖x‖ ^ 2 * ‖G x‖ ^ 2) (h₆ : Integrable fun x ↦ Q x ^ 2) :
    ∃ C : ℝ, ∀ L : ℝ, 0 < L →
      (∫ x, truncatedNormSq L x * ∑ i : Fin n, ‖∂[i] v x‖ ^ 2) +
        (c + n / 4 - 3 / 16) * ∫ x, truncatedNormSq L x * ‖v x‖ ^ 2 ≤ C := by
  obtain ⟨Ce, hCe0, hCe⟩ := exists_norm_fderiv_truncatedNormSq_le n
  obtain ⟨CΔ, -, hCΔ⟩ := exists_abs_laplacian_truncatedNormSq_le n
  refine ⟨16 * (∫ x, ‖x‖ ^ 2 * ‖G x‖ ^ 2) + 4 * Ce ^ 2 * (∫ x, Q x ^ 2) +
    (M ^ 2 * Ce ^ 2 + CΔ / 2) * ∫ x, ‖v x‖ ^ 2, fun L hL ↦ ?_⟩
  have hφc : ContDiff ℝ (⊤ : ℕ∞) (truncatedNormSq (n := n) L) := contDiff_truncatedNormSq L
  have hφ2 : ContDiff ℝ 2 (truncatedNormSq (n := n) L) := hφc.of_le (by simp)
  -- The integrability conditions on the weight.
  have h₃ : Integrable fun x : ℝ^n ↦
      ‖fderiv ℝ (truncatedNormSq L) x‖ * (1 + ‖x‖) * ‖v x‖ ^ 2 := by
    refine h₂.bdd_mul (c := Ce * (2 * L) * (1 + 2 * L))
      (((hφc.continuous_fderiv (by simp)).norm.mul
        (continuous_const.add continuous_norm)).aestronglyMeasurable) (.of_forall fun x ↦ ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (by positivity))]
    by_cases hx : ‖x‖ ≤ 2 * L
    · have hroot : √(truncatedNormSq L x) ≤ 2 * L := by
        calc √(truncatedNormSq L x) ≤ √((2 * L) ^ 2) :=
              Real.sqrt_le_sqrt (truncatedNormSq_le hL x)
          _ = 2 * L := Real.sqrt_sq (by positivity)
      exact mul_le_mul ((hCe L hL x).trans (mul_le_mul_of_nonneg_left hroot hCe0))
        (by linarith) (by positivity) (by positivity)
    · rw [fderiv_truncatedNormSq_of_two_mul_lt hL (not_le.mp hx), norm_zero, zero_mul]
      positivity
  have h₄ : Integrable fun x : ℝ^n ↦ |laplacian (truncatedNormSq L) x| * ‖v x‖ ^ 2 :=
    h₂.bdd_mul (c := CΔ) hφ2.continuous_coordinate_laplacian.abs.aestronglyMeasurable
      (.of_forall fun x ↦ by
        rw [Real.norm_eq_abs, abs_abs]
        exact hCΔ L hL x)
  -- The weighted right side: `φ_L ≤ 4 |x|²`.
  have hG4 : ∀ x : ℝ^n, truncatedNormSq L x * ‖G x‖ ^ 2 ≤ 4 * (‖x‖ ^ 2 * ‖G x‖ ^ 2) :=
    fun x ↦ by
      nlinarith [mul_le_mul_of_nonneg_right (truncatedNormSq_le_four_mul hL x)
        (sq_nonneg ‖G x‖)]
  have h₅' : Integrable fun x : ℝ^n ↦ truncatedNormSq L x * ‖G x‖ ^ 2 :=
    (h₅.const_mul 4).mono' ((hφc.continuous.mul (hG.norm.pow 2)).aestronglyMeasurable)
      (.of_forall fun x ↦ by
        rw [Real.norm_of_nonneg (mul_nonneg (truncatedNormSq_nonneg hL x) (by positivity))]
        exact hG4 x)
  have hGle := integral_mono h₅' (h₅.const_mul 4) hG4
  rw [integral_const_mul] at hGle
  -- The weighted energy estimate with `σ = 1`.
  have h := integral_weight_mul_energy_le (σ := fun _ ↦ 1) (γ := c + n / 4) hv hdivv hW hdivW
    hWb hQ hG heq hφ2 (truncatedNormSq_nonneg hL) (fun _ ↦ zero_le_one) hCe0
    (fun x ↦ by simpa using hCe L hL x) (fun x ↦ by simpa using hCΔ L hL x)
    (fun x ↦ by linarith [fderiv_truncatedNormSq_apply_self_nonneg hL x])
    (integrable_truncatedNormSq_mul hL h₁) (integrable_truncatedNormSq_mul hL h₂) h₃ h₄ h₅'
    (by simpa using h₆) (by simpa using h₂) (integrable_truncatedNormSq_mul hL h₆)
  simp only [one_pow, one_mul] at h
  linarith

/-- **Second moment of the gradient.** For data `(v, W, G, Q)` of the self-similar equation
with `v`, `∇v`, `|x| G`, `Q` and `|x| v` square integrable, `|x| ∇v` is square integrable. No
sign of the coefficient `c + n/4 - 3/16` is needed, because the moment of `v` is given. -/
theorem integrable_norm_sq_mul_sum_of_similarityPairing (hv : ContDiff ℝ 2 v)
    (hdivv : ∀ x, ∇· v x = 0) (hW : ContDiff ℝ 1 W) (hdivW : ∀ x, ∇· W x = 0)
    (hWb : ∀ x, ‖W x‖ ≤ M) (hQ : ContDiff ℝ 1 Q) (hG : Continuous G)
    (heq : ∀ x, similarityPairing c v W x = ⟪G x, v x⟫_ℝ - fderiv ℝ Q x (v x))
    (h₁ : Integrable fun x ↦ ∑ i : Fin n, ‖∂[i] v x‖ ^ 2) (h₂ : Integrable fun x ↦ ‖v x‖ ^ 2)
    (h₅ : Integrable fun x ↦ ‖x‖ ^ 2 * ‖G x‖ ^ 2) (h₆ : Integrable fun x ↦ Q x ^ 2)
    (h₂' : Integrable fun x ↦ ‖x‖ ^ 2 * ‖v x‖ ^ 2) :
    Integrable fun x ↦ ‖x‖ ^ 2 * ∑ i : Fin n, ‖∂[i] v x‖ ^ 2 := by
  obtain ⟨C, hC⟩ := exists_integral_truncatedNormSq_mul_energy_le hv hdivv hW hdivW hWb hQ hG
    heq h₁ h₂ h₅ h₆
  refine (integrable_norm_sq_mul_of_forall_truncatedNormSq
    (C := C + |c + n / 4 - 3 / 16| * (4 * ∫ x, ‖x‖ ^ 2 * ‖v x‖ ^ 2)) h₁
    (fun x ↦ Finset.sum_nonneg fun i _ ↦ by positivity) fun L hL ↦ ?_).1
  have hX0 : 0 ≤ ∫ x, truncatedNormSq L x * ‖v x‖ ^ 2 :=
    integral_nonneg fun x ↦ mul_nonneg (truncatedNormSq_nonneg hL x) (by positivity)
  have hv4 : ∀ x : ℝ^n, truncatedNormSq L x * ‖v x‖ ^ 2 ≤ 4 * (‖x‖ ^ 2 * ‖v x‖ ^ 2) :=
    fun x ↦ by
      nlinarith [mul_le_mul_of_nonneg_right (truncatedNormSq_le_four_mul hL x)
        (sq_nonneg ‖v x‖)]
  have hX := integral_mono (integrable_truncatedNormSq_mul hL h₂) (h₂'.const_mul 4) hv4
  rw [integral_const_mul] at hX
  have h1 : -((c + n / 4 - 3 / 16) * ∫ x, truncatedNormSq L x * ‖v x‖ ^ 2) ≤
      |c + n / 4 - 3 / 16| * ∫ x, truncatedNormSq L x * ‖v x‖ ^ 2 := by
    rw [← neg_mul]
    exact mul_le_mul_of_nonneg_right (neg_le_abs _) hX0
  have h2 := mul_le_mul_of_nonneg_left hX (abs_nonneg (c + n / 4 - 3 / 16))
  linarith [hC L hL]

/-- **Second moments.** For data `(v, W, G, Q)` of the self-similar equation with `v`, `∇v`,
`|x| G` and `Q` square integrable, and `c + n/4 > 3/16`, both `|x| v` and `|x| ∇v` are square
integrable. -/
theorem integrable_norm_sq_mul_of_similarityPairing (hv : ContDiff ℝ 2 v)
    (hdivv : ∀ x, ∇· v x = 0) (hW : ContDiff ℝ 1 W) (hdivW : ∀ x, ∇· W x = 0)
    (hWb : ∀ x, ‖W x‖ ≤ M) (hQ : ContDiff ℝ 1 Q) (hG : Continuous G)
    (heq : ∀ x, similarityPairing c v W x = ⟪G x, v x⟫_ℝ - fderiv ℝ Q x (v x))
    (hc : 3 / 16 < c + n / 4)
    (h₁ : Integrable fun x ↦ ∑ i : Fin n, ‖∂[i] v x‖ ^ 2) (h₂ : Integrable fun x ↦ ‖v x‖ ^ 2)
    (h₅ : Integrable fun x ↦ ‖x‖ ^ 2 * ‖G x‖ ^ 2) (h₆ : Integrable fun x ↦ Q x ^ 2) :
    Integrable (fun x ↦ ‖x‖ ^ 2 * ‖v x‖ ^ 2) ∧
      Integrable (fun x ↦ ‖x‖ ^ 2 * ∑ i : Fin n, ‖∂[i] v x‖ ^ 2) := by
  obtain ⟨C, hC⟩ := exists_integral_truncatedNormSq_mul_energy_le hv hdivv hW hdivW hWb hQ hG
    heq h₁ h₂ h₅ h₆
  have hκ : 0 < c + n / 4 - 3 / 16 := by linarith
  have h₂' : Integrable fun x ↦ ‖x‖ ^ 2 * ‖v x‖ ^ 2 :=
    (integrable_norm_sq_mul_of_forall_truncatedNormSq (C := C / (c + n / 4 - 3 / 16)) h₂
      (fun x ↦ by positivity) fun L hL ↦ by
        have hY0 : 0 ≤ ∫ x, truncatedNormSq L x * ∑ i : Fin n, ‖∂[i] v x‖ ^ 2 :=
          integral_nonneg fun x ↦ mul_nonneg (truncatedNormSq_nonneg hL x)
            (Finset.sum_nonneg fun i _ ↦ by positivity)
        rw [le_div_iff₀ hκ]
        linarith [hC L hL]).1
  exact ⟨h₂', integrable_norm_sq_mul_sum_of_similarityPairing hv hdivv hW hdivW hWb hQ hG heq
    h₁ h₂ h₅ h₆ h₂'⟩

/-! ### Fourth moments: the weight `φ_L |x|²` -/

/-- **The weighted energy estimate with the weight `φ_L |x|²`, uniformly in `L`.** For data
`(v, W, G, Q)` of the self-similar equation with `v`, `|x| v`, `|x| ∇v`, `|x|² G` and `|x| Q`
square integrable, `∫ φ_L |x|² Σᵢ|∂ᵢv|² + (c + n/4 + ½ - 3/16) ∫ φ_L |x|² |v|²` is bounded by a
constant that does not depend on `L`. The drift gains `½` because
`x·∇(φ_L |x|²) ≥ 2 φ_L |x|²`. -/
theorem exists_integral_truncatedNormSq_mul_normSq_mul_energy_le (hv : ContDiff ℝ 2 v)
    (hdivv : ∀ x, ∇· v x = 0) (hW : ContDiff ℝ 1 W) (hdivW : ∀ x, ∇· W x = 0)
    (hWb : ∀ x, ‖W x‖ ≤ M) (hQ : ContDiff ℝ 1 Q) (hG : Continuous G)
    (heq : ∀ x, similarityPairing c v W x = ⟪G x, v x⟫_ℝ - fderiv ℝ Q x (v x))
    (h₀ : Integrable fun x ↦ ‖v x‖ ^ 2)
    (h₁ : Integrable fun x ↦ ‖x‖ ^ 2 * ∑ i : Fin n, ‖∂[i] v x‖ ^ 2)
    (h₂ : Integrable fun x ↦ ‖x‖ ^ 2 * ‖v x‖ ^ 2)
    (h₅ : Integrable fun x ↦ ‖x‖ ^ 4 * ‖G x‖ ^ 2)
    (h₆ : Integrable fun x ↦ ‖x‖ ^ 2 * Q x ^ 2) :
    ∃ C : ℝ, ∀ L : ℝ, 0 < L →
      (∫ x, truncatedNormSq L x * ‖x‖ ^ 2 * ∑ i : Fin n, ‖∂[i] v x‖ ^ 2) +
        (c + n / 4 + 1 / 2 - 3 / 16) * ∫ x, truncatedNormSq L x * ‖x‖ ^ 2 * ‖v x‖ ^ 2 ≤ C := by
  obtain ⟨Ce, hCe0, hCe⟩ := exists_norm_fderiv_truncatedNormSq_mul_normSq_le n
  obtain ⟨CΔ, -, hCΔ⟩ := exists_abs_laplacian_truncatedNormSq_mul_normSq_le n
  refine ⟨16 * (∫ x, ‖x‖ ^ 4 * ‖G x‖ ^ 2) + 4 * Ce ^ 2 * (∫ x, ‖x‖ ^ 2 * Q x ^ 2) +
    (M ^ 2 * Ce ^ 2 + CΔ / 2) * ∫ x, ‖x‖ ^ 2 * ‖v x‖ ^ 2, fun L hL ↦ ?_⟩
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_norm_fderiv_truncatedNormSq_mul_normSq_le_one_add (n := n) hL
  have hωc : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ^n ↦ truncatedNormSq L y * ‖y‖ ^ 2) :=
    (contDiff_truncatedNormSq L).mul (contDiff_norm_sq ℝ)
  have hω2 : ContDiff ℝ 2 (fun y : ℝ^n ↦ truncatedNormSq L y * ‖y‖ ^ 2) := hωc.of_le (by simp)
  have hφ0 : ∀ x : ℝ^n, 0 ≤ truncatedNormSq L x := truncatedNormSq_nonneg hL
  -- The weight is at most `(2L)² |x|²`, so the second moments give integrability.
  have hmul : ∀ {g : ℝ^n → ℝ}, Integrable (fun x ↦ ‖x‖ ^ 2 * g x) →
      Integrable fun x ↦ truncatedNormSq L x * ‖x‖ ^ 2 * g x := fun hg ↦ by
    simpa only [mul_assoc] using integrable_truncatedNormSq_mul hL hg
  have h₃ : Integrable fun x : ℝ^n ↦
      ‖fderiv ℝ (fun y : ℝ^n ↦ truncatedNormSq L y * ‖y‖ ^ 2) x‖ * (1 + ‖x‖) * ‖v x‖ ^ 2 := by
    have hsum : Integrable fun x : ℝ^n ↦
        2 * C₁ * ‖v x‖ ^ 2 + 2 * C₁ * (‖x‖ ^ 2 * ‖v x‖ ^ 2) :=
      (h₀.const_mul (2 * C₁)).add (h₂.const_mul (2 * C₁))
    refine hsum.mono' ((((hωc.continuous_fderiv (by simp)).norm.mul
      (continuous_const.add continuous_norm)).mul
        (hv.continuous.norm.pow 2)).aestronglyMeasurable) (.of_forall fun x ↦ ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) (by positivity))
      (by positivity))]
    have h1 : ‖fderiv ℝ (fun y : ℝ^n ↦ truncatedNormSq L y * ‖y‖ ^ 2) x‖ * (1 + ‖x‖) ≤
        2 * C₁ + 2 * C₁ * ‖x‖ ^ 2 := by
      calc ‖fderiv ℝ (fun y : ℝ^n ↦ truncatedNormSq L y * ‖y‖ ^ 2) x‖ * (1 + ‖x‖)
          ≤ C₁ * (1 + ‖x‖) * (1 + ‖x‖) := mul_le_mul_of_nonneg_right (hC₁ x) (by positivity)
        _ ≤ 2 * C₁ + 2 * C₁ * ‖x‖ ^ 2 := by
            nlinarith [mul_nonneg hC₁0 (sq_nonneg (1 - ‖x‖))]
    calc ‖fderiv ℝ (fun y : ℝ^n ↦ truncatedNormSq L y * ‖y‖ ^ 2) x‖ * (1 + ‖x‖) * ‖v x‖ ^ 2
        ≤ (2 * C₁ + 2 * C₁ * ‖x‖ ^ 2) * ‖v x‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = 2 * C₁ * ‖v x‖ ^ 2 + 2 * C₁ * (‖x‖ ^ 2 * ‖v x‖ ^ 2) := by ring
  have h₄ : Integrable fun x : ℝ^n ↦
      |laplacian (fun y : ℝ^n ↦ truncatedNormSq L y * ‖y‖ ^ 2) x| * ‖v x‖ ^ 2 :=
    (h₂.const_mul CΔ).mono'
      ((hω2.continuous_coordinate_laplacian.abs.mul
        (hv.continuous.norm.pow 2)).aestronglyMeasurable)
      (.of_forall fun x ↦ by
        rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (by positivity))]
        calc |laplacian (fun y : ℝ^n ↦ truncatedNormSq L y * ‖y‖ ^ 2) x| * ‖v x‖ ^ 2
            ≤ CΔ * ‖x‖ ^ 2 * ‖v x‖ ^ 2 :=
              mul_le_mul_of_nonneg_right (hCΔ L hL x) (by positivity)
          _ = CΔ * (‖x‖ ^ 2 * ‖v x‖ ^ 2) := by ring)
  -- The weighted right side: `φ_L |x|² ≤ 4 |x|⁴`.
  have hG4 : ∀ x : ℝ^n, truncatedNormSq L x * ‖x‖ ^ 2 * ‖G x‖ ^ 2 ≤
      4 * (‖x‖ ^ 4 * ‖G x‖ ^ 2) := fun x ↦ by
    have h := mul_le_mul_of_nonneg_right (truncatedNormSq_le_four_mul hL x)
      (mul_nonneg (sq_nonneg ‖x‖) (sq_nonneg ‖G x‖))
    calc truncatedNormSq L x * ‖x‖ ^ 2 * ‖G x‖ ^ 2
        = truncatedNormSq L x * (‖x‖ ^ 2 * ‖G x‖ ^ 2) := by ring
      _ ≤ 4 * ‖x‖ ^ 2 * (‖x‖ ^ 2 * ‖G x‖ ^ 2) := h
      _ = 4 * (‖x‖ ^ 4 * ‖G x‖ ^ 2) := by ring
  have h₅' : Integrable fun x : ℝ^n ↦ truncatedNormSq L x * ‖x‖ ^ 2 * ‖G x‖ ^ 2 :=
    (h₅.const_mul 4).mono' ((hωc.continuous.mul (hG.norm.pow 2)).aestronglyMeasurable)
      (.of_forall fun x ↦ by
        rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (hφ0 x) (sq_nonneg _))
          (by positivity))]
        exact hG4 x)
  have hGle := integral_mono h₅' (h₅.const_mul 4) hG4
  rw [integral_const_mul] at hGle
  -- The weighted energy estimate with `σ = |x|`.
  have h := integral_weight_mul_energy_le (ω := fun y : ℝ^n ↦ truncatedNormSq L y * ‖y‖ ^ 2)
    (σ := fun x ↦ ‖x‖) (γ := c + n / 4 + 1 / 2) hv hdivv hW hdivW hWb hQ hG heq hω2
    (fun x ↦ mul_nonneg (hφ0 x) (sq_nonneg _)) (fun x ↦ norm_nonneg x) hCe0 (hCe L hL)
    (hCΔ L hL)
    (fun x ↦ by linarith [two_mul_le_fderiv_truncatedNormSq_mul_normSq_apply_self hL x])
    (hmul h₁) (hmul h₂) h₃ h₄ h₅' h₆ h₂ (hmul h₆)
  linarith

/-- **Fourth moments.** For data `(v, W, G, Q)` of the self-similar equation with `v`, `|x| v`,
`|x| ∇v`, `|x|² G` and `|x| Q` square integrable, and `c + n/4 + ½ > 3/16`, both `|x|² v` and
`|x|² ∇v` are square integrable. -/
theorem integrable_norm_pow_four_mul_of_similarityPairing (hv : ContDiff ℝ 2 v)
    (hdivv : ∀ x, ∇· v x = 0) (hW : ContDiff ℝ 1 W) (hdivW : ∀ x, ∇· W x = 0)
    (hWb : ∀ x, ‖W x‖ ≤ M) (hQ : ContDiff ℝ 1 Q) (hG : Continuous G)
    (heq : ∀ x, similarityPairing c v W x = ⟪G x, v x⟫_ℝ - fderiv ℝ Q x (v x))
    (hc : 3 / 16 < c + n / 4 + 1 / 2)
    (h₀ : Integrable fun x ↦ ‖v x‖ ^ 2)
    (h₁ : Integrable fun x ↦ ‖x‖ ^ 2 * ∑ i : Fin n, ‖∂[i] v x‖ ^ 2)
    (h₂ : Integrable fun x ↦ ‖x‖ ^ 2 * ‖v x‖ ^ 2)
    (h₅ : Integrable fun x ↦ ‖x‖ ^ 4 * ‖G x‖ ^ 2)
    (h₆ : Integrable fun x ↦ ‖x‖ ^ 2 * Q x ^ 2) :
    Integrable (fun x ↦ ‖x‖ ^ 4 * ‖v x‖ ^ 2) ∧
      Integrable (fun x ↦ ‖x‖ ^ 4 * ∑ i : Fin n, ‖∂[i] v x‖ ^ 2) := by
  obtain ⟨C, hC⟩ := exists_integral_truncatedNormSq_mul_normSq_mul_energy_le hv hdivv hW hdivW
    hWb hQ hG heq h₀ h₁ h₂ h₅ h₆
  have hκ : 0 < c + n / 4 + 1 / 2 - 3 / 16 := by linarith
  have hD0 : ∀ x, 0 ≤ ∑ i : Fin n, ‖∂[i] v x‖ ^ 2 := fun x ↦
    Finset.sum_nonneg fun i _ ↦ by positivity
  have hX0 : ∀ L : ℝ, 0 < L → 0 ≤ ∫ x, truncatedNormSq L x * ‖x‖ ^ 2 * ‖v x‖ ^ 2 :=
    fun L hL ↦ integral_nonneg fun x ↦
      mul_nonneg (mul_nonneg (truncatedNormSq_nonneg hL x) (sq_nonneg _)) (by positivity)
  have hY0 : ∀ L : ℝ, 0 < L →
      0 ≤ ∫ x, truncatedNormSq L x * ‖x‖ ^ 2 * ∑ i : Fin n, ‖∂[i] v x‖ ^ 2 :=
    fun L hL ↦ integral_nonneg fun x ↦
      mul_nonneg (mul_nonneg (truncatedNormSq_nonneg hL x) (sq_nonneg _)) (hD0 x)
  have hv4 := (integrable_norm_sq_mul_of_forall_truncatedNormSq
    (C := C / (c + n / 4 + 1 / 2 - 3 / 16)) h₂
    (fun x ↦ mul_nonneg (sq_nonneg _) (by positivity)) fun L hL ↦ by
      rw [le_div_iff₀ hκ]
      simp only [← mul_assoc]
      linarith [hC L hL, hY0 L hL]).1
  have hD4 := (integrable_norm_sq_mul_of_forall_truncatedNormSq (C := C) h₁
    (fun x ↦ mul_nonneg (sq_nonneg _) (hD0 x)) fun L hL ↦ by
      simp only [← mul_assoc]
      have := mul_nonneg hκ.le (hX0 L hL)
      linarith [hC L hL]).1
  have e₁ : (fun x : ℝ^n ↦ ‖x‖ ^ 2 * (‖x‖ ^ 2 * ‖v x‖ ^ 2)) = fun x ↦ ‖x‖ ^ 4 * ‖v x‖ ^ 2 :=
    funext fun x ↦ by ring
  have e₂ : (fun x : ℝ^n ↦ ‖x‖ ^ 2 * (‖x‖ ^ 2 * ∑ i : Fin n, ‖∂[i] v x‖ ^ 2)) =
      fun x ↦ ‖x‖ ^ 4 * ∑ i : Fin n, ‖∂[i] v x‖ ^ 2 := funext fun x ↦ by ring
  rw [e₁] at hv4
  rw [e₂] at hD4
  exact ⟨hv4, hD4⟩

end Similarity

end PDE.Analysis
