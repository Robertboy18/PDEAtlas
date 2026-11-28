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
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Order.Filter.ENNReal
public import PDE.Analysis.ENNReal.Basic
public import PDE.Analysis.Scalar.Inequalities
public import PDE.Analysis.Scalar.Powers
public import PDE.Analysis.Scalar.Sums
public import PDE.Analysis.Topology.Continuity

set_option linter.style.header false

/-!
# Limits and eventual properties

The lemmas state convergence of sequences and of functions along filters, pass inequalities to the
limit, and derive that a property holds eventually. The proofs use `Filter.Tendsto` with the order
and metric lemmas of Mathlib and `filter_upwards`.

## Main results

* `PDE.Analysis.tendsto_zero_of_ofReal`: For a real sequence `a` with `0 ≤ a n` for all `n`, if
  `ENNReal.ofReal (a n)` tends to `0` in `ℝ≥0∞`, then `a n` tends to `0` in `ℝ`.
* `PDE.Analysis.cauchy_of_local_small_of_split_bound`: A Cauchy criterion for the sequence `T (s n)`
  in a normed additive group. Assume `G (s n) ≤ 2` for all `n`, that for every `R > 0` and `δ > 0`
  there is `N` with `V R (s m) (s n) < δ` and `W R j (s m) (s n) < δ` for all `j : Fin 3` and all
  `m, n ≥ N`, and that for every `ε > 0` there are `R > 0` and `A ≥ 0` with
  `‖T u - T u'‖ ≤ A * (V R u u' + ∑ j, W R j u u') + ε * (G u + G u')` for all `u u'`. Then for
  every `ε > 0` there is `N` with `‖T (s m) - T (s n)‖ < ε` for all `m, n ≥ N`.
* `PDE.Analysis.eventually_one_div_add_one_le`: For every `ε > 0`, `1 / (n + 1) ≤ ε` holds for all
  sufficiently large natural numbers `n`.
* `PDE.Analysis.tendsto_clm_of_weak`: A continuous linear map `L` from a real Hilbert space `E` to
  `Fin k → ℝ` turns weak convergence into convergence: if `inner ℝ (x n) y → inner ℝ x₀ y` for every
  `y : E`, then `L (x n) → L x₀`.
* `PDE.Analysis.tendsto_inner_clm_apply`: In real Hilbert spaces, let continuous linear maps
  `T n : E →L[ℝ] F` converge to `T₀` in operator norm, let `‖x n‖ ≤ B` for all `n`, and let `x n`
  converge weakly to `x₀`, that is `inner ℝ (x n) y → inner ℝ x₀ y` for every `y`. Then
  `inner ℝ (T n (x n)) z → inner ℝ (T₀ x₀) z` for every `z`.
* `PDE.Analysis.tendsto_sqrt_toReal_zero`: If a sequence `L : ℕ → ℝ≥0∞` tends to `0`, then the real
  sequence `√(L n).toReal` tends to `0`.
* `PDE.Analysis.tendsto_zero_of_pow_tendsto_zero`: If `f : ℕ → ℝ` is nonnegative, `k ≠ 0` is a
  natural number and `f i ^ k → 0` as `i → ∞`, then `f i → 0`.
* `PDE.Analysis.Icc_mem_nhdsWithin_Ici_zero`: For every real `τ`, the interval `Icc 0 (τ + 1)` is a
  neighbourhood of `τ` within `Ici 0`, that is, `Icc 0 (τ + 1) ∈ 𝓝[Ici 0] τ`.

There are 26 further lemmas of the same kind.

## References

* Levent Alpöge and Tristan Buckmaster, the Lean package of the paper "Finite-time blow-up for the
  Navier–Stokes equations", <https://github.com/tristanbuckmaster/navier-stokes>, folder `lean/`,
  commit `ad53419`: the lemmas of this module and their proofs, adapted to this library. See
  `NOTICE` for attribution and permission.
-/

@[expose] public section

noncomputable section

open Filter Topology Set Real
open scoped ENNReal

namespace PDE.Analysis

/-- For every real `τ`, the interval `Icc 0 (τ + 1)` is a neighbourhood of `τ` within `Ici 0`, that
is, `Icc 0 (τ + 1) ∈ 𝓝[Ici 0] τ`. -/
theorem Icc_mem_nhdsWithin_Ici_zero (τ : ℝ) : Icc 0 (τ + 1) ∈ 𝓝[Ici 0] τ := by
  rw [← Ici_inter_Iic]
  exact inter_mem_nhdsWithin _ (Iic_mem_nhds (by linarith))

/-- A Cauchy criterion for the sequence `T (s n)` in a normed additive group. Assume `G (s n) ≤ 2`
for all `n`, that for every `R > 0` and `δ > 0` there is `N` with `V R (s m) (s n) < δ` and
`W R j (s m) (s n) < δ` for all `j : Fin 3` and all `m, n ≥ N`, and that for every `ε > 0` there are
`R > 0` and `A ≥ 0` with `‖T u - T u'‖ ≤ A * (V R u u' + ∑ j, W R j u u') + ε * (G u + G u')` for
all `u u'`. Then for every `ε > 0` there is `N` with `‖T (s m) - T (s n)‖ < ε` for all `m, n ≥ N`.
-/
theorem cauchy_of_local_small_of_split_bound {X F : Type*} [NormedAddCommGroup F] (T : X → F)
    (G : X → ℝ)
    (V : ℝ → X → X → ℝ) (W : ℝ → Fin 3 → X → X → ℝ) (s : ℕ → X) (hg : ∀ n, G (s n) ≤ 2)
    (hloc : ∀ R > 0, ∀ δ > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, V R (s m) (s n) < δ ∧ ∀ j,
        W R j (s m) (s n) < δ)
    (hb : ∀ ε > 0, ∃ R > 0, ∃ A : ℝ, 0 ≤ A ∧ ∀ u u' : X,
      ‖T u - T u'‖ ≤ A * (V R u u' + ∑ j : Fin 3, W R j u u') + ε * (G u + G u')) :
    ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, ‖T (s m) - T (s n)‖ < ε := by
  intro ε hε
  obtain ⟨R, hR, A, hA, hbound⟩ := hb (ε / 8) (div_pos hε (by norm_num))
  obtain ⟨N, hN⟩ := hloc R hR (ε / (8 * (A + 1))) (div_pos hε (mul_pos (by norm_num) (by linarith)))
  refine ⟨N, fun m hm n hn ↦ ?_⟩
  obtain ⟨hv, hw⟩ := hN m hm n hn
  exact lt_of_le_mul_add_eighth_mul hε hA hv (sum_fin_three_lt hw) (hg m) (hg n)
      (hbound (s m) (s n))

/-- If a sequence `X : ℕ → ℝ≥0∞` tends to `0` and `K ≠ ⊤`, then `K * X n ^ (1 / 2 : ℝ)` tends to
`0`. -/
theorem ennreal_tendsto_const_mul_rpow_half {X : ℕ → ℝ≥0∞} (hX : Tendsto X atTop (𝓝 0)) {K : ℝ≥0∞}
    (hK : K ≠ ⊤) :
    Tendsto (fun n ↦ K * X n ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n ↦ X n ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
    have := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp hX
    rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at this
  have := ENNReal.Tendsto.const_mul h1 (Or.inr hK)
  rwa [mul_zero] at this

/-- The sequence `((k + 1 : ℕ) : ℝ≥0∞)⁻¹`, indexed by `k : ℕ`, tends to `0` in `ℝ≥0∞`. -/
theorem ennreal_tendsto_inv_nat_succ : Tendsto (fun k : ℕ ↦ (((k + 1 : ℕ) : ℝ≥0∞))⁻¹) atTop
    (nhds 0) :=
  ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)

/-- Two convergent real sequences that agree eventually have the same limit: if `u n → a`, `w n → c`
and `u n = w n` for all large `n`, then `a = c`. -/
theorem eq_of_tendsto_of_eventually_eq {u w : ℕ → ℝ} {a c : ℝ} (hu : Tendsto u atTop (𝓝 a))
    (hw : Tendsto w atTop (𝓝 c)) (h : ∀ᶠ n in atTop, u n = w n) : a = c :=
  tendsto_nhds_unique hu (hw.congr' (h.mono fun _ hn ↦ hn.symm))

/-- A sequence `f : ℕ → ℝ≥0∞` that tends to `0` satisfies `f n ≤ 1` for all large `n`. -/
theorem eventually_le_one_of_tendsto_zero {f : ℕ → ℝ≥0∞} (hf : Tendsto f atTop (𝓝 0)) :
    ∀ᶠ n in atTop, f n ≤ 1 :=
  (tendsto_order.1 hf).2 1 (by norm_num) |>.mono fun _ h ↦ h.le

/-- For reals `α`, `c`, `p`, `ε` with `0 < α`, `0 < p` and `0 < ε`, the inequality
`c * (T ^ (1 / (2 * α))) ^ p < ε` holds for all `T > 0` close enough to `0`, that is, eventually in
`𝓝[>] 0`. The left side tends to `0` as `T → 0` from the right, because real powers with positive
exponent are continuous at `0`. -/
theorem eventually_nhdsGT_zero_mul_rpow_rpow_lt {α c p ε : ℝ} (hα : 0 < α) (hp : 0 < p)
    (hε : 0 < ε) :
    ∀ᶠ T in 𝓝[>] (0 : ℝ), c * (T ^ (1 / (2 * α))) ^ p < ε := by
  have h1 : Tendsto (fun T : ℝ ↦ T ^ (1 / (2 * α))) (𝓝[>] 0) (𝓝 0) := by
    have := (Real.continuousAt_rpow_const 0 (1 / (2 * α)) (Or.inr (by positivity))).tendsto
    rw [Real.zero_rpow (by positivity)] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun T : ℝ ↦ c * (T ^ (1 / (2 * α))) ^ p) (𝓝[>] 0) (𝓝 0) := by
    have := ((Real.continuousAt_rpow_const 0 p (Or.inr hp.le)).tendsto.comp h1).const_mul c
    rwa [Real.zero_rpow hp.ne', mul_zero] at this
  exact h2.eventually (eventually_lt_nhds hε)

/-- For every `ε > 0`, `1 / (n + 1) ≤ ε` holds for all sufficiently large natural numbers `n`. -/
theorem eventually_one_div_add_one_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) ≤ ε :=
  (tendsto_one_div_add_atTop_nhds_zero_nat.eventually (ge_mem_nhds hε))

/-- For `0 < r`, the inequality `(1 : ℝ) / (n + 1) < r` holds for all sufficiently large natural
numbers `n` (eventually along `Filter.atTop`). -/
theorem eventually_one_div_add_one_lt {r : ℝ} (hr : 0 < r) :
    ∀ᶠ n : ℕ in Filter.atTop, (1 : ℝ) / (n + 1) < r := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hr
  refine Filter.eventually_atTop.2 ⟨n, fun m hm ↦ lt_of_le_of_lt ?_ hn⟩
  exact Nat.one_div_le_one_div hm

/-- For reals `a < b`, the numbers `(b - a) / (N + 1)` with `N : ℕ` are positive, satisfy
`a + (N + 1) * ((b - a) / (N + 1)) = b`, and tend to `0` as `N → ∞`. -/
theorem sub_div_succ_pos_and_tendsto_zero {a b : ℝ} (hab : a < b) :
    (∀ N : ℕ, 0 < (b - a) / ((N : ℝ) + 1)) ∧ (∀ N : ℕ, a + ((N + 1 : ℕ) : ℝ) *
        ((b - a) / ((N : ℝ) + 1)) = b) ∧
    Filter.Tendsto (fun N : ℕ ↦ (b - a) / ((N : ℝ) + 1)) Filter.atTop (nhds 0) := by
  refine ⟨fun N ↦ div_pos (sub_pos.2 hab) (by positivity), fun N ↦ ?_, ?_⟩
  · have : (N : ℝ) + 1 ≠ 0 := by positivity
    push_cast; field_simp; ring
  · have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (b - a)
    simpa only [mul_zero, mul_one_div] using this

/-- Let `A a : E →L[ℝ] F` be continuous linear maps of real normed spaces with `‖A a‖ ≤ C`
eventually along a filter `l`. If `A a u₀ → B u₀` and `u a → u₀` along `l`, then `A a (u a) → B u₀`
along `l`. The proof writes `A a (u a) = A a (u a - u₀) + A a u₀` and bounds the first term by
`C * ‖u a - u₀‖`. -/
theorem tendsto_apply_of_norm_le {α E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {l : Filter α} {A : α → E →L[ℝ] F} {B : E →L[ℝ] F}
    {u : α → E} {u₀ : E} {C : ℝ} (hA : Tendsto (fun a ↦ A a u₀) l (𝓝 (B u₀)))
    (hC : ∀ᶠ a in l, ‖A a‖ ≤ C) (hu : Tendsto u l (𝓝 u₀)) :
    Tendsto (fun a ↦ A a (u a)) l (𝓝 (B u₀)) := by
  have h1 : Tendsto (fun a ↦ A a (u a - u₀)) l (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h2 : Tendsto (fun a ↦ C * ‖u a - u₀‖) l (𝓝 0) := by
      simpa using (tendsto_iff_norm_sub_tendsto_zero.1 hu).const_mul C
    refine squeeze_zero' (Eventually.of_forall fun a ↦ norm_nonneg _) ?_ h2
    filter_upwards [hC] with a ha
    exact (A a).le_of_opNorm_le ha _
  have h3 := h1.add hA
  simp only [map_sub, sub_add_cancel, zero_add] at h3
  exact h3

/-- For a family `T : ℝ → E →L[ℝ] E` of continuous linear maps on a real normed space and a vector
`v`, if the difference quotient `t⁻¹ • (T t v - v)` has a limit `v'` as `t → 0` with `t ≠ 0`, then
`T t v → v` as `t → 0` with `t ≠ 0`. The proof writes `T t v = v + t • (t⁻¹ • (T t v - v))` for
`t ≠ 0`. -/
theorem tendsto_apply_of_tendsto_inv_smul_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ℝ → E →L[ℝ] E) (v v' : E)
    (hv : Tendsto (fun t : ℝ ↦ t⁻¹ • (T t v - v)) (𝓝[≠] 0) (𝓝 v')) :
    Tendsto (fun t : ℝ ↦ T t v) (𝓝[≠] 0) (𝓝 v) := by
  have ht : Tendsto (fun t : ℝ ↦ t) (𝓝[≠] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hlim : Tendsto (fun t : ℝ ↦ v + t • (t⁻¹ • (T t v - v))) (𝓝[≠] 0)
      (𝓝 (v + (0 : ℝ) • v')) := tendsto_const_nhds.add (ht.smul hv)
  rw [zero_smul, add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (htne : t ≠ 0)
  rw [smul_smul, mul_inv_cancel₀ htne, one_smul, add_sub_cancel]

/-- For `a > 0` and `b > 0`, the function `s ↦ arctan (√(b / a) * s) / (a * √(b / a))` tends to
`(π / 2) / (a * √(b / a))` as `s → +∞`. -/
theorem tendsto_arctan_sqrt_mul_div_atTop {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun s ↦ arctan (Real.sqrt (b / a) * s) / (a * Real.sqrt (b / a))) atTop
      (𝓝 ((π / 2) / (a * Real.sqrt (b / a)))) := by
  have hc := sqrt_div_pos ha hb
  have ht : Tendsto (fun s ↦ arctan (Real.sqrt (b / a) * s)) atTop (𝓝 (π / 2)) :=
    (tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atTop).comp (tendsto_id.const_mul_atTop hc)
  exact ht.div_const _

/-- In real Hilbert spaces, if `x n` converges weakly to `x₀` (`inner ℝ (x n) y → inner ℝ x₀ y` for
every `y`) and `n ↦ T (x n)` is a Cauchy sequence for a continuous linear map `T : E →L[ℝ] F`, then
`T (x n) → T x₀` in norm. The proof takes the limit `g` of `T (x n)` and shows `g = T x₀` by testing
against every `z` with the adjoint of `T`. -/
theorem tendsto_clm_apply_of_cauchySeq_of_weak {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (T : E →L[ℝ] F) (x : ℕ → E) (x₀ : E)
    (hw : ∀ y, Tendsto (fun n ↦ inner ℝ (x n) y) atTop (𝓝 (inner ℝ x₀ y)))
    (hc : CauchySeq fun n ↦ T (x n)) : Tendsto (fun n ↦ T (x n)) atTop (𝓝 (T x₀)) := by
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete hc
  have hz : ∀ z, inner ℝ g z = inner ℝ (T x₀) z := fun z ↦ by
    have h1 : Tendsto (fun n ↦ inner ℝ (T (x n)) z) atTop (𝓝 (inner ℝ g z)) :=
      hg.inner tendsto_const_nhds
    have h2 : Tendsto (fun n ↦ inner ℝ (T (x n)) z) atTop (𝓝 (inner ℝ (T x₀) z)) := by
      have := hw (ContinuousLinearMap.adjoint T z)
      simpa only [ContinuousLinearMap.adjoint_inner_right] using this
    exact tendsto_nhds_unique h1 h2
  have hgx : g = T x₀ := by
    have h := hz (g - T x₀)
    rw [← sub_eq_zero, ← inner_self_eq_zero (𝕜 := ℝ), inner_sub_left, h, sub_self]
  rw [hgx] at hg
  exact hg

/-- A continuous linear map `L` from a real Hilbert space `E` to `Fin k → ℝ` turns weak convergence
into convergence: if `inner ℝ (x n) y → inner ℝ x₀ y` for every `y : E`, then `L (x n) → L x₀`. The
proof writes each coordinate `a ↦ L a i` as the inner product with a fixed vector, by the Riesz
representation theorem. -/
theorem tendsto_clm_of_weak {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {k : ℕ} (L : E →L[ℝ] (Fin k → ℝ)) (x : ℕ → E) (x₀ : E)
    (hw : ∀ y, Tendsto (fun n ↦ inner ℝ (x n) y) atTop (𝓝 (inner ℝ x₀ y))) :
    Tendsto (fun n ↦ L (x n)) atTop (𝓝 (L x₀)) := by
  rw [tendsto_pi_nhds]
  intro i
  set ℓ : StrongDual ℝ E := (ContinuousLinearMap.proj i).comp L
  set y : E := (InnerProductSpace.toDual ℝ E).symm ℓ
  have hy : ∀ a, L a i = inner ℝ a y := fun a ↦ by
    rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
    rfl
  simp only [hy]
  exact hw y

/-- For every real `a`, the function `ε ↦ a + ε` tends to `a` as `ε → 0`. -/
theorem tendsto_const_add_nhds_zero (a : ℝ) : Filter.Tendsto (fun ε : ℝ ↦ a + ε) (nhds 0) (nhds a)
    := by
  have h := (tendsto_const_nhds (x := a)).add (Filter.tendsto_id (x := nhds (0 : ℝ)))
  rw [add_zero] at h
  exact h

/-- For every real `a`, the function
`t ↦ -(t + a)⁻¹ + a * ((t + a)⁻¹) ^ 2 - a ^ 2 / 3 * ((t + a)⁻¹) ^ 3` tends to `0` as `t → +∞`. -/
theorem tendsto_cubic_inv_add_atTop_nhds_zero {a : ℝ} :
    Tendsto (fun t : ℝ ↦ -(t + a)⁻¹ + a * ((t + a)⁻¹) ^ 2 - a ^ 2 / 3 * ((t + a)⁻¹) ^ 3)
      atTop (𝓝 0) := by
  have hu : Tendsto (fun t : ℝ ↦ (t + a)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ a tendsto_id)
  have hP : Continuous (fun u : ℝ ↦ -u + a * u ^ 2 - a ^ 2 / 3 * u ^ 3) := by fun_prop
  convert (hP.tendsto 0).comp hu using 2 <;> simp

/-- As `r` tends to `0` from the right, `Real.exp (-r)` tends to `1`:
`Tendsto (fun r ↦ Real.exp (-r)) (𝓝[>] 0) (𝓝 1)`. -/
theorem tendsto_exp_neg_nhdsGT_zero : Tendsto (fun r : ℝ ↦ Real.exp (-r)) (𝓝[>] 0) (𝓝 1) := by
  have h : Tendsto (fun r : ℝ ↦ Real.exp (-r)) (𝓝 0) (𝓝 (Real.exp (-0))) :=
    (Real.continuous_exp.comp continuous_neg).tendsto 0
  rw [neg_zero, Real.exp_zero] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- In real Hilbert spaces, let continuous linear maps `T n : E →L[ℝ] F` converge to `T₀` in
operator norm, let `‖x n‖ ≤ B` for all `n`, and let `x n` converge weakly to `x₀`, that is
`inner ℝ (x n) y → inner ℝ x₀ y` for every `y`. Then `inner ℝ (T n (x n)) z → inner ℝ (T₀ x₀) z` for
every `z`. The proof splits `T n (x n) = T₀ (x n) + (T n - T₀) (x n)`, uses the adjoint of `T₀` for
the first term and the bound `‖T n - T₀‖ * B * ‖z‖` for the second. -/
theorem tendsto_inner_clm_apply {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (T : ℕ → E →L[ℝ] F) (T₀ : E →L[ℝ] F) (x : ℕ → E) (x₀ : E) (B : ℝ)
    (hT : Tendsto T atTop (𝓝 T₀)) (hx : ∀ n, ‖x n‖ ≤ B)
    (hw : ∀ y, Tendsto (fun n ↦ inner ℝ (x n) y) atTop (𝓝 (inner ℝ x₀ y))) (z : F) :
    Tendsto (fun n ↦ inner ℝ (T n (x n)) z) atTop (𝓝 (inner ℝ (T₀ x₀) z)) := by
  have h1 : Tendsto (fun n ↦ inner ℝ (T₀ (x n)) z) atTop (𝓝 (inner ℝ (T₀ x₀) z)) := by
    have := hw (ContinuousLinearMap.adjoint T₀ z)
    simpa only [ContinuousLinearMap.adjoint_inner_right] using this
  have h2 : Tendsto (fun n ↦ inner ℝ ((T n - T₀) (x n)) z) atTop (𝓝 0) := by
    have hn : Tendsto (fun n ↦ ‖T n - T₀‖ * B * ‖z‖) atTop (𝓝 0) := by
      have h0 : Tendsto (fun n ↦ ‖T n - T₀‖) atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.1 hT
      simpa using (h0.mul_const B).mul_const ‖z‖
    refine squeeze_zero_norm (fun n ↦ ?_) hn
    calc ‖inner ℝ ((T n - T₀) (x n)) z‖ ≤ ‖(T n - T₀) (x n)‖ * ‖z‖ := norm_inner_le_norm _ _
      _ ≤ ‖T n - T₀‖ * ‖x n‖ * ‖z‖ := by gcongr; exact (T n - T₀).le_opNorm _
      _ ≤ ‖T n - T₀‖ * B * ‖z‖ := by gcongr; exact hx n
  have h3 := h2.add h1
  rw [zero_add] at h3
  refine h3.congr (fun n ↦ ?_)
  rw [show (T n - T₀) (x n) = T n (x n) - T₀ (x n) from rfl, inner_sub_left, sub_add_cancel]

/-- For a decidable proposition `p` and a real sequence `f` with `f n → a`, the sequence
`if p then 0 else f n` tends to `if p then 0 else a`. -/
theorem tendsto_ite_zero {p : Prop} [Decidable p] {f : ℕ → ℝ} {a : ℝ} (hf : Tendsto f atTop (𝓝 a)) :
    Tendsto (fun n ↦ if p then 0 else f n) atTop (𝓝 (if p then 0 else a)) := by
  by_cases hp : p
  · simp only [ite_eq_left hp]
    exact tendsto_const_nhds
  · simp only [ite_eq_right hp]
    exact hf

/-- If `r δ → 0` and `s δ → 0` as `δ` tends to `0` from the right, then for every real `C` the
function `δ ↦ max (r δ) (√(C * (s δ + s δ ^ 2)))` tends to `0` as `δ` tends to `0` from the right.
-/
theorem tendsto_max_sqrt_mul_add_sq_zero {r s : ℝ → ℝ} (C : ℝ) (hr : Tendsto r (𝓝[>] 0) (𝓝 0))
    (hs : Tendsto s (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun δ ↦ max (r δ) (Real.sqrt (C * (s δ + s δ ^ 2)))) (𝓝[>] 0) (𝓝 0) := by
  have h0 : Tendsto (fun δ ↦ C * (s δ + s δ ^ 2)) (𝓝[>] 0) (𝓝 (C * (0 + 0 ^ 2))) :=
    (hs.add (hs.pow 2)).const_mul C
  have hq : Tendsto (fun δ ↦ Real.sqrt (C * (s δ + s δ ^ 2))) (𝓝[>] 0) (𝓝 0) := by
    have := h0.sqrt
    simpa using this
  have := hr.max hq
  simpa using this

/-- For positive `L`, `r` and `s₀`, the function `s ↦ s * r / (s * r + L)` tends to
`𝓝[≥] (s₀ * r / (s₀ * r + L))` along `𝓝[≥] s₀`. The function is continuous at `s₀`, and its values
at `s ≥ s₀` are at least its value at `s₀`. -/
theorem tendsto_mul_div_mul_add_nhdsGE (L r s₀ : ℝ) (hL : 0 < L) (hr : 0 < r) (hs₀ : 0 < s₀) :
    Tendsto (fun s : ℝ ↦ s * r / (s * r + L)) (𝓝[≥] s₀) (𝓝[≥] (s₀ * r / (s₀ * r + L))) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    ((continuousAt_mul_div_mul_add L r s₀ (by positivity)).tendsto.mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : s₀ ≤ s := hs
  change s₀ * r / (s₀ * r + L) ≤ s * r / (s * r + L)
  rw [div_le_div_iff₀ (by positivity) (by nlinarith)]
  nlinarith [mul_nonneg (mul_nonneg hr.le hL.le) (sub_nonneg.2 hs')]

/-- The sequence `ENNReal.ofReal ((((k : ℝ) + 1)⁻¹) ^ 2)`, indexed by `k : ℕ`, tends to `0` in
`ℝ≥0∞`. -/
theorem tendsto_ofReal_inv_add_one_sq :
    Tendsto (fun k : ℕ ↦ ENNReal.ofReal ((((k : ℝ) + 1)⁻¹) ^ 2)) atTop (𝓝 0) := by
  have h0 : Tendsto (fun k : ℕ ↦ 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
  have h : Tendsto (fun k : ℕ ↦ (((k : ℝ) + 1)⁻¹) ^ 2) atTop (𝓝 0) := by
    simpa [one_div] using h0.pow 2
  have h2 := ENNReal.tendsto_ofReal h
  rwa [ENNReal.ofReal_zero] at h2

/-- If a sequence `X : ℕ → ℝ≥0∞` tends to `0`, then for every real `c` the sequence
`ENNReal.ofReal c * X n` tends to `0`. -/
theorem tendsto_ofReal_mul {X : ℕ → ℝ≥0∞} (hX : Tendsto X atTop (𝓝 0)) (c : ℝ) :
    Tendsto (fun n ↦ ENNReal.ofReal c * X n) atTop (𝓝 0) := by
  have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal c) hX (Or.inr ENNReal.ofReal_ne_top)
  rwa [mul_zero] at this

/-- Convergence in `ℝ≥0∞` from two-sided bounds with a free parameter: let `a ≠ ⊤` and `D n → 0`. If
for every real `ε > 0` and every `n` both `A n ≤ ofReal (1 + ε) * a + ofReal (1 + 1 / ε) * D n` and
`a ≤ ofReal (1 + ε) * A n + ofReal (1 + 1 / ε) * D n` hold, then `A n → a`. The proof takes
`ε = 1 / (j + 1)`, shows `a ≤ ofReal (1 + ε) * liminf A` and `limsup A ≤ ofReal (1 + ε) * a`, and
lets `j → ∞`. -/
theorem tendsto_of_eps_bounds {a : ℝ≥0∞} {A D : ℕ → ℝ≥0∞} (ha : a ≠ ⊤)
    (hD : Tendsto D atTop (𝓝 0))
    (hup : ∀ ε : ℝ, 0 < ε → ∀ n, A n ≤ ENNReal.ofReal (1 + ε) * a + ENNReal.ofReal (1 + 1 / ε) *
        D n)
    (hlow : ∀ ε : ℝ, 0 < ε → ∀ n, a ≤ ENNReal.ofReal (1 + ε) * A n + ENNReal.ofReal (1 + 1 / ε) *
        D n) :
    Tendsto A atTop (𝓝 a) := by
  have hε : Tendsto (fun j : ℕ ↦ ENNReal.ofReal (1 + 1 / ((j : ℝ) + 1))) atTop (𝓝 1) := by
    have h : Tendsto (fun j : ℕ ↦ 1 + 1 / ((j : ℝ) + 1)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
    rw [add_zero] at h
    have h2 : Tendsto (fun j : ℕ ↦ ENNReal.ofReal (1 + 1 / ((j : ℝ) + 1))) atTop
        (𝓝 (ENNReal.ofReal 1)) :=
      (ENNReal.continuous_ofReal.tendsto 1).comp h
    rwa [ENNReal.ofReal_one] at h2
  have hpos : ∀ j : ℕ, (0 : ℝ) < 1 / ((j : ℝ) + 1) := fun j ↦ by positivity
  have hcD : ∀ c : ℝ≥0∞, c ≠ ⊤ → Tendsto (fun n ↦ c * D n) atTop (𝓝 0) := fun c hc ↦ by
    simpa using ENNReal.Tendsto.const_mul hD (Or.inr hc)
  refine tendsto_of_le_liminf_of_limsup_le ?_ ?_ (by isBoundedDefault) (by isBoundedDefault)
  · have key : ∀ j : ℕ, a ≤ ENNReal.ofReal (1 + 1 / ((j : ℝ) + 1)) * liminf A atTop := by
      intro j
      have h1 : a ≤ liminf (fun n ↦ ENNReal.ofReal (1 + 1 / ((j : ℝ) + 1)) * A n
          + ENNReal.ofReal (1 + 1 / (1 / ((j : ℝ) + 1))) * D n) atTop :=
        le_liminf_of_le (by isBoundedDefault) (Eventually.of_forall fun n ↦ hlow _ (hpos j) n)
      have e1 : liminf (fun n ↦ ENNReal.ofReal (1 + 1 / ((j : ℝ) + 1)) * A n
          + ENNReal.ofReal (1 + 1 / (1 / ((j : ℝ) + 1))) * D n) atTop
          = liminf (fun n ↦ ENNReal.ofReal (1 + 1 / ((j : ℝ) + 1)) * A n) atTop :=
        ENNReal.liminf_add_of_right_tendsto_zero (hcD _ ENNReal.ofReal_ne_top) _
      rw [e1, ENNReal.liminf_const_mul_of_ne_top ENNReal.ofReal_ne_top] at h1
      exact h1
    have ht := ENNReal.Tendsto.mul_const hε (Or.inl one_ne_zero) (b := liminf A atTop)
    rw [one_mul] at ht
    exact ge_of_tendsto' ht key
  · have key : ∀ j : ℕ, limsup A atTop ≤ ENNReal.ofReal (1 + 1 / ((j : ℝ) + 1)) * a := by
      intro j
      have ht : Tendsto (fun n ↦ ENNReal.ofReal (1 + 1 / ((j : ℝ) + 1)) * a
          + ENNReal.ofReal (1 + 1 / (1 / ((j : ℝ) + 1))) * D n) atTop
          (𝓝 (ENNReal.ofReal (1 + 1 / ((j : ℝ) + 1)) * a)) := by
        simpa using tendsto_const_nhds.add (hcD _ ENNReal.ofReal_ne_top)
      calc limsup A atTop ≤ limsup (fun n ↦ ENNReal.ofReal (1 + 1 / ((j : ℝ) + 1)) * a
            + ENNReal.ofReal (1 + 1 / (1 / ((j : ℝ) + 1))) * D n) atTop :=
            limsup_le_limsup (Eventually.of_forall fun n ↦ hup _ (hpos j) n)
        _ = _ := ht.limsup_eq
    have ht := ENNReal.Tendsto.mul_const hε (Or.inr ha)
    rw [one_mul] at ht
    exact ge_of_tendsto' ht key

/-- Convergence of a real sequence from two-sided bounds with a free parameter: let `0 ≤ b`,
`0 ≤ d n` for all `n`, and `d n → 0`. If for all `n` and all `t > 0` both
`a n ≤ (1 + t) * b + (1 + 1 / t) * d n` and `b ≤ (1 + t) * a n + (1 + 1 / t) * d n` hold, then
`a n → b`. The proof takes `t = √(d n) + 1 / (n + 1)`, which gives
`|a n - b| ≤ t * (3 * b + 2 * d n) + d n + √(d n)`, and squeezes. -/
theorem tendsto_of_eps_bounds_real {a : ℕ → ℝ} {b : ℝ} {d : ℕ → ℝ} (hb : 0 ≤ b) (hd0 : ∀ n, 0 ≤ d n)
    (hd : Tendsto d atTop (nhds 0))
    (h1 : ∀ n t, 0 < t → a n ≤ (1 + t) * b + (1 + 1 / t) * d n)
    (h2 : ∀ n t, 0 < t → b ≤ (1 + t) * a n + (1 + 1 / t) * d n) : Tendsto a atTop (nhds b) := by
  set s : ℕ → ℝ := fun n ↦ Real.sqrt (d n) + 1 / ((n : ℝ) + 1) with hs
  have hs0 : ∀ n, 0 < s n := fun n ↦ by
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have := Real.sqrt_nonneg (d n)
    simp only [hs]
    linarith
  have hsq : Tendsto (fun n ↦ Real.sqrt (d n)) atTop (nhds 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hd
    rw [Real.sqrt_zero] at h
    exact h
  have hsl : Tendsto s atTop (nhds 0) := by
    have h := hsq.add tendsto_one_div_add_atTop_nhds_zero_nat
    rw [add_zero] at h
    exact h
  have hdiv : ∀ n, d n / s n ≤ Real.sqrt (d n) := fun n ↦ by
    rw [div_le_iff₀ (hs0 n)]
    have e : d n = Real.sqrt (d n) * Real.sqrt (d n) := (Real.mul_self_sqrt (hd0 n)).symm
    have hle : Real.sqrt (d n) ≤ s n := by
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      simp only [hs]
      linarith
    calc d n = Real.sqrt (d n) * Real.sqrt (d n) := e
      _ ≤ Real.sqrt (d n) * s n := mul_le_mul_of_nonneg_left hle (Real.sqrt_nonneg _)
  have hbound : ∀ n, |a n - b| ≤ s n * (3 * b + 2 * d n) + d n + Real.sqrt (d n) := by
    intro n
    have k1 := h1 n (s n) (hs0 n)
    have k2 := h2 n (s n) (hs0 n)
    have k3 := h1 n 1 one_pos
    have e : (1 + 1 / s n) * d n = d n + d n / s n := by ring
    rw [e] at k1 k2
    norm_num at k3
    have hq := hdiv n
    have hsn := (hs0 n).le
    have p1 := mul_le_mul_of_nonneg_left k3 hsn
    have p2 := mul_nonneg hsn hb
    have p3 := mul_nonneg hsn (hd0 n)
    rw [abs_le]
    constructor <;> nlinarith
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ (Real.norm_eq_abs _).le.trans (hbound n))
      ?_
  have h := ((hsl.mul ((tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ 3 * b) atTop (nhds (3 * b))).add
    (hd.const_mul 2))).add hd).add hsq
  simp only [zero_mul, add_zero] at h
  exact h

/-- If a sequence `L : ℕ → ℝ≥0∞` tends to `0`, then the real sequence `√(L n).toReal` tends to `0`.
-/
theorem tendsto_sqrt_toReal_zero {L : ℕ → ℝ≥0∞} (h : Filter.Tendsto L Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n ↦ Real.sqrt (L n).toReal) Filter.atTop (nhds 0) := by
  have ht := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  have hq := (Real.continuous_sqrt.tendsto _).comp ht
  simpa only [Function.comp_def, ENNReal.toReal_zero, Real.sqrt_zero] using hq

/-- For sequences `a b : ℕ → ℝ≥0∞` and a constant `c ≠ ⊤`, if `a n ≤ c * b n` for all `n` and
`b n → 0`, then `a n → 0`. -/
theorem tendsto_zero_of_le_const_mul {a b : ℕ → ℝ≥0∞} {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hab : ∀ n, a n ≤ c * b n)
    (hb : Tendsto b atTop (nhds 0)) : Tendsto a atTop (nhds 0) := by
  have h := ENNReal.Tendsto.const_mul hb (Or.inr hc)
  rw [mul_zero] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun n ↦ zero_le) hab

/-- For a real sequence `a` with `0 ≤ a n` for all `n`, if `ENNReal.ofReal (a n)` tends to `0` in
`ℝ≥0∞`, then `a n` tends to `0` in `ℝ`. -/
theorem tendsto_zero_of_ofReal {a : ℕ → ℝ} (ha0 : ∀ n, 0 ≤ a n)
    (h : Tendsto (fun n ↦ ENNReal.ofReal (a n)) atTop (𝓝 0)) : Tendsto a atTop (𝓝 0) := by
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  simp only [Function.comp_def, ENNReal.toReal_ofReal (ha0 _), ENNReal.toReal_zero] at this
  exact this

/-- If `f : ℕ → ℝ` is nonnegative, `k ≠ 0` is a natural number and `f i ^ k → 0` as `i → ∞`, then
`f i → 0`. -/
theorem tendsto_zero_of_pow_tendsto_zero {f : ℕ → ℝ} (hf : ∀ i, 0 ≤ f i) {k : ℕ} (hk : k ≠ 0)
    (h : Tendsto (fun i ↦ f i ^ k) atTop (𝓝 0)) : Tendsto f atTop (𝓝 0) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  have := h.rpow_const (p := (k : ℝ)⁻¹) (Or.inr (inv_nonneg.2 hk'.le))
  rw [Real.zero_rpow (inv_ne_zero hk'.ne')] at this
  exact this.congr fun i ↦ Real.pow_rpow_inv_natCast (hf i) hk

/-- Let `B : E →L[ℝ] E →L[ℝ] E` be a continuous bilinear map on a real normed space,
`T : ℝ → E →L[ℝ] E` a family of continuous linear maps, and `u u' v v' : E` with
`B (T t u) (T t v) = T t (B u v)` for all `t`. If `t⁻¹ • (T t u - u) → u'` and
`t⁻¹ • (T t v - v) → v'` as `t → 0` with `t ≠ 0`, then
`t⁻¹ • (T t (B u v) - B u v) → B u' v + B u v'` in the same sense. Proof idea: the quotient equals
`B (t⁻¹ • (T t u - u)) (T t v) + B u (t⁻¹ • (T t v - v))`, and `T t v → v`. -/
theorem tendsto_inv_smul_sub_bilin_of_covariant {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] E) (T : ℝ → E →L[ℝ] E) (u u' v v' : E)
    (hcov : ∀ t, B (T t u) (T t v) = T t (B u v))
    (hu : Tendsto (fun t : ℝ ↦ t⁻¹ • (T t u - u)) (𝓝[≠] 0) (𝓝 u'))
    (hv : Tendsto (fun t : ℝ ↦ t⁻¹ • (T t v - v)) (𝓝[≠] 0) (𝓝 v')) :
    Tendsto (fun t : ℝ ↦ t⁻¹ • (T t (B u v) - B u v)) (𝓝[≠] 0) (𝓝 (B u' v + B u v')) := by
  have hTv := tendsto_apply_of_tendsto_inv_smul_sub T v v' hv
  have h1 : Tendsto (fun t : ℝ ↦ B (t⁻¹ • (T t u - u)) (T t v)) (𝓝[≠] 0) (𝓝 (B u' v)) :=
    (B.continuous₂.tendsto (u', v)).comp (hu.prodMk_nhds hTv)
  have h2 : Tendsto (fun t : ℝ ↦ B u (t⁻¹ • (T t v - v))) (𝓝[≠] 0) (𝓝 (B u v')) :=
    ((B u).continuous.tendsto v').comp hv
  refine (h1.add h2).congr' (Eventually.of_forall fun t ↦ ?_)
  beta_reduce
  rw [← hcov t]
  simp only [map_sub, map_smul, sub_apply, smul_apply,
    smul_sub]
  abel

/-- Let `N : X → ℝ≥0∞` be finite at `v`, at every `u n` and at every `e n`, with `N (e n) → 0`. If
for all `n` and all real `t > 0` both
`N (u n) ≤ ofReal (1 + t) * N v + ofReal (1 + 1 / t) * N (e n)` and
`N v ≤ ofReal (1 + t) * N (u n) + ofReal (1 + 1 / t) * N (e n)` hold, then
`(N (u n)).toReal → (N v).toReal`. -/
theorem tendsto_toReal_of_eps_bounds {X : Type} {N : X → ℝ≥0∞} {v : X} {u e : ℕ → X}
    (hv : N v ≠ ⊤) (hu : ∀ n, N (u n) ≠ ⊤) (he : ∀ n, N (e n) ≠ ⊤)
    (hlim : Tendsto (fun n ↦ N (e n)) atTop (nhds 0))
    (hs : ∀ n t, 0 < t → N (u n) ≤ ENNReal.ofReal (1 + t) * N v + ENNReal.ofReal (1 + 1 / t) *
        N (e n) ∧
      N v ≤ ENNReal.ofReal (1 + t) * N (u n) + ENNReal.ofReal (1 + 1 / t) * N (e n)) :
    Tendsto (fun n ↦ (N (u n)).toReal) atTop (nhds (N v).toReal) := by
  have hd : Tendsto (fun n ↦ (N (e n)).toReal) atTop (nhds 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
    rw [ENNReal.toReal_zero] at h
    exact h
  exact tendsto_of_eps_bounds_real ENNReal.toReal_nonneg (fun n ↦ ENNReal.toReal_nonneg) hd
    (fun n t ht ↦ toReal_le_mul_toReal_add_mul_toReal hv (he n) ht (hs n t ht).1)
    (fun n t ht ↦ toReal_le_mul_toReal_add_mul_toReal (hu n) (he n) ht (hs n t ht).2)

/-- For every real `δ` and every `w > 0`, `δ / (n + 2) < w` for all sufficiently large natural
numbers `n`. The sequence `δ / (n + 2)` tends to zero. -/
theorem eventually_div_natCast_add_two_lt (δ : ℝ) {w : ℝ} (hw : 0 < w) :
    ∀ᶠ n : ℕ in atTop, δ / ((n : ℝ) + 2) < w := by
  have t : Tendsto (fun n : ℕ ↦ δ / ((n : ℝ) + 2)) atTop (𝓝 0) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat δ).comp (tendsto_add_atTop_nat 2)
    refine this.congr fun n ↦ ?_
    simp only [Function.comp_apply]
    push_cast
    ring
  exact (tendsto_order.1 t).2 w hw

/-- If `u` and `v`, with values in `ℝ≥0∞`, tend to zero along a filter `l` on `ℝ` and
`w t ≤ 2 * u t + 2 * v t` for `t` eventually in `l`, then `w` tends to zero along `l`. The
function `w` lies between zero and `2 * u + 2 * v`, which tends to zero. -/
theorem tendsto_zero_of_le_two_mul_add {l : Filter ℝ} {u v w : ℝ → ℝ≥0∞}
    (hu : Tendsto u l (𝓝 0)) (hv : Tendsto v l (𝓝 0)) (h : ∀ᶠ t in l, w t ≤ 2 * u t + 2 * v t) :
    Tendsto w l (𝓝 0) := by
  have h2 : Tendsto (fun t ↦ 2 * u t + 2 * v t) l (𝓝 0) := by
    have := (ENNReal.Tendsto.const_mul (a := (2 : ℝ≥0∞)) hu (Or.inr (by norm_num))).add
      (ENNReal.Tendsto.const_mul (a := (2 : ℝ≥0∞)) hv (Or.inr (by norm_num)))
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2
      (Eventually.of_forall fun _ ↦ zero_le) h

end PDE.Analysis
