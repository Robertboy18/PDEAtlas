/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.FiniteRankResponse.Discontinuous

/-!
# Spatial derivatives of separated response integrals

Let `G(τ, y) = ∑ₖ φₖ(τ) Hₖ(y)` be a space-time field with finitely many spatial factors `Hₖ`
and scalar time coefficients `φₖ`, the identity holding for `τ ≥ 0` off a countable set of times
and for `y` near a point `x`. Then the response `y ↦ ∫₀ᵗ a(s) G(t - s, y) ds` is the finite
combination `∑ₖ (∫₀ᵗ a(s) φₖ(t - s) ds) Hₖ(y)` near `x`, so its spatial derivatives at `x` are the
response integrals of the spatial derivatives of `G`, and a coefficient bound `|a| ≤ C` on
`[0, t]` gives

`‖∇ⁿ ∫₀ᵗ a(s) G(t - s) ds (x)‖ ≤ C ∫₀^∞ ‖∇ⁿ G(τ)(x)‖ dτ`

at every point where the spatial factors are `Cⁿ`. This is the argument of Chen and Hou behind
the derivative bounds of the finite-rank part and of the residual (Part I (5.89)). For spline
factors that are only `C^{k,1}`, the bound of order `k + 1` holds at the points off the knot
lines.

## Main results

* `IsSeparatedAt n G x`: near `x`, for `τ ≥ 0` off a countable set, `G` is a finite combination
  of spatial factors that are `Cⁿ` at `x`, with time coefficients integrable on bounded intervals.
* `integral_smul_eq_sum_smul`: the response of a separated field is a finite combination.
* `contDiffAt_integral_smul`: the response is `Cⁿ` at `x` when the factors are.
* `iteratedFDeriv_integral_smul`: its `n`-th derivative at `x` is the response of the `n`-th
  derivatives.
* `iteratedFDeriv_integral_smul_apply`, `enorm_iteratedFDeriv_integral_smul_apply_le`: the same
  in fixed directions, `|∇ⁿ ∫₀ᵗ a(s) G(t - s) ds (x)(v)| ≤ C ∫₀^∞ |∇ⁿ G(τ)(x)(v)| dτ`, for partial
  derivatives.
* `enorm_iteratedFDeriv_integral_smul_le`: the bound by `C ∫₀^∞ ‖∇ⁿ G(τ)(x)‖ dτ`, and the forms
  `IsSeparatedAt.contDiffAt_integral_smul`, `IsSeparatedAt.enorm_iteratedFDeriv_integral_smul_le`
  for continuous coefficients.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 5.7, (5.84) and (5.89).
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped Interval Topology ENNReal

namespace PDE.Analysis.Evolution

variable {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace F] {ι : Type*} [Fintype ι]

/-- **A separated response is a finite combination.** If `g(τ) = ∑ₖ φₖ(τ) vₖ` for `τ ≥ 0` off a
countable set of times and every `s ↦ a(s) φₖ(t - s)` is integrable on `[0, t]`, then
`∫₀ᵗ a(s) g(t - s) ds = ∑ₖ (∫₀ᵗ a(s) φₖ(t - s) ds) vₖ`. -/
theorem integral_smul_eq_sum_smul {g : ℝ → F} {φ : ι → ℝ → ℝ} {v : ι → F} {K : Set ℝ}
    (hK : K.Countable) (hg : ∀ τ ∉ K, 0 ≤ τ → g τ = ∑ k, φ k τ • v k) {a : ℝ → ℝ} {t : ℝ}
    (ht : 0 ≤ t) (hint : ∀ k, IntervalIntegrable (fun s ↦ a s * φ k (t - s)) volume 0 t) :
    ∫ s in 0..t, a s • g (t - s) = ∑ k, (∫ s in 0..t, a s * φ k (t - s)) • v k := by
  have hK' : ((fun s ↦ t - s) ⁻¹' K).Countable := hK.preimage sub_right_injective
  have hae : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ι 0 t →
      a s • g (t - s) = ∑ k, (a s * φ k (t - s)) • v k := by
    filter_upwards [hK'.ae_notMem volume] with s hs hst
    rw [uIoc_of_le ht] at hst
    rw [hg _ hs (sub_nonneg.2 hst.2), Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ ↦ smul_smul _ _ _
  rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_finsetSum
    fun k _ ↦ ⟨(hint k).1.smul_const (v k), (hint k).2.smul_const (v k)⟩]
  exact Finset.sum_congr rfl fun k _ ↦ intervalIntegral.integral_smul_const _ _

variable {G : ℝ → X → F} {φ : ι → ℝ → ℝ} {H : ι → X → F} {K : Set ℝ} {U : Set X} {x : X}
  {a : ℝ → ℝ} {t : ℝ}

omit [NormedSpace ℝ X] in
/-- Near `x`, the response of a field separated on a neighbourhood `U` of `x` is the finite
combination of the spatial factors. -/
theorem integral_smul_eventuallyEq (ht : 0 ≤ t) (hK : K.Countable) (hU : U ∈ 𝓝 x)
    (hG : ∀ τ ∉ K, 0 ≤ τ → ∀ y ∈ U, G τ y = ∑ k, φ k τ • H k y)
    (hint : ∀ k, IntervalIntegrable (fun s ↦ a s * φ k (t - s)) volume 0 t) :
    (fun y ↦ ∫ s in 0..t, a s • G (t - s) y) =ᶠ[𝓝 x]
      ∑ k, (∫ s in 0..t, a s * φ k (t - s)) • H k := by
  filter_upwards [hU] with y hy
  rw [integral_smul_eq_sum_smul (g := fun τ ↦ G τ y) hK (fun τ hτ h0 ↦ hG τ hτ h0 y hy) ht hint,
    Finset.sum_apply]
  rfl

/-- The response of a separated field is `Cⁿ` at `x` when the spatial factors are. -/
theorem contDiffAt_integral_smul {n : ℕ} (ht : 0 ≤ t) (hK : K.Countable) (hU : U ∈ 𝓝 x)
    (hG : ∀ τ ∉ K, 0 ≤ τ → ∀ y ∈ U, G τ y = ∑ k, φ k τ • H k y) (hH : ∀ k, ContDiffAt ℝ n (H k) x)
    (hint : ∀ k, IntervalIntegrable (fun s ↦ a s * φ k (t - s)) volume 0 t) :
    ContDiffAt ℝ n (fun y ↦ ∫ s in 0..t, a s • G (t - s) y) x := by
  refine ContDiffAt.congr_of_eventuallyEq ?_ (integral_smul_eventuallyEq ht hK hU hG hint)
  rw [Finset.sum_fn]
  exact ContDiffAt.sum fun k _ ↦ (hH k).const_smul _

omit [CompleteSpace F] in
/-- A separated field has, at `x` and off the exceptional times, the `n`-th derivative
`∑ₖ φₖ(τ) ∇ⁿHₖ(x)`. -/
theorem iteratedFDeriv_eq_sum_smul {n : ℕ} (hU : U ∈ 𝓝 x)
    (hH : ∀ k, ContDiffAt ℝ n (H k) x) {τ : ℝ} (hτ : ∀ y ∈ U, G τ y = ∑ k, φ k τ • H k y) :
    iteratedFDeriv ℝ n (G τ) x = ∑ k, φ k τ • iteratedFDeriv ℝ n (H k) x := by
  have heq : G τ =ᶠ[𝓝 x] ∑ k, φ k τ • H k := by
    filter_upwards [hU] with y hy
    rw [hτ y hy, Finset.sum_apply]
    rfl
  rw [(heq.iteratedFDeriv ℝ n).eq_of_nhds, iteratedFDeriv_sum_apply
    (f := fun k ↦ φ k τ • H k) fun k _ ↦ (hH k).const_smul _]
  exact Finset.sum_congr rfl fun k _ ↦ iteratedFDeriv_const_smul_apply (hH k)

/-- **The derivatives of a separated response** are the responses of the derivatives:
`∇ⁿ(∫₀ᵗ a(s) G(t - s) ds)(x) = ∫₀ᵗ a(s) ∇ⁿG(t - s)(x) ds`. -/
theorem iteratedFDeriv_integral_smul {n : ℕ} (ht : 0 ≤ t) (hK : K.Countable) (hU : U ∈ 𝓝 x)
    (hG : ∀ τ ∉ K, 0 ≤ τ → ∀ y ∈ U, G τ y = ∑ k, φ k τ • H k y) (hH : ∀ k, ContDiffAt ℝ n (H k) x)
    (hint : ∀ k, IntervalIntegrable (fun s ↦ a s * φ k (t - s)) volume 0 t) :
    iteratedFDeriv ℝ n (fun y ↦ ∫ s in 0..t, a s • G (t - s) y) x =
      ∫ s in 0..t, a s • iteratedFDeriv ℝ n (G (t - s)) x := by
  rw [((integral_smul_eventuallyEq ht hK hU hG hint).iteratedFDeriv ℝ n).eq_of_nhds,
    iteratedFDeriv_sum_apply (f := fun k ↦ (∫ s in 0..t, a s * φ k (t - s)) • H k)
      fun k _ ↦ (hH k).const_smul _,
    integral_smul_eq_sum_smul (g := fun τ ↦ iteratedFDeriv ℝ n (G τ) x) hK
      (fun τ hτ h0 ↦ iteratedFDeriv_eq_sum_smul hU hH (hG τ hτ h0)) ht hint]
  exact Finset.sum_congr rfl fun k _ ↦ iteratedFDeriv_const_smul_apply (hH k)

/-- **Part I (5.89) for separated fields.** If `G(τ, y) = ∑ₖ φₖ(τ) Hₖ(y)` for `y` near `x` and
`τ ≥ 0` off a countable set, the factors `Hₖ` are `Cⁿ` at `x`, the products `a(s) φₖ(t - s)` are
integrable on `[0, t]` and `|a| ≤ C` there, then
`‖∇ⁿ(∫₀ᵗ a(s) G(t - s) ds)(x)‖ ≤ C ∫₀^∞ ‖∇ⁿG(τ)(x)‖ dτ`. -/
theorem enorm_iteratedFDeriv_integral_smul_le {n : ℕ} {C : ℝ} (ht : 0 ≤ t)
    (hK : K.Countable) (hU : U ∈ 𝓝 x)
    (hG : ∀ τ ∉ K, 0 ≤ τ → ∀ y ∈ U, G τ y = ∑ k, φ k τ • H k y) (hH : ∀ k, ContDiffAt ℝ n (H k) x)
    (hint : ∀ k, IntervalIntegrable (fun s ↦ a s * φ k (t - s)) volume 0 t)
    (ha : ∀ s ∈ Icc 0 t, |a s| ≤ C) :
    ‖iteratedFDeriv ℝ n (fun y ↦ ∫ s in 0..t, a s • G (t - s) y) x‖ₑ ≤
      ENNReal.ofReal C * ∫⁻ τ in Ioi 0, ‖iteratedFDeriv ℝ n (G τ) x‖ₑ := by
  rw [iteratedFDeriv_integral_smul ht hK hU hG hH hint,
    ← responseIntegral_toSpanSingleton (fun τ ↦ iteratedFDeriv ℝ n (G τ) x)]
  refine (enorm_responseIntegral_le _ ht (C := C) fun s hs ↦ ?_).trans_eq ?_
  · rw [Real.norm_eq_abs]
    exact ha s hs
  · congr 1
    refine lintegral_congr fun τ ↦ ?_
    rw [← ofReal_norm, ← ofReal_norm, ContinuousLinearMap.norm_toSpanSingleton]

/-- **The derivatives of a separated response in fixed directions** are the responses of the
derivatives in those directions: `∇ⁿ(∫₀ᵗ a(s) G(t - s) ds)(x)(v) = ∫₀ᵗ a(s) ∇ⁿG(t - s)(x)(v) ds`.
For `n = 1` and a coordinate vector this is a partial derivative. -/
theorem iteratedFDeriv_integral_smul_apply {n : ℕ} (v : Fin n → X) (ht : 0 ≤ t)
    (hK : K.Countable) (hU : U ∈ 𝓝 x)
    (hG : ∀ τ ∉ K, 0 ≤ τ → ∀ y ∈ U, G τ y = ∑ k, φ k τ • H k y) (hH : ∀ k, ContDiffAt ℝ n (H k) x)
    (hint : ∀ k, IntervalIntegrable (fun s ↦ a s * φ k (t - s)) volume 0 t) :
    iteratedFDeriv ℝ n (fun y ↦ ∫ s in 0..t, a s • G (t - s) y) x v =
      ∫ s in 0..t, a s • iteratedFDeriv ℝ n (G (t - s)) x v := by
  rw [iteratedFDeriv_integral_smul ht hK hU hG hH hint,
    integral_smul_eq_sum_smul (g := fun τ ↦ iteratedFDeriv ℝ n (G τ) x) hK
      (fun τ hτ h0 ↦ iteratedFDeriv_eq_sum_smul hU hH (hG τ hτ h0)) ht hint,
    integral_smul_eq_sum_smul (g := fun τ ↦ iteratedFDeriv ℝ n (G τ) x v)
      (v := fun k ↦ iteratedFDeriv ℝ n (H k) x v) hK
      (fun τ hτ h0 ↦ by
        rw [iteratedFDeriv_eq_sum_smul hU hH (hG τ hτ h0)]
        simp only [sum_apply, smul_apply]) ht
      hint]
  simp only [sum_apply, smul_apply]

/-- **Part I (5.89) in fixed directions.** Under the hypotheses of
`enorm_iteratedFDeriv_integral_smul_le`, for every `v`,
`|∇ⁿ(∫₀ᵗ a(s) G(t - s) ds)(x)(v)| ≤ C ∫₀^∞ |∇ⁿG(τ)(x)(v)| dτ`. -/
theorem enorm_iteratedFDeriv_integral_smul_apply_le {n : ℕ} {C : ℝ} (v : Fin n → X)
    (ht : 0 ≤ t) (hK : K.Countable) (hU : U ∈ 𝓝 x)
    (hG : ∀ τ ∉ K, 0 ≤ τ → ∀ y ∈ U, G τ y = ∑ k, φ k τ • H k y) (hH : ∀ k, ContDiffAt ℝ n (H k) x)
    (hint : ∀ k, IntervalIntegrable (fun s ↦ a s * φ k (t - s)) volume 0 t)
    (ha : ∀ s ∈ Icc 0 t, |a s| ≤ C) :
    ‖iteratedFDeriv ℝ n (fun y ↦ ∫ s in 0..t, a s • G (t - s) y) x v‖ₑ ≤
      ENNReal.ofReal C * ∫⁻ τ in Ioi 0, ‖iteratedFDeriv ℝ n (G τ) x v‖ₑ := by
  rw [iteratedFDeriv_integral_smul_apply v ht hK hU hG hH hint,
    ← responseIntegral_toSpanSingleton (fun τ ↦ iteratedFDeriv ℝ n (G τ) x v)]
  refine (enorm_responseIntegral_le _ ht (C := C) fun s hs ↦ ?_).trans_eq ?_
  · rw [Real.norm_eq_abs]
    exact ha s hs
  · congr 1
    refine lintegral_congr fun τ ↦ ?_
    rw [← ofReal_norm, ← ofReal_norm, ContinuousLinearMap.norm_toSpanSingleton]

/-- `G` is **separated at `x` to order `n`**: there are finitely many spatial factors `Hₖ`, `Cⁿ`
at `x`, and time coefficients `φₖ`, integrable on every `[0, T]`, such that
`G(τ, y) = ∑ₖ φₖ(τ) Hₖ(y)` for `y` near `x` and `τ ≥ 0` off a countable set. Approximate solutions
built from fixed spatial bases with piecewise smooth time coefficients have this form. -/
def IsSeparatedAt (n : ℕ) (G : ℝ → X → F) (x : X) : Prop :=
  ∃ (N : ℕ) (φ : Fin N → ℝ → ℝ) (H : Fin N → X → F) (K : Set ℝ), K.Countable ∧
    (∀ k T, IntegrableOn (φ k) (Icc 0 T)) ∧ (∀ k, ContDiffAt ℝ n (H k) x) ∧
    ∀ᶠ y in 𝓝 x, ∀ τ ∉ K, 0 ≤ τ → G τ y = ∑ k, φ k τ • H k y

omit [CompleteSpace F] in
/-- A field separated to order `n` is separated to every lower order. -/
theorem IsSeparatedAt.of_le {m n : ℕ} (h : IsSeparatedAt n G x) (hmn : m ≤ n) :
    IsSeparatedAt m G x := by
  obtain ⟨N, φ, H, K, hK, hφ, hH, hG⟩ := h
  exact ⟨N, φ, H, K, hK, hφ, fun k ↦ (hH k).of_le (by exact_mod_cast hmn), hG⟩

omit [NormedSpace ℝ X] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] in
/-- A function integrable on `[0, t]`, reflected in time and multiplied by a coefficient
continuous on `[0, t]`, is integrable on `[0, t]`. -/
theorem intervalIntegrable_mul_comp_sub {a g : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hg : IntegrableOn g (Icc 0 t)) (ha : ContinuousOn a (Icc 0 t)) :
    IntervalIntegrable (fun s ↦ a s * g (t - s)) volume 0 t := by
  have h1 : IntervalIntegrable g volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le ht).2 hg
  have h2 := h1.comp_sub_left t
  simp only [sub_self, sub_zero] at h2
  exact h2.symm.continuousOn_mul (by rwa [uIcc_of_le ht])

/-- The response of a field separated at `x` to order `n` is `Cⁿ` at `x`. -/
theorem IsSeparatedAt.contDiffAt_integral_smul {n : ℕ} (h : IsSeparatedAt n G x) (ht : 0 ≤ t)
    (ha : ContinuousOn a (Icc 0 t)) :
    ContDiffAt ℝ n (fun y ↦ ∫ s in 0..t, a s • G (t - s) y) x := by
  obtain ⟨N, φ, H, K, hK, hφ, hH, hG⟩ := h
  exact Evolution.contDiffAt_integral_smul ht hK hG (fun τ hτ h0 y hy ↦ hy τ hτ h0) hH
    fun k ↦ intervalIntegrable_mul_comp_sub ht (hφ k t) ha

/-- **Part I (5.89) for a field separated at `x`.** For a coefficient continuous on `[0, t]` with
`|a| ≤ C` there, `‖∇ⁿ(∫₀ᵗ a(s) G(t - s) ds)(x)‖ ≤ C ∫₀^∞ ‖∇ⁿG(τ)(x)‖ dτ`. -/
theorem IsSeparatedAt.enorm_iteratedFDeriv_integral_smul_le {n : ℕ} {C : ℝ}
    (h : IsSeparatedAt n G x) (ht : 0 ≤ t) (ha : ContinuousOn a (Icc 0 t))
    (hC : ∀ s ∈ Icc 0 t, |a s| ≤ C) :
    ‖iteratedFDeriv ℝ n (fun y ↦ ∫ s in 0..t, a s • G (t - s) y) x‖ₑ ≤
      ENNReal.ofReal C * ∫⁻ τ in Ioi 0, ‖iteratedFDeriv ℝ n (G τ) x‖ₑ := by
  obtain ⟨N, φ, H, K, hK, hφ, hH, hG⟩ := h
  exact Evolution.enorm_iteratedFDeriv_integral_smul_le ht hK hG (fun τ hτ h0 y hy ↦ hy τ hτ h0) hH
    (fun k ↦ intervalIntegrable_mul_comp_sub ht (hφ k t) ha) hC

end PDE.Analysis.Evolution
