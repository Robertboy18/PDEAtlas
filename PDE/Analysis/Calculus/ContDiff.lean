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

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Polynomial
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.Topology.UniformSpace.Uniformizable

set_option linter.style.header false

/-!
# Smoothness of composed functions

The lemmas state `ContDiff`, `ContDiffAt` and `ContDiffOn` for products, compositions, quotients and
coordinates of smooth functions, and bound iterated derivatives. The proofs combine the rules of
Mathlib for `ContDiff`.

## Main results

* `PDE.Analysis.contDiff_one_of_contDiff_infty`: A smooth map `f : E → F` between real normed spaces
  is of class `C^1`: `ContDiff ℝ ∞ f` implies `ContDiff ℝ 1 f`. It is the case `1 ≤ ∞` of
  `ContDiff.of_le`.
* `PDE.Analysis.contDiff_parametric_intervalIntegral`: Let `E` be a finite-dimensional real normed
  space and `F` a real Banach space, both in the same universe, and let `n` be a natural number. If
  `(x, t) ↦ f x t` is of class `C^n` on `E × ℝ`, then for all real `a b` the function
  `x ↦ ∫ t in a..b, f x t` is of class `C^n` on `E`.
* `PDE.Analysis.contDiffAt_of_contDiffOn_Ioi_neg`: If `f : ℝ → ℝ` is `C^3` on `Set.Ioi (-δ)` with
  `0 < δ`, then `f` is `C^3` at every `s ≥ 0`.
* `PDE.Analysis.contDiffAt_two_ofReal_comp`: If `g : E → ℝ` on a real normed space `E` is `C^2` at
  `p`, then its complex-valued coercion `q ↦ (g q : ℂ)` is `C^2` at `p` over `ℝ`.
* `PDE.Analysis.contDiff_and_hasCompactSupport_fderiv_apply`: Let `ψ : ℝ × ℝ → ℝ` be smooth with
  compact support and with `0 < p.1` for every `p` in its topological support, and let `u : ℝ × ℝ`.
  Then the directional derivative `p ↦ fderiv ℝ ψ p u` is smooth, has compact support, and satisfies
  `0 < p.1` for every `p` in its topological support.
* `PDE.Analysis.contDiff_two_ofReal_comp`: If `f : ℝ × ℝ → ℝ` is `C^2`, then its complex-valued
  coercion `u ↦ (f u : ℂ)` is `C^2` over `ℝ`.
* `PDE.Analysis.abs_normed_convolution_le_three_mul`: Let `ρ` be a smooth bump function centred at
  `0` in `ℝ × ℝ` (a `ContDiffBump`) and `g : ℝ × ℝ → ℝ` continuous with `|g x| ≤ A` for all `x`.
  Then the convolution of the normalized bump `ρ.normed volume` with `g` has absolute value at most
  `3 * A` at every point `x`.
* `PDE.Analysis.contDiffAt_ofReal_norm_sq_pow`: For a natural number `k` and a complex number `w0`,
  the map `w ↦ (((‖w‖ ^ 2) ^ k : ℝ) : ℂ)` on `ℂ` is `C^2` at `w0` over `ℝ`.

There are 22 further lemmas of the same kind.

## References

* Levent Alpöge and Tristan Buckmaster, the Lean package of the paper "Finite-time blow-up for the
  Navier–Stokes equations", <https://github.com/tristanbuckmaster/navier-stokes>, folder `lean/`,
  commit `ad53419`: the lemmas of this module and their proofs, adapted to this library. See
  `NOTICE` for attribution and permission.
-/

@[expose] public section

noncomputable section

universe u

open Filter MeasureTheory Topology Set Asymptotics Metric
open scoped ContDiff Convolution

namespace PDE.Analysis

/-- Let `ρ` be a smooth bump function centred at `0` in `ℝ × ℝ` (a `ContDiffBump`) and
`g : ℝ × ℝ → ℝ` continuous with `|g x| ≤ A` for all `x`. Then the convolution of the normalized bump
`ρ.normed volume` with `g` has absolute value at most `3 * A` at every point `x`. The proof bounds
the distance from the convolution at `x` to `g x` by `2 * A`. -/
theorem abs_normed_convolution_le_three_mul (ρ : ContDiffBump (0 : ℝ × ℝ)) {g : ℝ × ℝ → ℝ}
    (hg : Continuous g) {A : ℝ}
    (hA : ∀ x, |g x| ≤ A) (x : ℝ × ℝ) :
    |(ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x| ≤ 3 * A := by
  have h := ρ.dist_normed_convolution_le (μ := volume) (x₀ := x)
      (ε := 2 * A) hg.aestronglyMeasurable
    (fun y _ ↦ by
      rw [Real.dist_eq]
      calc |g y - g x| ≤ |g y| + |g x| := abs_sub _ _
        _ ≤ A + A := add_le_add (hA y) (hA x)
        _ = 2 * A := by ring)
  rw [Real.dist_eq] at h
  calc _ = |((ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x - g x) + g x| := by
         ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ 2 * A + A := add_le_add h (hA x)
    _ = 3 * A := by ring

/-- If `f : ℝ → ℝ` is `C^3` on `Set.Ioi (-δ)` with `0 < δ`, then `f` is `C^3` at every `s ≥ 0`. -/
theorem contDiffAt_of_contDiffOn_Ioi_neg {f : ℝ → ℝ} {δ : ℝ} (hf : ContDiffOn ℝ 3 f (Set.Ioi (-δ)))
    (hδ : 0 < δ) {s : ℝ} (hs : 0 ≤ s) : ContDiffAt ℝ 3 f s :=
  hf.contDiffAt (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr (by linarith)))

/-- If `g : E → ℝ` on a real normed space `E` is `C^2` at `p`, then its complex-valued coercion
`q ↦ (g q : ℂ)` is `C^2` at `p` over `ℝ`. -/
theorem contDiffAt_two_ofReal_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : E → ℝ}
    {p : E}
    (h : ContDiffAt ℝ 2 g p) : ContDiffAt ℝ 2 (fun q ↦ ((g q : ℝ) : ℂ)) p :=
  Complex.ofRealCLM.contDiff.contDiffAt.comp p h

/-- For an integer `M`, a complex number `w ≠ 0` and every `n : WithTop ℕ∞`, the map `v ↦ v ^ M` on
`ℂ` is `C^n` at `w` over the field `ℂ`. -/
theorem contDiffAt_zpow_of_ne_zero {n : WithTop ℕ∞} (M : ℤ) {w : ℂ} (hw : w ≠ 0) :
    ContDiffAt ℂ n (fun v : ℂ ↦ v ^ M) w := by
  cases M with
  | ofNat m => simpa using (contDiffAt_id (x := w)).pow m
  | negSucc m =>
    have h := ((contDiffAt_id (𝕜 := ℂ) (n := n) (x := w)).pow (m + 1)).inv (pow_ne_zero _ hw)
    rw [show (fun v : ℂ ↦ v ^ Int.negSucc m) = fun v ↦ (v ^ (m + 1))⁻¹ from funext fun v ↦
        zpow_negSucc v m]
    exact h

/-- Let `ψ : ℝ × ℝ → ℝ` be smooth with compact support and with `0 < p.1` for every `p` in its
topological support, and let `u : ℝ × ℝ`. Then the directional derivative `p ↦ fderiv ℝ ψ p u` is
smooth, has compact support, and satisfies `0 < p.1` for every `p` in its topological support. -/
theorem contDiff_and_hasCompactSupport_fderiv_apply {ψ : ℝ × ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ)
    (hpos : ∀ p ∈ tsupport ψ, 0 < p.1) (u : ℝ × ℝ) :
    ContDiff ℝ ∞ (fun p ↦ fderiv ℝ ψ p u) ∧ HasCompactSupport (fun p ↦ fderiv ℝ ψ p u) ∧
      ∀ p ∈ tsupport (fun p ↦ fderiv ℝ ψ p u), 0 < p.1 :=
  ⟨(contDiff_infty_iff_fderiv.1 hψ).2.clm_apply contDiff_const, hc.fderiv_apply (𝕜 := ℝ) u,
    fun p hp ↦ hpos p (tsupport_fderiv_apply_subset ℝ u hp)⟩

/-- If `α β : ℝ → ℝ` are smooth with compact support, then `q ↦ α q.1 * β q.2` on `ℝ × ℝ` is smooth,
has compact support, and its topological support is contained in `tsupport α ×ˢ tsupport β`. The
support inclusion comes from the supports of the two factors, and the product of the two compact
supports is compact. -/
theorem contDiff_and_hasCompactSupport_fst_mul_snd {α β : ℝ → ℝ} (hα : ContDiff ℝ ∞ α)
    (hαc : HasCompactSupport α) (hβ : ContDiff ℝ ∞ β)
    (hβc : HasCompactSupport β) :
    ContDiff ℝ ∞ (fun q : ℝ × ℝ ↦ α q.1 * β q.2) ∧ HasCompactSupport
        (fun q : ℝ × ℝ ↦ α q.1 * β q.2) ∧
      tsupport (fun q : ℝ × ℝ ↦ α q.1 * β q.2) ⊆ tsupport α ×ˢ tsupport β := by
  have hsub : tsupport (fun q : ℝ × ℝ ↦ α q.1 * β q.2) ⊆ tsupport α ×ˢ tsupport β := by
    intro p hp
    have h1 : p ∈ tsupport (α ∘ Prod.fst) := tsupport_mul_subset_left hp
    have h2 : p ∈ tsupport (β ∘ Prod.snd) := tsupport_mul_subset_right hp
    exact ⟨tsupport_comp_subset_preimage α continuous_fst h1,
        tsupport_comp_subset_preimage β continuous_snd h2⟩
  exact ⟨(hα.comp contDiff_fst).mul (hβ.comp contDiff_snd),
    IsCompact.of_isClosed_subset (IsCompact.prod hαc hβc) (isClosed_tsupport _) hsub, hsub⟩

/-- Let `k : ℝ → ℝ` be smooth, vanish outside `Set.Ioo p q` and satisfy `∫ x, k x = 0`, and let
`l < p` and `q < r`. Then the primitive `t ↦ ∫ s in l..t, k s` is smooth, has compact support, has
topological support inside `Set.Ioo l r`, and has derivative `k`. The primitive vanishes outside
`Set.Icc p q`: to the left because `k` vanishes there, to the right because the total integral is
`0`. -/
theorem contDiff_and_hasCompactSupport_primitive {k : ℝ → ℝ} {l r p q : ℝ} (hk : ContDiff ℝ ∞ k)
    (hlp : l < p)
    (hqr : q < r) (hks : ∀ x, x ∉ Ioo p q → k x = 0) (hk0 : ∫ x, k x = 0) :
    ContDiff ℝ ∞ (fun t ↦ ∫ s in l..t, k s) ∧ HasCompactSupport (fun t ↦ ∫ s in l..t, k s) ∧
      tsupport (fun t ↦ ∫ s in l..t, k s) ⊆ Ioo l r ∧
      deriv (fun t ↦ ∫ s in l..t, k s) = k := by
  have hkc := hk.continuous
  have hd : ∀ t, HasDerivAt (fun t ↦ ∫ s in l..t, k s) (k t) t := fun t ↦
    intervalIntegral.integral_hasDerivAt_right (hkc.intervalIntegrable _ _)
      hkc.aestronglyMeasurable.stronglyMeasurableAtFilter hkc.continuousAt
  have hder : deriv (fun t ↦ ∫ s in l..t, k s) = k := funext fun t ↦ (hd t).deriv
  have hz : ∀ t, t ∉ Icc p q → ∫ s in l..t, k s = 0 := by
    intro t ht
    rcases le_or_gt t p with htp | htp
    · rw [intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) ?_,
          intervalIntegral.integral_zero]
      intro x hx
      apply hks
      intro hx'
      rcases Set.mem_uIcc.1 hx with ⟨_, h⟩ | ⟨_, h⟩ <;> linarith [hx'.1]
    · have hqt : q < t := by
        by_contra h
        exact ht ⟨htp.le, not_lt.1 h⟩
      rw [intervalIntegral.integral_of_le (by linarith),
        setIntegral_eq_integral_of_forall_compl_eq_zero, hk0]
      intro x hx
      apply hks
      intro hx'
      exact hx ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
  refine ⟨contDiff_infty_iff_deriv.2 ⟨fun t ↦ (hd t).differentiableAt, by rw [hder]; exact hk⟩,
    HasCompactSupport.intro isCompact_Icc hz, ?_, hder⟩
  exact (closure_minimal (Function.support_subset_iff'.2 hz) isClosed_Icc).trans
    (Icc_subset_Ioo hlp hqr)

/-- If `ψ : ℝ × ℝ → ℝ` is smooth, then `p ↦ p.1 * ψ p` is smooth. -/
theorem contDiff_fst_mul {ψ : ℝ × ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) : ContDiff ℝ ∞
    (fun p : ℝ × ℝ ↦ p.1 * ψ p) :=
  contDiff_fst.mul hψ

/-- The coercion `fun t : ℝ ↦ (t : ℂ)` from the real to the complex numbers is `C^∞` as a map of
real normed spaces. -/
theorem contDiff_infty_complex_ofReal : ContDiff ℝ ∞ (fun t : ℝ ↦ (t : ℂ)) :=
    Complex.ofRealCLM.contDiff

/-- Let `P Q : Polynomial ℝ` and a real `a` be such that the derivatives of `P` and `Q` of every
order `o ≤ k` have the same value at `a`. Then the function
`t ↦ if a ≤ t then Q.eval t else P.eval t` is of class `C^k`. The proof is by induction on `k`: the
derivative of the glued function is the gluing of the derivatives of `P` and `Q`. -/
theorem contDiff_ite_eval_of_iterate_derivative_eq (k : ℕ) : ∀ (P Q : Polynomial ℝ) (a : ℝ),
    (∀ o ≤ k, (Polynomial.derivative^[o] P).eval a = (Polynomial.derivative^[o] Q).eval a) →
    ContDiff ℝ k (fun t : ℝ ↦ if a ≤ t then Q.eval t else P.eval t) := by
  induction k with
  | zero =>
    intro P Q a h
    have h0 := h 0 le_rfl
    simp only [Function.iterate_zero, id] at h0
    rw [Nat.cast_zero, contDiff_zero]
    exact Continuous.if_le (Polynomial.contDiff_aeval Q 0).continuous
        (Polynomial.contDiff_aeval P 0).continuous
      continuous_const continuous_id (fun x hx ↦ by
        change a = x at hx
        rw [← hx]; exact h0.symm)
  | succ k ih =>
    intro P Q a h
    have h0 := h 0 (Nat.zero_le _)
    have h1 := h 1 (by omega)
    simp only [Function.iterate_zero, id, Function.iterate_one] at h0 h1
    have hd : ∀ t, HasDerivAt (fun t : ℝ ↦ if a ≤ t then Q.eval t else P.eval t)
        (if a ≤ t then (Polynomial.derivative Q).eval t else (Polynomial.derivative P).eval t) t :=
            by
      intro t
      rcases lt_trichotomy t a with hlt | heq | hgt
      · have hev : (fun t : ℝ ↦ if a ≤ t then Q.eval t else P.eval t) =ᶠ[nhds t]
            fun t ↦ P.eval t := by
          filter_upwards [Iio_mem_nhds hlt] with y hy
          rw [ite_eq_right (not_le.mpr hy)]
        rw [ite_eq_right (not_le.mpr hlt)]
        exact (P.hasDerivAt t).congr_of_eventuallyEq hev
      · rw [heq, ite_eq_left le_rfl]
        have hQ : HasDerivWithinAt (fun t : ℝ ↦ if a ≤ t then Q.eval t else P.eval t)
            ((Polynomial.derivative Q).eval a) (Set.Ici a) a :=
          (Q.hasDerivAt a).hasDerivWithinAt.congr_of_mem (fun y hy ↦ ite_eq_left hy)
              (Set.mem_Ici.mpr le_rfl)
        have hP : HasDerivWithinAt (fun t : ℝ ↦ if a ≤ t then Q.eval t else P.eval t)
            ((Polynomial.derivative Q).eval a) (Set.Iic a) a := by
          rw [← h1]
          refine (P.hasDerivAt a).hasDerivWithinAt.congr_of_mem (fun y hy ↦ ?_)
              (Set.mem_Iic.mpr le_rfl)
          by_cases hay : a ≤ y
          · rw [ite_eq_left hay, le_antisymm hy hay, h0]
          · rw [ite_eq_right hay]
        have hu := hP.union hQ
        rwa [Set.Iic_union_Ici, hasDerivWithinAt_univ] at hu
      · have hev : (fun t : ℝ ↦ if a ≤ t then Q.eval t else P.eval t) =ᶠ[nhds t]
            fun t ↦ Q.eval t := by
          filter_upwards [Ioi_mem_nhds hgt] with y hy
          rw [ite_eq_left (le_of_lt hy)]
        rw [ite_eq_left (le_of_lt hgt)]
        exact (Q.hasDerivAt t).congr_of_eventuallyEq hev
    have hderiv : deriv (fun t : ℝ ↦ if a ≤ t then Q.eval t else P.eval t) =
        fun t ↦ if a ≤ t then (Polynomial.derivative Q).eval t else
            (Polynomial.derivative P).eval t :=
      funext fun t ↦ (hd t).deriv
    rw [show ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 by
      push_cast; rfl, contDiff_succ_iff_deriv]
    refine ⟨fun t ↦ (hd t).differentiableAt, fun hk ↦ absurd hk (by simp), ?_⟩
    rw [hderiv]
    refine ih _ _ a (fun o ho ↦ ?_)
    have := h (o + 1) (by omega)
    simpa only [Function.iterate_succ_apply] using this

/-- If `g : ℝ → ℝ` is `C^n` for some `n : WithTop ℕ∞`, then its complex-valued coercion
`t ↦ (g t : ℂ)` is `C^n` over `ℝ`. -/
theorem contDiff_ofReal_comp {n : ℕ∞ω} {g : ℝ → ℝ} (hg : ContDiff ℝ n g) : ContDiff ℝ n
    (fun t ↦ (g t : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp hg

/-- Let `E` be a finite-dimensional real normed space, `F` a real normed space, and `f : E → F` a
map that is `C^n` on the complement of `0` with `f 0 = 0`. If for every `a ≤ n` there is `C` with
`‖iteratedFDeriv ℝ a f x‖ ≤ C * ‖x‖ ^ (n + 1 - a)` for all `x ≠ 0`, then `f` is `C^n` on the whole
space. The proof is by induction on `n`: the bound of order `0` shows that `f` is differentiable at
`0` with derivative `0`, and the induction hypothesis applies to `fderiv ℝ f`. -/
theorem contDiff_of_iteratedFDeriv_le_norm_pow {E : Type u} {F : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (n : ℕ) :
    ∀ (f : E → F), ContDiffOn ℝ n f {0}ᶜ → f 0 =
      0 → (∀ a ≤ n, ∃ C : ℝ, ∀ x ≠ 0, ‖iteratedFDeriv ℝ a f x‖ ≤ C *
      ‖x‖ ^ (n + 1 - a)) → ContDiff ℝ n f := by
  induction n generalizing F with
  | zero =>
    intro f hf h0 hb
    rw [Nat.cast_zero, contDiff_zero]
    obtain ⟨C, hC⟩ := hb 0 le_rfl
    refine continuous_iff_continuousAt.2 fun x ↦ ?_
    by_cases hx : x = 0
    · subst hx
      have hle : ∀ y : E, ‖f y‖ ≤ |C| * ‖y‖ := by
        intro y
        by_cases hy : y = 0
        · subst hy; simp [h0]
        · have := hC y hy
          rw [norm_iteratedFDeriv_zero] at this
          calc ‖f y‖ ≤ C * ‖y‖ ^ 1 := this
            _ ≤ |C| * ‖y‖ := by
              rw [pow_one]; exact mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg y)
      have ht : Tendsto (fun y : E ↦ |C| * ‖y‖) (𝓝 0) (𝓝 0) := by
        have := (tendsto_const_nhds (x := |C|)).mul (continuous_norm.tendsto' (0 : E) 0 norm_zero)
        rwa [mul_zero] at this
      rw [ContinuousAt, h0]
      exact squeeze_zero_norm hle ht
    · exact hf.continuousOn.continuousAt (isOpen_compl_singleton.mem_nhds hx)
  | succ n ih =>
    intro f hf h0 hb
    obtain ⟨C, hC⟩ := hb 0 (Nat.zero_le _)
    have hO : f =O[𝓝 0] fun x : E ↦ ‖x‖ ^ (n + 2) := by
      refine IsBigO.of_bound |C| (Eventually.of_forall fun y ↦ ?_)
      by_cases hy : y = 0
      · subst hy; simp [h0]
      · have := hC y hy
        rw [norm_iteratedFDeriv_zero] at this
        rw [norm_pow, norm_norm]
        calc ‖f y‖ ≤ C * ‖y‖ ^ (n + 1 + 1 - 0) := this
          _ ≤ |C| * ‖y‖ ^ (n + 2) := by
            rw [Nat.sub_zero]
            exact mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    have hlo : f =o[𝓝 0] fun x : E ↦ x := hO.trans_isLittleO (isLittleO_norm_pow_id (by omega))
    have hfd : HasFDerivAt f (0 : E →L[ℝ] F) 0 := by
      rw [hasFDerivAt_iff_isLittleO_nhds_zero]
      simpa [h0] using hlo
    have hdiff : Differentiable ℝ f := by
      intro x
      by_cases hx : x = 0
      · subst hx; exact hfd.differentiableAt
      · exact (hf.differentiableOn (by simp)).differentiableAt (isOpen_compl_singleton.mem_nhds hx)
    have hf' : ContDiffOn ℝ n (fderiv ℝ f) {0}ᶜ :=
      hf.fderiv_of_isOpen isOpen_compl_singleton (by push_cast; exact le_rfl)
    have hd : ContDiff ℝ n (fderiv ℝ f) := by
      refine ih (fderiv ℝ f) hf' hfd.fderiv fun a ha ↦ ?_
      obtain ⟨C', hC'⟩ := hb (a + 1) (by omega)
      refine ⟨C', fun x hx ↦ ?_⟩
      rw [norm_iteratedFDeriv_fderiv]
      have := hC' x hx
      have he : n + 1 + 1 - (a + 1) = n + 1 - a := by omega
      rwa [he] at this
    rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
    exact ⟨hdiff, by simp, hd⟩

/-- If `f : ℝ × ℝ → ℝ` is `C^1`, then its complex-valued coercion `p ↦ (f p : ℂ)` is `C^1` over `ℝ`.
-/
theorem contDiff_one_ofReal_comp {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f) : ContDiff ℝ 1
    (fun p ↦ (f p : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp hf

/-- A smooth map `f : E → F` between real normed spaces is of class `C^1`: `ContDiff ℝ ∞ f` implies
`ContDiff ℝ 1 f`. It is the case `1 ≤ ∞` of `ContDiff.of_le`. -/
theorem contDiff_one_of_contDiff_infty {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → F} (h : ContDiff ℝ ∞ f) : ContDiff ℝ 1 f := by
  simpa using contDiff_infty.1 h 1

/-- Let `H` be a real normed space that is a proper metric space and let `h : H × ℝ → ℂ` be of class
`C¹`. Then for all real `a b` the function `p ↦ ∫ s in a..b, h (p, s)` is of class `C¹` on `H`. The
proof differentiates under the integral sign, bounding the partial derivative in `p` on the compact
set `closedBall p₀ 1 ×ˢ uIcc a b`. -/
theorem contDiff_one_parametric_intervalIntegral {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] [ProperSpace H] (h : H × ℝ → ℂ) (hh : ContDiff ℝ 1 h) (a b : ℝ) :
    ContDiff ℝ 1 (fun p : H ↦ ∫ s in a..b, h (p, s)) := by
  have hcont : Continuous h := hh.continuous
  have hdcont : Continuous (fderiv ℝ h) := hh.continuous_fderiv one_ne_zero
  have hdiff : Differentiable ℝ h := hh.differentiable one_ne_zero
  let D : H → ℝ → H →L[ℝ] ℂ := fun p s ↦ (fderiv ℝ h (p, s)).comp (ContinuousLinearMap.inl ℝ H ℝ)
  have hDcont : Continuous (Function.uncurry D) :=
    ((ContinuousLinearMap.compL ℝ H (H × ℝ) ℂ).flip (ContinuousLinearMap.inl ℝ H ℝ)).continuous.comp
      hdcont
  have hsec : ∀ p : H, Continuous (fun s : ℝ ↦ h (p, s)) := fun p ↦
    hcont.comp (Continuous.prodMk continuous_const continuous_id)
  rw [contDiff_one_iff_hasFDerivAt]
  refine ⟨fun p ↦ ∫ s in a..b, D p s, ?_, fun p₀ ↦ ?_⟩
  · exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hDcont a b
  · obtain ⟨C, hC⟩ : ∃ C, ∀ q ∈ closedBall p₀ 1 ×ˢ uIcc a b, ‖Function.uncurry D q‖ ≤ C :=
      ((isCompact_closedBall p₀ 1).prod isCompact_uIcc).exists_bound_of_continuousOn
        hDcont.continuousOn
    refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ ↦ C)
      (F' := D) (closedBall_mem_nhds p₀ one_pos) ?_ ?_ ?_ ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun p ↦ (hsec p).aestronglyMeasurable
    · exact (hsec p₀).intervalIntegrable _ _
    · exact (hDcont.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun t ht p hp ↦ hC (p, t) ⟨hp, uIoc_subset_uIcc ht⟩
    · exact intervalIntegrable_const
    · exact Filter.Eventually.of_forall fun t _ p _ ↦
        (hdiff (p, t)).hasFDerivAt.comp p (hasFDerivAt_prodMk_left p t)

/-- Let `E` be a finite-dimensional real normed space and `F` a real Banach space, both in the same
universe, and let `n` be a natural number. If `(x, t) ↦ f x t` is of class `C^n` on `E × ℝ`, then
for all real `a b` the function `x ↦ ∫ t in a..b, f x t` is of class `C^n` on `E`. The proof is an
induction on `n` for all `F` at once: by differentiation under the integral sign, the derivative in
`x` is the integral of the partial derivative, which is of class `C^n` by the induction hypothesis.
-/
theorem contDiff_parametric_intervalIntegral {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (a b : ℝ) (n : ℕ) :
    ∀ (f : E → ℝ → F), ContDiff ℝ n (fun p : E × ℝ ↦ f p.1 p.2) →
      ContDiff ℝ n (fun x ↦ ∫ t in a..b, f x t) := by
  induction n generalizing F with
  | zero =>
    intro f hf
    simp only [CharP.cast_eq_zero, contDiff_zero] at hf ⊢
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hf a b
  | succ n ih =>
    intro f hf
    set g : E × ℝ → F := fun p ↦ f p.1 p.2 with hg
    have hd : Differentiable ℝ g := hf.differentiable (by simp)
    set f' : E → ℝ → (E →L[ℝ] F) := fun x t ↦ (fderiv ℝ g (x, t)).comp
        (ContinuousLinearMap.inl ℝ E ℝ)
      with hf'
    have hf'c : ContDiff ℝ n (fun p : E × ℝ ↦ f' p.1 p.2) := by
      have h1 : ContDiff ℝ n (fderiv ℝ g) := hf.fderiv_right (by push_cast; exact le_rfl)
      exact h1.clm_comp contDiff_const
    have hder : ∀ x t, HasFDerivAt (fun x ↦ f x t) (f' x t) x := by
      intro x t
      have h := (hd (x, t)).hasFDerivAt.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x t)
      exact h
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by push_cast; rfl]
    rw [contDiff_succ_iff_hasFDerivAt]
    refine ⟨fun x ↦ ∫ t in a..b, f' x t, ih f' hf'c, fun x₀ ↦ ?_⟩
    have hcont : Continuous (fun p : E × ℝ ↦ f' p.1 p.2) := hf'c.continuous
    have hK : IsCompact (Metric.closedBall x₀ 1 ×ˢ Set.uIcc a b) :=
      (isCompact_closedBall x₀ 1).prod isCompact_uIcc
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
    have hgc : Continuous g := hf.continuous
    refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ ↦ C)
      (Metric.closedBall_mem_nhds x₀ one_pos) ?_ ?_ ?_ ?_ intervalIntegrable_const ?_
    · exact Filter.Eventually.of_forall (fun x ↦
        (hgc.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable)
    · exact (hgc.comp (Continuous.prodMk continuous_const continuous_id)).intervalIntegrable a b
    · exact (hcont.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun t ht x hx ↦ hC (x, t) ⟨hx, ?_⟩)
      exact Set.uIoc_subset_uIcc ht
    · exact Filter.Eventually.of_forall (fun t _ x _ ↦ hder x t)

/-- Let `E` and `F` be real normed spaces in the same universe with `F` complete, and let `e : E`,
`a b : ℝ` and `n : ℕ`. If `Φ : E → F` is `n` times continuously differentiable and has compact
support, then `x ↦ ∫ t in a..b, Φ (x - t • e)` is `n` times continuously differentiable. The proof
is by induction on `n`, differentiating under the integral sign with the bounded derivative of `Φ`.
-/
theorem contDiff_shift_integral {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (e : E) (a b : ℝ) (n : ℕ) :
    ∀ {Φ : E → F}, ContDiff ℝ n Φ → HasCompactSupport Φ →
      ContDiff ℝ n (fun x ↦ ∫ t in a..b, Φ (x - t • e)) := by
  induction n generalizing F with
  | zero =>
    intro Φ hΦ _
    rw [Nat.cast_zero, contDiff_zero] at hΦ ⊢
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun x t ↦ Φ (x - t • e))
      (hΦ.comp (continuous_fst.sub (continuous_snd.smul continuous_const))) a b
  | succ n ih =>
    intro Φ hΦ hc
    have hΦ' : ContDiff ℝ (n + 1) Φ := by exact_mod_cast hΦ
    have hd : ContDiff ℝ n (fderiv ℝ Φ) := hΦ'.fderiv_right le_rfl
    have hdc : Continuous (fderiv ℝ Φ) := hΦ'.continuous_fderiv (by simp)
    have hdiff : Differentiable ℝ Φ := hΦ'.differentiable (by simp)
    obtain ⟨C, hC⟩ := hdc.bounded_above_of_compact_support (hc.fderiv (𝕜 := ℝ))
    have key := ih (F := E →L[ℝ] F) hd (hc.fderiv (𝕜 := ℝ))
    have hF : ∀ x₀ : E, HasFDerivAt (fun x ↦ ∫ t in a..b, Φ (x - t • e))
        (∫ t in a..b, fderiv ℝ Φ (x₀ - t • e)) x₀ := by
      intro x₀
      refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
        (F := fun x t ↦ Φ (x - t • e)) (F' := fun x t ↦ fderiv ℝ Φ (x - t • e))
        (bound := fun _ ↦ C) (s := univ) univ_mem ?_ ?_ ?_ ?_ intervalIntegrable_const ?_
      · exact Eventually.of_forall fun x ↦
          (hΦ'.continuous.comp (continuous_const.sub (continuous_id.smul
              continuous_const))).aestronglyMeasurable
      · exact (hΦ'.continuous.comp (continuous_const.sub
            (continuous_id.smul continuous_const))).intervalIntegrable _ _
      · exact (hdc.comp (continuous_const.sub (continuous_id.smul
            continuous_const))).aestronglyMeasurable
      · exact Eventually.of_forall fun t _ x _ ↦ hC _
      · refine Eventually.of_forall fun t _ x _ ↦ ?_
        have h1 := (hdiff (x - t • e)).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const (t • e))
        simp only [ContinuousLinearMap.comp_id] at h1
        exact h1
    have hres : ContDiff ℝ (n + 1) (fun x ↦ ∫ t in a..b, Φ (x - t • e)) :=
      contDiff_succ_iff_hasFDerivAt.2 ⟨_, key, hF⟩
    exact_mod_cast hres

/-- If `f : ℝ × ℝ → ℝ` is `C^2`, then its complex-valued coercion `u ↦ (f u : ℂ)` is `C^2` over `ℝ`.
-/
theorem contDiff_two_ofReal_comp {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f) : ContDiff ℝ 2
    (fun u ↦ (f u : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp hf

/-- If `f g : ℝ → ℝ` are `C^3` at `s` and `n ≤ 3`, then for every real `a`,
`iteratedDeriv n (fun t ↦ f t + a * g t) s = iteratedDeriv n f s + a * iteratedDeriv n g s`. -/
theorem iteratedDeriv_add_const_mul_of_le_three {f g : ℝ → ℝ} {s : ℝ} (a : ℝ) (n : ℕ) (hn : n ≤ 3)
    (hf : ContDiffAt ℝ 3 f s) (hg : ContDiffAt ℝ 3 g s) :
    iteratedDeriv n (fun t ↦ f t + a * g t) s = iteratedDeriv n f s + a * iteratedDeriv n g s := by
  have hle : ((n : ℕ) : WithTop ℕ∞) ≤ 3 := by exact_mod_cast hn
  have hf' : ContDiffAt ℝ n f s := hf.of_le hle
  have hg' : ContDiffAt ℝ n (fun t ↦ a * g t) s := contDiffAt_const.mul (hg.of_le hle)
  rw [iteratedDeriv_fun_add hf' hg', iteratedDeriv_const_mul_field]

/-- Over the real numbers, `minSmoothness ℝ 2 ≤ ∞`, where `∞` is the smoothness order of infinitely
differentiable functions in `WithTop ℕ∞`. It holds because `minSmoothness ℝ 2 = 2`. -/
theorem minSmoothness_real_two_le_infty : minSmoothness ℝ 2 ≤ ∞ := by
  simp only [minSmoothness_of_isRCLikeNormedField]
  exact WithTop.coe_le_coe.2 le_top

/-- For real `s` and `u` and `i : ℕ`, the `i`-th iterated Fréchet derivative of
`u ↦ Real.exp (-s * u)` at `u` has norm `|s| ^ i * Real.exp (-s * u)`. -/
theorem norm_iteratedFDeriv_exp_mul (s : ℝ) (i : ℕ) (u : ℝ) :
    ‖iteratedFDeriv ℝ i (fun u : ℝ ↦ Real.exp (-s * u)) u‖ = |s| ^ i * Real.exp (-s * u) := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_exp_const_mul, norm_mul, norm_pow,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_neg, abs_of_pos (Real.exp_pos _)]

/-- Let `E` be a finite-dimensional real normed space, `F` a real normed space, and let `f : E → F`
be `C^a` on the complement of `0` and positively homogeneous of degree `d ≥ a`, that is
`f (t • x) = t ^ d • f x` for all `t > 0` and all `x`. Then there is `C` with
`‖iteratedFDeriv ℝ a f x‖ ≤ C * ‖x‖ ^ (d - a)` for all `x ≠ 0`. The derivative is bounded on the
unit sphere by compactness, and homogeneity transports the bound to every `x ≠ 0` by rescaling. -/
theorem norm_iteratedFDeriv_le_of_homogeneous {E : Type u} {F : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (d a : ℕ)
    (ha : a ≤ d) (f : E → F)
    (hf : ContDiffOn ℝ a f {0}ᶜ) (hhom : ∀ t : ℝ, 0 < t → ∀ x, f (t • x) = t ^ d • f x) :
    ∃ C : ℝ, ∀ x ≠ 0, ‖iteratedFDeriv ℝ a f x‖ ≤ C * ‖x‖ ^ (d - a) := by
  have hopen : IsOpen ({0}ᶜ : Set E) := isOpen_compl_singleton
  have hcont : ContinuousOn (iteratedFDeriv ℝ a f) {0}ᶜ := by
    have h1 := hf.continuousOn_iteratedFDerivWithin le_rfl hopen.uniqueDiffOn
    exact h1.congr fun x hx ↦ (iteratedFDerivWithin_of_isOpen a hopen hx).symm
  have hsph : Metric.sphere (0 : E) 1 ⊆ {0}ᶜ := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    rw [h, mem_sphere_zero_iff_norm, norm_zero] at hx
    exact zero_ne_one hx
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : E) 1).exists_bound_of_continuousOn (hcont.mono hsph)
  refine ⟨M, fun x hx ↦ ?_⟩
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
  set t : ℝ := ‖x‖⁻¹ with ht_def
  have ht : 0 < t := inv_pos.2 hxn
  let e : E ≃L[ℝ] E := (LinearEquiv.smulOfNeZero ℝ E t ht.ne').toContinuousLinearEquiv
  have he : ∀ z, e z = t • z := fun z ↦ rfl
  have hfe : f ∘ e = t ^ d • f := by
    funext z
    simp only [Function.comp_apply, he, Pi.smul_apply]
    exact hhom t ht z
  have hcomp : iteratedFDeriv ℝ a (f ∘ e) x =
      (iteratedFDeriv ℝ a f (e x)).compContinuousLinearMap fun _ ↦ (e : E →L[ℝ] E) := by
    have := e.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (Set.mem_univ (e x)) a
    simpa [iteratedFDerivWithin_univ] using this
  have hxa : ContDiffAt ℝ a f x := hf.contDiffAt (hopen.mem_nhds hx)
  have hsm : iteratedFDeriv ℝ a (t ^ d • f) x = t ^ d • iteratedFDeriv ℝ a f x :=
    iteratedFDeriv_const_smul_apply hxa
  have hex : e x ∈ Metric.sphere (0 : E) 1 := by
    rw [mem_sphere_zero_iff_norm, he, norm_smul, Real.norm_eq_abs, abs_of_pos ht, ht_def,
      inv_mul_cancel₀ hxn.ne']
  have hnorm_e : ‖(e : E →L[ℝ] E)‖ ≤ t := by
    refine ContinuousLinearMap.opNorm_le_bound _ ht.le fun z ↦ ?_
    rw [ContinuousLinearEquiv.coe_coe, he, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  have key : t ^ d * ‖iteratedFDeriv ℝ a f x‖ ≤ M * t ^ a := by
    have h2 : ‖iteratedFDeriv ℝ a (f ∘ e) x‖ ≤ M * t ^ a := by
      rw [hcomp]
      refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      have hM' := hM (e x) hex
      have hM0 : 0 ≤ M := (norm_nonneg _).trans hM'
      exact mul_le_mul hM' (pow_le_pow_left₀ (norm_nonneg _) hnorm_e a) (by positivity) hM0
    rw [hfe, hsm, norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos ht d)] at h2
    exact h2
  have hsplit : ‖x‖ ^ d = ‖x‖ ^ (d - a) * ‖x‖ ^ a := by
    rw [← pow_add, Nat.sub_add_cancel ha]
  have htx : ‖x‖ * t = 1 := by rw [ht_def, mul_inv_cancel₀ hxn.ne']
  calc ‖iteratedFDeriv ℝ a f x‖ = ‖x‖ ^ d * (t ^ d * ‖iteratedFDeriv ℝ a f x‖) := by
        rw [← mul_assoc, ← mul_pow, htx, one_pow, one_mul]
    _ ≤ ‖x‖ ^ d * (M * t ^ a) := mul_le_mul_of_nonneg_left key (by positivity)
    _ = M * ‖x‖ ^ (d - a) * (‖x‖ * t) ^ a := by rw [hsplit, mul_pow]; ring
    _ = M * ‖x‖ ^ (d - a) := by rw [htx, one_pow, mul_one]

/-- Let `g : V → E` be `C^(m+1)` between real normed spaces with
`‖iteratedFDeriv ℝ (m + 1) g y‖ ≤ A` for all `y`. Then the `m`-th iterated derivative is Lipschitz
with constant `A`: `‖iteratedFDeriv ℝ m g y - iteratedFDeriv ℝ m g x‖ ≤ A * ‖y - x‖` for all `x` and
`y`. -/
theorem norm_iteratedFDeriv_sub_le_of_succ_le {V : Type*} {E : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] {g : V → E} {m : ℕ}
    (hg : ContDiff ℝ (m + 1 : ℕ) g) {A : ℝ}
    (hA : ∀ y, ‖iteratedFDeriv ℝ (m + 1) g y‖ ≤ A) (x y : V) :
    ‖iteratedFDeriv ℝ m g y - iteratedFDeriv ℝ m g x‖ ≤ A * ‖y - x‖ := by
  refine convex_univ.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (fun z _ ↦ ?_) (fun z _ ↦ ?_)
    (mem_univ x) (mem_univ y)
  · exact hg.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self m) z
  · rw [norm_fderiv_iteratedFDeriv]; exact hA z

/-- For a natural number `k` and a complex number `w0`, the map `w ↦ (((‖w‖ ^ 2) ^ k : ℝ) : ℂ)` on
`ℂ` is `C^2` at `w0` over `ℝ`. -/
theorem contDiffAt_ofReal_norm_sq_pow (k : ℕ) (w0 : ℂ) :
    ContDiffAt ℝ 2 (fun w : ℂ ↦ (((‖w‖ ^ 2) ^ k : ℝ) : ℂ)) w0 :=
  contDiffAt_two_ofReal_comp (((contDiff_norm_sq ℝ).contDiffAt).pow k)

/-- Let `E` be a finite-dimensional real normed space, `F` a real normed space, and let `f : E → F`
be `C^n` on the complement of `0`, with `f 0 = 0`, and positively homogeneous of degree `n + 1`,
that is `f (t • x) = t ^ (n + 1) • f x` for all `t > 0` and all `x`. Then `f` is `C^n` on the whole
space. -/
theorem contDiff_of_homogeneous {E : Type u} {F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (n : ℕ) (f : E → F)
    (hf : ContDiffOn ℝ n f {0}ᶜ) (h0 : f 0 = 0)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, f (t • x) = t ^ (n + 1) • f x) : ContDiff ℝ n f := by
  refine contDiff_of_iteratedFDeriv_le_norm_pow n f hf h0 fun a ha ↦ ?_
  exact norm_iteratedFDeriv_le_of_homogeneous (n + 1) a (by omega) f
    (hf.of_le (by exact_mod_cast ha)) hhom

/-- Bound for the `n`-th derivative by the function and the `(n+1)`-th derivative: if `g : V → E` is
`C^(n+1)` between real normed spaces, `‖g y‖ ≤ B` and `‖iteratedFDeriv ℝ (n + 1) g y‖ ≤ A` for all
`y`, then `‖iteratedFDeriv ℝ n g x‖ ≤ 2 ^ n * B + n * A` for all `x`. The proof is by induction on
`n`, applying the induction hypothesis to the difference `y ↦ g (y + v) - g y` for a unit vector `v`
and using a first-order Taylor bound for the `n`-th derivative. -/
theorem norm_iteratedFDeriv_le_two_pow_mul_add {V : Type*} {E : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) :
    ∀ (g : V → E) (B A : ℝ), ContDiff ℝ (n + 1 : ℕ) g → (∀ y, ‖g y‖ ≤
    B) → (∀ y, ‖iteratedFDeriv ℝ (n + 1) g y‖ ≤ A) → ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤
      2 ^ n * B + n * A := by
  induction n with
  | zero =>
    intro g B A _ hB _ x
    simpa [norm_iteratedFDeriv_zero] using hB x
  | succ n ih =>
    intro g B A hg hB hA x
    have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA x)
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB x)
    rw [← norm_fderiv_iteratedFDeriv]
    refine ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity) fun v hv ↦ ?_
    have hgt : ContDiff ℝ (n + 1 + 1 : ℕ) (fun y ↦ g (y + v)) :=
      hg.comp (contDiff_id.add contDiff_const)
    set h : V → E := (fun y ↦ g (y + v)) - g with hh
    have hhc : ContDiff ℝ (n + 1 : ℕ) h :=
      (hgt.sub hg).of_le (by exact_mod_cast Nat.le_succ (n + 1))
    have hDh : ∀ m : ℕ, m ≤ n + 1 + 1 → ∀ y, iteratedFDeriv ℝ m h y =
        iteratedFDeriv ℝ m g (y + v) - iteratedFDeriv ℝ m g y := by
      intro m hm y
      have hm' : ((m : ℕ) : WithTop ℕ∞) ≤ ((n + 1 + 1 : ℕ) : WithTop ℕ∞) := by exact_mod_cast hm
      rw [hh, iteratedFDeriv_sub_apply (hgt.contDiffAt.of_le hm') (hg.contDiffAt.of_le hm'),
        iteratedFDeriv_comp_add_right]
    have h1 : ∀ y, ‖h y‖ ≤ 2 * B := by
      intro y
      simp only [hh, Pi.sub_apply]
      exact (norm_sub_le _ _).trans (by linarith [hB (y + v), hB y])
    have h2 : ∀ y, ‖iteratedFDeriv ℝ (n + 1) h y‖ ≤ A := by
      intro y
      rw [hDh (n + 1) (Nat.le_succ _) y]
      have := norm_iteratedFDeriv_sub_le_of_succ_le hg hA y (y + v)
      rwa [add_sub_cancel_left, hv, mul_one] at this
    have h3 := ih h (2 * B) A hhc h1 h2 x
    rw [hDh n (by omega) x] at h3
    have h4 : ‖iteratedFDeriv ℝ n g (x + v) - iteratedFDeriv ℝ n g x -
        fderiv ℝ (iteratedFDeriv ℝ n g) x ((x + v) - x)‖ ≤ A * ‖(x + v) - x‖ := by
      refine (convex_closedBall x 1).norm_image_sub_le_of_norm_fderiv_le' (fun z _ ↦ ?_)
        (fun z hz ↦ ?_) (mem_closedBall_self zero_le_one) ?_
      · exact hg.differentiable_iteratedFDeriv (by exact_mod_cast (by omega : n < n + 1 + 1)) z
      · rw [fderiv_iteratedFDeriv, Function.comp_apply, Function.comp_apply,
          ← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map]
        have hz' : ‖z - x‖ ≤ 1 := by rwa [mem_closedBall, dist_eq_norm] at hz
        calc _ ≤ A * ‖z - x‖ := norm_iteratedFDeriv_sub_le_of_succ_le hg hA x z
          _ ≤ A * 1 := mul_le_mul_of_nonneg_left hz' hA0
          _ = A := mul_one A
      · rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, hv]
    rw [add_sub_cancel_left, hv, mul_one] at h4
    have h5 : ‖fderiv ℝ (iteratedFDeriv ℝ n g) x v‖ ≤
        ‖iteratedFDeriv ℝ n g (x + v) - iteratedFDeriv ℝ n g x‖ +
        ‖iteratedFDeriv ℝ n g (x + v) - iteratedFDeriv ℝ n g x -
          fderiv ℝ (iteratedFDeriv ℝ n g) x v‖ := by
      refine le_trans (le_of_eq ?_) (norm_sub_le _ _)
      congr 1; abel
    have h6 : (2 : ℝ) ^ (n + 1) = 2 ^ n * 2 := pow_succ 2 n
    push_cast
    rw [h6]
    linarith

/-- For every natural number `m`, the map `z ↦ (‖z‖ ^ 4) • (‖z‖⁻¹ • z) ^ m` on `ℂ` is `C^3` over
`ℝ`. It is smooth away from `0`, vanishes at `0`, and is positively homogeneous of degree `4`, so
the smoothness criterion for homogeneous maps applies with `n = 3`. -/
theorem contDiff_three_norm_pow_four_smul_pow (m : ℕ) :
    ContDiff ℝ 3 (fun z : ℂ ↦ (‖z‖ ^ 4) • (‖z‖⁻¹ • z) ^ m) := by
  have h := contDiff_of_homogeneous 3 (fun z : ℂ ↦ (‖z‖ ^ 4) • (‖z‖⁻¹ • z) ^ m) ?_ ?_ ?_
  · exact_mod_cast h
  · intro z hz
    have hz' : z ≠ 0 := hz
    exact (((contDiffAt_norm ℝ hz').pow 4).smul ((((contDiffAt_norm ℝ hz').inv
      (norm_ne_zero_iff.2 hz')).smul contDiffAt_id).pow m)).contDiffWithinAt
  · simp
  · intro t ht z
    have hn : ‖t • z‖ = t * ‖z‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    have hu : (t * ‖z‖)⁻¹ • (t • z) = ‖z‖⁻¹ • z := by
      rw [smul_smul, mul_inv, mul_comm t⁻¹, mul_assoc, inv_mul_cancel₀ ht.ne', mul_one]
    rw [hn, hu, mul_pow, smul_smul]

/-- Bound for the intermediate derivatives: if `g : V → E` is `C^j` between real normed spaces,
`‖g y‖ ≤ B` and `‖iteratedFDeriv ℝ j g y‖ ≤ A` for all `y`, then
`‖iteratedFDeriv ℝ n g y‖ ≤ (2 ^ j + j) ^ j * (A + B)` for every `n ≤ j` and every `y`. The proof
goes down from order `j` one order at a time, bounding each derivative by the function and the
derivative of the next order. -/
theorem norm_iteratedFDeriv_intermediate_le {V : Type*} {E : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] (j : ℕ) (g : V → E) (A B : ℝ)
    (hg : ContDiff ℝ j g) (hB : ∀ y, ‖g y‖ ≤ B)
    (hA : ∀ y, ‖iteratedFDeriv ℝ j g y‖ ≤ A) :
    ∀ n ≤ j, ∀ y, ‖iteratedFDeriv ℝ n g y‖ ≤ ((2 : ℝ) ^ j + j) ^ j * (A + B) := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  set K : ℝ := (2 : ℝ) ^ j + j with hK
  have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hK1 : 1 ≤ K := by rw [hK]; linarith
  have hAB : 0 ≤ A + B := by linarith
  have key : ∀ m ≤ j, ∀ y, ‖iteratedFDeriv ℝ (j - m) g y‖ ≤ K ^ m * (A + B) := by
    intro m
    induction m with
    | zero => intro _ y; simp only [Nat.sub_zero, pow_zero, one_mul]; linarith [hA y]
    | succ m ih =>
      intro hm y
      have hKm : 1 ≤ K ^ m := one_le_pow₀ hK1
      have hn1 : j - m = j - (m + 1) + 1 := by omega
      have hgn : ContDiff ℝ (j - (m + 1) + 1 : ℕ) g :=
        hg.of_le (by exact_mod_cast (by omega : j - (m + 1) + 1 ≤ j))
      have hb := norm_iteratedFDeriv_le_two_pow_mul_add (j - (m + 1)) g B (K ^ m * (A + B)) hgn hB
        (fun z ↦ by have := ih (by omega) z; rwa [hn1] at this) y
      have hnj : ((j - (m + 1) : ℕ) : ℝ) ≤ j := by exact_mod_cast (by omega : j - (m + 1) ≤ j)
      have h2n : (2 : ℝ) ^ (j - (m + 1)) ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) (by omega)
      have hX : 0 ≤ K ^ m * (A + B) := mul_nonneg (by linarith) hAB
      have hBle : B ≤ K ^ m * (A + B) := le_trans (by linarith) (le_mul_of_one_le_left hAB hKm)
      calc ‖iteratedFDeriv ℝ (j - (m + 1)) g y‖
          ≤ 2 ^ (j - (m + 1)) * B + ((j - (m + 1) : ℕ) : ℝ) * (K ^ m * (A + B)) := hb
        _ ≤ 2 ^ j * (K ^ m * (A + B)) + j * (K ^ m * (A + B)) :=
          add_le_add (mul_le_mul h2n hBle hB0 (by positivity)) (mul_le_mul_of_nonneg_right hnj hX)
        _ = K ^ (m + 1) * (A + B) := by rw [hK, pow_succ]; ring
  intro n hn y
  have := key (j - n) (Nat.sub_le j n) y
  rw [Nat.sub_sub_self hn] at this
  exact this.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hK1 (Nat.sub_le j n)) hAB)

/-- In `WithTop ℕ∞`, `∞ + 1 ≤ ∞`, where `∞` is the top of `ℕ∞`, the order of smoothness of `C^∞`
functions. -/
theorem infty_add_one_le_infty : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  exact le_of_eq rfl

/-- In `WithTop ℕ∞`, `2 ≤ ∞`, where `∞` is the top of `ℕ∞`, the order of smoothness of `C^∞`
functions. -/
theorem two_le_infty : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 le_top

end PDE.Analysis
