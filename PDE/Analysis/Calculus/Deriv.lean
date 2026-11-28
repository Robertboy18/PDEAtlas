/-
Authors: Levent Alpöge, Tristan Buckmaster

The lemmas of this file, except hasDerivAt_eval_mvPolynomial, come from modules of the Lean
package of the paper "Finite-time blow-up for the Navier–Stokes equations"
(https://github.com/tristanbuckmaster/navier-stokes, folder lean/, commit ad53419),
where they were steps of longer proofs. They were included in BlowupZoo
(https://github.com/lean-dojo/BlowupZoo, folder AtlasCandidates/) with the permission of the
authors (20 November 2026) and moved here from there; the file NOTICE of this repository records it.
The lemma hasDerivAt_eval_mvPolynomial was written for this library, with the induction by which
the authors proved two of its cases.
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Order.CompletePartialOrder
public import PDE.Analysis.Calculus.Deriv.Square
public import PDE.Analysis.Order.MinMax
public import PDE.Analysis.Scalar.Powers
public import PDE.Analysis.Topology.Compactness

set_option linter.style.header false

/-!
# Derivatives of functions of one real variable

The lemmas state `HasDerivAt` and `deriv` for products, compositions and quotients of particular
shapes, for functions with values in a normed space, and for functions that agree near a point. The
proofs combine the rules of Mathlib (`HasDerivAt.mul`, `HasDerivAt.comp`, `HasDerivAt.scomp`) and
identify the result by `ring` or `simp`.

## Main results

* `PDE.Analysis.hasDerivAt_eval_ofReal_pderiv_zero`: For a polynomial `P : MvPolynomial (Fin 2) ℂ`
  and real `x`, `t`, the function `s ↦ MvPolynomial.eval ![(s : ℂ), (x : ℂ)] P` of a real variable
  has derivative `MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (MvPolynomial.pderiv 0 P)` at `t`. This is
  `hasDerivAt_eval_pderiv_zero` at the complex number `x`.
* `PDE.Analysis.norm_sub_le_of_deriv_right_le`: Mean value inequality with right derivatives on a
  symmetric interval: if `g : ℝ → ℂ` is continuous, has derivative `g' s` at every `s` within
  `Set.Ici s`, and `‖g' s‖ ≤ M` whenever `|s| ≤ R`, then `‖g a - g b‖ ≤ M * |a - b|` for all `a` and
  `b` with `|a| ≤ R` and `|b| ≤ R`.
* `PDE.Analysis.deriv_eq_zero_of_lt_abs`: If `ψ : ℝ → ℝ` satisfies `ψ z = 0` whenever `N < |z|`,
  then `deriv ψ z = 0` whenever `N < |z|`.
* `PDE.Analysis.hasDerivAt_eval_mvPolynomial`: Chain rule for a polynomial `Q : MvPolynomial σ ℂ` in
  finitely many variables along a curve `x : ℝ → σ → ℂ`: if every coordinate `r ↦ x r i` has
  derivative `x' i` at `s`, then `r ↦ MvPolynomial.eval (x r) Q` has derivative
  `∑ i, MvPolynomial.eval (x s) (MvPolynomial.pderiv i Q) * x' i` at `s`. The next two lemmas are
  its cases for the curves `r ↦ ![y, r]` and `r ↦ ![r, y]`.
* `PDE.Analysis.hasDerivAt_eval_pderiv_one`: For a polynomial `Q : MvPolynomial (Fin 2) ℂ`, a
  complex number `y` and a real `s`, the function `r ↦ MvPolynomial.eval ![y, (r : ℂ)] Q` of a real
  variable has derivative `MvPolynomial.eval ![y, (s : ℂ)] (MvPolynomial.pderiv 1 Q)` at `s`.
* `PDE.Analysis.hasDerivAt_eval_pderiv_zero`: For a polynomial `Q : MvPolynomial (Fin 2) ℂ`, a
  complex number `y` and a real `s`, the function `r ↦ MvPolynomial.eval ![(r : ℂ), y] Q` of a real
  variable has derivative `MvPolynomial.eval ![(s : ℂ), y] (MvPolynomial.pderiv 0 Q)` at `s`.
* `PDE.Analysis.hasDerivAt_intervalIntegral_of_continuous`: Differentiation under the interval
  integral. Let `F`, `F' : ℝ → ℝ → E` take values in a complete real normed space, with
  `fun p ↦ F p.1 p.2` and `fun p ↦ F' p.1 p.2` continuous on `ℝ × ℝ` and `F' s t` the derivative of
  `fun s ↦ F s t` at `s` for all `s`, `t`; then for all real `a b x`, `fun s ↦ ∫ t in a..b, F s t`
  has derivative `∫ t in a..b, F' x t` at `x`.
* `PDE.Analysis.deriv_eq_of_eqOn_isOpen`: Let `U` be an open set of reals. If `F t = G t` for all
  `t ∈ U` and `G` has derivative `H t` at every `t ∈ U`, then `deriv F t = H t` for all `t ∈ U`.

There are 49 further lemmas of the same kind.

## Implementation notes

The derivative of the square, `PDE.Analysis.hasDerivAt_sq`, is in
`PDE.Analysis.Calculus.Deriv.Square`, which this module imports.

## References

* Levent Alpöge and Tristan Buckmaster, the Lean package of the paper "Finite-time blow-up for the
  Navier–Stokes equations", <https://github.com/tristanbuckmaster/navier-stokes>, folder `lean/`,
  commit `ad53419`: the lemmas of this module and their proofs, adapted to this library. See
  `NOTICE` for attribution and permission.
  The lemma `hasDerivAt_eval_mvPolynomial` is not from the package: it was written for this
  library, with the induction by which the authors proved two of its cases,
  `hasDerivAt_eval_pderiv_one` and `hasDerivAt_eval_pderiv_zero`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Topology Filter Set Real Polynomial
open scoped ContDiff

namespace PDE.Analysis

/-- Let `U` be an open set of reals. If `F t = G t` for all `t ∈ U` and `G` has derivative `H t` at
every `t ∈ U`, then `deriv F t = H t` for all `t ∈ U`. -/
theorem deriv_eq_of_eqOn_isOpen {F G H : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hFG : ∀ t ∈ U, F t = G t) (hG : ∀ t ∈ U, HasDerivAt G (H t) t) :
    ∀ t ∈ U, deriv F t = H t := by
  intro t ht
  have h : F =ᶠ[nhds t] G := Filter.eventually_of_mem (hU.mem_nhds ht) hFG
  rw [h.deriv_eq]
  exact (hG t ht).deriv

/-- If `ψ : ℝ → ℝ` satisfies `ψ z = 0` whenever `N < |z|`, then `deriv ψ z = 0` whenever `N < |z|`.
-/
theorem deriv_eq_zero_of_lt_abs {ψ : ℝ → ℝ} {N : ℝ} (hψN : ∀ z, N < |z| → ψ z = 0) :
    ∀ z, N < |z| → deriv ψ z = 0 := by
  intro z hz
  refine image_eq_zero_of_notMem_tsupport fun h ↦ ?_
  have := tsupport_subset_Icc hψN (tsupport_deriv_subset h)
  rw [mem_Icc] at this
  have := abs_le.2 this
  linarith

/-- If `f : ℝ → ℝ` vanishes outside a closed set `K` and `s ∉ K`, then `deriv f s = 0`. -/
theorem deriv_eq_zero_of_notMem_of_isClosed {f : ℝ → ℝ} {K : Set ℝ} (hK : IsClosed K)
    (hf : ∀ x, x ∉ K → f x = 0) {s : ℝ} (hs : s ∉ K) : deriv f s = 0 := by
  have h : f =ᶠ[nhds s] fun _ ↦ (0 : ℝ) :=
    Filter.eventuallyEq_of_mem (hK.isOpen_compl.mem_nhds hs) (fun x hx ↦ hf x hx)
  rw [h.deriv_eq]
  simp

/-- For all real `h` and `z`, `deriv (fun z ↦ 1 - z / h) z = -(1 / h)`, with no assumption that
`h ≠ 0`. -/
theorem deriv_one_sub_div_const (h z : ℝ) : deriv (fun z : ℝ ↦ 1 - z / h) z = -(1 / h) := by
  have : HasDerivAt (fun z : ℝ ↦ 1 - z / h) (-(1 / h)) z := by
    simpa using ((hasDerivAt_id z).div_const h).const_sub 1
  exact this.deriv

/-- If `g : ℝ → ℂ` is `C^2` over `ℝ`, then both `g` and `deriv g` are differentiable. -/
theorem differentiable_deriv_of_contDiff_two {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) :
    Differentiable ℝ g ∧ Differentiable ℝ (deriv g) := by
  have h := (contDiff_succ_iff_deriv (n := 1)).1 (show ContDiff ℝ (1 + 1) g from hg)
  exact ⟨h.1, h.2.2.differentiable (by norm_num)⟩

/-- Let `0 ≤ a` and let `φ : ℝ → ℝ` be `C^2` on `Set.Ioi a` with
`6 * deriv φ s + 4 * s * deriv (deriv φ) s = 0` for all `s > a` (the equation for `x ↦ φ (‖x‖ ^ 2)`
to be harmonic in dimension three). Then there are real constants `A` and `B` with
`φ s = A + B / √s` for all `s > a`. The proof shows that `s * √s * deriv φ s` is a constant `b` on
`Set.Ioi a`, and then that `φ s + 2 * b * (√s)⁻¹` is constant. -/
theorem eq_add_div_sqrt_of_radial_ode {φ : ℝ → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hφ : ContDiffOn ℝ 2 φ (Ioi a))
    (h : ∀ s > a, 6 * deriv φ s + 4 * s * deriv (deriv φ) s = 0) :
    ∃ A B : ℝ, ∀ s > a, φ s = A + B / √s := by
  have hU : IsOpen (Ioi a) := isOpen_Ioi
  have hpre : IsPreconnected (Ioi a) := isPreconnected_Ioi
  have hd1 : ∀ s > a, DifferentiableAt ℝ φ s := fun s hs ↦
    (hφ.contDiffAt (hU.mem_nhds hs)).differentiableAt (by norm_num)
  have hd2 : ∀ s > a, DifferentiableAt ℝ (deriv φ) s := fun s hs ↦
    ((hφ.deriv_of_isOpen hU (m := 1) (by norm_num)).contDiffAt
      (hU.mem_nhds hs)).differentiableAt (by norm_num)
  have hsq : ∀ s > a, HasDerivAt (fun t ↦ √t) (1 / (2 * √s)) s := fun s hs ↦
    Real.hasDerivAt_sqrt (ne_of_gt (lt_of_le_of_lt ha hs))
  have hψ : ∀ s > a, HasDerivAt (fun t ↦ t * √t * deriv φ t)
      (√s / 4 * (6 * deriv φ s + 4 * s * deriv (deriv φ) s)) s := by
    intro s hs
    have hs0 : 0 < s := lt_of_le_of_lt ha hs
    have hr : 0 < √s := Real.sqrt_pos.2 hs0
    have := ((hasDerivAt_id s).mul (hsq s hs)).mul (hd2 s hs).hasDerivAt
    refine this.congr_deriv ?_
    have hrs : √s ^ 2 = s := Real.sq_sqrt hs0.le
    simp only [Pi.mul_apply, id_eq]
    generalize √s = r at hrs hr ⊢
    subst hrs
    field_simp
    ring
  obtain ⟨b, hb⟩ : ∃ b : ℝ, ∀ s > a, s * √s * deriv φ s = b :=
    ⟨_, fun s hs ↦ hU.is_const_of_deriv_eq_zero hpre
      (fun t ht ↦ (hψ t ht).differentiableAt.differentiableWithinAt)
      (fun t ht ↦ by simp [(hψ t ht).deriv, h t ht]) hs
      (show a + 1 ∈ Ioi a by simp)⟩
  have hχ : ∀ s > a, HasDerivAt (fun t ↦ φ t + 2 * b * (√t)⁻¹) 0 s := by
    intro s hs
    have hs0 : 0 < s := lt_of_le_of_lt ha hs
    have hr : 0 < √s := Real.sqrt_pos.2 hs0
    have := (hd1 s hs).hasDerivAt.add (((hsq s hs).inv hr.ne').const_mul (2 * b))
    refine this.congr_deriv ?_
    rw [← hb s hs]
    have hrs : √s ^ 2 = s := Real.sq_sqrt hs0.le
    generalize √s = r at hrs hr ⊢
    subst hrs
    field_simp
    ring
  refine ⟨φ (a + 1) + 2 * b * (√(a + 1))⁻¹, -2 * b, fun s hs ↦ ?_⟩
  have := hU.is_const_of_deriv_eq_zero hpre (f := fun t ↦ φ t + 2 * b * (√t)⁻¹)
    (fun t ht ↦ (hχ t ht).differentiableAt.differentiableWithinAt)
    (fun t ht ↦ by simp [(hχ t ht).deriv]) hs (show a + 1 ∈ Ioi a by simp)
  rw [div_eq_mul_inv]
  linarith

/-- If `χ : ℝ → ℝ` has derivative `χ' s` at every `s`, then `χ' s = 0` for every `s` outside the
topological support of `χ`. -/
theorem eq_zero_of_hasDerivAt_of_notMem_tsupport {χ χ' : ℝ → ℝ} (hχ' : ∀ s, HasDerivAt χ (χ' s) s)
    {s : ℝ}
    (hs : s ∉ tsupport χ) : χ' s = 0 := by
  have h : χ =ᶠ[nhds s] fun _ ↦ (0 : ℝ) := (notMem_tsupport_iff_eventuallyEq).1 hs
  exact (hχ' s).unique ((hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq h)

/-- If `(X - C r) ^ n` divides a polynomial `P` over `ℂ` and `o < n`, then the `o`-th derivative of
`P` vanishes at `r`: `(derivative^[o] P).eval r = 0`. -/
theorem eval_iterate_derivative_eq_zero_of_dvd {P : Polynomial ℂ} {r : ℂ} {n o : ℕ}
    (h : (X - C r) ^ n ∣ P) (ho : o < n) : (derivative^[o] P).eval r = 0 := by
  obtain ⟨q, hq⟩ := pow_sub_dvd_iterate_derivative_of_pow_dvd o h
  rw [hq, eval_mul, eval_pow, eval_sub, eval_X, eval_C, sub_self, zero_pow (by omega), zero_mul]

/-- Let `p` be a real polynomial and `c = 1 - X ^ (2 * k + 2)`. Then
`(c * derivative c * p ^ 2).eval 1 - (c * derivative c * p ^ 2).eval (-1) = 0`, where `derivative`
is the formal derivative of polynomials. Both values vanish, because `c` vanishes at `1` and at
`-1`. -/
theorem eval_one_sub_eval_neg_one (k : ℕ) (p : ℝ[X]) :
    ((1 - X ^ (2 * k + 2)) * derivative (1 - X ^ (2 * k + 2)) * p ^ 2).eval 1
      - ((1 - X ^ (2 * k + 2)) * derivative (1 - X ^ (2 * k + 2)) * p ^ 2).eval (-1) = 0 := by
  simp only [eval_mul, eval_sub, eval_one, eval_pow, eval_X, one_pow, sub_self, zero_mul]
  rw [Even.neg_one_pow ⟨k + 1, by ring⟩]
  ring

/-- For `c : ℂ` and naturals `p`, `o`, the `o`-th derivative of the polynomial `C c * X ^ p`
evaluated at `0` is `c * p.factorial` if `o = p` and `0` otherwise. The proof writes the iterated
derivative as a descending factorial times a power of `X` and compares `o` with `p`. -/
theorem eval_zero_iterate_derivative_monomial (c : ℂ) (p o : ℕ) :
    (derivative^[o] (C c * X ^ p)).eval 0 = if o = p then c * (p.factorial : ℂ) else 0 := by
  rw [iterate_derivative_C_mul, iterate_derivative_X_pow_eq_C_mul, eval_mul, eval_C, eval_mul,
      eval_C,
    eval_pow, eval_X]
  rcases lt_trichotomy o p with h | h | h
  · rw [ite_eq_right h.ne, zero_pow (by omega)]
    ring
  · subst h
    simp [Nat.descFactorial_self]
  · rw [ite_eq_right h.ne', (Nat.descFactorial_eq_zero_iff_lt).2 h]
    simp

/-- If `f : ℝ → ℝ` is smooth (`ContDiff ℝ ∞`) and has compact support, then there is `M ≥ 0` with
`|deriv f s| ≤ M` for all `s`. -/
theorem exists_abs_deriv_le_of_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) : ∃ M : ℝ, 0 ≤ M ∧ ∀ s, |deriv f s| ≤ M := by
  obtain ⟨C, hC⟩ := (hf.continuous_deriv (by norm_num)).bounded_above_of_compact_support hs.deriv
  refine ⟨max C 0, le_max_right _ _, fun s ↦ ?_⟩
  have h := hC s
  rw [Real.norm_eq_abs] at h
  exact h.trans (le_max_left _ _)

/-- For `0 < a` and `0 < b`, the function
`s ↦ Real.arctan (Real.sqrt (b / a) * s) / (a * Real.sqrt (b / a))` has derivative
`(a + b * r ^ 2)⁻¹` at every real `r`, so it is a primitive of `r ↦ (a + b * r ^ 2)⁻¹`. -/
theorem hasDerivAt_arctan_sqrt_mul_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (r : ℝ) :
    HasDerivAt (fun s ↦ arctan (Real.sqrt (b / a) * s) / (a * Real.sqrt (b / a)))
      (a + b * r ^ 2)⁻¹ r := by
  have hc := sqrt_div_pos ha hb
  have hc2 : Real.sqrt (b / a) ^ 2 = b / a := Real.sq_sqrt (div_pos hb ha).le
  have h := (((hasDerivAt_id r).const_mul (Real.sqrt (b / a))).arctan).div_const
    (a * Real.sqrt (b / a))
  refine h.congr_deriv ?_
  simp only [id, mul_one, mul_pow, hc2]
  field_simp

/-- For real `a`, `b`, `u`, the function `v ↦ Complex.exp ((a * (b + v)) * Complex.I)` of a real
variable has derivative `Complex.exp ((a * (b + u)) * Complex.I) * (a * Complex.I)` at `u`. -/
theorem hasDerivAt_cexp_mul_add_mul_I (a b u : ℝ) :
    HasDerivAt (fun v : ℝ ↦ Complex.exp (((a * (b + v) : ℝ) : ℂ) * Complex.I))
      (Complex.exp (((a * (b + u) : ℝ) : ℂ) * Complex.I) * ((a : ℂ) * Complex.I)) u := by
  have h1 : HasDerivAt (fun v : ℝ ↦ a * (b + v)) a u := by
    simpa using ((hasDerivAt_id u).const_add b).const_mul a
  have h2 := (h1.ofReal_comp.mul_const Complex.I).cexp
  simpa using h2

/-- For real `c`, `d`, `t`, the function `s ↦ Complex.exp (-((d + c * s) * Complex.I))` of a real
variable has derivative `-(c * Complex.I) * Complex.exp (-((d + c * t) * Complex.I))` at `t`. -/
theorem hasDerivAt_cexp_neg_add_mul_mul_I (c d t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ Complex.exp (-(((d + c * s : ℝ) : ℂ) * Complex.I)))
      (-((c : ℂ) * Complex.I) * Complex.exp (-(((d + c * t : ℝ) : ℂ) * Complex.I))) t := by
  have h1 : HasDerivAt (fun s : ℝ ↦ d + c * s) c t := by
    simpa using ((hasDerivAt_id t).const_mul c).const_add d
  have h2 : HasDerivAt (fun s : ℝ ↦ -(((d + c * s : ℝ) : ℂ) * Complex.I))
      (-((c : ℂ) * Complex.I)) t :=
    ((h1.ofReal_comp).mul_const Complex.I).neg
  convert h2.cexp using 1
  ring

/-- For real `c`, `d`, `t`, the function `s ↦ Complex.exp (-((c * s + d) * Complex.I))` of a real
variable has derivative `-(c * Complex.I) * Complex.exp (-((c * t + d) * Complex.I))` at `t`. -/
theorem hasDerivAt_cexp_neg_mul_add_mul_I (c d t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ Complex.exp (-(((c * s + d : ℝ) : ℂ) * Complex.I)))
      (-((c : ℂ) * Complex.I) * Complex.exp (-(((c * t + d : ℝ) : ℂ) * Complex.I))) t := by
  have h1 : HasDerivAt (fun s : ℝ ↦ c * s + d) c t := by
    simpa using ((hasDerivAt_id t).const_mul c).add_const d
  have h2 : HasDerivAt (fun s : ℝ ↦ -(((c * s + d : ℝ) : ℂ) * Complex.I))
      (-((c : ℂ) * Complex.I)) t :=
    ((h1.ofReal_comp).mul_const Complex.I).neg
  convert h2.cexp using 1
  ring

/-- For real `n`, `k`, `τ`, `φ`, the function
`t ↦ Complex.exp (-((2 * π * n * τ + k * t) * Complex.I))` of a real variable has derivative
`Complex.exp (-((2 * π * n * τ + k * φ) * Complex.I)) * (-(k * Complex.I))` at `φ`. -/
theorem hasDerivAt_cexp_neg_two_pi_add_mul (n k τ φ : ℝ) :
    HasDerivAt (fun t : ℝ ↦ Complex.exp (-(((2 * Real.pi * n * τ + k * t : ℝ) : ℂ) * Complex.I)))
      (Complex.exp (-(((2 * Real.pi * n * τ + k * φ : ℝ) : ℂ) * Complex.I)) *
          (-((k : ℂ) * Complex.I))) φ := by
  have h1 : HasDerivAt (fun t : ℝ ↦ ((2 * Real.pi * n * τ + k * t : ℝ) : ℂ)) (k : ℂ) φ := by
    have := (((hasDerivAt_id φ).const_mul k).const_add (2 * Real.pi * n * τ)).ofReal_comp
    simpa using this
  exact ((h1.mul_const Complex.I).neg).cexp

/-- For real `n`, `c`, `τ`, the function `t ↦ Complex.exp (-((2 * π * n * t + c) * Complex.I))` of a
real variable has derivative
`Complex.exp (-((2 * π * n * τ + c) * Complex.I)) * (-((2 * π * n) * Complex.I))` at `τ`. -/
theorem hasDerivAt_cexp_neg_two_pi_mul_add (n : ℝ) (c : ℝ) (τ : ℝ) :
    HasDerivAt (fun t : ℝ ↦ Complex.exp (-(((2 * Real.pi * n * t + c : ℝ) : ℂ) * Complex.I)))
      (Complex.exp (-(((2 * Real.pi * n * τ + c : ℝ) : ℂ) * Complex.I)) *
          (-(((2 * Real.pi * n : ℝ) : ℂ) * Complex.I)))
      τ := by
  have h1 : HasDerivAt (fun t : ℝ ↦ ((2 * Real.pi * n * t + c : ℝ) : ℂ))
      ((2 * Real.pi * n : ℝ) : ℂ) τ := by
    have := (((hasDerivAt_id τ).const_mul (2 * Real.pi * n)).add_const c).ofReal_comp
    simpa using this
  have h3 : HasDerivAt (fun t : ℝ ↦ -(((2 * Real.pi * n * t + c : ℝ) : ℂ) * Complex.I))
      (-(((2 * Real.pi * n : ℝ) : ℂ) * Complex.I)) τ := (h1.mul_const Complex.I).neg
  exact h3.cexp

/-- Let `φ : ℝ → ℝ` have derivative `φ' s` at every `s`, with `φ' a = 0`. Then `s ↦ φ (min s a)` has
derivative `φ' (min t a)` at every `t`. For `t ≠ a` the function agrees near `t` with `φ` or with a
constant, and at `t = a` the left derivative `φ' a` and the right derivative `0` coincide. -/
theorem hasDerivAt_comp_min_of_deriv_eq_zero (φ φ' : ℝ → ℝ) (a t : ℝ)
    (h : ∀ s, HasDerivAt φ (φ' s) s)
    (ha : φ' a = 0) : HasDerivAt (fun s ↦ φ (min s a)) (φ' (min t a)) t := by
  rcases lt_trichotomy t a with hta | hta | hta
  · rw [min_eq_left hta.le]
    apply (h t).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hta] with s hs
    simp [min_eq_left (Set.mem_Iio.mp hs).le]
  · subst hta
    rw [min_self]
    have h1 : HasDerivWithinAt (fun s ↦ φ (min s t)) (φ' t) (Set.Iic t) t :=
      (h t).hasDerivWithinAt.congr (fun s hs ↦ by simp [min_eq_left (Set.mem_Iic.mp hs)])
        (by simp)
    have h2 : HasDerivWithinAt (fun s ↦ φ (min s t)) (φ' t) (Set.Ici t) t := by
      rw [ha]
      exact (hasDerivWithinAt_const t (Set.Ici t) (φ t)).congr
        (fun s hs ↦ by simp [min_eq_right (Set.mem_Ici.mp hs)]) (by simp)
    have h3 := h1.union h2
    rwa [Set.Iic_union_Ici, hasDerivWithinAt_univ] at h3
  · rw [min_eq_right hta.le, ha]
    apply (hasDerivAt_const t (φ a)).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hta] with s hs
    simp [min_eq_right (Set.mem_Ioi.mp hs).le]

/-- For every real `a`, the function `t ↦ Real.cos (a * t)` has derivative `0` at the point `0`. -/
theorem hasDerivAt_cos_const_mul_zero (a : ℝ) : HasDerivAt (fun t : ℝ ↦ Real.cos (a * t)) 0 0 := by
  have := ((hasDerivAt_id (0 : ℝ)).const_mul a).cos
  simpa using this

/-- Chain rule for the evaluation of a polynomial along a curve. Let `Q : MvPolynomial σ ℂ` with
`σ` finite, and let `x : ℝ → σ → ℂ` be such that every coordinate `r ↦ x r i` has derivative `x' i`
at `s`. Then `r ↦ MvPolynomial.eval (x r) Q` has derivative
`∑ i, MvPolynomial.eval (x s) (MvPolynomial.pderiv i Q) * x' i` at `s`. The proof is by induction on
`Q` over constants, sums and multiplication by a variable. -/
theorem hasDerivAt_eval_mvPolynomial {σ : Type*} [Fintype σ] (Q : MvPolynomial σ ℂ)
    {x : ℝ → σ → ℂ} {x' : σ → ℂ} {s : ℝ} (hx : ∀ i, HasDerivAt (fun r ↦ x r i) (x' i) s) :
    HasDerivAt (fun r : ℝ ↦ MvPolynomial.eval (x r) Q)
      (∑ i, MvPolynomial.eval (x s) (MvPolynomial.pderiv i Q) * x' i) s := by
  classical
  induction Q using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const s a
  | add p q hp hq =>
    simp only [map_add, add_mul, Finset.sum_add_distrib]
    exact hp.add hq
  | mul_X p j hp =>
    have hf : (fun r : ℝ ↦ MvPolynomial.eval (x r) (p * MvPolynomial.X j)) =
        fun r : ℝ ↦ MvPolynomial.eval (x r) p * x r j := by
      funext r; simp
    rw [hf]
    refine (hp.mul (hx j)).congr_deriv ?_
    simp only [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X, Pi.single_apply, map_add, map_mul,
      MvPolynomial.eval_X, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
    congr 1
    · exact Finset.sum_congr rfl fun i _ ↦ by ring
    · simp [apply_ite]

/-- For a polynomial `Q : MvPolynomial (Fin 2) ℂ`, a complex number `y` and a real `s`, the function
`r ↦ MvPolynomial.eval ![y, (r : ℂ)] Q` of a real variable has derivative
`MvPolynomial.eval ![y, (s : ℂ)] (MvPolynomial.pderiv 1 Q)` at `s`. This is
`hasDerivAt_eval_mvPolynomial` for the curve `r ↦ ![y, (r : ℂ)]`. -/
theorem hasDerivAt_eval_pderiv_one (Q : MvPolynomial (Fin 2) ℂ) (y : ℂ) (s : ℝ) :
    HasDerivAt (fun r : ℝ ↦ MvPolynomial.eval ![y, (r : ℂ)] Q)
      (MvPolynomial.eval ![y, (s : ℂ)] (MvPolynomial.pderiv 1 Q)) s := by
  have h := hasDerivAt_eval_mvPolynomial Q (x := fun r : ℝ ↦ ![y, (r : ℂ)]) (x' := ![0, 1])
    (s := s) (Fin.forall_fin_two.2 ⟨by simpa using hasDerivAt_const s y,
      by simpa using (hasDerivAt_id s).ofReal_comp⟩)
  simpa [Fin.sum_univ_two] using h

/-- For a polynomial `Q : MvPolynomial (Fin 2) ℂ`, a complex number `y` and a real `s`, the function
`r ↦ MvPolynomial.eval ![(r : ℂ), y] Q` of a real variable has derivative
`MvPolynomial.eval ![(s : ℂ), y] (MvPolynomial.pderiv 0 Q)` at `s`. This is
`hasDerivAt_eval_mvPolynomial` for the curve `r ↦ ![(r : ℂ), y]`. -/
theorem hasDerivAt_eval_pderiv_zero (Q : MvPolynomial (Fin 2) ℂ) (y : ℂ) (s : ℝ) :
    HasDerivAt (fun r : ℝ ↦ MvPolynomial.eval ![(r : ℂ), y] Q)
      (MvPolynomial.eval ![(s : ℂ), y] (MvPolynomial.pderiv 0 Q)) s := by
  have h := hasDerivAt_eval_mvPolynomial Q (x := fun r : ℝ ↦ ![(r : ℂ), y]) (x' := ![1, 0])
    (s := s) (Fin.forall_fin_two.2 ⟨by simpa using (hasDerivAt_id s).ofReal_comp,
      by simpa using hasDerivAt_const s y⟩)
  simpa [Fin.sum_univ_two] using h

/-- Differentiation under the interval integral. Let `F`, `F' : ℝ → ℝ → E` take values in a complete
real normed space, with `fun p ↦ F p.1 p.2` and `fun p ↦ F' p.1 p.2` continuous on `ℝ × ℝ` and
`F' s t` the derivative of `fun s ↦ F s t` at `s` for all `s`, `t`; then for all real `a b x`,
`fun s ↦ ∫ t in a..b, F s t` has derivative `∫ t in a..b, F' x t` at `x`. The proof bounds `F'` on
the compact set `closedBall x 1 ×ˢ uIcc a b` and applies the dominated differentiation theorem for
interval integrals. -/
theorem hasDerivAt_intervalIntegral_of_continuous {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {F F' : ℝ → ℝ → E}
    (hF : Continuous (fun p : ℝ × ℝ ↦ F p.1 p.2))
    (hF' : Continuous (fun p : ℝ × ℝ ↦ F' p.1 p.2))
    (hd : ∀ s t, HasDerivAt (fun s ↦ F s t) (F' s t) s) (a b x : ℝ) :
    HasDerivAt (fun s ↦ ∫ t in a..b, F s t) (∫ t in a..b, F' x t) x := by
  obtain ⟨C, hC⟩ := ((isCompact_closedBall x 1).prod (isCompact_uIcc (a := a)
      (b := b))).exists_bound_of_continuousOn
    hF'.continuousOn
  have hFs : ∀ s, Continuous (F s) := fun s ↦ hF.comp (continuous_const.prodMk continuous_id)
  have hF's : Continuous (F' x) := hF'.comp (continuous_const.prodMk continuous_id)
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
      (bound := fun _ ↦ C)
    (Metric.ball_mem_nhds x one_pos) (Filter.Eventually.of_forall fun s ↦
        (hFs s).aestronglyMeasurable)
    ((hFs x).intervalIntegrable a b) hF's.aestronglyMeasurable ?_ intervalIntegrable_const ?_).2
  · exact Filter.Eventually.of_forall fun t ht s hs ↦
      hC (s, t) ⟨Metric.ball_subset_closedBall hs, Set.uIoc_subset_uIcc ht⟩
  · exact Filter.Eventually.of_forall fun t _ s _ ↦ hd s t

/-- For real `L` and `r` with `r + L ≠ 0`, the function `r ↦ (r + L)⁻¹` has derivative
`-((r + L)⁻¹ ^ 2)` at `r`. -/
theorem hasDerivAt_inv_add_const {L r : ℝ} (h : r + L ≠ 0) :
    HasDerivAt (fun r : ℝ ↦ (r + L)⁻¹) (-((r + L)⁻¹) ^ 2) r := by
  have := ((hasDerivAt_id' r).add_const L).inv h
  exact this.congr_deriv (by field_simp)

/-- For real `L`, `r`, `s₀` with `s₀ * r + L ≠ 0`, the function `s ↦ s * r / (s * r + L)` has
derivative `r * L / (s₀ * r + L) ^ 2` at `s₀`. -/
theorem hasDerivAt_mul_div_mul_add (L r s₀ : ℝ) (hne : s₀ * r + L ≠ 0) :
    HasDerivAt (fun s : ℝ ↦ s * r / (s * r + L)) (r * L / (s₀ * r + L) ^ 2) s₀ := by
  have h : HasDerivAt (fun s : ℝ ↦ s * r / (s * r + L))
      ((1 * r * (s₀ * r + L) - s₀ * r * (1 * r)) / (s₀ * r + L) ^ 2) s₀ :=
    ((hasDerivAt_id' s₀).mul_const r).div (((hasDerivAt_id' s₀).mul_const r).add_const L) hne
  exact h.congr_deriv (by field_simp; ring)

/-- For `x : ℝ × ℝ` with `0 < x.1 ^ 2 + x.2 ^ 2`, the function
`t ↦ -2 * x.1 * t / (x.1 ^ 2 + t ^ 2)` has derivative
`-2 * x.1 * (x.1 ^ 2 - x.2 ^ 2) / (x.1 ^ 2 + x.2 ^ 2) ^ 2` at `x.2`. -/
theorem hasDerivAt_mul_div_sq_add_sq (x : ℝ × ℝ) (hx : 0 < x.1 ^ 2 + x.2 ^ 2) :
    HasDerivAt (fun t ↦ -2 * x.1 * t / (x.1 ^ 2 + t ^ 2))
      (-2 * x.1 * (x.1 ^ 2 - x.2 ^ 2) / (x.1 ^ 2 + x.2 ^ 2) ^ 2) x.2 := by
  refine (((hasDerivAt_id' x.2).const_mul (-2 * x.1)).fun_div
    ((hasDerivAt_pow 2 x.2).const_add (x.1 ^ 2)) hx.ne').congr_deriv ?_
  have := hx.ne'
  field_simp
  ring

/-- For `x : ℝ × ℝ` with `0 < x.2`, the function
`t ↦ x.1 * (x.1 ^ 2 - t ^ 2) / (t * (x.1 ^ 2 + t ^ 2))` has derivative
`x.1 * (x.2 ^ 4 - 4 * x.1 ^ 2 * x.2 ^ 2 - x.1 ^ 4) / (x.2 ^ 2 * (x.1 ^ 2 + x.2 ^ 2) ^
2)` at `x.2`. -/
theorem hasDerivAt_mul_sq_sub_sq_div_mul (x : ℝ × ℝ) (hx : 0 < x.2) :
    HasDerivAt (fun t ↦ x.1 * (x.1 ^ 2 - t ^ 2) / (t * (x.1 ^ 2 + t ^ 2)))
      (x.1 * (x.2 ^ 4 - 4 * x.1 ^ 2 * x.2 ^ 2 - x.1 ^ 4) / (x.2 ^ 2 * (x.1 ^ 2 + x.2 ^ 2) ^ 2))
          x.2 := by
  have h2 : x.2 ≠ 0 := hx.ne'
  have h3 : x.1 ^ 2 + x.2 ^ 2 ≠ 0 := by positivity
  have hq : x.2 * (x.1 ^ 2 + x.2 ^ 2) ≠ 0 := mul_ne_zero h2 h3
  refine ((((hasDerivAt_pow 2 x.2).const_sub (x.1 ^ 2)).const_mul x.1).fun_div
    ((hasDerivAt_id' x.2).mul ((hasDerivAt_pow 2 x.2).const_add (x.1 ^ 2))) hq).congr_deriv ?_
  simp only [Pi.mul_apply]
  field_simp
  ring

/-- For `x : ℝ × ℝ` with `0 < x.2`, the function `t ↦ -2 * t ^ 2 / (t ^ 2 + x.2 ^ 2)` has derivative
`-4 * x.1 * x.2 ^ 2 / (x.1 ^ 2 + x.2 ^ 2) ^ 2` at `x.1`. -/
theorem hasDerivAt_neg_sq_div_sq_add_sq (x : ℝ × ℝ) (hx : 0 < x.2) :
    HasDerivAt (fun t ↦ -2 * t ^ 2 / (t ^ 2 + x.2 ^ 2))
      (-4 * x.1 * x.2 ^ 2 / (x.1 ^ 2 + x.2 ^ 2) ^ 2) x.1 := by
  have hq : x.1 ^ 2 + x.2 ^ 2 ≠ 0 := by positivity
  refine (((hasDerivAt_pow 2 x.1).const_mul (-2)).fun_div
    ((hasDerivAt_pow 2 x.1).add_const (x.2 ^ 2)) hq).congr_deriv ?_
  field_simp
  ring

/-- For real `o`, `d`, `x`, the complex-valued function `x ↦ (((x - o) / d : ℝ) : ℂ)` of a real
variable has derivative `((1 / d : ℝ) : ℂ)` at `x`, with no assumption that `d ≠ 0`. -/
theorem hasDerivAt_ofReal_sub_div_const (o d : ℝ) (x : ℝ) :
    HasDerivAt (fun x : ℝ ↦ (((x - o) / d : ℝ) : ℂ)) (((1 / d : ℝ)) : ℂ) x := by
  have h : HasDerivAt (fun x : ℝ ↦ (x - o) / d) (1 / d) x :=
      ((hasDerivAt_id x).sub_const o).div_const d
  exact h.ofReal_comp

/-- For real `s₀` and `σ`, the function `x ↦ 1 - Real.exp (-(x - s₀))` has derivative
`Real.exp (-(σ - s₀))` at `σ`. -/
theorem hasDerivAt_one_sub_exp_neg_sub (s₀ σ : ℝ) :
    HasDerivAt (fun x : ℝ ↦ 1 - exp (-(x - s₀))) (exp (-(σ - s₀))) σ := by
  have h : HasDerivAt (fun x : ℝ ↦ 1 - exp (-(x - s₀))) (-(exp (-(σ - s₀)) * -1)) σ :=
    (((hasDerivAt_id' σ).sub_const s₀).neg.exp).const_sub 1
  exact h.congr_deriv (by ring)

/-- For every real `a`, the function `t ↦ Real.sin (a * t)` has derivative `a` at the point `0`. -/
theorem hasDerivAt_sin_const_mul_zero (a : ℝ) : HasDerivAt (fun t : ℝ ↦ Real.sin (a * t)) a 0 := by
  have := ((hasDerivAt_id (0 : ℝ)).const_mul a).sin
  simpa using this

/-- For `t < T`, the function `τ ↦ (T - τ) ^ (-(1 / 2 : ℝ))` has at `t` the derivative
`(1 / 2) * ((T - t) ^ (-(1 / 2 : ℝ)) * (T - t) ^ (-(1 / 2 : ℝ)) * (T - t) ^ (-(1 / 2 :
ℝ)))`, that is one half of the cube of `(T - t) ^ (-(1 / 2 : ℝ))`. -/
theorem hasDerivAt_sub_rpow_neg_half (T t : ℝ) (ht : t < T) :
    HasDerivAt (fun τ : ℝ ↦ (T - τ) ^ (-(1 / 2 : ℝ)))
      ((1 / 2 : ℝ) * ((T - t) ^ (-(1 / 2 : ℝ)) * (T - t) ^ (-(1 / 2 : ℝ)) *
          (T - t) ^ (-(1 / 2 : ℝ)))) t := by
  have hp : 0 < T - t := sub_pos.2 ht
  have h1 : HasDerivAt (fun τ : ℝ ↦ T - τ) (0 - 1) t :=
    (hasDerivAt_const t T).sub (hasDerivAt_id' t)
  have h2 := h1.rpow_const (p := -(1 / 2 : ℝ)) (Or.inl hp.ne')
  convert h2 using 1
  rw [show (-(1 / 2 : ℝ)) - 1 = -(1 / 2) + -(1 / 2) + -(1 / 2) by norm_num, rpow_add hp,
    rpow_add hp]
  ring

/-- For `x : ℝ × ℝ` with `0 < x.1 ^ 2 + x.2 ^ 2`, the function
`t ↦ (x.2 ^ 2 - t ^ 2) / (t ^ 2 + x.2 ^ 2)` has derivative
`-4 * x.1 * x.2 ^ 2 / (x.1 ^ 2 + x.2 ^ 2) ^ 2` at `x.1`. -/
theorem hasDerivAt_sub_sq_div_add_sq (x : ℝ × ℝ) (hx : 0 < x.1 ^ 2 + x.2 ^ 2) :
    HasDerivAt (fun t ↦ (x.2 ^ 2 - t ^ 2) / (t ^ 2 + x.2 ^ 2))
      (-4 * x.1 * x.2 ^ 2 / (x.1 ^ 2 + x.2 ^ 2) ^ 2) x.1 := by
  refine (((hasDerivAt_pow 2 x.1).const_sub (x.2 ^ 2)).fun_div
    ((hasDerivAt_pow 2 x.1).add_const (x.2 ^ 2)) hx.ne').congr_deriv ?_
  have := hx.ne'
  field_simp
  ring

/-- For polynomials `P`, `q` over `ℂ` with `derivative q = C c` and a natural `o`, the `o`-th
derivative of the composition is
`derivative^[o] (P.comp q) = C (c ^ o) * (derivative^[o] P).comp q`. -/
theorem iterate_derivative_comp_linear (P q : Polynomial ℂ) (c : ℂ) (hq : derivative q = C c)
    (o : ℕ) : derivative^[o] (P.comp q) = C (c ^ o) * (derivative^[o] P).comp q := by
  induction o with
  | zero => simp
  | succ o ih =>
    rw [Function.iterate_succ_apply', ih, derivative_C_mul, derivative_comp, hq,
      Function.iterate_succ_apply', pow_succ, C_mul]
    ring

/-- For real `C` and `s ≠ 0`, the function `g = fun y ↦ C + Real.log y / 2` satisfies
`s * deriv g s = 1 / 2`, `s ^ 2 * iteratedDeriv 2 g s = -1 / 2` and
`s ^ 3 * iteratedDeriv 3 g s = 1`. The first two derivatives of `g` are `y ↦ y⁻¹ / 2` and
`y ↦ -(y ^ 2)⁻¹ / 2`, and the third derivative at `s` is `(s ^ 3)⁻¹`. -/
theorem iteratedDeriv_const_add_log_div_two (C s : ℝ) (hs : s ≠ 0) :
    s * deriv (fun y ↦ C + Real.log y / 2) s = 1 / 2 ∧
    s ^ 2 * iteratedDeriv 2 (fun y ↦ C + Real.log y / 2) s = -1 / 2 ∧
    s ^ 3 * iteratedDeriv 3 (fun y ↦ C + Real.log y / 2) s = 1 := by
  have h1 : deriv (fun y ↦ C + Real.log y / 2) = fun y ↦ y⁻¹ / 2 := by
    funext y
    rw [deriv_const_add, deriv_div_const, Real.deriv_log]
  have h2 : deriv (fun y : ℝ ↦ y⁻¹ / 2) = fun y ↦ -(y ^ 2)⁻¹ / 2 := by
    funext y
    rw [deriv_div_const, deriv_inv]
  have e2 : iteratedDeriv 2 (fun y ↦ C + Real.log y / 2) = fun y ↦ -(y ^ 2)⁻¹ / 2 := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, h1, h2]
  have h3 : HasDerivAt (fun y : ℝ ↦ -(y ^ 2)⁻¹ / 2)
      (-(-(((2 : ℕ) : ℝ) * s ^ (2 - 1)) / (s ^ 2) ^ 2) / 2) s :=
    (((hasDerivAt_pow 2 s).inv (pow_ne_zero 2 hs)).neg).div_const 2
  have e3 : iteratedDeriv 3 (fun y ↦ C + Real.log y / 2) s = (s ^ 3)⁻¹ := by
    rw [iteratedDeriv_succ, e2]
    rw [h3.deriv]
    norm_num
    field_simp
  refine ⟨?_, ?_, ?_⟩
  · rw [h1]
    field_simp
  · rw [e2]
    field_simp
  · rw [e3]
    field_simp

/-- Mean value inequality with right derivatives on a symmetric interval: if `g : ℝ → ℂ` is
continuous, has derivative `g' s` at every `s` within `Set.Ici s`, and `‖g' s‖ ≤ M` whenever
`|s| ≤ R`, then `‖g a - g b‖ ≤ M * |a - b|` for all `a` and `b` with `|a| ≤ R` and `|b| ≤ R`. The
proof applies the mean value inequality for right derivatives on the interval between `a` and `b`.
-/
theorem norm_sub_le_of_deriv_right_le {g g' : ℝ → ℂ} {R M : ℝ} (hc : Continuous g)
    (hd : ∀ s, HasDerivWithinAt g (g' s) (Ici s) s) (hb : ∀ s, |s| ≤ R → ‖g' s‖ ≤ M) :
    ∀ a b : ℝ, |a| ≤ R → |b| ≤ R → ‖g a - g b‖ ≤ M * |a - b| := by
  have key : ∀ a b : ℝ, b ≤ a → |a| ≤ R → |b| ≤ R → ‖g a - g b‖ ≤ M * |a - b| := by
    intro a b hba ha hb'
    have h := norm_image_sub_le_of_norm_deriv_right_le_segment (a := b) (b := a) hc.continuousOn
      (fun s _ ↦ hd s) (fun s hs ↦ hb s (abs_le.mpr ⟨le_trans (abs_le.mp hb').1 hs.1,
        le_trans hs.2.le (abs_le.mp ha).2⟩)) a ⟨hba, le_rfl⟩
    rwa [abs_of_nonneg (sub_nonneg.mpr hba)]
  intro a b ha hb'
  rcases le_total b a with h | h
  · exact key a b h ha hb'
  · rw [norm_sub_rev, abs_sub_comm]
    exact key b a h hb' ha

/-- First-order Taylor bound with the base point at the end of the step: if `g : ℝ → E` is `C^2`
with values in a real normed space and `‖deriv (deriv g) t‖ ≤ C` whenever `|t - s| ≤ |δ|`, then
`‖g (s + δ) - δ • deriv g (s + δ) - g s‖ ≤ δ ^ 2 / 2 * C`. The proof applies the mean value
inequality on `[0, 1]` to `u ↦ g (s + u * δ) - (u * δ) • deriv g (s + u * δ) - g s`, whose
derivative is `-((u * δ ^ 2) • deriv (deriv g) (s + u * δ))`. -/
theorem norm_taylor_remainder_at_end_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E)
    (hg : ContDiff ℝ 2 g) (s δ C : ℝ)
    (hC : ∀ t, |t - s| ≤ |δ| → ‖deriv (deriv g) t‖ ≤ C) :
    ‖g (s + δ) - δ • deriv g (s + δ) - g s‖ ≤ δ ^ 2 / 2 * C := by
  have hg' : ContDiff ℝ (1 + 1) g := by rw [one_add_one_eq_two]; exact hg
  have h1 : ContDiff ℝ 1 (deriv g) := ((contDiff_succ_iff_deriv (n := 1)).1 hg').2.2
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hd : Differentiable ℝ (deriv g) := h1.differentiable (by norm_num)
  set F : ℝ → E := fun u ↦ g (s + u * δ) - (u * δ) • deriv g (s + u * δ) - g s with hF
  set F' : ℝ → E := fun u ↦ -((u * δ ^ 2) • deriv (deriv g) (s + u * δ)) with hF'
  have hder : ∀ u, HasDerivAt F (F' u) u := by
    intro u
    have ha : HasDerivAt (fun u : ℝ ↦ s + u * δ) δ u := by
      simpa using ((hasDerivAt_id u).mul_const δ).const_add s
    have hg1 : HasDerivAt (fun u ↦ g (s + u * δ)) (δ • deriv g (s + u * δ)) u :=
      (hgd (s + u * δ)).hasDerivAt.scomp u ha
    have hg2 : HasDerivAt ((deriv g) ∘ (fun u : ℝ ↦ s + u * δ))
        (δ • deriv (deriv g) (s + u * δ)) u :=
      HasDerivAt.scomp u (hd (s + u * δ)).hasDerivAt ha
    have hm : HasDerivAt (fun u : ℝ ↦ u * δ) δ u := by simpa using (hasDerivAt_id u).mul_const δ
    have hp := hm.smul hg2
    have := (hg1.sub hp).sub_const (g s)
    refine this.congr_deriv ?_
    change _ = -((u * δ ^ 2) • deriv (deriv g) (s + u * δ))
    simp only [Function.comp_apply]
    module
  have hcont : Continuous F := by
    refine Continuous.sub (Continuous.sub ?_ ?_) continuous_const
    · exact hgd.continuous.comp (by fun_prop)
    · exact (continuous_id.mul continuous_const).smul (hd.continuous.comp (by fun_prop))
  have hB : ∀ u ∈ Set.Icc (0:ℝ) 1, ‖F u‖ ≤ δ ^ 2 * C * u ^ 2 / 2 := by
    intro u hu
    refine image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := 1) (f := F) (f' := F')
      (B := fun u ↦ δ ^ 2 * C * u ^ 2 / 2) (B' := fun u ↦ δ ^ 2 * C * u)
      hcont.continuousOn (fun x _ ↦ (hder x).hasDerivWithinAt) ?_
      (fun x ↦ ?_) (fun x hx ↦ ?_) hu
    · simp [hF]
    · have := ((hasDerivAt_pow 2 x).const_mul (δ ^ 2 * C)).div_const 2
      refine this.congr_deriv ?_
      first | (norm_num; done) | (norm_num; ring)
    · have hx0 : 0 ≤ x := hx.1
      have hx1 : x ≤ 1 := hx.2.le
      have hb : ‖deriv (deriv g) (s + x * δ)‖ ≤ C := by
        apply hC
        rw [show s + x * δ - s = x * δ by ring, abs_mul, abs_of_nonneg hx0]
        nlinarith [abs_nonneg δ]
      simp only [hF', norm_neg, norm_smul, Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity : 0 ≤ x * δ ^ 2)]
      calc x * δ ^ 2 * ‖deriv (deriv g) (s + x * δ)‖ ≤ x * δ ^ 2 * C :=
            mul_le_mul_of_nonneg_left hb (by positivity)
        _ = δ ^ 2 * C * x := by ring
  have := hB 1 ⟨zero_le_one, le_rfl⟩
  simpa [hF] using this.trans (le_of_eq (by ring))

/-- Let `p` be a real polynomial, `x` a real number and `c = 1 - X ^ (2 * k + 2)`. Then
`(derivative (c * p)).eval x ^ 2 = (1 - x ^ (2 * k + 2)) ^ 2 * (derivative p).eval x ^ 2 + (2 * k +
2) * (2 * k + 1) * (x ^ (2 * k) - x ^ (2 * (2 * k + 1))) * p.eval x ^ 2 + (derivative (c *
derivative c * p ^ 2)).eval x`. Here `derivative` is the formal derivative of polynomials. -/
theorem sq_eval_derivative_sub_X_pow_mul (k : ℕ) (p : ℝ[X]) (x : ℝ) :
    (derivative ((1 - X ^ (2 * k + 2)) * p)).eval x ^ 2
      = (1 - x ^ (2 * k + 2)) ^ 2 * (derivative p).eval x ^ 2
        + (2 * k + 2) * (2 * k + 1) * (x ^ (2 * k) - x ^ (2 * (2 * k + 1))) * p.eval x ^ 2
        + (derivative ((1 - X ^ (2 * k + 2)) * derivative (1 - X ^ (2 * k + 2)) * p ^ 2)).eval x :=
            by
  simp [derivative_mul, derivative_pow]
  ring

/-- Let `f g : ℝ → E` take values in a real normed space, with `f` having derivative `g σ` within
`segment ℝ t s` at every point `σ` of that segment and `g` continuous on it. With the points
`x k = t + (k / (N + 1)) * (s - t)` of the uniform partition, the sums
`∑ k ∈ Finset.range (N + 1), (f (x (k + 1)) - f (x k) - ((s - t) / (N + 1)) • g (x
k))` tend to `0` as `N →
∞`. Proof idea: by the uniform continuity of `g` and the mean value inequality, each term has norm
at most `η * |s - t| / (N + 1)` once `N` is large, for any given `η > 0`. -/
theorem tendsto_sum_partition_sub_smul_deriv_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    {f g : ℝ → E} {t s : ℝ}
    (hder : ∀ σ ∈ segment ℝ t s, HasDerivWithinAt f (g σ) (segment ℝ t s) σ)
    (hg : ContinuousOn g (segment ℝ t s)) :
    Tendsto (fun N : ℕ ↦ ∑ k ∈ Finset.range (N + 1),
      (f (t + (((k + 1 : ℕ) : ℝ) / (N + 1)) * (s - t)) - f (t + ((k : ℝ) / (N + 1)) * (s - t))
        - ((s - t) / (N + 1)) • g (t + ((k : ℝ) / (N + 1)) * (s - t)))) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set η : ℝ := ε / (2 * (|s - t| + 1)) with hη
  have hηpos : 0 < η := by positivity
  have huc := (show IsCompact (segment ℝ t s) by
    rw [segment_eq_uIcc]; exact isCompact_uIcc).uniformContinuousOn_of_continuous hg
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδc⟩ := huc η hηpos
  obtain ⟨N0, hN0⟩ := exists_nat_gt (|s - t| / δ)
  refine ⟨N0, fun N hN ↦ ?_⟩
  have hNpos : (0 : ℝ) < N + 1 := by positivity
  have hstep : |s - t| / (N + 1) < δ := by
    rw [div_lt_iff₀ hNpos]
    have : |s - t| / δ < N + 1 := by
      have : (N0 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    rw [div_lt_iff₀ hδ] at this
    linarith
  have hterm : ∀ k ∈ Finset.range (N + 1),
      ‖f (t + (((k + 1 : ℕ) : ℝ) / (N + 1)) * (s - t)) - f (t + ((k : ℝ) / (N + 1)) * (s - t))
        - ((s - t) / (N + 1)) • g (t + ((k : ℝ) / (N + 1)) * (s - t))‖ ≤ η * (|s - t| / (N + 1)) :=
            by
    intro k hk
    have hk' : k + 1 ≤ N + 1 := Finset.mem_range.1 hk
    set a := t + ((k : ℝ) / (N + 1)) * (s - t) with ha
    set b := t + (((k + 1 : ℕ) : ℝ) / (N + 1)) * (s - t) with hb
    have haI : a ∈ segment ℝ t s := add_div_mul_sub_mem_segment t s N k (by omega)
    have hbI : b ∈ segment ℝ t s := add_div_mul_sub_mem_segment t s N (k + 1) hk'
    have hJ : segment ℝ a b ⊆ segment ℝ t s := (convex_segment t s).segment_subset haI hbI
    have hba : b - a = (s - t) / (N + 1) := by
      rw [ha, hb]; push_cast; field_simp; ring
    have hφ : ∀ τ ∈ segment ℝ a b, HasDerivWithinAt (fun τ ↦ f τ - τ • g a) (g τ - g a)
        (segment ℝ a b) τ := by
      intro τ hτ
      have h1 := (hder τ (hJ hτ)).mono hJ
      have h2 : HasDerivWithinAt (fun τ : ℝ ↦ τ • g a) ((1 : ℝ) • g a) (segment ℝ a b) τ :=
        (hasDerivWithinAt_id τ _).smul_const (g a)
      rw [one_smul] at h2
      exact h1.sub h2
    have hbound : ∀ τ ∈ segment ℝ a b, ‖g τ - g a‖ ≤ η := by
      intro τ hτ
      have hdist : dist τ a < δ := by
        rw [Real.dist_eq]
        rw [segment_eq_uIcc] at hτ
        calc |τ - a| ≤ |b - a| := abs_sub_left_of_mem_uIcc hτ
          _ = |s - t| / (N + 1) := by rw [hba, abs_div, abs_of_pos hNpos]
          _ < δ := hstep
      have := hδc τ (hJ hτ) a haI hdist
      rw [dist_eq_norm] at this
      exact this.le
    have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hφ hbound (convex_segment a b)
      (left_mem_segment ℝ a b) (right_mem_segment ℝ a b)
    have heq : (f b - b • g a) - (f a - a • g a) = f b - f a - ((s - t) / (N + 1)) • g a := by
      rw [← hba, sub_smul]; abel
    rw [heq, hba, Real.norm_eq_abs, abs_div, abs_of_pos hNpos] at hmv
    exact hmv
  rw [dist_zero_right]
  calc _ ≤ ∑ k ∈ Finset.range (N + 1), η * (|s - t| / (N + 1)) := by
        refine (norm_sum_le _ _).trans ?_
        exact Finset.sum_le_sum hterm
    _ = η * |s - t| := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; field_simp
    _ < ε := by
        rw [hη]
        have h3 : 0 < |s - t| + 1 := by positivity
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [abs_nonneg (s - t)]

/-- Chain rule for the square: if `g : ℝ → ℝ` has derivative `g'` at `r ^ 2`, then `x ↦ g (x ^ 2)`
has derivative `g' * (2 * r)` at `r`. -/
theorem hasDerivAt_comp_sq {g : ℝ → ℝ} {g' r : ℝ} (hg : HasDerivAt g g' (r ^ 2)) :
    HasDerivAt (fun x : ℝ ↦ g (x ^ 2)) (g' * (2 * r)) r :=
  hg.comp (h := fun x : ℝ ↦ x ^ 2) r (hasDerivAt_sq r)

/-- Chain rule for the square, with the derivative given as a function: if `f : ℝ → ℝ` has
derivative `f' (s ^ 2)` at `s ^ 2`, then `x ↦ f (x ^ 2)` has derivative `f' (s ^ 2) * (2 * s)` at
`s`. A case of `PDE.Analysis.hasDerivAt_comp_sq`. -/
theorem hasDerivAt_comp_sq_apply {f f' : ℝ → ℝ} {s : ℝ} (h : HasDerivAt f (f' (s ^ 2)) (s ^ 2)) :
    HasDerivAt (fun x : ℝ ↦ f (x ^ 2)) (f' (s ^ 2) * (2 * s)) s :=
  hasDerivAt_comp_sq h

/-- Let `G : ℝ × ℝ → ℂ` be `C^1`. Then for all real `a b x`, `fun s ↦ ∫ t in a..b, G (s, t)` has
derivative `∫ t in a..b, fderiv ℝ G (x, t) (1, 0)` at `x`. The statement also records that, for all
`s` and `t`, `fun s ↦ G (s, t)` has derivative `fderiv ℝ G (s, t) (1, 0)` at `s`. -/
theorem hasDerivAt_intervalIntegral_of_contDiff {G : ℝ × ℝ → ℂ} (hG : ContDiff ℝ 1 G) (a b x : ℝ) :
    HasDerivAt (fun s ↦ ∫ t in a..b, G (s, t)) (∫ t in a..b, fderiv ℝ G (x, t) (1, 0)) x ∧
      ∀ s t, HasDerivAt (fun s ↦ G (s, t)) (fderiv ℝ G (s, t) (1, 0)) s := by
  have hd : ∀ s t, HasDerivAt (fun s ↦ G (s, t)) (fderiv ℝ G (s, t) (1, 0)) s := fun s t ↦
    ((hG.differentiable (by norm_num) (s, t)).hasFDerivAt).comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (hasDerivAt_const s t))
  refine ⟨hasDerivAt_intervalIntegral_of_continuous (F := fun s t ↦ G (s, t))
      (F' := fun s t ↦ fderiv ℝ G (s, t) (1, 0))
    hG.continuous ((hG.continuous_fderiv (by norm_num)).clm_apply continuous_const) hd a b x, hd⟩

/-- For real `L` and `r` with `r + L ≠ 0`, the function `r ↦ ((r + L)⁻¹) ^ 2` has derivative
`-(2 * ((r + L)⁻¹) ^ 3)` at `r`. -/
theorem hasDerivAt_inv_add_const_sq {L r : ℝ} (h : r + L ≠ 0) :
    HasDerivAt (fun r : ℝ ↦ ((r + L)⁻¹) ^ 2) (-(2 * ((r + L)⁻¹) ^ 3)) r := by
  have := (hasDerivAt_inv_add_const h).pow 2
  exact this.congr_deriv (by push_cast; ring)

/-- For real `rate`, `c` and `t > -c`, the function `s ↦ rate / 2 * (c + s)⁻¹` has derivative
`-(rate / 2) * ((c + t) ^ 2)⁻¹` at `t`. -/
theorem hasDerivAt_mul_inv_const_add (rate c : ℝ) (t : ℝ) (ht : t ∈ Set.Ioi (-c)) :
    HasDerivAt (fun s ↦ rate / 2 * (c + s)⁻¹) (-(rate / 2) * ((c + t) ^ 2)⁻¹) t := by
  have hpos : 0 < c + t := neg_lt_iff_pos_add'.mp ht
  refine ((((hasDerivAt_id' t).const_add c).inv hpos.ne').const_mul (rate / 2)).congr_deriv ?_
  ring

/-- For real `rate` and `c` with `0 < c`, and for `t > -c`, the function
`s ↦ rate / 2 * Real.log (1 + s / c)` has derivative `rate / 2 * (c + t)⁻¹` at `t`. This is the
chain rule for the logarithm, with `1 + t / c = (c + t) / c > 0`. -/
theorem hasDerivAt_mul_log_one_add_div (rate c : ℝ) (hc : 0 < c) (t : ℝ) (ht : t ∈ Set.Ioi (-c)) :
    HasDerivAt (fun s ↦ rate / 2 * Real.log (1 + s / c)) (rate / 2 * (c + t)⁻¹) t := by
  have hpos : 0 < c + t := neg_lt_iff_pos_add'.mp ht
  have hrw : 1 + t / c = (c + t) / c := by field_simp
  have hne : 1 + t / c ≠ 0 := by
    rw [hrw]
    exact (div_pos hpos hc).ne'
  have h1 : HasDerivAt (fun s ↦ 1 + s / c) (1 / c) t :=
    ((hasDerivAt_id' t).div_const c).const_add 1
  refine ((h1.log hne).const_mul (rate / 2)).congr_deriv ?_
  rw [hrw]
  have hne' : c + t ≠ 0 := hpos.ne'
  have hcne : c ≠ 0 := hc.ne'
  field_simp

/-- For real `rate`, `c` and `t > -c`, the function `s ↦ -(rate / 2) * ((c + s) ^ 2)⁻¹` has
derivative `rate * ((c + t) ^ 3)⁻¹` at `t`. -/
theorem hasDerivAt_neg_mul_inv_sq_const_add (rate c : ℝ) (t : ℝ) (ht : t ∈ Set.Ioi (-c)) :
    HasDerivAt (fun s ↦ -(rate / 2) * ((c + s) ^ 2)⁻¹) (rate * ((c + t) ^ 3)⁻¹) t := by
  have hpos : 0 < c + t := neg_lt_iff_pos_add'.mp ht
  refine (((((hasDerivAt_id' t).const_add c).pow 2).inv (pow_pos hpos 2).ne').const_mul
      (-(rate / 2))).congr_deriv ?_
  have hne' : c + t ≠ 0 := hpos.ne'
  simp only [Pi.pow_apply]
  field_simp
  ring

/-- For every natural number `n` and real `r`, the function `y ↦ (y : ℂ) ^ n` of the real variable
`y` has derivative `n * (r : ℂ) ^ (n - 1)` at `r`. -/
theorem hasDerivAt_ofReal_pow (n : ℕ) (r : ℝ) : HasDerivAt (fun y : ℝ ↦ (y : ℂ) ^ n)
    ((n : ℂ) * (r : ℂ) ^ (n - 1)) r :=
  (hasDerivAt_pow n (r : ℂ)).comp_ofReal

/-- If `f : ℝ → ℂ` has derivative `f'` at `0`, then its real part `s ↦ (f s).re` has derivative
`f'.re` at `0`. -/
theorem hasDerivAt_re_of_hasDerivAt_zero {f : ℝ → ℂ} {f' : ℂ} (hf : HasDerivAt f f' 0) :
    HasDerivAt (fun s ↦ (f s).re) f'.re 0 := by
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hf

/-- For real `k` and `θ`, the function `s ↦ exp (k * (θ + s) * I)` of the real variable `s`, with
values in `ℂ`, has derivative `exp (k * θ * I) * (k * I)` at `0`. -/
theorem hasDerivAt_cexp_mul_add_mul_I_zero (k θ : ℝ) :
    HasDerivAt (fun s : ℝ ↦ Complex.exp ((k * (θ + s) : ℝ) * Complex.I))
      (Complex.exp ((k * θ : ℝ) * Complex.I) * ((k : ℂ) * Complex.I)) 0 := by
  have h1 := (((hasDerivAt_id (0 : ℝ)).const_add θ).const_mul k).ofReal_comp.mul_const Complex.I
  have h2 := h1.cexp
  refine (h2.congr_deriv (by simp)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s ↦ ?_)
  simp

/-- For every real `θ`, the function `s ↦ sin (θ + s)` has derivative `cos θ` at `0`. -/
theorem hasDerivAt_sin_const_add_zero (θ : ℝ) : HasDerivAt (fun s : ℝ ↦ Real.sin (θ + s))
    (Real.cos θ) 0 := by
  have h := (Real.hasDerivAt_sin (θ + 0)).comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).const_add θ)
  rw [add_zero, mul_one] at h
  exact h

/-- For every real `θ`, the function `s ↦ cos (θ + s)` has derivative `-sin θ` at `0`. -/
theorem hasDerivAt_cos_const_add_zero (θ : ℝ) : HasDerivAt (fun s : ℝ ↦ Real.cos (θ + s))
    (-Real.sin θ) 0 := by
  have h := (Real.hasDerivAt_cos (θ + 0)).comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).const_add θ)
  rw [add_zero, mul_one] at h
  exact h

/-- The derivative of `Real.smoothTransition` is a continuous function on `ℝ`. -/
theorem continuous_deriv_smoothTransition : Continuous (deriv Real.smoothTransition) :=
  (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl

/-- The function `Real.smoothTransition` is differentiable on `ℝ`. -/
theorem differentiable_smoothTransition : Differentiable ℝ Real.smoothTransition :=
  (Real.smoothTransition.contDiff (n := 1)).differentiable (by simp)

/-- For a complex polynomial `P` in two variables and real `t`, `x`, the function
`s ↦ MvPolynomial.eval ![t, s] P` of the real variable `s` has at `x` the derivative
`MvPolynomial.eval ![t, x] (MvPolynomial.pderiv 1 P)`. This is
`hasDerivAt_eval_pderiv_one` at the complex number `t`. -/
theorem hasDerivAt_eval_ofReal_pderiv_one (P : MvPolynomial (Fin 2) ℂ) (t x : ℝ) :
    HasDerivAt (fun s : ℝ ↦ MvPolynomial.eval ![(t : ℂ), (s : ℂ)] P)
      (MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (MvPolynomial.pderiv 1 P)) x :=
          hasDerivAt_eval_pderiv_one P (t : ℂ) x

/-- For real `a` and `σ`, the function `s ↦ exp (a * s * I)` of the real variable `s`, with values
in `ℂ`, has derivative `exp (a * σ * I) * (a * I)` at `σ`. By the chain rule for the complex
exponential. -/
theorem hasDerivAt_cexp_mul_mul_I (a σ : ℝ) :
    HasDerivAt (fun s : ℝ ↦ Complex.exp (((a * s : ℝ) : ℂ) * Complex.I))
      (Complex.exp (((a * σ : ℝ) : ℂ) * Complex.I) * ((a : ℂ) * Complex.I)) σ := by
  have h1 : HasDerivAt (fun s : ℝ ↦ ((a * s : ℝ) : ℂ)) (a : ℂ) σ := by
    have h2 := ((hasDerivAt_id σ).const_mul a).ofReal_comp
    simpa using h2
  exact (h1.mul_const Complex.I).cexp

/-- If `f : ℝ → ℂ` is zero on a neighbourhood of `t`, then `deriv f t = 0`. -/
theorem deriv_eq_zero_of_eventuallyEq_zero {f : ℝ → ℂ} {t : ℝ} (h : f =ᶠ[nhds t] fun _ ↦ 0) :
    deriv f t = 0 := by
  rw [h.deriv_eq]
  exact deriv_const t 0

/-- For a polynomial `P : MvPolynomial (Fin 2) ℂ` and real `x`, `t`, the function
`s ↦ MvPolynomial.eval ![(s : ℂ), (x : ℂ)] P` of a real variable has derivative
`MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (MvPolynomial.pderiv 0 P)` at `t`. This is
`hasDerivAt_eval_pderiv_zero` at the complex number `x`. -/
theorem hasDerivAt_eval_ofReal_pderiv_zero (P : MvPolynomial (Fin 2) ℂ) (x t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ MvPolynomial.eval ![(s : ℂ), (x : ℂ)] P)
      (MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (MvPolynomial.pderiv 0 P)) t :=
          hasDerivAt_eval_pderiv_zero P (x : ℂ) t

end PDE.Analysis
