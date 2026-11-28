/-
Authors: Levent Alpöge, Tristan Buckmaster

The lemmas of this file, except setIntegral_mul_comp_eq_sum_triPoly, come from modules of the Lean
package of the paper "Finite-time blow-up for the Navier–Stokes equations"
(https://github.com/tristanbuckmaster/navier-stokes, folder lean/, commit ad53419),
where they were steps of longer proofs. They were included in BlowupZoo
(https://github.com/lean-dojo/BlowupZoo, folder AtlasCandidates/) with the permission of the
authors (20 November 2026) and moved here from there; the file NOTICE of this repository records it.
The lemma setIntegral_mul_comp_eq_sum_triPoly was written for this library, with the authors' proof
of two of its cases.
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Data.List.GetD
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Tactic.Linarith.NNRealPreprocessor
public import Mathlib.Topology.Algebra.Polynomial
public import PDE.Analysis.Scalar.Definitions
public import PDE.Analysis.Scalar.Sums

set_option linter.style.header false

/-!
# Polynomials of a triangular array of coefficients

The lemmas show that polynomial functions are continuous, are determined by their values on an
interval and are closed under sums over a list; that the monomials up to a degree lie in the span of
the first polynomials of a triangular array with nonzero diagonal; and that a function in that span
is its own expansion in the family when the family is orthonormal on an interval, also under an
integral over a product set and on a strip cut into segments. The proofs are inductions on the
degree and calculations with finite sums, and the expansions under an integral use the linearity of
the integral.

## Main results

* `PDE.Analysis.pow_eq_sum_mul_triPoly`: If `co j j ≠ 0` for all `j`, then for every `i ≤ Q` there
  are real `a j` with `x ^ i = ∑ j : Fin (Q + 1), a j * triPoly co j x` for all `x`.
* `PDE.Analysis.continuous_of_isPolyFun`: A polynomial function `f : ℝ → ℝ` (`IsPolyFun f`) is
  continuous.
* `PDE.Analysis.isPolyFun_ext_of_eqOn_Icc`: Two polynomial functions that agree on an interval
  `[a, b]` with `a < b` agree everywhere.
* `PDE.Analysis.isPolyFun_list_sum`: The sum over a list of polynomial functions is a polynomial
  function: if `G p` is a polynomial function for every `p` in the list `l`, so is
  `s ↦ ∑ p in l, G p s`.
* `PDE.Analysis.isPolyFun_sum_range_mul_pow`: For an array of coefficients `t` and every `d`, the
  function `s ↦ ∑ i ∈ range (d + 1), t d i * s ^ i` is a polynomial function.
* `PDE.Analysis.mem_span_triPoly_of_eq_sum_pow`: If `C d d ≠ 0` for all `d` and
  `t u = ∑ i ∈ range (m + 1), a i * u ^ (i + j)` with `m + j ≤ M`, then `t` lies in the real span of
  `triPoly C 0, …, triPoly C M`.
* `PDE.Analysis.pow_eq_sum_mul_triPoly_of_pos`: If the diagonal coefficients `cf j j` are positive,
  then for `i ≤ d` the monomial `r ^ i` is a combination of `triPoly cf 0, …, triPoly cf d`: there
  are real `a j` with `r ^ i = ∑ j, a j * triPoly cf j r` for all `r`.
* `PDE.Analysis.setIntegral_mul_comp_eq_sum_triPoly`: Let `triPoly C 0, …, triPoly C M` be
  orthonormal for the integral over `[lo, hi]` and `t` in their real span. For a compact set `K` of
  a Hausdorff space whose open sets are measurable, a measure `μ`, a continuous `π : X → ℝ` and `g`
  integrable on `K`, the integral of `g x * t (π x)` over `K` is the sum over `d` of
  `∫ v in [lo, hi], t v * triPoly C d v` times the integral of `g x * triPoly C d (π x)`. The next
  lemma and its twin for the second projection are its cases.
* `PDE.Analysis.setIntegral_prod_mul_fst_eq_sum_triPoly`: Let `triPoly C 0, …, triPoly C M` be
  orthonormal for the integral over `[lo, hi]`, `t` in their real span, `A` compact and `g`
  integrable on `[lo, hi] × A`. Then the integral of `g p * t p.1` over `[lo, hi] × A` is the sum
  over `d` of the coefficient `∫ v in [lo, hi], t v * triPoly C d v` times the integral of
  `g p * triPoly C d p.1`.

There are 9 further lemmas of the same kind.

## References

* Levent Alpöge and Tristan Buckmaster, the Lean package of the paper "Finite-time blow-up for the
  Navier–Stokes equations", <https://github.com/tristanbuckmaster/navier-stokes>, folder `lean/`,
  commit `ad53419`: the lemmas of this module and their proofs, adapted to this library. See
  `NOTICE` for attribution and permission.
  The lemma `setIntegral_mul_comp_eq_sum_triPoly` is not from the package: it was written for this
  library, with the authors' proof of two of its cases, `setIntegral_prod_mul_fst_eq_sum_triPoly`
  and `setIntegral_prod_mul_snd_eq_sum_triPoly`, for a continuous map in place of a projection.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PDE.Analysis

/-- A polynomial function `f : ℝ → ℝ` (`IsPolyFun f`) is continuous. -/
theorem continuous_of_isPolyFun {f : ℝ → ℝ} (h : IsPolyFun f) : Continuous f := by
  obtain ⟨P, hP⟩ := h
  have : f = fun s ↦ P.eval s := funext hP
  rw [this]
  exact P.continuous

/-- Let `triPoly C 0, …, triPoly C M` be orthonormal for the integral over `[lo, hi]`. A function
`t` in their real span is its own expansion:
`t u = ∑ d, (∫ v in [lo, hi], t v * triPoly C d v) * triPoly C d u`. -/
theorem eq_sum_integral_mul_triPoly_of_orthonormal (C : ℕ → ℕ → ℝ) (lo hi : ℝ) (M : ℕ)
    (horth : ∀ d d', d ≤ M → d' ≤ M →
      ∫ u in Icc lo hi, triPoly C d u * triPoly C d' u = if d = d' then 1 else 0)
    (t : ℝ → ℝ) (ht : t ∈ Submodule.span ℝ (range fun d : Fin (M + 1) ↦ triPoly C d)) (u : ℝ) :
    t u = ∑ d : Fin (M + 1), (∫ v in Icc lo hi, t v * triPoly C d v) * triPoly C d u := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 ht
  have hpt : ∀ v, t v = ∑ d : Fin (M + 1), c d * triPoly C d v := by
    intro v
    rw [← hc]
    simp [Finset.sum_apply]
  have hcoef : ∀ d' : Fin (M + 1), ∫ v in Icc lo hi, t v * triPoly C d' v = c d' := by
    intro d'
    simp_rw [hpt, Finset.sum_mul]
    rw [integral_finsetSum]
    · simp_rw [mul_assoc, integral_const_mul]
      rw [Finset.sum_eq_single d']
      · rw [horth _ _ (Nat.lt_succ_iff.1 d'.isLt) (Nat.lt_succ_iff.1 d'.isLt)]
        simp
      · intro b _ hb
        rw [horth _ _ (Nat.lt_succ_iff.1 b.isLt) (Nat.lt_succ_iff.1 d'.isLt),
            ite_eq_right (fun h ↦ hb (Fin.ext h))]
        simp
      · simp
    · intro d _
      have h1 := continuous_triPoly C d
      have h2 := continuous_triPoly C d'
      exact Continuous.integrableOn_Icc (by fun_prop)
  rw [hpt u]
  simp_rw [hcoef]

/-- Two polynomial functions that agree on an interval `[a, b]` with `a < b` agree everywhere. -/
theorem isPolyFun_ext_of_eqOn_Icc {f g : ℝ → ℝ} (hf : IsPolyFun f) (hg : IsPolyFun g) {a b : ℝ}
    (hab : a < b)
    (h : ∀ s ∈ Set.Icc a b, f s = g s) (s : ℝ) : f s = g s := by
  obtain ⟨P, hP⟩ := hf
  obtain ⟨Q, hQ⟩ := hg
  have hz : P - Q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply (Set.Icc_infinite hab).mono
    intro u hu
    change Polynomial.IsRoot (P - Q) u
    rw [Polynomial.IsRoot.def, Polynomial.eval_sub, ← hP, ← hQ, h u hu, sub_self]
  rw [hP, hQ, ← sub_eq_zero, ← Polynomial.eval_sub, hz, Polynomial.eval_zero]

/-- The sum over a list of polynomial functions is a polynomial function: if `G p` is a polynomial
function for every `p` in the list `l`, so is `s ↦ ∑ p in l, G p s`. -/
theorem isPolyFun_list_sum {β : Type*} (l : List β) (G : β → ℝ → ℝ)
    (hG : ∀ p ∈ l, IsPolyFun (G p)) :
    IsPolyFun (fun s ↦ (l.map (fun p ↦ G p s)).sum) := by
  induction l with
  | nil => exact ⟨0, fun s ↦ by simp⟩
  | cons p ps ih =>
    obtain ⟨P, hP⟩ := hG p List.mem_cons_self
    obtain ⟨Q, hQ⟩ := ih (fun q hq ↦ hG q (List.mem_cons_of_mem _ hq))
    exact ⟨P + Q, fun s ↦ by
      have h2 := hQ s
      beta_reduce at h2 ⊢
      rw [List.map_cons, List.sum_cons, hP, h2, Polynomial.eval_add]⟩

/-- For an array of coefficients `t` and every `d`, the function
`s ↦ ∑ i ∈ range (d + 1), t d i * s ^ i` is a polynomial function. -/
theorem isPolyFun_sum_range_mul_pow (t : ℕ → ℕ → ℝ) (d : ℕ) : IsPolyFun
    (fun s ↦ ∑ i ∈ Finset.range (d + 1), t d i * s ^ i) :=
  ⟨∑ i ∈ Finset.range (d + 1), Polynomial.C (t d i) * Polynomial.X ^ i, fun s ↦ by
    simp [Polynomial.eval_finsetSum]⟩

/-- If `co j j ≠ 0` for all `j`, then for every `i ≤ Q` there are real `a j` with
`x ^ i = ∑ j : Fin (Q + 1), a j * triPoly co j x` for all `x`. -/
theorem pow_eq_sum_mul_triPoly (co : ℕ → ℕ → ℝ) (hco : ∀ j, co j j ≠ 0) (Q : ℕ) :
    ∀ i ≤ Q, ∃ a : Fin (Q + 1) → ℝ, ∀ x : ℝ, x ^ i = ∑ j : Fin (Q + 1), a j * triPoly co j x := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    choose a ha using fun k : Fin i ↦ ih k k.2 (by omega)
    refine ⟨fun j ↦ (co i i)⁻¹ * ((if (j : ℕ) = i then 1 else 0) - ∑ k : Fin i, co i k * a k j),
        ?_⟩
    intro x
    have hP : triPoly co i x = co i i * x ^ i + ∑ k : Fin i, co i k * x ^ (k : ℕ) := by
      rw [triPoly, Finset.sum_range_succ, ← Fin.sum_univ_eq_sum_range (fun k ↦ co i k * x ^ k)]
      ring
    have h1 : ∑ j : Fin (Q + 1), (if (j : ℕ) = i then (1 : ℝ) else 0) * triPoly co j x =
        triPoly co i x := by
      rw [Finset.sum_eq_single (⟨i, by omega⟩ : Fin (Q + 1))]
      · simp
      · intro b _ hb
        have : (b : ℕ) ≠ i := fun h ↦ hb (Fin.ext h)
        simp [this]
      · simp
    have h2 : ∀ k : Fin i, ∑ j : Fin (Q + 1), a k j * triPoly co j x = x ^ (k : ℕ) :=
        fun k ↦ (ha k x).symm
    calc x ^ i = (co i i)⁻¹ * (triPoly co i x - ∑ k : Fin i, co i k * x ^ (k : ℕ)) := by
          rw [hP]; field_simp [hco i]; ring
      _ = (co i i)⁻¹ * (∑ j : Fin (Q + 1), (if (j : ℕ) = i then (1 : ℝ) else 0) * triPoly co j x
            - ∑ k : Fin i, co i k * ∑ j : Fin (Q + 1), a k j * triPoly co j x) := by
          rw [h1]; simp only [h2]
      _ = ∑ j : Fin (Q + 1), (co i i)⁻¹ * ((if (j : ℕ) = i then 1 else 0) - ∑ k : Fin i,
          co i k * a k j)
            * triPoly co j x := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin i)))]
          rw [← Finset.sum_sub_distrib, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun j _ ↦ ?_)
          rw [mul_assoc, sub_mul, Finset.sum_mul]
          simp only [mul_assoc]

/-- If `P j r = ∑ i ∈ range (j + 1), a j i * r ^ i` for all `j` and `r`, and `a j j ≠ 0` for all
`j`, then for every `i ≤ Q` the monomial `r ↦ r ^ i` lies in the real span of `P 0, …, P Q`.
By strong induction on `i`: `r ^ i` is `P i` minus lower monomials, divided by `a i i`. -/
theorem pow_mem_span_of_triangular (P : ℕ → ℝ → ℝ) (a : ℕ → ℕ → ℝ)
    (hP : ∀ j r, P j r = ∑ i ∈ Finset.range (j + 1), a j i * r ^ i) (ha : ∀ j, a j j ≠ 0) (Q : ℕ) :
    ∀ i, i ≤ Q → (fun r : ℝ ↦ r ^ i) ∈ Submodule.span ℝ
        (Set.range (fun j : Fin (Q + 1) ↦ P j)) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    have hPi : (P i) ∈ Submodule.span ℝ (Set.range (fun j : Fin (Q + 1) ↦ P j)) :=
      Submodule.subset_span ⟨⟨i, by omega⟩, rfl⟩
    have heq : (fun r : ℝ ↦ r ^ i) =
        (a i i)⁻¹ • (P i - ∑ t ∈ Finset.range i, a i t • (fun r : ℝ ↦ r ^ t)) := by
      funext r
      simp only [Pi.smul_apply, Pi.sub_apply, Finset.sum_apply, smul_eq_mul, hP,
          Finset.sum_range_succ]
      rw [add_sub_cancel_left, inv_mul_cancel_left₀ (ha i)]
    rw [heq]
    refine Submodule.smul_mem _ _ (Submodule.sub_mem _ hPi (Submodule.sum_mem _ fun t ht ↦
      Submodule.smul_mem _ _ (ih t (Finset.mem_range.mp ht) ?_)))
    have := Finset.mem_range.mp ht
    omega

/-- If `C d d ≠ 0` for all `d`, then for `m ≤ M` the monomial `u ↦ u ^ m` lies in the real span of
`triPoly C 0, …, triPoly C M`. A case of `PDE.Analysis.pow_mem_span_of_triangular`. -/
theorem pow_mem_span_triPoly (C : ℕ → ℕ → ℝ) (hlead : ∀ d, C d d ≠ 0) (M : ℕ) :
    ∀ m ≤ M, (fun u : ℝ ↦ u ^ m) ∈ Submodule.span ℝ (range fun d : Fin (M + 1) ↦ triPoly C d) :=
  pow_mem_span_of_triangular (triPoly C) C (fun _ _ ↦ rfl) hlead M

/-- If the diagonal coefficients `cf j j` are positive, then for `i ≤ d` the monomial `r ↦ r ^ i`
lies in the real span of `triPoly cf 0, …, triPoly cf d`. A case of
`PDE.Analysis.pow_mem_span_of_triangular`. -/
theorem pow_mem_span_triPoly_of_pos (cf : ℕ → ℕ → ℝ) (hlead : ∀ j, 0 < cf j j) (d : ℕ) :
    ∀ i, i ≤ d → (fun r : ℝ ↦ r ^ i) ∈
      Submodule.span ℝ (Set.range fun j : Fin (d + 1) ↦ triPoly cf j) :=
  pow_mem_span_of_triangular (triPoly cf) cf (fun _ _ ↦ rfl) (fun j ↦ (hlead j).ne') d

/-- For `j ≤ Q`, the polynomial `triPoly rc j x` is the sum over `i : Fin (Q + 1)` of
`rc j i * x ^ i` for `i ≤ j` and of zero for `i > j`. -/
theorem triPoly_eq_sum_fin (rc : ℕ → ℕ → ℝ) {Q j : ℕ} (hj : j ≤ Q) (x : ℝ) :
    triPoly rc j x = ∑ i : Fin (Q + 1), (if (i : ℕ) ≤ j then rc j i else 0) * x ^ (i : ℕ) := by
  rw [triPoly, sum_range_succ_eq_sum_fin_ite _ hj]
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  split_ifs <;> simp

/-- If `C d d ≠ 0` for all `d` and `t u = ∑ i ∈ range (m + 1), a i * u ^ (i + j)` with `m + j ≤ M`,
then `t` lies in the real span of `triPoly C 0, …, triPoly C M`. -/
theorem mem_span_triPoly_of_eq_sum_pow (C : ℕ → ℕ → ℝ) (hlead : ∀ d, C d d ≠ 0) (M m j : ℕ)
    (hm : m + j ≤ M)
    (a : ℕ → ℝ) (t : ℝ → ℝ) (ht : ∀ u, t u = ∑ i ∈ Finset.range (m + 1), a i * u ^ (i + j)) :
    t ∈ Submodule.span ℝ (range fun d : Fin (M + 1) ↦ triPoly C d) := by
  have : t = ∑ i ∈ Finset.range (m + 1), a i • fun u : ℝ ↦ u ^ (i + j) := by
    funext u
    simp only [ht, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [this]
  refine Submodule.sum_mem _ fun i hi ↦ Submodule.smul_mem _ _
      (pow_mem_span_triPoly C hlead M _ ?_)
  have := Finset.mem_range.1 hi
  omega

/-- If the diagonal coefficients `cf j j` are positive, then for `i ≤ d` the monomial `r ^ i` is a
combination of `triPoly cf 0, …, triPoly cf d`: there are real `a j` with
`r ^ i = ∑ j, a j * triPoly cf j r` for all `r`. -/
theorem pow_eq_sum_mul_triPoly_of_pos (cf : ℕ → ℕ → ℝ) (hlead : ∀ j, 0 < cf j j) (d i : ℕ)
    (hi : i ≤ d) :
    ∃ a : Fin (d + 1) → ℝ, ∀ r : ℝ, r ^ i = ∑ j : Fin (d + 1), a j * triPoly cf j r := by
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1
      (pow_mem_span_triPoly_of_pos cf hlead d i hi)
  refine ⟨a, fun r ↦ ?_⟩
  have := congrFun ha r
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
  exact this.symm

/-- Let `triPoly C 0, …, triPoly C M` be orthonormal for the integral over `[lo, hi]` and `t` in
their real span. Let `K` be a compact set of a Hausdorff space `X` whose open sets are measurable,
`μ` a measure on `X`, `π : X → ℝ` continuous and `g : X → ℂ` integrable on `K`. Then the integral
of `g x * t (π x)` over `K` is the sum over `d` of the coefficient
`∫ v in [lo, hi], t v * triPoly C d v` times the integral of `g x * triPoly C d (π x)` over `K`. -/
theorem setIntegral_mul_comp_eq_sum_triPoly (C : ℕ → ℕ → ℝ) (lo hi : ℝ) (M : ℕ)
    (horth : ∀ d d', d ≤ M → d' ≤ M →
      ∫ u in Icc lo hi, triPoly C d u * triPoly C d' u = if d = d' then 1 else 0)
    (t : ℝ → ℝ) (ht : t ∈ Submodule.span ℝ (range fun d : Fin (M + 1) ↦ triPoly C d))
    {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {μ : Measure X} {K : Set X} (hK : IsCompact K) {π : X → ℝ} (hπ : Continuous π) (g : X → ℂ)
    (hg : IntegrableOn g K μ) :
    ∫ x in K, g x * ((t (π x) : ℝ) : ℂ) ∂μ =
      ∑ d : Fin (M + 1), (((∫ v in Icc lo hi, t v * triPoly C d v : ℝ)) : ℂ) *
        ∫ x in K, g x * ((triPoly C d (π x) : ℝ) : ℂ) ∂μ := by
  have h1 : ∀ x : X, g x * ((t (π x) : ℝ) : ℂ) = ∑ d : Fin (M + 1),
      (((∫ v in Icc lo hi, t v * triPoly C d v : ℝ)) : ℂ) *
        (g x * ((triPoly C d (π x) : ℝ) : ℂ)) := by
    intro x
    rw [eq_sum_integral_mul_triPoly_of_orthonormal C lo hi M horth t ht (π x), Complex.ofReal_sum,
        Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    rw [Complex.ofReal_mul]
    ring
  simp_rw [h1]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul]
  · intro d _
    have hc := continuous_triPoly C d
    exact (hg.mul_continuousOn (by fun_prop) hK).const_mul _

/-- Let `triPoly C 0, …, triPoly C M` be orthonormal for the integral over `[lo, hi]`, `t` in their
real span, `A` compact and `g` integrable on `[lo, hi] × A`. Then the integral of `g p * t p.1` over
`[lo, hi] × A` is the sum over `d` of the coefficient `∫ v in [lo, hi], t v * triPoly C d v` times
the integral of `g p * triPoly C d p.1`. This is `setIntegral_mul_comp_eq_sum_triPoly` for the
first projection. -/
theorem setIntegral_prod_mul_fst_eq_sum_triPoly (C : ℕ → ℕ → ℝ) (lo hi : ℝ) (M : ℕ)
    (horth : ∀ d d', d ≤ M → d' ≤ M →
      ∫ u in Icc lo hi, triPoly C d u * triPoly C d' u = if d = d' then 1 else 0)
    (t : ℝ → ℝ) (ht : t ∈ Submodule.span ℝ (range fun d : Fin (M + 1) ↦ triPoly C d))
    (A : Set ℝ) (hA : IsCompact A) (g : ℝ × ℝ → ℂ) (hg : IntegrableOn g (Icc lo hi ×ˢ A)) :
    ∫ p in Icc lo hi ×ˢ A, g p * ((t p.1 : ℝ) : ℂ) =
      ∑ d : Fin (M + 1), (((∫ v in Icc lo hi, t v * triPoly C d v : ℝ)) : ℂ) *
        ∫ p in Icc lo hi ×ˢ A, g p * ((triPoly C d p.1 : ℝ) : ℂ) :=
  setIntegral_mul_comp_eq_sum_triPoly C lo hi M horth t ht (isCompact_Icc.prod hA) continuous_fst
    g hg

/-- Let `triPoly C 0, …, triPoly C M` be orthonormal for the integral over `[lo, hi]`, `t` in their
real span, `A` compact and `g` integrable on `A × [lo, hi]`. Then the integral of `g p * t p.2` over
`A × [lo, hi]` is the sum over `d` of the coefficient `∫ v in [lo, hi], t v * triPoly C d v` times
the integral of `g p * triPoly C d p.2`. This is `setIntegral_mul_comp_eq_sum_triPoly` for the
second projection. -/
theorem setIntegral_prod_mul_snd_eq_sum_triPoly (C : ℕ → ℕ → ℝ) (lo hi : ℝ) (M : ℕ)
    (horth : ∀ d d', d ≤ M → d' ≤ M →
      ∫ u in Icc lo hi, triPoly C d u * triPoly C d' u = if d = d' then 1 else 0)
    (t : ℝ → ℝ) (ht : t ∈ Submodule.span ℝ (range fun d : Fin (M + 1) ↦ triPoly C d))
    (A : Set ℝ) (hA : IsCompact A) (g : ℝ × ℝ → ℂ) (hg : IntegrableOn g (A ×ˢ Icc lo hi)) :
    ∫ p in A ×ˢ Icc lo hi, g p * ((t p.2 : ℝ) : ℂ) =
      ∑ d : Fin (M + 1), (((∫ v in Icc lo hi, t v * triPoly C d v : ℝ)) : ℂ) *
        ∫ p in A ×ˢ Icc lo hi, g p * ((triPoly C d p.2 : ℝ) : ℂ) :=
  setIntegral_mul_comp_eq_sum_triPoly C lo hi M horth t ht (hA.prod isCompact_Icc) continuous_snd
    g hg

/-- For coefficients `t : ℕ → ℕ → ℝ` and a degree `d`, the polynomial function
`s ↦ ∑ i ∈ Finset.range (d + 1), t d i * s ^ i` is continuous on `ℝ`. This is `continuous_triPoly`
with `triPoly t d` written out. -/
theorem continuous_sum_range_mul_pow (t : ℕ → ℕ → ℝ) (d : ℕ) : Continuous
    (fun s : ℝ ↦ ∑ i ∈ Finset.range (d + 1),
    t d i * s ^ i) := continuous_triPoly t d

/-- If `a < b` and the complex coefficients `s j`, `j : Fin d`, satisfy `∑ j, s j * r ^ j = 0` for
every real `r` in `(a, b)`, then `s = 0`. A polynomial with infinitely many roots is zero. -/
theorem eq_zero_of_sum_mul_pow_Ioo {d : ℕ} (s : Fin d → ℂ) {a b : ℝ} (hab : a < b)
    (h : ∀ r ∈ Set.Ioo a b, ∑ j, s j * (r : ℂ) ^ (j : ℕ) = 0) : s = 0 := by
  classical
  set P : Polynomial ℂ := ∑ j : Fin d, Polynomial.C (s j) * Polynomial.X ^ (j : ℕ) with hP
  have hev : ∀ r : ℝ, P.eval (r : ℂ) = ∑ j, s j * (r : ℂ) ^ (j : ℕ) := by
    intro r
    rw [hP, Polynomial.eval_finsetSum]
    simp
  have hP0 : P = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono ?_ ((Set.Ioo_infinite hab).image
      (fun x _ y _ hxy ↦ Complex.ofReal_injective hxy))
    rintro _ ⟨r, hr, rfl⟩
    change P.IsRoot (r : ℂ)
    rw [Polynomial.IsRoot, hev]
    exact h r hr
  funext j
  have hc := congrArg (fun P : Polynomial ℂ ↦ P.coeff (j : ℕ)) hP0
  simp only [hP, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_zero] at hc
  rw [Finset.sum_eq_single j (fun j' _ hj' ↦ ite_eq_right (fun h ↦ hj' (Fin.ext h.symm)))
    (fun h ↦ absurd (Finset.mem_univ j) h)] at hc
  simpa using hc

/-- If `a < b`, `e < f` and the complex coefficients `c i`, `i : Fin d1 × Fin d2`, satisfy
`∑ i, c i * r ^ i.1 * z ^ i.2 = 0` for all real `r` in `(a, b)` and `z` in `(e, f)`, then
`c = 0`. The statement for one variable is applied first in `r`, then in `z`. -/
theorem eq_zero_of_sum_pow_pow_Ioo {d1 d2 : ℕ} (c : Fin d1 × Fin d2 → ℂ) {a b e f : ℝ}
    (hab : a < b) (hef : e < f)
    (h : ∀ r ∈ Set.Ioo a b, ∀ z ∈ Set.Ioo e f, ∑ i, c i * (r : ℂ) ^ (i.1 : ℕ) *
        (z : ℂ) ^ (i.2 : ℕ) = 0) :
    c = 0 := by
  have h1 : ∀ z ∈ Set.Ioo e f, ∀ j, ∑ l, c (j, l) * (z : ℂ) ^ (l : ℕ) = 0 := by
    intro z hz
    have := eq_zero_of_sum_mul_pow_Ioo (fun j ↦ ∑ l, c (j, l) * (z : ℂ) ^ (l : ℕ)) hab
        (fun r hr ↦ by
      rw [← h r hr z hz, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ ↦ by ring)
    exact fun j ↦ congrFun this j
  funext i
  have := eq_zero_of_sum_mul_pow_Ioo (fun l ↦ c (i.1, l)) hef (fun z hz ↦ h1 z hz i.1)
  exact congrFun this i.2

end PDE.Analysis
