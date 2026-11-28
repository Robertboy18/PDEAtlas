/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.FDeriv.PartialDeriv.HigherNormSq.Leibniz
public import Mathlib.RingTheory.PowerSeries.Derivative
import PDE.Analysis.Analytic.PowerSeries.Nonnegative

/-!
# The chain rule for coordinate square norms

## Motivation

How large are the derivatives of a composition `g ∘ P`, in terms of the derivatives of `g` and
of `P`, in a form that still closes after `k` differentiations with constants of size `k!`?

## The idea

Faà di Bruno's formula writes `Dᵏ(g ∘ P)` as a sum over partitions. We do not need the formula,
only a bound, and the bound is easiest to state with a generating series. Let `p` be the formal
power series whose coefficient of `tʲ` is `|DʲP(x)|/j!` for `j ≥ 1` (`coordinateNormSeries P x`).
Then

`|Dᵏ(g ∘ P)(x)|/k! ≤ ∑ₘ ‖Dᵐg(P x)‖/m! · [tᵏ] pᵐ`.

The proof is an induction on `k`. One derivative of `g ∘ P` is `(Dg ∘ P)(∂ᵢ P)`, the Leibniz rule
for the coordinate norm bounds its derivatives of order `k`, the induction hypothesis is applied
to `Dg`, and the coefficient identity behind `(pᵐ⁺¹)' = (m + 1) pᵐ p'` collects the terms. The
norms of `g` are operator norms of `iteratedFDeriv` on an arbitrary normed space, so no
coordinates are needed in the middle space.

## Main results

* `iteratedCoordinateNorm_comp_le`: the bound above, for all `g` that are `C^k` at `P x` and all
  `P` that are `C^k` at `x`.

## Relations

The proof iterates `iteratedCoordinateNorm_clm_apply_le`. Mathlib's `norm_iteratedFDeriv_comp_le`
is the bound `‖Dᵏ(g ∘ f)(x)‖ ≤ k! C Dᵏ` for `C^k` maps `g` and `f` with `‖Dⁱg(f x)‖ ≤ C` for
`i ≤ k` and `‖Dⁱf(x)‖ ≤ Dⁱ` for `1 ≤ i ≤ k`. The series form here keeps the factorials of
both functions, which is what bounds of size `k!` need.

## What stays open

Faà di Bruno's formula itself, with its coefficients, is not stated for these norms.

## References

* S. Blatt, *On the analyticity of solutions to non-linear elliptic partial differential
  equations*, arXiv:2009.08762v2, 2024, Proposition 2.8 and Lemma 2.9 (the higher order chain
  rule as a sum with positive coefficients, compared with the one-variable case).
  <https://arxiv.org/abs/2009.08762>
-/

@[expose] public noncomputable section

open scoped ContDiff Topology
open PowerSeries (coeff)

universe u v

variable {n : ℕ}

/-- The powers of a real power series with nonnegative coefficients have nonnegative
coefficients. This is `MvPowerSeries.coeff_pow_nonneg` for one variable. -/
theorem PowerSeries.coeff_pow_nonneg {p : PowerSeries ℝ} (hp : ∀ j, 0 ≤ coeff j p) (m j : ℕ) :
    0 ≤ coeff j (p ^ m) :=
  MvPowerSeries.coeff_pow_nonneg (f := p) (fun a ↦ by
    rw [Finsupp.unique_single a]
    exact hp (a ())) m _

/-- The coefficient form of `(pᵐ⁺¹)' = (m + 1) pᵐ p'`, for power series over a commutative
semiring. -/
theorem PowerSeries.succ_mul_coeff_succ_pow_succ {R : Type*} [CommSemiring R] (p : PowerSeries R)
    (m k : ℕ) :
    ((k : R) + 1) * coeff (k + 1) (p ^ (m + 1)) =
      ((m : R) + 1) * ∑ l ∈ Finset.range (k + 1),
        (((k - l : ℕ) : R) + 1) * coeff l (p ^ m) * coeff (k - l + 1) p := by
  have h := congrArg (coeff k) (PowerSeries.derivative_pow p (m + 1))
  rw [PowerSeries.coeff_derivative, Nat.add_sub_cancel, mul_assoc, ← nsmul_eq_mul, map_nsmul,
    nsmul_eq_mul, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b ↦ coeff a (p ^ m) * coeff b (PowerSeries.derivative p))] at h
  simp only [PowerSeries.coeff_derivative] at h
  rw [mul_comm, h]
  push_cast
  congr 1
  exact Finset.sum_congr rfl fun l _ ↦ by ring

namespace PDE

/-- The series of the coordinate norms of positive order of `P` at `x`: the coefficient of `tʲ`
is `|DʲP(x)|/j!` for `j ≥ 1`, and the constant coefficient is zero. -/
def coordinateNormSeries {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (P : ℝ^n → E)
    (x : ℝ^n) : PowerSeries ℝ :=
  PowerSeries.mk fun j ↦ if j = 0 then 0 else iteratedCoordinateNorm j P x / j.factorial

section Series

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (P : ℝ^n → E) (x : ℝ^n)

/-- The constant coefficient of `coordinateNormSeries P x` is zero. -/
@[simp]
theorem coeff_zero_coordinateNormSeries : coeff 0 (coordinateNormSeries P x) = 0 := by
  simp [coordinateNormSeries]

/-- For `j ≥ 1` the coefficient of `tʲ` in `coordinateNormSeries P x` is `|DʲP(x)|/j!`. -/
theorem coeff_coordinateNormSeries {j : ℕ} (hj : j ≠ 0) :
    coeff j (coordinateNormSeries P x) = iteratedCoordinateNorm j P x / j.factorial := by
  simp [coordinateNormSeries, hj]

/-- The coefficients of `coordinateNormSeries P x` are nonnegative. -/
theorem coeff_coordinateNormSeries_nonneg (j : ℕ) : 0 ≤ coeff j (coordinateNormSeries P x) := by
  rcases eq_or_ne j 0 with rfl | hj
  · simp
  · rw [coeff_coordinateNormSeries P x hj]
    exact div_nonneg (iteratedCoordinateNorm_nonneg _ _ _) (Nat.cast_nonneg _)

end Series

/-- The chain rule bound with the middle space and the target in one universe; the general
statement is `iteratedCoordinateNorm_comp_le`. -/
private theorem iteratedCoordinateNorm_comp_le_aux {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (P : ℝ^n → E) (x : ℝ^n) (k : ℕ) :
    ∀ {G : Type (max u v)} [NormedAddCommGroup G] [NormedSpace ℝ G] {g : E → G},
      ContDiffAt ℝ k g (P x) → ContDiffAt ℝ k P x →
      iteratedCoordinateNorm k (g ∘ P) x ≤ k.factorial * ∑ m ∈ Finset.range (k + 1),
        ‖iteratedFDeriv ℝ m g (P x)‖ / m.factorial * coeff k (coordinateNormSeries P x ^ m) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro G _ _ g hg hP
    rcases k with _ | k
    · simp [norm_iteratedFDeriv_zero]
    set p := coordinateNormSeries P x with hp
    have hpn : ∀ j, 0 ≤ coeff j p := coeff_coordinateNormSeries_nonneg P x
    have hk1 : (1 : WithTop ℕ∞) ≤ ((k + 1 : ℕ) : WithTop ℕ∞) := by
      exact_mod_cast Nat.le_add_left 1 k
    have hPk : ContDiffAt ℝ k P x := hP.of_le (by exact_mod_cast Nat.le_succ k)
    have hgd : ContDiffAt ℝ k (fderiv ℝ g) (P x) := hg.fderiv_right (by simp)
    have hT : ContDiffAt ℝ k (fun y ↦ fderiv ℝ g (P y)) x := hgd.comp x hPk
    -- one derivative of `g ∘ P` is `(Dg ∘ P) (∂ᵢ P)` near `x`
    have hchain (i : Fin n) : ∂[i] (g ∘ P) =ᶠ[𝓝 x] fun y ↦ fderiv ℝ g (P y) ((∂[i] P) y) := by
      filter_upwards [hP.eventually_differentiableAt hk1,
        hP.continuousAt.eventually (hg.eventually_differentiableAt hk1)] with y hPy hgy
      simp only [partialDeriv, fderiv_comp y hgy hPy, ContinuousLinearMap.comp_apply]
    -- the Leibniz rule for each coordinate derivative, then Minkowski over `i`
    have hstep (i : Fin n) : iteratedCoordinateNorm k (∂[i] (g ∘ P)) x ≤
        ∑ l ∈ Finset.range (k + 1), (k.choose l : ℝ) *
          iteratedCoordinateNorm l (fun y ↦ fderiv ℝ g (P y)) x *
            iteratedCoordinateNorm (k - l) (∂[i] P) x := by
      rw [(hchain i).iteratedCoordinateNorm k]
      exact iteratedCoordinateNorm_clm_apply_le k hT (hP.partialDeriv i le_rfl)
    have hmink := sqrt_sum_sq_le_sum_mul_sqrt (Finset.range (k + 1))
      (c := fun l ↦ (k.choose l : ℝ) * iteratedCoordinateNorm l (fun y ↦ fderiv ℝ g (P y)) x)
      (u := fun l i ↦ iteratedCoordinateNorm (k - l) (∂[i] P) x)
      (fun i ↦ iteratedCoordinateNorm_nonneg k _ x)
      (fun l _ ↦ mul_nonneg (Nat.cast_nonneg _) (iteratedCoordinateNorm_nonneg _ _ _)) hstep
    simp only [← iteratedCoordinateNorm_succ] at hmink
    -- the induction hypothesis for `Dg`, with the sum over `m` extended to `m ≤ k`
    have hD (l : ℕ) (hl : l ∈ Finset.range (k + 1)) :
        iteratedCoordinateNorm l (fun y ↦ fderiv ℝ g (P y)) x ≤ l.factorial *
          ∑ m ∈ Finset.range (k + 1),
            ‖iteratedFDeriv ℝ (m + 1) g (P x)‖ / m.factorial * coeff l (p ^ m) := by
      have hlk : l ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
      have hle : ((l : ℕ) : WithTop ℕ∞) ≤ ((k : ℕ) : WithTop ℕ∞) := by exact_mod_cast hlk
      refine (ih l (Nat.lt_succ_of_le hlk) (g := fderiv ℝ g) (hgd.of_le hle)
        (hPk.of_le hle)).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      simp only [norm_iteratedFDeriv_fderiv]
      refine Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.mpr (Nat.succ_le_succ hlk)) fun m _ _ ↦ ?_
      exact mul_nonneg (div_nonneg (norm_nonneg _) (Nat.cast_nonneg _))
        (PowerSeries.coeff_pow_nonneg hpn m l)
    -- each term of the Leibniz sum in terms of the series
    have hterm (l : ℕ) (hl : l ∈ Finset.range (k + 1)) :
        (k.choose l : ℝ) * iteratedCoordinateNorm l (fun y ↦ fderiv ℝ g (P y)) x *
            iteratedCoordinateNorm (k - l + 1) P x ≤
          k.factorial * ∑ m ∈ Finset.range (k + 1),
            ‖iteratedFDeriv ℝ (m + 1) g (P x)‖ / m.factorial *
              ((((k - l : ℕ) : ℝ) + 1) * coeff l (p ^ m) * coeff (k - l + 1) p) := by
      have hlk : l ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
      have hfac : (k.choose l : ℝ) * l.factorial * (k - l).factorial = k.factorial := by
        exact_mod_cast Nat.choose_mul_factorial_mul_factorial hlk
      have hP1 : iteratedCoordinateNorm (k - l + 1) P x =
          (((k - l : ℕ) : ℝ) + 1) * (k - l).factorial * coeff (k - l + 1) p := by
        rw [hp, coeff_coordinateNormSeries P x (Nat.succ_ne_zero _), Nat.factorial_succ]
        push_cast
        field_simp
      calc (k.choose l : ℝ) * iteratedCoordinateNorm l (fun y ↦ fderiv ℝ g (P y)) x *
            iteratedCoordinateNorm (k - l + 1) P x
          ≤ (k.choose l : ℝ) * (l.factorial * ∑ m ∈ Finset.range (k + 1),
              ‖iteratedFDeriv ℝ (m + 1) g (P x)‖ / m.factorial * coeff l (p ^ m)) *
              iteratedCoordinateNorm (k - l + 1) P x :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hD l hl) (Nat.cast_nonneg _))
              (iteratedCoordinateNorm_nonneg _ _ _)
        _ = ((k.choose l : ℝ) * l.factorial * (k - l).factorial) *
              ∑ m ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ (m + 1) g (P x)‖ / m.factorial *
                ((((k - l : ℕ) : ℝ) + 1) * coeff l (p ^ m) * coeff (k - l + 1) p) := by
            rw [hP1, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
            exact Finset.sum_congr rfl fun m _ ↦ by ring
        _ = _ := by rw [hfac]
    -- sum over `l`, exchange the sums and use the coefficient identity
    calc iteratedCoordinateNorm (k + 1) (g ∘ P) x
        ≤ ∑ l ∈ Finset.range (k + 1), (k.choose l : ℝ) *
            iteratedCoordinateNorm l (fun y ↦ fderiv ℝ g (P y)) x *
              iteratedCoordinateNorm (k - l + 1) P x := hmink
      _ ≤ ∑ l ∈ Finset.range (k + 1), (k.factorial : ℝ) * ∑ m ∈ Finset.range (k + 1),
            ‖iteratedFDeriv ℝ (m + 1) g (P x)‖ / m.factorial *
              ((((k - l : ℕ) : ℝ) + 1) * coeff l (p ^ m) * coeff (k - l + 1) p) :=
          Finset.sum_le_sum hterm
      _ = (k.factorial : ℝ) * ∑ m ∈ Finset.range (k + 1),
            ‖iteratedFDeriv ℝ (m + 1) g (P x)‖ / m.factorial *
              ∑ l ∈ Finset.range (k + 1),
                (((k - l : ℕ) : ℝ) + 1) * coeff l (p ^ m) * coeff (k - l + 1) p := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          simp only [Finset.mul_sum]
      _ = ((k + 1).factorial : ℝ) * ∑ m ∈ Finset.range (k + 1),
            ‖iteratedFDeriv ℝ (m + 1) g (P x)‖ / (m + 1).factorial *
              coeff (k + 1) (p ^ (m + 1)) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ ↦ ?_
          have hid := PowerSeries.succ_mul_coeff_succ_pow_succ p m k
          have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
          have hsum : ∑ l ∈ Finset.range (k + 1),
              (((k - l : ℕ) : ℝ) + 1) * coeff l (p ^ m) * coeff (k - l + 1) p =
                ((k : ℝ) + 1) * coeff (k + 1) (p ^ (m + 1)) / ((m : ℝ) + 1) := by
            rw [hid]; field_simp
          rw [hsum, Nat.factorial_succ, Nat.factorial_succ]
          push_cast
          field_simp
      _ ≤ ((k + 1).factorial : ℝ) * ∑ m ∈ Finset.range (k + 1 + 1),
            ‖iteratedFDeriv ℝ m g (P x)‖ / m.factorial * coeff (k + 1) (p ^ m) := by
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          rw [Finset.sum_range_succ' _ (k + 1)]
          exact le_add_of_nonneg_right (mul_nonneg (div_nonneg (norm_nonneg _)
            (Nat.cast_nonneg _)) (PowerSeries.coeff_pow_nonneg hpn 0 (k + 1)))

/-- **Chain rule for the coordinate norm.** Let `g` be `C^k` at `P x` and `P` be `C^k` at `x`,
and let `p = coordinateNormSeries P x` be the series with coefficients `|DʲP(x)|/j!`, `j ≥ 1`.
Then `|Dᵏ(g ∘ P)(x)| ≤ k! ∑ₘ ‖Dᵐg(P x)‖/m! · [tᵏ] pᵐ`, the sum over `m ≤ k`. This is the
majorant form of Faà di Bruno's formula; the proof is an induction on `k` with the Leibniz rule
and the identity `(pᵐ⁺¹)' = (m + 1) pᵐ p'`. -/
theorem iteratedCoordinateNorm_comp_le {E : Type u} {G : Type v} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] (k : ℕ) {g : E → G}
    {P : ℝ^n → E} {x : ℝ^n} (hg : ContDiffAt ℝ k g (P x)) (hP : ContDiffAt ℝ k P x) :
    iteratedCoordinateNorm k (g ∘ P) x ≤ k.factorial * ∑ m ∈ Finset.range (k + 1),
      ‖iteratedFDeriv ℝ m g (P x)‖ / m.factorial * coeff k (coordinateNormSeries P x ^ m) := by
  -- lift the target to the universe of the middle space
  let e : ULift.{u, v} G ≃ₗᵢ[ℝ] G := LinearIsometryEquiv.ulift ℝ G
  have hge : ContDiffAt ℝ k (e.symm ∘ g) (P x) :=
    e.symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp (P x) hg
  have h := iteratedCoordinateNorm_comp_le_aux.{u, v} P x k hge hP
  have hnorm : iteratedCoordinateNorm k ((e.symm ∘ g) ∘ P) x =
      iteratedCoordinateNorm k (g ∘ P) x := by
    simp only [iteratedCoordinateNorm]
    exact congrArg Real.sqrt (iteratedCoordinateNormSq_linearIsometryEquiv_comp e.symm k (g ∘ P) x)
  simpa only [hnorm, e.symm.norm_iteratedFDeriv_comp_left g (P x)] using h

end PDE
