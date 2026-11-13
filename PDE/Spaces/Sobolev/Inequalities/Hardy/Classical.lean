/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Hardy.WeightedInterval
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Covering.Besicovitch

/-!
# Classical one-dimensional Hardy inequalities

Hardy's inequality on the half-line says that for `p > 1` and `u` vanishing at the origin,
`∫₀^∞ |u(x)/x|^p dx ≤ (p/(p-1))^p ∫₀^∞ |u'(x)|^p dx`. We prove the `L²` case, where
the constant is `4`, first for `C¹` functions on a finite interval `[ε, R]` with `0 < ε` that
vanish at both endpoints, then for compactly supported `C¹` functions on `(0, ∞)`.

Both interval results specialize `WeightedInterval` at `s = 1`. Integrating `u²/x² = -u² (x⁻¹)'` by
parts gives the identity `∫ u²/x² = 2 ∫ (u/x) u'`, and Cauchy–Schwarz on the right-hand side yields
`X ≤ 2 √X √Y`, hence `X ≤ 4Y`. The positive lower endpoint keeps `x⁻¹` smooth on the interval, and
the endpoint values remove both boundary terms. Passing to `(0, ∞)` uses only that a compact subset
of `(0, ∞)` lies in some `(ε, R)`.

We also record what is needed to realize `u ↦ u/x^j` as a bounded operator on `L²`:
division by `x^j` preserves continuity and compact support when the support stays away from
`0`, and the `L²` norm of such a quotient is an integral over `(0, ∞)`.

## Main results

* `hardy_interval_identity`, `hardy_interval`: the identity and the inequality with constant `4`
  on `[ε, R]` for `C¹` functions vanishing at both endpoints.
* `hardy_interval_iteratedDeriv`, `hardy_Ioi_iteratedDeriv_of_support_subset_Ioo`: the same for
  the `m`-th derivative of a `C^{m+1}` function, controlling `x⁻¹ f^{(m)}` by `f^{(m+1)}`.
* `hardy_Ioi_of_hasCompactSupport`: the half-line inequality on the smooth core `C¹_c((0, ∞))`,
  with no endpoints supplied by the caller.
* `memLp_div_pow_of_hasCompactSupport`, `norm_div_toLp_le_two_norm_deriv_toLp`: `u/x^j ∈ L²`,
  and the operator form `‖u/x‖₂ ≤ 2 ‖u'‖₂` on the smooth core.

## Implementation notes

The finite-interval statements assume `u ε = 0` and `u R = 0` directly rather than a support
condition, so that they apply to iterated derivatives whose supports are only known through
`tsupport_iteratedDeriv_subset`. The half-line statements take `HasCompactSupport u` together
with `tsupport u ⊆ Ioi 0`, which is exactly what a `TestFunctionOn 1 (HalfSpace.upper 1)`
provides after pullback to `ℝ`.

## References

* G. H. Hardy, J. E. Littlewood and G. Pólya, *Inequalities*, 2nd ed., Cambridge Mathematical
  Library, Cambridge University Press, 1988, Chapter IX, for Hardy's inequality in integral form
  with the constant `(p/(p-1))^p`.
* A. Kufner, L. Maligranda and L.-E. Persson, "The prehistory of the Hardy inequality",
  *Amer. Math. Monthly* 113 (2006), no. 8, 715-732, for the history of the inequality and its
  constant.
  <https://doi.org/10.1080/00029890.2006.11920356>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace


namespace Hardy

open Set MeasureTheory
open scoped ENNReal


/--
Finite-interval Hardy identity: for `0 < ε < R` and a `C¹` function `u` with `u ε = 0` and
`u R = 0`, `∫_ε^R u²/x² = 2 ∫_ε^R (u/x) u'`. The positive lower endpoint makes `x⁻¹`
differentiable on the interval, and the endpoint values remove both boundary terms.
-/
theorem hardy_interval_identity
    {u : ℝ → ℝ} {ε R : ℝ} (hε : 0 < ε) (hεR : ε < R)
    (hu : ContDiff ℝ 1 u) (huε : u ε = 0) (huR : u R = 0) :
    (∫ x in ε..R, u x ^ 2 / x ^ 2) =
      2 * ∫ x in ε..R, (u x / x) * deriv u x := by
  have h := weighted_hardy_interval_identity (s := 1) hε hεR hu huε huR
  norm_num [Real.rpow_neg, Real.rpow_two, Real.rpow_neg_one, div_eq_mul_inv] at h ⊢
  exact h

/--
Hardy's inequality on a positive finite interval: for `0 < ε < R` and a `C¹` function `u` with
`u ε = 0` and `u R = 0`, `∫_ε^R u²/x² ≤ 4 ∫_ε^R (u')²`. This is the case `s = 1` of
`weighted_hardy_interval`.
-/
theorem hardy_interval
    {u : ℝ → ℝ} {ε R : ℝ} (hε : 0 < ε) (hεR : ε < R)
    (hu : ContDiff ℝ 1 u) (huε : u ε = 0) (huR : u R = 0) :
    (∫ x in ε..R, u x ^ 2 / x ^ 2) ≤
      4 * ∫ x in ε..R, (deriv u x) ^ 2 := by
  have h := weighted_hardy_interval (s := 1) hε hεR (by norm_num) hu huε huR
  norm_num [Real.rpow_neg, Real.rpow_two, Real.rpow_neg_one, div_eq_mul_inv] at h ⊢
  exact h

/-- For `0 < ε < R` and a `C^{m+1}` function `f` whose `m`-th derivative vanishes at `ε` and at
`R`, `∫_ε^R (f^{(m)})²/x² ≤ 4 ∫_ε^R (f^{(m+1)})²`. -/
theorem hardy_interval_iteratedDeriv
    (m : ℕ) {f : ℝ → ℝ} {ε R : ℝ} (hε : 0 < ε) (hεR : ε < R)
    (hf : ContDiff ℝ (m + 1) f)
    (hfε : iteratedDeriv m f ε = 0) (hfR : iteratedDeriv m f R = 0) :
    (∫ x in ε..R, (iteratedDeriv m f x) ^ 2 / x ^ 2) ≤
      4 * ∫ x in ε..R, (iteratedDeriv (m + 1) f x) ^ 2 := by
  have hm : ContDiff ℝ 1 (iteratedDeriv m f) :=
    (contDiff_nat_succ_iff_contDiff_one_iteratedDeriv.mp hf).2
  have h := hardy_interval hε hεR hm hfε hfR
  simpa only [← iteratedDeriv_succ] using h

/--
Half-line Hardy inequality: for `0 < ε < R` and a `C¹` function `u` with support in `(ε, R)`,
`∫_0^∞ u²/x² ≤ 4 ∫_0^∞ (u')²`. No support hypothesis on `u'` is needed.
-/
theorem hardy_Ioi_of_support_subset_Ioo
    {u : ℝ → ℝ} {ε R : ℝ} (hε : 0 < ε) (hεR : ε < R)
    (hu : ContDiff ℝ 1 u)
    (hsupp : Function.support u ⊆ Set.Ioo ε R) :
    (∫ x in Set.Ioi (0 : ℝ), u x ^ 2 / x ^ 2) ≤
      4 * ∫ x in Set.Ioi (0 : ℝ), (deriv u x) ^ 2 := by
  have h := weighted_hardy_Ioi_of_support_subset_Ioo (s := 1) hε hεR (by norm_num) hu hsupp
  norm_num [Real.rpow_neg, Real.rpow_two, Real.rpow_neg_one, div_eq_mul_inv] at h ⊢
  exact h

/-- For `0 < ε < R` and a `C^{m+1}` function `f` whose `m`-th derivative has support in
`(ε, R)`, `∫_0^∞ (f^{(m)})²/x² ≤ 4 ∫_0^∞ (f^{(m+1)})²`. -/
theorem hardy_Ioi_iteratedDeriv_of_support_subset_Ioo
    (m : ℕ) {f : ℝ → ℝ} {ε R : ℝ} (hε : 0 < ε) (hεR : ε < R)
    (hf : ContDiff ℝ (m + 1) f)
    (hsupp : Function.support (iteratedDeriv m f) ⊆ Set.Ioo ε R) :
    (∫ x in Set.Ioi (0 : ℝ), (iteratedDeriv m f x) ^ 2 / x ^ 2) ≤
      4 * ∫ x in Set.Ioi (0 : ℝ), (iteratedDeriv (m + 1) f x) ^ 2 := by
  have hm : ContDiff ℝ 1 (iteratedDeriv m f) :=
    (contDiff_nat_succ_iff_contDiff_one_iteratedDeriv.mp hf).2
  have hderivEq : deriv (iteratedDeriv m f) = iteratedDeriv (m + 1) f :=
    (iteratedDeriv_succ (n := m) (f := f)).symm
  have h := hardy_Ioi_of_support_subset_Ioo hε hεR hm hsupp
  simpa only [hderivEq] using h

/--
If `u` has compact support and `tsupport u ⊆ (0, ∞)`, then `tsupport u ⊆ (ε, R)` for some
`0 < ε < R`. This turns the support condition of `TestFunctionOn (Ioi 0)` into the explicit
endpoints used by the integration by parts.
-/
theorem exists_Ioo_bounds_tsupport_of_subset_Ioi
    {u : ℝ → ℝ} (hcompact : HasCompactSupport u)
    (hpos : tsupport u ⊆ Set.Ioi (0 : ℝ)) :
    ∃ ε R : ℝ, 0 < ε ∧ ε < R ∧ tsupport u ⊆ Set.Ioo ε R := by
  by_cases hne : (tsupport u).Nonempty
  · obtain ⟨xmin, hxmin, hmin⟩ :=
      hcompact.exists_isMinOn hne continuousOn_id
    obtain ⟨xmax, hxmax, hmax⟩ :=
      hcompact.exists_isMaxOn hne continuousOn_id
    refine ⟨xmin / 2, xmax + 1, ?_, ?_, ?_⟩
    · have hxminPos : 0 < xmin := hpos hxmin
      linarith
    · have hxminPos : 0 < xmin := hpos hxmin
      have hxminLe : xmin ≤ xmax := hmin hxmax
      linarith
    · intro x hx
      have hxminLe : xmin ≤ x := hmin hx
      have hxmaxLe : x ≤ xmax := hmax hx
      have hxminPos : 0 < xmin := hpos hxmin
      constructor <;> linarith
  · refine ⟨1, 2, by norm_num, by norm_num, ?_⟩
    intro x hx
    exact False.elim (hne ⟨x, hx⟩)

/--
Half-line Hardy inequality on the smooth core: for a `C¹` function `u` with compact support and
`tsupport u ⊆ (0, ∞)`, `∫_0^∞ u²/x² ≤ 4 ∫_0^∞ (u')²`.
-/
theorem hardy_Ioi_of_hasCompactSupport
    {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u) (hcompact : HasCompactSupport u)
    (hpos : tsupport u ⊆ Set.Ioi (0 : ℝ)) :
    (∫ x in Set.Ioi (0 : ℝ), u x ^ 2 / x ^ 2) ≤
      4 * ∫ x in Set.Ioi (0 : ℝ), (deriv u x) ^ 2 := by
  obtain ⟨ε, R, hε, hεR, hsuppTop⟩ :=
    exists_Ioo_bounds_tsupport_of_subset_Ioi hcompact hpos
  have hsupp : Function.support u ⊆ Set.Ioo ε R :=
    (subset_tsupport u).trans hsuppTop
  exact hardy_Ioi_of_support_subset_Ioo hε hεR hu hsupp

/-- Dividing by the radial coordinate is globally continuous when the
function's topological support stays a positive distance from the axis. -/
theorem continuous_div_id_of_tsupport_subset_Ioo
    {u : ℝ → ℝ} {ε R : ℝ} (hε : 0 < ε) (hu : Continuous u)
    (hsupp : tsupport u ⊆ Set.Ioo ε R) :
    Continuous (fun x : ℝ ↦ u x / x) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst x
    refine (continuousAt_const : ContinuousAt (fun _ : ℝ ↦ (0 : ℝ)) 0).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hε] with y hy
    have huy : u y = 0 := by
      by_contra hne
      have hymem := hsupp (subset_tsupport u hne)
      exact lt_asymm hymem.1 hy
    simp [huy]
  · exact hu.continuousAt.div continuousAt_id hx

/-- The quotient `u(x) / x` of a continuous compactly supported function whose
support stays away from the origin lies in every `Lᵖ(ℝ)`. -/
theorem memLp_div_id_of_hasCompactSupport_at
    {u : ℝ → ℝ} {p : ℝ≥0∞} (hu : Continuous u)
    (hcompact : HasCompactSupport u)
    (hpos : tsupport u ⊆ Set.Ioi (0 : ℝ)) :
    MemLp (fun x : ℝ ↦ u x / x) p volume := by
  obtain ⟨ε, R, hε, _hεR, hsupp⟩ :=
    exists_Ioo_bounds_tsupport_of_subset_Ioi hcompact hpos
  have hcont := continuous_div_id_of_tsupport_subset_Ioo hε hu hsupp
  have hcompactQuot : HasCompactSupport (fun x : ℝ ↦ u x / x) := by
    apply hcompact.mono
    intro x hx
    by_contra hnot
    have hux : u x = 0 := Function.notMem_support.mp hnot
    exact hx (by simp [hux])
  exact hcont.memLp_of_hasCompactSupport hcompactQuot

/-- Division by an arbitrary natural power of the radial coordinate remains
continuous when the numerator vanishes on a neighborhood of the axis. -/
theorem continuous_div_pow_of_tsupport_subset_Ioo
    (j : ℕ) {u : ℝ → ℝ} {ε R : ℝ} (hε : 0 < ε) (hu : Continuous u)
    (hsupp : tsupport u ⊆ Set.Ioo ε R) :
    Continuous (fun x : ℝ ↦ u x / x ^ j) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst x
    refine (continuousAt_const : ContinuousAt (fun _ : ℝ ↦ (0 : ℝ)) 0).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hε] with y hy
    have huy : u y = 0 := by
      by_contra hne
      have hymem := hsupp (subset_tsupport u hne)
      exact lt_asymm hymem.1 hy
    simp [huy]
  · exact hu.continuousAt.div (continuousAt_id.pow j) (pow_ne_zero j hx)

/-- Compactly supported data away from the axis may be divided by `r^j` in
`L²` for every natural singular order `j`. -/
theorem memLp_div_pow_of_hasCompactSupport
    (j : ℕ) {u : ℝ → ℝ} (hu : Continuous u) (hcompact : HasCompactSupport u)
    (hpos : tsupport u ⊆ Set.Ioi (0 : ℝ)) :
    MemLp (fun x : ℝ ↦ u x / x ^ j) 2 volume := by
  obtain ⟨ε, R, hε, _hεR, hsupp⟩ :=
    exists_Ioo_bounds_tsupport_of_subset_Ioi hcompact hpos
  have hcont := continuous_div_pow_of_tsupport_subset_Ioo j hε hu hsupp
  have hcompactQuot : HasCompactSupport (fun x : ℝ ↦ u x / x ^ j) := by
    apply hcompact.mono
    intro x hx
    by_contra hnot
    have hux : u x = 0 := Function.notMem_support.mp hnot
    exact hx (by simp [hux])
  exact hcont.memLp_of_hasCompactSupport hcompactQuot

/-- For a real `L²` representative, its squared `Lp` norm is the integral of
the representative's square. -/
theorem norm_toLp_two_sq_eq_integral_sq
    {u : ℝ → ℝ} (hu : MemLp u 2 volume) :
    ‖hu.toLp u‖ ^ 2 = ∫ x : ℝ, u x ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hu.coeFn_toLp] with x hx
  rw [hx]
  simp [pow_two]

/-- A function supported in the positive half-line has the same square
integral over `ℝ` and over `(0,∞)`. -/
theorem integral_sq_eq_integral_Ioi_of_tsupport_subset
    {u : ℝ → ℝ} (hpos : tsupport u ⊆ Set.Ioi (0 : ℝ)) :
    (∫ x : ℝ, u x ^ 2) = ∫ x in Set.Ioi (0 : ℝ), u x ^ 2 := by
  have hzero : ∀ x ∈ (Set.univ : Set ℝ) \ Set.Ioi (0 : ℝ), u x ^ 2 = 0 := by
    intro x hx
    have hux : u x = 0 := by
      by_contra hne
      exact hx.2 (hpos (subset_tsupport u hne))
    simp [hux]
  simpa only [MeasureTheory.setIntegral_univ] using
    (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (f := fun x : ℝ ↦ u x ^ 2) (s := Set.Ioi (0 : ℝ))
      (t := Set.univ) MeasurableSet.univ (Set.subset_univ _) hzero)

/--
Norm form of Hardy on `C_c¹((0,∞))`: the quotient map has operator
bound `2` relative to the derivative `L²` norm.
-/
theorem norm_div_toLp_le_two_norm_deriv_toLp
    {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u) (hcompact : HasCompactSupport u)
    (hpos : tsupport u ⊆ Set.Ioi (0 : ℝ)) :
    let hq := memLp_div_id_of_hasCompactSupport_at (p := 2) hu.continuous hcompact hpos
    let hd : MemLp (deriv u) 2 volume :=
      (hu.continuous_deriv (by norm_num)).memLp_of_hasCompactSupport hcompact.deriv
    ‖hq.toLp (fun x : ℝ ↦ u x / x)‖ ≤ 2 * ‖hd.toLp (deriv u)‖ := by
  dsimp only
  let hq := memLp_div_id_of_hasCompactSupport_at (p := 2) hu.continuous hcompact hpos
  let hd : MemLp (deriv u) 2 volume :=
    (hu.continuous_deriv (by norm_num)).memLp_of_hasCompactSupport hcompact.deriv
  have hqSq := norm_toLp_two_sq_eq_integral_sq hq
  have hdSq := norm_toLp_two_sq_eq_integral_sq hd
  have hqIntegral :
      (∫ x : ℝ, (u x / x) ^ 2) =
        ∫ x in Set.Ioi (0 : ℝ), u x ^ 2 / x ^ 2 := by
    calc
      (∫ x : ℝ, (u x / x) ^ 2) =
          ∫ x in Set.Ioi (0 : ℝ), (u x / x) ^ 2 := by
            apply integral_sq_eq_integral_Ioi_of_tsupport_subset
            apply (closure_minimal ?_ (isClosed_tsupport u)).trans hpos
            intro x hx
            apply subset_tsupport u
            intro hux
            exact hx (by simp [hux])
      _ = ∫ x in Set.Ioi (0 : ℝ), u x ^ 2 / x ^ 2 := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x _hx
        exact div_pow (u x) x 2
  have hdIntegral :
      (∫ x : ℝ, (deriv u x) ^ 2) =
        ∫ x in Set.Ioi (0 : ℝ), (deriv u x) ^ 2 :=
    integral_sq_eq_integral_Ioi_of_tsupport_subset
      (tsupport_deriv_subset.trans hpos)
  have hHardy := hardy_Ioi_of_hasCompactSupport hu hcompact hpos
  have hsq :
      ‖hq.toLp (fun x : ℝ ↦ u x / x)‖ ^ 2 ≤
        4 * ‖hd.toLp (deriv u)‖ ^ 2 := by
    rw [hqSq, hdSq, hqIntegral, hdIntegral]
    exact hHardy
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) (norm_nonneg _))).mp
  nlinarith

end Hardy

end SobolevSpace
