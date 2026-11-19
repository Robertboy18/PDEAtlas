/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.Core
public import PDE.Spaces.Sobolev.Foundations.Representatives.Definitions
import Mathlib.MeasureTheory.Measure.Haar.Unique
import PDE.FDeriv.Calculus.Convolution
import PDE.Analysis.Integration.ConvolutionDerivative
import PDE.Spaces.Sobolev.Approximation.Mollification.LpApproximation

/-!
# Mollification and weak derivatives

The identity behind interior approximation of Sobolev functions: if `g` is the weak derivative
`∂^α f` on an open set `Ω`, then for a mollifier `ρ_ε` supported in `closedBall 0 (εR)`,
`∂^α (ρ_ε ⋆ f) = ρ_ε ⋆ g` at every point `x` with `closedBall x (εR) ⊆ Ω`. The classical
derivative of the convolution falls on the smooth kernel, `∂^α_x ρ_ε(x - y) = (-1)^{|α|} ∂^α_y
ρ_ε(x - y)`, and the definition of the weak derivative moves it onto `f` because
`y ↦ ρ_ε(x - y)` is a test function supported inside `Ω`. This is the computation in Evans' proof
of local approximation by smooth functions (Evans, PDE, §5.3.1), here carried out with the
mollification performed on the zero extension `Ω.indicator f`.

Combined with the `Lᵖ` convergence of mollifiers from `Mollification.LpApproximation`, the
identity yields Evans' interior approximation theorem: mollifications of a `W^{k,p}(Ω)` function
converge to it, together with all derivatives of order at most `k`, in `Lᵖ(K)` for every compact
`K ⊆ Ω`. Convergence is along all positive real scales tending to zero, expressed by
`nhdsWithin 0 (Ioi 0)`. Compact containment makes the derivative identity valid uniformly on
`K` for all sufficiently small positive scales. The sequence `ε_m = 1/(m+1)` gives the
sequential approximation theorem as a corollary.

## Main results

* `iteratedPartialDeriv_mollify_eq_mollify_of_hasWeakDerivative_univ`: on `ℝ^n`, mollification
  commutes with every weak derivative of positive order.
* `iteratedPartialDeriv_mollify_indicator_eq_mollify_indicator_of_hasWeakDerivativeOn`: the
  interior version on a domain `Ω`, valid at points whose `εR`-ball lies in `Ω`.
* `interior_mollification`: the actual mollified zero extension is smooth at every positive
  scale and converges locally in `W^{k,p}` as that scale tends to zero from above.
* `interiorApproximation_Wkp`: interior approximation of `W^{k,p}(Ω)` functions by smooth
  functions, with convergence of all derivatives up to order `k` in `Lᵖ(K)` for compact `K ⊆ Ω`.
* `partialDeriv_const_mul`, `iteratedPartialDeriv_comp_const_sub`: calculus lemmas for
  coordinate derivatives of the reflected kernel `y ↦ k(x - y)`.

## Implementation notes

Multi-indices are lists `α : List (Fin n)` and `iteratedPartialDeriv α` applies the coordinate
derivatives in order; the empty list is excluded from the commutation identities (`hα : α ≠ []`)
because the order-zero case is trivial and the proof peels off one coordinate. Convolutions are
written with Mathlib's `ContinuousLinearMap.mul ℝ ℝ`, and `convolution_lsmul_eq_mul` converts
from the `lsmul` form used by `mollify`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.3.1, Theorem 1, pp. 264-265, and step 1 of its proof, the
  identity `D^α u^ε = η_ε * D^α u` in `U_ε`.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (partialDeriv iteratedPartialDeriv)

noncomputable section

open TopologicalSpace
open scoped Distributions

namespace SobolevSpace

open MeasureTheory Set Function ENNReal
open scoped Convolution Pointwise Topology

namespace Approximation

variable {n : ℕ}

section WeakDerivativeMollify

open scoped Convolution

open ContinuousLinearMap

private theorem convolution_mul_comm (f g : ℝ^n → ℝ) :
    (f ⋆[mul ℝ ℝ, volume] g) = (g ⋆[mul ℝ ℝ, volume] f) := by
  ext x
  -- Use the symmetric formula and commutativity of multiplication.
  calc
    (f ⋆[mul ℝ ℝ, volume] g) x = ∫ t, f (x - t) * g t ∂(volume) := by
      simpa using (convolution_mul_swap (μ := volume) (x := x) (f := f) (g := g))
    _ = ∫ t, g t * f (x - t) ∂(volume) := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with t
      simp [mul_comm]
    _ = (g ⋆[mul ℝ ℝ, volume] f) x := by
      simp [convolution_def]

private theorem partialDeriv_comp_const_sub (i : Fin n) {h : ℝ^n → ℝ} {x y : ℝ^n}
    (hh : DifferentiableAt ℝ h (x - y)) :
    (∂[i] (fun z ↦ h (x - z))) y = -(∂[i] h) (x - y) := by
  have hcomp := hh.hasFDerivAt.comp y ((hasFDerivAt_id y).const_sub x)
  simpa [partialDeriv, Function.comp_def] using
    congrArg (fun T : ℝ^n →L[ℝ] ℝ ↦ T (EuclideanSpace.single i (1 : ℝ))) hcomp.fderiv

/-- Coordinate differentiation commutes with multiplication by a constant. -/
theorem partialDeriv_const_mul (i : Fin n) (c : ℝ) {h : ℝ^n → ℝ} {x : ℝ^n}
    (hh : DifferentiableAt ℝ h x) :
    (∂[i] (fun y ↦ c * h y)) x = c * (∂[i] h) x := by
  unfold partialDeriv
  have hfderiv :
      fderiv ℝ (fun y ↦ c * h y) x = c • fderiv ℝ h x := by
    simpa using (fderiv_const_mul (𝕜 := ℝ) (a := h) (x := x) hh c)
  -- Evaluation on `e_i` gives the corresponding coordinate derivative.
  simp [hfderiv, smul_eq_mul]

/-- Iterated coordinate derivatives of the affine reflection `y ↦ k (x-y)`
acquire one factor of `-1` per derivative. -/
theorem iteratedPartialDeriv_comp_const_sub (α : List (Fin n)) {k : ℝ^n → ℝ}
    (hk : ContDiff ℝ (⊤ : ℕ∞) k) (x y : ℝ^n) :
    iteratedPartialDeriv (n := n) α (fun z ↦ k (x - z)) y =
      (-1 : ℝ) ^ α.length * iteratedPartialDeriv (n := n) α k (x - y) := by
  induction α generalizing y with
  | nil => simp [iteratedPartialDeriv]
  | cons i rest ih =>
    have hd : Differentiable ℝ (iteratedPartialDeriv (n := n) rest k) :=
      (PDE.contDiff_top_iteratedPartialDeriv (n := n) hk rest).differentiable (by simp)
    -- The leading derivative passes the parity factor and contributes one more sign.
    have hmul := partialDeriv_const_mul (n := n) i ((-1 : ℝ) ^ rest.length) (x := y)
      (h := fun z ↦ iteratedPartialDeriv (n := n) rest k (x - z))
      ((hd (x - y)).comp y (differentiableAt_id.const_sub x))
    have hchain := partialDeriv_comp_const_sub (n := n) i
      (h := iteratedPartialDeriv (n := n) rest k) (x := x) (y := y) (hd (x - y))
    simp [iteratedPartialDeriv, ih, hmul, hchain, pow_succ]

/-- A supported multiplier identifies a whole-space zero-extension integral with a domain integral.
No measurability of the domain is needed because the product vanishes on its complement. -/
private theorem integral_indicator_mul_eq_setIntegral_of_support_subset
    {Ω : Set (ℝ^n)} (f ψ : ℝ^n → ℝ) (hψ : Function.support ψ ⊆ Ω) :
    (∫ y, Ω.indicator f y * ψ y) = ∫ y in Ω, f y * ψ y := by
  have hzero (y : ℝ^n) (hy : y ∉ Ω) : ψ y = 0 :=
    notMem_support.mp (fun h ↦ hy (hψ h))
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy ↦ by rw [hzero y hy, mul_zero])]
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : y ∈ Ω
  · simp [hy]
  · simp [hy, hzero y hy]

/-- Moving a weak derivative onto a smooth compactly supported convolution kernel is valid
whenever the translated kernel support lies in the domain. -/
theorem convolution_iteratedPartialDeriv_eq_of_hasWeakDerivativeOn
    {Ω : Set (ℝ^n)} {α : List (Fin n)} {f g k : ℝ^n → ℝ}
    (hweak : HasWeakDerivativeOn (n := n) Ω α f g)
    (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hkcs : HasCompactSupport k)
    (x : ℝ^n) (hx : tsupport (fun y ↦ k (x - y)) ⊆ Ω) :
    ((Ω.indicator f) ⋆[mul ℝ ℝ, volume] iteratedPartialDeriv (n := n) α k) x =
      ((Ω.indicator g) ⋆[mul ℝ ℝ, volume] k) x := by
  let φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ) :=
    { toFun := fun y ↦ k (x - y)
      contDiff' := hk.comp (contDiff_const.sub contDiff_id)
      hasCompactSupport' := hkcs.comp_homeomorph (Homeomorph.subLeft x)
      tsupport_subset' := Set.subset_univ _ }
  have hDφ : Function.support (iteratedPartialDeriv (n := n) α φ.toFun) ⊆ Ω :=
    (subset_tsupport _).trans ((tsupport_iteratedPartialDeriv_subset_tsupport α φ.toFun).trans hx)
  have hidentity :
      (∫ y, Ω.indicator f y * iteratedPartialDeriv (n := n) α φ.toFun y) =
        (-1 : ℝ) ^ α.length * ∫ y, Ω.indicator g y * φ.toFun y := by
    rw [integral_indicator_mul_eq_setIntegral_of_support_subset f _ hDφ,
      integral_indicator_mul_eq_setIntegral_of_support_subset g _ ((subset_tsupport _).trans hx)]
    exact hweak φ hx
  have hleft :
      (fun y ↦ Ω.indicator f y * iteratedPartialDeriv (n := n) α φ.toFun y) =
        fun y ↦ (-1 : ℝ) ^ α.length *
          (Ω.indicator f y * iteratedPartialDeriv (n := n) α k (x - y)) := by
    funext y
    change Ω.indicator f y * iteratedPartialDeriv (n := n) α (fun z ↦ k (x - z)) y = _
    rw [iteratedPartialDeriv_comp_const_sub α hk x y]
    ring
  rw [hleft, integral_const_mul] at hidentity
  apply mul_left_cancel₀ (pow_ne_zero α.length (by norm_num : (-1 : ℝ) ≠ 0))
  simpa [convolution_def, φ] using hidentity

/-- Positive-scale mollification on `ℝ^n` commutes with every nonempty weak derivative word. -/
theorem iteratedPartialDeriv_mollify_eq_mollify_of_hasWeakDerivative_univ (μ : Mollifier n)
    {ε : ℝ} (hε : 0 < ε) {α : List (Fin n)} (hα : α ≠ [])
    {f g : ℝ^n → ℝ} (hf : LocallyIntegrable f (volume))
    (hweak : HasWeakDerivativeOn (n := n) Set.univ α f g) :
    (fun x ↦ iteratedPartialDeriv (n := n) α (mollify μ ε f) x) = mollify μ ε g := by
  cases α with
  | nil => exact (hα rfl).elim
  | cons i rest =>
    have hk : ContDiff ℝ (⊤ : ℕ∞) (scaled μ ε) := scaled_contDiff μ
    have hkcs : HasCompactSupport (scaled μ ε) := scaled_hasCompactSupport μ hε
    have hmoll (v : ℝ^n → ℝ) : mollify μ ε v = (v ⋆[mul ℝ ℝ, volume] scaled μ ε) := by
      change (scaled μ ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) = _
      rw [convolution_lsmul_eq_mul]
      exact convolution_mul_comm _ v
    -- On `ℝ^n` every translated kernel is a test function, so the weak identity applies at
    -- every point.
    funext x
    have hweak_x :=
      convolution_iteratedPartialDeriv_eq_of_hasWeakDerivativeOn hweak hk hkcs x (subset_univ _)
    simp only [indicator_univ] at hweak_x
    rw [hmoll, hmoll,
      PDE.Analysis.convolution_iteratedPartialDeriv_right f _ hf hkcs hk (i :: rest) x]
    exact hweak_x

/-- Mollification commutes with weak derivatives on interior points of a domain `Ω`.

This is the local Evans identity, with the mollification performed on the zero extension
`Ω.indicator f`, assumed locally integrable on `ℝ^n`. The conclusion holds at a point `x`
provided the convolution only sees values inside `Ω` (a closed-ball inclusion condition). -/
theorem iteratedPartialDeriv_mollify_indicator_eq_mollify_indicator_of_hasWeakDerivativeOn
    (μ : Mollifier n)
    {ε : ℝ} (hε : 0 < ε) {R : ℝ} (hR : tsupport μ.ρ ⊆ Metric.closedBall (0 : ℝ^n) R)
    {Ω : Set (ℝ^n)} {α : List (Fin n)} (hα : α ≠ [])
    {f g : ℝ^n → ℝ}
    (hf : LocallyIntegrable (Ω.indicator f) (volume))
    (hweak : HasWeakDerivativeOn (n := n) Ω α f g) :
    ∀ x : ℝ^n, Metric.closedBall x (ε * R) ⊆ Ω →
      iteratedPartialDeriv (n := n) α (mollify μ ε (Ω.indicator f)) x =
        mollify μ ε (Ω.indicator g) x := by
  cases α with
  | nil => exact (hα rfl).elim
  | cons i rest =>
    intro x hxΩ
    let k : ℝ^n → ℝ := scaled μ ε
    have hk : ContDiff ℝ (⊤ : ℕ∞) k := scaled_contDiff μ
    have hkcs : HasCompactSupport k := scaled_hasCompactSupport μ hε
    have hmoll (v : ℝ^n → ℝ) : mollify μ ε v = (v ⋆[mul ℝ ℝ, volume] k) := by
      change (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) = _
      rw [convolution_lsmul_eq_mul]
      exact convolution_mul_comm k v
    have hsupp : tsupport (fun y ↦ k (x - y)) ⊆ Ω := by
      apply Set.Subset.trans (closure_minimal (t := Metric.closedBall x (ε * R)) ?_
        Metric.isClosed_closedBall) hxΩ
      intro y hy
      have hxy := support_scaled_subset_closedBall μ hε hR hy
      simpa only [Metric.mem_closedBall, dist_zero_right, dist_eq_norm, sub_zero, norm_sub_rev]
        using hxy
    rw [hmoll]
    calc
      iteratedPartialDeriv (n := n) (i :: rest) ((Ω.indicator f) ⋆[mul ℝ ℝ, volume] k) x =
          ((Ω.indicator f) ⋆[mul ℝ ℝ, volume] iteratedPartialDeriv (n := n) (i :: rest) k) x :=
        PDE.Analysis.convolution_iteratedPartialDeriv_right _ _ hf hkcs hk (i :: rest) x
      _ = ((Ω.indicator g) ⋆[mul ℝ ℝ, volume] k) x :=
        convolution_iteratedPartialDeriv_eq_of_hasWeakDerivativeOn hweak hk hkcs x hsupp
      _ = mollify μ ε (Ω.indicator g) x := congrFun (hmoll _).symm x

end WeakDerivativeMollify

/-- Local Sobolev mollification for every positive scale (Evans §5.3.1, Theorem 1).

For `1 ≤ p < ∞` and any natural order `k`, the actual convolution of the zero extension of
`u ∈ W^{k,p}(Ω)` is smooth and converges to `u` locally in `W^{k,p}`. The derivative clause
expresses this convergence in representative form: one `Lᵖ(Ω)` weak derivative for each word
of length at most `k`, with convergence of the corresponding classical derivatives on every
compact subset of `Ω`. The representatives are chosen independently of the compact subset.

No sequence of scales is prescribed: the limit uses `nhdsWithin 0 (Ioi 0)`. The mollifier may
have any compact support; its support radius only determines how small the scale must be in
the interior derivative identity. Since the zero extension is globally `Lᵖ`, its mollification
is in fact smooth on all of `ℝ^n` at every positive scale. -/
theorem interior_mollification
    (μ : Mollifier n) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {k : ℕ} {Ω : Set (ℝ^n)} (hΩ : IsOpen Ω) (u : SobolevSpaceOn n k p Ω) :
    (∀ ε : ℝ, 0 < ε →
      ContDiff ℝ (⊤ : ℕ∞) (mollify μ ε (Ω.indicator u.toFun))) ∧
    (∀ K : Set (ℝ^n), IsCompact K → K ⊆ Ω →
      Filter.Tendsto
        (fun ε ↦ eLpNorm (fun x ↦ mollify μ ε (Ω.indicator u.toFun) x - u.toFun x)
          p (domainMeasure n K))
        (nhdsWithin 0 (Ioi 0)) (𝓝 0)) ∧
    (∀ α : List (Fin n), α.length ≤ k →
      ∃ g : ℝ^n → ℝ,
        MemLp g p (domainMeasure n Ω) ∧
        HasWeakDerivativeOn Ω α u.toFun g ∧
        ∀ K : Set (ℝ^n), IsCompact K → K ⊆ Ω →
          Filter.Tendsto
            (fun ε ↦ eLpNorm (fun x ↦
              iteratedPartialDeriv α (mollify μ ε (Ω.indicator u.toFun)) x - g x)
              p (domainMeasure n K))
            (nhdsWithin 0 (Ioi 0)) (𝓝 0)) := by
  have huΩLp : MemLp (Ω.indicator u.toFun) p volume :=
    (memLp_indicator_iff_restrict hΩ.measurableSet.nullMeasurableSet).2 u.memLp
  have huΩLoc := huΩLp.locallyIntegrable (Fact.out : 1 ≤ p)
  have hconv_u (K : Set (ℝ^n)) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :=
    tendsto_eLpNorm_mollify_indicator_sub_on_subset μ hp
      hΩ.measurableSet hK.measurableSet hKΩ u.memLp
  refine ⟨fun ε hε ↦ mollify_contDiff_of_pos μ hε _ huΩLoc, hconv_u, fun α hαk ↦ ?_⟩
  cases α with
  | nil =>
    exact ⟨u.toFun, u.memLp,
      hasWeakDerivativeOn_nil (memLp_locallyIntegrableOn_domain u.memLp (Fact.out : 1 ≤ p)),
      fun K hK hKΩ ↦ by simpa only [iteratedPartialDeriv] using hconv_u K hK hKΩ⟩
  | cons i rest =>
    obtain ⟨g, hgLp, hweak⟩ := u.weak_derivs_inLp (i :: rest) hαk
    refine ⟨g, hgLp, hweak, fun K hK hKΩ ↦ ?_⟩
    obtain ⟨R, hR⟩ := μ.compactSupport.isCompact.isBounded.subset_closedBall (0 : ℝ^n)
    obtain ⟨δ, hδpos, hδK⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
    have hεR0 : Filter.Tendsto (fun ε : ℝ ↦ ε * R) (nhdsWithin 0 (Ioi 0)) (𝓝 (0 : ℝ)) := by
      simpa using (Filter.tendsto_id.mono_right nhdsWithin_le_nhds :
        Filter.Tendsto (fun ε : ℝ ↦ ε) (nhdsWithin 0 (Ioi 0)) (𝓝 0)).mul_const R
    -- For `ε R < δ` the mollification at points of `K` only sees `Ω`, where it commutes with
    -- the weak derivative.
    refine (tendsto_eLpNorm_mollify_indicator_sub_on_subset μ hp hΩ.measurableSet
      hK.measurableSet hKΩ hgLp).congr' ?_
    filter_upwards [self_mem_nhdsWithin, hεR0.eventually (Iio_mem_nhds hδpos)]
      with ε hε hsmall
    refine (eLpNorm_congr_ae (ae_restrict_of_forall_mem hK.measurableSet fun x hxK ↦ ?_)).symm
    rw [iteratedPartialDeriv_mollify_indicator_eq_mollify_indicator_of_hasWeakDerivativeOn
      μ hε hR (by simp) huΩLoc hweak x ((Metric.closedBall_subset_cthickening hxK _).trans
        ((Metric.cthickening_mono hsmall.le K).trans hδK))]

/-- Interior approximation by smooth functions (Evans §5.3.1), in an Evans-style `W^{k,p}` sense.

Evans’ interior theorem is local: for any compact `K ⊆ Ω`, mollification provides smooth
approximants whose classical derivatives converge in `L^p(K)` to a weak derivative representative
of `u`. -/
theorem interiorApproximation_Wkp (μ : Mollifier n) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (k : ℕ)
    (Ω : Set (ℝ^n)) :
    ∀ u : SobolevSpaceOn n k p Ω,
      IsOpen Ω →
      ∀ K : Set (ℝ^n), IsCompact K → K ⊆ Ω →
        ∃ u_m : ℕ → (ℝ^n → ℝ),
          (∀ m, ContDiff ℝ (⊤ : ℕ∞) (u_m m)) ∧
          Filter.Tendsto
            (fun m ↦
              eLpNorm (fun x ↦ u_m m x - u.toFun x) p (domainMeasure n K))
            Filter.atTop (𝓝 0) ∧
          (∀ α : List (Fin n), α.length ≤ k →
            ∃ g : ℝ^n → ℝ,
              MemLp g p (domainMeasure n Ω) ∧
              HasWeakDerivativeOn (n := n) Ω α u.toFun g ∧
              Filter.Tendsto
                (fun m ↦
                  eLpNorm (fun x ↦ iteratedPartialDeriv (n := n) α (u_m m) x - g x) p
                    (domainMeasure n K))
                Filter.atTop (𝓝 0)) := by
  intro u hΩopen K hK hKΩ
  classical
  let ε : ℕ → ℝ := fun m ↦ (1 : ℝ) / ((m : ℝ) + 1)
  have hεpos (m : ℕ) : 0 < ε m := by dsimp [ε]; positivity
  have hε0 : Filter.Tendsto ε Filter.atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hεright : Filter.Tendsto ε Filter.atTop (nhdsWithin 0 (Ioi 0)) :=
    tendsto_nhdsWithin_iff.2 ⟨hε0, Filter.Eventually.of_forall hεpos⟩
  obtain ⟨hsmooth, hconv, hderiv⟩ := interior_mollification μ hp hΩopen u
  refine ⟨fun m ↦ mollify μ (ε m) (Ω.indicator u.toFun),
    fun m ↦ hsmooth _ (hεpos m), (hconv K hK hKΩ).comp hεright, ?_⟩
  intro α hαk
  obtain ⟨g, hgLp, hweak, hgconv⟩ := hderiv α hαk
  exact ⟨g, hgLp, hweak, (hgconv K hK hKΩ).comp hεright⟩

end Approximation

end SobolevSpace

end
