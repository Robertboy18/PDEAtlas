/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Definitions
public import PDE.Analysis.MeasureTheory.LpNorm
import PDE.Spaces.Sobolev.Approximation.Mollification.Core -- shake: keep
import Mathlib.Algebra.Order.Ring.Star

/-!
# Closedness of weak derivatives under `L^p` convergence

Weak differentiation is a closed operator on `L^p`: if `f_m → f` and `g_m → g` in `L^p(Ω)` and `g_m`
is the weak derivative `D^α f_m` for every `m`, then `g` is the weak derivative `D^α f`. The
argument is step 3 of Evans's proof that `W^{k,p}` is complete (§5.2.3, Theorem 2). For a fixed test
function `φ`, both sides of the defining identity `∫ f_m D^α φ = (-1)^{|α|} ∫ g_m φ` are pairings
against a fixed `L^{p'}` function, so they are continuous under `L^p` convergence and the identity
survives in the limit.

This is the limit step used by the pullback chain rules: identities are first proved for
smooth (mollified) approximants and then transferred to the Sobolev function.

## Main results

* `tendsto_integral_mul_of_tendsto_eLpNorm`: `∫ f_m ψ → ∫ f ψ` when `f_m → f` in `L^p`
  (measured by `eLpNorm`) and `ψ ∈ L^{p'}`, with `p'` the Hölder conjugate of `p`.
* `hasWeakDerivativeOn_of_tendsto_eLpNorm`: `HasWeakDerivativeOn` is preserved under
  simultaneous `L^p` convergence of the functions and of their derivative representatives.

## Implementation notes

Convergence is stated as `eLpNorm (f_m - f) → 0` rather than as convergence in the `Lp` type,
so that the lemmas compose directly with the mollification estimates, which are phrased the
same way. Nothing here excludes `p = ∞`; the finite-exponent restriction in `FiniteExponent`
comes from the mollification step.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.2.3, Theorem 2, pp. 262-263; claim (8) in step 3 of the
  proof, p. 263, passes the identity `∫ u_m D^α φ = (-1)^{|α|} ∫ D^α u_m φ` to the limit.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section
namespace SobolevSpace

open MeasureTheory Set Function ENNReal Approximation
open scoped Topology

namespace WeakChangeOfVariables

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

local notation "qₚ" => ENNReal.conjExponent p


/-!
## A pairing lemma for passing to the limit in weak-derivative identities

If `f_m → f` in `L^p` and `ψ ∈ L^q`, then `∫ f_m ψ → ∫ f ψ`. The hypothesis is expressed using
`eLpNorm` so it composes directly with the approximation lemmas used below.
-/

private noncomputable def pairingWith (μ : Measure (ℝ^n)) (ψ : MeasureTheory.Lp ℝ qₚ μ) :
    MeasureTheory.Lp ℝ p μ →L[ℝ] ℝ :=
  (ContinuousLinearMap.lpPairing μ p qₚ (ContinuousLinearMap.mul ℝ ℝ)).flip ψ

private theorem pairingWith_eq_integral (μ : Measure (ℝ^n)) (ψ : MeasureTheory.Lp ℝ qₚ μ)
    (f : MeasureTheory.Lp ℝ p μ) :
    pairingWith (p := p) (μ := μ) ψ f = ∫ x, (f x) * (ψ x) ∂ μ := by
  simpa [pairingWith] using
    (ContinuousLinearMap.lpPairing_eq_integral (B := ContinuousLinearMap.mul ℝ ℝ) (μ := μ)
      (p := p) (q := qₚ) f ψ)

/-- Pairing against a conjugate-exponent test function is continuous under
`L^p` convergence expressed by `eLpNorm`. -/
theorem tendsto_integral_mul_of_tendsto_eLpNorm {μ : Measure (ℝ^n)} {ψ : ℝ^n → ℝ}
    (hψ : MeasureTheory.MemLp ψ qₚ μ) {f : ℕ → ℝ^n → ℝ} {f_lim : ℝ^n → ℝ}
    (hf : ∀ m, MeasureTheory.MemLp (f m) p μ) (hf_lim : MeasureTheory.MemLp f_lim p μ)
    (h_tendsto :
      Filter.Tendsto (fun m ↦ MeasureTheory.eLpNorm (fun x ↦ f m x - f_lim x) p μ)
        Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun m ↦ ∫ x, (f m x) * ψ x ∂ μ) Filter.atTop (𝓝 (∫ x, f_lim x * ψ x ∂ μ)) := by
  classical
  let ψLp : MeasureTheory.Lp ℝ qₚ μ := hψ.toLp ψ
  let F : MeasureTheory.Lp ℝ p μ := hf_lim.toLp f_lim
  have hF :
      Filter.Tendsto (fun m ↦ (hf m).toLp (f m)) Filter.atTop (𝓝 F) := by
    have h' :
        Filter.Tendsto (fun m ↦ MeasureTheory.eLpNorm (f m - f_lim) p μ) Filter.atTop (𝓝 0) := by
      refine Filter.Tendsto.congr (fun m ↦ ?_) h_tendsto
      exact MeasureTheory.eLpNorm_congr_ae <| Filter.Eventually.of_forall fun x ↦ rfl
    exact
      (MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (μ := μ) (p := p) (f := f)
          (f_ℒp := hf) (f_lim := f_lim) (f_lim_ℒp := hf_lim)).2 h'
  let L : MeasureTheory.Lp ℝ p μ →L[ℝ] ℝ := pairingWith (p := p) (μ := μ) ψLp
  have hL := (L.continuous.tendsto _).comp hF
  have hL_m :
      (fun m ↦ L ((hf m).toLp (f m))) = fun m ↦ ∫ x, (f m x) * ψ x ∂ μ := by
    funext m
    have hfm_ae : ((hf m).toLp (f m) : ℝ^n → ℝ) =ᵐ[μ] f m := (hf m).coeFn_toLp
    have hψ_ae : (ψLp : ℝ^n → ℝ) =ᵐ[μ] ψ := hψ.coeFn_toLp
    have hEq :
        (∫ x, (((hf m).toLp (f m) : MeasureTheory.Lp ℝ p μ) x) * (ψLp x) ∂ μ) =
          ∫ x, (f m x) * ψ x ∂ μ := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hfm_ae, hψ_ae] with x hx1 hx2
      simp [hx1, hx2]
    simp [L, pairingWith_eq_integral (p := p) (μ := μ) (ψ := ψLp), hEq]
  have hL_lim :
      L F = ∫ x, f_lim x * ψ x ∂ μ := by
    have hf_ae : (F : ℝ^n → ℝ) =ᵐ[μ] f_lim := hf_lim.coeFn_toLp
    have hψ_ae : (ψLp : ℝ^n → ℝ) =ᵐ[μ] ψ := hψ.coeFn_toLp
    have hEq :
        (∫ x, (F x) * (ψLp x) ∂ μ) = ∫ x, f_lim x * ψ x ∂ μ := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hf_ae, hψ_ae] with x hx1 hx2
      simp [hx1, hx2]
    simp [L, pairingWith_eq_integral (p := p) (μ := μ) (ψ := ψLp), hEq]
  have hL' :
      Filter.Tendsto (fun m ↦ ∫ x, (f m x) * ψ x ∂ μ) Filter.atTop (𝓝 (L F)) := by
    refine hL.congr' ?_
    refine Filter.Eventually.of_forall ?_
    intro m
    simpa using congrArg (fun g ↦ g m) hL_m
  simpa [hL_lim] using hL'

/-- Weak derivatives are closed under simultaneous `L^p` convergence, for any `1 ≤ p ≤ ∞`: if
`fSeq m → f` and `gSeq m → g` in `L^p(Ω)`, measured by `eLpNorm`, and `gSeq m` is the weak
derivative `D^α (fSeq m)` on `Ω` for every `m`, then `g` is the weak derivative `D^α f` on `Ω`.
This is the limit step used when a classical identity is proved on smooth approximants. -/
theorem hasWeakDerivativeOn_of_tendsto_eLpNorm
    {Ω : Set (ℝ^n)} {α : List (Fin n)}
    {f g : ℝ^n → ℝ} {fSeq gSeq : ℕ → ℝ^n → ℝ}
    (hfSeq : ∀ m, MeasureTheory.MemLp (fSeq m) p (domainMeasure n Ω))
    (hgSeq : ∀ m, MeasureTheory.MemLp (gSeq m) p (domainMeasure n Ω))
    (hf : MeasureTheory.MemLp f p (domainMeasure n Ω))
    (hg : MeasureTheory.MemLp g p (domainMeasure n Ω))
    (hweak : ∀ m, HasWeakDerivativeOn (n := n) Ω α (fSeq m) (gSeq m))
    (hf_tendsto :
      Filter.Tendsto
        (fun m ↦ MeasureTheory.eLpNorm (fun x ↦ fSeq m x - f x) p
          (domainMeasure n Ω)) Filter.atTop (𝓝 0))
    (hg_tendsto :
      Filter.Tendsto
        (fun m ↦ MeasureTheory.eLpNorm (fun x ↦ gSeq m x - g x) p
          (domainMeasure n Ω)) Filter.atTop (𝓝 0)) :
    HasWeakDerivativeOn (n := n) Ω α f g := by
  refine ⟨memLp_locallyIntegrableOn_domain hf Fact.out,
    memLp_locallyIntegrableOn_domain hg Fact.out, ?_⟩
  intro φ hφsupp
  let dφ : ℝ^n → ℝ := iteratedPartialDeriv (n := n) α φ.toFun
  have hdφ : MeasureTheory.MemLp dφ qₚ (domainMeasure n Ω) := by
    exact (PDE.contDiff_top_iteratedPartialDeriv (n := n) φ.contDiff α).continuous
      |>.memLp_of_hasCompactSupport
      (iteratedPartialDeriv_hasCompactSupport (n := n) φ α)
  have hφ : MeasureTheory.MemLp φ.toFun qₚ (domainMeasure n Ω) := by
    exact φ.contDiff.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport
  have hleft := tendsto_integral_mul_of_tendsto_eLpNorm (n := n) (p := p)
    (μ := domainMeasure n Ω) (ψ := dφ) hdφ hfSeq hf hf_tendsto
  have hright := tendsto_integral_mul_of_tendsto_eLpNorm (n := n) (p := p)
    (μ := domainMeasure n Ω) (ψ := φ.toFun) hφ hgSeq hg hg_tendsto
  let sign : ℝ := (-1 : ℝ) ^ α.length
  have hright' :
      Filter.Tendsto
        (fun m ↦ ∫ x, fSeq m x * dφ x ∂ domainMeasure n Ω)
        Filter.atTop
        (𝓝 (sign * ∫ x, g x * φ.toFun x ∂ domainMeasure n Ω)) := by
    have hs := hright.const_mul sign
    convert hs using 1
    funext m
    simpa [sign, dφ, HasWeakDerivativeOn] using hweak m φ hφsupp
  have hlimit :
      (∫ x, f x * dφ x ∂ domainMeasure n Ω) =
        sign * ∫ x, g x * φ.toFun x ∂ domainMeasure n Ω :=
    tendsto_nhds_unique hleft hright'
  simpa [sign, dφ] using hlimit


end WeakChangeOfVariables

end SobolevSpace
