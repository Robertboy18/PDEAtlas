/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.WeakWave.Coefficients.ContinuousUniqueness

/-!
# Existence and uniqueness for the classical-coefficient Dirichlet wave

The Galerkin construction and classical-coefficient uniqueness theorem give the
weak solution of Evans, §7.2.2, Theorems 3 and 4. The input consists of coefficient fields
and the natural data. Coefficient classes, uniform bounds, pairing integrability, and the
solution are constructed. Both initial values and the uniform energy bounds are kept.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.2, Theorems 3 and 4.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace SobolevSpace.GraphSpace

/-- Classical Evans coefficients and natural energy data determine a unique weak
Dirichlet wave on a bounded open domain. Uniqueness holds among all weak waves, without
assuming the uniform energy bounds of the constructed solution. -/
theorem exists_unique_weakWave_of_continuousOn_compact_coefficients {n : ℕ} {Ω : Set (ℝ^n)}
    (hn : 0 < n) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) {a b : ℝ} (hab : a < b)
    (A Adot : ℝ → Fin n → Fin n → ℝ^n → ℝ) (B : ℝ → Fin n → ℝ^n → ℝ)
    (DB : ℝ → Fin n → Fin n → ℝ^n → ℝ) (C : ℝ → ℝ^n → ℝ)
    (hA : ∀ i j, ContinuousOn (fun p ↦ A p.1 i j p.2) (Icc a b ×ˢ closure Ω))
    (hAdot : ∀ i j, ContinuousOn (fun p ↦ Adot p.1 i j p.2) (Icc a b ×ˢ closure Ω))
    (hAderiv : ∀ i j, ∀ x ∈ closure Ω, ∀ t ∈ Icc a b,
      HasDerivWithinAt (fun s ↦ A s i j x) (Adot t i j x) (Icc a b) t)
    (hB : ∀ i, ContinuousOn (fun p ↦ B p.1 i p.2) (Icc a b ×ˢ closure Ω))
    (hDB : ∀ i j, ContinuousOn (fun p ↦ DB p.1 i j p.2) (Icc a b ×ˢ closure Ω))
    (hC : ContinuousOn (Function.uncurry C) (Icc a b ×ˢ closure Ω))
    (hBdiff : ∀ t ∈ Icc a b, ∀ i, ∀ x ∈ Ω, ContDiffAt ℝ 1 (B t i) x)
    (hDBderiv : ∀ t ∈ Icc a b, ∀ i j, ∀ x ∈ Ω, DB t i j x = (∂[j] (B t i)) x)
    (hsymm : ∀ t ∈ Icc a b, ∀ x ∈ Ω, ∀ i j, A t i j x = A t j i x) {alpha : ℝ} (halpha : 0 < alpha)
    (helliptic : ∀ t ∈ Icc a b, ∀ x ∈ Ω, ∀ ξ : Fin n → ℝ, alpha * ∑ i : Fin n, ξ i * ξ i ≤ ∑ i :
      Fin n, ∑ j : Fin n, A t i j x * ξ j * ξ i)
    (f : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b))) (q₀ : H¹₀(Ω)) (p₀ : DerivLp n 2 Ω) :
    let T := h10L2GelfandTriple hΩ
    ∃ (coeff : ℝ → Fin n → Fin n → DerivLp n ∞ Ω)
        (z : ℝ → (Fin n → DerivLp n ∞ Ω) × DerivLp n ∞ Ω),
      (∀ t ∈ Icc a b, ∀ i j,
        (coeff t i j : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] A t i j) ∧
      (∀ t ∈ Icc a b, ∀ i,
        ((z t).1 i : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] B t i) ∧
      (∀ t ∈ Icc a b, ((z t).2 : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] C t) ∧
      let form := fun t ↦ fullDivergenceForm (multiplicationCoefficientOperator (coeff t))
        (fun i ↦ mulLpLeft ((z t).1 i)) (mulLpLeft (z t).2)
      let load := T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) f
      ∃ (u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b)))
          (velocity : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b)))
          (acceleration :
            Lp (StrongDual ℝ (H¹₀(Ω))) 2 (volume.restrict (Ioc a b))),
        Hyperbolic.Variational.IsGelfandWeakWaveSolution
            T form load u velocity acceleration q₀ p₀ ∧
          MemLp (fun t ↦ u t) ∞ (volume.restrict (Ioc a b)) ∧
          MemLp (fun t ↦ velocity t) ∞ (volume.restrict (Ioc a b)) ∧
          ∀ u' velocity' acceleration',
            Hyperbolic.Variational.IsGelfandWeakWaveSolution
              T form load u' velocity' acceleration' q₀ p₀ →
              u' = u ∧ velocity' = velocity ∧ acceleration' = acceleration := by
  have hex := exists_weakWave_of_continuousOn_compact_coefficients
    hn hΩ hΩbounded hab A Adot B C hA hAdot hAderiv hB hC hsymm halpha helliptic f q₀ p₀
  let coeff := hex.choose
  let z := hex.choose_spec.choose
  have hdata := hex.choose_spec.choose_spec
  let u := hdata.2.2.2.choose
  let velocity := hdata.2.2.2.choose_spec.choose
  let acceleration := hdata.2.2.2.choose_spec.choose_spec.choose
  have hsolution := hdata.2.2.2.choose_spec.choose_spec.choose_spec
  refine ⟨coeff, z, hdata.1, hdata.2.1, hdata.2.2.1,
    u, velocity, acceleration, hsolution.1, hsolution.2.1, hsolution.2.2, ?_⟩
  intro u' velocity' acceleration' h'
  exact weakWave_eq_of_continuousOn_compact_coefficients hn hΩ hΩbounded
    A Adot B DB C hA hAdot hAderiv hB hDB hC hBdiff hDBderiv hsymm halpha helliptic
    coeff z hdata.1 hdata.2.1 hdata.2.2.1 h' hsolution.1

end SobolevSpace.GraphSpace
