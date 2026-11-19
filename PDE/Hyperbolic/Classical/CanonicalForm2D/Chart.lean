/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Classical.CanonicalForm2D.CharacteristicMap
public import PDE.Analysis.Calculus.InverseFunction.Jacobian
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Local characteristic charts

Strict hyperbolicity and C² germs of the three principal coefficients construct
a C² local diffeomorphism. On its open source both pure coefficients vanish and
the mixed coefficient is nonzero. The inverse function theorem supplies the chart;
shrinking its source makes all the conclusions hold throughout the chart.

`exists_characteristic_chart` gives the new variables `y = Φ(x)` of Evans, §7.2.5, (83) for a
hyperbolic equation, `det A < 0` as in (89): both components solve the characteristic
equation (88), so the pure coefficients vanish as in (87), and the mixed coefficient is
nonzero, as in (94). The components are those of `exists_characteristic_map`, and the inverse
function theorem makes the map a chart.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.5, equations (83)-(94).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter
open scoped Topology
open PDE.Analysis

namespace Hyperbolic.CanonicalForm2D

/-- A general strictly hyperbolic principal part with local C² coefficients admits
a C² characteristic chart and C² inverse on open neighborhoods. -/
theorem exists_characteristic_chart {A : ℝ^2 → PrincipalPart} {x : ℝ^2}
    (h₁₁ : ContDiffAt ℝ 2 (fun y ↦ (A y).a11) x) (h₁₂ : ContDiffAt ℝ 2 (fun y ↦ (A y).a12) x)
    (h₂₂ : ContDiffAt ℝ 2 (fun y ↦ (A y).a22) x) (hA : (A x).IsHyperbolic) :
    ∃ e : OpenPartialHomeomorph ℝ^2 ℝ^2, x ∈ e.source ∧
      ContDiffOn ℝ 2 e e.source ∧ ContDiffOn ℝ 2 e.symm e.target ∧
      ∀ y ∈ e.source, (transformedPrincipal A e y).a11 = 0 ∧
        (transformedPrincipal A e y).a22 = 0 ∧
        (transformedPrincipal A e y).a12 ≠ 0 := by
  obtain ⟨Φ, hΦ, hdet, hnull⟩ := exists_characteristic_map h₁₁ h₁₂ h₂₂ hA
  obtain ⟨e, he, hxe, hinv⟩ :=
    exists_openPartialHomeomorph_of_det_jacobianMatrix_ne_zero hΦ (by norm_num) hdet
  rw [← he] at hΦ hdet hnull hinv
  have hpartial (i j : Fin 2) : ContinuousAt (fun y ↦ (∂[i] (fun z ↦ e z j)) y) x :=
    (PDE.contDiffAt_partialDeriv 1 ((contDiffAt_piLp 2).mp hΦ j) i).continuousAt
  have hdetcont : ContinuousAt (fun y ↦ (jacobianMatrix e y).det) x := by
    have h := ((hpartial 0 0).mul (hpartial 1 1)).sub ((hpartial 1 0).mul (hpartial 0 1))
    change ContinuousAt (fun y ↦ (∂[0] (fun z ↦ e z 0)) y * (∂[1] (fun z ↦ e z 1)) y -
      (∂[1] (fun z ↦ e z 0)) y * (∂[0] (fun z ↦ e z 1)) y) x at h
    simpa only [Matrix.det_fin_two, jacobianMatrix, jacobianColumn, Matrix.of_apply] using h
  have hAcont : ContinuousAt (fun y ↦ (A y).determinant) x :=
    ((h₁₁.mul h₂₂).sub (h₁₂.pow 2)).continuousAt
  have hgood : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 e y ∧
      ContDiffAt ℝ 2 e.symm (e y) ∧ (jacobianMatrix e y).det ≠ 0 ∧ (A y).determinant ≠ 0 ∧
      (transformedPrincipal A e y).a11 = 0 ∧
      (transformedPrincipal A e y).a22 = 0 := by
    filter_upwards [hΦ.eventually (by norm_num),
      hΦ.continuousAt.eventually (hinv.eventually (by norm_num)),
      hdetcont.eventually_ne hdet, hAcont.eventually_ne (ne_of_lt hA), hnull]
      with y hy hyinv hydet hyA hy₀
    exact ⟨hy, hyinv, hydet, hyA, hy₀⟩
  obtain ⟨s, hsgood, hs, hxs⟩ := mem_nhds_iff.mp hgood
  let e' := e.restrOpen s hs
  refine ⟨e', ⟨hxe, hxs⟩, ?_, ?_, ?_⟩
  · exact fun y hy ↦ (hsgood hy.2).1.contDiffWithinAt
  · intro z hz
    have hy := e'.map_target hz
    have hreg := (hsgood hy.2).2.1
    have hez : e (e'.symm z) = z := e'.right_inv hz
    rw [hez] at hreg
    exact hreg.contDiffWithinAt
  · intro y hy
    obtain ⟨_, _, hydet, hyA, hy₀, hy₁⟩ := hsgood hy.2
    refine ⟨hy₀, hy₁, ?_⟩
    apply (A y).mixed_ne_zero_of_null _ _ _ _ hyA hy₀ hy₁
    simpa only [Matrix.det_fin_two, jacobianMatrix, jacobianColumn, Matrix.of_apply,
      PrincipalPart.covectorDeterminant] using hydet

end Hyperbolic.CanonicalForm2D
