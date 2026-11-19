/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Differentiation.UniformBoundaryData
public import PDE.Spaces.Sobolev.Inequalities.Morrey.HigherOrder.Embedding
import PDE.FDeriv.Calculus

/-!
# Uniform classical derivatives of Morrey representatives

The adjacent Morrey fields are the coordinate derivatives in the open domain.
Their ambient continuity makes each derivative uniformly continuous on the bounded
domain. For `n < p` and `k + 1 ≤ m`, the Morrey representative of `U ∈ W^{m,p}(Ω)` is therefore
in `C^k(Ω̄)` in the sense of Evans, Appendix A.3: its derivatives of order at most `k` are uniformly
continuous on `Ω`. This is the `C^k` part of Evans §5.6.3, Theorem 6(ii), in the case `n < p`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.6.3, Theorem 6(ii), pp. 284-286; and App. A.3, p. 702.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (partialDeriv iteratedPartialDeriv)

namespace SobolevSpace.GraphSpace

open Set
open scoped Topology ENNReal Sobolev

variable {n m : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)} {p q : ℝ}
variable [Fact (1 ≤ ENNReal.ofReal p)] [hΩ : Boundary.C1ExtensionAtlas n Ω]

/-- Coordinate differentiation of a Morrey representative gives the adjacent fields.
The list is reversed because its head is the outermost derivative. -/
theorem iteratedPartialDeriv_finiteMorreyDerivativeRepresentativeOn
    (hp : (n : ℝ) < p) (hpq : p.HolderConjugate q)
    (α β : List (Fin n)) (hαβ : α.length + β.length + 1 ≤ m)
    (U : W^{m,ENNReal.ofReal p}(Ω)) {x : ℝ^n} (hx : x ∈ Ω) :
    iteratedPartialDeriv β
      (finiteMorreyDerivativeRepresentativeOn hp hpq α (by omega) U) x =
    finiteMorreyDerivativeRepresentativeOn hp hpq (α ++ β.reverse)
      (by
        simp only [List.length_append, List.length_reverse]
        omega) U x := by
  induction β generalizing x with
  | nil => simp only [iteratedPartialDeriv, List.reverse_nil, List.append_nil]
  | cons i β ih =>
    have heq :
        iteratedPartialDeriv β
          (finiteMorreyDerivativeRepresentativeOn hp hpq α (by omega) U) =ᶠ[𝓝 x]
        finiteMorreyDerivativeRepresentativeOn hp hpq (α ++ β.reverse)
          (by
            simp only [List.length_append, List.length_reverse]
            simp only [List.length_cons] at hαβ
            omega) U := by
      filter_upwards [hΩ.isOpen.mem_nhds hx] with y hy
      exact ih (by simp only [List.length_cons] at hαβ; omega) hy
    change partialDeriv i _ x = _
    rw [PDE.partialDeriv_congr_nhds i heq]
    unfold partialDeriv
    rw [(finiteMorreyDerivativeRepresentativeOn_hasFDerivAt hp hpq
      (α ++ β.reverse) (by
        simp only [List.length_append, List.length_reverse]
        simp only [List.length_cons] at hαβ
        omega) U hx).fderiv]
    simp [innerSL_apply_apply, EuclideanSpace.inner_single_right, List.reverse_cons,
      List.append_assoc]

/-- For `n < p`, `U ∈ W^{m,p}(Ω)` and a derivative word `α` with `|α| + k + 1 ≤ m`, the Morrey
representative of the `α`-derivative of `U` is `C^k` in `Ω`, and its classical derivatives of order
at most `k` are uniformly continuous on `Ω`. -/
theorem finiteMorreyDerivativeRepresentativeOn_contDiffUpToBoundary
    (hp : (n : ℝ) < p) (hpq : p.HolderConjugate q)
    (k : ℕ) (α : List (Fin n)) (hα : α.length + k + 1 ≤ m)
    (U : W^{m,ENNReal.ofReal p}(Ω)) :
    ContDiffUpToBoundary k
      (finiteMorreyDerivativeRepresentativeOn hp hpq α (by omega) U) Ω := by
  refine ⟨finiteMorreyDerivativeRepresentativeOn_contDiffOn hp hpq k α hα U,
    fun β hβ ↦ ?_⟩
  have hc := continuous_finiteMorreyDerivativeRepresentativeOn hp hpq (α ++ β.reverse)
    (by
      simp only [List.length_append, List.length_reverse]
      omega) U
  have hu := (hΩ.bounded.isCompact_closure.uniformContinuousOn_of_continuous hc.continuousOn).mono
    (show Ω ⊆ closure Ω from subset_closure)
  exact hu.congr fun x hx ↦
    (iteratedPartialDeriv_finiteMorreyDerivativeRepresentativeOn hp hpq α β (by omega) U hx).symm

/-- If `1 < p`, `n < p` and `k + 1 ≤ m`, every `U ∈ W^{m,p}(Ω)` has a representative `f`, equal
almost everywhere on `Ω` to the base representative of `U`, that is `C^k` on `closure Ω`
(`ContDiffOn`) and whose classical derivatives of order at most `k` are uniformly continuous
on `Ω`. -/
theorem exists_contDiffUpToBoundary_representative_of_dimension_lt
    {k : ℕ} {p : NNReal} [hpFact : Fact (1 ≤ (p : ℝ≥0∞))]
    (hp : 1 < p) (hnp : (n : ℝ) < p) (hkm : k + 1 ≤ m) :
    ∀ U : W^{m,(p : ℝ≥0∞)}(Ω),
    ∃ f : ℝ^n → ℝ, ContDiffUpToBoundary k f Ω ∧
      ContDiffOn ℝ k f (closure Ω) ∧
      f =ᵐ[domainMeasure n Ω] baseRepresentative U := by
  have hpR : 1 < (p : ℝ) := by exact_mod_cast hp
  revert hpFact
  rw [← (ENNReal.ofReal_coe_nnreal (p := p))]
  intro inst V
  let f := finiteMorreyDerivativeRepresentativeOn hnp
    (Real.HolderConjugate.conjExponent hpR) [] (by
      simp only [List.length_nil, Nat.zero_add]
      omega) V
  refine ⟨f,
    finiteMorreyDerivativeRepresentativeOn_contDiffUpToBoundary hnp
      (Real.HolderConjugate.conjExponent hpR) k [] (by simpa using hkm) V,
    finiteMorreyDerivativeRepresentativeOn_contDiffOn_closure hnp
      (Real.HolderConjugate.conjExponent hpR) k [] (by simpa using hkm) V, ?_⟩
  have hf := finiteMorreyDerivativeRepresentativeOn_ae hnp
    (Real.HolderConjugate.conjExponent hpR) [] (by
      simp only [List.length_nil, Nat.zero_add]
      omega) V
  simpa only [f, baseRepresentative, derivativeWordIndex_baseIndex, derivIndexOfList_nil] using hf

end SobolevSpace.GraphSpace
