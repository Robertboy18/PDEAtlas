/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Slobodeckij
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Rigid-motion invariance of the Gagliardo seminorm

The Gagliardo seminorm is invariant under linear isometries and translations: its kernel depends
only on `‖x - y‖`, while Lebesgue measure is invariant under both transformations. These elementary
facts are useful when reducing local extension arguments to standard coordinate patches. Di Nezza,
Palatucci and Valdinoci, in the proof of their extension theorem for Lipschitz domains (Theorem
5.4), transport the seminorm through bi-Lipschitz charts by a change of variables, (5.10), at the
cost of a constant; for rigid motions the constant is one.

The statements need no restriction on the fractional exponent `s`; the domain
is assumed measurable only to transport its restricted volume measure.

## Main results

* `gagliardoSq_comp_isometry` and `gagliardoSq_comp_add` preserve the squared
  Gagliardo seminorm.
* `memGagliardo_comp_isometry` and `memGagliardo_comp_add` transport
  `MemGagliardo`.

## References

* E. Di Nezza, G. Palatucci and E. Valdinoci, "Hitchhiker's guide to the fractional Sobolev spaces",
  *Bull. Sci. Math.* 136 (2012), 521-573, numbering of arXiv:1104.4345v3, Section 5, Theorem 5.4,
  the extension theorem for `W^{s,p}(Ω)` with `s ∈ (0, 1)`, `1 ≤ p < ∞` and `Ω` a Lipschitz domain
  with bounded boundary, and the change of variables (5.10) in its proof.
  <https://arxiv.org/abs/1104.4345v3>
* R. A. Adams and J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Pure and Applied Mathematics 140,
  Academic Press, 2003, Chapter 7, Fractional Order Spaces, pp. 205-260.
  <https://shop.elsevier.com/books/sobolev-spaces/adams/978-0-12-044143-3>
* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Princeton
  University Press, 1970, Chapter VI, Extensions and Restrictions, pp. 166-195.
  <https://doi.org/10.1515/9781400883882>
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace SobolevSpace.Fractional

variable {n : ℕ} {s : ℝ}

/-- The difference quotient commutes with a linear isometry. -/
theorem diffQuot_comp_isometry (T : (ℝ^n) ≃ₗᵢ[ℝ] (ℝ^n)) (v : ℝ^n → ℝ)
    (p : ℝ^n × ℝ^n) :
    diffQuot n s (v ∘ T) p = diffQuot n s v (Prod.map T T p) := by
  have hd : ‖T p.1 - T p.2‖ = ‖p.1 - p.2‖ := by
    rw [← T.map_sub, LinearIsometryEquiv.norm_map]
  simp only [diffQuot, Function.comp_apply, Prod.map_fst, Prod.map_snd, hd]

/-- The squared Gagliardo seminorm is invariant under a linear isometry. -/
theorem gagliardoSq_comp_isometry (T : (ℝ^n) ≃ₗᵢ[ℝ] (ℝ^n)) {Ω : Set (ℝ^n)}
    (hΩ : MeasurableSet Ω) (v : ℝ^n → ℝ) :
    gagliardoSq n s (T ⁻¹' Ω) (v ∘ T) = gagliardoSq n s Ω v := by
  have hT : MeasurePreserving (T : ℝ^n → ℝ^n)
      ((volume : Measure (ℝ^n)).restrict (T ⁻¹' Ω))
      ((volume : Measure (ℝ^n)).restrict Ω) :=
    T.measurePreserving.restrict_preimage hΩ
  have hemb :
      MeasurableEmbedding (Prod.map (T : ℝ^n → ℝ^n) (T : ℝ^n → ℝ^n)) :=
    T.toHomeomorph.measurableEmbedding.prodMap
      T.toHomeomorph.measurableEmbedding
  have hcomp := (hT.prod hT).lintegral_comp_emb hemb
    (fun q : ℝ^n × ℝ^n ↦ (‖diffQuot n s v q‖₊ : ℝ≥0∞) ^ 2)
  rw [gagliardoSq, gagliardoSq, ← hcomp]
  refine lintegral_congr fun p ↦ ?_
  rw [diffQuot_comp_isometry]

/-- The squared Gagliardo seminorm is invariant under translation. -/
theorem gagliardoSq_comp_add (h : ℝ^n) {Ω : Set (ℝ^n)}
    (hΩ : MeasurableSet Ω) (v : ℝ^n → ℝ) :
    gagliardoSq n s ((fun x ↦ x + h) ⁻¹' Ω) (fun x ↦ v (x + h)) =
      gagliardoSq n s Ω v := by
  have hT : MeasurePreserving (fun x : ℝ^n ↦ x + h)
      ((volume : Measure (ℝ^n)).restrict ((fun x ↦ x + h) ⁻¹' Ω))
      ((volume : Measure (ℝ^n)).restrict Ω) :=
    (measurePreserving_add_right (volume : Measure (ℝ^n)) h).restrict_preimage hΩ
  have hemb :
      MeasurableEmbedding
        (Prod.map (fun x : ℝ^n ↦ x + h) (fun x : ℝ^n ↦ x + h)) :=
    (Homeomorph.addRight h).measurableEmbedding.prodMap
      (Homeomorph.addRight h).measurableEmbedding
  have hcomp := (hT.prod hT).lintegral_comp_emb hemb
    (fun q : ℝ^n × ℝ^n ↦ (‖diffQuot n s v q‖₊ : ℝ≥0∞) ^ 2)
  rw [gagliardoSq, gagliardoSq, ← hcomp]
  refine lintegral_congr fun p ↦ ?_
  have hd : ‖(p.1 + h) - (p.2 + h)‖ = ‖p.1 - p.2‖ := by
    rw [show (p.1 + h) - (p.2 + h) = p.1 - p.2 by abel]
  simp only [diffQuot, Prod.map_fst, Prod.map_snd, hd]

/-- The Gagliardo condition is preserved by a linear isometry. -/
theorem memGagliardo_comp_isometry (T : (ℝ^n) ≃ₗᵢ[ℝ] (ℝ^n))
    {Ω : Set (ℝ^n)} (hΩ : MeasurableSet Ω) {v : ℝ^n → ℝ}
    (hv : MemGagliardo n s Ω v) :
    MemGagliardo n s (T ⁻¹' Ω) (v ∘ T) := by
  obtain ⟨hL2, hgag⟩ := (memGagliardo_iff v).1 hv
  refine (memGagliardo_iff (v ∘ T)).2 ⟨?_, ?_⟩
  · exact hL2.comp_measurePreserving
      (T.measurePreserving.restrict_preimage hΩ)
  · rw [gagliardoSq_comp_isometry T hΩ]
    exact hgag

/-- The Gagliardo condition is preserved by translation. -/
theorem memGagliardo_comp_add (h : ℝ^n) {Ω : Set (ℝ^n)}
    (hΩ : MeasurableSet Ω) {v : ℝ^n → ℝ}
    (hv : MemGagliardo n s Ω v) :
    MemGagliardo n s ((fun x ↦ x + h) ⁻¹' Ω) (fun x ↦ v (x + h)) := by
  obtain ⟨hL2, hgag⟩ := (memGagliardo_iff v).1 hv
  refine (memGagliardo_iff (fun x ↦ v (x + h))).2 ⟨?_, ?_⟩
  · exact hL2.comp_measurePreserving
      ((measurePreserving_add_right (volume : Measure (ℝ^n)) h).restrict_preimage hΩ)
  · rw [gagliardoSq_comp_add h hΩ]
    exact hgag

end SobolevSpace.Fractional
