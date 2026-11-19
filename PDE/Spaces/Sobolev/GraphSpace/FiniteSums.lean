/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Model.Notation

/-!
# Finite sums in Sobolev graph spaces

We split sums over first-order derivative indices into base and derivative
terms, and record representative formulas for finite sums of graph-space elements.
These identities are independent of any localization
or partition-of-unity construction.
-/

@[expose] public section

namespace SobolevSpace.GraphSpace

open MeasureTheory
open scoped ENNReal Sobolev

/-- Split a sum over all first-order derivative indices into the base term
and the first partial derivatives. -/
theorem sum_derivIndex_one {n : ℕ} {M : Type*} [AddCommMonoid M]
    (f : DerivIndex n 1 → M) :
    (∑ a, f a) = f (baseIndex n 1) + ∑ i : Fin n, f (singleDerivIndex n i) := by
  classical
  change (∑ a : Σ m : Fin 2, Sym (Fin n) m.1, f a) = _
  rw [Fintype.sum_sigma, Fin.sum_univ_two]
  congr 1
  · have hidx :
        (⟨(0 : Fin 2), (default : Sym (Fin n) 0)⟩ : DerivIndex n 1) =
          baseIndex n 1 := by
      apply Sigma.ext rfl
      apply heq_of_eq
      apply Sym.ext
      exact Multiset.card_eq_zero.mp (default : Sym (Fin n) 0).2
    change (∑ q : Sym (Fin n) 0, f ⟨(0 : Fin 2), q⟩) = f (baseIndex n 1)
    rw [Fintype.sum_unique, hidx]
  · exact (Fintype.sum_equiv (Sym.oneEquiv : Fin n ≃ Sym (Fin n) 1)
      (fun i ↦ f (singleDerivIndex n i))
      (fun q ↦ f ⟨(1 : Fin 2), q⟩) (fun _ ↦ rfl)).symm


variable {n k : ℕ} {p : ℝ≥0∞}

/-- Every derivative coordinate of a finite sum of Sobolev fields
is represented almost everywhere by the pointwise finite sum. -/
theorem coeFn_finsetSum_coordinate
    {Ω : Set (ℝ^n)} {ι : Type*}
    (s : Finset ι) (F : ι → W^{k,p}(Ω))
    (a : DerivIndex n k) :
    (((((∑ i ∈ s, F i) : W^{k,p}(Ω)) :
        WkpAmbientOn n k p Ω) a : DerivLp n p Ω) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω]
        fun x ↦ ∑ i ∈ s,
          (((F i : WkpAmbientOn n k p Ω) a :
            DerivLp n p Ω) : ℝ^n → ℝ) x := by
  classical
  rw [show
      (((((∑ i ∈ s, F i) : W^{k,p}(Ω)) :
          WkpAmbientOn n k p Ω) a : DerivLp n p Ω)) =
        ∑ i ∈ s,
          (((F i : WkpAmbientOn n k p Ω) a :
            DerivLp n p Ω)) by
    simp]
  exact MeasureTheory.Lp.coeFn_fun_finsetSum s fun i ↦
    ((F i : WkpAmbientOn n k p Ω) a : DerivLp n p Ω)

end SobolevSpace.GraphSpace
