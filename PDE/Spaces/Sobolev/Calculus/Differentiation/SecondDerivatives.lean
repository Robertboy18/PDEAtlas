/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Variational.Spaces.H1

/-!
# Assembling second weak derivatives

In every dimension, an `H¹` function whose first weak derivatives possess all coordinate weak
derivatives in `L²` has an `H²` representative. This is the Sobolev-space conclusion used after the
difference-quotient estimate in Evans, §6.3.1.

The hypotheses are exactly the weak second derivatives that the multidimensional
interior regularity argument constructs; the elliptic estimate itself is separate.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.1, proof of Theorem 1, step 6, p. 331, where the
  difference-quotient bound and §5.8.2, Theorem 3(ii), give `Du ∈ H¹_loc(U; ℝ^n)` and thus
  `u ∈ H²_loc(U)`.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set Function
open scoped ENNReal Sobolev

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The canonical family of weak-derivative rows used to assemble an `H²`
representative from an `H¹` function and coordinate second derivatives.
Rows of order zero and one come from `U`; the chosen representative `[i, j]`
of a second-order coordinate is the supplied representative of
`∂ⱼ(∂ᵢu)`. -/
def h2DerivativeRows (U : H¹(Ω))
    (g : Fin n → Fin n → ℝ^n → ℝ) (a : DerivIndex n 2) : ℝ^n → ℝ :=
  secondOrderRows
    (((U : WkpAmbientOn n 1 2 Ω) (baseIndex n 1) : DerivLp n 2 Ω) : ℝ^n → ℝ)
    (fun i ↦
      (((U : WkpAmbientOn n 1 2 Ω) (singleDerivIndex (n := n) i) :
        DerivLp n 2 Ω) : ℝ^n → ℝ))
    g a

/-- Assemble coordinatewise `L²` weak derivatives of the first derivatives
of an `H¹` function into an `H²` representative, together with the exact
finite-row formula for its squared `H²` norm.

The family `g i j` represents `∂ⱼ(∂ᵢu)`. No equality hypothesis
`g i j = g j i` is required: the Sobolev bundle stores one canonical
ordering for each symmetric second-order index. On an open domain,
alternative supplied representatives can be identified separately by weak
uniqueness; this constructor does not require that identification. -/
theorem exists_H2_of_firstDerivatives_haveWeakDerivatives
    (U : H¹(Ω))
    (g : Fin n → Fin n → ℝ^n → ℝ)
    (hg : ∀ i j, MemLp (g i j) 2 (domainMeasure n Ω))
    (hsecond : ∀ i j,
      HasWeakDerivativeOn (n := n) Ω [j]
        (((U : WkpAmbientOn n 1 2 Ω) (singleDerivIndex (n := n) i) :
          DerivLp n 2 Ω) : ℝ^n → ℝ)
        (g i j)) :
    ∃ W : W^{2,2}(Ω),
      ((((W : WkpAmbientOn n 2 2 Ω) (baseIndex n 2) : DerivLp n 2 Ω) : ℝ^n → ℝ)
        =ᵐ[domainMeasure n Ω]
        (((U : WkpAmbientOn n 1 2 Ω) (baseIndex n 1) : DerivLp n 2 Ω) : ℝ^n → ℝ)) ∧
      (∀ i,
        ((((W : WkpAmbientOn n 2 2 Ω)
            (firstDerivIndex n 2 (by omega) i) : DerivLp n 2 Ω) :
              ℝ^n → ℝ)
          =ᵐ[domainMeasure n Ω]
          (((U : WkpAmbientOn n 1 2 Ω) (singleDerivIndex (n := n) i) :
            DerivLp n 2 Ω) : ℝ^n → ℝ))) ∧
      (∀ (a : DerivIndex n 2) (i j : Fin n), a.toList = [i, j] →
        ((((W : WkpAmbientOn n 2 2 Ω) a : DerivLp n 2 Ω) : ℝ^n → ℝ)
          =ᵐ[domainMeasure n Ω] g i j)) ∧
      ‖W‖ ^ 2 =
        ∑ a : DerivIndex n 2,
          ∫ x, (h2DerivativeRows U g a x) ^ 2 ∂domainMeasure n Ω := by
  let f0 : ℝ^n → ℝ :=
    (((U : WkpAmbientOn n 1 2 Ω) (baseIndex n 1) : DerivLp n 2 Ω) : ℝ^n → ℝ)
  let f1 : Fin n → ℝ^n → ℝ := fun i ↦
    (((U : WkpAmbientOn n 1 2 Ω) (singleDerivIndex (n := n) i) :
      DerivLp n 2 Ω) : ℝ^n → ℝ)
  let d : DerivIndex n 2 → ℝ^n → ℝ := h2DerivativeRows U g
  have hbase : d (baseIndex n 2) = f0 := by
    simp [d, h2DerivativeRows, f0]
  have hf0mem : MemLp f0 2 (domainMeasure n Ω) := by
    exact Lp.memLp ((U : WkpAmbientOn n 1 2 Ω) (baseIndex n 1))
  have hf1mem : ∀ i, MemLp (f1 i) 2 (domainMeasure n Ω) := by
    intro i
    exact Lp.memLp ((U : WkpAmbientOn n 1 2 Ω) (singleDerivIndex (n := n) i))
  have hmem : ∀ a : DerivIndex n 2, MemLp (d a) 2 (domainMeasure n Ω) := by
    intro a
    exact a.inductionOnOrderTwo
      (motive := fun b ↦ MemLp (d b) 2 (domainMeasure n Ω))
      (by simpa [d, h2DerivativeRows, f0] using hf0mem)
      (fun i ↦ by simpa [d, h2DerivativeRows, f1] using hf1mem i)
      (fun b i j hlist ↦ by
        simpa [d, h2DerivativeRows,
          secondOrderRows_of_toList_eq_pair _ _ _ b i j hlist] using hg i j)
  have hu0 : HasWeakDerivativeOn (n := n) Ω [] f0 f0 := by
    simpa [f0] using U.property (baseIndex n 1)
  have hu1 : ∀ i, HasWeakDerivativeOn (n := n) Ω [i] f0 (f1 i) := by
    intro i
    simpa [f0, f1, firstDerivIndex_one] using
      U.property.hasWeakDerivativeOn_first (by norm_num) i
  have hu2 : ∀ i j, HasWeakDerivativeOn (n := n) Ω [i, j] f0 (g i j) := by
    intro i j
    exact (hu1 i).append_single j (by simpa [f1] using hsecond i j)
  have hweak : ∀ a : DerivIndex n 2,
      HasWeakDerivativeOn (n := n) Ω a.toList f0 (d a) := by
    intro a
    exact a.inductionOnOrderTwo
      (motive := fun b ↦ HasWeakDerivativeOn (n := n) Ω b.toList f0 (d b))
      (by simpa [d, h2DerivativeRows, f0] using hu0)
      (fun i ↦ by simpa [d, h2DerivativeRows, f1] using hu1 i)
      (fun b i j hlist ↦ by
        simpa [d, h2DerivativeRows, hlist,
          secondOrderRows_of_toList_eq_pair _ _ _ b i j hlist] using hu2 i j)
  let W := mkWkpSpaceOnOfWeakDerivatives
    (n := n) (k := 2) (p := (2 : ℝ≥0∞)) (Ω := Ω) f0 d hbase hmem hweak
  refine ⟨W, ?_, ?_, ?_, ?_⟩
  · simpa [W, f0, d, h2DerivativeRows] using
      mkWkpSpaceOnOfWeakDerivatives_apply_ae
      (n := n) (k := 2) (p := (2 : ℝ≥0∞)) (Ω := Ω) f0 d hbase hmem hweak
      (baseIndex n 2)
  · intro i
    have h := mkWkpSpaceOnOfWeakDerivatives_apply_ae
      (n := n) (k := 2) (p := (2 : ℝ≥0∞)) (Ω := Ω) f0 d hbase hmem hweak
      (firstDerivIndex n 2 (by omega) i)
    simpa [W, f1, d, h2DerivativeRows] using h
  · intro a i j hlist
    have h := mkWkpSpaceOnOfWeakDerivatives_apply_ae
      (n := n) (k := 2) (p := (2 : ℝ≥0∞)) (Ω := Ω) f0 d hbase hmem hweak a
    simpa [W, d, h2DerivativeRows,
      secondOrderRows_of_toList_eq_pair _ _ _ a i j hlist] using h
  · simpa [W, d] using norm_sq_mkWkpSpaceOnOfWeakDerivatives
      (n := n) (k := 2) (Ω := Ω) f0 d hbase hmem hweak

end SobolevSpace.GraphSpace
