/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.HigherForcing
public import PDE.Spaces.Sobolev.Calculus.Composition.HigherOrder.FiniteLipschitz
public import PDE.Spaces.Sobolev.GraphSpace.Operators.PartialDerivatives

/-!
# Smooth first-jet forcing at the sharp Sobolev order

Spatial derivatives, velocity and displacement form a finite family in Hˢ
when the state belongs to Hˢ⁺¹ × Hˢ. The sharp finite composition theorem makes
the full reaction locally Lipschitz for exactly s > n/2. The source cancels
the mass in the higher wave semigroup. This is the evolution
construction for Theorem 3 of Evans, §12.2.2, with order `k = s + 1`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.2.2, Theorem 3.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Sobolev SobolevSpace.WholeSpaceHilbert

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet

open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Composition
open PDE.Analysis.Evolution

variable {n k : ℕ}

/-- Assemble the weak spatial derivatives, velocity and displacement as a
finite family at the same Sobolev order. -/
def higherJetCLM : (W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) →L[ℝ]
    (Fin n ⊕ Bool → W^{k,2}(ℝ^n)) :=
  ContinuousLinearMap.pi fun j ↦ Sum.elim
    (fun i ↦ (partialDerivCLM i).comp (ContinuousLinearMap.fst ℝ _ _))
    (fun b ↦ if b then
      (lowerOrderCLM (Nat.le_succ k)).comp (ContinuousLinearMap.fst ℝ _ _)
      else ContinuousLinearMap.snd ℝ _ _) j

/-- Convert finite scalar coordinates to the gradient, velocity and
displacement argument of the reaction. -/
def decodeJetCLM : (Fin n ⊕ Bool → ℝ) →L[ℝ] (ℝ^n × ℝ × ℝ) :=
  (((EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap).comp
    (ContinuousLinearMap.pi fun i ↦ ContinuousLinearMap.proj (Sum.inl i))).prod
    ((ContinuousLinearMap.proj (Sum.inr false)).prod
      (ContinuousLinearMap.proj (Sum.inr true)))

variable [NeZero n] {f : (ℝ^n × ℝ × ℝ) → ℝ}

/-- The smooth full-jet reaction as a Sobolev graph. -/
def higherReaction (hk : (n : ℝ) < 2 * (k : ℝ))
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0)
    (z : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) : W^{k,2}(ℝ^n) :=
  finiteComposition hk (hf.comp (decodeJetCLM (n := n)).contDiff)
    (by simpa only [Function.comp_apply, map_zero] using hf0) (higherJetCLM (n := n) (k := k) z)

/-- The higher reaction is precisely the first-derivative expression almost
everywhere, using the base coordinates of the weak partial derivatives. -/
theorem higherReaction_ae (hk : (n : ℝ) < 2 * (k : ℝ)) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0)
    (z : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) :
    baseRepresentative (higherReaction hk hf hf0 z) =ᵐ[volume]
      (fun y ↦ f ((EuclideanSpace.equiv (Fin n) ℝ).symm (fun i ↦ baseRepresentative (∂[i] z.1) y),
      baseRepresentative z.2 y, baseRepresentative z.1 y)) :=
  finiteComposition_ae hk (hf.comp (decodeJetCLM (n := n)).contDiff)
    (by simpa only [Function.comp_apply, map_zero] using hf0) (higherJetCLM (n := n) (k := k) z)

/-- The full first-derivative reaction is locally Lipschitz in the high norm
at exactly the strict threshold s > n/2. -/
theorem locallyLipschitz_higherReaction (hk : (n : ℝ) < 2 * (k : ℝ))
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0) :
    LocallyLipschitz (higherReaction hk hf hf0) := by
  have hF := locallyLipschitz_finiteComposition (ι := Fin n ⊕ Bool) hk
    (hf.comp (decodeJetCLM (n := n)).contDiff)
    (by simpa only [Function.comp_apply, map_zero] using hf0)
  have hJ := (higherJetCLM (n := n) (k := k)).lipschitzWith.locallyLipschitz
  exact hF.comp hJ

/-- The mass-canceling first-jet source at the sharp higher energy level. -/
def higherSource (hk : (n : ℝ) < 2 * (k : ℝ))
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0)
    (z : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) :
    W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n) :=
  (0, lowerOrderCLM (Nat.le_succ k) z.1 - higherReaction hk hf hf0 z)

/-- The first-jet source satisfies the hypothesis of the local
semigroup existence and uniqueness theorem. -/
theorem locallyLipschitz_higherSource (hk : (n : ℝ) < 2 * (k : ℝ))
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0) :
    LocallyLipschitz (higherSource hk hf hf0) := by
  let Q : (W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) →L[ℝ] W^{k,2}(ℝ^n) :=
    (lowerOrderCLM (Nat.le_succ k)).comp (ContinuousLinearMap.fst ℝ _ _)
  have hQ : LocallyLipschitz Q := Q.lipschitzWith.locallyLipschitz
  exact (LocallyLipschitz.const (0 : W^{k + 1,2}(ℝ^n))).prodMk
    (hQ.sub (locallyLipschitz_higherReaction hk hf hf0))

/-- Continuous state map for the full-jet higher evolution. -/
def higherMap (hk : (n : ℝ) < 2 * (k : ℝ))
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0) :
    C(W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n), W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) :=
  ⟨higherSource hk hf hf0, (locallyLipschitz_higherSource hk hf hf0).continuous⟩

/-- Arbitrary data at the Sobolev threshold give a unique local
continuous mild trajectory for the full-jet reaction. -/
theorem exists_unique_higher_mild (hk : (n : ℝ) < 2 * (k : ℝ)) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf0 : f 0 = 0) (x : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) :
    ∃ τ : NNReal, 0 < τ ∧ ∃! u : C(Icc (0 : ℝ) (τ : ℝ), W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)),
      (higherLinearSemigroup n k).IsMildSolutionOn (higherMap hk hf hf0) x τ u := by
  have hF : LocallyLipschitz (higherMap hk hf hf0) := locallyLipschitz_higherSource hk hf hf0
  let S := higherLinearSemigroup n k
  exact S.exists_pos_existsUnique_mildSolutionOn_of_locallyLipschitz_unrestricted hF x

end PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet
