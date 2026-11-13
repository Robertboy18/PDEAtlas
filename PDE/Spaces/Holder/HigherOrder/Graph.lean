/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.UniformDerivativeGraph
public import PDE.Common.Euclidean
public import PDE.Spaces.Holder.HigherOrder.MultiIndex
public import PDE.Spaces.Holder.On

/-!
# The closed graph of classical Hölder derivatives

All derivative fields are bounded continuous functions on the closure. Their first
derivatives in the open domain are the next coordinate fields, and the top-order
fields lie in the scalar Hölder space. Continuity on the closure gives uniform
continuity on every bounded subset, which is the condition in the definition of `C^k(Ū)` in
Evans (App. A.3, p. 702). Global uniform continuity of lower-order fields is not required on an
unbounded domain.

## Main definitions

* `HolderSpace.JetData n k Ω γ`: bounded continuous fields indexed by the multiindices of order
  at most `k`, with a scalar Hölder representative for each multiindex of order `k`.
* `HolderSpace.JetData.Compatible`: the fields are the classical derivatives of each other in
  `Ω`, and the Hölder representatives agree with the top-order fields.
* `HolderSpace.CKGammaOn n k Ω γ`: the submodule of compatible fields, with the inherited norm.

## Main results

* `HolderSpace.JetData.isClosed_compatible`: for open `Ω`, uniform limits of compatible fields
  are compatible.
* `HolderSpace.CKGammaOn.completeSpace`: for open `Ω`, `CKGammaOn n k Ω γ` is complete.

## How it works

Evans states that `C^{k,γ}(Ū)` is a Banach space (§5.1, Theorem 1, p. 255) and leaves the proof
as an exercise. We obtain completeness by realizing the space as a closed subspace of the finite
product `JetData n k Ω γ` of Banach spaces. The derivative relations pass to uniform limits by
`BoundedContinuousFunction.hasFDerivAt_of_tendsto`, a wrapper around Mathlib's
`hasFDerivAt_of_tendstoUniformlyOn`; this gives `JetData.isClosed_compatible`, and
`IsClosed.completeSpace_coe` then gives `completeSpace`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, App. A.3, p. 702, and §5.1, Theorem 1, p. 255.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology BoundedContinuousFunction

namespace HolderSpace

/-- Ambient derivative fields, with Hölder control recorded at the top order. -/
abbrev JetData (n k : ℕ) (Ω : Set (ℝ^n)) (γ : Exponent) :=
  (MultiIndex n k → closure Ω →ᵇ ℝ) ×
    (MultiIndex.Top n k → C0GammaOn (closure Ω) γ)

namespace JetData

variable {n k : ℕ} {Ω : Set (ℝ^n)} {γ : Exponent}

/-- The derivative of one field, assembled from its coordinate successor fields. -/
def gradientCLM (a : MultiIndex n k) (ha : a.order < k) :
    JetData n k Ω γ →L[ℝ] (closure Ω →ᵇ (ℝ^n →L[ℝ] ℝ)) :=
  ∑ i : Fin n,
    (ContinuousLinearMap.compLeftContinuousBounded (closure Ω)
      (ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.proj i))).comp
        ((ContinuousLinearMap.proj (a.succ ha i)).comp (ContinuousLinearMap.fst ℝ _ _))

/-- Evaluation of the assembled derivative is the usual coordinate formula. -/
theorem gradientCLM_apply (a : MultiIndex n k) (ha : a.order < k)
    (f : JetData n k Ω γ) (x : closure Ω) :
    gradientCLM a ha f x = ∑ i : Fin n, f.1 (a.succ ha i) x • EuclideanSpace.proj i := by
  simp [gradientCLM, BoundedContinuousFunction.coe_sum]

/-- Compatibility means that the fields are derivatives of each other.
The top-order Hölder representatives must equal their continuous derivative fields. -/
def Compatible (f : JetData n k Ω γ) : Prop :=
  (∀ a : MultiIndex.Top n k, (f.2 a).toBoundedContinuousFunction = f.1 a.1) ∧
  ∀ a (ha : a.order < k) x (hx : x ∈ Ω),
    HasFDerivAt (Function.extend Subtype.val (f.1 a) 0)
      (gradientCLM a ha f ⟨x, subset_closure hx⟩) x

/-- Zero fields satisfy the derivative relations. -/
theorem compatible_zero : Compatible (0 : JetData n k Ω γ) := by
  refine ⟨fun _ ↦ rfl, ?_⟩
  intro a ha x hx
  change HasFDerivAt (Function.extend Subtype.val (0 : closure Ω →ᵇ ℝ) 0) _ x
  rw [BoundedContinuousFunction.extend_zero_zero]
  simpa only [map_zero, BoundedContinuousFunction.coe_zero, Pi.zero_apply] using
    (hasFDerivAt_zero (𝕜 := ℝ) (F := ℝ) x)

/-- Compatible derivative fields are closed under addition. -/
theorem Compatible.add {f g : JetData n k Ω γ} (hf : Compatible f) (hg : Compatible g) :
    Compatible (f + g) := by
  refine ⟨?_, ?_⟩
  · intro a
    exact congrArg₂ (· + ·) (hf.1 a) (hg.1 a)
  · intro a ha x hx
    change HasFDerivAt (Function.extend Subtype.val (f.1 a + g.1 a) 0) _ x
    rw [BoundedContinuousFunction.extend_zero_add]
    simpa using (hf.2 a ha x hx).add (hg.2 a ha x hx)

/-- Compatible derivative fields are closed under real scalar multiplication. -/
theorem Compatible.smul {f : JetData n k Ω γ} (hf : Compatible f) (c : ℝ) :
    Compatible (c • f) := by
  refine ⟨?_, ?_⟩
  · intro a
    exact congrArg (c • ·) (hf.1 a)
  · intro a ha x hx
    change HasFDerivAt (Function.extend Subtype.val (c • f.1 a) 0) _ x
    rw [BoundedContinuousFunction.extend_zero_smul]
    simpa using (hf.2 a ha x hx).const_smul c

/-- The linear subspace cut out by the classical derivative relations. -/
def compatibleSubmodule (n k : ℕ) (Ω : Set (ℝ^n)) (γ : Exponent) :
    Submodule ℝ (JetData n k Ω γ) where
  carrier := {f | Compatible f}
  zero_mem' := compatible_zero
  add_mem' := Compatible.add
  smul_mem' c _ hf := hf.smul c

/-- Uniform limits preserve the derivative relations and the top-order Hölder fields. -/
theorem isClosed_compatible (hΩ : IsOpen Ω) :
    IsClosed {f : JetData n k Ω γ | Compatible f} := by
  refine IsSeqClosed.isClosed ?_
  intro f g hf hg
  have hfield (a : MultiIndex n k) :
      Tendsto (fun j ↦ (f j).1 a) atTop (𝓝 (g.1 a)) :=
    ((continuous_apply a).comp continuous_fst).tendsto g |>.comp hg
  refine ⟨?_, ?_⟩
  · intro a
    have ht := C0GammaOn.toBoundedContinuousFunctionCLM.continuous.tendsto (g.2 a)
      |>.comp (((continuous_apply a).comp continuous_snd).tendsto g |>.comp hg)
    exact tendsto_nhds_unique (ht.congr fun j ↦ (hf j).1 a) (hfield a.1)
  · intro a ha x hx
    exact BoundedContinuousFunction.hasFDerivAt_of_tendsto hΩ subset_closure
      (hfield a) ((gradientCLM a ha).continuous.tendsto g |>.comp hg)
      (fun j y hy ↦ (hf j).2 a ha y hy) hx

end JetData

/-- `C^{k,γ}` functions on the closure of `Ω`, represented by their compatible derivative
fields. For open `Ω` this is the classical space; completeness (`completeSpace`) and the
identification with `C^k` functions use `IsOpen Ω`. The inherited maximum norm is equivalent
to the derivative sum norm. -/
def CKGammaOn (n k : ℕ) (Ω : Set (ℝ^n)) (γ : Exponent) : Type :=
  ↥(JetData.compatibleSubmodule n k Ω γ)
  deriving AddCommGroup, Module ℝ, NormedAddCommGroup, NormedSpace ℝ

namespace CKGammaOn

variable {n k : ℕ} {Ω : Set (ℝ^n)} {γ : Exponent}

/-- The derivative graph is a closed subspace of a finite product of Banach spaces. -/
theorem completeSpace (hΩ : IsOpen Ω) : CompleteSpace (CKGammaOn n k Ω γ) := by
  have : IsClosed (JetData.compatibleSubmodule n k Ω γ : Set (JetData n k Ω γ)) :=
    JetData.isClosed_compatible hΩ
  exact IsClosed.completeSpace_coe

instance [hΩ : Fact (IsOpen Ω)] : CompleteSpace (CKGammaOn n k Ω γ) :=
  completeSpace hΩ.out

end CKGammaOn

end HolderSpace
