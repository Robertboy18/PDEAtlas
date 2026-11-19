/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Morrey.FiniteExponent.Embedding
import PDE.Spaces.Sobolev.Boundary.Regularity.Closure
import PDE.Spaces.Sobolev.Calculus.Differentiation.WeakToClassical

import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Higher-order Morrey embeddings

For finite `p > n > 0`, the first-order Morrey embedding gives a bounded
`C^{0,1-n/p}` representative of every `W^{1,p}` function. Applying it to
the derivative-word extraction

`W^{m,p}(Ω) → W^{1,p}(Ω)`

gives a Hölder representative for every weak derivative of order strictly
less than `m`.

We bundle these maps individually and as a finite Hölder jet. The
jet is a completed Banach-space target. Adjacent representatives satisfy
the weak-derivative relation, and on the interior they reconstruct the
ordinary Fréchet derivative. Extending this reconstruction through the
boundary uses the operational boundary charts and mathlib's
derivative-extension theorem.

This is the case `n < p < ∞` of Evans, PDE, §5.6.3, Theorem 6(ii): then `[n/p] = 0`, and
step 2 of Evans's proof applies Morrey's inequality to each `D^α u` with `|α| ≤ k - 1`, as
we do.

## Main results

* `finiteMorreyDerivativeEmbedding`, `finiteMorreyDerivativeEmbeddingOn`: the bounded linear
  maps sending `U ∈ W^{m,p}` to the `C^{0,1-n/p}` representative of `D^α U` for `|α| + 1 ≤ m`, on
  `ℝ^n` and on a `C¹` extension domain, with a.e. agreement (`_ae`) and norm bounds (`norm_…_le`).
* `finiteMorreyDerivativeRepresentativeOn_hasWeakDerivativeOn`: adjacent representatives satisfy
  the weak-derivative relation `∂ᵢ (D^α U) = D^{α i} U` on `Ω`.
* `finiteMorreyDerivativeRepresentativeOn_hasFDerivAt`,
  `finiteMorreyDerivativeRepresentativeOn_contDiffOn`: in the interior, the representative of
  `D^α U` is classically differentiable with derivative given by the representatives of the
  `D^{α i} U`, hence `C^k` when `|α| + k + 1 ≤ m`.
* `finiteMorreyDerivativeRepresentativeOn_hasFDerivWithinAt_closure`,
  `finiteMorreyDerivativeRepresentativeOn_contDiffOn_closure`: the same within the closure of `Ω`.
* `finiteMorreyJetEmbeddingOn`: all representatives of order at most `k` of a `W^{k+1,p}`
  function, bundled as one bounded linear map into the finite jet `MorreyHolderJetOn n k Ω γ`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.6.3, Theorem 6(ii), (31)-(32), pp. 284-285, and step 2 of
  its proof, p. 285.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace
namespace GraphSpace

open MeasureTheory Set
open scoped ENNReal Topology Sobolev

/-- The completed finite jet of `C^{0,γ}` representatives indexed by all
derivatives of order at most `k`. -/
abbrev MorreyHolderJetOn
    (n k : ℕ) (Ω : Type*) [MetricSpace Ω] (γ : HolderSpace.Exponent) :=
  (a : DerivIndex n k) → HolderSpace.C0GammaOn Ω γ

/-! ## Global derivative representatives -/

/-- The global Morrey embedding applied to the weak derivative `D^α U`.

The order condition `|α| + 1 ≤ m` ensures that the order-`m` Sobolev bundle
contains `D^α U` and all of its first weak derivatives. -/
noncomputable def finiteMorreyDerivativeEmbedding
    {n m : ℕ} {p q : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hn : 0 < n) (hp : (n : ℝ) < p)
    (hpq : p.HolderConjugate q)
    (α : List (Fin n)) (hα : α.length + 1 ≤ m) :
    W^{m,(ENNReal.ofReal p)}(ℝ^n) →L[ℝ]
      HolderSpace.C0GammaOn (ℝ^n)
        (finiteMorreyHolderExponent n p hn hp) :=
  (SobolevSpace.finiteMorreyEmbedding hn hp hpq).comp
    (derivativeWordCLM
      (n := n) (m := m) (r := 1) (p := ENNReal.ofReal p)
      (Ω := Set.univ) α hα)

/-- The derivative embedding is the first-order Morrey embedding applied to the `W^{1,p}` bundle
of `D^α U` extracted by `derivativeWordCLM`. -/
@[simp]
theorem finiteMorreyDerivativeEmbedding_apply
    {n m : ℕ} {p q : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hn : 0 < n) (hp : (n : ℝ) < p)
    (hpq : p.HolderConjugate q)
    (α : List (Fin n)) (hα : α.length + 1 ≤ m)
    (U : W^{m,(ENNReal.ofReal p)}(ℝ^n)) :
    finiteMorreyDerivativeEmbedding hn hp hpq α hα U =
      SobolevSpace.finiteMorreyEmbedding hn hp hpq
        (derivativeWordCLM
          (n := n) (m := m) (r := 1) (p := ENNReal.ofReal p)
          (Ω := Set.univ) α hα U) :=
  rfl

/-- The global derivative representative agrees almost everywhere with the
corresponding coordinate of the higher-order Sobolev bundle. -/
theorem finiteMorreyDerivativeEmbedding_ae
    {n m : ℕ} {p q : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hn : 0 < n) (hp : (n : ℝ) < p)
    (hpq : p.HolderConjugate q)
    (α : List (Fin n)) (hα : α.length + 1 ≤ m)
    (U : W^{m,(ENNReal.ofReal p)}(ℝ^n)) :
    (fun x ↦ finiteMorreyDerivativeEmbedding hn hp hpq α hα U x)
        =ᵐ[volume]
      (((U : WkpAmbientOn n m (ENNReal.ofReal p) Set.univ)
        (derivativeWordIndex (n := n) (m := m) (r := 1)
          α hα (baseIndex n 1)) :
          DerivLp n (ENNReal.ofReal p) Set.univ) :
        ℝ^n → ℝ) := by
  simpa [finiteMorreyDerivativeEmbedding, GraphSpace.baseRepresentative] using
    SobolevSpace.finiteMorreyEmbedding_ae hn hp hpq
      (derivativeWordCLM
        (n := n) (m := m) (r := 1) (p := ENNReal.ofReal p)
        (Ω := Set.univ) α hα U)

/-- The explicit first-order Morrey constant controls every extracted
derivative representative. -/
theorem norm_finiteMorreyDerivativeEmbedding_le
    {n m : ℕ} {p q : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hn : 0 < n) (hp : (n : ℝ) < p)
    (hpq : p.HolderConjugate q)
    (α : List (Fin n)) (hα : α.length + 1 ≤ m)
    (U : W^{m,(ENNReal.ofReal p)}(ℝ^n)) :
    ‖finiteMorreyDerivativeEmbedding hn hp hpq α hα U‖ ≤
      finiteMorreyEmbeddingConstant n p q *
        ‖derivativeWordCLM
          (n := n) (m := m) (r := 1) (p := ENNReal.ofReal p)
          (Ω := Set.univ) α hα U‖ :=
  SobolevSpace.norm_morreyHolderRepresentative_le hn hp hpq
    (derivativeWordCLM
      (n := n) (m := m) (r := 1) (p := ENNReal.ofReal p)
      (Ω := Set.univ) α hα U)

/-! ## Domain derivative representatives -/

/-- The ambient representative underlying the domain Morrey embedding of
`D^α U`. Its restriction to `Ω` is
`finiteMorreyDerivativeEmbeddingOn hp hpq α hα U`. -/
def finiteMorreyDerivativeRepresentativeOn
    {n m : ℕ} {Ω : Set (ℝ^n)} {p q : ℝ}
    [Fact (0 < n)] [Fact (1 ≤ ENNReal.ofReal p)]
    [Boundary.C1ExtensionAtlas n Ω]
    (hp : (n : ℝ) < p) (hpq : p.HolderConjugate q)
    (α : List (Fin n)) (hα : α.length + 1 ≤ m)
    (U : W^{m,ENNReal.ofReal p}(Ω)) :
    ℝ^n → ℝ :=
  fun x ↦
    SobolevSpace.finiteMorreyEmbedding Fact.out hp hpq
      (Extension.C1.extensionCLM
        (n := n) (p := ENNReal.ofReal p) (Ω := Ω)
        (derivativeWordCLM
          (n := n) (m := m) (r := 1) (p := ENNReal.ofReal p)
          (Ω := Ω) α hα U)) x

/-- The ambient representative used by the domain derivative embedding is
continuous on all of `ℝ^n`. -/
theorem continuous_finiteMorreyDerivativeRepresentativeOn
    {n m : ℕ} {Ω : Set (ℝ^n)} {p q : ℝ}
    [Fact (0 < n)] [Fact (1 ≤ ENNReal.ofReal p)]
    [Boundary.C1ExtensionAtlas n Ω]
    (hp : (n : ℝ) < p) (hpq : p.HolderConjugate q)
    (α : List (Fin n)) (hα : α.length + 1 ≤ m)
    (U : W^{m,ENNReal.ofReal p}(Ω)) :
    Continuous
      (finiteMorreyDerivativeRepresentativeOn hp hpq α hα U) :=
  (SobolevSpace.finiteMorreyEmbedding Fact.out hp hpq
    (Extension.C1.extensionCLM
      (n := n) (p := ENNReal.ofReal p) (Ω := Ω)
      (derivativeWordCLM
        (n := n) (m := m) (r := 1) (p := ENNReal.ofReal p)
        (Ω := Ω) α hα U))).continuous

/-- The bounded-domain Morrey embedding applied to the weak derivative
`D^α U`. -/
noncomputable def finiteMorreyDerivativeEmbeddingOn
    {n m : ℕ} {Ω : Set (ℝ^n)} {p q : ℝ}
    [Fact (0 < n)] [Fact (1 ≤ ENNReal.ofReal p)]
    [Boundary.C1ExtensionAtlas n Ω]
    (hp : (n : ℝ) < p) (hpq : p.HolderConjugate q)
    (α : List (Fin n)) (hα : α.length + 1 ≤ m) :
    W^{m,ENNReal.ofReal p}(Ω) →L[ℝ]
      HolderSpace.C0GammaOn Ω
        (finiteMorreyHolderExponent n p Fact.out hp) :=
  (SobolevSpace.finiteMorreyEmbeddingOn hp hpq).comp
    (derivativeWordCLM
      (n := n) (m := m) (r := 1) (p := ENNReal.ofReal p)
      (Ω := Ω) α hα)

/-- On a domain, the derivative embedding evaluates to the ambient representative
`finiteMorreyDerivativeRepresentativeOn` at points of `Ω`. -/
@[simp]
theorem finiteMorreyDerivativeEmbeddingOn_apply
    {n m : ℕ} {Ω : Set (ℝ^n)} {p q : ℝ}
    [Fact (0 < n)] [Fact (1 ≤ ENNReal.ofReal p)]
    [Boundary.C1ExtensionAtlas n Ω]
    (hp : (n : ℝ) < p) (hpq : p.HolderConjugate q)
    (α : List (Fin n)) (hα : α.length + 1 ≤ m)
    (U : W^{m,ENNReal.ofReal p}(Ω)) (x : Ω) :
    finiteMorreyDerivativeEmbeddingOn hp hpq α hα U x =
      finiteMorreyDerivativeRepresentativeOn hp hpq α hα U x :=
  rfl

/-- The domain derivative representative agrees almost everywhere with the
corresponding coordinate of the higher-order Sobolev bundle. -/
theorem finiteMorreyDerivativeRepresentativeOn_ae
    {n m : ℕ} {Ω : Set (ℝ^n)} {p q : ℝ}
    [Fact (0 < n)] [Fact (1 ≤ ENNReal.ofReal p)]
    [Boundary.C1ExtensionAtlas n Ω]
    (hp : (n : ℝ) < p) (hpq : p.HolderConjugate q)
    (α : List (Fin n)) (hα : α.length + 1 ≤ m)
    (U : W^{m,ENNReal.ofReal p}(Ω)) :
    finiteMorreyDerivativeRepresentativeOn hp hpq α hα U
        =ᵐ[domainMeasure n Ω]
      (((U : WkpAmbientOn n m (ENNReal.ofReal p) Ω)
        (derivativeWordIndex (n := n) (m := m) (r := 1)
          α hα (baseIndex n 1)) :
          DerivLp n (ENNReal.ofReal p) Ω) :
        ℝ^n → ℝ) := by
  change
    (fun x ↦
      SobolevSpace.finiteMorreyEmbedding Fact.out hp hpq
        (Extension.C1.extensionCLM
          (n := n) (p := ENNReal.ofReal p) (Ω := Ω)
          (derivativeWordCLM
            (n := n) (m := m) (r := 1) (p := ENNReal.ofReal p)
            (Ω := Ω) α hα U)) x) =ᵐ[domainMeasure n Ω] _
  simpa only [derivativeWordCLM_apply] using
    SobolevSpace.finiteMorreyEmbeddingOn_ae hp hpq
      (derivativeWordCLM
        (n := n) (m := m) (r := 1) (p := ENNReal.ofReal p)
        (Ω := Ω) α hα U)

/-- Quantitative domain estimate for an extracted derivative
representative. -/
theorem norm_finiteMorreyDerivativeEmbeddingOn_le
    {n m : ℕ} {Ω : Set (ℝ^n)} {p q : ℝ}
    [Fact (0 < n)] [Fact (1 ≤ ENNReal.ofReal p)]
    [Boundary.C1ExtensionAtlas n Ω]
    (hp : (n : ℝ) < p) (hpq : p.HolderConjugate q)
    (α : List (Fin n)) (hα : α.length + 1 ≤ m)
    (U : W^{m,ENNReal.ofReal p}(Ω)) :
    ‖finiteMorreyDerivativeEmbeddingOn hp hpq α hα U‖ ≤
      finiteMorreyEmbeddingConstant n p q *
        ‖Extension.C1.extensionCLM
          (n := n) (p := ENNReal.ofReal p) (Ω := Ω)‖ *
        ‖derivativeWordCLM
          (n := n) (m := m) (r := 1) (p := ENNReal.ofReal p)
          (Ω := Ω) α hα U‖ :=
  SobolevSpace.norm_finiteMorreyEmbeddingOn_le hp hpq
    (derivativeWordCLM
      (n := n) (m := m) (r := 1) (p := ENNReal.ofReal p)
      (Ω := Ω) α hα U)

/-! ## Compatibility of adjacent jet coordinates -/

/-- Adjacent ambient representatives in the higher-order Morrey jet satisfy
the certified weak-derivative relation on the original domain. -/
theorem finiteMorreyDerivativeRepresentativeOn_hasWeakDerivativeOn
    {n m : ℕ} {Ω : Set (ℝ^n)} {p q : ℝ}
    [Fact (0 < n)] [Fact (1 ≤ ENNReal.ofReal p)]
    [Boundary.C1ExtensionAtlas n Ω]
    (hp : (n : ℝ) < p) (hpq : p.HolderConjugate q)
    (α : List (Fin n)) (hα : α.length + 2 ≤ m)
    (i : Fin n) (U : W^{m,ENNReal.ofReal p}(Ω)) :
    HasWeakDerivativeOn (n := n) Ω [i]
      (finiteMorreyDerivativeRepresentativeOn hp hpq α (by omega) U)
      (finiteMorreyDerivativeRepresentativeOn
        hp hpq (α ++ [i]) (by simp; omega) U) := by
  let hαone : α.length + 1 ≤ m := by omega
  let hαi : (α ++ [i]).length + 1 ≤ m := by
    simp
    omega
  let V : W^{1,ENNReal.ofReal p}(Ω) :=
    derivativeWordCLM
      (n := n) (m := m) (r := 1) (p := ENNReal.ofReal p)
      (Ω := Ω) α hαone U
  have hraw :
      HasWeakDerivativeOn (n := n) Ω [i]
        (((V : WkpAmbientOn n 1 (ENNReal.ofReal p) Ω)
          (baseIndex n 1) :
            DerivLp n (ENNReal.ofReal p) Ω) :
          ℝ^n → ℝ)
        (((V : WkpAmbientOn n 1 (ENNReal.ofReal p) Ω)
          (singleDerivIndex n i) :
            DerivLp n (ENNReal.ofReal p) Ω) :
          ℝ^n → ℝ) := by
    simpa only [firstDerivIndex_one] using
      V.property.hasWeakDerivativeOn_first (by norm_num) i
  have hbase :
      finiteMorreyDerivativeRepresentativeOn hp hpq α hαone U
          =ᵐ[domainMeasure n Ω]
        (((V : WkpAmbientOn n 1 (ENNReal.ofReal p) Ω)
          (baseIndex n 1) :
            DerivLp n (ENNReal.ofReal p) Ω) :
          ℝ^n → ℝ) := by
    simpa [V] using
      finiteMorreyDerivativeRepresentativeOn_ae
        hp hpq α hαone U
  have hderiv :
      finiteMorreyDerivativeRepresentativeOn
          hp hpq (α ++ [i]) hαi U
          =ᵐ[domainMeasure n Ω]
        (((V : WkpAmbientOn n 1 (ENNReal.ofReal p) Ω)
          (singleDerivIndex n i) :
            DerivLp n (ENNReal.ofReal p) Ω) :
          ℝ^n → ℝ) := by
    have h :=
      finiteMorreyDerivativeRepresentativeOn_ae
        hp hpq (α ++ [i]) hαi U
    rw [derivativeWordIndex_append_singleton_baseIndex
      α i hαone hαi (by norm_num), firstDerivIndex_one] at h
    simpa [V] using h
  exact
    (hasWeakDerivativeOn_congr_ae
      (n := n) (Ω := Ω) (α := [i]) hbase hderiv).mpr hraw

/-- An interior Morrey representative has the classical derivative given by
the adjacent representatives in the higher-order jet.

The order condition `|α| + 2 ≤ m` supplies one weak derivative beyond
each adjacent derivative word, so its Morrey representative is continuous. The
conclusion is local to the open domain and makes no boundary regularity
claim. -/
theorem finiteMorreyDerivativeRepresentativeOn_hasFDerivAt
    {n m : ℕ} {Ω : Set (ℝ^n)} {p q : ℝ}
    [Fact (0 < n)] [Fact (1 ≤ ENNReal.ofReal p)]
    [hΩ : Boundary.C1ExtensionAtlas n Ω]
    (hp : (n : ℝ) < p) (hpq : p.HolderConjugate q)
    (α : List (Fin n)) (hα : α.length + 2 ≤ m)
    (U : W^{m,ENNReal.ofReal p}(Ω))
    {x : ℝ^n} (hx : x ∈ Ω) :
    HasFDerivAt
      (finiteMorreyDerivativeRepresentativeOn hp hpq α (by omega) U)
      (innerSL ℝ (WithLp.toLp 2 fun i ↦
        finiteMorreyDerivativeRepresentativeOn
          hp hpq (α ++ [i]) (by simp; omega) U x)) x := by
  apply
    Approximation.hasFDerivAt_of_continuous_weakPartialDerivativesOn
      hΩ.isOpen
      (continuous_finiteMorreyDerivativeRepresentativeOn
        hp hpq α (by omega) U)
      (fun i ↦
        continuous_finiteMorreyDerivativeRepresentativeOn
          hp hpq (α ++ [i]) (by simp; omega) U)
      (fun i ↦
        finiteMorreyDerivativeRepresentativeOn_hasWeakDerivativeOn
          hp hpq α hα i U)
      hx

/-- A Morrey representative has the derivative supplied by the adjacent
representatives at every point of the domain closure. -/
theorem finiteMorreyDerivativeRepresentativeOn_hasFDerivWithinAt_closure
    {n m : ℕ} {Ω : Set (ℝ^n)} {p q : ℝ}
    [Fact (0 < n)] [Fact (1 ≤ ENNReal.ofReal p)]
    [hΩ : Boundary.C1ExtensionAtlas n Ω]
    (hp : (n : ℝ) < p) (hpq : p.HolderConjugate q)
    (α : List (Fin n)) (hα : α.length + 2 ≤ m)
    (U : W^{m,ENNReal.ofReal p}(Ω))
    {x : ℝ^n} (hx : x ∈ closure Ω) :
    HasFDerivWithinAt
      (finiteMorreyDerivativeRepresentativeOn hp hpq α (by omega) U)
      (innerSL ℝ (WithLp.toLp 2 fun i ↦
        finiteMorreyDerivativeRepresentativeOn
          hp hpq (α ++ [i]) (by simp; omega) U x))
      (closure Ω) x := by
  let f : ℝ^n → ℝ :=
    finiteMorreyDerivativeRepresentativeOn hp hpq α (by omega) U
  let f' : ℝ^n → (ℝ^n →L[ℝ] ℝ) := fun y ↦
    innerSL ℝ (WithLp.toLp 2 fun i ↦
      finiteMorreyDerivativeRepresentativeOn
        hp hpq (α ++ [i]) (by simp; omega) U y)
  apply
    Boundary.Regularity.hasFDerivWithinAt_closure_of_continuous_derivative
      (f := f) (f' := f')
      (continuous_finiteMorreyDerivativeRepresentativeOn
        hp hpq α (by omega) U)
  · have hvec : Continuous
        (fun y ↦ WithLp.toLp 2 fun i ↦
          finiteMorreyDerivativeRepresentativeOn
            hp hpq (α ++ [i]) (by simp; omega) U y) := by
      exact
        (PiLp.continuous_toLp 2 fun _ : Fin n ↦ ℝ).comp <|
          continuous_pi fun i ↦
            continuous_finiteMorreyDerivativeRepresentativeOn
              hp hpq (α ++ [i]) (by simp; omega) U
    simpa [f', Function.comp_def] using
      (innerSL ℝ).continuous.comp hvec
  · intro y hy
    exact
      finiteMorreyDerivativeRepresentativeOn_hasFDerivAt
        hp hpq α hα U hy
  · exact hx

/-- The Morrey representative of a derivative word is classically `C^k` in
the interior when `|α| + k + 1 ≤ m`.

This reconstructs the compatible interior jet directly in Mathlib's
`ContDiffOn` hierarchy. It does not assert differentiability through the
boundary. -/
theorem finiteMorreyDerivativeRepresentativeOn_contDiffOn
    {n m : ℕ} {Ω : Set (ℝ^n)} {p q : ℝ}
    [Fact (0 < n)] [Fact (1 ≤ ENNReal.ofReal p)]
    [hΩ : Boundary.C1ExtensionAtlas n Ω]
    (hp : (n : ℝ) < p) (hpq : p.HolderConjugate q)
    (k : ℕ) (α : List (Fin n))
    (hα : α.length + k + 1 ≤ m)
    (U : W^{m,ENNReal.ofReal p}(Ω)) :
    ContDiffOn ℝ k
      (finiteMorreyDerivativeRepresentativeOn hp hpq α (by omega) U) Ω := by
  induction k generalizing α with
  | zero =>
      change ContDiffOn ℝ 0 _ Ω
      rw [contDiffOn_zero]
      exact
        (continuous_finiteMorreyDerivativeRepresentativeOn
          hp hpq α (by omega) U).continuousOn
  | succ k ih =>
      let f : ℝ^n → ℝ :=
        finiteMorreyDerivativeRepresentativeOn hp hpq α (by omega) U
      let f' : ℝ^n → (ℝ^n →L[ℝ] ℝ) := fun x ↦
        innerSL ℝ (WithLp.toLp 2 fun i ↦
          finiteMorreyDerivativeRepresentativeOn
            hp hpq (α ++ [i]) (by simp; omega) U x)
      have hf' : ContDiffOn ℝ k f' Ω := by
        have hvec : ContDiffOn ℝ k
            (fun x ↦ WithLp.toLp 2 fun i ↦
              finiteMorreyDerivativeRepresentativeOn
                hp hpq (α ++ [i]) (by simp; omega) U x) Ω := by
          apply contDiffOn_piLp' 2
          intro i
          exact ih (α ++ [i]) (by simp; omega)
        simpa [f', Function.comp_def] using
          (innerSL ℝ).contDiff.comp_contDiffOn hvec
      refine
        (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
          (n := k) hΩ.isOpen.uniqueDiffOn).2 ?_
      refine ⟨by simp, f', hf', ?_⟩
      intro x hx
      exact
        (finiteMorreyDerivativeRepresentativeOn_hasFDerivAt
          hp hpq α (by omega) U hx).hasFDerivWithinAt

/-- The Morrey representative of a derivative word is classically `C^k`
within the domain closure when `|α| + k + 1 ≤ m`. -/
theorem finiteMorreyDerivativeRepresentativeOn_contDiffOn_closure
    {n m : ℕ} {Ω : Set (ℝ^n)} {p q : ℝ}
    [Fact (0 < n)] [Fact (1 ≤ ENNReal.ofReal p)]
    [Boundary.C1ExtensionAtlas n Ω]
    (hp : (n : ℝ) < p) (hpq : p.HolderConjugate q)
    (k : ℕ) (α : List (Fin n))
    (hα : α.length + k + 1 ≤ m)
    (U : W^{m,ENNReal.ofReal p}(Ω)) :
    ContDiffOn ℝ k
      (finiteMorreyDerivativeRepresentativeOn hp hpq α (by omega) U)
      (closure Ω) := by
  induction k generalizing α with
  | zero =>
      change ContDiffOn ℝ 0 _ (closure Ω)
      rw [contDiffOn_zero]
      exact
        (continuous_finiteMorreyDerivativeRepresentativeOn
          hp hpq α (by omega) U).continuousOn
  | succ k ih =>
      let f : ℝ^n → ℝ :=
        finiteMorreyDerivativeRepresentativeOn hp hpq α (by omega) U
      let f' : ℝ^n → (ℝ^n →L[ℝ] ℝ) := fun x ↦
        innerSL ℝ (WithLp.toLp 2 fun i ↦
          finiteMorreyDerivativeRepresentativeOn
            hp hpq (α ++ [i]) (by simp; omega) U x)
      have hf' : ContDiffOn ℝ k f' (closure Ω) := by
        have hvec : ContDiffOn ℝ k
            (fun x ↦ WithLp.toLp 2 fun i ↦
              finiteMorreyDerivativeRepresentativeOn
                hp hpq (α ++ [i]) (by simp; omega) U x)
            (closure Ω) := by
          apply contDiffOn_piLp' 2
          intro i
          exact ih (α ++ [i]) (by simp; omega)
        simpa [f', Function.comp_def] using
          (innerSL ℝ).contDiff.comp_contDiffOn hvec
      refine
        (contDiffOn_succ_iff_hasFDerivWithinAt
          (n := k) (by simp)).2 ?_
      intro x hx
      refine ⟨closure Ω, ?_, by simp, f', ?_, hf'⟩
      · simpa [insert_eq_of_mem hx] using
          (self_mem_nhdsWithin : closure Ω ∈ 𝓝[closure Ω] x)
      · intro y hy
        exact
          finiteMorreyDerivativeRepresentativeOn_hasFDerivWithinAt_closure
            hp hpq α (by omega) U hy

/-! ## Bundled higher-order Hölder jets -/

/-- Every weak derivative through order `k` of a `W^{k+1,p}` function,
bundled as a finite family of completed Hölder representatives. -/
noncomputable def finiteMorreyJetEmbeddingOn
    {n k : ℕ} {Ω : Set (ℝ^n)} {p q : ℝ}
    [Fact (0 < n)] [Fact (1 ≤ ENNReal.ofReal p)]
    [Boundary.C1ExtensionAtlas n Ω]
    (hp : (n : ℝ) < p) (hpq : p.HolderConjugate q) :
    W^{k + 1,ENNReal.ofReal p}(Ω) →L[ℝ]
      MorreyHolderJetOn n k Ω
        (finiteMorreyHolderExponent n p Fact.out hp) := by
  classical
  exact ContinuousLinearMap.pi fun a ↦
    finiteMorreyDerivativeEmbeddingOn hp hpq a.toList
      (Nat.add_le_add_right a.toList_length_le 1)

/-- Coordinate `a` of the Hölder jet is the derivative embedding for the word `a.toList`; the
order bound `|a| + 1 ≤ k + 1` is automatic for `a : DerivIndex n k`. -/
@[simp]
theorem finiteMorreyJetEmbeddingOn_apply
    {n k : ℕ} {Ω : Set (ℝ^n)} {p q : ℝ}
    [Fact (0 < n)] [Fact (1 ≤ ENNReal.ofReal p)]
    [Boundary.C1ExtensionAtlas n Ω]
    (hp : (n : ℝ) < p) (hpq : p.HolderConjugate q)
    (U : W^{k + 1,ENNReal.ofReal p}(Ω))
    (a : DerivIndex n k) :
    finiteMorreyJetEmbeddingOn hp hpq U a =
      finiteMorreyDerivativeEmbeddingOn hp hpq a.toList
        (Nat.add_le_add_right a.toList_length_le 1) U :=
  rfl

/-- Every coordinate of the bundled Hölder jet represents the corresponding
weak derivative almost everywhere on the domain. -/
theorem finiteMorreyJetEmbeddingOn_coordinate_ae
    {n k : ℕ} {Ω : Set (ℝ^n)} {p q : ℝ}
    [Fact (0 < n)] [Fact (1 ≤ ENNReal.ofReal p)]
    [Boundary.C1ExtensionAtlas n Ω]
    (hp : (n : ℝ) < p) (hpq : p.HolderConjugate q)
    (U : W^{k + 1,ENNReal.ofReal p}(Ω))
    (a : DerivIndex n k) :
    finiteMorreyDerivativeRepresentativeOn hp hpq a.toList
      (Nat.add_le_add_right a.toList_length_le 1) U =ᵐ[domainMeasure n Ω]
        (((U : WkpAmbientOn n (k + 1) (ENNReal.ofReal p) Ω)
          (derivativeWordIndex
            (n := n) (m := k + 1) (r := 1) a.toList
              (Nat.add_le_add_right a.toList_length_le 1) (baseIndex n 1)) :
            DerivLp n (ENNReal.ofReal p) Ω) :
          ℝ^n → ℝ) :=
  finiteMorreyDerivativeRepresentativeOn_ae hp hpq a.toList
    (Nat.add_le_add_right a.toList_length_le 1) U

end GraphSpace
end SobolevSpace
