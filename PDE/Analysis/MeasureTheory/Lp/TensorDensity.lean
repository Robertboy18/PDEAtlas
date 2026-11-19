/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!
# Dense scalar tensors in Bochner Lebesgue spaces

Dense sets of coefficient vectors and scalar Lebesgue functions give a dense
span of their pointwise products. The bilinear `compLpL₂` map transports density
in each factor, and Mathlib's simple-function induction exhausts the Bochner
space. The measure and coefficient normed space are arbitrary.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace MeasureTheory.Lp

/-- Products from dense sets of scalar Lebesgue functions and coefficient vectors
span a dense subspace of the Bochner Lebesgue space. -/
theorem dense_span_smul_tensors {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure α}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {s : Set E} {t : Set (Lp ℝ p μ)} (hs : Dense s) (ht : Dense t) :
    Dense (Submodule.span ℝ {u : Lp E p μ | ∃ c ∈ s, ∃ f ∈ t,
      ((ContinuousLinearMap.lsmul ℝ ℝ).flip c).compLp f = u} : Set (Lp E p μ)) := by
  let B : E →L[ℝ] ℝ →L[ℝ] E := (ContinuousLinearMap.lsmul ℝ ℝ).flip
  let T := B.compLpL₂ p μ
  let S := Submodule.span ℝ {u : Lp E p μ | ∃ c ∈ s, ∃ f ∈ t, T c f = u}
  let C := S.topologicalClosure
  have hC : IsClosed (C : Set (Lp E p μ)) := S.isClosed_topologicalClosure
  have hT (c : E) (f : Lp ℝ p μ) : T c f ∈ C := by
    apply hs.induction (P := fun c ↦ T c f ∈ C) ?_
      (hC.preimage ((ContinuousLinearMap.apply ℝ (Lp E p μ) f).comp T).continuous) c
    intro c hc
    apply ht.induction (P := fun f ↦ T c f ∈ C) ?_ (hC.preimage (T c).continuous) f
    intro f hf
    exact S.le_topologicalClosure (Submodule.subset_span ⟨c, hc, f, hf, rfl⟩)
  have hall (u : Lp E p μ) : u ∈ C := by
    apply Lp.induction hp (motive := fun u ↦ u ∈ C) ?_ ?_ hC u
    · intro c a ha hμa
      have he : T c (indicatorConstLp p ha hμa.ne (1 : ℝ)) =
          indicatorConstLp p ha hμa.ne c := by
        change (B c).compLp (indicatorConstLp p ha hμa.ne (1 : ℝ)) = _
        apply Lp.ext
        filter_upwards [(B c).coeFn_compLp (indicatorConstLp p ha hμa.ne (1 : ℝ)),
          (indicatorConstLp_coeFn (p := p) (hs := ha) (hμs := hμa.ne) (c := (1 : ℝ))),
          (indicatorConstLp_coeFn (p := p) (hs := ha) (hμs := hμa.ne) (c := c))]
          with x hB hf hc
        rw [hB, hf, hc]
        by_cases hx : x ∈ a <;> simp [B, hx]
      simpa only [simpleFunc.coe_indicatorConst, he] using
        hT c (indicatorConstLp p ha hμa.ne (1 : ℝ))
    · intro f g hf hg _ hfC hgC
      exact C.add_mem hfC hgC
  intro u
  exact hall u

end MeasureTheory.Lp
