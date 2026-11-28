/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Analysis.Operator.Resolvent.Spectrum

/-!
# Relatively bounded perturbations of an unbounded operator

When is `z - (A + B)` invertible on the domain of `A`, for an unbounded perturbation `B`? We
answer with the resolvent `R = (z - A)⁻¹`: if `B R` is a bounded operator of norm less than one,
then `z` is in the resolvent set of `A + B`, and this holds when `B` is bounded relative to `A`
with small enough constants. The self-similar linearization of the Navier–Stokes equations is
such a sum, a second-order operator plus a first-order perturbation on the domain of the first,
and the identification of the generator of a perturbed semigroup
(`IsComplexLinear.generator_eq_add`) uses `IsResolventAt.mem_resolventSet_add` with the
resolvent bound of a generator. Perturbations that are not relatively bounded are not treated
here; for semigroup generators, the Miyadera condition `∫₀^{t₀} ‖B T(s) x‖ ds ≤ q ‖x‖` with
`q < 1` gives the perturbed semigroup itself
(`IsComplexLinear.exists_generator_eq_add_of_miyadera`), through
`IsResolventAt.add_of_norm_lt_one`.

## Main results

* `mem_graph_add_iff`: the graph of a sum of partial operators.
* `IsResolventAt.exists_comp_of_relBound`: if `‖B x‖ ≤ a ‖A x‖ + b ‖x‖` on the domain of `A`,
  then `B R` is a bounded operator `W` with `‖W‖ ≤ a (|z| ‖R‖ + 1) + b ‖R‖`.
* `IsResolventAt.add_of_inverse`: `R V` is the resolvent of `A + B` at `z` when `V` is a
  two-sided inverse of `1 - B R`.
* `IsResolventAt.add_of_norm_lt_one`: on a Banach space, the case `‖B R‖ < 1`.
* `IsResolventAt.mem_resolventSet_add`: on a Banach space, `z` is in the resolvent set of
  `A + B` when `B` is bounded relative to `A` with `a (|z| ‖R‖ + 1) + b ‖R‖ < 1`.

## How it works

With `W = B R`, `z - A - B = (1 - W) (z - A)` on the domain of `A`, so
`(z - A - B)⁻¹ = R (1 - W)⁻¹`. A relative bound makes `W` bounded because `A R = z R - 1`. For a
bounded `B` this is the Neumann series of `LinearPMap.IsResolventAt.of_inverse` in another form.
-/

@[expose] public noncomputable section

namespace LinearPMap

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {A B : E →ₗ.[𝕜] E} {z : 𝕜} {R : E →L[𝕜] E}

/-- The graph of a sum: `(A + B) x = y` exactly when `A x = y₁`, `B x = y₂` and
`y = y₁ + y₂`. -/
theorem mem_graph_add_iff {x y : E} :
    (x, y) ∈ (A + B).graph ↔
      ∃ y₁ y₂, (x, y₁) ∈ A.graph ∧ (x, y₂) ∈ B.graph ∧ y = y₁ + y₂ := by
  constructor
  · intro h
    obtain ⟨u, rfl, rfl⟩ := (mem_graph_iff _).mp h
    exact ⟨A ⟨u, u.2.1⟩, B ⟨u, u.2.2⟩, A.mem_graph ⟨u, u.2.1⟩, B.mem_graph ⟨u, u.2.2⟩,
      add_apply A B u⟩
  · rintro ⟨y₁, y₂, h₁, h₂, rfl⟩
    have hx₁ := mem_domain_of_mem_graph h₁
    have hx₂ := mem_domain_of_mem_graph h₂
    refine (mem_graph_iff _).mpr ⟨⟨x, hx₁, hx₂⟩, rfl, ?_⟩
    rw [add_apply, (image_iff hx₁).mpr h₁, (image_iff hx₂).mpr h₂]

/-- **`B (z - A)⁻¹` is bounded when `B` is bounded relative to `A`.** If the domain of `B`
contains the domain of `A` and `‖B x‖ ≤ a ‖A x‖ + b ‖x‖` there, then `B R` is a bounded operator
`W` with `‖W‖ ≤ a (|z| ‖R‖ + 1) + b ‖R‖`. -/
theorem IsResolventAt.exists_comp_of_relBound (h : A.IsResolventAt z R)
    (hdom : A.domain ≤ B.domain) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hB : ∀ ⦃x y w⦄, (x, y) ∈ A.graph → (x, w) ∈ B.graph → ‖w‖ ≤ a * ‖y‖ + b * ‖x‖) :
    ∃ W : E →L[𝕜] E, (∀ y, (R y, W y) ∈ B.graph) ∧
      ‖W‖ ≤ a * (‖z‖ * ‖R‖ + 1) + b * ‖R‖ := by
  obtain ⟨f, hf⟩ : ∃ f : E →ₗ[𝕜] E, ∀ y, (R y, f y) ∈ B.graph :=
    ⟨B.toFun.comp (R.toLinearMap.codRestrict B.domain fun y ↦ hdom (h.mem_domain y)),
      fun y ↦ B.mem_graph ⟨R y, hdom (h.mem_domain y)⟩⟩
  have hbound : ∀ y, ‖f y‖ ≤ (a * (‖z‖ * ‖R‖ + 1) + b * ‖R‖) * ‖y‖ := fun y ↦ by
    have h2 : ‖z • R y - y‖ ≤ (‖z‖ * ‖R‖ + 1) * ‖y‖ :=
      calc ‖z • R y - y‖ ≤ ‖z • R y‖ + ‖y‖ := norm_sub_le _ _
        _ ≤ ‖z‖ * (‖R‖ * ‖y‖) + ‖y‖ := by
            rw [norm_smul]
            gcongr
            exact R.le_opNorm y
        _ = (‖z‖ * ‖R‖ + 1) * ‖y‖ := by ring
    calc ‖f y‖ ≤ a * ‖z • R y - y‖ + b * ‖R y‖ := hB (h.mem_graph y) (hf y)
      _ ≤ a * ((‖z‖ * ‖R‖ + 1) * ‖y‖) + b * (‖R‖ * ‖y‖) := by
          gcongr
          exact R.le_opNorm y
      _ = (a * (‖z‖ * ‖R‖ + 1) + b * ‖R‖) * ‖y‖ := by ring
  exact ⟨f.mkContinuous _ hbound, hf, f.mkContinuous_norm_le (by positivity) hbound⟩

/-- **The resolvent of a perturbed operator.** If `R` is the resolvent of `A` at `z`, `B R` is
a bounded operator `W`, and `V` is a two-sided inverse of `1 - W`, then `R V` is the resolvent
of `A + B` at `z`: `(z - A - B) R = 1 - W`. -/
theorem IsResolventAt.add_of_inverse (h : A.IsResolventAt z R) {W V : E →L[𝕜] E}
    (hW : ∀ y, (R y, W y) ∈ B.graph) (hV1 : (1 - W) * V = 1) (hV2 : V * (1 - W) = 1) :
    (A + B).IsResolventAt z (R * V) := by
  refine ⟨fun y ↦ ?_, fun x y hxy ↦ ?_⟩
  · have h3 : V y - W (V y) = y := DFunLike.congr_fun hV1 y
    refine mem_graph_add_iff.mpr ⟨_, _, h.mem_graph (V y), hW (V y), ?_⟩
    calc z • (R * V) y - y = z • R (V y) - (V y - W (V y)) := by rw [h3, mul_apply_eq_comp]
      _ = z • R (V y) - V y + W (V y) := by abel
  · obtain ⟨y₁, y₂, h₁, h₂, rfl⟩ := mem_graph_add_iff.mp hxy
    have hv := h.apply_eq h₁
    have hW2 : W (z • x - y₁) = y₂ := B.mem_graph_snd_inj (hW (z • x - y₁)) h₂ hv
    have h4 : V ((1 - W) (z • x - y₁)) = z • x - y₁ := DFunLike.congr_fun hV2 _
    have e : z • x - (y₁ + y₂) = (1 - W) (z • x - y₁) := by
      rw [_root_.sub_apply, one_apply_eq_self, hW2]
      abel
    rw [e, mul_apply_eq_comp, h4, hv]

/-- **The resolvent of a perturbed operator, by the Neumann series.** If `R` is the resolvent of
`A` at `z` and `B R` is a bounded operator `W` of norm less than one, then `R (1 - W)⁻¹` is the
resolvent of `A + B` at `z`. -/
theorem IsResolventAt.add_of_norm_lt_one [CompleteSpace E] (h : A.IsResolventAt z R)
    {W : E →L[𝕜] E} (hW : ∀ y, (R y, W y) ∈ B.graph) (hWn : ‖W‖ < 1) :
    ∃ V : E →L[𝕜] E, (1 - W) * V = 1 ∧ V * (1 - W) = 1 ∧ (A + B).IsResolventAt z (R * V) := by
  obtain ⟨u, hu⟩ := IsUnit.one_sub_of_norm_lt_one hWn
  have hV1 : (1 - W) * ↑u⁻¹ = 1 := by rw [← hu]; exact u.mul_inv
  have hV2 : ↑u⁻¹ * (1 - W) = 1 := by rw [← hu]; exact u.inv_mul
  exact ⟨_, hV1, hV2, h.add_of_inverse hW hV1 hV2⟩

/-- **Relatively bounded perturbations.** If `‖B x‖ ≤ a ‖A x‖ + b ‖x‖` on the domain of `A`,
`R` is the resolvent of `A` at `z`, and `a (|z| ‖R‖ + 1) + b ‖R‖ < 1`, then `z` is in the
resolvent set of `A + B`. -/
theorem IsResolventAt.mem_resolventSet_add [CompleteSpace E] (h : A.IsResolventAt z R)
    (hdom : A.domain ≤ B.domain) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hB : ∀ ⦃x y w⦄, (x, y) ∈ A.graph → (x, w) ∈ B.graph → ‖w‖ ≤ a * ‖y‖ + b * ‖x‖)
    (hsmall : a * (‖z‖ * ‖R‖ + 1) + b * ‖R‖ < 1) : z ∈ (A + B).resolventSet := by
  obtain ⟨W, hW, hWn⟩ := h.exists_comp_of_relBound hdom ha hb hB
  obtain ⟨V, -, -, hV⟩ := h.add_of_norm_lt_one hW (hWn.trans_lt hsmall)
  exact hV.mem_resolventSet

end LinearPMap
