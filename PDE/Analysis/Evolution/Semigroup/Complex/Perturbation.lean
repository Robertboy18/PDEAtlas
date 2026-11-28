/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Duhamel.Differentiability
public import PDE.Analysis.Evolution.Semigroup.Complex.Resolvent
public import PDE.Analysis.Operator.Resolvent.Perturbation

/-!
# The generator of a perturbed semigroup

Let `A` generate a semigroup `T`, let `B` be a perturbation defined on the domain of `A`, and let
`S` be a semigroup given by a Duhamel formula `S(t) x = T(t) x + ∫₀ᵗ U(t - s) f(s) ds` on the
domain of `A`, with `f` continuous and `f(0) = B x`; here `U` is `T` or `S`, depending on how the
formula is written. Then the generator of `S` contains `A + B`. If `B` is bounded relative to
`A` with a small relative bound, the generator of `S` is exactly `A + B` on the domain of `A`.
This identifies the generator of a perturbed semigroup that is already given; nothing here
constructs `S`. Under the integral condition of Miyadera, which needs no smallness of the
relative bound, `IsComplexLinear.perturbed` constructs `S`, and
`IsComplexLinear.exists_generator_eq_add_of_miyadera` identifies its generator.

## Main results

* `StronglyContinuousSemigroup.hasGeneratorAt_of_eq_orbit_add_duhamel`: for semigroups on a real
  Banach space, if `A x = y` and `S(t) x = T(t) x + ∫₀ᵗ U(t - s) f(s) ds` for `t ≥ 0` with `f`
  continuous, then the generator of `S` maps `x` to `y + f(0)`.
* `IsComplexLinear.exists_mem_resolventSet_generator_add`: if `‖T(t)‖ ≤ M e^{ωt}` and
  `‖B x‖ ≤ a ‖A x‖ + b ‖x‖` on the domain of `A` with `a (M + 1) < 1`, every large real number is
  in the resolvent set of `A + B`.
* `IsComplexLinear.generator_eq_of_le_of_mem_resolventSet`: an operator contained in a
  generator, with every large real number in its resolvent set, is the generator.
* `IsComplexLinear.add_le_generator_of_duhamel`, `generator_eq_add` and
  `generator_eq_add_of_duhamel`: from the Duhamel formula, the generator of `S` is `A + B`.

## How it works

The Duhamel integral has the derivative `f(0)` at `t = 0` (`hasDerivAt_duhamel_zero`), so the
right derivative of `S(t) x` at zero is `A x + f(0)`. For the other inclusion, the resolvent
bound `‖(z - A)⁻¹‖ ≤ M / (z - ω)` (`IsComplexLinear.norm_resolvent_generator_le`) makes
`B (z - A)⁻¹` small for large real `z` when `a (M + 1) < 1`, so `z` is in the resolvent set of
`A + B` (`LinearPMap.IsResolventAt.mem_resolventSet_add`). Large real numbers are also in the
resolvent set of the generator of `S`, and an operator with a resolvent at `z` has no proper
extension with a resolvent at `z` (`LinearPMap.IsResolventAt.eq_of_le`).
-/

@[expose] public noncomputable section

open Set

namespace PDE.Analysis.Evolution.StronglyContinuousSemigroup

/-- **The generator along Duhamel's formula.** If `A x = y` for the generator of `T` and
`S(t) x = T(t) x + ∫₀ᵗ U(t - s) f(s) ds` for `t ≥ 0`, with `f` continuous, then the generator of
`S` maps `x` to `y + f(0)`. -/
theorem hasGeneratorAt_of_eq_orbit_add_duhamel {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {S T U : StronglyContinuousSemigroup E} {x y : E}
    (hx : T.HasGeneratorAt x y) {f : ℝ → E} (hf : Continuous f)
    (h : ∀ t : ℝ, 0 ≤ t → S.realOrbit x t = T.realOrbit x t + U.duhamel f t) :
    S.HasGeneratorAt x (y + f 0) :=
  (HasDerivWithinAt.add hx (U.hasDerivAt_duhamel_zero hf).hasDerivWithinAt).congr
    (fun t ht ↦ h t ht) (h 0 le_rfl)

namespace IsComplexLinear

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  {S T : StronglyContinuousSemigroup X} (hS : S.IsComplexLinear) (hT : T.IsComplexLinear)
  {B : X →ₗ.[ℂ] X} {a b M ω : ℝ}

include hT in
/-- **Large real parameters are in the resolvent set of `A + B`.** Let `A` generate `T` with
`‖T(t)‖ ≤ M e^{ωt}`, and let `‖B x‖ ≤ a ‖A x‖ + b ‖x‖` on the domain of `A` with
`a (M + 1) < 1`. Then every real `z ≥ z₀` is in the resolvent set of `A + B`, for some `z₀`. -/
theorem exists_mem_resolventSet_generator_add (hdom : hT.generator.domain ≤ B.domain)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hB : ∀ ⦃x y w⦄, (x, y) ∈ hT.generator.graph → (x, w) ∈ B.graph →
      ‖w‖ ≤ a * ‖y‖ + b * ‖x‖)
    (hM : ∀ t : NNReal, ‖T t‖ ≤ M * Real.exp (ω * t)) (hsmall : a * (M + 1) < 1) :
    ∃ z₀ : ℝ, ∀ z : ℝ, z₀ ≤ z → (z : ℂ) ∈ (hT.generator + B).resolventSet := by
  have hM0 : 0 ≤ M := by simpa using (norm_nonneg _).trans (hM 0)
  have hθ : 0 < 1 - a * (M + 1) := sub_pos.mpr hsmall
  refine ⟨ω + ((a * |ω| + b) * M + 1) / (1 - a * (M + 1)), fun z hz ↦ ?_⟩
  have hnum : 0 < (a * |ω| + b) * M + 1 := by positivity
  have hd : 0 < z - ω := by
    have := div_pos hnum hθ
    linarith
  have hθd : (a * |ω| + b) * M + 1 ≤ (1 - a * (M + 1)) * (z - ω) := by
    have h1 : ((a * |ω| + b) * M + 1) / (1 - a * (M + 1)) ≤ z - ω := by linarith
    exact ((div_le_iff₀ hθ).mp h1).trans_eq (mul_comm _ _)
  have hzre : ω < (z : ℂ).re := by simpa using sub_pos.mp hd
  have hR := LinearPMap.isResolventAt_resolvent (hT.mem_resolventSet_generator hM hzre)
  refine hR.mem_resolventSet_add hdom ha hb hB ?_
  have hρ : ‖hT.generator.resolvent z‖ ≤ M / (z - ω) := by
    simpa using hT.norm_resolvent_generator_le hM hzre
  have hn : ‖(z : ℂ)‖ ≤ |ω| + (z - ω) := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    calc |z| = |ω + (z - ω)| := by rw [add_sub_cancel]
      _ ≤ |ω| + |z - ω| := abs_add_le _ _
      _ = |ω| + (z - ω) := by rw [abs_of_pos hd]
  have h1 : ‖(z : ℂ)‖ * ‖hT.generator.resolvent z‖ ≤ (|ω| + (z - ω)) * (M / (z - ω)) :=
    mul_le_mul hn hρ (norm_nonneg _) (by positivity)
  have h2 : (a * |ω| + b) * M / (z - ω) < 1 - a * (M + 1) := by
    rw [div_lt_iff₀ hd]
    linarith
  calc a * (‖(z : ℂ)‖ * ‖hT.generator.resolvent z‖ + 1) + b * ‖hT.generator.resolvent z‖
      ≤ a * ((|ω| + (z - ω)) * (M / (z - ω)) + 1) + b * (M / (z - ω)) := by gcongr
    _ = a * (M + 1) + (a * |ω| + b) * M / (z - ω) := by
        field_simp
        ring
    _ < 1 := by linarith

include hS in
/-- **An operator inside a generator, with large real resolvent points, is the generator.** If
the graph of `A'` is contained in the graph of the generator of `S` and every large real number
is in the resolvent set of `A'`, then `A'` is the generator of `S`: large real numbers are also
in the resolvent set of the generator, and an operator with a resolvent has no proper extension
with the same resolvent point. -/
theorem generator_eq_of_le_of_mem_resolventSet {A' : X →ₗ.[ℂ] X} (hle : A' ≤ hS.generator)
    (hres : ∃ z₀ : ℝ, ∀ z : ℝ, z₀ ≤ z → (z : ℂ) ∈ A'.resolventSet) : hS.generator = A' := by
  obtain ⟨z₀, hz₀⟩ := hres
  obtain ⟨M', ω', hM'⟩ := S.exists_norm_le_exp
  obtain ⟨R₁, hR₁⟩ := hz₀ (max z₀ (ω' + 1)) (le_max_left _ _)
  obtain ⟨R₂, hR₂⟩ := hS.mem_resolventSet_generator hM' (z := ((max z₀ (ω' + 1) : ℝ) : ℂ))
    (by simp)
  exact (hR₁.eq_of_le hR₂ hle).symm

include hS hT in
/-- **`A + B` is contained in the generator of a semigroup given by Duhamel's formula.** If for
every `x` in the domain of `A` there is a continuous `f` with `f(0) = B x` and
`S(t) x = T(t) x + ∫₀ᵗ U(t - s) f(s) ds` for `t ≥ 0`, then the generator of `S` extends `A + B`:
the Duhamel integral has the derivative `f(0)` at `t = 0`. -/
theorem add_le_generator_of_duhamel {U : StronglyContinuousSemigroup X}
    (hduh : ∀ x ∈ hT.generator.domain, ∃ f : ℝ → X, Continuous f ∧ (x, f 0) ∈ B.graph ∧
      ∀ t : ℝ, 0 ≤ t → S.realOrbit x t = T.realOrbit x t + U.duhamel f t) :
    hT.generator + B ≤ hS.generator := by
  refine LinearPMap.le_of_le_graph ?_
  rintro ⟨x, y⟩ hxy
  obtain ⟨y₁, y₂, h₁, h₂, rfl⟩ := LinearPMap.mem_graph_add_iff.mp hxy
  obtain ⟨f, hf, hf0, hduh⟩ := hduh x (LinearPMap.mem_domain_of_mem_graph h₁)
  rw [B.mem_graph_snd_inj h₂ hf0 rfl]
  exact hS.mem_graph_generator_iff.mpr
    (hasGeneratorAt_of_eq_orbit_add_duhamel (hT.mem_graph_generator_iff.mp h₁) hf hduh)

include hS hT in
/-- **The generator of a perturbed semigroup.** Let `A` generate `T` with `‖T(t)‖ ≤ M e^{ωt}`,
let `B` be bounded relative to `A` with `a (M + 1) < 1`, and let `A + B` be contained in the
generator of a semigroup `S`. Then the generator of `S` is `A + B`, on the domain of `A`: it has
no larger domain. Large real `z` are in the resolvent set of `A + B`, so
`generator_eq_of_le_of_mem_resolventSet` applies. -/
theorem generator_eq_add (hdom : hT.generator.domain ≤ B.domain) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hB : ∀ ⦃x y w⦄, (x, y) ∈ hT.generator.graph → (x, w) ∈ B.graph →
      ‖w‖ ≤ a * ‖y‖ + b * ‖x‖)
    (hM : ∀ t : NNReal, ‖T t‖ ≤ M * Real.exp (ω * t)) (hsmall : a * (M + 1) < 1)
    (hle : hT.generator + B ≤ hS.generator) : hS.generator = hT.generator + B :=
  hS.generator_eq_of_le_of_mem_resolventSet hle
    (hT.exists_mem_resolventSet_generator_add hdom ha hb hB hM hsmall)

include hS hT in
/-- **The generator of a semigroup given by Duhamel's formula.** Let `A` generate `T` with
`‖T(t)‖ ≤ M e^{ωt}` and let `B` be bounded relative to `A` with `a (M + 1) < 1`. If for every
`x` in the domain of `A` there is a continuous `f` with `f(0) = B x` and
`S(t) x = T(t) x + ∫₀ᵗ U(t - s) f(s) ds` for `t ≥ 0`, then the generator of `S` is `A + B`. The
formula is the form in which a perturbed semigroup is usually given, with `U = T` or `U = S`.
It gives `A + B ≤ generator S` (`add_le_generator_of_duhamel`), and `generator_eq_add`
applies. -/
theorem generator_eq_add_of_duhamel {U : StronglyContinuousSemigroup X}
    (hdom : hT.generator.domain ≤ B.domain) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hB : ∀ ⦃x y w⦄, (x, y) ∈ hT.generator.graph → (x, w) ∈ B.graph →
      ‖w‖ ≤ a * ‖y‖ + b * ‖x‖)
    (hM : ∀ t : NNReal, ‖T t‖ ≤ M * Real.exp (ω * t)) (hsmall : a * (M + 1) < 1)
    (hduh : ∀ x ∈ hT.generator.domain, ∃ f : ℝ → X, Continuous f ∧ (x, f 0) ∈ B.graph ∧
      ∀ t : ℝ, 0 ≤ t → S.realOrbit x t = T.realOrbit x t + U.duhamel f t) :
    hS.generator = hT.generator + B :=
  hS.generator_eq_add hT hdom ha hb hB hM hsmall (hS.add_le_generator_of_duhamel hT hduh)

end IsComplexLinear

end PDE.Analysis.Evolution.StronglyContinuousSemigroup
