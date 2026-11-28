/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Complex.DysonPhillips
public import PDE.Analysis.Evolution.Semigroup.Complex.Perturbation

/-!
# The perturbation theorem of Miyadera and Voigt

Let `A` generate a complex-linear semigroup `T` on a complex Banach space, and let `B` be
defined on the domain of `A` and bounded relative to `A`. If `∫₀^α ‖B T(s) x‖ ds ≤ q ‖x‖` on the
domain of `A` for some `α > 0` and `q < 1`, then `A + B`, on the domain of `A`, generates a
strongly continuous semigroup `S`, and

`S(t) x = T(t) x + ∫₀ᵗ S(t - s) B T(s) x ds`

for `x` in the domain of `A` and `t ≥ 0`. The integral condition holds when
`‖B T(s) x‖ ≤ c s^{-θ} ‖x‖` for small `s` and some `θ < 1`. A first-order perturbation of a
heat-type semigroup has `θ = 1/2`. By `StronglyContinuousSemigroup.eq_of_generatorPMap_eq` there
is only one semigroup with generator `A + B`. Real Banach spaces are not treated, and three
statements are not proved here: the other variation of constants formula
`S(t) x = T(t) x + ∫₀ᵗ T(t - s) B S(s) x ds`, the bound `∫₀^α ‖B S(s) x‖ ds ≤ q/(1 - q) ‖x‖`, and,
for bounded `B`, the formula for all `x` with the bound `‖S(t)‖ ≤ M e^{(ω + M ‖B‖) t}`.

## Main results

* `IsComplexLinear.exists_generator_eq_add_of_miyadera`: the theorem of Miyadera and Voigt,
  with the Duhamel formula for all `t ≥ 0`.
* `IsComplexLinear.exists_generator_eq_add_of_norm_le`: the same when `‖B T(s) x‖ ≤ φ(s) ‖x‖`
  for `0 < s ≤ s₀`, with `φ` integrable on `(0, s₀]`.
* `IsComplexLinear.exists_generator_eq_add_of_norm_le_rpow`: the case `φ(s) = c s^{-θ}`,
  `θ < 1`.
* `IsComplexLinear.exists_generator_eq_add_of_bounded`: every bounded `B`, a case in which all
  hypotheses hold.
* `IsComplexLinear.norm_comp_truncatedTransform_le` and
  `exists_mem_resolventSet_generator_add_of_isMiyadera`: under the Miyadera condition,
  `‖C ∫₀^α e^{-μs} T(s) w ds‖ ≤ q ‖R w‖` for real `μ ≥ 0`, and large real numbers are in the
  resolvent set of `A + B`.
* `IsComplexLinear.exists_isResolventAt_comp` and `exists_continuous_mem_graph_realOrbit`: the
  bounded data `R = (z₀ - A)⁻¹` and `C = B R` of a relatively bounded `B`, and continuity of
  `s ↦ B T(s) x` on the domain.

## How it works

With `R = (z₀ - A)⁻¹` and `C = B R`, the integral condition is the Miyadera condition for the
bounded data of the Dyson–Phillips construction `IsComplexLinear.perturbed`, which gives `S`
and the formula. The Duhamel integral has the derivative `B x` at `t = 0`, so `A + B` is
contained in the generator of `S` (`IsComplexLinear.add_le_generator_of_duhamel`). For a real
`μ ≥ 0` the truncated transform `F = ∫₀^α e^{-μs} T(s) ds` satisfies
`‖B F x‖ ≤ ∫₀^α ‖B T(s) x‖ ds ≤ q ‖x‖`. The resolvent of `A` at `μ` is `F (1 - E)⁻¹` with
`E = e^{-μα} T(α)`, and `‖E‖` is small for large `μ`. So `‖B (μ - A)⁻¹‖ < 1`, and `μ` is in the
resolvent set of `A + B`. Large `μ` are also in the resolvent set of the generator of `S`, and
`IsComplexLinear.generator_eq_of_le_of_mem_resolventSet` concludes. Unlike
`IsComplexLinear.generator_eq_add`, which needs a small relative bound, the relative bound here
is arbitrary. For an integrable bound `φ`, the integral of `φ` over a short interval `(0, α]` is
at most `1/2`, which is the Miyadera condition.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Graduate Texts in Mathematics 194, Springer, 2000, Chapter III, Section 3 (the perturbation
  theorem of Miyadera and Voigt). <https://doi.org/10.1007/b97696>
-/

@[expose] public noncomputable section

open Filter Topology Set MeasureTheory

namespace PDE.Analysis.Evolution.StronglyContinuousSemigroup.IsComplexLinear

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  {T : StronglyContinuousSemigroup X} (hT : T.IsComplexLinear) {B : X →ₗ.[ℂ] X}
  {C R : X →L[ℂ] X} {z₀ : ℂ} {α q : ℝ}

include hT

/-- **The Miyadera condition bounds the truncated transform.** For a real `μ ≥ 0`,
`‖C ∫₀^α e^{-μs} T(s) w ds‖ ≤ ∫₀^α ‖C T(s) w‖ ds ≤ q ‖R w‖`. -/
theorem norm_comp_truncatedTransform_le (h : T.IsMiyadera C R α q) {μ : ℝ} (hμ : 0 ≤ μ)
    (w : X) : ‖C (hT.truncatedTransform (μ : ℂ) α.toNNReal w)‖ ≤ q * ‖R w‖ := by
  have hS := hT.isComplexLinear_rescale (-(μ : ℂ))
  have hint : IntervalIntegrable ((hT.rescale (-(μ : ℂ))).realOrbit w) volume 0 α :=
    ((hT.rescale (-(μ : ℂ))).continuous_realOrbit w).intervalIntegrable _ _
  rw [truncatedTransform, hS.integral_apply, Real.coe_toNNReal α h.pos.le,
    ← C.intervalIntegral_comp_comm hint]
  refine (intervalIntegral.norm_integral_le_of_norm_le h.pos.le
    (Eventually.of_forall fun s _ ↦ ?_)
    ((C.continuous.comp (T.continuous_realOrbit w)).norm.intervalIntegrable _ _)).trans
    (h.integral_le w)
  have h1 : (hT.rescale (-(μ : ℂ))).realOrbit w s =
      Complex.exp (-(μ : ℂ) * ((s.toNNReal : ℝ) : ℂ)) • T.realOrbit w s := rfl
  have hre : (-(μ : ℂ) * ((s.toNNReal : ℝ) : ℂ)).re = -μ * (s.toNNReal : ℝ) := by simp
  rw [h1, _root_.map_smul, norm_smul, Complex.norm_exp, hre]
  refine mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr ?_)
  have := mul_nonneg hμ (s.toNNReal).coe_nonneg
  linarith

/-- **Large real parameters are in the resolvent set of `A + B`**, under the Miyadera
condition. Here `R` is a resolvent of the generator `A`, and `C = B R`. For large real `μ` the
resolvent of `A` at `μ` is `F (1 - E)⁻¹` with `F = ∫₀^α e^{-μs} T(s) ds` and `E = e^{-μα} T(α)`,
and `‖B F‖ ≤ q`, so `‖B (μ - A)⁻¹‖ < 1`. -/
theorem exists_mem_resolventSet_generator_add_of_isMiyadera
    (hR : hT.generator.IsResolventAt z₀ R) (hC : ∀ y, (R y, C y) ∈ B.graph)
    (h : T.IsMiyadera C R α q) :
    ∃ μ₀ : ℝ, ∀ μ : ℝ, μ₀ ≤ μ → (μ : ℂ) ∈ (hT.generator + B).resolventSet := by
  have hα : ((α.toNNReal : NNReal) : ℝ) = α := Real.coe_toNNReal α h.pos.le
  have hθ : 0 < (1 - q) / 2 := by linarith [h.lt_one]
  -- `e^{-μα} ‖T(α)‖` is small for large `μ`
  have hlim : Tendsto (fun μ : ℝ ↦ Real.exp (-(μ * α)) * ‖T α.toNNReal‖) atTop (𝓝 0) := by
    have h1 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.atTop_mul_const h.pos)).mul_const ‖T α.toNNReal‖
    simpa using h1
  obtain ⟨μ₁, hμ₁⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hθ))
  refine ⟨max μ₁ 0, fun μ hμ ↦ ?_⟩
  have hμ0 : 0 ≤ μ := (le_max_right _ _).trans hμ
  -- `E = e^{-μα} T(α)` and the inverse `V` of `1 - E`
  obtain ⟨E, hE⟩ : ∃ E : X →L[ℂ] X,
      E = Complex.exp (-(μ : ℂ) * ((α.toNNReal : ℝ) : ℂ)) • hT.clm α.toNNReal := ⟨_, rfl⟩
  have hEn : ‖E‖ < (1 - q) / 2 := by
    have hre : (-(μ : ℂ) * ((α.toNNReal : ℝ) : ℂ)).re = -(μ * α) := by simp [hα]
    rw [hE, norm_smul, Complex.norm_exp, hT.norm_clm, hre]
    exact hμ₁ μ ((le_max_left _ _).trans hμ)
  obtain ⟨u, hu⟩ := IsUnit.one_sub_of_norm_lt_one (hEn.trans (by linarith [h.nonneg]))
  obtain ⟨V, hV⟩ : ∃ V : X →L[ℂ] X, V = ↑u⁻¹ := ⟨_, rfl⟩
  have hV1 : (1 - E) * V = 1 := by rw [← hu, hV]; exact u.mul_inv
  have hV2 : V * (1 - E) = 1 := by rw [← hu, hV]; exact u.inv_mul
  have hVn : ‖V‖ * (1 - ‖E‖) ≤ 1 := by
    have h1 : V = 1 + E * V := by
      rw [sub_mul, one_mul] at hV1
      exact eq_add_of_sub_eq hV1
    have h2 : ‖V‖ ≤ 1 + ‖E‖ * ‖V‖ :=
      calc ‖V‖ = ‖1 + E * V‖ := congrArg norm h1
        _ ≤ ‖(1 : X →L[ℂ] X)‖ + ‖E * V‖ := norm_add_le _ _
        _ ≤ 1 + ‖E‖ * ‖V‖ := add_le_add ContinuousLinearMap.norm_id_le (norm_mul_le _ _)
    linarith
  -- the resolvent of `A` at `μ`
  obtain ⟨L, hL⟩ : ∃ L : X →L[ℂ] X, L = hT.truncatedTransform (μ : ℂ) α.toNNReal := ⟨_, rfl⟩
  have hRμ : hT.generator.IsResolventAt (μ : ℂ) (L * V) := by
    rw [hL]
    exact hT.isResolventAt_truncatedTransform_mul (by rw [← hE]; exact hV1)
      (by rw [← hE]; exact hV2)
  -- `B F` is the bounded operator `Y`, of norm at most `q`
  have hY : ‖C * ((z₀ - (μ : ℂ)) • L + (1 - E))‖ ≤ q :=
    norm_le_of_denseRange h.denseRange h.nonneg fun w ↦ by
      have h1 := hT.truncatedTransform_apply_of_mem_graph (μ : ℂ) α.toNNReal (hR.mem_graph w)
      rw [← hL] at h1
      have h3 : L ((μ : ℂ) • R w - (z₀ • R w - w)) = ((μ : ℂ) - z₀) • L (R w) + L w := by
        rw [show (μ : ℂ) • R w - (z₀ • R w - w) = ((μ : ℂ) - z₀) • R w + w by module,
          _root_.map_add, _root_.map_smul]
      have h4 : E (R w) =
          Complex.exp (-(μ : ℂ) * ((α.toNNReal : ℝ) : ℂ)) • T α.toNNReal (R w) := by
        rw [hE]
        rfl
      have h2 : (C * ((z₀ - (μ : ℂ)) • L + (1 - E))) (R w) = C (L w) := by
        simp only [mul_apply_eq_comp, _root_.add_apply, _root_.smul_apply, _root_.sub_apply,
          one_apply_eq_self]
        congr 1
        rw [h4, ← h1, h3]
        module
      rw [h2, hL]
      exact hT.norm_comp_truncatedTransform_le h hμ0 w
  -- `B (μ - A)⁻¹` is the bounded operator `W = Y V`, of norm less than one
  have hW : ∀ y, ((L * V) y, (C * ((z₀ - (μ : ℂ)) • (L * V) + 1)) y) ∈ B.graph := fun y ↦ by
    have h1 := hR.apply_eq (hRμ.mem_graph y)
    have h2 := hC (z₀ • (L * V) y - ((μ : ℂ) • (L * V) y - y))
    rw [h1] at h2
    have e : (C * ((z₀ - (μ : ℂ)) • (L * V) + 1)) y =
        C (z₀ • (L * V) y - ((μ : ℂ) • (L * V) y - y)) := by
      simp only [mul_apply_eq_comp, _root_.add_apply, _root_.smul_apply, one_apply_eq_self]
      congr 1
      module
    rwa [e]
  have hWY : C * ((z₀ - (μ : ℂ)) • (L * V) + 1) = C * ((z₀ - (μ : ℂ)) • L + (1 - E)) * V := by
    rw [mul_assoc, add_mul, smul_mul_assoc, hV1]
  have hWn : ‖C * ((z₀ - (μ : ℂ)) • (L * V) + 1)‖ < 1 := by
    rw [hWY]
    have h1 : ‖C * ((z₀ - (μ : ℂ)) • L + (1 - E)) * V‖ ≤ q * ‖V‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hY (norm_nonneg _))
    have h2 : ‖V‖ * ((1 + q) / 2) ≤ 1 :=
      (mul_le_mul_of_nonneg_left (by linarith : (1 + q) / 2 ≤ 1 - ‖E‖) (norm_nonneg V)).trans hVn
    refine h1.trans_lt ?_
    rcases le_or_gt ‖V‖ 1 with hv | hv
    · exact (mul_le_mul_of_nonneg_left hv h.nonneg).trans_lt (by linarith [h.lt_one])
    · have h3 : ‖V‖ * ((1 + q) / 2) = (‖V‖ + q * ‖V‖) / 2 := by ring
      linarith
  obtain ⟨V', -, -, hres⟩ := hRμ.add_of_norm_lt_one hW hWn
  exact hres.mem_resolventSet

/-- **Bounded data for a relatively bounded perturbation.** If `B` is defined on the domain of
the generator `A` and bounded relative to `A`, there are a resolvent `R = (z₀ - A)⁻¹` of `A` and
the bounded operator `C = B R`. The range of `R` is the domain of `A`, so it is dense, `R`
commutes with the semigroup, and `B T(s) R w = C T(s) w` for all `w` and `s`. -/
theorem exists_isResolventAt_comp {a b : ℝ} (hdom : hT.generator.domain ≤ B.domain)
    (hB : ∀ ⦃x y w⦄, (x, y) ∈ hT.generator.graph → (x, w) ∈ B.graph →
      ‖w‖ ≤ a * ‖y‖ + b * ‖x‖) :
    ∃ (z₀ : ℂ) (R C : X →L[ℂ] X), hT.generator.IsResolventAt z₀ R ∧
      (∀ y, (R y, C y) ∈ B.graph) ∧ DenseRange R ∧
      (∀ (t : NNReal) (w : X), R (T t w) = T t (R w)) ∧
      ∀ (w : X) (s : ℝ), (T.realOrbit (R w) s, C (T.realOrbit w s)) ∈ B.graph := by
  obtain ⟨z₀, R, hR⟩ := hT.resolventSet_generator_nonempty
  obtain ⟨C, hC, -⟩ := hR.exists_comp_of_relBound hdom (abs_nonneg a) (abs_nonneg b)
    fun x y w hxy hxw ↦ (hB hxy hxw).trans (add_le_add
      (mul_le_mul_of_nonneg_right (le_abs_self a) (norm_nonneg _))
      (mul_le_mul_of_nonneg_right (le_abs_self b) (norm_nonneg _)))
  have hRT : ∀ (t : NNReal) (w : X), R (T t w) = T t (R w) := fun t w ↦
    (DFunLike.congr_fun (hR.commute_of_map_mem_graph (S := hT.clm t)
      fun _ _ hxy ↦ hT.map_mem_graph t hxy).eq w).symm
  have hdense : DenseRange R := by
    have hrange : Set.range R = (hT.generator.domain : Set X) := by
      ext x
      exact ⟨fun ⟨y, hy⟩ ↦ hy ▸ hR.mem_domain y, fun hx ↦ ⟨_, hR.resolvent_apply ⟨x, hx⟩⟩⟩
    rw [DenseRange, hrange]
    exact hT.dense_domain_generator
  refine ⟨z₀, R, C, hR, hC, hdense, hRT, fun w s ↦ ?_⟩
  have h1 := hC (T.realOrbit w s)
  rwa [show R (T.realOrbit w s) = T.realOrbit (R w) s from hRT _ _] at h1

/-- **`s ↦ B T(s) x` is continuous** for `x` in the domain of the generator `A`, when `B` is
bounded relative to `A`: there is a continuous `g` with `g(s) = B T(s) x` for every `s`. So the
integrals in the theorem of Miyadera and Voigt are integrals of continuous functions. -/
theorem exists_continuous_mem_graph_realOrbit {a b : ℝ}
    (hdom : hT.generator.domain ≤ B.domain)
    (hB : ∀ ⦃x y w⦄, (x, y) ∈ hT.generator.graph → (x, w) ∈ B.graph →
      ‖w‖ ≤ a * ‖y‖ + b * ‖x‖) {x : X} (hx : x ∈ hT.generator.domain) :
    ∃ g : ℝ → X, Continuous g ∧ ∀ s : ℝ, (T.realOrbit x s, g s) ∈ B.graph := by
  obtain ⟨z₀, R, C, hR, -, -, -, hgraph⟩ := hT.exists_isResolventAt_comp hdom hB
  obtain ⟨w, rfl⟩ : ∃ w, R w = x := ⟨_, hR.resolvent_apply ⟨x, hx⟩⟩
  exact ⟨fun s ↦ C (T.realOrbit w s), C.continuous.comp (T.continuous_realOrbit w), hgraph w⟩

/-- **The perturbation theorem of Miyadera and Voigt.** Let `A` generate the semigroup `T`, and
let `B` be defined on the domain of `A` and bounded relative to `A`,
`‖B x‖ ≤ a ‖A x‖ + b ‖x‖`. If `∫₀^α ‖B T(s) x‖ ds ≤ q ‖x‖` for all `x` in the domain of `A`, with
`α > 0` and `q < 1`, then `A + B`, on the domain of `A`, generates a strongly continuous
semigroup `S`, and for every `x` in the domain of `A` and all `t ≥ 0`

`S(t) x = T(t) x + ∫₀ᵗ S(t - s) B T(s) x ds`.

Both integrals are stated with any function `g` such that `g(s) = B T(s) x` on the interval of
integration. There is exactly one such function there, and it is continuous
(`exists_continuous_mem_graph_realOrbit`); this is where the relative bound is used in the
statement, and the proof uses it to make `B (z₀ - A)⁻¹` a bounded operator.

A bound `‖B T(s) x‖ ≤ c s^{-1/2} ‖x‖` for small `s` gives the integral condition for small `α`
(`exists_generator_eq_add_of_norm_le_rpow`). The semigroup is the Dyson–Phillips series
(`IsComplexLinear.perturbed`), and its generator is `A + B` because both operators have large
real numbers in their resolvent sets. The formula is the one in which the perturbation acts
after `T`; the formula `S(t) x = T(t) x + ∫₀ᵗ T(t - s) B S(s) x ds` is not proved here. -/
theorem exists_generator_eq_add_of_miyadera {a b : ℝ}
    (hdom : hT.generator.domain ≤ B.domain)
    (hB : ∀ ⦃x y w⦄, (x, y) ∈ hT.generator.graph → (x, w) ∈ B.graph →
      ‖w‖ ≤ a * ‖y‖ + b * ‖x‖)
    (hα : 0 < α) (hq : q < 1)
    (hMi : ∀ x ∈ hT.generator.domain, ∀ g : ℝ → X,
      (∀ s ∈ Icc (0 : ℝ) α, (T.realOrbit x s, g s) ∈ B.graph) →
        ∫ s in (0 : ℝ)..α, ‖g s‖ ≤ q * ‖x‖) :
    ∃ (S : StronglyContinuousSemigroup X) (hS : S.IsComplexLinear),
      hS.generator = hT.generator + B ∧
      ∀ x ∈ hT.generator.domain, ∀ t : ℝ, 0 ≤ t → ∀ g : ℝ → X,
        (∀ s ∈ Icc (0 : ℝ) t, (T.realOrbit x s, g s) ∈ B.graph) →
          S.realOrbit x t = T.realOrbit x t + S.duhamel g t := by
  -- bounded data: a resolvent `R` of `A` and `C = B R`
  obtain ⟨z₀, R, C, hR, hC, hdense, hRT, hgraph⟩ := hT.exists_isResolventAt_comp hdom hB
  have hmi : T.IsMiyadera C R α (max q 0) :=
    ⟨hα, le_max_right _ _, max_lt hq one_pos, hdense, hRT, fun w ↦
      (hMi (R w) (hR.mem_domain w) (fun s ↦ C (T.realOrbit w s)) fun s _ ↦ hgraph w s).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))⟩
  have hS := hT.isComplexLinear_perturbed hmi
  refine ⟨hT.perturbed hmi, hS, hS.generator_eq_of_le_of_mem_resolventSet
    (hS.add_le_generator_of_duhamel hT (U := hT.perturbed hmi) fun x hx ↦ ?_)
    (hT.exists_mem_resolventSet_generator_add_of_isMiyadera hR hC hmi), fun x hx t ht g hg ↦ ?_⟩
  · -- `A + B` is contained in the generator of `S`: the formula with a continuous `f`
    obtain ⟨w, rfl⟩ : ∃ w, R w = x := ⟨_, hR.resolvent_apply ⟨x, hx⟩⟩
    have h0 := hgraph w 0
    rw [T.realOrbit_zero (R w)] at h0
    exact ⟨fun s ↦ C (T.realOrbit w s), C.continuous.comp (T.continuous_realOrbit w), h0,
      fun t ht ↦ hT.perturbed_duhamel hmi ht w⟩
  · -- the Duhamel formula on the domain of `A`
    obtain ⟨w, rfl⟩ : ∃ w, R w = x := ⟨_, hR.resolvent_apply ⟨x, hx⟩⟩
    rw [hT.perturbed_duhamel hmi ht w]
    congr 1
    exact duhamel_congr _ ht fun s hs ↦ B.mem_graph_snd_inj (hgraph w s) (hg s hs) rfl

/-- **Perturbations with an integrable bound.** Let `A` generate `T`, and let `B` be defined on
the domain of `A` and bounded relative to `A`. If `‖B T(s) x‖ ≤ φ(s) ‖x‖` for `x` in the domain
of `A` and `0 < s ≤ s₀`, with `φ` integrable on `(0, s₀]`, then `A + B` generates a strongly
continuous semigroup `S` with `S(t) x = T(t) x + ∫₀ᵗ S(t - s) B T(s) x ds` on the domain of `A`.
The integral of `φ` over a short interval `(0, α]` is at most `1/2`, which is the Miyadera
condition. -/
theorem exists_generator_eq_add_of_norm_le {a b s₀ : ℝ} {φ : ℝ → ℝ}
    (hdom : hT.generator.domain ≤ B.domain)
    (hB : ∀ ⦃x y w⦄, (x, y) ∈ hT.generator.graph → (x, w) ∈ B.graph →
      ‖w‖ ≤ a * ‖y‖ + b * ‖x‖)
    (hs₀ : 0 < s₀) (hφ : IntervalIntegrable φ volume 0 s₀)
    (hsm : ∀ x ∈ hT.generator.domain, ∀ (s : ℝ) (y : X), 0 < s → s ≤ s₀ →
      (T.realOrbit x s, y) ∈ B.graph → ‖y‖ ≤ φ s * ‖x‖) :
    ∃ (S : StronglyContinuousSemigroup X) (hS : S.IsComplexLinear),
      hS.generator = hT.generator + B ∧
      ∀ x ∈ hT.generator.domain, ∀ t : ℝ, 0 ≤ t → ∀ g : ℝ → X,
        (∀ s ∈ Icc (0 : ℝ) t, (T.realOrbit x s, g s) ∈ B.graph) →
          S.realOrbit x t = T.realOrbit x t + S.duhamel g t := by
  -- a short interval on which the integral of `φ` is at most `1/2`
  obtain ⟨α, hα, hαs, hαφ⟩ : ∃ α : ℝ, 0 < α ∧ α ≤ s₀ ∧ ∫ s in (0 : ℝ)..α, φ s ≤ 1 / 2 := by
    have hcont : ContinuousOn (fun c ↦ ∫ s in (0 : ℝ)..c, φ s) (uIcc 0 s₀) :=
      intervalIntegral.continuousOn_primitive_interval
        (by rw [uIcc_of_le hs₀.le]; exact (intervalIntegrable_iff_integrableOn_Icc_of_le
          hs₀.le).mp hφ)
    rw [uIcc_of_le hs₀.le] at hcont
    obtain ⟨δ, hδ, h⟩ := Metric.continuousWithinAt_iff.mp (hcont 0 ⟨le_rfl, hs₀.le⟩) (1 / 2)
      (by norm_num)
    refine ⟨min (δ / 2) s₀, lt_min (half_pos hδ) hs₀, min_le_right _ _, ?_⟩
    have h1 := h (x := min (δ / 2) s₀) ⟨(lt_min (half_pos hδ) hs₀).le, min_le_right _ _⟩ (by
      rw [Real.dist_eq, sub_zero, abs_of_pos (lt_min (half_pos hδ) hs₀)]
      exact (min_le_left _ _).trans_lt (half_lt_self hδ))
    rw [intervalIntegral.integral_same, Real.dist_eq, sub_zero] at h1
    exact (abs_lt.mp h1).2.le
  refine hT.exists_generator_eq_add_of_miyadera hdom hB hα (by norm_num : (1 / 2 : ℝ) < 1)
    fun x hx g hg ↦ ?_
  have hφα : IntervalIntegrable φ volume 0 α :=
    hφ.mono_set (by rw [uIcc_of_le hα.le, uIcc_of_le hs₀.le]; exact Icc_subset_Icc_right hαs)
  calc ∫ s in (0 : ℝ)..α, ‖g s‖ ≤ ∫ s in (0 : ℝ)..α, φ s * ‖x‖ := by
        rw [intervalIntegral.integral_of_le hα.le, intervalIntegral.integral_of_le hα.le]
        refine integral_mono_of_nonneg (Eventually.of_forall fun s ↦ norm_nonneg _)
          (hφα.mul_const _).1 ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        exact hsm x hx s (g s) hs.1 (hs.2.trans hαs) (hg s ⟨hs.1.le, hs.2⟩)
    _ = (∫ s in (0 : ℝ)..α, φ s) * ‖x‖ := intervalIntegral.integral_mul_const _ _
    _ ≤ 1 / 2 * ‖x‖ := by gcongr

/-- **Perturbations with a power bound.** If `‖B T(s) x‖ ≤ c s^{-θ} ‖x‖` for `x` in the domain
of `A` and `0 < s ≤ s₀`, with `θ < 1`, then `A + B` generates a strongly continuous semigroup `S`
with `S(t) x = T(t) x + ∫₀ᵗ S(t - s) B T(s) x ds` on the domain of `A`. A first-order
perturbation of a heat-type semigroup has `θ = 1/2`. The power `s^{-θ}` is integrable at `0`. -/
theorem exists_generator_eq_add_of_norm_le_rpow {a b c θ s₀ : ℝ}
    (hdom : hT.generator.domain ≤ B.domain)
    (hB : ∀ ⦃x y w⦄, (x, y) ∈ hT.generator.graph → (x, w) ∈ B.graph →
      ‖w‖ ≤ a * ‖y‖ + b * ‖x‖)
    (hθ : θ < 1) (hs₀ : 0 < s₀)
    (hsm : ∀ x ∈ hT.generator.domain, ∀ (s : ℝ) (y : X), 0 < s → s ≤ s₀ →
      (T.realOrbit x s, y) ∈ B.graph → ‖y‖ ≤ c * s ^ (-θ) * ‖x‖) :
    ∃ (S : StronglyContinuousSemigroup X) (hS : S.IsComplexLinear),
      hS.generator = hT.generator + B ∧
      ∀ x ∈ hT.generator.domain, ∀ t : ℝ, 0 ≤ t → ∀ g : ℝ → X,
        (∀ s ∈ Icc (0 : ℝ) t, (T.realOrbit x s, g s) ∈ B.graph) →
          S.realOrbit x t = T.realOrbit x t + S.duhamel g t :=
  hT.exists_generator_eq_add_of_norm_le hdom hB hs₀
    ((intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul c) hsm

/-- **Bounded perturbations.** For a bounded operator `B`, `A + B` generates a strongly
continuous semigroup `S`, and `S(t) x = T(t) x + ∫₀ᵗ S(t - s) B T(s) x ds` for `x` in the domain
of `A`. This is the case of the theorem of Miyadera and Voigt in which every hypothesis holds:
`‖B T(s) x‖ ≤ ‖B‖ M ‖x‖` for `0 ≤ s ≤ 1`. The formula for all `x` and the bound of `‖S(t)‖`,
which the bounded perturbation theorem also has, are not stated. -/
theorem exists_generator_eq_add_of_bounded (B : X →L[ℂ] X) :
    ∃ (S : StronglyContinuousSemigroup X) (hS : S.IsComplexLinear),
      hS.generator = hT.generator + B.toLinearMap.toPMap ⊤ ∧
      ∀ x ∈ hT.generator.domain, ∀ t : ℝ, 0 ≤ t →
        S.realOrbit x t = T.realOrbit x t + S.duhamel (fun s ↦ B (T.realOrbit x s)) t := by
  obtain ⟨M, -, hM⟩ := T.exists_norm_le_on_Icc 1
  obtain ⟨S, hS, hgen, hduh⟩ := hT.exists_generator_eq_add_of_norm_le
    (B := B.toLinearMap.toPMap ⊤) (a := 0) (b := ‖B‖) (φ := fun _ ↦ ‖B‖ * M) (s₀ := 1)
    (fun _ _ ↦ Submodule.mem_top)
    (fun x y w _ hw ↦ by
      rw [← LinearPMap.mem_graph_toPMap_top.mp hw, zero_mul, zero_add]
      exact B.le_opNorm x)
    one_pos intervalIntegrable_const
    (fun x _ s y _ hs1 hy ↦ by
      rw [← LinearPMap.mem_graph_toPMap_top.mp hy]
      have h1 : ‖T.realOrbit x s‖ ≤ M * ‖x‖ :=
        (T s.toNNReal).le_of_opNorm_le (hM _ ⟨zero_le, Real.toNNReal_le_one.mpr hs1⟩) x
      calc ‖B (T.realOrbit x s)‖ ≤ ‖B‖ * ‖T.realOrbit x s‖ := B.le_opNorm _
        _ ≤ ‖B‖ * (M * ‖x‖) := by gcongr
        _ = ‖B‖ * M * ‖x‖ := by ring)
  exact ⟨S, hS, hgen, fun x hx t ht ↦ hduh x hx t ht _
    fun s _ ↦ LinearPMap.mem_graph_toPMap_top.mpr rfl⟩

end PDE.Analysis.Evolution.StronglyContinuousSemigroup.IsComplexLinear
