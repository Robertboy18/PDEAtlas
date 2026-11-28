/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import PDE.Analysis.Evolution.Semigroup.Complex.Generator
public import PDE.Analysis.Evolution.Semigroup.GrowthBound
public import PDE.Analysis.Operator.Resolvent.Spectrum

/-!
# The resolvent of a semigroup generator at complex parameters

Let `A` generate a complex-linear semigroup `T` on a complex Banach space with
`‖T(t)‖ ≤ M e^{ωt}`. Every `z` with `Re z > ω` is in the resolvent set of `A`, and
`‖(z - A)⁻¹‖ ≤ M / (Re z - ω)`. The same holds relative to a bounded operator `P` that commutes
with the semigroup and along which it decays, `‖T(t) P‖ ≤ M e^{ωt}`. That is the form a spectral
decomposition needs: on a stable part the generator has no spectrum to the right of the decay
rate. Two consequences are proved here: the spectral bound is at most the growth bound,
`s(A) ≤ ω₀(T)`, and the spectral inclusion theorem `e^{t σ(A)} ⊆ σ(T(t))`. For contraction
semigroups on real spaces and real `λ > 0`, the real library has
`StronglyContinuousSemigroup.mem_realResolventSet_generatorPMap`. The resolvent is obtained as
a limit of truncated transforms along the integers; its form as an improper integral over
`(0, ∞)` is not stated.

## Main results

* `IsComplexLinear.truncatedTransform`: `F_t x = ∫₀ᵗ e^{-zs} T(s) x ds`, with
  `(z - A) F_t u = u - e^{-zt} T(t) u` (`truncatedTransform_mem_graph`) and
  `F_t (z - A) x = x - e^{-zt} T(t) x` on the domain (`truncatedTransform_apply_of_mem_graph`).
  At real parameters it is the real library's `truncatedLaplaceTransform`
  (`truncatedTransform_ofReal`).
* `IsComplexLinear.exists_isResolventAtOn`: if `P` commutes with the semigroup,
  `‖T(t) P‖ ≤ M e^{ωt}` and `Re z > ω`, then `F_n P` converges in operator norm to an inverse of
  `z - A` relative to `P` (`LinearPMap.IsResolventAtOn`).
* `IsComplexLinear.mem_resolventSet_generator` and `norm_resolvent_generator_le`: if
  `‖T(t)‖ ≤ M e^{ωt}`, the half-plane `Re z > ω` is in the resolvent set and
  `‖(z - A)⁻¹‖ ≤ M / (Re z - ω)`. In particular the resolvent set is not empty
  (`resolventSet_generator_nonempty`).
* `IsComplexLinear.spectralBound_generator_le_growthBound`: `s(A) ≤ ω₀(T)`.
* `IsComplexLinear.isResolventAt_truncatedTransform_mul`: if `1 - e^{-zt} T(t)` has a two-sided
  inverse `V`, then `F_t V` is the resolvent of `A` at `z`.
* `IsComplexLinear.exp_mem_spectrum_of_mem_spectrum_generator`: the spectral inclusion theorem.

## How it works

The truncated transforms are the time integrals of the rescaled semigroup `e^{-zt} T(t)`,
whose generator is `A - z` (`IsComplexLinear.hasGeneratorAt_rescale_iff`), so the two identities
for `F_t` are the identities of a time integral. On the range of `P` the boundary term
`e^{-zt} T(t) P u` decays like `e^{-(Re z - ω) t}`, and
`‖(F_{n+1} - F_n) P‖ ≤ M e^{-(Re z - ω) n}`, so `F_n P` is a Cauchy sequence. The generator is
closed, so both identities pass to the limit. For the spectral inclusion, if `e^{zt} - T(t)` is
invertible, so is `1 - e^{-zt} T(t)`, and its inverse commutes with `A` because it commutes with
a resolvent of `A`.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Graduate Texts in Mathematics 194, Springer, 2000, Chapter II, Section 1 (the resolvent of a
  generator and the bound `M / (Re λ - ω)`), and Chapter IV, Section 3 (the spectral inclusion
  theorem). <https://doi.org/10.1007/b97696>
-/

@[expose] public noncomputable section

open Filter Topology Set
open scoped Interval

namespace PDE.Analysis.Evolution.StronglyContinuousSemigroup.IsComplexLinear

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  {T : StronglyContinuousSemigroup X} (hT : T.IsComplexLinear) {x y : X} {z : ℂ}

include hT

/-- The truncated transform `F_t x = ∫₀ᵗ e^{-zs} T(s) x ds` as a complex-linear bounded
operator: the time integral of the rescaled semigroup `e^{-zt} T(t)`. -/
def truncatedTransform (z : ℂ) (t : NNReal) : X →L[ℂ] X :=
  (hT.isComplexLinear_rescale (-z)).integral t

/-- At a real parameter the truncated transform is the truncated Laplace transform of the real
library. -/
theorem truncatedTransform_ofReal (ω : ℝ) (t : NNReal) (x : X) :
    hT.truncatedTransform (ω : ℂ) t x = T.truncatedLaplaceTransform ω t x := by
  rw [truncatedTransform, integral_apply, truncatedLaplaceTransform_apply]
  refine intervalIntegral.integral_congr fun s hs ↦ ?_
  rw [uIcc_of_le t.coe_nonneg] at hs
  simp only [realOrbit, rescale_apply, _root_.smul_apply, Real.coe_toNNReal s hs.1]
  rw [← Complex.ofReal_neg, ← Complex.ofReal_mul, ← Complex.ofReal_exp, Complex.coe_smul]

/-- `(z - A) F_t u = u - e^{-zt} T(t) u`: the truncated transform maps into the domain. -/
theorem truncatedTransform_mem_graph (z : ℂ) (t : NNReal) (u : X) :
    (hT.truncatedTransform z t u,
      z • hT.truncatedTransform z t u + Complex.exp (-z * ((t : ℝ) : ℂ)) • T t u - u) ∈
      hT.generator.graph := by
  have h := (hT.isComplexLinear_rescale (-z)).integral_mem_graph t u
  rw [mem_graph_generator_iff, hasGeneratorAt_rescale_iff] at h
  have e : z • hT.truncatedTransform z t u + Complex.exp (-z * ((t : ℝ) : ℂ)) • T t u - u =
      hT.rescale (-z) t u - u - -z • (hT.isComplexLinear_rescale (-z)).integral t u := by
    rw [rescale_apply, smul_apply, truncatedTransform]
    module
  rw [mem_graph_generator_iff, e]
  exact h

/-- `F_t (z - A) x = x - e^{-zt} T(t) x` for `x` in the domain. -/
theorem truncatedTransform_apply_of_mem_graph (z : ℂ) (t : NNReal)
    (h : (x, y) ∈ hT.generator.graph) :
    hT.truncatedTransform z t (z • x - y) = x - Complex.exp (-z * ((t : ℝ) : ℂ)) • T t x := by
  have hS : (x, y - z • x) ∈ (hT.isComplexLinear_rescale (-z)).generator.graph := by
    rw [mem_graph_generator_iff, hasGeneratorAt_rescale_iff, ← mem_graph_generator_iff hT]
    convert h using 2
    module
  have h1 := (hT.isComplexLinear_rescale (-z)).integral_apply_of_mem_graph t hS
  rw [show z • x - y = -(y - z • x) by abel, _root_.map_neg, truncatedTransform, h1]
  simp only [rescale_apply, smul_apply]
  abel

omit [CompleteSpace X] in
/-- On a part where `‖T(t) P‖ ≤ M e^{ωt}`, the rescaled orbits decay:
`‖e^{-zs} T(s) P u‖ ≤ M e^{-(Re z - ω) s} ‖u‖`. -/
theorem norm_rescale_neg_apply_le {P : X →L[ℂ] X} {M ω : ℝ}
    (hM : ∀ t : NNReal, ‖hT.clm t * P‖ ≤ M * Real.exp (ω * t)) (z : ℂ) (s : NNReal) (u : X) :
    ‖hT.rescale (-z) s (P u)‖ ≤ M * Real.exp (-(z.re - ω) * s) * ‖u‖ := by
  have h1 : ‖T s (P u)‖ ≤ M * Real.exp (ω * s) * ‖u‖ :=
    (hT.clm s * P).le_of_opNorm_le (hM s) u
  rw [rescale_apply, smul_apply, norm_smul, Complex.norm_exp]
  have hre : (-z * ((s : ℝ) : ℂ)).re = -z.re * s := by simp
  rw [hre]
  calc Real.exp (-z.re * s) * ‖T s (P u)‖
      ≤ Real.exp (-z.re * s) * (M * Real.exp (ω * s) * ‖u‖) := by gcongr
    _ = M * Real.exp (-(z.re - ω) * s) * ‖u‖ := by
        rw [show -(z.re - ω) * (s : ℝ) = -z.re * s + ω * s by ring, Real.exp_add]
        ring

/-- **The bound of the truncated transforms**: if `‖T(t) P‖ ≤ M e^{ωt}` and `Re z > ω`,
then `‖∫₀ᵗ e^{-zs} T(s) P ds‖ ≤ M / (Re z - ω)` for every `t`. -/
theorem norm_truncatedTransform_mul_le {P : X →L[ℂ] X} {M ω : ℝ}
    (hM : ∀ t : NNReal, ‖hT.clm t * P‖ ≤ M * Real.exp (ω * t)) (hz : ω < z.re) (t : NNReal) :
    ‖hT.truncatedTransform z t * P‖ ≤ M / (z.re - ω) := by
  have hM0 : 0 ≤ M := by simpa using (norm_nonneg _).trans (hM 0)
  have hε : 0 < z.re - ω := sub_pos.mpr hz
  refine ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hM0 hε.le) fun u ↦ ?_
  have hS := hT.isComplexLinear_rescale (-z)
  have hg : IntervalIntegrable (fun s : ℝ ↦ M * Real.exp (-(z.re - ω) * s) * ‖u‖)
      MeasureTheory.volume 0 t :=
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  have h1 : ‖(hT.truncatedTransform z t * P) u‖ ≤
      ∫ s in (0 : ℝ)..t, M * Real.exp (-(z.re - ω) * s) * ‖u‖ := by
    rw [mul_apply_eq_comp, truncatedTransform, hS.integral_apply]
    refine intervalIntegral.norm_integral_le_of_norm_le t.coe_nonneg
      (Eventually.of_forall fun s hs ↦ ?_) hg
    have h2 := hT.norm_rescale_neg_apply_le hM z s.toNNReal u
    rwa [Real.coe_toNNReal s hs.1.le] at h2
  have h3 : ∫ s in (0 : ℝ)..t, Real.exp (-(z.re - ω) * s) ≤ 1 / (z.re - ω) := by
    rw [intervalIntegral.integral_comp_mul_left (f := Real.exp) (neg_ne_zero.mpr hε.ne'),
      integral_exp, mul_zero, Real.exp_zero, smul_eq_mul, inv_neg, neg_mul, ← mul_neg, neg_sub,
      ← div_eq_inv_mul]
    exact div_le_div_of_nonneg_right (sub_le_self _ (Real.exp_nonneg _)) hε.le
  calc ‖(hT.truncatedTransform z t * P) u‖
      ≤ ∫ s in (0 : ℝ)..t, M * Real.exp (-(z.re - ω) * s) * ‖u‖ := h1
    _ = M * (∫ s in (0 : ℝ)..t, Real.exp (-(z.re - ω) * s)) * ‖u‖ := by
        rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul]
    _ ≤ M * (1 / (z.re - ω)) * ‖u‖ := by gcongr
    _ = M / (z.re - ω) * ‖u‖ := by ring

/-- **The resolvent relative to a decaying part.** Let `P` commute with the semigroup, with
`‖T(t) P‖ ≤ M e^{ωt}`, and let `Re z > ω`. The operators `F_n P`, `F_n x = ∫₀ⁿ e^{-zs} T(s) x ds`,
converge in operator norm to an `L` with `(z - A) L = P` and `L (z - A) = P` on the domain. -/
theorem exists_isResolventAtOn {P : X →L[ℂ] X} (hPT : ∀ t, Commute P (hT.clm t)) {M ω : ℝ}
    (hM : ∀ t : NNReal, ‖hT.clm t * P‖ ≤ M * Real.exp (ω * t)) (hz : ω < z.re) :
    ∃ L : X →L[ℂ] X, hT.generator.IsResolventAtOn z P L ∧
      Tendsto (fun n : ℕ ↦ hT.truncatedTransform z n * P) atTop (𝓝 L) := by
  have hM0 : 0 ≤ M := by simpa using (norm_nonneg _).trans (hM 0)
  have hε : 0 < z.re - ω := sub_pos.mpr hz
  have hS := hT.isComplexLinear_rescale (-z)
  have hdecay := hT.norm_rescale_neg_apply_le hM z
  set G : ℕ → X →L[ℂ] X := fun n ↦ hT.truncatedTransform z n * P with hG
  -- consecutive truncations differ by a geometric amount
  have hstep (n : ℕ) : dist (G n) (G (n + 1)) ≤ M * Real.exp (-(z.re - ω)) ^ n := by
    rw [dist_comm, dist_eq_norm]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u ↦ ?_
    have hint (a b : ℝ) : IntervalIntegrable ((hT.rescale (-z)).realOrbit (P u))
        MeasureTheory.volume a b :=
      ((hT.rescale (-z)).continuous_realOrbit (P u)).intervalIntegrable a b
    have hsub : (G (n + 1) - G n) u =
        ∫ s in (n : ℝ)..((n + 1 : ℕ) : ℝ), (hT.rescale (-z)).realOrbit (P u) s := by
      simp only [hG, _root_.sub_apply, mul_apply_eq_comp, truncatedTransform, hS.integral_apply,
        NNReal.coe_natCast]
      exact intervalIntegral.integral_interval_sub_left (hint _ _) (hint _ _)
    rw [hsub]
    have hb : ∀ s ∈ Ι (n : ℝ) ((n + 1 : ℕ) : ℝ), ‖(hT.rescale (-z)).realOrbit (P u) s‖ ≤
        M * Real.exp (-(z.re - ω)) ^ n * ‖u‖ := by
      intro s hs
      rw [uIoc_of_le (by exact_mod_cast Nat.le_succ n)] at hs
      have hs0 : 0 ≤ s := (Nat.cast_nonneg n).trans hs.1.le
      have hexp : Real.exp (-(z.re - ω) * s) ≤ Real.exp (-(z.re - ω)) ^ n := by
        rw [← Real.exp_nat_mul]
        have := mul_le_mul_of_nonneg_left hs.1.le hε.le
        exact Real.exp_le_exp.mpr (by linarith)
      refine (hdecay s.toNNReal u).trans ?_
      rw [Real.coe_toNNReal s hs0]
      gcongr
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
    have h1 : |((n + 1 : ℕ) : ℝ) - (n : ℝ)| = 1 := by
      rw [Nat.cast_succ, add_sub_cancel_left, abs_one]
    rwa [h1, mul_one] at h
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_le_geometric _ M (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hε)) hstep)
  have hLy (u : X) : Tendsto (fun n ↦ G n u) atTop (𝓝 (L u)) :=
    ((ContinuousLinearMap.apply ℂ X u).continuous.tendsto L).comp hL
  -- the boundary term decays
  have hzero (u : X) : Tendsto (fun n : ℕ ↦ Complex.exp (-z * (((n : NNReal) : ℝ) : ℂ)) •
      T (n : NNReal) (P u)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun n : ℕ ↦ M * Real.exp (-(z.re - ω)) ^ n * ‖u‖)
      (fun n ↦ ?_) ?_
    · have h := hdecay (n : NNReal) u
      rwa [rescale_apply, smul_apply, NNReal.coe_natCast, mul_comm (-(z.re - ω)),
        Real.exp_nat_mul] at h
    · have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_nonneg _)
        (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hε))).const_mul M).mul_const ‖u‖
      simpa using h
  refine ⟨L, ⟨fun u ↦ ?_, fun x y hxy ↦ ?_⟩, hL⟩
  · -- `(z - A) L u = P u`, by closedness of the generator
    refine hT.isClosed_generator.mem_of_tendsto (b := atTop)
      (f := fun n : ℕ ↦ (G n u, z • G n u +
        Complex.exp (-z * (((n : NNReal) : ℝ) : ℂ)) • T (n : NNReal) (P u) - P u)) ?_
      (Eventually.of_forall fun n ↦ hT.truncatedTransform_mem_graph z n (P u))
    have h2 := (((hLy u).const_smul z).add (hzero u)).sub_const (P u)
    rw [add_zero] at h2
    exact (hLy u).prodMk_nhds h2
  · -- `L (z - A) x = P x`
    have hP : (P x, P y) ∈ hT.generator.graph := hT.map_mem_graph_of_commute hPT hxy
    have h1 (n : ℕ) : G n (z • x - y) =
        P x - Complex.exp (-z * (((n : NNReal) : ℝ) : ℂ)) • T (n : NNReal) (P x) := by
      rw [hG, mul_apply_eq_comp, _root_.map_sub, _root_.map_smul,
        hT.truncatedTransform_apply_of_mem_graph z n hP]
    have h2 : Tendsto (fun n ↦ G n (z • x - y)) atTop (𝓝 (P x - 0)) := by
      simp only [h1]
      exact tendsto_const_nhds.sub (hzero x)
    rw [sub_zero] at h2
    exact tendsto_nhds_unique (hLy _) h2

/-- **The half-plane to the right of the growth rate is in the resolvent set.** If
`‖T(t)‖ ≤ M e^{ωt}`, every `z` with `Re z > ω` is in the resolvent set of the generator. -/
theorem mem_resolventSet_generator {M ω : ℝ} (hM : ∀ t : NNReal, ‖T t‖ ≤ M * Real.exp (ω * t))
    (hz : ω < z.re) : z ∈ hT.generator.resolventSet := by
  obtain ⟨L, hL, -⟩ := hT.exists_isResolventAtOn (P := 1) (fun t ↦ Commute.one_left _)
    (fun t ↦ by rw [mul_one, norm_clm]; exact hM t) hz
  exact ⟨L, LinearPMap.isResolventAtOn_one_iff.mp hL⟩

/-- **The resolvent bound of a semigroup generator**: if `‖T(t)‖ ≤ M e^{ωt}` and `Re z > ω`,
then `‖(z - A)⁻¹‖ ≤ M / (Re z - ω)`. This is the bound that perturbation arguments for
generators start from. The resolvent is the limit of the truncated transforms
`∫₀ⁿ e^{-zs} T(s) ds`, and each of them has this bound (`norm_truncatedTransform_mul_le`). -/
theorem norm_resolvent_generator_le {M ω : ℝ} (hM : ∀ t : NNReal, ‖T t‖ ≤ M * Real.exp (ω * t))
    (hz : ω < z.re) : ‖hT.generator.resolvent z‖ ≤ M / (z.re - ω) := by
  have hM' : ∀ t : NNReal, ‖hT.clm t * 1‖ ≤ M * Real.exp (ω * t) := fun t ↦ by
    rw [mul_one, norm_clm]
    exact hM t
  obtain ⟨L, hL, hlim⟩ := hT.exists_isResolventAtOn (P := 1) (fun t ↦ Commute.one_left _) hM' hz
  rw [(LinearPMap.isResolventAtOn_one_iff.mp hL).resolvent_eq]
  exact le_of_tendsto' hlim.norm fun n ↦ hT.norm_truncatedTransform_mul_le hM' hz n

/-- The generator of a complex-linear semigroup on a Banach space has a resolvent. -/
theorem resolventSet_generator_nonempty : hT.generator.resolventSet.Nonempty := by
  obtain ⟨M, ω, hM⟩ := T.exists_norm_le_exp
  exact ⟨(ω + 1 : ℝ), hT.mem_resolventSet_generator hM (by simp)⟩

/-- **The spectral bound of the generator is at most the growth bound**, `s(A) ≤ ω₀(T)`: the
half-plane to the right of any growth rate is in the resolvent set. -/
theorem spectralBound_generator_le_growthBound : hT.generator.spectralBound ≤ T.growthBound := by
  refine le_sInf ?_
  rintro _ ⟨ω, ⟨M, hM⟩, rfl⟩
  refine sSup_le ?_
  rintro _ ⟨z, hz, rfl⟩
  exact EReal.coe_le_coe_iff.mpr (not_lt.mp fun h ↦ hz (hT.mem_resolventSet_generator hM h))

/-- **The resolvent from one truncated transform.** If `V` is a two-sided inverse of
`1 - e^{-zt} T(t)` for some time `t`, then `F V` is the resolvent of the generator `A` at `z`,
where `F = ∫₀ᵗ e^{-zs} T(s) ds`: the truncated transform satisfies
`(z - A) F = F (z - A) = 1 - e^{-zt} T(t)`, and `V` commutes with `A`. -/
theorem isResolventAt_truncatedTransform_mul {t : NNReal} {V : X →L[ℂ] X}
    (hUV : (1 - Complex.exp (-z * ((t : ℝ) : ℂ)) • hT.clm t) * V = 1)
    (hVU : V * (1 - Complex.exp (-z * ((t : ℝ) : ℂ)) • hT.clm t) = 1) :
    hT.generator.IsResolventAt z (hT.truncatedTransform z t * V) := by
  obtain ⟨U, hU⟩ : ∃ U : X →L[ℂ] X, U = 1 - Complex.exp (-z * ((t : ℝ) : ℂ)) • hT.clm t :=
    ⟨_, rfl⟩
  rw [← hU] at hUV hVU
  -- `V` commutes with a resolvent of `A`, hence with `A`
  obtain ⟨z₀, R₀, hR₀⟩ := hT.resolventSet_generator_nonempty
  have hUR : Commute U R₀ := by
    rw [hU]
    exact (Commute.one_left _).sub_left ((hR₀.commute_of_map_mem_graph
      fun _ _ hxy ↦ hT.map_mem_graph t hxy).smul_left _)
  have hVR : Commute V R₀ :=
    calc V * R₀ = V * R₀ * (U * V) := by rw [hUV, mul_one]
      _ = V * (R₀ * U) * V := by simp only [mul_assoc]
      _ = V * (U * R₀) * V := by rw [hUR.eq]
      _ = R₀ * V := by rw [← mul_assoc, hVU, one_mul]
  refine ⟨fun y ↦ ?_, fun x y hxy ↦ ?_⟩
  · have h1 := hT.truncatedTransform_mem_graph z t (V y)
    have e : z • hT.truncatedTransform z t (V y) +
        Complex.exp (-z * ((t : ℝ) : ℂ)) • T t (V y) - V y =
        z • (hT.truncatedTransform z t * V) y - y := by
      have h2 : V y - Complex.exp (-z * ((t : ℝ) : ℂ)) • T t (V y) = y := by
        have h3 : U (V y) = y := DFunLike.congr_fun hUV y
        rwa [hU] at h3
      rw [mul_apply_eq_comp]
      calc z • hT.truncatedTransform z t (V y) +
            Complex.exp (-z * ((t : ℝ) : ℂ)) • T t (V y) - V y
          = z • hT.truncatedTransform z t (V y) -
            (V y - Complex.exp (-z * ((t : ℝ) : ℂ)) • T t (V y)) := by abel
        _ = z • hT.truncatedTransform z t (V y) - y := by rw [h2]
    rwa [e] at h1
  · have h1 := hT.truncatedTransform_apply_of_mem_graph z t (hR₀.map_mem_graph hVR hxy)
    have h4 : V x - Complex.exp (-z * ((t : ℝ) : ℂ)) • T t (V x) = x := by
      have h5 : U (V x) = x := DFunLike.congr_fun hUV x
      rwa [hU] at h5
    rw [mul_apply_eq_comp, _root_.map_sub, _root_.map_smul, h1, h4]

/-- **The spectral inclusion theorem**, in the form of resolvent sets: if `e^{zt} - T(t)` is
invertible for some time `t`, then `z` is in the resolvent set of the generator `A`. Then
`1 - e^{-zt} T(t)` is invertible, and `isResolventAt_truncatedTransform_mul` gives the
resolvent. -/
theorem mem_resolventSet_generator_of_exp_mem_resolventSet {t : NNReal}
    (h : Complex.exp (z * ((t : ℝ) : ℂ)) ∈ resolventSet ℂ (hT.clm t)) :
    z ∈ hT.generator.resolventSet := by
  have hunit : IsUnit (1 - Complex.exp (-z * ((t : ℝ) : ℂ)) • hT.clm t) := by
    have h1 := (spectrum.mem_resolventSet_iff.mp h).smul
      (Units.mk0 _ (Complex.exp_ne_zero (-z * ((t : ℝ) : ℂ))))
    convert h1 using 1
    rw [Units.smul_def, Units.val_mk0, smul_sub, Algebra.algebraMap_eq_smul_one, smul_smul,
      ← Complex.exp_add, show -z * ((t : ℝ) : ℂ) + z * ((t : ℝ) : ℂ) = 0 by ring,
      Complex.exp_zero, one_smul]
  obtain ⟨u, hu⟩ := hunit
  exact (hT.isResolventAt_truncatedTransform_mul (V := ↑u⁻¹) (by rw [← hu]; exact u.mul_inv)
    (by rw [← hu]; exact u.inv_mul)).mem_resolventSet

/-- **The spectral inclusion theorem** `e^{t σ(A)} ⊆ σ(T(t))`: if `z` is in the spectrum of the
generator, then `e^{zt}` is in the spectrum of `T(t)`. -/
theorem exp_mem_spectrum_of_mem_spectrum_generator (hz : z ∈ hT.generator.spectrum)
    (t : NNReal) : Complex.exp (z * ((t : ℝ) : ℂ)) ∈ spectrum ℂ (hT.clm t) := fun h ↦
  hz (hT.mem_resolventSet_generator_of_exp_mem_resolventSet h)

end PDE.Analysis.Evolution.StronglyContinuousSemigroup.IsComplexLinear
