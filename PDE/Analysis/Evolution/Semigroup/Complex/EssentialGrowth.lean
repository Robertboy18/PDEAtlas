/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Data.EReal.Basic
public import PDE.Analysis.Spectral.RieszProjection.FiniteRank
public import PDE.Analysis.Evolution.Semigroup.Complex.PointSpectrum
public import PDE.Analysis.Evolution.Semigroup.Complex.Resolvent
public import PDE.Analysis.Order.FinitePositive
public import PDE.Analysis.Spectral.EssentialNorm
public import PDE.Analysis.Spectral.RieszProjection.Unbounded

/-!
# The essential growth bound of a semigroup and the spectrum above it

The essential growth bound `ω_ess(T)` measures how fast a semigroup grows modulo compact
operators. Above it the generator has only finitely many spectral points, each an eigenvalue
whose Riesz projection has finite rank, and off these projections the semigroup decays at a
rate below the chosen one. This is how a compact perturbation of a decaying semigroup gets a
finite-dimensional unstable part: compact differences do not change `ω_ess`, and for the
decaying semigroup `ω_ess` is at most the decay rate. Here `ω_ess` is an infimum over single
times; its description as a limit is not needed for the decomposition and is not proved. The
identity `ω₀ = max (ω_ess, s(A))` is `IsComplexLinear.growthBound_eq_max`, which also needs the
growth of the semigroup on the range of each Riesz projection.

## Main results

* `IsComplexLinear.essGrowthBound`: the infimum of the `ω` with `‖T(t)‖_ess < e^{ωt}` for some
  `t > 0`, where `‖·‖_ess` is the distance to the compact operators; `essGrowthBound_lt_iff`
  unfolds `ω_ess(T) < ω`.
* `IsComplexLinear.essGrowthBound_le_of_essNorm_le` and
  `essGrowthBound_le_of_isCompactOperator_sub_of_norm_le`: `ω_ess(T) ≤ ω` from one time `t > 0`
  with `‖T(t)‖_ess ≤ e^{ωt}`, for instance when `T(t) - S` is compact and `‖S‖ ≤ e^{ωt}`.
* `IsComplexLinear.essGrowthBound_le_of_isCompactOperator_sub`: `ω_ess(T) ≤ ω` when
  `T(t) - S(t)` is compact for every `t > 0` and `‖S(t)‖ ≤ M e^{ωt}`;
  `essGrowthBound_eq_of_isCompactOperator_sub`: two semigroups with compact differences have the
  same `ω_ess`.
* `IsComplexLinear.essGrowthBound_le_of_norm_le` and `essGrowthBound_le_growthBound`:
  `ω_ess(T) ≤ ω₀(T)`.
* `IsComplexLinear.range_le_domain_generator_of_finiteDimensional`: the range of a projection of
  finite rank that commutes with the semigroup lies in the domain of the generator.
* `IsComplexLinear.exists_spectral_gap`: for every `ω > ω_ess(T)`, the decomposition above.

## How it works

Let `ω > ω_ess(T)` and fix a time `t₀` with `T(t₀) = T₀ + K`, `K` compact and `‖T₀‖ < e^{ωt₀}`.
The library's results on compact perturbations of a bounded operator give a circle of radius
`r₀ < e^{ωt₀}` without spectrum of `T(t₀)` (`exists_radius_notMem_spectrum_of_pow_bound`) whose
outer Riesz projection `Q` has finite rank (`finiteDimensional_range_one_sub_rieszInner`), and
`‖T(t₀)ⁿ (1 - Q)‖ ≤ C ρⁿ` with `ρ < r₀` (`exists_norm_pow_mul_rieszInner_le`). Everything
commutes with the semigroup. Put `ω' = log ρ / t₀ < ω`. On the kernel of `Q` the semigroup
decays like `e^{ω't}`, so `z - A` is invertible there for `Re z > ω'`
(`IsComplexLinear.exists_isResolventAtOn`). The range of `Q` is finite dimensional and lies in
the domain of `A`, so `z - A` is invertible there except at finitely many eigenvalues
(`LinearPMap.exists_isResolventAtOn_of_finiteDimensional`), and such an eigenvalue `μ` has
`|e^{μt₀}| > r₀`, so `Re μ > ω'`. Adding the two inverses shows that the spectrum in `Re z > ω'`
is this finite set `Λ`. On a small circle around `μ ∈ Λ` the Riesz projection `P_μ` of `A`
vanishes on the kernel of `Q` by Cauchy's theorem, and the range of `Q` is spanned by
generalized eigenvectors, which `P_μ` fixes or kills. Hence `Σ_μ P_μ = Q`, and
`‖T(t) (1 - Σ_μ P_μ)‖ ≤ M e^{ω't}`. This is the continuous-time form of the discrete splitting
`PDE.Analysis.Spectral.exists_unstable_splitting`, with projections given by contour integrals
of the resolvent of the generator.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Graduate Texts in Mathematics 194, Springer, 2000, Chapter IV, Section 2 (the essential growth
  bound). <https://doi.org/10.1007/b97696>
-/

@[expose] public noncomputable section

open Filter Topology Set Metric PDE.Analysis.Spectral

namespace PDE.Analysis.Evolution.StronglyContinuousSemigroup.IsComplexLinear

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  {T : StronglyContinuousSemigroup X} (hT : T.IsComplexLinear) {x y : X} {z : ℂ}

include hT

/-! ### The essential growth bound -/

/-- **The essential growth bound** `ω_ess(T)` of a semigroup: the infimum of the `ω` such that
`‖T(t)‖_ess < e^{ωt}` for some `t > 0`. It is `-∞` when some `T(t)` is compact. -/
def essGrowthBound : EReal :=
  sInf ((fun ω : ℝ ↦ (ω : EReal)) ''
    {ω | ∃ t : NNReal, 0 < t ∧ essNorm (hT.clm t) < Real.exp (ω * t)})

/-- `ω_ess(T) < ω` exactly when `‖T(t)‖_ess < e^{ωt}` for some `t > 0`. Every use of the
essential growth bound goes through this form: it gives one time at which `T(t)` is within
`e^{ωt}` of a compact operator. For the direction from the right, a rate slightly below `ω`
still works at the same time, because the inequality is strict. -/
theorem essGrowthBound_lt_iff {ω : ℝ} :
    hT.essGrowthBound < ω ↔ ∃ t : NNReal, 0 < t ∧ essNorm (hT.clm t) < Real.exp (ω * t) := by
  constructor
  · intro h
    obtain ⟨_, ⟨ω₁, ⟨t, ht, hess⟩, rfl⟩, hlt⟩ := sInf_lt_iff.mp h
    have hω : ω₁ ≤ ω := (EReal.coe_lt_coe_iff.mp hlt).le
    exact ⟨t, ht, hess.trans_le (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hω t.coe_nonneg))⟩
  · rintro ⟨t, ht, hess⟩
    have ht' : (0 : ℝ) < t := ht
    -- a rate `ω₁ < ω` that still works at the time `t`
    set m := (essNorm (hT.clm t) + Real.exp (ω * t)) / 2
    have hm1 : essNorm (hT.clm t) < m := by simp only [m]; linarith
    have hm2 : m < Real.exp (ω * t) := by simp only [m]; linarith
    have hm0 : 0 < m := (essNorm_nonneg _).trans_lt hm1
    have hlog : Real.log m / t < ω := by
      rw [div_lt_iff₀ ht']
      exact (Real.log_lt_iff_lt_exp hm0).mpr hm2
    have hmem : ((Real.log m / t : ℝ) : EReal) ∈ (fun ω : ℝ ↦ (ω : EReal)) ''
        {ω | ∃ t : NNReal, 0 < t ∧ essNorm (hT.clm t) < Real.exp (ω * t)} :=
      ⟨Real.log m / t, ⟨t, ht, by rwa [div_mul_cancel₀ _ ht'.ne', Real.exp_log hm0]⟩, rfl⟩
    exact (sInf_le hmem).trans_lt (EReal.coe_lt_coe_iff.mpr hlog)

/-- **The essential norm at one time bounds the essential growth bound**: if
`‖T(t)‖_ess ≤ e^{ωt}` for one `t > 0`, then `ω_ess(T) ≤ ω`. -/
theorem essGrowthBound_le_of_essNorm_le {ω : ℝ} {t : NNReal} (ht : 0 < t)
    (h : essNorm (hT.clm t) ≤ Real.exp (ω * t)) : hT.essGrowthBound ≤ ω := by
  by_contra hlt
  obtain ⟨ω₁, h1, h2⟩ := EReal.lt_iff_exists_real_btwn.mp (not_le.mp hlt)
  have ht' : (0 : ℝ) < t := ht
  exact h2.not_gt (hT.essGrowthBound_lt_iff.mpr ⟨t, ht, h.trans_lt (Real.exp_lt_exp.mpr
    (mul_lt_mul_of_pos_right (EReal.coe_lt_coe_iff.mp h1) ht'))⟩)

/-- **A compact perturbation at one time.** If `T(t) - S` is compact for one `t > 0` and
`‖S‖ ≤ e^{ωt}`, then `ω_ess(T) ≤ ω`. With a comparison semigroup that has the bound `e^{ωt}`
with constant one, compactness of the difference at a single time is enough. -/
theorem essGrowthBound_le_of_isCompactOperator_sub_of_norm_le {S : X →L[ℂ] X} {ω : ℝ}
    {t : NNReal} (ht : 0 < t) (hK : IsCompactOperator (hT.clm t - S))
    (hS : ‖S‖ ≤ Real.exp (ω * t)) : hT.essGrowthBound ≤ ω := by
  refine hT.essGrowthBound_le_of_essNorm_le ht (le_trans ?_ hS)
  have h := essNorm_le_norm_sub (hT.clm t) hK
  rwa [sub_sub_cancel] at h

/-- **Compact perturbations.** If `T(t) - S(t)` is compact for every `t > 0` and
`‖S(t)‖ ≤ M e^{ωt}`, then `ω_ess(T) ≤ ω`: the distance from `T(t)` to the compact operators is
at most `‖S(t)‖`, and `M e^{ωt} < e^{ω₁t}` for every `ω₁ > ω` once `t` is large. -/
theorem essGrowthBound_le_of_isCompactOperator_sub {S : NNReal → X →L[ℂ] X} {M ω : ℝ}
    (hK : ∀ t : NNReal, 0 < t → IsCompactOperator (hT.clm t - S t))
    (hS : ∀ t : NNReal, ‖S t‖ ≤ M * Real.exp (ω * t)) : hT.essGrowthBound ≤ ω := by
  by_contra hlt
  obtain ⟨ω₁, h1, h2⟩ := EReal.lt_iff_exists_real_btwn.mp (not_le.mp hlt)
  refine h2.not_gt (hT.essGrowthBound_lt_iff.mpr ?_)
  have hω : ω < ω₁ := EReal.coe_lt_coe_iff.mp h1
  -- a time at which `M e^{ωt} < e^{ω₁t}`
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M (Real.one_lt_exp_iff.mpr (sub_pos.mpr hω))
  refine ⟨(n + 1 : ℕ), by exact_mod_cast n.succ_pos, ?_⟩
  have hess : essNorm (hT.clm (n + 1 : ℕ)) ≤ ‖S (n + 1 : ℕ)‖ := by
    have h := essNorm_le_norm_sub (hT.clm (n + 1 : ℕ))
      (hK (n + 1 : ℕ) (by exact_mod_cast n.succ_pos))
    rwa [sub_sub_cancel] at h
  have hM : M < Real.exp (ω₁ - ω) ^ (n + 1) :=
    hn.trans_le (pow_le_pow_right₀ (Real.one_lt_exp_iff.mpr (sub_pos.mpr hω)).le n.le_succ)
  calc essNorm (hT.clm (n + 1 : ℕ)) ≤ M * Real.exp (ω * ((n + 1 : ℕ) : NNReal)) :=
        hess.trans (hS _)
    _ < Real.exp (ω₁ - ω) ^ (n + 1) * Real.exp (ω * ((n + 1 : ℕ) : NNReal)) := by gcongr
    _ = Real.exp (ω₁ * ((n + 1 : ℕ) : NNReal)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, NNReal.coe_natCast]
        congr 1
        ring

/-- **Semigroups with compact differences have the same essential growth bound**: if
`T(t) - S(t)` is compact for every `t > 0`, then `ω_ess(T) = ω_ess(S)`. -/
theorem essGrowthBound_eq_of_isCompactOperator_sub {S : StronglyContinuousSemigroup X}
    (hS : S.IsComplexLinear)
    (hK : ∀ t : NNReal, 0 < t → IsCompactOperator (hT.clm t - hS.clm t)) :
    hT.essGrowthBound = hS.essGrowthBound := by
  unfold essGrowthBound
  congr 2
  ext ω
  exact exists_congr fun t ↦ and_congr_right fun ht ↦ by
    rw [essNorm_eq_of_isCompactOperator_sub (hK t ht)]

/-- The essential growth bound is at most the growth bound: if `‖T(t)‖ ≤ M e^{ωt}`, then
`ω_ess(T) ≤ ω`. -/
theorem essGrowthBound_le_of_norm_le {M ω : ℝ} (hM : ∀ t : NNReal, ‖T t‖ ≤ M * Real.exp (ω * t)) :
    hT.essGrowthBound ≤ ω :=
  hT.essGrowthBound_le_of_isCompactOperator_sub (S := hT.clm)
    (fun t _ ↦ by rw [sub_self]; exact isCompactOperator_zero)
    fun t ↦ by rw [norm_clm]; exact hM t

/-- The essential growth bound is at most the growth bound, `ω_ess(T) ≤ ω₀(T)`. -/
theorem essGrowthBound_le_growthBound : hT.essGrowthBound ≤ T.growthBound := by
  refine le_sInf ?_
  rintro _ ⟨ω, ⟨M, hM⟩, rfl⟩
  exact hT.essGrowthBound_le_of_norm_le hM

/-! ### Finite-dimensional invariant subspaces -/

variable [CompleteSpace X]

/-- **From discrete to continuous time.** A bound `‖T(t₀)ⁿ A‖ ≤ C ρⁿ` at the multiples of a time
`t₀ > 0` gives `‖T(t) A‖ ≤ M e^{ωt}` at all times, with `ω = log ρ / t₀`. This is
`norm_map_mul_le_of_norm_pow_mul_le` for the complex-linear operators of the semigroup. -/
theorem exists_norm_clm_mul_le_of_norm_pow_mul_le {A : X →L[ℂ] X} {t₀ : NNReal} (ht₀ : 0 < t₀)
    {C ρ : ℝ} (hρ : 0 < ρ) (hC : ∀ n : ℕ, ‖hT.clm t₀ ^ n * A‖ ≤ C * ρ ^ n) :
    ∃ M : ℝ, ∀ t : NNReal, ‖hT.clm t * A‖ ≤ M * Real.exp (Real.log ρ / t₀ * t) := by
  obtain ⟨B, -, hB⟩ := T.exists_norm_le_on_Icc t₀
  exact ⟨_, norm_map_mul_le_of_norm_pow_mul_le hT.clm_zero hT.clm_add ht₀
    (fun s hs ↦ (hT.norm_clm s).le.trans (hB s ⟨zero_le, hs⟩)) hρ hC⟩

/-- **Finite-dimensional invariant subspaces are in the domain.** If a projection `Q` of finite
rank commutes with the semigroup, its range is in the domain of the generator: `Q` maps the
dense domain onto a dense subspace of the range, and a dense subspace of a finite-dimensional
space is the whole space. -/
theorem range_le_domain_generator_of_finiteDimensional {Q : X →L[ℂ] X} (hQ : IsIdempotentElem Q)
    [FiniteDimensional ℂ (LinearMap.range Q.toLinearMap)] (hQT : ∀ t, Commute Q (hT.clm t)) :
    LinearMap.range Q.toLinearMap ≤ hT.generator.domain := by
  set W := hT.generator.domain ⊓ LinearMap.range Q.toLinearMap
  have : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le inf_le_right
  have hWc : IsClosed (W : Set X) := W.isClosed_of_finiteDimensional
  have himg : Q '' (hT.generator.domain : Set X) ⊆ W := by
    rintro _ ⟨d, hd, rfl⟩
    exact ⟨LinearPMap.mem_domain_of_mem_graph (hT.map_mem_graph_of_commute hQT
      (hT.generator.mem_graph ⟨d, hd⟩)), d, rfl⟩
  rintro _ ⟨y, rfl⟩
  have h1 : Q (Q y) ∈ closure (Q '' (hT.generator.domain : Set X)) :=
    image_closure_subset_closure_image Q.continuous
      ⟨Q y, hT.dense_domain_generator (Q y), rfl⟩
  have h2 : Q (Q y) = Q y := DFunLike.congr_fun hQ.eq y
  rw [h2] at h1
  exact (hWc.closure_subset_iff.mpr himg h1).1

/-! ### The spectrum above the essential growth bound -/

/-- **The spectrum above the essential growth bound.** Let `ω` be above the essential growth
bound of the semigroup `T` with generator `A`. Then there are a rate `ω' < ω`, a finite set `Λ`
and a radius `r > 0` such that

* the spectrum of `A` in the half-plane `Re z > ω'` is `Λ`, and every point of `Λ` is an
  eigenvalue;
* the closed discs of radius `r` around the points of `Λ` are disjoint and lie in the
  half-plane, so each circle `C(μ, r)` surrounds `μ` and no other point of the spectrum
  (`LinearPMap.closedBall_sdiff_subset_resolventSet`);
* the Riesz projections `P_μ = (2πi)⁻¹ ∮_{C(μ, r)} (z - A)⁻¹ dz` have finite rank;
* off these projections the semigroup decays: `‖T(t) (1 - Σ_μ P_μ)‖ ≤ M e^{ω't}`.

The proof splits the space with the Riesz projection of the bounded operator `T(t₀)` for a
circle without spectrum, at a time `t₀` where `T(t₀)` is within `e^{ωt₀}` of a compact
operator; see the module docstring. -/
theorem exists_spectral_gap {ω : ℝ} (hω : hT.essGrowthBound < ω) :
    ∃ (ω' : ℝ) (Λ : Finset ℂ) (r M : ℝ), ω' < ω ∧ 0 < r ∧
      (∀ z : ℂ, ω' < z.re → (z ∈ hT.generator.spectrum ↔ z ∈ Λ)) ∧
      (∀ μ ∈ Λ, ω' < μ.re - r) ∧
      (∀ μ ∈ Λ, ∀ ν ∈ Λ, μ ≠ ν → 2 * r < dist μ ν) ∧
      (∀ μ ∈ Λ, ∃ x, x ≠ 0 ∧ (x, μ • x) ∈ hT.generator.graph) ∧
      (∀ μ ∈ Λ, FiniteDimensional ℂ
        (LinearMap.range (rieszProjection hT.generator.resolvent μ r).toLinearMap)) ∧
      ∀ t : NNReal,
        ‖hT.clm t * (1 - ∑ μ ∈ Λ, rieszProjection hT.generator.resolvent μ r)‖ ≤
          M * Real.exp (ω' * t) := by
  classical
  -- a time `t₀` at which `T(t₀) = T₀ + K` with `K` compact and `‖T₀‖ < e^{ωt₀}`
  obtain ⟨t₀, ht₀, hess⟩ := hT.essGrowthBound_lt_iff.mp hω
  obtain ⟨K, hK, hTK⟩ := essNorm_lt_iff.mp hess
  have ht₀' : (0 : ℝ) < t₀ := ht₀
  obtain ⟨T₀, hT₀def⟩ : ∃ T₀, T₀ = hT.clm t₀ - K := ⟨_, rfl⟩
  have hB : hT.clm t₀ = T₀ + K := by rw [hT₀def, sub_add_cancel]
  have hq0 : 0 ≤ ‖T₀‖ := norm_nonneg _
  have hqω : ‖T₀‖ < Real.exp (ω * t₀) := by rwa [hT₀def]
  have hT₀ : ∀ n : ℕ, ‖T₀ ^ n‖ ≤ 1 * ‖T₀‖ ^ n := fun n ↦ by
    rw [one_mul]
    induction n with
    | zero =>
      rw [pow_zero, pow_zero]
      exact ContinuousLinearMap.norm_id_le
    | succ n ih =>
      rw [pow_succ, pow_succ]
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih hq0)
  -- a circle without spectrum of `T(t₀)`, of radius between `‖T₀‖` and `e^{ωt₀}`
  obtain ⟨r₀, hqr₀, hr₀ω, hfree⟩ := exists_radius_notMem_spectrum_of_pow_bound hB hK hT₀ hq0
    (a := (‖T₀‖ + Real.exp (ω * t₀)) / 2) (b := Real.exp (ω * t₀)) (by linarith) (by linarith)
  have hqr : ‖T₀‖ < r₀ := by linarith
  have hr₀ : 0 < r₀ := hq0.trans_lt hqr
  -- the stable projection `Pin` and the unstable projection `Q = 1 - Pin` of `T(t₀)`
  obtain ⟨Pin, hPindef⟩ : ∃ Pin, Pin = rieszInner (hT.clm t₀) r₀ := ⟨_, rfl⟩
  have hPin : IsIdempotentElem Pin := by
    rw [hPindef]
    exact rieszInner_idem hfree
  have hPinT : ∀ t, Commute Pin (hT.clm t) := fun t ↦ by
    rw [hPindef]
    exact (commute_rieszInner (hT.commute_clm t t₀)).symm
  obtain ⟨Q, hQdef⟩ : ∃ Q, Q = 1 - Pin := ⟨_, rfl⟩
  have hQ : IsIdempotentElem Q := by
    rw [hQdef]
    exact hPin.one_sub
  have : FiniteDimensional ℂ (LinearMap.range Q.toLinearMap) := by
    rw [hQdef, hPindef]
    exact finiteDimensional_range_one_sub_rieszInner hB hK hq0 hqr hT₀ hfree
  have hQT : ∀ t, Commute Q (hT.clm t) := fun t ↦ by
    rw [hQdef]
    exact (Commute.one_left _).sub_left (hPinT t)
  have hsum : Pin + Q = 1 := by rw [hQdef, add_sub_cancel]
  have hQPin : Q * Pin = 0 := by rw [hQdef, sub_mul, one_mul, hPin.eq, sub_self]
  -- the stable part decays in continuous time, at the rate `ω' = log ρ / t₀`
  obtain ⟨ρ, C, hρ, hρr, -, hC⟩ := exists_norm_pow_mul_rieszInner_le (a := hT.clm t₀) hr₀ hfree
  rw [← hPindef] at hC
  obtain ⟨M, hM⟩ := hT.exists_norm_clm_mul_le_of_norm_pow_mul_le ht₀ hρ hC
  obtain ⟨ω', hω'def⟩ : ∃ ω', ω' = Real.log ρ / t₀ := ⟨_, rfl⟩
  rw [← hω'def] at hM
  have hω'r : ω' < Real.log r₀ / t₀ := by
    rw [hω'def]
    gcongr
  have hr₀ω' : Real.log r₀ / t₀ < ω := by
    rw [div_lt_iff₀ ht₀']
    exact (Real.log_lt_iff_lt_exp hr₀).mpr hr₀ω
  -- the generator on the range of `Q`
  have hQA : ∀ ⦃x y⦄, (x, y) ∈ hT.generator.graph → (Q x, Q y) ∈ hT.generator.graph :=
    fun _ _ h ↦ hT.map_mem_graph_of_commute hQT h
  have hV := hT.range_le_domain_generator_of_finiteDimensional hQ hQT
  have hfixQ : ∀ x ∈ LinearMap.range Q.toLinearMap, Q x = x := by
    rintro _ ⟨y, rfl⟩
    exact DFunLike.congr_fun hQ.eq y
  have hAV : ∀ ⦃x y⦄, (x, y) ∈ hT.generator.graph → x ∈ LinearMap.range Q.toLinearMap →
      y ∈ LinearMap.range Q.toLinearMap := fun x y hxy hx ↦ by
    have h := hQA hxy
    rw [hfixQ x hx] at h
    exact ⟨y, hT.generator.mem_graph_snd_inj h hxy rfl⟩
  -- its eigenvalues
  have hΛfin := LinearPMap.finite_setOf_exists_mem_graph_smul hV hAV
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ : Finset ℂ, Λ = hΛfin.toFinset := ⟨_, rfl⟩
  have hΛ : ∀ μ, μ ∈ Λ ↔ ∃ x ∈ LinearMap.range Q.toLinearMap, x ≠ 0 ∧
      (x, μ • x) ∈ hT.generator.graph := fun μ ↦ by
    rw [hΛdef]
    exact hΛfin.mem_toFinset
  -- an eigenvalue in the range of `Q` is to the right of `log r₀ / t₀`
  have hΛre : ∀ μ ∈ Λ, Real.log r₀ / t₀ < μ.re := by
    intro μ hμ
    obtain ⟨x, hxV, hx0, hx⟩ := (hΛ μ).mp hμ
    have hBx : hT.clm t₀ x = Complex.exp (μ * ((t₀ : ℝ) : ℂ)) • x :=
      hT.apply_eq_exp_smul_of_mem_graph_smul hx t₀
    by_contra hle
    have hle' : μ.re * t₀ ≤ Real.log r₀ := (le_div_iff₀ ht₀').mp (not_lt.mp hle)
    have hnorm : ‖Complex.exp (μ * ((t₀ : ℝ) : ℂ))‖ ≤ r₀ := by
      rw [Complex.norm_exp, show (μ * ((t₀ : ℝ) : ℂ)).re = μ.re * t₀ by simp]
      exact (Real.exp_le_exp.mpr hle').trans_eq (Real.exp_log hr₀)
    have hPx : Pin x = 0 := by
      have h := hfixQ x hxV
      rwa [hQdef, _root_.sub_apply, one_apply_eq_self, sub_eq_self] at h
    rcases hnorm.lt_or_eq with hlt | heq
    · have h1 : Pin x = x := by
        rw [hPindef]
        exact rieszInner_apply_eq_self_of_apply_eq_smul hr₀ hfree hBx hlt
      exact hx0 (h1.symm.trans hPx)
    · exact hfree _ heq (ContinuousLinearMap.mem_spectrum_of_apply_eq_smul hBx hx0)
  -- the inverse of `z - A` on the stable part, for `Re z > ω'`
  have hLex : ∀ z : ℂ, ω' < z.re →
      ∃ L, hT.generator.IsResolventAtOn z Pin L ∧ L * Pin = L := by
    intro z hz
    obtain ⟨L, hL, hlim⟩ := hT.exists_isResolventAtOn hPinT hM hz
    refine ⟨L, hL, tendsto_nhds_unique ?_ hlim⟩
    have h := hlim.mul_const Pin
    simpa only [mul_assoc, hPin.eq] using h
  choose! L hL hLP using hLex
  have hPL : ∀ z, ω' < z.re → Pin * L z = L z := fun z hz ↦ by
    rw [← (hL z hz).commute.eq, hLP z hz]
  have hLps : IsPseudoResolventOn L {z : ℂ | ω' < z.re} := fun z hz w hw ↦
    (hL z hz).sub_eq (hL w hw) (hLP z hz) (hPL w hw)
  have hUo : IsOpen {z : ℂ | ω' < z.re} := isOpen_lt continuous_const Complex.continuous_re
  -- the inverse of `z - A` on the range of `Q`, for `z` outside `Λ`
  have hSex : ∀ z : ℂ, z ∉ Λ →
      ∃ S, hT.generator.IsResolventAtOn z Q S ∧ S * Q = S ∧ Q * S = S := fun z hz ↦
    LinearPMap.exists_isResolventAtOn_of_finiteDimensional hQ hQA hV fun x hQx hx ↦ by
      by_contra hx0
      exact hz ((hΛ z).mpr ⟨x, ⟨x, hQx⟩, hx0, hx⟩)
  choose! S hS hSQ hQS using hSex
  -- the resolvent of `A` in the half-plane, off `Λ`
  have hres : ∀ z : ℂ, ω' < z.re → z ∉ Λ → hT.generator.IsResolventAt z (L z + S z) :=
    fun z hz hzΛ ↦ (hL z hz).isResolventAt_add (hS z hzΛ) hsum
  have hspec : ∀ z : ℂ, ω' < z.re → (z ∈ hT.generator.spectrum ↔ z ∈ Λ) := fun z hz ↦
    ⟨fun hzσ ↦ by_contra fun hzΛ ↦ hzσ (hres z hz hzΛ).mem_resolventSet, fun hzΛ ↦ by
      obtain ⟨x, -, hx0, hx⟩ := (hΛ z).mp hzΛ
      exact LinearPMap.mem_spectrum_of_mem_graph_smul hx hx0⟩
  -- a radius for which the closed discs around `Λ` are disjoint and inside the half-plane
  obtain ⟨r₁, hr₁, hr₁lt⟩ := Finset.exists_pos_forall_lt Λ (fun μ ↦ μ.re - ω')
    fun μ hμ ↦ sub_pos.mpr (hω'r.trans (hΛre μ hμ))
  obtain ⟨r₂, hr₂, hr₂lt⟩ := Finset.exists_pos_forall_lt ((Λ ×ˢ Λ).filter fun p ↦ p.1 ≠ p.2)
    (fun p ↦ dist p.1 p.2 / 2) fun p hp ↦ half_pos (dist_pos.mpr (Finset.mem_filter.mp hp).2)
  obtain ⟨r, hrdef⟩ : ∃ r, r = min r₁ r₂ := ⟨_, rfl⟩
  have hr : 0 < r := by
    rw [hrdef]
    exact lt_min hr₁ hr₂
  have hrre : ∀ μ ∈ Λ, ω' < μ.re - r := fun μ hμ ↦ by
    have h1 := hr₁lt μ hμ
    have h2 := min_le_left r₁ r₂
    rw [hrdef]
    linarith
  have hrdist : ∀ μ ∈ Λ, ∀ ν ∈ Λ, μ ≠ ν → 2 * r < dist μ ν := fun μ hμ ν hν hne ↦ by
    have h1 := hr₂lt (μ, ν) (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hμ, hν⟩, hne⟩)
    have h2 := min_le_right r₁ r₂
    rw [hrdef]
    linarith
  have hball : ∀ μ ∈ Λ, closedBall μ r ⊆ {z : ℂ | ω' < z.re} := fun μ hμ z hz ↦ by
    have h1 : |z.re - μ.re| ≤ r := by
      rw [← Complex.sub_re]
      exact (Complex.abs_re_le_norm (z - μ)).trans (by rwa [← dist_eq_norm])
    have h2 := hrre μ hμ
    have h3 := neg_abs_le (z.re - μ.re)
    change ω' < z.re
    linarith
  have hnotΛ : ∀ μ ∈ Λ, ∀ z ∈ closedBall μ r, z ≠ μ → z ∉ Λ := fun μ hμ z hz hzμ hzΛ ↦ by
    have h1 := hrdist z hzΛ μ hμ hzμ
    have h2 : dist z μ ≤ r := hz
    linarith
  have hiso : ∀ μ ∈ Λ, closedBall μ r \ {μ} ⊆ hT.generator.resolventSet := fun μ hμ ↦
    LinearPMap.closedBall_sdiff_subset_resolventSet hspec hrre hrdist hμ
  have hsph : ∀ μ ∈ Λ, sphere μ r ⊆ hT.generator.resolventSet := fun μ hμ ↦
    sphere_subset_of_closedBall_sdiff_subset hr (hiso μ hμ)
  -- the Riesz projection of `A` at `μ ∈ Λ` vanishes on the stable part: Cauchy's theorem
  have hPPin : ∀ μ ∈ Λ, rieszProjection hT.generator.resolvent μ r * Pin = 0 := by
    intro μ hμ
    have hcont : ContinuousOn hT.generator.resolvent (sphere μ r) :=
      LinearPMap.continuousOn_resolvent.mono (hsph μ hμ)
    have heq : EqOn (fun z ↦ hT.generator.resolvent z * Pin) L (sphere μ r) := fun z hz ↦ by
      have hzc := sphere_subset_closedBall hz
      have hzΛ := hnotΛ μ hμ z hzc (ne_of_mem_sphere hz hr.ne')
      have hzre := hball μ hμ hzc
      change hT.generator.resolvent z * Pin = L z
      rw [(hres z hzre hzΛ).resolvent_eq, add_mul, hLP z hzre, ← hSQ z hzΛ, mul_assoc, hQPin,
        mul_zero, add_zero]
    rw [rieszProjection, dunfordIntegral_mul_right (g := 1) hr.le continuousOn_const hcont,
      dunfordIntegral_congr_left hr.le heq]
    exact rieszProjection_eq_zero hLps hUo hr.le (hball μ hμ)
  have hPQ : ∀ μ ∈ Λ, rieszProjection hT.generator.resolvent μ r * Q =
      rieszProjection hT.generator.resolvent μ r := fun μ hμ ↦ by
    have h : rieszProjection hT.generator.resolvent μ r * (Pin + Q) =
        rieszProjection hT.generator.resolvent μ r := by rw [hsum, mul_one]
    rwa [mul_add, hPPin μ hμ, zero_add] at h
  have hQP : ∀ μ ∈ Λ, Q * rieszProjection hT.generator.resolvent μ r =
      rieszProjection hT.generator.resolvent μ r := fun μ hμ ↦ by
    rw [(LinearPMap.commute_rieszProjection_resolvent hr.le (hsph μ hμ) hQA).eq, hPQ μ hμ]
  have hfinP : ∀ μ ∈ Λ, FiniteDimensional ℂ
      (LinearMap.range (rieszProjection hT.generator.resolvent μ r).toLinearMap) := by
    intro μ hμ
    refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range Q.toLinearMap) ?_
    rintro _ ⟨y, rfl⟩
    exact ⟨rieszProjection hT.generator.resolvent μ r y, DFunLike.congr_fun (hQP μ hμ) y⟩
  -- on the range of `Q` the Riesz projections add up to the identity
  have hsumV : ∀ v ∈ LinearMap.range Q.toLinearMap,
      (∑ μ ∈ Λ, rieszProjection hT.generator.resolvent μ r) v = v := by
    intro v hv
    refine Submodule.iSup_induction
      (motive := fun v ↦ (∑ μ ∈ Λ, rieszProjection hT.generator.resolvent μ r) v = v) _
      (LinearPMap.le_iSup_genEigenspace_inf hV hAV hv) ?_ (by simp)
      fun x y hx hy ↦ by rw [_root_.map_add, hx, hy]
    rintro ν x ⟨hx, hxV⟩
    by_cases hx0 : x = 0
    · rw [hx0, _root_.map_zero]
    have hν : ν ∈ Λ := by
      obtain ⟨u, huV, hu0, hu⟩ :=
        LinearPMap.exists_mem_graph_smul_of_mem_genEigenspace hAV hx hxV hx0
      exact (hΛ ν).mpr ⟨u, huV, hu0, hu⟩
    rw [_root_.sum_apply, Finset.sum_eq_single ν]
    · exact LinearPMap.rieszProjection_resolvent_apply_eq_self_of_mem_genEigenspace hr
        (hsph ν hν) (mem_ball_self hr) hx
    · intro μ hμ hμν
      refine LinearPMap.rieszProjection_resolvent_apply_eq_zero_of_mem_genEigenspace hr
        (hsph μ hμ) (fun hνb ↦ ?_) hx
      have h1 := hrdist μ hμ ν hν hμν
      have h2 : dist ν μ ≤ r := hνb
      rw [dist_comm] at h2
      linarith
    · exact fun h ↦ absurd hν h
  have hsumQ : ∑ μ ∈ Λ, rieszProjection hT.generator.resolvent μ r = Q := by
    refine ContinuousLinearMap.ext fun x ↦ ?_
    have h1 : (∑ μ ∈ Λ, rieszProjection hT.generator.resolvent μ r) x =
        (∑ μ ∈ Λ, rieszProjection hT.generator.resolvent μ r) (Q x) := by
      rw [_root_.sum_apply, _root_.sum_apply]
      exact Finset.sum_congr rfl fun μ hμ ↦ (DFunLike.congr_fun (hPQ μ hμ) x).symm
    rw [h1, hsumV (Q x) ⟨x, rfl⟩]
  refine ⟨ω', Λ, r, M, hω'r.trans hr₀ω', hr, hspec, hrre, hrdist, fun μ hμ ↦ ?_, hfinP,
    fun t ↦ ?_⟩
  · obtain ⟨x, -, hx0, hx⟩ := (hΛ μ).mp hμ
    exact ⟨x, hx0, hx⟩
  · rw [hsumQ, hQdef, sub_sub_cancel]
    exact hM t

end PDE.Analysis.Evolution.StronglyContinuousSemigroup.IsComplexLinear
