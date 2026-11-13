/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Dichotomy
public import PDE.Analysis.Spectral.UnstableSplitting
public import PDE.Fluid.NavierStokes.Selfsimilar.ProfileEigen

/-!
# Exponential dichotomy of the profile evolution

Let `U` be an unstable profile and `S` the self-similar evolution around it, with generator
`L₀ + profileTransport U`. On `L²` the time-one map `S(1)` is a compact perturbation of the free
time-one map, a contraction, and it has the eigenvalue `e^μ > 1`. Read through the isometry of
`L²` fields with a Hilbert space, the unstable splitting gives a radius `e^η` with
`0 < η < min(μ, 1/16)` whose circle carries no spectrum, a finite-rank projection `P₀` fixing the
eigenvector and commuting with `S`, with divergence-free range since the gradient part evolves
by the free contraction, the bound `‖S(1)ⁿ (1 - P₀)‖ ≤ M e^{ω' n}` with `ω' < η`, and
an inverse `W₀` of `S(1)` on the range of `P₀` with `‖W₀ⁿ P₀‖ ≤ M e^{-κ n}`, `κ > η`
(`UnstableProfile.exists_profileSemigroup_splitting`).

The semigroup maps `L²` into `H³` at positive times, so a lift `G` of `S(1)` from `L²` to `H³`
carries the splitting to `H³`: `P = G W₀ ι` and `W = G W₀² ι`, with `ι` the lowering from `H³` to
`L²`. The semigroup on `H³` extends to a group on the range of `P`. With the gain `S(r)` from
`H²` to `H³` and the Leray projection `Π`, the stable kernel `(1 - P) S(r) Π` has the bound
`M r^{-1/2} e^{η r}`, the unstable kernel `S(-r) P Π` the bound `M e^{-κ r}`, and the
eigenvector gives the homogeneous unstable paths `τ ↦ e^{μ τ} s e`. These are the kernels and
paths of the mixed ancient Duhamel operator `mixedDuhamelOperatorOfJoint` with weight `η` and
stable rate `η < 2η` (Hou, Wang and Yang, Section 2.2, (2.14)-(2.16)).
The data are collected in `ProfileDichotomy`; `exists_dichotomy` states them for an unstable
profile.

## References

* T. Hou, Y. Wang, and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Section 2.2, the Riesz projection
  and (2.14)-(2.16), p. 13.
  <https://arxiv.org/abs/2509.25116v2>
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace IncompressibleFlow
open NavierStokes NavierStokes.Selfsimilar HeatEquation.WholeSpace PDE.Analysis.Evolution
open scoped ENNReal NNReal Sobolev BoundedContinuousFunction

namespace NavierStokes.Nonuniqueness.UnstableProfile

variable (D : UnstableProfile)

/-- **Unstable splitting on `L²`.** The time-one map of the profile evolution on `L²` splits off
a finite-rank unstable part: there are rates `0 < η < 1/16`, `η < μ`, an eigenvector `u` with
`S(t) u = e^{μt} u`, a projection `P₀` fixing `u`, commuting with `S` and with divergence-free
range, and an inverse `W₀` of `S(1)` on the range of `P₀`, with
`‖S(1)ⁿ (1 - P₀)‖ ≤ M e^{ω' n}` for some `0 ≤ ω' < η` and `‖W₀ⁿ P₀‖ ≤ M' e^{-κ n}` for some
`κ > η`. -/
theorem exists_profileSemigroup_splitting :
    ∃ (μ η : ℝ) (u : VectorH 3 0) (P₀ W₀ : VectorH 3 0 →L[ℝ] VectorH 3 0),
      0 < η ∧ η < 1 / 16 ∧ η < μ ∧ u ≠ 0 ∧
      (∀ t : ℝ≥0, profileSemigroup 0 D.transportCoefficients D.stretchingCoefficients
        (D.profileCoefficientBounds 0) t u = Real.exp (μ * t) • u) ∧
      P₀ u = u ∧ IsIdempotentElem P₀ ∧ FiniteDimensional ℝ (LinearMap.range P₀.toLinearMap) ∧
      (∀ t, Commute (profileSemigroup 0 D.transportCoefficients D.stretchingCoefficients
        (D.profileCoefficientBounds 0) t) P₀) ∧
      (∀ t, Commute (profileSemigroup 0 D.transportCoefficients D.stretchingCoefficients
        (D.profileCoefficientBounds 0) t) W₀) ∧
      profileSemigroup 0 D.transportCoefficients D.stretchingCoefficients
        (D.profileCoefficientBounds 0) 1 * W₀ = P₀ ∧ P₀ * W₀ = W₀ ∧
      (∀ y, leraySobolev 3 0 (P₀ y) = P₀ y) ∧
      (∃ M ω' : ℝ, 0 ≤ M ∧ 0 ≤ ω' ∧ ω' < η ∧ ∀ n : ℕ,
        ‖profileSemigroup 0 D.transportCoefficients D.stretchingCoefficients
          (D.profileCoefficientBounds 0) 1 ^ n * (1 - P₀)‖ ≤ M * Real.exp (ω' * n)) ∧
      ∃ M κ : ℝ, 0 ≤ M ∧ η < κ ∧ ∀ n : ℕ, ‖W₀ ^ n * P₀‖ ≤ M * Real.exp (-(κ * n)) := by
  set hk := D.profileCoefficientBounds 0
  set S := profileSemigroup 0 D.transportCoefficients D.stretchingCoefficients hk
  have hS : S = profileSemigroup0 D.transportCoefficients D.stretchingCoefficients hk :=
    profileSemigroup_zero hk
  obtain ⟨μ, hμ, u, hu0, -, hSu⟩ := D.exists_profileSemigroup_eigenvector hk
  rw [← hS] at hSu
  set F : VectorH 3 0 →L[ℝ] VectorH 3 0 := vectorSelfsimilarHeatSemigroup 3 0 1
  have hK : IsCompactOperator (S 1 - F) := by
    rw [hS]
    exact D.isCompactOperator_profileSemigroup_sub hk
  have hF1 : ‖F‖ ≤ 1 := isContraction_vectorSelfsimilarHeatSemigroup (n := 3) (by norm_num) 1
  have hF : ∀ m : ℕ, ‖F ^ m‖ ≤ 1 * 1 ^ m := by
    intro m
    rw [one_pow, one_mul]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [pow_zero]
      exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ by simp
    · exact (norm_pow_le' F hm).trans (pow_le_one₀ (by positivity) hF1)
  have hTu : S 1 u = Real.exp μ • u := by
    rw [hSu 1, NNReal.coe_one, mul_one]
  set w := min μ (1 / 16)
  have hw : 0 < w := lt_min hμ (by norm_num)
  obtain ⟨P₀, η, hη₁, hη₂, hP₀, hfin, hPu, hcomm, ⟨M, ω', hM, hω', hst⟩, W₀, hTW, -, hPW, -,
      hcommW, ⟨M', κ, hM', hκ, hun⟩⟩ :=
    PDE.Analysis.Spectral.exists_unstable_splitting_of_linearIsometryEquiv
      (vectorLpEquivZeroOrder 3).symm (S 1) F (S 1 - F) (add_sub_cancel F (S 1)).symm hK hF hu0
      (Real.one_lt_exp_iff.mpr hμ) hTu (by rw [Real.log_one]; positivity) (half_lt_self hw)
      (by rw [Real.log_exp]; exact min_le_left _ _)
  have hη : 0 < η := (half_pos hw).trans hη₁
  have hcS : ∀ t, Commute (S t) (S 1) := fun t ↦ S.map_comm t 1
  have hRA : (1 - leraySobolev 3 0) * S 1 = F * (1 - leraySobolev 3 0) := by
    ext1 v
    exact sub_leraySobolev_profileSemigroup hk 1 v
  have hRP := PDE.Analysis.Evolution.mul_eq_zero_of_mul_eq_mul hP₀ hTW hPW hRA
    (fun m ↦ by simpa using hF m) (hη.trans hκ) hun
  refine ⟨μ, η, u, P₀, W₀, hη, hη₂.trans_le (min_le_right _ _), hη₂.trans_le (min_le_left _ _),
    hu0, hSu, hPu, hP₀, hfin, fun t ↦ hcomm _ (hcS t), fun t ↦ hcommW _ (hcS t), hTW, hPW,
    fun y ↦ (sub_eq_zero.mp (congrArg (fun A ↦ A y) hRP)).symm,
    ⟨M, max ω' 0, hM, le_max_right _ _, max_lt hω' hη, fun n ↦ (hst n).trans ?_⟩,
    M', κ, hM', hκ, hun⟩
  gcongr
  exact le_max_left _ _

end NavierStokes.Nonuniqueness.UnstableProfile

namespace NavierStokes.Selfsimilar

open NavierStokes.Nonuniqueness

/-- An exponential dichotomy of the profile evolution `S` with coefficients `b`, `c` from vector
`H²` to vector `H³`, in the form used by the mixed ancient Duhamel operator
`mixedDuhamelOperatorOfJoint`: a weight `η`, a finite-rank projection `P` on `H³` commuting with
`S`, the stable kernel `(1 - P) S(r) Π` with the bound `Ms r^{-1/2} e^{ω r}`, `ω < 2η`, the
unstable kernel `S(-r) P Π` with the bound `Mu e^{-κ r}`, `κ ≥ η`, and an eigenvector `e` with
eigenvalue `μ > η` together with its homogeneous paths. The range of `P` consists of
divergence-free fields. -/
structure ProfileDichotomy (transport : Fin 3 → DerivLp 3 ∞ Set.univ)
    (stretching : Fin 3 → Fin 3 → DerivLp 3 ∞ Set.univ)
    (hk2 : ProfileCoefficientBounds 2 transport stretching)
    (hk3 : ProfileCoefficientBounds 3 transport stretching) where
  /-- The weight of the ancient paths. -/
  η : ℝ
  /-- The growth rate in the bound of the stable kernel. -/
  ω : ℝ
  /-- The decay rate in the bound of the unstable kernel. -/
  κ : ℝ
  /-- The constant in the bound of the stable kernel. -/
  Ms : ℝ
  /-- The constant in the bound of the unstable kernel. -/
  Mu : ℝ
  /-- The stable kernel `S(r) (1 - P) Π`. -/
  Ks : ℝ → VectorH 3 2 →L[ℝ] VectorH 3 3
  /-- The unstable kernel `(S|range P)(-r) P Π`. -/
  Ku : ℝ → VectorH 3 2 →L[ℝ] VectorH 3 3
  /-- The projection onto the unstable part. -/
  P : VectorH 3 3 →L[ℝ] VectorH 3 3
  /-- An unstable eigenvector. -/
  e : VectorH 3 3
  /-- The unstable eigenvalue of `e`. -/
  μ : ℝ
  /-- The homogeneous unstable paths. -/
  b : ℝ → (Iic (0 : ℝ) →ᵇ VectorH 3 3)
  /-- The weight is positive. -/
  η_pos : 0 < η
  /-- The weight is at most `1/16`. -/
  η_le : η ≤ 1 / 16
  /-- The stable rate is below the weight `2η` of quadratic forcing. -/
  ω_lt : ω < 2 * η
  /-- The unstable decay rate is at least the weight. -/
  η_le_κ : η ≤ κ
  /-- The stable constant is nonnegative. -/
  Ms_nonneg : 0 ≤ Ms
  /-- The unstable constant is nonnegative. -/
  Mu_nonneg : 0 ≤ Mu
  /-- The stable kernel acts jointly continuously at positive times. -/
  continuousOn_Ks : ContinuousOn (fun p : ℝ × VectorH 3 2 ↦ Ks p.1 p.2) (Ioi 0 ×ˢ univ)
  /-- The unstable kernel is continuous in operator norm. -/
  continuous_Ku : Continuous Ku
  /-- The stable kernel has the bound `Ms r^{-1/2} e^{ω r}`. -/
  norm_Ks_le : ∀ r, 0 < r → ‖Ks r‖ ≤ Ms * r ^ (-(1 / 2 : ℝ)) * Real.exp (ω * r)
  /-- The unstable kernel has the bound `Mu e^{-κ r}` at nonnegative times. -/
  norm_Ku_le : ∀ r, 0 ≤ r → ‖Ku r‖ ≤ Mu * Real.exp (-(κ * r))
  /-- The projection annihilates the stable kernel. -/
  P_Ks : ∀ r, 0 < r → ∀ x, P (Ks r x) = 0
  /-- The eigenvector is nonzero. -/
  e_ne_zero : e ≠ 0
  /-- The projection fixes the eigenvector. -/
  P_e : P e = e
  /-- The projection is idempotent. -/
  isIdempotentElem_P : IsIdempotentElem P
  /-- The projection has finite rank. -/
  finiteDimensional_range_P : FiniteDimensional ℝ (LinearMap.range P.toLinearMap)
  /-- The range of the projection consists of divergence-free fields. -/
  leraySobolev_P : ∀ x, leraySobolev 3 3 (P x) = P x
  /-- The projection commutes with the evolution on `H³`. -/
  P_semigroup : ∀ (t : ℝ≥0) x, P (profileSemigroup 3 transport stretching hk3 t x) =
    profileSemigroup 3 transport stretching hk3 t (P x)
  /-- The stable kernel is `(1 - P) S(r) Π`, with `S(r)` the gain from `H²` to `H³`. -/
  Ks_apply : ∀ r x, Ks r x = profileGain 2 transport stretching hk2 r (leraySobolev 3 2 x) -
    P (profileGain 2 transport stretching hk2 r (leraySobolev 3 2 x))
  /-- The evolution continues the stable kernel. -/
  semigroup_Ks : ∀ (t : ℝ≥0) r, 0 < r → ∀ x,
    profileSemigroup 3 transport stretching hk3 t (Ks r x) = Ks (t + r) x
  /-- At negative arguments the unstable kernel is `P S(r) Π`. -/
  Ku_neg : ∀ r, 0 < r → ∀ x,
    Ku (-r) x = P (profileGain 2 transport stretching hk2 r (leraySobolev 3 2 x))
  /-- The evolution shifts the unstable kernel, so `Ku(r)` inverts `S(r)` on the range of
  `P`. -/
  semigroup_Ku : ∀ (t : ℝ≥0) r x,
    profileSemigroup 3 transport stretching hk3 t (Ku r x) = Ku (r - t) x
  /-- The projection fixes the unstable kernel. -/
  P_Ku : ∀ r x, P (Ku r x) = Ku r x
  /-- The eigenvalue exceeds the weight. -/
  η_lt_μ : η < μ
  /-- The evolution acts on the eigenvector by `e^{μt}`. -/
  semigroup_e : ∀ t : ℝ≥0, profileSemigroup 3 transport stretching hk3 t e = Real.exp (μ * t) • e
  /-- The homogeneous path `b s` decodes to `τ ↦ e^{μτ} s e`. -/
  ancientLift_b : ∀ s τ, τ ≤ 0 → ancientLift η (b s) τ = Real.exp (μ * τ) • (s • e)
  /-- The homogeneous path `b s` has the terminal value `s e`. -/
  b_zero : ∀ s, b s ⟨0, self_mem_Iic⟩ = s • e
  /-- The homogeneous path `b s` has norm at most `|s| ‖e‖`. -/
  norm_b_le : ∀ s, ‖b s‖ ≤ |s| * ‖e‖

namespace ProfileDichotomy

variable {b : Fin 3 → DerivLp 3 ∞ Set.univ} {c : Fin 3 → Fin 3 → DerivLp 3 ∞ Set.univ}
  {hk2 : ProfileCoefficientBounds 2 b c} {hk3 : ProfileCoefficientBounds 3 b c}
  (d : ProfileDichotomy b c hk2 hk3)

/-- At a positive time the two kernels add up to the gain: `Ks(r) + Ku(-r) = S(r) Π`. -/
theorem Ks_add_Ku_neg {r : ℝ} (hr : 0 < r) (x : VectorH 3 2) :
    d.Ks r x + d.Ku (-r) x = profileGain 2 b c hk2 r (leraySobolev 3 2 x) := by
  rw [d.Ks_apply, d.Ku_neg r hr, sub_add_cancel]

/-- The unstable eigenvector is divergence-free. -/
theorem leraySobolev_e : leraySobolev 3 3 d.e = d.e := by
  conv_lhs => rw [← d.P_e]
  rw [d.leraySobolev_P, d.P_e]

end ProfileDichotomy

section Lift

variable {b : Fin 3 → DerivLp 3 ∞ Set.univ} {c : Fin 3 → Fin 3 → DerivLp 3 ∞ Set.univ}
  (hk0 : ProfileCoefficientBounds 0 b c) (hk2 : ProfileCoefficientBounds 2 b c)
  (hk3 : ProfileCoefficientBounds 3 b c)

local notation "𝐒₀" => profileSemigroup 0 b c hk0
local notation "𝐒₃" => profileSemigroup 3 b c hk3
local notation "𝛊₃" => (vectorLowerOrderCLM (m := 3) (Ω := Set.univ) (Nat.zero_le 3) :
  VectorH 3 3 →L[ℝ] VectorH 3 0)
local notation "𝛊₂" => (vectorLowerOrderCLM (m := 3) (Ω := Set.univ) (Nat.zero_le 2) :
  VectorH 3 2 →L[ℝ] VectorH 3 0)

/-- Kernels from a splitting on `H³`: a finite-rank projection `P` commuting with the evolution
on `H³`, an inverse `W` of `S(1)` on its range with discrete bounds, an operator `Q` from `H²`
into the range of `P` with `S(r) Q = P S(r) Π` at positive times, and an eigenvector `e` fixed
by `P` give an exponential dichotomy of the profile evolution from `H²` to `H³`. -/
theorem nonempty_profileDichotomy_of_kernels {η ω' κ μ M₃ M₃' : ℝ}
    {P W : VectorH 3 3 →L[ℝ] VectorH 3 3} {Q : VectorH 3 2 →L[ℝ] VectorH 3 3} {e : VectorH 3 3}
    (hη16 : η < 1 / 16) (hημ : η < μ) (hω'0 : 0 ≤ ω') (hω'η : ω' < η)
    (hηκ : η < κ) (hP : IsIdempotentElem P) (hTW : 𝐒₃ 1 * W = P) (hPW : P * W = W)
    (hcP : ∀ t, Commute (𝐒₃ t) P) (hcW : ∀ t, Commute (𝐒₃ t) W)
    (hfin : FiniteDimensional ℝ (LinearMap.range P.toLinearMap))
    (hst₃ : ∀ n : ℕ, ‖𝐒₃ 1 ^ n * (1 - P)‖ ≤ M₃ * Real.exp (ω' * n))
    (hun₃ : ∀ n : ℕ, ‖W ^ n * P‖ ≤ M₃' * Real.exp (-(κ * n)))
    (hLP : ∀ x, leraySobolev 3 3 (P x) = P x) (hPQ : ∀ x, P (Q x) = Q x)
    (hQ : ∀ r, 0 < r → ∀ x,
      𝐒₃ r.toNNReal (Q x) = P (profileGain 2 b c hk2 r (leraySobolev 3 2 x)))
    (he0 : e ≠ 0) (hPe : P e = e) (hSe : ∀ t : ℝ≥0, 𝐒₃ t e = Real.exp (μ * t) • e) :
    Nonempty (ProfileDichotomy b c hk2 hk3) := by
  have hη : 0 < η := by linarith
  have hM₃'0 : 0 ≤ M₃' := by
    have h := (ContinuousLinearMap.opNorm_nonneg _).trans (hun₃ 0)
    rw [Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, mul_one] at h
    exact h
  -- the bound of the semigroup on `[0, 1]`
  obtain ⟨B, hB0, hB1⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℝ≥0, s ≤ 1 → ‖𝐒₃ s‖ ≤ B := by
    obtain ⟨B₀, ωB, hB₀, hB⟩ := profileSemigroup_exists_norm_le hk3
    refine ⟨B₀ * Real.exp |ωB|, by positivity, fun s hs ↦ (hB s).trans ?_⟩
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hB₀
    calc ωB * s ≤ |ωB| * s := mul_le_mul_of_nonneg_right (le_abs_self _) s.2
      _ ≤ |ωB| * 1 := mul_le_mul_of_nonneg_left (by exact_mod_cast hs) (abs_nonneg _)
      _ = |ωB| := mul_one _
  have hstc := StronglyContinuousSemigroup.norm_mul_le_of_norm_pow_mul_le _ hω'0 hB1 hst₃
  -- the gain from `H²` to `H³`
  have hTg : ∀ (t : ℝ≥0) (s : ℝ), 0 < s → ∀ y,
      𝐒₃ t (profileGain 2 b c hk2 s y) = profileGain 2 b c hk2 (t + s) y :=
    fun t s hs y ↦ profileSemigroup_profileGain hk3 hk2 t hs y
  obtain ⟨Ms, hMs, hKs⟩ := exists_norm_stableKernel_le (L := leraySobolev 3 2) hcP hTg hstc
    (fun r hr ↦ norm_profileGain_le hk2 hr) hω'0 hω'η
  have hKu : ∀ r, 0 < r → ∀ x, unstableKernel 𝐒₃ W P Q (-r) x =
      P (profileGain 2 b c hk2 r (leraySobolev 3 2 x)) := fun r hr x ↦ by
    rw [unstableKernel_neg hr.le, hPQ, hQ r hr]
  exact ⟨{
    η := η, ω := η, κ := κ, Ms := Ms, Mu := B * M₃' * ‖Q‖,
    Ks := stableKernel P (profileGain 2 b c hk2) (leraySobolev 3 2),
    Ku := unstableKernel 𝐒₃ W P Q, P := P, e := e, μ := μ,
    b := fun s ↦ exponentialPath hημ.le (s • e),
    η_pos := hη, η_le := hη16.le, ω_lt := by linarith, η_le_κ := hηκ.le, Ms_nonneg := hMs,
    Mu_nonneg := by positivity,
    continuousOn_Ks := continuousOn_stableKernel (continuousOn_profileGain_apply_prod hk2),
    continuous_Ku := continuous_unstableKernel hP hTW hPW,
    norm_Ks_le := hKs,
    norm_Ku_le := fun r hr ↦ norm_unstableKernel_le (hη.trans hηκ).le hB1 hun₃ hr,
    P_Ks := fun r _ x ↦ map_stableKernel hP r x,
    e_ne_zero := he0, P_e := hPe, isIdempotentElem_P := hP, finiteDimensional_range_P := hfin,
    leraySobolev_P := hLP,
    P_semigroup := fun t x ↦ (congrArg (fun A ↦ A x) (hcP t).eq).symm,
    Ks_apply := fun r x ↦ stableKernel_apply _ _ _ r x,
    semigroup_Ks := fun t r hr x ↦ semigroup_stableKernel hcP hTg t hr x,
    Ku_neg := hKu,
    semigroup_Ku := semigroup_unstableKernel hP hTW hPW hcW hcP,
    P_Ku := map_unstableKernel hP hPW hcP,
    η_lt_μ := hημ, semigroup_e := hSe,
    ancientLift_b := fun s τ hτ ↦ ancientLift_exponentialPath hημ.le (s • e) hτ,
    b_zero := fun s ↦ exponentialPath_zero hημ.le (s • e),
    norm_b_le := fun s ↦ (norm_exponentialPath_le hημ.le (s • e)).trans_eq
      (by rw [norm_smul, Real.norm_eq_abs]) }⟩

/-- An unstable splitting of the profile evolution on `L²` lifts by smoothing to an exponential
dichotomy of the kernels from `H²` to `H³`. -/
theorem nonempty_profileDichotomy_of_splitting {μ η ω' κ M M' : ℝ} {u : VectorH 3 0}
    {P₀ W₀ : VectorH 3 0 →L[ℝ] VectorH 3 0}
    (hη16 : η < 1 / 16) (hημ : η < μ) (hu0 : u ≠ 0)
    (hSu : ∀ t : ℝ≥0, 𝐒₀ t u = Real.exp (μ * t) • u) (hPu : P₀ u = u)
    (hP₀ : IsIdempotentElem P₀) (hfin₀ : FiniteDimensional ℝ (LinearMap.range P₀.toLinearMap))
    (hcP₀ : ∀ t, Commute (𝐒₀ t) P₀) (hcW₀ : ∀ t, Commute (𝐒₀ t) W₀)
    (hTW₀ : 𝐒₀ 1 * W₀ = P₀) (hPW₀ : P₀ * W₀ = W₀) (hL₀ : ∀ y, leraySobolev 3 0 (P₀ y) = P₀ y)
    (hM : 0 ≤ M) (hω'0 : 0 ≤ ω') (hω'η : ω' < η)
    (hst : ∀ n : ℕ, ‖𝐒₀ 1 ^ n * (1 - P₀)‖ ≤ M * Real.exp (ω' * n))
    (hηκ : η < κ) (hun : ∀ n : ℕ, ‖W₀ ^ n * P₀‖ ≤ M' * Real.exp (-(κ * n))) :
    Nonempty (ProfileDichotomy b c hk2 hk3) := by
  have hη : 0 < η := by linarith
  have hι : Function.Injective 𝛊₃ := vectorLowerOrderCLM_injective _ isOpen_univ
  have hιS : ∀ t x, 𝛊₃ (𝐒₃ t x) = 𝐒₀ t (𝛊₃ x) := vectorLowerOrderCLM_profileSemigroup 0 3 hk3 hk0
  obtain ⟨G, hιG⟩ : ∃ G : VectorH 3 0 →L[ℝ] VectorH 3 3, ∀ y, 𝛊₃ (G y) = 𝐒₀ 1 y := by
    obtain ⟨Cg, ωg, -, hsm⟩ := profileSemigroup_exists_smoothing 0 3 hk3 hk0
    obtain ⟨G, hG, -⟩ := hsm 1 one_pos
    exact ⟨G, fun y ↦ congrArg (fun A ↦ A y) hG⟩
  have hιgain : ∀ r, 0 < r → ∀ y, 𝛊₃ (profileGain 2 b c hk2 r y) = 𝐒₀ r.toNNReal (𝛊₂ y) := by
    intro r hr y
    have h := congrArg (fun A ↦ A y)
      (vectorLower_comp_profileGain hk2 (t := r.toNNReal) (Real.toNNReal_pos.mpr hr))
    simp only [ContinuousLinearMap.comp_apply, Real.coe_toNNReal _ hr.le] at h
    rw [← vectorLowerOrderCLM_trans_apply (Nat.zero_le 2) (Nat.le_succ 2), ← vectorLower, h]
    exact vectorLowerOrderCLM_profileSemigroup 0 2 hk2 hk0 _ y
  obtain ⟨hP, hTW, hPW, hcP, hcW, hfin, ⟨M₃, -, hst₃⟩, M₃', hun₃⟩ :=
    StronglyContinuousSemigroup.lift_splitting (T := 𝐒₃) hι hιS hιG hP₀ hfin₀ hcP₀ hcW₀
      hTW₀ hPW₀ hM hω'0 hst hun
  have hιP : ∀ y, 𝛊₃ (G (W₀ y)) = P₀ y :=
    StronglyContinuousSemigroup.lower_liftProjection_apply hιG hTW₀
  have hιe : 𝛊₃ (Real.exp (-μ) • G u) = u := by
    rw [map_smul, hιG, hSu 1, NNReal.coe_one, mul_one, smul_smul, ← Real.exp_add,
      neg_add_cancel, Real.exp_zero, one_smul]
  refine nonempty_profileDichotomy_of_kernels hk2 hk3 (Q := G.comp (W₀.comp (𝛊₂.comp
    (leraySobolev 3 2)))) (e := Real.exp (-μ) • G u) hη16 hημ hω'0 hω'η hηκ hP hTW hPW hcP
    hcW hfin hst₃ hun₃ (fun x ↦ hι ?_) (fun x ↦ hι ?_) (fun r hr x ↦ hι ?_)
    (fun h ↦ hu0 (by rw [← hιe, h, map_zero])) (hι ?_) (fun t ↦ hι ?_)
  · change 𝛊₃ (leraySobolev 3 3 (G (W₀ (𝛊₃ x)))) = 𝛊₃ (G (W₀ (𝛊₃ x)))
    rw [vectorLowerOrderCLM_leraySobolev, hιP, hL₀]
  · change 𝛊₃ (G (W₀ (𝛊₃ (G (W₀ (𝛊₂ (leraySobolev 3 2 x))))))) =
      𝛊₃ (G (W₀ (𝛊₂ (leraySobolev 3 2 x))))
    simp only [hιP]
    exact congrArg (fun A ↦ A (𝛊₂ (leraySobolev 3 2 x))) hP₀.eq
  · change 𝛊₃ (𝐒₃ r.toNNReal (G (W₀ (𝛊₂ (leraySobolev 3 2 x))))) =
      𝛊₃ (G (W₀ (𝛊₃ (profileGain 2 b c hk2 r (leraySobolev 3 2 x)))))
    rw [hιS, hιP, hιP, hιgain r hr]
    exact congrArg (fun A ↦ A (𝛊₂ (leraySobolev 3 2 x))) (hcP₀ _).eq
  · change 𝛊₃ (G (W₀ (𝛊₃ (Real.exp (-μ) • G u)))) = _
    rw [hιP, hιe, hPu]
  · rw [hιS, hιe, hSu, map_smul, hιe]

end Lift

end NavierStokes.Selfsimilar

namespace NavierStokes.Nonuniqueness.UnstableProfile

open NavierStokes.Selfsimilar

variable (D : UnstableProfile)

/-- The profile evolution of an unstable profile has an exponential dichotomy from `H²` to
`H³`. -/
theorem nonempty_profileDichotomy :
    Nonempty (ProfileDichotomy D.transportCoefficients D.stretchingCoefficients
      (D.profileCoefficientBounds 2) (D.profileCoefficientBounds 3)) := by
  obtain ⟨μ, η, u, P₀, W₀, hη, hη16, hημ, hu0, hSu, hPu, hP₀, hfin₀, hcP₀, hcW₀, hTW₀, hPW₀,
    hL₀, ⟨M, ω', hM, hω'0, hω'η, hst⟩, M', κ, -, hηκ, hun⟩ := D.exists_profileSemigroup_splitting
  exact nonempty_profileDichotomy_of_splitting (D.profileCoefficientBounds 0)
    (D.profileCoefficientBounds 2) (D.profileCoefficientBounds 3) hη16 hημ hu0 hSu hPu hP₀
    hfin₀ hcP₀ hcW₀ hTW₀ hPW₀ hL₀ hM hω'0 hω'η hst hηκ hun

/-- A chosen exponential dichotomy of the profile evolution from `H²` to `H³`. -/
def dichotomy : ProfileDichotomy D.transportCoefficients D.stretchingCoefficients
    (D.profileCoefficientBounds 2) (D.profileCoefficientBounds 3) :=
  Classical.choice D.nonempty_profileDichotomy

end NavierStokes.Nonuniqueness.UnstableProfile

namespace NavierStokes.Selfsimilar

open NavierStokes.Nonuniqueness

/-- **Exponential dichotomy of the profile linearization.** For an unstable profile there are a
weight `0 < η ≤ 1/16`, a stable rate `ω < 2η`, an unstable rate `κ ≥ η`, a projection `P` on
`H³` and an eigenvector `e` fixed by `P`, such that the stable kernel `Ks r = (1 - P) S(r) Π`
from `H²` to `H³` acts jointly continuously at positive times, is annihilated by `P` and has the
bound `Ms r^{-1/2} e^{ω r}`, and the unstable kernel `Ku`, continuous in operator norm, equals
`P S(r) Π` at `-r < 0`, is shifted by the evolution, `S(t) Ku(r) = Ku(r - t)`, and has the bound
`Mu e^{-κ r}` at `r ≥ 0`. The projection is idempotent with finite-dimensional range and fixes
`Ku`. The eigenvector satisfies `S(t) e = e^{μt} e` with `μ > η`, and the
homogeneous unstable paths `b s` decode to `τ ↦ e^{μτ} s e` with the weight `η`. Here `S(r)`
is the gain `profileGain 2` from `H²` to `H³`, `S(t)` on `H³` is `profileSemigroup 3`, and `Π`
is the Leray projection on `H²`. -/
theorem exists_dichotomy (D : UnstableProfile) :
    ∃ (η ω κ Ms Mu : ℝ) (Ks Ku : ℝ → VectorH 3 2 →L[ℝ] VectorH 3 3)
      (P : VectorH 3 3 →L[ℝ] VectorH 3 3) (e : VectorH 3 3),
      0 < η ∧ η ≤ 1 / 16 ∧ ω < 2 * η ∧ η ≤ κ ∧ 0 ≤ Ms ∧ 0 ≤ Mu ∧
      ContinuousOn (fun p : ℝ × VectorH 3 2 ↦ Ks p.1 p.2) (Ioi 0 ×ˢ univ) ∧
      Continuous Ku ∧
      (∀ r, 0 < r → ‖Ks r‖ ≤ Ms * r ^ (-(1 / 2 : ℝ)) * Real.exp (ω * r)) ∧
      (∀ r, 0 ≤ r → ‖Ku r‖ ≤ Mu * Real.exp (-(κ * r))) ∧
      (∀ r, 0 < r → ∀ x, P (Ks r x) = 0) ∧
      e ≠ 0 ∧ P e = e ∧ IsIdempotentElem P ∧
      FiniteDimensional ℝ (LinearMap.range P.toLinearMap) ∧ (∀ r x, P (Ku r x) = Ku r x) ∧
      (∀ r x, Ks r x = profileGain 2 D.transportCoefficients D.stretchingCoefficients
          (D.profileCoefficientBounds 2) r (leraySobolev 3 2 x) -
        P (profileGain 2 D.transportCoefficients D.stretchingCoefficients
          (D.profileCoefficientBounds 2) r (leraySobolev 3 2 x))) ∧
      (∀ r, 0 < r → ∀ x, Ku (-r) x = P (profileGain 2 D.transportCoefficients
        D.stretchingCoefficients (D.profileCoefficientBounds 2) r (leraySobolev 3 2 x))) ∧
      (∀ (t : ℝ≥0) r x, profileSemigroup 3 D.transportCoefficients D.stretchingCoefficients
        (D.profileCoefficientBounds 3) t (Ku r x) = Ku (r - t) x) ∧
      ∃ μ : ℝ, η < μ ∧
        (∀ t : ℝ≥0, profileSemigroup 3 D.transportCoefficients D.stretchingCoefficients
          (D.profileCoefficientBounds 3) t e = Real.exp (μ * t) • e) ∧
        ∃ b : ℝ → (Iic (0 : ℝ) →ᵇ VectorH 3 3), ∀ s : ℝ,
          ∀ τ, τ ≤ 0 → ancientLift η (b s) τ = Real.exp (μ * τ) • (s • e) := by
  obtain ⟨d⟩ := D.nonempty_profileDichotomy
  exact ⟨d.η, d.ω, d.κ, d.Ms, d.Mu, d.Ks, d.Ku, d.P, d.e, d.η_pos, d.η_le, d.ω_lt, d.η_le_κ,
    d.Ms_nonneg, d.Mu_nonneg, d.continuousOn_Ks, d.continuous_Ku, d.norm_Ks_le, d.norm_Ku_le,
    d.P_Ks, d.e_ne_zero, d.P_e, d.isIdempotentElem_P, d.finiteDimensional_range_P, d.P_Ku,
    d.Ks_apply, d.Ku_neg, d.semigroup_Ku, d.μ, d.η_lt_μ, d.semigroup_e, d.b, d.ancientLift_b⟩

end NavierStokes.Selfsimilar
