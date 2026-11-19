/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Solution.Singularity.FiniteTime.NonlinearHeat.SelfSimilar
import CAS.ExactTactic
import PDE.FDeriv.Calculus

/-!
# Spatially constant nonlinear-heat blow-up

For every `p > 1`, the spatially constant function

`u(x,t) = ((p - 1)(T - t))^(-1/(p - 1))`

solves `uₜ = Δu + uᵖ` on `t < T`. The proof differentiates the real power on its positive
pre-singular domain and verifies `uₜ = uᵖ`; spatial constancy makes the Laplacian vanish.

We also show that the constant similarity profile satisfies the reduced Type I equation and that
its ansatz is the explicit formula, which ties the example to the self-similar theory. The
classical-solution theorem itself is proved directly from the formula.

The PDE statement `isNonnegativePointwiseClassicalSolutionOn_constantBlowUp` and the blow-up
statement `spatialSupNormBlowsUpAt_constantBlowUp` are proved separately; the latter goes through
the spatial norm `spatialSupNorm_constantBlowUp` and the pointwise limit
`tendsto_constantBlowUp_atTop`. The existence theorem at the end combines both for the same
witness.

The scalar ODE `y' = yᵖ` is the blow-up mechanism; Evans, §9.4.1, p. 547, isolates the case
`u̇ = u²` for `u_t - Δu = u²`. The solution here is an exact whole-space solution for every real
`p > 1`.

As a function of time the profile is the solution `odeSolution p u₀` of `u' = uᵖ` from
`u(0) = u₀ > 0`, which blows up at `odeBlowUpTime p u₀ = u₀ ^ (1 - p) / (p - 1)`.
`lt_odeBlowUpTime_and_eqOn` says that this is the exact lifespan: every solution on a closed
interval `[0, T]`, continuous with right derivatives on `[0, T)`, has `T < odeBlowUpTime p u₀`
and equals `odeSolution p u₀` there.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.4.1, p. 547.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace PDE.Solution.Singularity.FiniteTime.NonlinearHeat

open Filter Topology
open PDE.Representations.Similarity

variable {n : ℕ}

/-- The constant profile used by the explicit Type I candidate. -/
noncomputable def constantTypeIProfile
    (p : ℝ) (_y : ℝ^n) : ℝ :=
  (p - 1) ^ (-1 / (p - 1))

/-- The spatially constant blow-up candidate with exponent `p` and time `T`.

The formula is defined for every `t`; it is a classical solution for `p > 1` and `t < T`. -/
noncomputable def constantBlowUp
    (p T : ℝ) (_x : ℝ^n) (t : ℝ) : ℝ :=
  ((p - 1) * (T - t)) ^ (-1 / (p - 1))

/-- The spatially constant blow-up profile is strictly positive before its singular time. -/
theorem constantBlowUp_pos
    {p T t : ℝ} (hp : 1 < p) (x : ℝ^n) (ht : t < T) :
    0 < constantBlowUp p T x t := by
  exact
    Real.rpow_pos_of_pos
      (mul_pos (sub_pos.mpr hp) (sub_pos.mpr ht)) _

/-- For `p > 1`, the constant profile satisfies the reduced Type I elliptic equation. -/
theorem hasZeroTypeIProfileResidual_constantTypeIProfile
    {p : ℝ} (hp : 1 < p) :
    HasZeroTypeIProfileResidual (n := n) p (constantTypeIProfile p) := by
  have hp_sub_pos : 0 < p - 1 :=
    sub_pos.mpr hp
  have hreaction :
      ((p - 1) ^ (-1 / (p - 1))) ^ p =
        (1 / (p - 1)) * (p - 1) ^ (-1 / (p - 1)) := by
    rw [← Real.rpow_mul hp_sub_pos.le]
    calc
      (p - 1) ^ ((-1 / (p - 1)) * p) =
          (p - 1) ^ ((-1 : ℝ) + (-1 / (p - 1))) := by
        congr 1
        field_simp [hp_sub_pos.ne']
        ring
      _ = (p - 1) ^ (-1 : ℝ) * (p - 1) ^ (-1 / (p - 1)) :=
        Real.rpow_add hp_sub_pos _ _
      _ = (1 / (p - 1)) * (p - 1) ^ (-1 / (p - 1)) := by
        rw [Real.rpow_neg_one]
        rw [one_div]
  intro y
  rw [type_i_profile_residual_eq]
  have hconst :
      constantTypeIProfile (n := n) p =
        fun _ : ℝ^n ↦ (p - 1) ^ (-1 / (p - 1)) :=
    rfl
  rw [hconst]
  simp [PDE.laplacian_const, hreaction]

/-- Before the singular time, the Type I ansatz of the constant profile is exactly the explicit
spatially constant blow-up formula. -/
theorem typeIAnsatz_constantTypeIProfile
    {p T : ℝ} (hp : 1 < p) (center x : ℝ^n) {t : ℝ} (ht : t < T) :
    typeIAnsatz p (constantTypeIProfile p) T center x t =
      constantBlowUp p T x t := by
  have hp_sub_nonneg : 0 ≤ p - 1 :=
    (sub_pos.mpr hp).le
  have htime_nonneg : 0 ≤ T - t :=
    (sub_pos.mpr ht).le
  unfold typeIAnsatz backwardSelfSimilarAnsatz scaledProfileAnsatz
  simp only [constantTypeIProfile, backwardPowerScale, smul_eq_mul, constantBlowUp]
  rw [Real.mul_rpow hp_sub_nonneg htime_nonneg]
  ring_nf

/-- Before `T`, the time derivative of the spatially constant field is its `p`th power. The
derivative follows from the real-power chain rule; the exponent identity
`-1/(p-1) - 1 = (-1/(p-1)) * p` then identifies it with the `p`th power. -/
theorem deriv_constantBlowUp
    {p T t : ℝ} (hp : 1 < p) (x : ℝ^n) (ht : t < T) :
    deriv (fun s ↦ constantBlowUp p T x s) t =
      constantBlowUp p T x t ^ p := by
  have hp_sub_pos : 0 < p - 1 := sub_pos.mpr hp
  have hbase_pos : 0 < (p - 1) * (T - t) :=
    mul_pos hp_sub_pos (sub_pos.mpr ht)
  unfold constantBlowUp
  rw [← Real.rpow_mul hbase_pos.le]
  have hexp : (-1 / (p - 1)) * p = -1 / (p - 1) - 1 := by
    cas using [hp_sub_pos.ne']
  rw [hexp]
  have hbase : HasDerivAt (fun s : ℝ ↦ (p - 1) * (T - s)) (-(p - 1)) t := by
    simpa only [Pi.sub_apply, id_eq, zero_sub, mul_neg_one] using
      ((hasDerivAt_const t T).sub (hasDerivAt_id t)).const_mul (p - 1)
  rw [(hbase.rpow_const (p := -1 / (p - 1)) (Or.inl hbase_pos.ne')).deriv]
  cas using [hp_sub_pos.ne']

/-! ## Pointwise equation -/

/-- Before `T`, the explicit field satisfies the nonlinear heat equation pointwise. -/
theorem constantBlowUp_equation
    {p T t : ℝ} (hp : 1 < p) (x : ℝ^n) (ht : t < T) :
    deriv (fun s ↦ constantBlowUp p T x s) t =
      laplacian (fun y ↦ constantBlowUp p T y t) x +
        constantBlowUp p T x t ^ p := by
  rw [deriv_constantBlowUp hp x ht]
  have hslice :
      (fun y : ℝ^n ↦ constantBlowUp p T y t) =
        fun _ ↦ constantBlowUp p T x t :=
    rfl
  rw [hslice, PDE.laplacian_const]
  simp

/-- The spatially constant field is a pointwise classical solution of `uₜ = Δu + uᵖ` on `t < T`.

The positive real-power base gives joint spacetime `C¹` regularity on the open domain. Every
spatial slice is constant and hence globally `C²`; `constantBlowUp_equation` supplies the
pointwise equation. -/
theorem isNonnegativePointwiseClassicalSolutionOn_constantBlowUp
    {p : ℝ} (hp : 1 < p) (T : ℝ) :
    IsNonnegativePointwiseClassicalSolutionOn
      (n := n) p (Set.Iio T) (constantBlowUp p T) where
  exponent_superlinear := hp
  time_domain_open := isOpen_Iio
  spacetime_contDiffOn := by
    unfold constantBlowUp
    apply ContDiffOn.rpow_const_of_ne
    · fun_prop
    · intro xt hxt
      exact (mul_pos (sub_pos.mpr hp) (sub_pos.mpr hxt.2)).ne'
  spatial_slice_contDiff := by
    intro t _ht
    unfold constantBlowUp
    fun_prop
  nonnegative := by
    intro x t ht
    exact (constantBlowUp_pos hp x ht).le
  equation := by
    intro x t ht
    exact constantBlowUp_equation hp x ht

/-- At every spatial point, the solution diverges to `+∞` as `t` approaches `T` from below. -/
theorem tendsto_constantBlowUp_atTop
    {p : ℝ} (hp : 1 < p) (T : ℝ) (x : ℝ^n) :
    Tendsto (fun t ↦ constantBlowUp p T x t)
      (nhdsWithin T (Set.Iio T)) atTop := by
  have hp_sub_pos : 0 < p - 1 := sub_pos.mpr hp
  have hbase_nhds :
      Tendsto (fun t : ℝ ↦ (p - 1) * (T - t))
        (nhdsWithin T (Set.Iio T)) (nhds 0) := by
    have hcontinuous :
        ContinuousAt (fun t : ℝ ↦ (p - 1) * (T - t)) T := by
      fun_prop
    simpa using hcontinuous.tendsto.mono_left nhdsWithin_le_nhds
  have hbase_pos :
      ∀ᶠ t in nhdsWithin T (Set.Iio T), 0 < (p - 1) * (T - t) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact mul_pos hp_sub_pos (sub_pos.mpr ht)
  have hbase :
      Tendsto (fun t : ℝ ↦ (p - 1) * (T - t))
        (nhdsWithin T (Set.Iio T)) (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.2 ⟨hbase_nhds, hbase_pos⟩
  exact
    (tendsto_rpow_neg_nhdsGT_zero
      (div_neg_of_neg_of_pos (by norm_num) hp_sub_pos)).comp hbase

/-- Before `T`, the spatial supremum norm is the scalar blow-up profile itself. -/
theorem spatialSupNorm_constantBlowUp
    {p : ℝ} (hp : 1 < p) (T : ℝ) {t : ℝ} (ht : t < T) :
    spatialSupNorm (constantBlowUp (n := n) p T) t =
      ENNReal.ofReal (((p - 1) * (T - t)) ^ (-1 / (p - 1))) := by
  have hpos :
      0 < ((p - 1) * (T - t)) ^ (-1 / (p - 1)) :=
    constantBlowUp_pos (n := n) hp 0 ht
  simp [spatialSupNorm, constantBlowUp, Real.norm_eq_abs, abs_of_pos hpos]

/-- The spatially constant nonlinear-heat solution blows up in spatial supremum norm at `T`. -/
theorem spatialSupNormBlowsUpAt_constantBlowUp
    {p : ℝ} (hp : 1 < p) (T : ℝ) :
    SpatialSupNormBlowsUpAt (constantBlowUp (n := n) p T) T := by
  apply SpatialSupNormBlowsUpAt.of_sample (fun _ ↦ (0 : ℝ^n))
  · filter_upwards [self_mem_nhdsWithin] with t ht
    rw [spatialSupNorm_constantBlowUp hp T ht]
    exact ENNReal.ofReal_ne_top
  · exact NormBlowsUpAt.of_tendsto_atTop (tendsto_constantBlowUp_atTop hp T 0)

/-- For every superlinear exponent and finite time, there is a nonnegative pointwise classical
solution on the preceding time interval whose spatial supremum norm blows up at that time. -/
theorem exists_isNonnegativePointwiseClassicalSolutionOn_spatialSupNormBlowsUpAt
    {p : ℝ} (hp : 1 < p) (T : ℝ) :
    ∃ u : ℝ^n → ℝ → ℝ,
      IsNonnegativePointwiseClassicalSolutionOn p (Set.Iio T) u ∧
        SpatialSupNormBlowsUpAt u T :=
  ⟨constantBlowUp p T,
    isNonnegativePointwiseClassicalSolutionOn_constantBlowUp hp T,
    spatialSupNormBlowsUpAt_constantBlowUp hp T⟩

/-! ## The ODE `u' = u ^ p`

A solution on `[0, T]` from `u₀ > 0` stays above `u₀`, since its derivative `u₀ ^ p` is positive
wherever it equals `u₀`. Then `u ^ (1 - p)` has right derivative `1 - p`, so it is the affine
function `u₀ ^ (1 - p) - (p - 1) t`. This function stays positive on `[0, T]` because `u` does,
which is `T < odeBlowUpTime p u₀`, and solving for `u` gives the profile. The derivative and the
blow-up of the profile are those of `constantBlowUp`. -/

section ODE

open Set

variable {p u₀ t : ℝ}

/-- The blow-up time `u₀ ^ (1 - p) / (p - 1)` of `u' = u ^ p` from `u(0) = u₀`, for `1 < p` and
`0 < u₀`. -/
noncomputable def odeBlowUpTime (p u₀ : ℝ) : ℝ :=
  u₀ ^ (1 - p) / (p - 1)

/-- The solution `((p - 1) (T - t)) ^ (-1 / (p - 1))` of `u' = u ^ p` from `u(0) = u₀`, for `1 < p`,
`0 < u₀` and `t < T`, where `T = odeBlowUpTime p u₀`. As a function of time it is
`constantBlowUp p T x` at any point `x`. -/
noncomputable def odeSolution (p u₀ t : ℝ) : ℝ :=
  ((p - 1) * (odeBlowUpTime p u₀ - t)) ^ (-1 / (p - 1))

/-- The blow-up time is positive. -/
theorem odeBlowUpTime_pos (hp : 1 < p) (hu₀ : 0 < u₀) : 0 < odeBlowUpTime p u₀ :=
  div_pos (Real.rpow_pos_of_pos hu₀ _) (sub_pos.mpr hp)

/-- The base of the solution is the affine function `u₀ ^ (1 - p) - (p - 1) t`. -/
private theorem sub_one_mul_odeBlowUpTime_sub (hp : 1 < p) (u₀ t : ℝ) :
    (p - 1) * (odeBlowUpTime p u₀ - t) = u₀ ^ (1 - p) - (p - 1) * t := by
  have hp' : p - 1 ≠ 0 := (sub_pos.mpr hp).ne'
  unfold odeBlowUpTime
  cas using [hp']

/-- The exponents `1 - p` and `-1 / (p - 1)` are inverse to each other. -/
private theorem one_sub_mul_neg_one_div (hp : 1 < p) : (1 - p) * (-1 / (p - 1)) = 1 := by
  have hp' : p - 1 ≠ 0 := (sub_pos.mpr hp).ne'
  cas using [hp']

/-- The solution starts at `u₀`. -/
theorem odeSolution_zero (hp : 1 < p) (hu₀ : 0 < u₀) : odeSolution p u₀ 0 = u₀ := by
  rw [odeSolution, sub_one_mul_odeBlowUpTime_sub hp, mul_zero, sub_zero, ← Real.rpow_mul hu₀.le,
    one_sub_mul_neg_one_div hp, Real.rpow_one]

/-- The solution is positive before the blow-up time. -/
theorem odeSolution_pos (hp : 1 < p) (ht : t < odeBlowUpTime p u₀) : 0 < odeSolution p u₀ t :=
  constantBlowUp_pos (n := 0) hp 0 ht

/-- Before the blow-up time the solution solves `u' = u ^ p`. -/
theorem hasDerivAt_odeSolution (hp : 1 < p) (ht : t < odeBlowUpTime p u₀) :
    HasDerivAt (odeSolution p u₀) (odeSolution p u₀ t ^ p) t := by
  have hbase : 0 < (p - 1) * (odeBlowUpTime p u₀ - t) :=
    mul_pos (sub_pos.mpr hp) (sub_pos.mpr ht)
  have hd : DifferentiableAt ℝ (odeSolution p u₀) t :=
    ((differentiableAt_const _).mul ((differentiableAt_const _).sub differentiableAt_id)).rpow_const
      (Or.inl hbase.ne')
  have hderiv : deriv (odeSolution p u₀) t = odeSolution p u₀ t ^ p :=
    deriv_constantBlowUp (n := 0) hp 0 ht
  exact hderiv ▸ hd.hasDerivAt

/-- The solution tends to infinity at the blow-up time. -/
theorem tendsto_odeSolution (hp : 1 < p) :
    Tendsto (odeSolution p u₀) (𝓝[<] odeBlowUpTime p u₀) atTop :=
  tendsto_constantBlowUp_atTop (n := 0) hp _ 0

/-- The solution blows up in norm at the blow-up time. -/
theorem normBlowsUpAt_odeSolution (hp : 1 < p) :
    NormBlowsUpAt (odeSolution p u₀) (odeBlowUpTime p u₀) :=
  NormBlowsUpAt.of_tendsto_atTop (tendsto_odeSolution hp)

/-- A solution of `u' = u ^ p` on `[0, T]` from `u₀ > 0`, with right derivatives on `[0, T)`,
stays above `u₀`. -/
private theorem le_of_hasDerivWithinAt_rpow (hu₀ : 0 < u₀) {T : ℝ} {u : ℝ → ℝ} (h0 : u 0 = u₀)
    (hc : ContinuousOn u (Icc 0 T))
    (hd : ∀ t ∈ Ico 0 T, HasDerivWithinAt u (u t ^ p) (Ici t) t) :
    ∀ t ∈ Icc 0 T, u₀ ≤ u t := by
  intro t ht
  have h := image_le_of_deriv_right_lt_deriv_boundary' (f := fun s ↦ -u s)
    (f' := fun s ↦ -(u s ^ p)) (B := fun _ ↦ -u₀) (B' := fun _ ↦ 0) hc.neg
    (fun s hs ↦ (hd s hs).neg) (by simp [h0]) continuousOn_const
    (fun s _ ↦ hasDerivWithinAt_const s _ _) (fun s _ hs ↦ by
      rw [neg_inj.mp hs]
      exact neg_lt_zero.mpr (Real.rpow_pos_of_pos hu₀ p)) ht
  exact neg_le_neg_iff.mp h

/-- **Exact lifespan of `u' = u ^ p`.** For `p > 1`, a solution of `u' = u ^ p` on `[0, T]` from
`u₀ > 0`, continuous with right derivatives on `[0, T)`, has `T < odeBlowUpTime p u₀` and is the
explicit solution `odeSolution p u₀` on `[0, T]`. -/
theorem lt_odeBlowUpTime_and_eqOn (hp : 1 < p) (hu₀ : 0 < u₀) {T : ℝ} {u : ℝ → ℝ} (hT : 0 ≤ T)
    (h0 : u 0 = u₀) (hc : ContinuousOn u (Icc 0 T))
    (hd : ∀ t ∈ Ico 0 T, HasDerivWithinAt u (u t ^ p) (Ici t) t) :
    T < odeBlowUpTime p u₀ ∧ EqOn u (odeSolution p u₀) (Icc 0 T) := by
  have hpos : ∀ t ∈ Icc 0 T, 0 < u t := fun t ht ↦
    hu₀.trans_le (le_of_hasDerivWithinAt_rpow hu₀ h0 hc hd t ht)
  have haffine : ∀ t ∈ Icc 0 T, u t ^ (1 - p) = u₀ ^ (1 - p) - (p - 1) * t := by
    refine eq_of_has_deriv_right_eq (f := fun t ↦ u t ^ (1 - p))
      (g := fun t ↦ u₀ ^ (1 - p) - (p - 1) * t) (f' := fun _ ↦ 1 - p) (fun t ht ↦ ?_)
      (fun t _ ↦ ?_) (hc.rpow_const fun t ht ↦ Or.inl (hpos t ht).ne') (by fun_prop)
      (by simp [h0])
    · have hut := hpos t (Ico_subset_Icc_self ht)
      have hrpow := (hd t ht).rpow_const (p := 1 - p) (Or.inl hut.ne')
      have hcancel : u t ^ p * (1 - p) * u t ^ (1 - p - 1) = 1 - p := by
        rw [mul_comm (u t ^ p), mul_assoc, ← Real.rpow_add hut]
        norm_num
      convert hrpow using 1
      exact hcancel.symm
    · have hlin := (((hasDerivAt_id t).const_mul (p - 1)).const_sub (u₀ ^ (1 - p))).hasDerivWithinAt
        (s := Ici t)
      convert hlin using 1
      · funext s
        simp
      · ring
  refine ⟨?_, fun t ht ↦ ?_⟩
  · have hT' : (0 : ℝ) < (p - 1) * (odeBlowUpTime p u₀ - T) := by
      rw [sub_one_mul_odeBlowUpTime_sub hp, ← haffine T ⟨hT, le_rfl⟩]
      exact Real.rpow_pos_of_pos (hpos T ⟨hT, le_rfl⟩) _
    exact sub_pos.mp (pos_of_mul_pos_right hT' (sub_pos.mpr hp).le)
  · rw [odeSolution, sub_one_mul_odeBlowUpTime_sub hp, ← haffine t ht,
      ← Real.rpow_mul (hpos t ht).le, one_sub_mul_neg_one_div hp, Real.rpow_one]

/-- For `p = 2` the blow-up time is `u₀⁻¹`. -/
theorem odeBlowUpTime_two (u₀ : ℝ) : odeBlowUpTime 2 u₀ = u₀⁻¹ := by
  norm_num [odeBlowUpTime, Real.rpow_neg_one]

/-- For `p = 2` the solution is `(u₀⁻¹ - t)⁻¹`. -/
theorem odeSolution_two (u₀ t : ℝ) : odeSolution 2 u₀ t = (u₀⁻¹ - t)⁻¹ := by
  norm_num [odeSolution, odeBlowUpTime_two, Real.rpow_neg_one]

end ODE

end PDE.Solution.Singularity.FiniteTime.NonlinearHeat
