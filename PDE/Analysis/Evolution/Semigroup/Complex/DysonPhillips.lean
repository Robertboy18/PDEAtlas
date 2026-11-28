/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import PDE.Analysis.Evolution.Semigroup.Duhamel.Basic
public import PDE.Analysis.Evolution.Semigroup.JointContinuity
public import PDE.Analysis.Evolution.Semigroup.Complex.Generator
public import PDE.Analysis.Evolution.Semigroup.Local

/-!
# The Dyson–Phillips series under the Miyadera condition

Let `A` generate a semigroup `T` and let `B` be an unbounded perturbation, bounded relative to
`A`, with `∫₀^α ‖B T(s) x‖ ds ≤ q ‖x‖` on the domain of `A` for some `α > 0` and `q < 1`. Then
there is a semigroup `S` with `S(t) x = T(t) x + ∫₀ᵗ S(t - s) B T(s) x ds` on the domain of `A`.
This module constructs `S` as a Dyson–Phillips series, from data in which `B` has already been
made bounded, and proves the Duhamel formula for all `t ≥ 0`. The perturbation theorem of
Miyadera and Voigt, `IsComplexLinear.exists_generator_eq_add_of_miyadera`, identifies the
generator of `S` as `A + B`. The construction does not use the complex structure; it is stated
for complex-linear semigroups because that is where the generator is identified. The bound
`∫₀^α ‖B S(s) x‖ ds ≤ q/(1 - q) ‖x‖` for the perturbed semigroup is not proved. The library also
solves forward Volterra equations `v(t) = g(t) + ∫₀ᵗ K(t - s) A(s) v(s) ds` for paths
(`exists_eq_add_forwardDuhamel`), where the perturbation acts before a smoothing kernel; here
it acts after the semigroup, and the solution is a semigroup.

## Main results

* `StronglyContinuousSemigroup.IsMiyadera`: the Miyadera condition for bounded data `C` and
  `R`: `R` has dense range and commutes with the semigroup, and
  `∫₀^α ‖C T(s) w‖ ds ≤ q ‖R w‖` for every `w`.
* `IsStrongFamily`: a uniformly bounded, strongly continuous family of operators on the line.
* `IsMiyadera.isStrongFamily_volterra`: the Volterra operator `volterra` maps a strong family
  with bound `c` to one with bound `c q`.
* `IsMiyadera.eq_zero_of_eq_integral`: a bounded solution of the homogeneous Volterra equation
  on `[0, β]`, `β ≤ α`, vanishes there.
* `IsMiyadera.mul_eq_of_fixedPoint`: a strong family that solves the Duhamel equation on
  `[0, α]` satisfies `S(t + s) = S(t) S(s)` for `t, s ≥ 0` with `t + s ≤ α`.
* `IsComplexLinear.dysonSum` and `dysonSum_apply_of_mem`: the Dyson–Phillips series, and the
  Duhamel equation on `[0, α]`.
* `IsComplexLinear.perturbed`: the perturbed semigroup. It is complex linear
  (`isComplexLinear_perturbed`) and satisfies the Duhamel formula for all `t ≥ 0`
  (`perturbed_duhamel`).

## How it works

The unbounded operator is removed first. With `R = (z₀ - A)⁻¹` and `C = B R`, which is bounded
when `B` is bounded relative to `A`, `B T(s) R w = C T(s) w` for every `w`, and the Miyadera
condition reads `∫₀^α ‖C T(s) w‖ ds ≤ q ‖R w‖`. For a strong family `F` with bound `c`, the
integral `∫₀ᵗ F(t - s) C T(s) w ds` is then at most `c q ‖R w‖`. It is linear in `w` and `R` has
dense range, so it is `V(t) R w` for a unique bounded operator `V(t)` with `‖V(t)‖ ≤ c q`. Times
are clamped to `[0, α]`, so all families are defined, bounded and continuous on the whole line.
The series `S = Σₙ Sₙ`, with `S₀ = T` and `Sₙ₊₁` the Volterra operator of `Sₙ`, converges in
operator norm because `‖Sₙ(t)‖ ≤ M qⁿ`, where `M` bounds `T` on `[0, α]`.

The same bound gives uniqueness: a bounded solution `D` of `D(s) R w = ∫₀ˢ D(s - r) C T(r) w dr`
has bound `c qⁿ` for every `n`. Applied to `D(s) = S(t + s) - S(t) S(s)` it gives the semigroup
law for `t + s ≤ α`. The local semigroup extends to all times (`extendLocal`), and the Duhamel
formula passes from `[0, k α]` to `[0, (k + 1) α]` by the semigroup laws of `S` and `T`.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Graduate Texts in Mathematics 194, Springer, 2000, Chapter III, Section 1 (the Dyson–Phillips
  series) and Section 3 (the perturbation theorem of Miyadera and Voigt).
  <https://doi.org/10.1007/b97696>
-/

@[expose] public noncomputable section

open Filter Topology Set MeasureTheory
open scoped Interval

namespace PDE.Analysis.Evolution

/-- The time `t` moved into the interval `[0, α]`, `max 0 (min t α)`. For `0 ≤ α` it is
Mathlib's `Set.projIcc` (`clampTime_eq_projIcc`); this form needs no proof of `0 ≤ α`, so the
families below are defined for every `α`. -/
def clampTime (α t : ℝ) : ℝ := max 0 (min t α)

/-- The clamp is Mathlib's projection onto the interval `[0, α]`, as a real number. -/
theorem clampTime_eq_projIcc {α : ℝ} (hα : 0 ≤ α) (t : ℝ) :
    clampTime α t = Set.projIcc 0 α hα t := by
  rw [clampTime, Set.coe_projIcc, min_comm]

/-- Clamping the time is continuous. -/
theorem continuous_clampTime (α : ℝ) : Continuous (clampTime α) :=
  continuous_const.max (continuous_id.min continuous_const)

/-- A clamped time is in `[0, α]`. -/
theorem clampTime_mem {α : ℝ} (hα : 0 ≤ α) (t : ℝ) : clampTime α t ∈ Icc 0 α :=
  ⟨le_max_left _ _, max_le hα (min_le_right _ _)⟩

/-- Clamping does not move a time of `[0, α]`. -/
theorem clampTime_of_mem {α t : ℝ} (ht : t ∈ Icc 0 α) : clampTime α t = t := by
  rw [clampTime, min_eq_left ht.2, max_eq_right ht.1]

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- A family of operators on the real line that is bounded by `c` and strongly continuous. -/
structure IsStrongFamily (F : ℝ → X →L[ℂ] X) (c : ℝ) : Prop where
  /-- The uniform bound. -/
  norm_le : ∀ t, ‖F t‖ ≤ c
  /-- Strong continuity. -/
  continuous : ∀ y, Continuous fun t ↦ F t y

/-- The bound of a strong family is nonnegative. -/
theorem IsStrongFamily.nonneg {F : ℝ → X →L[ℂ] X} {c : ℝ} (hF : IsStrongFamily F c) : 0 ≤ c :=
  (norm_nonneg _).trans (hF.norm_le 0)

/-- A strong family acts jointly continuously. -/
theorem IsStrongFamily.continuous_apply {F : ℝ → X →L[ℂ] X} {c : ℝ} (hF : IsStrongFamily F c) :
    Continuous fun p : ℝ × X ↦ F p.1 p.2 :=
  continuous_apply_prod_of_norm_le hF.continuous hF.norm_le

namespace StronglyContinuousSemigroup

variable [CompleteSpace X] (T : StronglyContinuousSemigroup X) (C R : X →L[ℂ] X) (α q : ℝ)

/-- **The Miyadera condition for bounded data.** `R` has dense range and commutes with the
semigroup, and `∫₀^α ‖C T(s) w‖ ds ≤ q ‖R w‖` for every `w`, with `0 ≤ q < 1` and `α > 0`. With
`R = (z₀ - A)⁻¹` and `C = B R` this is `∫₀^α ‖B T(s) x‖ ds ≤ q ‖x‖` on the domain of the
generator `A`. -/
structure IsMiyadera : Prop where
  /-- The length of the time interval is positive. -/
  pos : 0 < α
  /-- The constant is nonnegative. -/
  nonneg : 0 ≤ q
  /-- The constant is less than one. -/
  lt_one : q < 1
  /-- The range of `R` is dense. -/
  denseRange : DenseRange R
  /-- `R` commutes with the semigroup. -/
  commute : ∀ (t : NNReal) (w : X), R (T t w) = T t (R w)
  /-- The integral condition. -/
  integral_le : ∀ w, ∫ s in (0 : ℝ)..α, ‖C (T.realOrbit w s)‖ ≤ q * ‖R w‖

open Classical in
/-- **The Volterra operator** of the Dyson–Phillips series: `volterra F t` is the bounded
operator `V` with `V (R w) = ∫₀^τ F(τ - s) C T(s) w ds` for all `w`, where `τ` is `t` clamped to
`[0, α]`; it is `0` if there is no such operator. -/
def volterra (F : ℝ → X →L[ℂ] X) (t : ℝ) : X →L[ℂ] X :=
  if h : ∃ V : X →L[ℂ] X, ∀ w, V (R w) =
      ∫ s in (0 : ℝ)..clampTime α t, F (clampTime α t - s) (C (T.realOrbit w s)) then
    h.choose
  else 0

variable {T C R α q}

omit [CompleteSpace X] in
/-- The integrand `s ↦ F(t - s) C T(s) w` is continuous for a jointly continuous family `F`. -/
theorem continuous_volterraIntegrand {F : ℝ → X →L[ℂ] X}
    (hF : Continuous fun p : ℝ × X ↦ F p.1 p.2) (t : ℝ) (w : X) :
    Continuous fun s : ℝ ↦ F (t - s) (C (T.realOrbit w s)) :=
  hF.comp ((continuous_const.sub continuous_id).prodMk
    (C.continuous.comp (T.continuous_realOrbit w)))

omit [CompleteSpace X] in
/-- The orbit at a sum of two nonnegative times: `T(a + h) x = T(h) T(a) x`. -/
theorem realOrbit_add (T : StronglyContinuousSemigroup X) (x : X) {a h : ℝ} (ha : 0 ≤ a)
    (hh : 0 ≤ h) : T.realOrbit x (a + h) = T h.toNNReal (T.realOrbit x a) := by
  rw [realOrbit, realOrbit, Real.toNNReal_add ha hh, add_comm, T.map_add_apply]

omit [CompleteSpace X] in
/-- **Splitting a Duhamel integral.** For `t, s ≥ 0`, the integral
`∫₀^{t+s} F(t + s - r) C T(r) w dr` is the sum of `∫₀ˢ F(t + s - r) C T(r) w dr` and
`∫₀ᵗ F(t - r) C T(r) T(s) w dr`. -/
theorem integral_volterraIntegrand_add {F : ℝ → X →L[ℂ] X}
    (hF : Continuous fun p : ℝ × X ↦ F p.1 p.2) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (w : X) :
    ∫ r in (0 : ℝ)..t + s, F (t + s - r) (C (T.realOrbit w r)) =
      (∫ r in (0 : ℝ)..s, F (t + s - r) (C (T.realOrbit w r))) +
        ∫ r in (0 : ℝ)..t, F (t - r) (C (T.realOrbit (T s.toNNReal w) r)) := by
  have hc := continuous_volterraIntegrand (T := T) (C := C) hF (t + s) w
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 s)
    (hc.intervalIntegrable s (t + s))]
  congr 1
  have h1 := intervalIntegral.integral_comp_add_right (a := 0) (b := t)
    (fun r ↦ F (t + s - r) (C (T.realOrbit w r))) s
  rw [zero_add] at h1
  rw [← h1]
  refine intervalIntegral.integral_congr fun r hr ↦ ?_
  rw [uIcc_of_le ht] at hr
  have e1 : t + s - (r + s) = t - r := by ring
  have e2 : T.realOrbit w (r + s) = T.realOrbit (T s.toNNReal w) r := by
    rw [add_comm, T.realOrbit_add w hs hr.1]
    rfl
  simp only [e1, e2]

namespace IsMiyadera

variable (h : T.IsMiyadera C R α q)

include h

omit [CompleteSpace X] in
/-- **The key bound.** For `t` in `[0, α]` and a family with `‖F(t - s)‖ ≤ c` for `0 ≤ s ≤ t`,
`‖∫₀ᵗ F(t - s) C T(s) w ds‖ ≤ c q ‖R w‖`. -/
theorem norm_integral_le {F : ℝ → X →L[ℂ] X} {c t : ℝ} (hc : 0 ≤ c) (ht : t ∈ Icc 0 α)
    (hF : ∀ s ∈ Icc 0 t, ‖F (t - s)‖ ≤ c) (w : X) :
    ‖∫ s in (0 : ℝ)..t, F (t - s) (C (T.realOrbit w s))‖ ≤ c * q * ‖R w‖ := by
  have hcont : Continuous fun s : ℝ ↦ ‖C (T.realOrbit w s)‖ :=
    (C.continuous.comp (T.continuous_realOrbit w)).norm
  calc ‖∫ s in (0 : ℝ)..t, F (t - s) (C (T.realOrbit w s))‖
      ≤ ∫ s in (0 : ℝ)..t, c * ‖C (T.realOrbit w s)‖ :=
        intervalIntegral.norm_integral_le_of_norm_le ht.1 (Eventually.of_forall fun s hs ↦
          ((F (t - s)).le_opNorm _).trans (mul_le_mul_of_nonneg_right
            (hF s ⟨hs.1.le, hs.2⟩) (norm_nonneg _)))
          ((continuous_const.mul hcont).intervalIntegrable _ _)
    _ = c * ∫ s in (0 : ℝ)..t, ‖C (T.realOrbit w s)‖ := intervalIntegral.integral_const_mul _ _
    _ ≤ c * ∫ s in (0 : ℝ)..α, ‖C (T.realOrbit w s)‖ :=
        mul_le_mul_of_nonneg_left (intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
          (Eventually.of_forall fun s ↦ norm_nonneg _) (hcont.intervalIntegrable _ _)) hc
    _ ≤ c * (q * ‖R w‖) := mul_le_mul_of_nonneg_left (h.integral_le w) hc
    _ = c * q * ‖R w‖ := (mul_assoc _ _ _).symm

omit [CompleteSpace X] in
/-- **Uniqueness for the Volterra equation.** A family `D` that is bounded on `[0, β]`,
`β ≤ α`, and satisfies `D(s) R w = ∫₀ˢ D(s - r) C T(r) w dr` there vanishes on `[0, β]`: the
bound `c` of `D` improves to `c qⁿ` for every `n`. -/
theorem eq_zero_of_eq_integral {D : ℝ → X →L[ℂ] X} {β c : ℝ} (hβ : β ≤ α)
    (hD : ∀ s ∈ Icc 0 β, ‖D s‖ ≤ c)
    (heq : ∀ s ∈ Icc 0 β, ∀ w, D s (R w) = ∫ r in (0 : ℝ)..s, D (s - r) (C (T.realOrbit w r)))
    {s : ℝ} (hs : s ∈ Icc 0 β) : D s = 0 := by
  have hc : 0 ≤ c := (norm_nonneg _).trans (hD s hs)
  have key : ∀ n : ℕ, ∀ s ∈ Icc 0 β, ‖D s‖ ≤ c * q ^ n := by
    intro n
    induction n with
    | zero => simpa using hD
    | succ n ih =>
      intro s hs
      have hcn : 0 ≤ c * q ^ n := mul_nonneg hc (pow_nonneg h.nonneg n)
      rw [pow_succ, ← mul_assoc]
      refine norm_le_of_denseRange h.denseRange (mul_nonneg hcn h.nonneg) fun w ↦ ?_
      rw [heq s hs w]
      exact h.norm_integral_le hcn ⟨hs.1, hs.2.trans hβ⟩
        (fun r hr ↦ ih (s - r) ⟨sub_nonneg.mpr hr.2, (sub_le_self s hr.1).trans hs.2⟩) w
  have hlim : Tendsto (fun n : ℕ ↦ c * q ^ n) atTop (𝓝 (c * 0)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one h.nonneg h.lt_one).const_mul c
  rw [mul_zero] at hlim
  exact norm_le_zero_iff.mp (ge_of_tendsto' hlim fun n ↦ key n s hs)

/-- **The Volterra operator on the range of `R`**: for a strong family `F`,
`volterra F t (R w) = ∫₀^τ F(τ - s) C T(s) w ds` with `τ` the time `t` clamped to `[0, α]`. The
right side is linear in `w` and bounded by a multiple of `‖R w‖`, so it factors through `R`. -/
theorem volterra_apply (hT : T.IsComplexLinear) {F : ℝ → X →L[ℂ] X} {c : ℝ}
    (hF : IsStrongFamily F c) (t : ℝ) (w : X) :
    T.volterra C R α F t (R w) =
      ∫ s in (0 : ℝ)..clampTime α t, F (clampTime α t - s) (C (T.realOrbit w s)) := by
  have hint : ∀ w, IntervalIntegrable
      (fun s ↦ F (clampTime α t - s) (C (T.realOrbit w s))) volume 0 (clampTime α t) :=
    fun w ↦ (continuous_volterraIntegrand hF.continuous_apply _ w).intervalIntegrable _ _
  obtain ⟨W, hW⟩ : ∃ W : X →ₗ[ℂ] X, ∀ w, W w =
      ∫ s in (0 : ℝ)..clampTime α t, F (clampTime α t - s) (C (T.realOrbit w s)) :=
    ⟨{ toFun := fun w ↦
          ∫ s in (0 : ℝ)..clampTime α t, F (clampTime α t - s) (C (T.realOrbit w s))
       map_add' := fun w₁ w₂ ↦ by
         rw [← intervalIntegral.integral_add (hint w₁) (hint w₂)]
         refine intervalIntegral.integral_congr fun s _ ↦ ?_
         simp only [realOrbit, _root_.map_add]
       map_smul' := fun a w ↦ by
         rw [RingHom.id_apply, ← intervalIntegral.integral_smul]
         refine intervalIntegral.integral_congr fun s _ ↦ ?_
         simp only [realOrbit, hT.map_smul_complex, _root_.map_smul] }, fun _ ↦ rfl⟩
  have hbound : ∀ w, ‖W w‖ ≤ c * q * ‖R w‖ := fun w ↦ by
    rw [hW]
    exact h.norm_integral_le hF.nonneg (clampTime_mem h.pos.le t) (fun s _ ↦ hF.norm_le _) w
  have hex : ∃ V : X →L[ℂ] X, ∀ w, V (R w) =
      ∫ s in (0 : ℝ)..clampTime α t, F (clampTime α t - s) (C (T.realOrbit w s)) :=
    ⟨W.extendOfNorm R.toLinearMap, fun w ↦
      (LinearMap.extendOfNorm_eq h.denseRange ⟨_, hbound⟩ w).trans (hW w)⟩
  rw [volterra, dite_eq_left hex]
  exact hex.choose_spec w

/-- **The Volterra operator maps strong families to strong families**, with the bound
multiplied by `q`. -/
theorem isStrongFamily_volterra (hT : T.IsComplexLinear) {F : ℝ → X →L[ℂ] X} {c : ℝ}
    (hF : IsStrongFamily F c) : IsStrongFamily (T.volterra C R α F) (c * q) := by
  have hb : ∀ t, ‖T.volterra C R α F t‖ ≤ c * q := fun t ↦
    norm_le_of_denseRange h.denseRange (mul_nonneg hF.nonneg h.nonneg) fun w ↦ by
      rw [h.volterra_apply hT hF]
      exact h.norm_integral_le hF.nonneg (clampTime_mem h.pos.le t) (fun s _ ↦ hF.norm_le _) w
  refine ⟨hb, continuous_family_of_denseRange h.denseRange hb fun w ↦ ?_⟩
  have e : (fun t ↦ T.volterra C R α F t (R w)) = fun t ↦
      ∫ s in (0 : ℝ)..clampTime α t, F (clampTime α t - s) (C (T.realOrbit w s)) :=
    funext fun t ↦ h.volterra_apply hT hF t w
  rw [e]
  have hf : Continuous (Function.uncurry fun (t s : ℝ) ↦
      F (clampTime α t - s) (C (T.realOrbit w s))) :=
    hF.continuous_apply.comp
      ((((continuous_clampTime α).comp continuous_fst).sub continuous_snd).prodMk
        (C.continuous.comp ((T.continuous_realOrbit w).comp continuous_snd)))
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hf
    (continuous_clampTime α)

omit [CompleteSpace X] in
/-- A solution of the Duhamel equation on `[0, α]` is the identity at time zero. -/
theorem eq_one_of_fixedPoint {S : ℝ → X →L[ℂ] X}
    (hfp : ∀ t ∈ Icc 0 α, ∀ w, S t (R w) =
      T.realOrbit (R w) t + ∫ r in (0 : ℝ)..t, S (t - r) (C (T.realOrbit w r))) :
    S 0 = 1 := by
  refine ContinuousLinearMap.ext fun y ↦ ?_
  refine h.denseRange.induction_on (p := fun y ↦ S 0 y = (1 : X →L[ℂ] X) y) y
    (isClosed_eq (S 0).continuous (1 : X →L[ℂ] X).continuous) fun w ↦ ?_
  rw [hfp 0 ⟨le_rfl, h.pos.le⟩ w, intervalIntegral.integral_same, add_zero, realOrbit_zero]
  rfl

/-- **The local semigroup law.** A strong family `S` that solves the Duhamel equation
`S(t) R w = T(t) R w + ∫₀ᵗ S(t - r) C T(r) w dr` on `[0, α]` satisfies `S(t + s) = S(t) S(s)` for
`t, s ≥ 0` with `t + s ≤ α`: the defect `D(s) = S(t + s) - S(t) S(s)` solves the homogeneous
Volterra equation. -/
theorem mul_eq_of_fixedPoint {S : ℝ → X →L[ℂ] X} {N : ℝ} (hS : IsStrongFamily S N)
    (hfp : ∀ t ∈ Icc 0 α, ∀ w, S t (R w) =
      T.realOrbit (R w) t + ∫ r in (0 : ℝ)..t, S (t - r) (C (T.realOrbit w r)))
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hts : t + s ≤ α) : S (t + s) = S t * S s := by
  have hN : 0 ≤ N := hS.nonneg
  refine sub_eq_zero.mp (h.eq_zero_of_eq_integral (D := fun σ ↦ S (t + σ) - S t * S σ)
    (β := α - t) (c := N + N * N) (by linarith) (fun σ _ ↦ (norm_sub_le _ _).trans
      (add_le_add (hS.norm_le _) ((norm_mul_le _ _).trans
        (mul_le_mul (hS.norm_le _) (hS.norm_le _) (norm_nonneg _) hN))))
    (fun σ hσ w ↦ ?_) (s := s) ⟨hs, by linarith⟩)
  have hσ0 : 0 ≤ σ := hσ.1
  have hσα : σ ≤ α - t := hσ.2
  have hjoint := hS.continuous_apply
  -- the Duhamel equation at `t + σ`, split at `σ`
  have h1 := hfp (t + σ) ⟨by linarith, by linarith⟩ w
  rw [integral_volterraIntegrand_add hjoint ht hσ0 w] at h1
  -- the Duhamel equation at `t` for `T(σ) w`
  have h2 := hfp t ⟨ht, by linarith⟩ (T σ.toNNReal w)
  have e1 : T.realOrbit (T σ.toNNReal (R w)) t = T.realOrbit (R w) (t + σ) := by
    rw [add_comm, T.realOrbit_add (R w) hσ0 ht]
    rfl
  rw [h.commute, e1] at h2
  -- the Duhamel equation at `σ`, under `S(t)`
  have hint1 : IntervalIntegrable (fun r ↦ S (σ - r) (C (T.realOrbit w r))) volume 0 σ :=
    (continuous_volterraIntegrand hjoint σ w).intervalIntegrable _ _
  have h3 : S t (S σ (R w)) = S t (T σ.toNNReal (R w)) +
      ∫ r in (0 : ℝ)..σ, S t (S (σ - r) (C (T.realOrbit w r))) := by
    rw [hfp σ ⟨hσ0, by linarith⟩ w, _root_.map_add, (S t).intervalIntegral_comp_comm hint1]
    rfl
  -- the two sides of the Volterra equation for the defect
  have hint2 : IntervalIntegrable (fun r ↦ S (t + σ - r) (C (T.realOrbit w r))) volume 0 σ :=
    (continuous_volterraIntegrand hjoint (t + σ) w).intervalIntegrable _ _
  have hint3 : IntervalIntegrable (fun r ↦ S t (S (σ - r) (C (T.realOrbit w r)))) volume 0 σ :=
    ((S t).continuous.comp (continuous_volterraIntegrand hjoint σ w)).intervalIntegrable _ _
  have hR : ∫ r in (0 : ℝ)..σ, (S (t + (σ - r)) - S t * S (σ - r)) (C (T.realOrbit w r)) =
      (∫ r in (0 : ℝ)..σ, S (t + σ - r) (C (T.realOrbit w r))) -
        ∫ r in (0 : ℝ)..σ, S t (S (σ - r) (C (T.realOrbit w r))) := by
    rw [← intervalIntegral.integral_sub hint2 hint3]
    refine intervalIntegral.integral_congr fun r _ ↦ ?_
    simp only [_root_.sub_apply, mul_apply_eq_comp, add_sub_assoc]
  change S (t + σ) (R w) - S t (S σ (R w)) = _
  rw [hR, h1, h3, h2]
  abel

end IsMiyadera

/-- A bound of the semigroup on `[0, α]`, for a real `α`: `exists_norm_le_on_Icc` of the
library. -/
private theorem exists_norm_le_of_coe_le (T : StronglyContinuousSemigroup X) (α : ℝ) :
    ∃ M : ℝ, ∀ s : NNReal, (s : ℝ) ≤ α → ‖T s‖ ≤ M := by
  obtain ⟨M, -, hM⟩ := T.exists_norm_le_on_Icc α.toNNReal
  exact ⟨M, fun s hs ↦ hM s ⟨zero_le,
    (Real.le_toNNReal_iff_coe_le (s.coe_nonneg.trans hs)).mpr hs⟩⟩

namespace IsComplexLinear

variable (hT : T.IsComplexLinear)

/-- **The terms of the Dyson–Phillips series**: `S₀(t) = T(t)` and `Sₙ₊₁` is the Volterra
operator of `Sₙ`, with times clamped to `[0, α]`. -/
def dysonTerm (hT : T.IsComplexLinear) (C R : X →L[ℂ] X) (α : ℝ) : ℕ → ℝ → X →L[ℂ] X
  | 0 => fun t ↦ hT.clm (clampTime α t).toNNReal
  | n + 1 => T.volterra C R α (dysonTerm hT C R α n)

omit [CompleteSpace X] in
/-- The first term of the Dyson–Phillips series is the semigroup. -/
theorem dysonTerm_zero (C R : X →L[ℂ] X) (α t : ℝ) :
    hT.dysonTerm C R α 0 t = hT.clm (clampTime α t).toNNReal :=
  rfl

omit [CompleteSpace X] in
/-- Each further term of the Dyson–Phillips series is the Volterra operator of the term
before. -/
theorem dysonTerm_succ (C R : X →L[ℂ] X) (α : ℝ) (n : ℕ) :
    hT.dysonTerm C R α (n + 1) = T.volterra C R α (hT.dysonTerm C R α n) :=
  rfl

/-- **The Dyson–Phillips series** `S(t) = Σₙ Sₙ(t)`, with times clamped to `[0, α]`. -/
def dysonSum (hT : T.IsComplexLinear) (C R : X →L[ℂ] X) (α : ℝ) (t : ℝ) : X →L[ℂ] X :=
  ∑' n, hT.dysonTerm C R α n t

section Series

variable {M : ℝ} (h : T.IsMiyadera C R α q) (hM : ∀ s : NNReal, (s : ℝ) ≤ α → ‖T s‖ ≤ M)

include h hM

/-- The `n`-th term of the Dyson–Phillips series is a strong family with bound `M qⁿ`, where
`M` bounds the semigroup on `[0, α]`. -/
theorem isStrongFamily_dysonTerm (n : ℕ) : IsStrongFamily (hT.dysonTerm C R α n) (M * q ^ n) := by
  induction n with
  | zero =>
    refine ⟨fun t ↦ ?_, fun y ↦ ?_⟩
    · rw [pow_zero, mul_one, dysonTerm_zero, hT.norm_clm]
      refine hM _ ?_
      rw [Real.coe_toNNReal _ (clampTime_mem h.pos.le t).1]
      exact (clampTime_mem h.pos.le t).2
    · exact (T.continuous_orbit y).comp (continuous_real_toNNReal.comp (continuous_clampTime α))
  | succ n ih =>
    rw [pow_succ, ← mul_assoc, dysonTerm_succ]
    exact h.isStrongFamily_volterra hT ih

omit hM in
/-- The Dyson–Phillips series converges in operator norm at every time. -/
theorem summable_dysonTerm (t : ℝ) : Summable fun n ↦ hT.dysonTerm C R α n t := by
  obtain ⟨M, hM⟩ := T.exists_norm_le_of_coe_le α
  exact Summable.of_norm_bounded ((summable_geometric_of_lt_one h.nonneg h.lt_one).mul_left M)
    fun n ↦ (hT.isStrongFamily_dysonTerm h hM n).norm_le t

/-- The Dyson–Phillips series is a strong family with bound `M / (1 - q)`. -/
theorem isStrongFamily_dysonSum : IsStrongFamily (hT.dysonSum C R α) (M / (1 - q)) := by
  have hgeo := (hasSum_geometric_of_lt_one h.nonneg h.lt_one).mul_left M
  refine ⟨fun t ↦ ?_, fun y ↦ ?_⟩
  · rw [div_eq_mul_inv]
    exact tsum_of_norm_bounded hgeo fun n ↦ (hT.isStrongFamily_dysonTerm h hM n).norm_le t
  · have e : (fun t ↦ hT.dysonSum C R α t y) = fun t ↦ ∑' n, hT.dysonTerm C R α n t y :=
      funext fun t ↦ (ContinuousLinearMap.apply ℂ X y).map_tsum (hT.summable_dysonTerm h t)
    rw [e]
    exact continuous_tsum (fun n ↦ (hT.isStrongFamily_dysonTerm h hM n).continuous y)
      (hgeo.summable.mul_right ‖y‖) fun n t ↦
        ((hT.dysonTerm C R α n t).le_opNorm y).trans (mul_le_mul_of_nonneg_right
          ((hT.isStrongFamily_dysonTerm h hM n).norm_le t) (norm_nonneg y))

omit hM in
/-- **The Dyson–Phillips series solves the Duhamel equation**, with clamped times:
`S(t) R w = T(τ) R w + ∫₀^τ S(τ - s) C T(s) w ds`. -/
theorem dysonSum_apply (t : ℝ) (w : X) :
    hT.dysonSum C R α t (R w) = hT.clm (clampTime α t).toNNReal (R w) +
      ∫ s in (0 : ℝ)..clampTime α t,
        hT.dysonSum C R α (clampTime α t - s) (C (T.realOrbit w s)) := by
  obtain ⟨M, hM⟩ := T.exists_norm_le_of_coe_le α
  have hterm := hT.isStrongFamily_dysonTerm h hM
  have hgeo : Summable fun n : ℕ ↦ M * q ^ n :=
    (summable_geometric_of_lt_one h.nonneg h.lt_one).mul_left M
  have hsum : ∀ r y, HasSum (fun n ↦ hT.dysonTerm C R α n r y) (hT.dysonSum C R α r y) :=
    fun r y ↦ (ContinuousLinearMap.apply ℂ X y).hasSum (hT.summable_dysonTerm h r).hasSum
  have hint : HasSum (fun n ↦ ∫ s in (0 : ℝ)..clampTime α t,
      hT.dysonTerm C R α n (clampTime α t - s) (C (T.realOrbit w s)))
      (∫ s in (0 : ℝ)..clampTime α t,
        hT.dysonSum C R α (clampTime α t - s) (C (T.realOrbit w s))) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (F := fun n s ↦ hT.dysonTerm C R α n (clampTime α t - s) (C (T.realOrbit w s)))
      (f := fun s ↦ hT.dysonSum C R α (clampTime α t - s) (C (T.realOrbit w s)))
      (fun n s ↦ M * q ^ n * ‖C (T.realOrbit w s)‖)
      (fun n ↦ (continuous_volterraIntegrand (hterm n).continuous_apply _ w).aestronglyMeasurable)
      (fun n ↦ Eventually.of_forall fun s _ ↦ ((hT.dysonTerm C R α n _).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right ((hterm n).norm_le _) (norm_nonneg _)))
      (Eventually.of_forall fun s _ ↦ hgeo.mul_right _) ?_
      (Eventually.of_forall fun s _ ↦ hsum _ _)
    have e : (fun s : ℝ ↦ ∑' n : ℕ, M * q ^ n * ‖C (T.realOrbit w s)‖) =
        fun s ↦ (∑' n : ℕ, M * q ^ n) * ‖C (T.realOrbit w s)‖ := funext fun s ↦ tsum_mul_right
    rw [e]
    exact (continuous_const.mul
      (C.continuous.comp (T.continuous_realOrbit w)).norm).intervalIntegrable _ _
  have e : ∀ n, hT.dysonTerm C R α (n + 1) t (R w) = ∫ s in (0 : ℝ)..clampTime α t,
      hT.dysonTerm C R α n (clampTime α t - s) (C (T.realOrbit w s)) := fun n ↦ by
    rw [dysonTerm_succ, h.volterra_apply hT (hterm n) t w]
  have h1 : HasSum (fun n ↦ hT.dysonTerm C R α (n + 1) t (R w))
      (∫ s in (0 : ℝ)..clampTime α t,
        hT.dysonSum C R α (clampTime α t - s) (C (T.realOrbit w s))) := by
    simp only [e]
    exact hint
  have h2 := (hasSum_nat_add_iff (f := fun n ↦ hT.dysonTerm C R α n t (R w)) 1).mp h1
  rw [Finset.sum_range_one, dysonTerm_zero] at h2
  rw [(hsum t (R w)).unique h2, add_comm]

omit hM in
/-- **The Dyson–Phillips series solves the Duhamel equation on `[0, α]`**:
`S(t) R w = T(t) R w + ∫₀ᵗ S(t - s) C T(s) w ds`. -/
theorem dysonSum_apply_of_mem {t : ℝ} (ht : t ∈ Icc 0 α) (w : X) :
    hT.dysonSum C R α t (R w) =
      T.realOrbit (R w) t + ∫ s in (0 : ℝ)..t, hT.dysonSum C R α (t - s) (C (T.realOrbit w s)) := by
  have h1 := hT.dysonSum_apply h t w
  rw [clampTime_of_mem ht] at h1
  exact h1

omit hM in
/-- The Dyson–Phillips series is the identity at time zero. -/
theorem dysonSum_zero : hT.dysonSum C R α 0 = 1 :=
  h.eq_one_of_fixedPoint fun _ ht w ↦ hT.dysonSum_apply_of_mem h ht w

omit hM in
/-- **The Dyson–Phillips series is a local semigroup**: `S(t + s) = S(t) S(s)` for `t, s ≥ 0`
with `t + s ≤ α`. -/
theorem dysonSum_add {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hts : t + s ≤ α) :
    hT.dysonSum C R α (t + s) = hT.dysonSum C R α t * hT.dysonSum C R α s := by
  obtain ⟨M, hM⟩ := T.exists_norm_le_of_coe_le α
  exact h.mul_eq_of_fixedPoint (hT.isStrongFamily_dysonSum h hM)
    (fun _ ht w ↦ hT.dysonSum_apply_of_mem h ht w) ht hs hts

end Series

/-! ### The perturbed semigroup -/

/-- **The perturbed semigroup** of the Dyson–Phillips series: the extension of the local
semigroup `dysonSum` on `[0, α]` to all times. -/
def perturbed (hT : T.IsComplexLinear) (h : T.IsMiyadera C R α q) :
    StronglyContinuousSemigroup X where
  toMonoidHom :=
    { toFun := fun t ↦ (extendLocal (hT.dysonSum C R α) α t.toAdd).restrictScalars ℝ
      map_one' := by
        change (extendLocal (hT.dysonSum C R α) α 0).restrictScalars ℝ = 1
        rw [extendLocal_zero (hT.dysonSum_zero h)
          (fun s t hs ht hst ↦ hT.dysonSum_add h hs ht hst) h.pos]
        rfl
      map_mul' := fun s t ↦ by
        change (extendLocal (hT.dysonSum C R α) α (s.toAdd + t.toAdd)).restrictScalars ℝ = _
        rw [extendLocal_add (hT.dysonSum_zero h)
          (fun s t hs ht hst ↦ hT.dysonSum_add h hs ht hst) h.pos]
        rfl }
  continuous_toPointwise := by
    obtain ⟨M, hM⟩ := T.exists_norm_le_of_coe_le α
    apply PointwiseConvergenceCLM.continuous_of_continuous_eval
    intro x
    exact continuous_extendLocal_apply (hT.dysonSum_zero h)
      (fun s t hs ht hst ↦ hT.dysonSum_add h hs ht hst) h.pos
      (hT.isStrongFamily_dysonSum h hM).norm_le (hT.isStrongFamily_dysonSum h hM).continuous x

variable (h : T.IsMiyadera C R α q)

/-- The perturbed semigroup at time `t` is the extension of the Dyson–Phillips series. -/
theorem perturbed_apply (t : NNReal) (x : X) :
    hT.perturbed h t x = extendLocal (hT.dysonSum C R α) α t x :=
  rfl

/-- The perturbed semigroup is complex linear. -/
theorem isComplexLinear_perturbed : (hT.perturbed h).IsComplexLinear := fun t x ↦ by
  rw [perturbed_apply, perturbed_apply, _root_.map_smul]

/-- On `[0, α]` the perturbed semigroup is the Dyson–Phillips series. -/
theorem perturbed_apply_of_mem {t : ℝ} (ht : t ∈ Icc 0 α) (x : X) :
    hT.perturbed h t.toNNReal x = hT.dysonSum C R α t x := by
  rw [perturbed_apply, extendLocal_of_le (hT.dysonSum_zero h)
    (fun s t hs ht hst ↦ hT.dysonSum_add h hs ht hst) h.pos
    (by rw [Real.coe_toNNReal t ht.1]; exact ht.2), Real.coe_toNNReal t ht.1]

/-- **The Duhamel formula of the perturbed semigroup on `[0, α]`.** -/
theorem perturbed_duhamel_of_mem {t : ℝ} (ht : t ∈ Icc 0 α) (w : X) :
    (hT.perturbed h).realOrbit (R w) t =
      T.realOrbit (R w) t + (hT.perturbed h).duhamel (fun s ↦ C (T.realOrbit w s)) t := by
  have h1 : (hT.perturbed h).realOrbit (R w) t = hT.dysonSum C R α t (R w) :=
    hT.perturbed_apply_of_mem h ht (R w)
  rw [h1, hT.dysonSum_apply_of_mem h ht w, duhamel]
  congr 1
  refine intervalIntegral.integral_congr fun s hs ↦ ?_
  rw [uIcc_of_le ht.1] at hs
  exact (hT.perturbed_apply_of_mem h
    ⟨sub_nonneg.mpr hs.2, (sub_le_self t hs.1).trans ht.2⟩ _).symm

/-- **The Duhamel formula of the perturbed semigroup**, for all `t ≥ 0`:
`S(t) R w = T(t) R w + ∫₀ᵗ S(t - s) C T(s) w ds`. With `R = (z₀ - A)⁻¹` and `C = B R` this is
`S(t) x = T(t) x + ∫₀ᵗ S(t - s) B T(s) x ds` for `x` in the domain of `A`. The formula holds on
`[0, α]` by construction, and it passes from `[0, k α]` to `[0, (k + 1) α]` by the semigroup laws
of `S` and `T`. -/
theorem perturbed_duhamel {t : ℝ} (ht : 0 ≤ t) (w : X) :
    (hT.perturbed h).realOrbit (R w) t =
      T.realOrbit (R w) t + (hT.perturbed h).duhamel (fun s ↦ C (T.realOrbit w s)) t := by
  have key : ∀ k : ℕ, ∀ t, 0 ≤ t → t ≤ k * α → ∀ w,
      (hT.perturbed h).realOrbit (R w) t =
        T.realOrbit (R w) t + (hT.perturbed h).duhamel (fun s ↦ C (T.realOrbit w s)) t := by
    intro k
    induction k with
    | zero =>
      intro t ht0 ht1 w
      have ht : t = 0 := le_antisymm (by simpa using ht1) ht0
      subst ht
      simp [duhamel]
    | succ k ih =>
      intro t ht0 ht1 w
      by_cases hk : t ≤ k * α
      · exact ih t ht0 hk w
      -- `t = t₂ + t₁` with `t₂ = k α` and `0 ≤ t₁ ≤ α`
      obtain ⟨t₂, ht₂def⟩ : ∃ t₂ : ℝ, t₂ = k * α := ⟨_, rfl⟩
      obtain ⟨t₁, ht₁def⟩ : ∃ t₁ : ℝ, t₁ = t - t₂ := ⟨_, rfl⟩
      have ht₂ : 0 ≤ t₂ := ht₂def ▸ mul_nonneg (Nat.cast_nonneg k) h.pos.le
      have hk1 : ((k + 1 : ℕ) : ℝ) * α = t₂ + α := by
        rw [ht₂def]
        push_cast
        ring
      rw [hk1] at ht1
      rw [← ht₂def] at hk
      have ht₁ : t₁ ∈ Icc 0 α := ⟨by linarith, by linarith⟩
      have hsum : t = t₂ + t₁ := by linarith
      subst hsum
      have hf : Continuous fun s : ℝ ↦ C (T.realOrbit w s) :=
        C.continuous.comp (T.continuous_realOrbit w)
      -- the formula at `t₁` for `T(t₂) w`
      have e2 : T.realOrbit (R w) t₂ = R (T t₂.toNNReal w) := (h.commute _ _).symm
      have e3 : T.realOrbit (R (T t₂.toNNReal w)) t₁ = T.realOrbit (R w) (t₂ + t₁) := by
        rw [← e2, T.realOrbit_add (R w) ht₂ ht₁.1]
        rfl
      have e4 : (hT.perturbed h).duhamel (fun s ↦ C (T.realOrbit (T t₂.toNNReal w) s)) t₁ =
          (hT.perturbed h).duhamel (fun s ↦ C (T.realOrbit w (t₂ + s))) t₁ :=
        duhamel_congr _ ht₁.1 fun s hs ↦ by
          rw [T.realOrbit_add w ht₂ hs.1]
          rfl
      have h4 : hT.perturbed h t₁.toNNReal (T.realOrbit (R w) t₂) =
          T.realOrbit (R w) (t₂ + t₁) +
            (hT.perturbed h).duhamel (fun s ↦ C (T.realOrbit w (t₂ + s))) t₁ := by
        rw [e2, ← e3, ← e4]
        exact hT.perturbed_duhamel_of_mem h ht₁ (T t₂.toNNReal w)
      rw [(hT.perturbed h).duhamel_add hf ht₂ ht₁.1, (hT.perturbed h).realOrbit_add (R w) ht₂ ht₁.1,
        ih t₂ ht₂ ht₂def.le w, _root_.map_add, h4]
      abel
  obtain ⟨k, hk⟩ := exists_nat_ge (t / α)
  exact key k t ht ((div_le_iff₀ h.pos).mp hk) w

end IsComplexLinear

end StronglyContinuousSemigroup

end PDE.Analysis.Evolution
