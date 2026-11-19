/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Control.InitialValue
public import PDE.Hyperbolic.HamiltonJacobi.Control.TimeTranslation
public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.FiniteHorizon.TimeReversal

/-!
# The control value with prescribed terminal time

The value at `(x, t)` is the infimum of the costs of measurable controls on `[t, T]`.
Translating the controls identifies it with `controlInitialValue` at time `T - t`,
so the terminal touching tests have upper inequality `≥ 0` and lower inequality `≤ 0`.

`controlTerminalValue_solves_terminal_problem` is Theorem 2 of Evans, §10.3.3, for the
terminal-value problem (22), with the touching inequalities (24)-(25) of his Remark (ii); the
time reflection is his Remark (iii). Evans's Hamiltonian (23) is a minimum over a compact
control set. Ours is an infimum, and the control space need not be compact. Bounded Lipschitz
data give existence and uniqueness on each finite slab. On a compact control space with
dynamics and cost jointly continuous, the infimum is attained
(`exists_controlHamiltonian_minimizer`).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §10.3.3, Theorem 2 and Remarks (i)-(iii), equations
  (22)-(25).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace HamiltonJacobi

open Function Set TopologicalSpace
open scoped ContDiff Gradient InnerProductSpace Topology

section Value

variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [TopologicalSpace A] [PseudoMetrizableSpace A] [MeasurableSpace A] [BorelSpace A]

variable (f : E → A → E) (hf : Continuous (fun p : E × A ↦ f p.1 p.2))
  (K M : NNReal) (hK : ∀ v, LipschitzWith K (fun x ↦ f x v))
  (hM : ∀ x v, ‖f x v‖ ≤ (M : ℝ)) (h : E → A → ℝ) (g : E → ℝ)

local notation "V" => controlValue f hf K M hK hM

/-- The control value with terminal time `T`: at `(x, t)`, the infimum of costs over
controls on `[min t T, T]`. For `t ≥ T` the horizon has length zero. -/
def controlTerminalValue (T : ℝ) (z : E × ℝ) : ℝ :=
  V h g (min_le_right z.2 T) z.1

/-- For `t ≤ T` the terminal value at `(x, t)` is the control value on `[t, T]`. -/
theorem controlTerminalValue_eq_controlValue {t T : ℝ} (ht : t ≤ T) (x : E) :
    controlTerminalValue f hf K M hK hM h g T (x, t) = V h g ht x := by
  simp only [controlTerminalValue, min_eq_left ht]

/-- Translating time by `-T` identifies the value on `[t, T]` with the value on
`[t - T, 0]`. -/
theorem control_value_eq_zero_terminal {t T : ℝ} (ht : t ≤ T) (x : E) :
    V h g ht x = V h g (a := t - T) (b := 0) (sub_nonpos.mpr ht) x := by
  simpa only [sub_eq_add_neg, add_neg_cancel] using
    (control_value_translate f hf K M hK hM h g ht (-T) x).symm

/-- The terminal value is the forward control value composed with the reflection
`t ↦ T - t` of the time coordinate. -/
theorem controlTerminalValue_eq_initialValue (T : ℝ) (z : E × ℝ) :
    controlTerminalValue f hf K M hK hM h g T z =
      controlInitialValue f hf K M hK hM h g (timeReflection T z) := by
  have ht : min z.2 T - T = -max (T - z.2) 0 := by
    rcases le_total z.2 T with hz | hz <;> simp [hz]
  change V h g (min_le_right z.2 T) z.1 = V h g (a := -max (T - z.2) 0) (b := 0) _ z.1
  simpa only [ht] using control_value_eq_zero_terminal f hf K M hK hM h g (min_le_right z.2 T) z.1

/-- At time `T` the value equals the terminal cost. -/
@[simp]
theorem controlTerminalValue_terminal [Nonempty A] (T : ℝ) (x : E) :
    controlTerminalValue f hf K M hK hM h g T (x, T) = g x := by
  simp only [controlTerminalValue, min_self, control_value_zero]

end Value

section Minimum

variable {E A : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace A] [CompactSpace A] [Nonempty A]

/-- On a nonempty compact control space, with jointly continuous dynamics and cost, the
infimum `-controlHamiltonian f h p x` of `⟪p, f x a⟫ + h x a` over controls `a` is
attained. -/
theorem exists_controlHamiltonian_minimizer (f : E → A → E) (h : E → A → ℝ)
    (hf : Continuous (fun q : E × A ↦ f q.1 q.2)) (hh : Continuous (fun q : E × A ↦ h q.1 q.2))
    (p x : E) :
    ∃ a, -controlHamiltonian f h p x = ⟪p, f x a⟫_ℝ + h x a ∧
      ∀ b, ⟪p, f x a⟫_ℝ + h x a ≤ ⟪p, f x b⟫_ℝ + h x b := by
  let q : A → ℝ := fun a ↦ ⟪p, f x a⟫_ℝ + h x a
  have hq : Continuous q :=
    (continuous_const.inner (hf.comp (continuous_const.prodMk continuous_id))).add
      (hh.comp (continuous_const.prodMk continuous_id))
  obtain ⟨a, _, ha⟩ := isCompact_univ.exists_isMinOn univ_nonempty hq.continuousOn
  have hlower : ∀ b, q a ≤ q b := fun b ↦ ha (mem_univ b)
  exact ⟨a, (neg_neg _).trans (IsLeast.csInf_eq ⟨mem_range_self a, forall_mem_range.2 hlower⟩),
    hlower⟩

end Minimum

section TerminalProblem

variable {E A : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace A] [PseudoMetrizableSpace A] [MeasurableSpace A] [BorelSpace A]
  [Nonempty A]

/-- The control value is the unique bounded, uniformly continuous viscosity solution on
`[0, T]` of the terminal problem with terminal cost `g` and Hamiltonian
`-controlHamiltonian f h`, the infimum over controls. The value satisfies the touching
inequalities for every local `C¹` test. A competitor `v` is assumed to satisfy them only
for tests smooth on the open slab, and is compared with the value on the closed slab. -/
theorem controlTerminalValue_solves_terminal_problem (f : E → A → E)
    (hf : Continuous (fun p : E × A ↦ f p.1 p.2)) (K M : NNReal)
    (hK : ∀ v, LipschitzWith K (fun x ↦ f x v)) (hM : ∀ x v, ‖f x v‖ ≤ (M : ℝ)) (h : E → A → ℝ)
    (hh : Measurable (fun p : E × A ↦ h p.1 p.2)) (C L : NNReal) (hC : ∀ x v, |h x v| ≤ (C : ℝ))
    (hL : ∀ v, LipschitzWith L (fun x ↦ h x v)) (g : E → ℝ) (D G : NNReal)
    (hg : ∀ x, |g x| ≤ (D : ℝ)) (hG : LipschitzWith G g) (T : ℝ) (hT : 0 < T) :
    let U := controlTerminalValue f hf K M hK hM h g T
    (Bornology.IsBounded (U '' closedTimeSlab T) ∧
      UniformContinuousOn U (closedTimeSlab T)) ∧
    (∀ x, U (x, T) = g x) ∧
    (∀ z ∈ openTimeSlab T, ∀ φ : E × ℝ → ℝ, ContDiffAt ℝ 1 φ z →
      IsLocalMaxOn (fun y ↦ U y - φ y) (openTimeSlab T) z →
        0 ≤ fderiv ℝ φ z (0, 1) -
          controlHamiltonian f h (∇ (fun x ↦ φ (x, z.2)) z.1) z.1) ∧
    (∀ z ∈ openTimeSlab T, ∀ φ : E × ℝ → ℝ, ContDiffAt ℝ 1 φ z →
      IsLocalMinOn (fun y ↦ U y - φ y) (openTimeSlab T) z →
        fderiv ℝ φ z (0, 1) -
          controlHamiltonian f h (∇ (fun x ↦ φ (x, z.2)) z.1) z.1 ≤ 0) ∧
    (∀ v : E × ℝ → ℝ,
      (Bornology.IsBounded (v '' closedTimeSlab T) ∧
        UniformContinuousOn v (closedTimeSlab T)) →
      (∀ x, v (x, T) = g x) →
      (∀ z ∈ openTimeSlab T, ∀ φ : E × ℝ → ℝ,
        ContDiffOn ℝ ∞ φ (openTimeSlab T) →
        IsLocalMaxOn (fun y ↦ v y - φ y) (openTimeSlab T) z →
          0 ≤ fderiv ℝ φ z (0, 1) -
            controlHamiltonian f h (∇ (fun x ↦ φ (x, z.2)) z.1) z.1) →
      (∀ z ∈ openTimeSlab T, ∀ φ : E × ℝ → ℝ,
        ContDiffOn ℝ ∞ φ (openTimeSlab T) →
        IsLocalMinOn (fun y ↦ v y - φ y) (openTimeSlab T) z →
          fderiv ℝ φ z (0, 1) -
            controlHamiltonian f h (∇ (fun x ↦ φ (x, z.2)) z.1) z.1 ≤ 0) →
      EqOn v U (closedTimeSlab T)) := by
  let U := controlTerminalValue f hf K M hK hM h g T
  let W := controlInitialValue f hf K M hK hM h g
  have hUW : U = W ∘ timeReflection T :=
    funext (controlTerminalValue_eq_initialValue f hf K M hK hM h g T)
  have hWU : U ∘ timeReflection T = W := by
    rw [hUW]
    ext z
    simp only [Function.comp_apply, timeReflection_timeReflection]
  have hW := isViscosityInitialSolution_controlInitialValue f hf K M hK hM
    h hh C L hC hL g D G hg hG
  have hub : Bornology.IsBounded (U '' closedTimeSlab T) ∧
      UniformContinuousOn U (closedTimeSlab T) := by
    rw [hUW]
    exact bounded_uniformContinuousOn_timeReflection (hW.1 T hT)
  have hsub : IsSpatialViscositySubsolution (controlHamiltonian f h)
      (openTimeSlab T) W := ⟨isOpen_openTimeSlab T, fun z hz φ hφ hcontact ↦ hW.2.1.1.2 z hz.1 φ hφ
      ((hcontact.isLocalMax ((isOpen_openTimeSlab T).mem_nhds hz)).isLocalMaxOn _)⟩
  have hsuper : IsSpatialViscositySupersolution (controlHamiltonian f h)
      (openTimeSlab T) W := ⟨isOpen_openTimeSlab T, fun z hz φ hφ hcontact ↦ hW.2.1.2.2 z hz.1 φ hφ
      ((hcontact.isLocalMin ((isOpen_openTimeSlab T).mem_nhds hz)).isLocalMinOn _)⟩
  have huupper := (isSpatialViscositySubsolution_timeReflection_iff
    (fun p x ↦ -controlHamiltonian f h p x) T U).mp
      (by simpa only [neg_neg, hWU] using hsub)
  have hulower := (isSpatialViscositySupersolution_timeReflection_iff
    (fun p x ↦ -controlHamiltonian f h p x) T U).mp
      (by simpa only [neg_neg, hWU] using hsuper)
  refine ⟨hub, controlTerminalValue_terminal f hf K M hK hM h g T,
    by simpa only [sub_eq_add_neg] using huupper, by simpa only [sub_eq_add_neg] using hulower,
    fun v hvb hvterminal hvupper hvlower ↦ ?_⟩
  apply eqOn_closedTimeSlab_of_terminal_smooth_tests_of_lipschitz
    (H := fun p x ↦ -controlHamiltonian f h p x) (Cp := M) (Cx := K + L)
    (fun x ↦ (lipschitzWith_controlHamiltonian f h M C hM hC x).neg) (fun p x y ↦ ?_) hvb hub
    (by simpa only [sub_eq_add_neg] using hvupper)
    (by simpa only [sub_eq_add_neg] using hvlower) (fun z hz φ hφ ↦ huupper z hz φ
      ((hφ.contDiffAt ((isOpen_openTimeSlab T).mem_nhds hz)).of_le (by simp)))
    (fun z hz φ hφ ↦ hulower z hz φ
      ((hφ.contDiffAt ((isOpen_openTimeSlab T).mem_nhds hz)).of_le (by simp)))
    (fun x ↦ (hvterminal x).trans (controlTerminalValue_terminal f hf K M hK hM h g T x).symm) hT
  simpa only [neg_sub_neg, abs_sub_comm] using
    abs_controlHamiltonian_sub_position_le f h M C hM hC K L hK hL p x y

end TerminalProblem

end HamiltonJacobi
