/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.FiniteHorizon.Smooth
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Terminal viscosity tests and reversal of time

Reflection about the midpoint of a finite time interval preserves spatial
gradients and reverses time derivatives. Consequently the terminal equation
`u_t + H(Dₓu,x) = 0` has upper-test inequality `≥ 0` and lower-test inequality
`≤ 0` when its reflected forward equation uses the Hamiltonian `-H`.

The comparison theorem below requires bounded uniform continuity only on the
given closed slab. It imposes no equation or regular continuation beyond it.

These are Remarks (ii) and (iii) after Theorem 2 in Evans, §10.3.3: the terminal-value
inequalities (24)-(25) reverse those of the initial-value problem, and `w(x,t) = u(x,T-t)`
solves `w_t - H(Dw,x) = 0`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §10.3.3, Remarks (ii)-(iii) after Theorem 2,
  (24)-(25).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace HamiltonJacobi

open Filter Function Set
open scoped ContDiff Gradient Topology

variable {E : Type*}

/-- Reverse time in a slab while keeping the spatial point fixed. -/
def timeReflection (T : ℝ) (z : E × ℝ) : E × ℝ :=
  (z.1, T - z.2)

/-- Reflecting twice restores the original spacetime point. -/
@[simp]
theorem timeReflection_timeReflection (T : ℝ) (z : E × ℝ) :
    timeReflection T (timeReflection T z) = z := by
  ext <;> simp only [timeReflection, sub_sub_cancel]

/-- Time reflection preserves the interior of the slab. -/
@[simp]
theorem timeReflection_mem_openTimeSlab (T : ℝ) (z : E × ℝ) :
    timeReflection T z ∈ openTimeSlab T ↔ z ∈ openTimeSlab T := by
  change (0 < T - z.2 ∧ T - z.2 < T) ↔ (0 < z.2 ∧ z.2 < T)
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- Time reflection preserves the closed slab, including both endpoint faces. -/
@[simp]
theorem timeReflection_mem_closedTimeSlab (T : ℝ) (z : E × ℝ) :
    timeReflection T z ∈ closedTimeSlab T ↔ z ∈ closedTimeSlab T := by
  change (0 ≤ T - z.2 ∧ T - z.2 ≤ T) ↔ (0 ≤ z.2 ∧ z.2 ≤ T)
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

variable [NormedAddCommGroup E]

/-- The product metric is unchanged by time reflection. -/
theorem isometry_timeReflection (T : ℝ) : Isometry (timeReflection (E := E) T) := by
  refine Isometry.of_dist_eq fun z w ↦ ?_
  simp only [timeReflection, Prod.dist_eq, Real.dist_eq, sub_sub_sub_cancel_left, abs_sub_comm]

/-- Bounded uniform continuity on a slab is preserved by time reflection. -/
theorem bounded_uniformContinuousOn_timeReflection {T : ℝ} {u : E × ℝ → ℝ}
    (hu : Bornology.IsBounded (u '' closedTimeSlab T) ∧ UniformContinuousOn u (closedTimeSlab T)) :
    Bornology.IsBounded ((u ∘ timeReflection T) '' closedTimeSlab T) ∧
      UniformContinuousOn (u ∘ timeReflection T) (closedTimeSlab T) := by
  refine ⟨hu.1.subset ?_, hu.2.comp
    (isometry_timeReflection T).uniformContinuous.uniformContinuousOn
    (fun z hz ↦ (timeReflection_mem_closedTimeSlab T z).2 hz)⟩
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨timeReflection T z, (timeReflection_mem_closedTimeSlab T z).2 hz, rfl⟩

/-- Time reflection is continuous at the reflected point, with limit the point itself. -/
private theorem tendsto_timeReflection (T : ℝ) (z : E × ℝ) :
    Tendsto (timeReflection T) (𝓝 (timeReflection T z)) (𝓝 z) := by
  have hc := (isometry_timeReflection T).continuous.continuousAt (x := timeReflection T z)
  change Tendsto (timeReflection T) (𝓝 (timeReflection T z))
    (𝓝 (timeReflection T (timeReflection T z))) at hc
  simpa only [timeReflection_timeReflection] using hc

/-- An upper contact reflects to an upper contact at the reflected point. -/
theorem isLocalMaxOn_comp_timeReflection {T : ℝ} {f : E × ℝ → ℝ} {z : E × ℝ}
    (hf : IsLocalMaxOn f (openTimeSlab T) z) (hz : z ∈ openTimeSlab T) :
    IsLocalMaxOn (f ∘ timeReflection T) (openTimeSlab T) (timeReflection T z) := by
  apply IsLocalMax.isLocalMaxOn
  have hn := (tendsto_timeReflection T z).eventually
    (hf.isLocalMax ((isOpen_openTimeSlab T).mem_nhds hz))
  change ∀ᶠ w in 𝓝 (timeReflection T z), f (timeReflection T w) ≤
    f (timeReflection T (timeReflection T z))
  simpa only [timeReflection_timeReflection] using hn

/-- A lower contact reflects to a lower contact at the reflected point. -/
theorem isLocalMinOn_comp_timeReflection {T : ℝ} {f : E × ℝ → ℝ} {z : E × ℝ}
    (hf : IsLocalMinOn f (openTimeSlab T) z) (hz : z ∈ openTimeSlab T) :
    IsLocalMinOn (f ∘ timeReflection T) (openTimeSlab T) (timeReflection T z) := by
  apply IsLocalMin.isLocalMinOn
  have hn := (tendsto_timeReflection T z).eventually
    (hf.isLocalMin ((isOpen_openTimeSlab T).mem_nhds hz))
  change ∀ᶠ w in 𝓝 (timeReflection T z), f (timeReflection T (timeReflection T z)) ≤
    f (timeReflection T w)
  simpa only [timeReflection_timeReflection] using hn

section Differentiation

variable [NormedSpace ℝ E]

/-- Time reflection is smooth in spacetime. -/
theorem contDiff_timeReflection (T : ℝ) : ContDiff ℝ ∞ (timeReflection (E := E) T) :=
  contDiff_fst.prodMk (contDiff_const.sub contDiff_snd)

/-- The derivative of time reflection negates only the time direction. -/
theorem hasFDerivAt_timeReflection (T : ℝ) (z : E × ℝ) :
    HasFDerivAt (timeReflection T)
      ((ContinuousLinearMap.fst ℝ E ℝ).prod (-ContinuousLinearMap.snd ℝ E ℝ)) z :=
  hasFDerivAt_fst.prodMk (hasFDerivAt_snd.const_sub T)

/-- A reflected differentiable test has the opposite time derivative. -/
theorem fderiv_comp_timeReflection_time {T : ℝ} {φ : E × ℝ → ℝ} {z : E × ℝ}
    (hφ : DifferentiableAt ℝ φ (timeReflection T z)) :
    fderiv ℝ (φ ∘ timeReflection T) z (0, 1) = -fderiv ℝ φ (timeReflection T z) (0, 1) := by
  rw [(hφ.hasFDerivAt.comp z (hasFDerivAt_timeReflection T z)).fderiv]
  change fderiv ℝ φ (timeReflection T z) (0, -1) = _
  simpa only [Prod.neg_mk, neg_zero] using map_neg (fderiv ℝ φ (timeReflection T z)) (0, 1)

end Differentiation

variable [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Reflection does not change the spatial slice of a test at the corresponding time. -/
theorem gradient_comp_timeReflection (T : ℝ) (φ : E × ℝ → ℝ) (z : E × ℝ) :
    ∇ (fun x ↦ (φ ∘ timeReflection T) (x, z.2)) z.1 =
      ∇ (fun x ↦ φ (x, (timeReflection T z).2)) (timeReflection T z).1 :=
  rfl

/-- **Transport of touching tests under time reflection.** Let `P` be a class of tests and `K`
a kind of contact, both stable under composition with the reflection of the slab, and let every
test in `P` be differentiable at its contact point. If every test `φ` of `u` satisfies the jet
condition `J (∂ₜφ) (∇ₓφ) x` at its contact points `(x, t)`, then every test of
`u ∘ timeReflection T` satisfies `J (-∂ₜφ) (∇ₓφ) x`: reflection keeps the spatial gradient and
reverses the time derivative. -/
private theorem tests_comp_timeReflection {T : ℝ} {P K : (E × ℝ → ℝ) → E × ℝ → Prop}
    {J : ℝ → E → E → Prop}
    (hP : ∀ φ z, z ∈ openTimeSlab T → P φ z →
      P (φ ∘ timeReflection T) (timeReflection T z) ∧ DifferentiableAt ℝ φ z)
    (hK : ∀ f z, z ∈ openTimeSlab T → K f z → K (f ∘ timeReflection T) (timeReflection T z))
    {u : E × ℝ → ℝ}
    (hu : ∀ z ∈ openTimeSlab T, ∀ φ : E × ℝ → ℝ, P φ z → K (fun y ↦ u y - φ y) z →
      J (fderiv ℝ φ z (0, 1)) (∇ (fun x ↦ φ (x, z.2)) z.1) z.1) :
    ∀ z ∈ openTimeSlab T, ∀ φ : E × ℝ → ℝ, P φ z →
      K (fun y ↦ (u ∘ timeReflection T) y - φ y) z →
      J (-fderiv ℝ φ z (0, 1)) (∇ (fun x ↦ φ (x, z.2)) z.1) z.1 := by
  intro z hz φ hφ hcontact
  obtain ⟨hψ, hd⟩ := hP φ z hz hφ
  have htest : K (fun y ↦ u y - (φ ∘ timeReflection T) y) (timeReflection T z) := by
    simpa only [Function.comp_def, timeReflection_timeReflection] using hK _ z hz hcontact
  have h := hu (timeReflection T z) ((timeReflection_mem_openTimeSlab T z).2 hz)
    (φ ∘ timeReflection T) hψ htest
  have hd' : DifferentiableAt ℝ φ (timeReflection T (timeReflection T z)) := by
    simpa only [timeReflection_timeReflection] using hd
  rw [fderiv_comp_timeReflection_time hd', gradient_comp_timeReflection,
    timeReflection_timeReflection] at h
  exact h

omit [CompleteSpace E] in
/-- Tests that are `C¹` at their contact point are stable under time reflection. -/
private theorem contDiffAt_test_timeReflection {T : ℝ} (φ : E × ℝ → ℝ) (z : E × ℝ)
    (_hz : z ∈ openTimeSlab T) (hφ : ContDiffAt ℝ 1 φ z) :
    ContDiffAt ℝ 1 (φ ∘ timeReflection T) (timeReflection T z) ∧ DifferentiableAt ℝ φ z :=
  ⟨ContDiffAt.comp (timeReflection T z)
      (by simpa only [timeReflection_timeReflection] using hφ)
      ((contDiff_timeReflection T).contDiffAt.of_le (by simp)), hφ.differentiableAt_one⟩

omit [CompleteSpace E] in
/-- Tests that are smooth on the open slab are stable under time reflection. -/
private theorem contDiffOn_test_timeReflection {T : ℝ} (φ : E × ℝ → ℝ) (z : E × ℝ)
    (hz : z ∈ openTimeSlab T) (hφ : ContDiffOn ℝ ∞ φ (openTimeSlab T)) :
    ContDiffOn ℝ ∞ (φ ∘ timeReflection T) (openTimeSlab T) ∧ DifferentiableAt ℝ φ z :=
  ⟨hφ.comp (contDiff_timeReflection T).contDiffOn
      (fun w hw ↦ (timeReflection_mem_openTimeSlab T w).2 hw),
    (hφ.contDiffAt ((isOpen_openTimeSlab T).mem_nhds hz)).differentiableAt (by simp)⟩

/-- Forward subsolution tests are exactly terminal upper tests with the reversed sign. -/
theorem isSpatialViscositySubsolution_timeReflection_iff (H : E → E → ℝ) (T : ℝ) (u : E × ℝ → ℝ) :
    IsSpatialViscositySubsolution (fun p x ↦ -H p x) (openTimeSlab T)
        (u ∘ timeReflection T) ↔
      ∀ z ∈ openTimeSlab T, ∀ φ : E × ℝ → ℝ, ContDiffAt ℝ 1 φ z →
        IsLocalMaxOn (fun y ↦ u y - φ y) (openTimeSlab T) z →
          0 ≤ fderiv ℝ φ z (0, 1) + H (∇ (fun x ↦ φ (x, z.2)) z.1) z.1 := by
  constructor
  · intro hu z hz φ hφ hcontact
    have h := tests_comp_timeReflection (K := fun f z ↦ IsLocalMaxOn f (openTimeSlab T) z)
      (J := fun a p x ↦ a + -H p x ≤ 0) contDiffAt_test_timeReflection
      (fun _ _ hz hf ↦ isLocalMaxOn_comp_timeReflection hf hz) hu.2 z hz φ hφ
      (by simpa only [Function.comp_def, timeReflection_timeReflection] using hcontact)
    linarith only [h]
  · intro hu
    refine ⟨isOpen_openTimeSlab T, fun z hz φ hφ hcontact ↦ ?_⟩
    have h := tests_comp_timeReflection (K := fun f z ↦ IsLocalMaxOn f (openTimeSlab T) z)
      (J := fun a p x ↦ 0 ≤ a + H p x) contDiffAt_test_timeReflection
      (fun _ _ hz hf ↦ isLocalMaxOn_comp_timeReflection hf hz) hu z hz φ hφ hcontact
    linarith only [h]

/-- Forward supersolution tests are exactly terminal lower tests with the reversed sign. -/
theorem isSpatialViscositySupersolution_timeReflection_iff (H : E → E → ℝ) (T : ℝ) (u : E × ℝ → ℝ) :
    IsSpatialViscositySupersolution (fun p x ↦ -H p x) (openTimeSlab T)
        (u ∘ timeReflection T) ↔
      ∀ z ∈ openTimeSlab T, ∀ φ : E × ℝ → ℝ, ContDiffAt ℝ 1 φ z →
        IsLocalMinOn (fun y ↦ u y - φ y) (openTimeSlab T) z →
          fderiv ℝ φ z (0, 1) + H (∇ (fun x ↦ φ (x, z.2)) z.1) z.1 ≤ 0 := by
  constructor
  · intro hu z hz φ hφ hcontact
    have h := tests_comp_timeReflection (K := fun f z ↦ IsLocalMinOn f (openTimeSlab T) z)
      (J := fun a p x ↦ 0 ≤ a + -H p x) contDiffAt_test_timeReflection
      (fun _ _ hz hf ↦ isLocalMinOn_comp_timeReflection hf hz) hu.2 z hz φ hφ
      (by simpa only [Function.comp_def, timeReflection_timeReflection] using hcontact)
    linarith only [h]
  · intro hu
    refine ⟨isOpen_openTimeSlab T, fun z hz φ hφ hcontact ↦ ?_⟩
    have h := tests_comp_timeReflection (K := fun f z ↦ IsLocalMinOn f (openTimeSlab T) z)
      (J := fun a p x ↦ a + H p x ≤ 0) contDiffAt_test_timeReflection
      (fun _ _ hz hf ↦ isLocalMinOn_comp_timeReflection hf hz) hu z hz φ hφ hcontact
    linarith only [h]

/-- Terminal smooth upper tests become forward smooth subsolution tests after reflection.
This transport alone requires no continuity or convexity of the Hamiltonian. -/
theorem smooth_subsolution_tests_timeReflection {H : E → E → ℝ} {T : ℝ} {u : E × ℝ → ℝ}
    (hu : ∀ z ∈ openTimeSlab T, ∀ φ : E × ℝ → ℝ, ContDiffOn ℝ ∞ φ (openTimeSlab T) →
      IsLocalMaxOn (fun y ↦ u y - φ y) (openTimeSlab T) z → 0 ≤
      fderiv ℝ φ z (0, 1) + H (∇ (fun x ↦ φ (x, z.2)) z.1) z.1) :
    ∀ z ∈ openTimeSlab T, ∀ φ : E × ℝ → ℝ, ContDiffOn ℝ ∞ φ (openTimeSlab T) →
      IsLocalMaxOn (fun y ↦ (u ∘ timeReflection T) y - φ y) (openTimeSlab T) z →
      fderiv ℝ φ z (0, 1) - H (∇ (fun x ↦ φ (x, z.2)) z.1) z.1 ≤ 0 := by
  intro z hz φ hφ hcontact
  have h := tests_comp_timeReflection (P := fun φ _ ↦ ContDiffOn ℝ ∞ φ (openTimeSlab T))
    (K := fun f z ↦ IsLocalMaxOn f (openTimeSlab T) z) (J := fun a p x ↦ 0 ≤ a + H p x)
    contDiffOn_test_timeReflection (fun _ _ hz hf ↦ isLocalMaxOn_comp_timeReflection hf hz)
    hu z hz φ hφ hcontact
  linarith only [h]

/-- Terminal smooth lower tests become forward smooth supersolution tests after reflection. -/
theorem smooth_supersolution_tests_timeReflection {H : E → E → ℝ} {T : ℝ} {u : E × ℝ → ℝ}
    (hu : ∀ z ∈ openTimeSlab T, ∀ φ : E × ℝ → ℝ, ContDiffOn ℝ ∞ φ (openTimeSlab T) →
      IsLocalMinOn (fun y ↦ u y - φ y) (openTimeSlab T) z →
      fderiv ℝ φ z (0, 1) + H (∇ (fun x ↦ φ (x, z.2)) z.1) z.1 ≤ 0) :
    ∀ z ∈ openTimeSlab T, ∀ φ : E × ℝ → ℝ, ContDiffOn ℝ ∞ φ (openTimeSlab T) →
      IsLocalMinOn (fun y ↦ (u ∘ timeReflection T) y - φ y) (openTimeSlab T) z → 0 ≤
      fderiv ℝ φ z (0, 1) - H (∇ (fun x ↦ φ (x, z.2)) z.1) z.1 := by
  intro z hz φ hφ hcontact
  have h := tests_comp_timeReflection (P := fun φ _ ↦ ContDiffOn ℝ ∞ φ (openTimeSlab T))
    (K := fun f z ↦ IsLocalMinOn f (openTimeSlab T) z) (J := fun a p x ↦ a + H p x ≤ 0)
    contDiffOn_test_timeReflection (fun _ _ hz hf ↦ isLocalMinOn_comp_timeReflection hf hz)
    hu z hz φ hφ hcontact
  linarith only [h]

/-- Terminal uniqueness in the smooth-test class on a single finite slab.
The candidates need no continuation or viscosity equation outside this slab. -/
theorem eqOn_closedTimeSlab_of_terminal_smooth_tests_of_lipschitz [FiniteDimensional ℝ E]
    {H : E → E → ℝ} {u v : E × ℝ → ℝ} {Cp Cx : NNReal} {T : ℝ}
    (hp : ∀ x, LipschitzWith Cp (fun p ↦ H p x))
    (hx : ∀ p x y, |H p x - H p y| ≤ Cx * ‖x - y‖ * (1 + ‖p‖))
    (hub : Bornology.IsBounded (u '' closedTimeSlab T) ∧ UniformContinuousOn u (closedTimeSlab T))
    (hvb : Bornology.IsBounded (v '' closedTimeSlab T) ∧ UniformContinuousOn v (closedTimeSlab T))
    (huupper : ∀ z ∈ openTimeSlab T, ∀ φ : E × ℝ → ℝ, ContDiffOn ℝ ∞ φ (openTimeSlab T) →
      IsLocalMaxOn (fun y ↦ u y - φ y) (openTimeSlab T) z → 0 ≤
      fderiv ℝ φ z (0, 1) + H (∇ (fun x ↦ φ (x, z.2)) z.1) z.1)
    (hulower : ∀ z ∈ openTimeSlab T, ∀ φ : E × ℝ → ℝ, ContDiffOn ℝ ∞ φ (openTimeSlab T) →
      IsLocalMinOn (fun y ↦ u y - φ y) (openTimeSlab T) z →
      fderiv ℝ φ z (0, 1) + H (∇ (fun x ↦ φ (x, z.2)) z.1) z.1 ≤ 0)
    (hvupper : ∀ z ∈ openTimeSlab T, ∀ φ : E × ℝ → ℝ, ContDiffOn ℝ ∞ φ (openTimeSlab T) →
      IsLocalMaxOn (fun y ↦ v y - φ y) (openTimeSlab T) z → 0 ≤
      fderiv ℝ φ z (0, 1) + H (∇ (fun x ↦ φ (x, z.2)) z.1) z.1)
    (hvlower : ∀ z ∈ openTimeSlab T, ∀ φ : E × ℝ → ℝ, ContDiffOn ℝ ∞ φ (openTimeSlab T) →
      IsLocalMinOn (fun y ↦ v y - φ y) (openTimeSlab T) z →
      fderiv ℝ φ z (0, 1) + H (∇ (fun x ↦ φ (x, z.2)) z.1) z.1 ≤ 0)
    (hterminal : ∀ x, u (x, T) = v (x, T)) (hT : 0 < T) :
    EqOn u v (closedTimeSlab T) := by
  have hp' : ∀ x, LipschitzWith Cp (fun p ↦ -H p x) := fun x ↦ (hp x).neg
  have hx' : ∀ p x y, |-H p x - -H p y| ≤ Cx * ‖x - y‖ * (1 + ‖p‖) := by
    intro p x y
    simpa only [neg_sub_neg, abs_sub_comm] using hx p x y
  have heq := eqOn_closedTimeSlab_of_smooth_tests_of_lipschitz hp' hx'
    (bounded_uniformContinuousOn_timeReflection hub)
    (bounded_uniformContinuousOn_timeReflection hvb)
    (by simpa only [sub_eq_add_neg] using smooth_subsolution_tests_timeReflection huupper)
    (by simpa only [sub_eq_add_neg] using smooth_supersolution_tests_timeReflection hulower)
    (by simpa only [sub_eq_add_neg] using smooth_subsolution_tests_timeReflection hvupper)
    (by simpa only [sub_eq_add_neg] using smooth_supersolution_tests_timeReflection hvlower)
    (fun x ↦ by simpa only [Function.comp_apply, timeReflection, sub_zero] using hterminal x) hT
  intro z hz
  simpa only [Function.comp_apply, timeReflection_timeReflection] using
    heq ((timeReflection_mem_closedTimeSlab T z).2 hz)

end HamiltonJacobi
