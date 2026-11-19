/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.LinearUniqueness
public import PDE.Analysis.Evolution.Semigroup.Semilinear.Iteration

/-!
# Energy solutions of semilinear wave equations on the whole space

A semilinear wave equation `u_tt = A(u, u_t)` on `ℝ^n` is given by its acceleration
`A : H¹(ℝ^n) × L²(ℝ^n) → H⁻¹(ℝ^n)`, for instance `A(u, v) = Δu - f(u)` or
`A(u, v) = Δu - f(Du, v, u)`. `IsEnergySolutionOn A x I u` says that the curve `u` of states
`(u, u_t)` is continuous on the time set `I` in the energy space, starts at `x`, and satisfies on
`I` the two integrated equations `u_t = v` in `L²` and `v_t = A(u, v)` in the `H¹` dual. The time
set is `Ici 0` for a forward global solution and `Icc 0 τ` for a solution on a finite interval.

Every statement is for an arbitrary acceleration `A`. The theorems that use the wave semigroup
take three hypotheses which present `A` through an `L²` force:

* `hF`: the force `F : H¹ × L² → L²` is continuous;
* `hA`: `A z = F z - (1 - Δ) z.1` in the `H¹` dual, that is `pivotToDual (F z) - massForm z.1`;
* `hG`: `G` is the vector field `z ↦ (0, F z)` in the coordinates of `EnergyState n`.

For `A(u, v) = Δu - N(u, v)` the force is `F(u, v) = u - N(u, v)`: the mass term of the generator
`linearSemigroup` cancels. The scalar reaction `f(u)`, the first-jet reaction `f(Du, u_t, u)` and
the defocusing energy-space nonlinearities are instances.

## Main definitions

* `IsEnergySolutionOn`: the energy-solution predicate on a time set.
* `forwardExtension`: the constant extension before time zero of a curve continuous on `[0, ∞)`.
* `IsEnergySolutionOn.extension`: the constant extension of a solution on `[0, τ]`.
* `energyTrace`: a continuous energy trajectory on `[0, τ]` in the coordinates of `EnergyState n`.

## Main results

* `IsEnergySolutionOn.hasDerivWithinAt_displacement`,
  `IsEnergySolutionOn.hasDerivWithinAt_velocity`: a forward solution has `u_t = v` in `L²` and
  `v_t = A(u, v)` in the `H¹` dual, with right derivatives at time zero.
* `IsEnergySolutionOn.weakWave_on`, `IsEnergySolutionOn.weak_pde`: the Bochner weak-wave
  formulation on every finite interval, and the equation against spatial and time tests.
* `IsEnergySolutionOn.forwardExtend`: the constant extension before time zero of a forward
  solution is a forward solution, on all of `[0, ∞)`.
* `IsEnergySolutionOn.extend`: the constant extension of a solution on `[0, τ]` is a solution on
  `[0, τ]`.
* `IsEnergySolutionOn.mild_eq`: a solution on `[0, b]` satisfies the Duhamel formula of
  `linearSemigroup` at each time of `[0, b]`.
* `IsEnergySolutionOn.isMildSolutionOn`: the same formula as the mild-solution predicate of the
  vector field `G` on `[0, τ]`.
* `IsEnergySolutionOn.eqOn_Icc`, `IsEnergySolutionOn.eqOn_Ici`: for a locally Lipschitz `G`, two
  solutions with the same data agree.
* `exists_isEnergySolutionOn_Ici`: for a globally Lipschitz `G`, every datum in `H¹ × L²` has a
  forward global solution.

## How it works

Existence is Picard iteration for the Duhamel formula (`exists_global_mild`), followed by the two
integrated identities of the forced linear evolution (`linear_forced_integral`). For uniqueness,
linear weak-wave uniqueness (`linear_integral_identification`) identifies an energy solution with
the Duhamel curve of its own force (`IsEnergySolutionOn.mild_eq`, the one place where the
identification is applied to an `IsEnergySolutionOn`), so it is a mild solution, and mild solutions
of a locally Lipschitz field are unique.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Sobolev InnerProductSpace SobolevSpace.WholeSpaceHilbert Interval Topology ENNReal

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

open SobolevSpace SobolevSpace.GraphSpace
open PDE.Analysis.Evolution Hyperbolic.Variational

variable {n : ℕ}

local notation "C" => WaveEnergySpace.coordinates
  (H := DerivLp n 2 univ) (massForm n) (massForm_coercive n) massForm_symmetric

/-- Globally Lipschitz forcing gives a continuous trajectory solving the mild
equation at every nonnegative time. Values before zero provide a constant
continuous extension, used only to write unrestricted Bochner integrals. -/
theorem exists_global_mild {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (S : StronglyContinuousSemigroup E) {F : C(E, E)} {K : NNReal} (hF : LipschitzWith K F)
    (x : E) :
    ∃ u : C(ℝ, E), u 0 = x ∧
      ∀ t : ℝ, 0 ≤ t → u t = S.realOrbit x t + S.duhamel (fun s ↦ F (u s)) t := by
  have hlife : S.mildLifespan F x = ∞ := by
    refine ENNReal.eq_top_of_forall_nnreal_le fun τ ↦ ?_
    exact ((S.lt_mildLifespan_iff hF.locallyLipschitz x).mpr
      (S.existsUnique_mildSolutionOn_of_lipschitzWith hF x τ).exists).le
  obtain ⟨hcont, heq⟩ := S.maximalMildSolution_global_of_lifespan_eq_top hF.locallyLipschitz x hlife
  let u : C(ℝ, E) := ⟨fun t ↦ S.maximalMildSolution hF.locallyLipschitz x (max t 0),
      hcont.comp_continuous (continuous_id.max continuous_const) (fun t ↦ le_max_right t 0)⟩
  have hu (t : ℝ) (ht : 0 ≤ t) :
      u t = S.maximalMildSolution hF.locallyLipschitz x t := by
    change S.maximalMildSolution hF.locallyLipschitz x (max t 0) = _
    rw [max_eq_left ht]
  refine ⟨u, (hu 0 le_rfl).trans (S.maximalMildSolution_zero _ x), fun t ht ↦ ?_⟩
  rw [hu t ht, heq t ht]
  congr 1
  exact S.duhamel_congr ht fun s hs ↦ congrArg F (hu s hs.1).symm

/-- If `Φ t - Φ 0 = ∫₀ᵗ g (v s) ds` for `t ≥ 0`, with `v` continuous on `[0, ∞)` and `g`
continuous, then `Φ` has derivative `g (v t)` within `[0, ∞)` at every `t ≥ 0`. -/
theorem hasDerivWithinAt_Ici_of_integral_eq {E F : Type*} [TopologicalSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {v : ℝ → E} (hv : ContinuousOn v (Ici 0)) {g : E → F} (hg : Continuous g) {Φ : ℝ → F}
    (h : ∀ t, 0 ≤ t → ∫ s in (0 : ℝ)..t, g (v s) = Φ t - Φ 0) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt Φ (g (v t)) (Ici 0) t := by
  have hw : Continuous (fun s ↦ g (v (max s 0))) :=
    hg.comp (hv.comp_continuous (continuous_id.max continuous_const) fun s ↦ le_max_right s 0)
  have hd := (intervalIntegral.integral_hasDerivAt_right (hw.intervalIntegrable 0 t)
    hw.aestronglyMeasurable.stronglyMeasurableAtFilter hw.continuousAt).add_const (Φ 0)
  rw [max_eq_left ht] at hd
  apply hd.hasDerivWithinAt.congr_of_mem _ ht
  intro s hs
  have hcongr : (∫ r in (0 : ℝ)..s, g (v (max r 0))) = ∫ r in (0 : ℝ)..s, g (v r) := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le hs] at hr
    simp only [max_eq_left hr.1]
  rw [hcongr, h s hs, sub_add_cancel]

/-- Constant extension before the initial time of a curve that is continuous on `[0, ∞)`:
`forwardExtension hu t = u (max t 0)`. -/
def forwardExtension {X : Type*} [TopologicalSpace X] {u : ℝ → X}
    (hu : ContinuousOn u (Ici 0)) : C(ℝ, X) :=
  ⟨fun t ↦ u (max t 0), hu.comp_continuous (continuous_id.max continuous_const)
    (fun t ↦ le_max_right t 0)⟩

/-- Extension leaves all nonnegative-time values unchanged. -/
theorem forwardExtension_apply {X : Type*} [TopologicalSpace X] {u : ℝ → X}
    (hu : ContinuousOn u (Ici 0)) {t : ℝ} (ht : 0 ≤ t) :
    forwardExtension hu t = u t := by
  change u (max t 0) = u t
  rw [max_eq_left ht]

/-- On `[0, t]` the constant extension does not change a time integral. -/
theorem intervalIntegral_comp_forwardExtension {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {u : ℝ → X} (hu : ContinuousOn u (Ici 0))
    (g : X → E) {t : ℝ} (ht : 0 ≤ t) :
    ∫ s in (0 : ℝ)..t, g (forwardExtension hu s) = ∫ s in (0 : ℝ)..t, g (u s) := by
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht] at hs
  simp only [forwardExtension_apply hu hs.1]

/-- A finite-time energy trace in the equivalent Hilbert norm used by the
constructed linear evolution. -/
def energyTrace (u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)) (τ : NNReal) :
    C(Icc (0 : ℝ) (τ : ℝ), EnergyState n) :=
  ⟨fun t ↦ (C).symm (u t),
    (C).symm.continuous.comp (u.continuous.comp continuous_subtype_val)⟩

/-- `IsEnergySolutionOn A x I u`: the curve `u` of states `(u, u_t)` is an energy solution of
`u_tt = A(u, u_t)` on the time set `I` with data `x`. It is continuous on `I` in `H¹ × L²`,
equals `x` at time zero, and satisfies for `t ∈ I` the integrated equations `u_t = v` in `L²`
and `v_t = A(u, v)` in the `H¹` dual. All spatial derivatives are Sobolev weak derivatives. -/
structure IsEnergySolutionOn (A : H¹(ℝ^n) × DerivLp n 2 univ → StrongDual ℝ H¹(ℝ^n))
    (x : H¹(ℝ^n) × DerivLp n 2 univ) (I : Set ℝ)
    (u : ℝ → H¹(ℝ^n) × DerivLp n 2 univ) : Prop where
  /-- Continuity in `H¹ × L²` on the time set. -/
  continuous : ContinuousOn u I
  /-- Both prescribed initial values. -/
  initial : u 0 = x
  /-- The integrated identity `u_t = v` in spatial `L²`. -/
  displacement : ∀ t ∈ I,
    (∫ s in (0 : ℝ)..t, (u s).2) =
      (energyTriple n).inclusion (u t).1 - (energyTriple n).inclusion x.1
  /-- The integrated equation `v_t = A(u, v)` in the `H¹` dual. -/
  velocity : ∀ t ∈ I,
    (∫ s in (0 : ℝ)..t, A (u s)) =
      (energyTriple n).pivotToDual (u t).2 - (energyTriple n).pivotToDual x.2

namespace IsEnergySolutionOn

variable {A : H¹(ℝ^n) × DerivLp n 2 univ → StrongDual ℝ H¹(ℝ^n)}
variable {x : H¹(ℝ^n) × DerivLp n 2 univ} {I J : Set ℝ}
variable {u v : ℝ → H¹(ℝ^n) × DerivLp n 2 univ}

/-- An energy solution on `I` is an energy solution on every smaller time set. -/
theorem mono (h : IsEnergySolutionOn A x I u) (hJ : J ⊆ I) : IsEnergySolutionOn A x J u :=
  ⟨h.continuous.mono hJ, h.initial, fun t ht ↦ h.displacement t (hJ ht),
    fun t ht ↦ h.velocity t (hJ ht)⟩

/-- The constant extension before time zero of a forward energy solution is a forward energy
solution with the same data, for an arbitrary acceleration `A`: `forwardExtension h.continuous` is
continuous on the whole line, agrees with `u` on `[0, ∞)`, and satisfies both integrated equations
at every `t ≥ 0`. -/
theorem forwardExtend (h : IsEnergySolutionOn A x (Ici 0) u) :
    IsEnergySolutionOn A x (Ici 0) (forwardExtension h.continuous) := by
  refine ⟨(forwardExtension h.continuous).continuous.continuousOn,
    (forwardExtension_apply h.continuous le_rfl).trans h.initial, fun t ht ↦ ?_, fun t ht ↦ ?_⟩
  · rw [forwardExtension_apply h.continuous ht]
    exact (intervalIntegral_comp_forwardExtension h.continuous Prod.snd ht).trans
      (h.displacement t ht)
  · rw [forwardExtension_apply h.continuous ht]
    exact (intervalIntegral_comp_forwardExtension h.continuous A ht).trans (h.velocity t ht)

/-! ### Traces and time derivatives of a forward solution -/

/-- Both initial data are attained strongly from the right in `H¹ × L²`. -/
theorem tendsto_initial (h : IsEnergySolutionOn A x (Ici 0) u) :
    Tendsto u (𝓝[≥] (0 : ℝ)) (𝓝 x) := by
  simpa only [ContinuousWithinAt, h.initial] using h.continuous 0 self_mem_Ici

/-- The integrated displacement equation gives its `L²` derivative, including at zero. -/
theorem hasDerivWithinAt_displacement (h : IsEnergySolutionOn A x (Ici 0) u) {t : ℝ}
    (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s ↦ (energyTriple n).inclusion (u s).1) (u t).2 (Ici 0) t :=
  hasDerivWithinAt_Ici_of_integral_eq h.continuous continuous_snd
    (fun s hs ↦ by rw [h.displacement s hs, h.initial]) ht

/-- For a continuous acceleration, the integrated equation gives the derivative of the velocity
in the `H¹` dual, including at zero. -/
theorem hasDerivWithinAt_velocity (h : IsEnergySolutionOn A x (Ici 0) u) (hA : Continuous A)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s ↦ (energyTriple n).pivotToDual (u s).2) (A (u t)) (Ici 0) t :=
  hasDerivWithinAt_Ici_of_integral_eq h.continuous hA
    (fun s hs ↦ by rw [h.velocity s hs, h.initial]) ht

/-- At every positive time the displacement is differentiable in spatial `L²`. -/
theorem hasDerivAt_displacement (h : IsEnergySolutionOn A x (Ici 0) u) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s ↦ (energyTriple n).inclusion (u s).1) (u t).2 t :=
  (h.hasDerivWithinAt_displacement ht.le).hasDerivAt (Ici_mem_nhds ht)

/-- For a continuous acceleration, the velocity is differentiable in the `H¹` dual at every
positive time. -/
theorem hasDerivAt_velocity (h : IsEnergySolutionOn A x (Ici 0) u) (hA : Continuous A) {t : ℝ}
    (ht : 0 < t) :
    HasDerivAt (fun s ↦ (energyTriple n).pivotToDual (u s).2) (A (u t)) t :=
  (h.hasDerivWithinAt_velocity hA ht.le).hasDerivAt (Ici_mem_nhds ht)

/-! ### The weak formulation of a forward solution -/

/-- Every finite restriction of a forward energy solution has the standard Bochner weak-wave
formulation, when the acceleration is `A z = ell z - gradientForm z.1` for a continuous load
`ell`. The load, displacement, velocity, acceleration, and initial data are all identified. This
is a weak PDE statement in the whole-space Gelfand triple. -/
theorem weakWave_on {ell : H¹(ℝ^n) × DerivLp n 2 univ → StrongDual ℝ H¹(ℝ^n)}
    {u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)} (h : IsEnergySolutionOn A x (Ici 0) u)
    (hell : Continuous ell) (hA : ∀ z, A z = ell z - gradientForm n z.1) {b : ℝ} (hb : 0 < b) :
    ∃ (ellLp : Lp (StrongDual ℝ H¹(ℝ^n)) 2 (volume.restrict (Ioc 0 b)))
      (q : Lp H¹(ℝ^n) 2 (volume.restrict (Ioc 0 b)))
      (p : Lp (DerivLp n 2 univ) 2 (volume.restrict (Ioc 0 b)))
      (a : Lp (StrongDual ℝ H¹(ℝ^n)) 2 (volume.restrict (Ioc 0 b))),
      (ellLp : ℝ → StrongDual ℝ H¹(ℝ^n)) =ᵐ[volume.restrict (Ioc 0 b)] (fun t ↦ ell (u t)) ∧
      (q : ℝ → H¹(ℝ^n)) =ᵐ[volume.restrict (Ioc 0 b)] (fun t ↦ (u t).1) ∧
      (p : ℝ → DerivLp n 2 univ) =ᵐ[volume.restrict (Ioc 0 b)] (fun t ↦ (u t).2) ∧
      (a : ℝ → StrongDual ℝ H¹(ℝ^n)) =ᵐ[volume.restrict (Ioc 0 b)] (fun t ↦ A (u t)) ∧
      IsGelfandWeakWaveSolution (energyTriple n) (fun _ ↦ gradientForm n)
        ellLp q p a x.1 x.2 := by
  have hAu : (fun s ↦ A (u s)) = fun s ↦ ell (u s) - gradientForm n (u s).1 :=
    funext fun s ↦ hA (u s)
  have hload : Continuous fun t : ℝ ↦ ell (u t) := hell.comp u.continuous
  rw [hAu]
  refine exists_weakWave_of_continuous_integral_equations
    (energyTriple n) (gradientForm n) hload u.continuous x hb
    (fun t ht ↦ h.displacement t ht.1) (fun t ht ↦ ?_)
  have hv := h.velocity t ht.1
  rw [hAu] at hv
  exact hv

/-- The integrated equation of a forward energy solution against every spatial H¹ test `w` and
every endpoint time test `τ`, for a continuous acceleration: integration by parts moves the time
derivative of the velocity onto the time test, and the initial velocity occurs in the boundary
term. -/
theorem weak_pde {u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)} (h : IsEnergySolutionOn A x (Ici 0) u)
    (hA : Continuous A) {b : ℝ} (hb : 0 ≤ b) (w : H¹(ℝ^n)) (τ : TimeTest 0 b) :
    -(∫ t in (0 : ℝ)..b, ⟪(u t).2, (energyTriple n).inclusion w⟫_ℝ * τ.derivFun t) =
      (∫ t in (0 : ℝ)..b, A (u t) w * τ.toFun t) +
        ⟪x.2, (energyTriple n).inclusion w⟫_ℝ * τ.toFun 0 := by
  have hacc : Continuous (fun t ↦ A (u t)) := hA.comp u.continuous
  have hg : Continuous (fun t ↦ A (u t) w) :=
    (ContinuousLinearMap.apply ℝ ℝ w).continuous.comp hacc
  have hscalar (t : ℝ) (ht : t ∈ Icc 0 b) : (∫ s in (0 : ℝ)..t, A (u s) w) =
        ⟪(u t).2, (energyTriple n).inclusion w⟫_ℝ -
          ⟪x.2, (energyTriple n).inclusion w⟫_ℝ := by
    have heq := congrArg (fun l : StrongDual ℝ H¹(ℝ^n) ↦ l w) (h.velocity t ht.1)
    change (∫ s in (0 : ℝ)..t, A (u s)) w =
      ((energyTriple n).pivotToDual (u t).2 - (energyTriple n).pivotToDual x.2) w at heq
    rw [ContinuousLinearMap.intervalIntegral_apply
      (hacc.intervalIntegrable (μ := volume) 0 t)] at heq
    simpa only [sub_apply, GelfandTriple.pivotToDual_apply] using heq
  exact τ.initial_identity_of_integral_eq hb hg ⟪x.2, (energyTriple n).inclusion w⟫_ℝ hscalar

/-! ### Solutions on a finite interval -/

variable {τ : NNReal}

/-- Constant extension of a finite energy trajectory. -/
def extension (h : IsEnergySolutionOn A x (Icc 0 (τ : ℝ)) u) :
    C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ) :=
  ⟨IccExtend τ.coe_nonneg (fun t ↦ u t),
    (continuousOn_iff_continuous_domRestrict.mp h.continuous).Icc_extend'⟩

/-- Extension leaves all values in the original interval unchanged. -/
theorem extension_apply (h : IsEnergySolutionOn A x (Icc 0 (τ : ℝ)) u)
    {t : ℝ} (ht : t ∈ Icc 0 (τ : ℝ)) : h.extension t = u t :=
  IccExtend_of_mem τ.coe_nonneg (fun t ↦ u t) ht

/-- Constant extension preserves the finite-interval integral equations. -/
theorem extend (h : IsEnergySolutionOn A x (Icc 0 (τ : ℝ)) u) :
    IsEnergySolutionOn A x (Icc 0 (τ : ℝ)) h.extension := by
  refine ⟨h.extension.continuous.continuousOn,
    (h.extension_apply ⟨le_rfl, τ.coe_nonneg⟩).trans h.initial, ?_, ?_⟩
  · intro t ht
    rw [h.extension_apply ht]
    refine Eq.trans ?_ (h.displacement t ht)
    refine intervalIntegral.integral_congr fun s hs ↦ ?_
    rw [uIcc_of_le ht.1] at hs
    exact congrArg Prod.snd (h.extension_apply ⟨hs.1, hs.2.trans ht.2⟩)
  · intro t ht
    rw [h.extension_apply ht]
    refine Eq.trans ?_ (h.velocity t ht)
    refine intervalIntegral.integral_congr fun s hs ↦ ?_
    rw [uIcc_of_le ht.1] at hs
    exact congrArg A (h.extension_apply ⟨hs.1, hs.2.trans ht.2⟩)

/-- A finite energy trajectory is uniformly bounded in the natural `H¹ × L²` norm. -/
theorem exists_norm_bound (h : IsEnergySolutionOn A x (Icc 0 (τ : ℝ)) u) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ t ∈ Icc 0 (τ : ℝ), ‖u t‖ ≤ R := by
  obtain ⟨R, hR⟩ := (isCompact_Icc.image_of_continuousOn h.continuous).isBounded.exists_norm_le
  exact ⟨max 0 R, le_max_left _ _, fun t ht ↦
    (hR _ (mem_image_of_mem u ht)).trans (le_max_right _ _)⟩

/-! ### The mild equation and uniqueness -/

variable {F : H¹(ℝ^n) × DerivLp n 2 univ → DerivLp n 2 univ}
variable {G : C(EnergyState n, EnergyState n)}

/-- Linear identification gives the Duhamel formula at each time. Let `A` be presented by the
continuous force `F` (`hF`, `hA`) and let `0 < b`. An energy solution `u` on `[0, b]` of
`u_tt = A(u, u_t)` with data `x` satisfies, for every `t ∈ [0, b]` and in the coordinates of
`EnergyState n`, `u t = S(t) x + ∫₀ᵗ S(t - s) (0, F (u s)) ds` for the semigroup
`S = linearSemigroup n`. For the predicate `IsEnergySolutionOn` this is the one use of
`linear_integral_identification`; the mild-solution statements of this file and of the scalar,
first-jet and defocusing families are corollaries. -/
theorem mild_eq {u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)} {b : ℝ}
    (h : IsEnergySolutionOn A x (Icc 0 b) u) (hF : Continuous F)
    (hA : ∀ z, (energyTriple n).pivotToDual (F z) - massForm n z.1 = A z) (hb : 0 < b) {t : ℝ}
    (ht : t ∈ Icc 0 b) :
    (C).symm (u t) = (linearSemigroup n).realOrbit ((C).symm x) t +
      (linearSemigroup n).duhamel (fun s ↦ (C).symm (0, F (u s))) t := by
  have hg : Continuous fun s ↦ F (u s) := hF.comp u.continuous
  have hw := linear_integral_identification hg u.continuous ((C).symm x) hb
    (fun s hs ↦ by
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using h.displacement s hs)
    (fun s hs ↦ by
      simpa only [hA, ContinuousLinearEquiv.apply_symm_apply] using h.velocity s hs)
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using congrArg (C).symm (hw ht)

/-- An energy solution on `[0, τ]` of `u_tt = A(u, u_t)`, with `A` presented by the force `F`
and the vector field `G` (`hF`, `hA`, `hG`), is a mild solution of `G` for the constructed
whole-space generator: `IsEnergySolutionOn.mild_eq` at every time of `[0, τ]`, with the Duhamel
integrand written through `G` and the trajectory `energyTrace u τ`. -/
theorem isMildSolutionOn {u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)}
    (h : IsEnergySolutionOn A x (Icc 0 (τ : ℝ)) u) (hF : Continuous F)
    (hA : ∀ z, (energyTriple n).pivotToDual (F z) - massForm n z.1 = A z)
    (hG : ∀ z, G z = (C).symm (0, F (C z))) (hτ : 0 < (τ : ℝ)) :
    (linearSemigroup n).IsMildSolutionOn G ((C).symm x) τ (energyTrace u τ) := by
  intro t
  have heq := h.mild_eq hF hA hτ t.property
  change (energyTrace u τ) t = (linearSemigroup n) (t : ℝ).toNNReal ((C).symm x) +
    (linearSemigroup n).duhamel (fun s ↦ (C).symm (0, F (u s))) t at heq
  rw [heq]
  congr 1
  refine (linearSemigroup n).duhamel_congr t.property.1 fun s hs ↦ ?_
  change (C).symm (0, F (u s)) = G (IccExtend τ.coe_nonneg (energyTrace u τ) s)
  rw [IccExtend_of_mem τ.coe_nonneg (energyTrace u τ) ⟨hs.1, hs.2.trans t.property.2⟩, hG]
  change (C).symm (0, F (u s)) = (C).symm (0, F (C ((C).symm (u s))))
  rw [ContinuousLinearEquiv.apply_symm_apply]

/-- Let `A` be presented by the continuous force `F` and the vector field `G` (`hF`, `hA`, `hG`).
If `G` is locally Lipschitz, two energy solutions on `[0, τ]` with the same data agree there.
Neither is assumed to be a mild solution. -/
theorem eqOn_Icc (hu : IsEnergySolutionOn A x (Icc 0 (τ : ℝ)) u)
    (hv : IsEnergySolutionOn A x (Icc 0 (τ : ℝ)) v) (hF : Continuous F)
    (hA : ∀ z, (energyTriple n).pivotToDual (F z) - massForm n z.1 = A z)
    (hG : ∀ z, G z = (C).symm (0, F (C z))) (hGL : LocallyLipschitz G) :
    EqOn u v (Icc 0 (τ : ℝ)) := by
  by_cases hτ : 0 < (τ : ℝ)
  · have heq := (hu.extend.isMildSolutionOn hF hA hG hτ).eq_of_locallyLipschitz hGL
      (hv.extend.isMildSolutionOn hF hA hG hτ)
    intro t ht
    have hval := congrArg (fun w ↦ C (w ⟨t, ht⟩)) heq
    simpa only [energyTrace, ContinuousMap.coe_mk, ContinuousLinearEquiv.apply_symm_apply,
      hu.extension_apply ht, hv.extension_apply ht] using hval
  · have hz : (τ : ℝ) = 0 := le_antisymm (not_lt.mp hτ) τ.coe_nonneg
    intro t ht
    have ht0 : t = 0 := le_antisymm (ht.2.trans hz.le) ht.1
    rw [ht0, hu.initial, hv.initial]

/-- Let `A` be presented by the continuous force `F` and the vector field `G` (`hF`, `hA`, `hG`).
If `G` is locally Lipschitz, two forward energy solutions with the same data agree at every
nonnegative time. Neither is assumed to be a mild solution. -/
theorem eqOn_Ici (hu : IsEnergySolutionOn A x (Ici 0) u) (hv : IsEnergySolutionOn A x (Ici 0) v)
    (hF : Continuous F)
    (hA : ∀ z, (energyTriple n).pivotToDual (F z) - massForm n z.1 = A z)
    (hG : ∀ z, G z = (C).symm (0, F (C z))) (hGL : LocallyLipschitz G) :
    EqOn u v (Ici 0) := by
  intro t ht
  have ht0 : (0 : ℝ) ≤ t := ht
  exact (hu.mono Icc_subset_Ici_self).eqOn_Icc (τ := ⟨t, ht0⟩) (hv.mono Icc_subset_Ici_self)
    hF hA hG hGL ⟨ht0, le_rfl⟩

end IsEnergySolutionOn

/-- Let `A` be presented by the continuous force `F` and the vector field `G` (`hF`, `hA`, `hG`).
If `G` is globally Lipschitz, arbitrary whole-space energy data admit a forward global energy
solution of `u_tt = A(u, u_t)`. There is no smallness, compact-support, extra spatial regularity,
or finite-lifetime assumption. Negative times merely supply a continuous extension for
integration. -/
theorem exists_isEnergySolutionOn_Ici
    {A : H¹(ℝ^n) × DerivLp n 2 univ → StrongDual ℝ H¹(ℝ^n)}
    {F : H¹(ℝ^n) × DerivLp n 2 univ → DerivLp n 2 univ} {G : C(EnergyState n, EnergyState n)}
    {K : NNReal} (hF : Continuous F)
    (hA : ∀ z, (energyTriple n).pivotToDual (F z) - massForm n z.1 = A z)
    (hG : ∀ z, G z = (C).symm (0, F (C z))) (hGK : LipschitzWith K G)
    (x : H¹(ℝ^n) × DerivLp n 2 univ) :
    ∃ u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ), IsEnergySolutionOn A x (Ici 0) u := by
  obtain ⟨z, hz0, hz⟩ := exists_global_mild (linearSemigroup n) hGK ((C).symm x)
  let u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ) := ⟨fun t ↦ C (z t), (C).continuous.comp z.continuous⟩
  let g := fun s ↦ F (u s)
  have hg : Continuous g := hF.comp u.continuous
  let w := fun t ↦ C ((linearSemigroup n).realOrbit ((C).symm x) t +
    (linearSemigroup n).duhamel (fun s ↦ (C).symm (0, g s)) t)
  have huw (t : ℝ) (ht : 0 ≤ t) : u t = w t := by
    have h := hz t ht
    simp only [hG] at h
    exact congrArg C h
  refine ⟨u, u.continuous.continuousOn, ?_, ?_, ?_⟩
  · change C (z 0) = x
    rw [hz0, ContinuousLinearEquiv.apply_symm_apply]
  · intro t ht
    have ht0 : (0 : ℝ) ≤ t := ht
    have hw := (linear_forced_integral hg ((C).symm x) ht0).1
    simp only [ContinuousLinearEquiv.apply_symm_apply] at hw
    change (∫ s in (0 : ℝ)..t, (w s).2) =
      (energyTriple n).inclusion (w t).1 - (energyTriple n).inclusion x.1 at hw
    rw [← huw t ht0] at hw
    refine Eq.trans ?_ hw
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht0] at hs
    exact congrArg Prod.snd (huw s hs.1)
  · intro t ht
    have ht0 : (0 : ℝ) ≤ t := ht
    have hw := (linear_forced_integral hg ((C).symm x) ht0).2
    simp only [ContinuousLinearEquiv.apply_symm_apply] at hw
    change (∫ s in (0 : ℝ)..t, (energyTriple n).pivotToDual (g s) - massForm n (w s).1) =
      (energyTriple n).pivotToDual (w t).2 - (energyTriple n).pivotToDual x.2 at hw
    rw [← huw t ht0] at hw
    refine Eq.trans ?_ hw
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht0] at hs
    change A (u s) = (energyTriple n).pivotToDual (g s) - massForm n (w s).1
    rw [← huw s hs.1]
    exact (hA (u s)).symm

end PDE.Hyperbolic.NonlinearWave.Cauchy
