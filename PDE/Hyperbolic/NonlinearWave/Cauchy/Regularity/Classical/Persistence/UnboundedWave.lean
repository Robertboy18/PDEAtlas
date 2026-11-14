/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Scalar.OddPower
public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.Lifespan
import PDE.Analysis.Calculus.LocalExtension.ForwardBand
import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Persistence.SmoothMaximalExistence
import PDE.Hyperbolic.NonlinearWave.NegativeEnergy.CompactData.GlobalObstruction
import CAS.ExactTactic

/-!
# Smooth waves that are unbounded near a finite time

For a smooth reaction `f` with `f 0 = 0` and smooth compactly supported Cauchy data `g`, `h` on
`ℝ³`, `exists_maximal_smooth_wave` gives a smooth solution of `u_tt - Δu + f(u) = 0` on a maximal
interval `[0, L)`, and when `L` is finite the solution is unbounded on every strip
`[a, L) × ℝ³`. This file names the finite case and ties it to the classical solutions
`WaveEquation.SmallData.Classical.IsSolutionBefore`.

Two classes of solutions with the data `g`, `h` occur. A *forward solution* on `[0, S)` is `C²`
for `0 < t < S` and `C¹` for `0 ≤ t < S`, solves the equation for `0 < t < S`, equals `g` at
`t = 0` and has the velocity `h` there as a derivative from the right; these are the competitors
in the maximality clause of `exists_maximal_smooth_wave`, and the smooth wave is one of them on
every `[0, S)`, `S < L`. A *classical solution before `S`* is
`WaveEquation.SmallData.Classical.IsSolutionBefore`: it is `C²` on `{t < S}`, negative times
included, and solves the equation for `0 ≤ t < S`. We prove:

* `IsUnboundedWave f g h T u`: `T > 0`, `u` is smooth on `[0, T) × ℝ^n`, solves the equation for
  `0 < t < T` with the data `g`, `h`, every forward solution on `[0, S)` has `S ≤ T`, and `u` is
  unbounded on every strip `[a, T) × ℝ^n`, `a < T`.
* `exists_global_or_isUnboundedWave`: in `ℝ³`, for all smooth `f` with `f 0 = 0` and all smooth
  compactly supported data, there is a smooth solution for all `t ≥ 0`, or there are `T`, `u` with
  `IsUnboundedWave f g h T u`. `IsUnboundedWave.not_global`: not both.
* `exists_isUnboundedWave_of_negative_energy`: the second case holds for `f = V'` when `V` is
  smooth with `V 0 = 0` and `z V'(z) ≤ Λ V(z)`, `Λ > 2`, and the data have negative energy
  `∫ ½ (h² + |∇g|²) + V(g)`. `exists_isUnboundedWave_oddPower`: the equations
  `u_tt - Δu + m u + c u^(2k+1) = 0` with `m ≥ 0` and `k ≥ 1`, for
  `PDE.Analysis.Scalar.oddPowerPotential`.
* `IsUnboundedWave.eqOn`, `IsUnboundedWave.unique`, for a locally Lipschitz `f` and `n ≥ 1`:
  every forward solution on `[0, S)` has `S ≤ T` and agrees with `u` for `0 ≤ t < S`, and two
  unbounded waves with the same data have the same time and agree before it.
* `exists_isSolutionBefore_of_contDiffOn_forward`, `mem_existenceTimes_of_contDiffOn_forward`:
  for a continuous `f`, every `n` and `T > 0`, a solution that is `C²` on `[0, T) × ℝ^n`, up to
  the initial time, with the velocity as a derivative from the right, agrees for `t ≥ 0` with a
  classical solution before `T`. So `T` is the duration of a classical solution.
* `IsUnboundedWave.exists_isMaximalSolutionBefore`, `IsUnboundedWave.existenceTimes_eq`,
  `IsUnboundedWave.time_le`, for a continuous `f`: the unbounded wave agrees for `t ≥ 0` with a
  maximal classical solution before `T`, the durations of all classical solutions with the same
  data are exactly the times in `(0, T]`, and a bound for those durations bounds `T`.

## What unbounded means

The last field of `IsUnboundedWave` says that `sup |u|` over `[a, T) × ℝ^n` is infinite for every
`a < T`. This is a statement about a limit superior: there are times `tₖ → T` and points `xₖ` with
`|u (tₖ, xₖ)| → ∞`. It does not say that `sup_x |u (t, x)|` tends to infinity as `t → T`. The
module doc of `exists_maximal_smooth_wave` compares this with the blow-up (12) of Evans,
§12.3.2, Theorem 2.

There is a limit for another norm. The wave of `exists_maximal_smooth_wave` is the displacement
of a trajectory in `W^{5,2} × W^{4,2}`, and `higherSmooth_maximal_norm_eventually_gt` says that the
norm of that trajectory tends to infinity at a finite lifespan. The statement of
`exists_maximal_smooth_wave` does not give the trajectory, so this file does not have that limit.

## How it works

A classical solution before `T` is `C²` on `{t < T}`, negative times included, and the smooth
wave is given for `t ≥ 0` only. `PDE.Analysis.exists_contDiffOn_extension_halfOpenBand` extends
it to a `C²` function on `{t < T}` that agrees with it for `t ≥ 0`. The extension solves the
equation for `0 < t < T`, where it agrees with `u` near every point. At `t = 0` the equation
follows by continuity (`WaveEquation.waveOperator_add_eq_zero_of_mem_Icc`), applied to a `C²`
function on the whole space-time that agrees with the extension near `t ≤ T / 2`
(`WaveEquation.SmallData.Classical.exists_contDiff_eventuallyEq_before`).

The global case is excluded for negative energy by
`WaveEquation.NegativeEnergy.not_global_forward_semilinearWave_of_compact_negative_energy`.

## References

The existence and the negative-energy obstruction restate `exists_maximal_smooth_wave` and
`WaveEquation.NegativeEnergy.not_global_forward_semilinearWave_of_compact_negative_energy`. The
module docs of
`PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Persistence.SmoothMaximalExistence` and
`PDE.Hyperbolic.NonlinearWave.NegativeEnergy.CompactData.GlobalObstruction` cite their sources;
this module adds none of its own.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Common PDE.Analysis.Scalar WaveEquation
open WaveEquation.SmallData.Classical
open scoped ENNReal Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

variable {n : ℕ} {f : ℝ → ℝ} {g h : ℝ^n → ℝ} {S T : ℝ} {u : ℝ^(n + 1) → ℝ}

/-- `IsUnboundedWave f g h T u`: `T > 0`, `u` is a smooth solution of `u_tt - Δu + f(u) = 0` on
`[0, T) × ℝ^n` with the Cauchy data `g`, `h`, no forward solution with the same data lives longer
than `T`, and `u` is unbounded on every strip `[a, T) × ℝ^n`, `a < T`. The last clause is about a
limit superior: it does not say that `sup_x |u (t, x)|` tends to infinity as `t → T`. -/
structure IsUnboundedWave (f : ℝ → ℝ) (g h : ℝ^n → ℝ) (T : ℝ) (u : ℝ^(n + 1) → ℝ) : Prop where
  /-- The time `T` is positive. -/
  time_pos : 0 < T
  /-- `u` is smooth on `[0, T) × ℝ^n`, up to the initial time. -/
  smooth : ContDiffOn ℝ (⊤ : ℕ∞) u {p | p 0 ∈ Ico 0 T}
  /-- The displacement at time zero is `g`. -/
  position : ∀ x, u (timeSpaceCons 0 x) = g x
  /-- The velocity at time zero, a derivative from the right, is `h`. -/
  velocity : ∀ x, HasDerivWithinAt (fun t ↦ u (timeSpaceCons t x)) (h x) (Ici 0) 0
  /-- `u_tt - Δu + f(u) = 0` for `0 < t < T`. -/
  equation : ∀ t ∈ Ioo 0 T, ∀ x,
    waveOperator u (timeSpaceCons t x) + f (u (timeSpaceCons t x)) = 0
  /-- A solution with the same data that is `C²` for `0 < t < S` and `C¹` for `0 ≤ t < S` has
  `S ≤ T`. -/
  maximal : ∀ (S : ℝ) (v : ℝ^(n + 1) → ℝ), ContDiffOn ℝ 2 v {p | p 0 ∈ Ioo 0 S} →
    ContDiffOn ℝ 1 v {p | p 0 ∈ Ico 0 S} →
    (∀ t ∈ Ioo 0 S, ∀ x, waveOperator v (timeSpaceCons t x) + f (v (timeSpaceCons t x)) = 0) →
    (∀ x, v (timeSpaceCons 0 x) = g x) →
    (∀ x, derivWithin (fun t ↦ v (timeSpaceCons t x)) (Ici 0) 0 = h x) → S ≤ T
  /-- `u` is unbounded on every strip `[a, T) × ℝ^n`, `a < T`. -/
  unbounded : ∀ a < T, ∀ B : ℝ, ∃ t ∈ Ico (max 0 a) T, ∃ x, B < |u (timeSpaceCons t x)|

/-! ## Existence -/

/-- **The alternative.** In `ℝ³`, for a smooth reaction `f` with `f 0 = 0` and smooth compactly
supported Cauchy data `g`, `h`, the equation `u_tt - Δu + f(u) = 0` has a smooth solution for all
`t ≥ 0`, or it has a smooth solution on `[0, T)`, `T < ∞`, that is unbounded on every strip
`[a, T) × ℝ³` and that no classical solution with the same data outlives. This is
`exists_maximal_smooth_wave`, split by whether its lifespan is finite. -/
theorem exists_global_or_isUnboundedWave {f : ℝ → ℝ} (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0)
    {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hgc : HasCompactSupport g) (hhc : HasCompactSupport h) :
    (∃ u : ℝ^4 → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) u {p | 0 ≤ p 0} ∧
      (∀ x, u (timeSpaceCons 0 x) = g x) ∧
      (∀ x, HasDerivWithinAt (fun t ↦ u (timeSpaceCons t x)) (h x) (Ici 0) 0) ∧
      ∀ t : ℝ, 0 < t → ∀ x : ℝ^3,
        waveOperator u (timeSpaceCons t x) + f (u (timeSpaceCons t x)) = 0) ∨
      ∃ T u, IsUnboundedWave f g h T u := by
  obtain ⟨L, hL, u, hu, hpos, hvel, hwave, hmax, hblow⟩ :=
    exists_maximal_smooth_wave hs hf0 g h hg hh hgc hhc
  rcases eq_or_ne L ∞ with rfl | hLtop
  · exact .inl ⟨u, hu.mono fun p hp ↦ ⟨hp, ENNReal.ofReal_lt_top⟩, hpos, hvel,
      fun t ht x ↦ hwave t ht ENNReal.ofReal_lt_top x⟩
  · have hlt {t : ℝ} (ht : 0 ≤ t) (htL : t < L.toReal) : ENNReal.ofReal t < L :=
      (ENNReal.ofReal_lt_iff_lt_toReal ht hLtop).mpr htL
    exact .inr ⟨L.toReal, u, ENNReal.toReal_pos hL.ne' hLtop,
      hu.mono fun p hp ↦ ⟨hp.1, hlt hp.1 hp.2⟩, hpos, hvel,
      fun t ht x ↦ hwave t ht.1 (hlt ht.1.le ht.2) x,
      fun S v hv₂ hv₁ hvw hvp hvv ↦
        (ENNReal.ofReal_le_iff_le_toReal hLtop).mp (hmax S v hv₂ hv₁ hvw hvp hvv),
      by simpa only [Real.norm_eq_abs] using hblow hLtop⟩

/-- **Negative energy.** Let `V` be smooth with `V 0 = 0` and `z V'(z) ≤ Λ V(z)` for some
`Λ > 2`. In `ℝ³`, smooth compactly supported Cauchy data `g`, `h` with negative energy
`∫ ½ (h² + |∇g|²) + V(g)` have a smooth solution of `u_tt - Δu + V'(u) = 0` on `[0, T)`, `T < ∞`,
that is unbounded on every strip `[a, T) × ℝ³` and that no classical solution with the same data
outlives. -/
theorem exists_isUnboundedWave_of_negative_energy {V : ℝ → ℝ} {Λ : ℝ}
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hV0 : V 0 = 0) (hΛ : 2 < Λ)
    (hgrowth : ∀ z, z * deriv V z ≤ Λ * V z) {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hgc : HasCompactSupport g) (hhc : HasCompactSupport h)
    (hE : (∫ x : ℝ^3, (1 / 2 : ℝ) * ((h x) ^ 2 + ∑ i : Fin 3, ((∂[i] g) x) ^ 2) + V (g x)) < 0) :
    ∃ T u, IsUnboundedWave (deriv V) g h T u := by
  have hV2 : ContDiff ℝ 2 V := hV.of_le (by simp)
  refine (exists_global_or_isUnboundedWave (contDiff_infty_iff_deriv.mp hV).2
    (NegativeEnergy.deriv_potential_zero_of_growth hV2 hV0 hΛ hgrowth) hg hh hgc
    hhc).resolve_left ?_
  rintro ⟨u, hu, hpos, hvel, hwave⟩
  exact NegativeEnergy.not_global_forward_semilinearWave_of_compact_negative_energy hV2 hV0 hΛ
    hgrowth hgc hhc hE ((hu.of_le (by simp)).mono fun p (hp : 0 < p 0) ↦ hp.le)
    (hu.of_le (by simp)) hwave hpos fun x ↦ (hvel x).derivWithin (uniqueDiffWithinAt_Ici 0)

/-- **Odd powers.** For `m ≥ 0`, `k ≥ 1` and every `c`, smooth compactly supported Cauchy data
`g`, `h` on `ℝ³` with negative energy `∫ ½ (h² + |∇g|²) + m g² / 2 + c g^(2k+2) / (2k + 2)` have a
smooth solution of `u_tt - Δu + m u + c u^(2k+1) = 0` on `[0, T)`, `T < ∞`, that is unbounded on
every strip `[a, T) × ℝ³` and that no classical solution with the same data outlives. The
energy can be negative only for `c < 0`: for `c ≥ 0` the potential is nonnegative, by
`PDE.Analysis.Scalar.oddPowerPotential_nonneg`. -/
theorem exists_isUnboundedWave_oddPower {m c : ℝ} {k : ℕ} (hm : 0 ≤ m) (hk : 0 < k)
    {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hgc : HasCompactSupport g) (hhc : HasCompactSupport h)
    (hE : (∫ x : ℝ^3, (1 / 2 : ℝ) * ((h x) ^ 2 + ∑ i : Fin 3, ((∂[i] g) x) ^ 2) +
      oddPowerPotential m c k (g x)) < 0) :
    ∃ T u, IsUnboundedWave (oddPowerPolynomial m c k) g h T u := by
  rw [← funext (deriv_oddPowerPotential m c k)]
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  exact exists_isUnboundedWave_of_negative_energy
    ((contDiff_oddPowerPotential m c k).of_le le_top) (oddPowerPotential_zero m c k)
    (by cas using [hk']) (mul_deriv_oddPowerPotential_le c k hm) hg hh hgc hhc hE

namespace IsUnboundedWave

/-- An unbounded wave excludes a smooth solution for all `t ≥ 0` with the same data: the two
cases of `exists_global_or_isUnboundedWave` exclude each other. -/
theorem not_global (hu : IsUnboundedWave f g h T u) {v : ℝ^(n + 1) → ℝ}
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v {p | 0 ≤ p 0}) (hvp : ∀ x, v (timeSpaceCons 0 x) = g x)
    (hvv : ∀ x, HasDerivWithinAt (fun t ↦ v (timeSpaceCons t x)) (h x) (Ici 0) 0)
    (hvw : ∀ t : ℝ, 0 < t → ∀ x,
      waveOperator v (timeSpaceCons t x) + f (v (timeSpaceCons t x)) = 0) : False :=
  (lt_add_one T).not_ge (hu.maximal (T + 1) v ((hv.of_le (by simp)).mono fun p hp ↦ hp.1.le)
    ((hv.of_le (by simp)).mono fun p hp ↦ hp.1) (fun t ht x ↦ hvw t ht.1 x) hvp
    fun x ↦ (hvv x).derivWithin (uniqueDiffWithinAt_Ici 0))

/-- **Uniqueness.** Let `f` be locally Lipschitz and `n ≥ 1`. A solution with the data of an
unbounded wave that is `C²` for `0 < t < S` and `C¹` for `0 ≤ t < S` has `S ≤ T` and agrees with
the unbounded wave for `0 ≤ t < S`. -/
theorem eqOn [Fact (0 < n)] (hf : LocallyLipschitz f) (hu : IsUnboundedWave f g h T u)
    {v : ℝ^(n + 1) → ℝ} (hv₂ : ContDiffOn ℝ 2 v {p | p 0 ∈ Ioo 0 S})
    (hv₁ : ContDiffOn ℝ 1 v {p | p 0 ∈ Ico 0 S})
    (hvw : ∀ t ∈ Ioo 0 S, ∀ x,
      waveOperator v (timeSpaceCons t x) + f (v (timeSpaceCons t x)) = 0)
    (hvp : ∀ x, v (timeSpaceCons 0 x) = g x)
    (hvv : ∀ x, derivWithin (fun t ↦ v (timeSpaceCons t x)) (Ici 0) 0 = h x) :
    S ≤ T ∧ ∀ t ∈ Ico 0 S, ∀ x, v (timeSpaceCons t x) = u (timeSpaceCons t x) := by
  have hST := hu.maximal S v hv₂ hv₁ hvw hvp hvv
  exact ⟨hST, eq_on_finite_forward_strip hf hv₂
    ((hu.smooth.of_le (by simp)).mono fun p hp ↦ ⟨hp.1.le, hp.2.trans_le hST⟩) hv₁
    ((hu.smooth.of_le (by simp)).mono fun p hp ↦ ⟨hp.1, hp.2.trans_le hST⟩) hvw
    (fun t ht x ↦ hu.equation t ⟨ht.1, ht.2.trans_le hST⟩ x)
    (fun x ↦ (hvp x).trans (hu.position x).symm)
    fun x ↦ (hvv x).trans ((hu.velocity x).derivWithin (uniqueDiffWithinAt_Ici 0)).symm⟩

/-- **The unbounded wave is unique.** Let `f` be locally Lipschitz and `n ≥ 1`. Two unbounded
waves with the same data have the same time `T` and agree for `0 ≤ t < T`. -/
theorem unique [Fact (0 < n)] (hf : LocallyLipschitz f) (hu : IsUnboundedWave f g h T u)
    {v : ℝ^(n + 1) → ℝ} (hv : IsUnboundedWave f g h S v) :
    S = T ∧ ∀ t ∈ Ico 0 T, ∀ x, v (timeSpaceCons t x) = u (timeSpaceCons t x) := by
  obtain ⟨hST, he⟩ := hu.eqOn hf
    ((hv.smooth.of_le (by simp)).mono fun p hp ↦ ⟨hp.1.le, hp.2⟩) (hv.smooth.of_le (by simp))
    hv.equation hv.position fun x ↦ (hv.velocity x).derivWithin (uniqueDiffWithinAt_Ici 0)
  obtain ⟨hTS, -⟩ := hv.eqOn hf
    ((hu.smooth.of_le (by simp)).mono fun p hp ↦ ⟨hp.1.le, hp.2⟩) (hu.smooth.of_le (by simp))
    hu.equation hu.position fun x ↦ (hu.velocity x).derivWithin (uniqueDiffWithinAt_Ici 0)
  obtain rfl := le_antisymm hST hTS
  exact ⟨rfl, he⟩

end IsUnboundedWave

/-! ## The classical solutions with the same data -/

/-- **A classical representative.** Let `f` be continuous and let `u` be `C²` on `[0, T) × ℝ^n`,
`T > 0`, up to the initial time, with `u_tt - Δu + f(u) = 0` for `0 < t < T`, `u = g` at time
zero and the velocity `h` there, as a derivative from the right. Then `u` agrees for `t ≥ 0`
with a classical solution before `T` with the data `g`, `h`, which is `C²` on `{t < T}`. -/
theorem exists_isSolutionBefore_of_contDiffOn_forward (hf : Continuous f) (hT : 0 < T)
    (hu : ContDiffOn ℝ 2 u {p | p 0 ∈ Ico 0 T}) (hpos : ∀ x, u (timeSpaceCons 0 x) = g x)
    (hvel : ∀ x, HasDerivWithinAt (fun t ↦ u (timeSpaceCons t x)) (h x) (Ici 0) 0)
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x,
      waveOperator u (timeSpaceCons t x) + f (u (timeSpaceCons t x)) = 0) :
    ∃ v : ℝ^(n + 1) → ℝ, IsSolutionBefore f g h T v ∧ ∀ p, 0 ≤ p 0 → v p = u p := by
  obtain ⟨v, hv, hvu⟩ :=
    PDE.Analysis.exists_contDiffOn_extension_halfOpenBand (0 : Fin (n + 1)) (k := 2) hT hu
  have hv : ContDiffOn ℝ 2 v {p | p 0 < T} := hv
  have hvwave (t : ℝ) (ht : t ∈ Ioo 0 T) (x : ℝ^n) :
      waveOperator v (timeSpaceCons t x) + f (v (timeSpaceCons t x)) = 0 := by
    have hgerm : v =ᶠ[𝓝 (timeSpaceCons t x)] u :=
      eventuallyEq_of_eqOn_forward hvu (by simpa using ht.1)
    rw [waveOperator_congr_nhds hgerm, hgerm.eq_of_nhds]
    exact hwave t ht x
  -- The equation at time zero, through a `C²` function on the whole space-time.
  obtain ⟨w, hw, hwv⟩ :=
    WaveEquation.SmallData.Classical.exists_contDiff_eventuallyEq_before hv (half_lt_self hT)
  have hzero (x : ℝ^n) : waveOperator v (timeSpaceCons 0 x) + f (v (timeSpaceCons 0 x)) = 0 := by
    have h0 := hwv (timeSpaceCons 0 x) (by simpa using (half_pos hT).le)
    rw [← waveOperator_congr_nhds h0, ← h0.eq_of_nhds]
    exact waveOperator_add_eq_zero_of_mem_Icc hf hw (half_pos hT) (fun t ht ↦ by
      have ht' := hwv (timeSpaceCons t x) (by simpa using ht.2.le)
      rw [waveOperator_congr_nhds ht', ht'.eq_of_nhds]
      exact hvwave t ⟨ht.1, ht.2.trans (half_lt_self hT)⟩ x) ⟨le_rfl, (half_pos hT).le⟩
  refine ⟨v, ⟨hT, hv, fun p hp ↦ ?_, fun x ↦ ?_, fun x ↦ ?_⟩, fun p hp ↦ hvu hp⟩
  · rw [← timeSpaceCons_spatialPart p]
    rcases hp.1.eq_or_lt with h0 | h0
    · rw [← h0]
      exact eq_neg_of_add_eq_zero_left (hzero _)
    · exact eq_neg_of_add_eq_zero_left (hvwave _ ⟨h0, hp.2⟩ _)
  · rw [hvu (show (0 : ℝ) ≤ (timeSpaceCons 0 x) 0 by simp), hpos]
  · have hopen : {p : ℝ^(n + 1) | p 0 < T} ∈ 𝓝 (timeSpaceCons 0 x) :=
      (isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const).mem_nhds (by simpa using hT)
    have hd := (PDE.hasDerivAt_timeSpaceCons v 0 x
      ((hv.contDiffAt hopen).differentiableAt (by norm_num))).hasDerivWithinAt (s := Ici 0)
    exact (uniqueDiffWithinAt_Ici 0).eq_deriv _ hd ((hvel x).congr
      (fun t ht ↦ hvu (show (0 : ℝ) ≤ (timeSpaceCons t x) 0 by simpa using ht))
      (hvu (show (0 : ℝ) ≤ (timeSpaceCons 0 x) 0 by simp)))

/-- Under the hypotheses of `exists_isSolutionBefore_of_contDiffOn_forward`, the time `T` is the
duration of a classical solution with the data `g`, `h`. -/
theorem mem_existenceTimes_of_contDiffOn_forward (hf : Continuous f) (hT : 0 < T)
    (hu : ContDiffOn ℝ 2 u {p | p 0 ∈ Ico 0 T}) (hpos : ∀ x, u (timeSpaceCons 0 x) = g x)
    (hvel : ∀ x, HasDerivWithinAt (fun t ↦ u (timeSpaceCons t x)) (h x) (Ici 0) 0)
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x,
      waveOperator u (timeSpaceCons t x) + f (u (timeSpaceCons t x)) = 0) :
    T ∈ existenceTimes f g h := by
  obtain ⟨v, hv, -⟩ := exists_isSolutionBefore_of_contDiffOn_forward hf hT hu hpos hvel hwave
  exact ⟨v, hv⟩

namespace IsUnboundedWave

/-- No classical solution with the data of an unbounded wave lives longer than its time `T`. -/
theorem le_of_isSolutionBefore (hu : IsUnboundedWave f g h T u) {v : ℝ^(n + 1) → ℝ}
    (hv : IsSolutionBefore f g h S v) : S ≤ T := by
  have hopen : IsOpen {p : ℝ^(n + 1) | p 0 < S} :=
    isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const
  refine hu.maximal S v (hv.regular.mono fun p hp ↦ hp.2)
    ((hv.regular.of_le (by norm_num)).mono fun p hp ↦ hp.2)
    (fun t ht x ↦ by
      rw [hv.equation _ (by simpa using And.intro ht.1.le ht.2), neg_add_cancel])
    hv.position fun x ↦ ?_
  rw [← hv.velocity x]
  exact (PDE.hasDerivAt_timeSpaceCons v 0 x ((hv.regular.contDiffAt
    (hopen.mem_nhds (by simpa using hv.time_pos))).differentiableAt
      (by norm_num))).hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici 0)

/-- **The maximal classical solution.** For a continuous `f`, an unbounded wave agrees for
`t ≥ 0` with a maximal classical solution before its time `T`: a classical solution before `T`
that no classical solution with the same data extends. -/
theorem exists_isMaximalSolutionBefore (hf : Continuous f) (hu : IsUnboundedWave f g h T u) :
    ∃ v : ℝ^(n + 1) → ℝ, IsMaximalSolutionBefore f g h T v ∧ ∀ p, 0 ≤ p 0 → v p = u p := by
  obtain ⟨v, hv, hvu⟩ := exists_isSolutionBefore_of_contDiffOn_forward hf hu.time_pos
    (hu.smooth.of_le (by simp)) hu.position hu.velocity hu.equation
  exact ⟨v, ⟨hv, fun hTS hw _ ↦ not_lt_of_ge (hu.le_of_isSolutionBefore hw) hTS⟩, hvu⟩

/-- **The durations.** For a continuous `f`, the durations of the classical solutions with the
data of an unbounded wave are exactly the times in `(0, T]`. -/
theorem existenceTimes_eq (hf : Continuous f) (hu : IsUnboundedWave f g h T u) :
    existenceTimes f g h = Ioc 0 T := by
  obtain ⟨v, hv, -⟩ := hu.exists_isMaximalSolutionBefore hf
  ext S
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨hw.time_pos, hu.le_of_isSolutionBefore hw⟩
  · exact fun hS ↦ ⟨v, hv.toIsSolutionBefore.mono hS.1 hS.2⟩

/-- For a continuous `f`, a bound for the durations of all classical solutions with the data of
an unbounded wave bounds its time `T`. -/
theorem time_le (hf : Continuous f) (hu : IsUnboundedWave f g h T u) {c : ℝ}
    (hc : ∀ S ∈ existenceTimes f g h, S ≤ c) : T ≤ c :=
  hc T (mem_existenceTimes_of_contDiffOn_forward hf hu.time_pos (hu.smooth.of_le (by simp))
    hu.position hu.velocity hu.equation)

end IsUnboundedWave

end PDE.Hyperbolic.NonlinearWave.Cauchy
