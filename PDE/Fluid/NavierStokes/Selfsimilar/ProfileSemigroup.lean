/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Nonlinearity.BoundedTransport
public import PDE.Parabolic.Heat.WholeSpace.SelfsimilarTransportSemigroup

/-!
# The self-similar evolution around a profile on `L²`

Let `b` and `c` be bounded transport and stretching coefficients on `ℝ³`, and let
`B v = Σᵢ bᵢ ∂ᵢ v + c v` be the bounded map from vector `H¹` to vector `L²`. The linearization
of the self-similar Navier-Stokes equation about a profile `U` has this form with `b = U` and
`c = ∇U`: it is `L v = L₀ v - Π B v`, where `Π` is the Leray projection and `L₀` generates the
free self-similar heat evolution `S₀`.

The evolution `S` is the free self-similar evolution perturbed by `B`
(`HeatEquation.WholeSpace.transportSemigroup`), built by Volterra iteration of the gaining path
`t ↦ S(t) u` in `H¹`. It solves the Duhamel equation
`S(t) u = S₀(t) u - ∫₀ᵗ Π S₀(t - s) B S(s) u ds`, has an exponential bound, gains one
derivative with the bound `C t^{-1/2} e^{ω t}`, and preserves divergence-free fields. Every path
in `H¹` that is continuous at positive times, solves the Duhamel equation and has a singular
bound `C t^{-1/2} e^{ω' t}`, with any rate `ω'`, is the gaining path.

Only bounded coefficients enter at this order. The structure `ProfileCoefficientBounds k`
records `W^{k,∞}` bounds of the coefficients for the evolution on `Hᵏ`.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace IncompressibleFlow
open HeatEquation.WholeSpace PDE.Analysis.Evolution
open scoped ENNReal NNReal Sobolev

namespace NavierStokes.Selfsimilar

/-- Bounds of order `k` for the transport and stretching coefficients of a linearized
self-similar operator: each coefficient is the base function of a `W^{k,∞}` field. -/
structure ProfileCoefficientBounds (k : ℕ) (b : Fin 3 → DerivLp 3 ∞ Set.univ)
    (c : Fin 3 → Fin 3 → DerivLp 3 ∞ Set.univ) : Prop where
  /-- Each transport coefficient has `k` weak derivatives in `L∞`. -/
  transport_mem : ∀ i, ∃ B : W^{k,∞}(ℝ^3), wkpBaseCoordinateCLM B = b i
  /-- Each stretching coefficient has `k` weak derivatives in `L∞`. -/
  stretching_mem : ∀ j i, ∃ C : W^{k,∞}(ℝ^3), wkpBaseCoordinateCLM C = c j i

/-- Bounded coefficients satisfy the bounds of order zero. -/
theorem ProfileCoefficientBounds.zero (b : Fin 3 → DerivLp 3 ∞ Set.univ)
    (c : Fin 3 → Fin 3 → DerivLp 3 ∞ Set.univ) : ProfileCoefficientBounds 0 b c :=
  ⟨fun i ↦ ⟨lpToZeroOrder (b i), rfl⟩, fun j i ↦ ⟨lpToZeroOrder (c j i), rfl⟩⟩

variable (b : Fin 3 → DerivLp 3 ∞ Set.univ) (c : Fin 3 → Fin 3 → DerivLp 3 ∞ Set.univ)

/-! ### The gaining path -/

/-- The gaining path of the profile evolution at positive times, extended by zero: the gaining
path of the free evolution perturbed by the bounded transport. -/
def profileGain0 (t : ℝ) : VectorH 3 0 →L[ℝ] VectorH 3 1 :=
  transportGain (BoundedTransport.transport b c) t

/-- The gaining path is the decoded weighted fixed point. -/
theorem profileGain0_apply (t : ℝ) (u : VectorH 3 0) :
    profileGain0 b c t u = forwardDecode (transportWeight (BoundedTransport.transport b c))
      (transportGainPath (BoundedTransport.transport b c) u) t :=
  transportGain_apply _ t u

/-- The gaining path vanishes at nonpositive times. -/
theorem profileGain0_of_nonpos {t : ℝ} (ht : t ≤ 0) : profileGain0 b c t = 0 :=
  transportGain_of_nonpos _ ht

/-- At positive times the gaining path has the singular bound with the constant
`‖transportGainPath B u‖`. -/
theorem norm_profileGain0_apply_le {t : ℝ} (ht : 0 < t) (u : VectorH 3 0) :
    ‖profileGain0 b c t u‖ ≤ ‖transportGainPath (BoundedTransport.transport b c) u‖ *
      t ^ (-(1 / 2 : ℝ)) * Real.exp (transportWeight (BoundedTransport.transport b c) * t) :=
  norm_transportGain_apply_le _ ht u

/-- The gaining path is continuous at positive times. -/
theorem continuousOn_profileGain0_apply (u : VectorH 3 0) :
    ContinuousOn (fun t ↦ profileGain0 b c t u) (Ioi 0) :=
  continuousOn_transportGain_apply _ u

/-- The gaining path solves the forward Duhamel equation in vector `H¹`. -/
theorem profileGain0_eq_forwardDuhamel {t : ℝ} (ht : 0 < t) (u : VectorH 3 0) :
    profileGain0 b c t u = vectorSelfsimilarHeatGainKernel 3 0 t u -
      forwardDuhamel (transportKernel (BoundedTransport.transport b c))
        (fun s ↦ profileGain0 b c s u) t :=
  transportGain_eq_forwardDuhamel _ ht u

/-- The gaining path solves the Duhamel equation in vector `H¹`. -/
theorem profileGain0_eq {t : ℝ} (ht : 0 < t) (u : VectorH 3 0) :
    profileGain0 b c t u = vectorSelfsimilarHeatGainKernel 3 0 t u -
      ∫ s in (0 : ℝ)..t, projectedSelfsimilarHeatGainKernel 3 0 (t - s)
        (BoundedTransport.transport b c (profileGain0 b c s u)) :=
  transportGain_eq_forwardDuhamel _ ht u

/-- The gaining path at a time shifted by `s > 0` has the singular bound with the constant
`‖transportGainPath B u‖ e^{ω s}`. -/
theorem norm_profileGain0_add_le {s : ℝ≥0} (hs : 0 < (s : ℝ)) (u : VectorH 3 0) {t : ℝ}
    (ht : 0 < t) :
    ‖profileGain0 b c (t + s) u‖ ≤
      ‖transportGainPath (BoundedTransport.transport b c) u‖ *
        Real.exp (transportWeight (BoundedTransport.transport b c) * s) * t ^ (-(1 / 2 : ℝ)) *
          Real.exp (transportWeight (BoundedTransport.transport b c) * t) :=
  norm_transportGain_add_le _ hs u ht

/-- The gaining path is the only solution of the `H¹` Duhamel equation that is continuous at
positive times and has a singular bound `C t^{-1/2} e^{ω t}`, for any rate `ω`. -/
theorem eq_profileGain0_of_duhamel {u : VectorH 3 0} {v : ℝ → VectorH 3 1}
    (hvc : ContinuousOn v (Ioi 0)) {C ω : ℝ}
    (hvb : ∀ t, 0 < t → ‖v t‖ ≤ C * t ^ (-(1 / 2 : ℝ)) * Real.exp (ω * t))
    (hv : ∀ t, 0 < t → v t = vectorSelfsimilarHeatGainKernel 3 0 t u -
      ∫ s in (0 : ℝ)..t, projectedSelfsimilarHeatGainKernel 3 0 (t - s)
        (BoundedTransport.transport b c (v s)))
    {t : ℝ} (ht : 0 < t) : v t = profileGain0 b c t u :=
  eq_transportGain_of_duhamel _ hvc hvb hv ht

/-- The gaining path has the singular bound `C t^{-1/2} e^{ω t}` in operator norm. -/
theorem norm_profileGain0_le {t : ℝ} (ht : 0 < t) :
    ‖profileGain0 b c t‖ ≤ transportGainConstant (BoundedTransport.transport b c) *
      t ^ (-(1 / 2 : ℝ)) * Real.exp (transportWeight (BoundedTransport.transport b c) * t) :=
  norm_transportGain_le _ ht

/-- The gaining path of a field fixed by the Leray projection is fixed by the Sobolev Leray
projection. -/
theorem leraySobolev_profileGain0 {t : ℝ} (ht : 0 < t) {u : VectorH 3 0}
    (hu : leraySobolev 3 0 u = u) :
    leraySobolev 3 1 (profileGain0 b c t u) = profileGain0 b c t u :=
  leraySobolev_transportGain _ ht hu

/-! ### The semigroup -/

/-- The self-similar evolution around a profile with bounded transport coefficients `b` and
stretching coefficients `c`, as a strongly continuous semigroup on vector `L²`. Its generator
is `L₀ - Π B`, where `B v = Σᵢ bᵢ ∂ᵢ v + c v`. -/
def profileSemigroup0 (_hk : ProfileCoefficientBounds 0 b c) :
    StronglyContinuousSemigroup (VectorH 3 0) :=
  transportSemigroup (BoundedTransport.transport b c)

variable (hk : ProfileCoefficientBounds 0 b c)

/-- The profile semigroup is the free evolution perturbed by the bounded transport. -/
theorem profileSemigroup0_apply (t : ℝ≥0) :
    profileSemigroup0 b c hk t = transportSemigroup (BoundedTransport.transport b c) t :=
  rfl

/-- The gaining path restarted at a positive time solves the Volterra identity with the
evolved datum. -/
theorem profileGain0_add_forwardDuhamel {τ : ℝ} (hτ : 0 < τ) {s : ℝ≥0} (hs : 0 < (s : ℝ))
    (u : VectorH 3 0) :
    profileGain0 b c (τ + s) u + ∫ r in (0 : ℝ)..τ,
        transportKernel (BoundedTransport.transport b c) (τ - r) (profileGain0 b c (r + s) u) =
      vectorSelfsimilarHeatGainKernel 3 0 τ (profileSemigroup0 b c hk s u) :=
  transportGain_add_forwardDuhamel _ hτ hs u

/-- Restarting at a positive time: the gaining path at `t + s` is the gaining path at `t` of
the evolved datum. -/
theorem profileGain0_add {t : ℝ} (ht : 0 < t) {s : ℝ≥0} (hs : 0 < (s : ℝ)) (u : VectorH 3 0) :
    profileGain0 b c (t + s) u = profileGain0 b c t (profileSemigroup0 b c hk s u) :=
  transportGain_add _ ht hs u

/-- The Duhamel formula of the profile semigroup. The transport loses one derivative, so it acts
on the gaining path `profileGain0 b c s u` in `H¹`; the projected free gain returns to `H¹`, and
the integral is lowered to `L²`. -/
theorem profileSemigroup0_duhamel (t : ℝ≥0) (u : VectorH 3 0) :
    profileSemigroup0 b c hk t u = vectorSelfsimilarHeatSemigroup 3 0 t u -
      vectorLower 3 0 (∫ s in (0 : ℝ)..t, projectedSelfsimilarHeatGainKernel 3 0 (t - s)
        (BoundedTransport.transport b c (profileGain0 b c s u))) :=
  transportSemigroup_duhamel _ t u

/-- The Duhamel formula of the profile semigroup in `L²`, with the projected free evolution as
kernel. -/
theorem profileSemigroup0_duhamel_l2 (t : ℝ≥0) (u : VectorH 3 0) :
    profileSemigroup0 b c hk t u = vectorSelfsimilarHeatSemigroup 3 0 t u -
      ∫ s in (0 : ℝ)..t, leraySobolev 3 0 (vectorSelfsimilarHeat 3 0 (t - s).toNNReal
        (BoundedTransport.transport b c (profileGain0 b c s u))) :=
  transportSemigroup_duhamel_lower _ t u

/-- At positive time the profile semigroup is the gaining path with the gained derivative
forgotten. -/
theorem vectorLower_comp_profileGain0 {t : ℝ≥0} (ht : 0 < t) :
    (vectorLower 3 0).comp (profileGain0 b c t) = profileSemigroup0 b c hk t :=
  vectorLower_comp_transportGain _ ht

/-- The profile semigroup gains one derivative with the bound `C t^{-1/2} e^{ω t}`. -/
theorem profileSemigroup0_exists_gain :
    ∃ C ω : ℝ, 0 ≤ C ∧ ∀ t : ℝ≥0, 0 < t →
      ∃ G : VectorH 3 0 →L[ℝ] VectorH 3 1, (vectorLower 3 0).comp G = profileSemigroup0 b c hk t ∧
        ‖G‖ ≤ C * (t : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (ω * t) :=
  transportSemigroup_exists_gain _

/-- The profile semigroup has an exponential bound. -/
theorem profileSemigroup0_exists_norm_le :
    ∃ M ω : ℝ, 0 ≤ M ∧ ∀ t : ℝ≥0, ‖profileSemigroup0 b c hk t‖ ≤ M * Real.exp (ω * t) :=
  transportSemigroup_exists_norm_le _

/-- The profile semigroup preserves fields fixed by the Leray projection. -/
theorem leraySobolev_profileSemigroup0 (t : ℝ≥0) {u : VectorH 3 0}
    (hu : leraySobolev 3 0 u = u) :
    leraySobolev 3 0 (profileSemigroup0 b c hk t u) = profileSemigroup0 b c hk t u :=
  leraySobolev_transportSemigroup _ t hu

/-- The profile semigroup preserves divergence-free fields. -/
theorem profileSemigroup0_base_mem_solenoidal (t : ℝ≥0) {u : VectorH 3 0}
    (hu : l2SobolevRow (baseIndex 3 0) u ∈ l2Solenoidal 3) :
    l2SobolevRow (baseIndex 3 0) (profileSemigroup0 b c hk t u) ∈ l2Solenoidal 3 := by
  have hfix : leraySobolev 3 0 u = u := by
    apply l2SobolevRow_base_injective
    rw [l2SobolevRow_leraySobolev, lerayProjection_eq_self hu]
  rw [← leraySobolev_profileSemigroup0 b c hk t hfix, l2SobolevRow_leraySobolev]
  exact lerayProjection_mem 3 _

end NavierStokes.Selfsimilar
