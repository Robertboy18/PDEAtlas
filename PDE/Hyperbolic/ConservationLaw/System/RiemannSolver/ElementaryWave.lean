/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.WaveCurve
public import PDE.Hyperbolic.ConservationLaw.System.PlanarShock
public import PDE.Hyperbolic.ConservationLaw.InitialValueWeakForm

/-!
# Elementary connections realized by spacetime profiles

`IsElementaryWave` identifies a profile with a constant state, a Lax shock,
a contact discontinuity, or a rarefaction along a specified characteristic
curve. In the rarefaction case the values on every ray through that curve
are recorded, including both fan edges. Thus the connection witness and
the spacetime wave describe the same states throughout the fan.

These are the waves of Evans, §11.2: centered rarefaction waves (Theorem 1 of §11.2.2),
contact discontinuities (32)-(34), and shock waves admissible in the sense of (42), both in
§11.2.3(b). The proof of Theorem 4 in §11.2.4 joins nearby states by such waves.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.2.2, Theorem 1; §11.2.3(b), equations (32)-(42);
  §11.2.4, Theorem 4.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System

open Set

variable {m : ℕ} {flux : ℝ^m → ℝ^m}

/-- A spacetime profile realizing an admissible elementary connection.
Rarefactions carry their entire characteristic-curve witness and its values
on positive-time rays. -/
inductive IsElementaryWave (fields : Fin m → CharacteristicField flux) (k : Fin m) :
    ℝ^m → ℝ^m → (ℝ^2 → ℝ^m) → Prop
  | same (state : ℝ^m) :
      IsElementaryWave fields k state state (fun _ ↦ state)
  | shock {left right : ℝ^m} (speed : ℝ) (h : LaxShock fields k left right speed) :
      IsElementaryWave fields k left right (planarShock left right speed)
  | contact {left right : ℝ^m} (speed : ℝ)
      (h : ContactDiscontinuity (fields k) left right speed) :
      IsElementaryWave fields k left right (planarShock left right speed)
  | rarefaction {left right : ℝ^m} {u : ℝ^2 → ℝ^m}
      (curve : ℝ → ℝ^m) (strength : ℝ) (interval : Set ℝ)
      (hopen : IsOpen interval) (hsegment : uIcc 0 strength ⊆ interval)
      (hreg : ContDiffOn ℝ 1 curve interval) (hleft : curve 0 = left)
      (hflow : IsIntegralCurveOn curve (fields k).vectorField interval)
      (hright : curve strength = right)
      (hmono : StrictMonoOn
        (fun θ : ℝ ↦ (fields k).speed (curve (θ * strength))) (Icc 0 1))
      (hspeed : ContinuousOn (fun s ↦ (fields k).speed (curve s)) interval)
      (houterLeft : ∀ p : ℝ^2, 0 < p 0 →
        p 1 < (fields k).speed left * p 0 → u p = left)
      (houterRight : ∀ p : ℝ^2, 0 < p 0 →
        (fields k).speed right * p 0 ≤ p 1 → u p = right)
      (hcurve : ∀ θ ∈ Icc (0 : ℝ) 1, ∀ t : ℝ, 0 < t →
        u (AffineInterface.interface ((fields k).speed (curve (θ * strength))) t) =
          curve (θ * strength)) :
      IsElementaryWave fields k left right u

/-- Forgetting a realized profile recovers the elementary-connection
predicate, with exactly the same shock, contact, or rarefaction witness. -/
theorem IsElementaryWave.isElementaryConnection {fields : Fin m → CharacteristicField flux}
    {k : Fin m} {left right : ℝ^m} {u : ℝ^2 → ℝ^m} (h : IsElementaryWave fields k left right u) :
    IsElementaryConnection fields k left right := by
  cases h with
  | same => exact .same _
  | shock speed h => exact .shock speed h
  | contact speed h => exact .contact speed h
  | rarefaction curve strength interval hopen hsegment hreg hleft hflow hright hmono _ _ _ _ =>
    exact .rarefaction
      ⟨curve, strength, interval, hopen, hsegment, hreg, hleft, hflow, hright, hmono⟩

/-- An elementary connection with decreasing characteristic speed must be
a Lax shock. This recovers the shock witness from an admissible local wave
transformation without imposing a separate shock parametrization. -/
theorem IsElementaryConnection.exists_laxShock_of_speed_lt
    {fields : Fin m → CharacteristicField flux} {k : Fin m}
    {left right : ℝ^m} (h : IsElementaryConnection fields k left right)
    (hspeed : (fields k).speed right < (fields k).speed left) :
    ∃ speed : ℝ, LaxShock fields k left right speed := by
  cases h with
  | same => exact (lt_irrefl _ hspeed).elim
  | rarefaction h => exact (lt_asymm hspeed h.speed_lt).elim
  | shock speed h => exact ⟨speed, h⟩
  | contact speed h =>
    exact (ne_of_lt hspeed (h.2.2.symm.trans h.2.1)).elim

/-- A fixed rarefaction curve determines its entire positive-time profile.
Continuity of the speed ensures that the sampled rays cover the fan.
This is uniqueness for the specified curve and outer states, not uniqueness
of a weak initial-value problem. -/
theorem eq_on_forwardHalfSpace_of_rarefaction_rays {speed : ℝ^m → ℝ} {curve : ℝ → ℝ^m}
    {strength : ℝ} {left right : ℝ^m} {u v : ℝ^2 → ℝ^m} (hleft : curve 0 = left)
    (hright : curve strength = right)
    (hcontinuous : ContinuousOn (fun θ : ℝ ↦ speed (curve (θ * strength))) (Icc 0 1))
    (huLeft : ∀ p : ℝ^2, 0 < p 0 → p 1 < speed left * p 0 → u p = left)
    (hvLeft : ∀ p : ℝ^2, 0 < p 0 → p 1 < speed left * p 0 → v p = left)
    (huRight : ∀ p : ℝ^2, 0 < p 0 → speed right * p 0 ≤ p 1 → u p = right)
    (hvRight : ∀ p : ℝ^2, 0 < p 0 → speed right * p 0 ≤ p 1 → v p = right)
    (huCurve : ∀ θ ∈ Icc (0 : ℝ) 1, ∀ t : ℝ, 0 < t →
      u (AffineInterface.interface (speed (curve (θ * strength))) t) = curve (θ * strength))
    (hvCurve : ∀ θ ∈ Icc (0 : ℝ) 1, ∀ t : ℝ, 0 < t →
      v (AffineInterface.interface (speed (curve (θ * strength))) t) = curve (θ * strength)) :
    EqOn u v forwardHalfSpace := by
  intro p hp
  by_cases hl : p 1 < speed left * p 0
  · exact (huLeft p hp hl).trans (hvLeft p hp hl).symm
  by_cases hr : speed right * p 0 ≤ p 1
  · exact (huRight p hp hr).trans (hvRight p hp hr).symm
  have hξ : p 1 / p 0 ∈ Icc
      (speed (curve (0 * strength))) (speed (curve (1 * strength))) := by
    simpa only [mem_Icc, zero_mul, one_mul, hleft, hright] using
      And.intro ((le_div_iff₀ hp).mpr (le_of_not_gt hl)) ((div_le_iff₀ hp).mpr (le_of_not_ge hr))
  obtain ⟨θ, hθ, heq⟩ := intermediate_value_Icc zero_le_one hcontinuous hξ
  change speed (curve (θ * strength)) = p 1 / p 0 at heq
  have hpoint : AffineInterface.interface (speed (curve (θ * strength))) (p 0) = p := by
    ext i
    fin_cases i
    · rfl
    · change speed (curve (θ * strength)) * p 0 = p 1
      rw [heq, div_mul_cancel₀ _ hp.ne']
  exact ((congrArg u hpoint).symm.trans (huCurve θ hθ (p 0) hp)).trans
    (((congrArg v hpoint).symm.trans (hvCurve θ hθ (p 0) hp)).symm)

end PDE.Hyperbolic.ConservationLaw.System
