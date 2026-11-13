/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.LocalFreeField
public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.LocalPower.LowerPower.PhysicalCone
public import PDE.Analysis.Calculus.SignedPower
import CAS.ExactTactic

/-!
# Short-time uniqueness for bounded signed-power integral trajectories

Restriction to the physical cone converts an integral equation with
arbitrary free field to the Banach-space cone equation. The signed
power is Lipschitz on the bounded range of two trajectories. Absorption then
gives their equality, with a time restriction depending only on amplitude.
-/

@[expose] public noncomputable section

open Set MeasureTheory BoundedContinuousFunction PDE.Analysis
open WaveEquation.SmallData.Classical.LocalPower
open WaveEquation.SmallData.Classical.LocalPower.LowerPower
open scoped unitInterval

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- A forward integral trajectory with arbitrary free field satisfies the
normalized equation on each of its compact physical cones. -/
theorem physicalCone_eq_of_free_integral_eq {T : ℝ} {v : ℝ × ℝ^3 → ℝ}
    (hv : ContinuousOn v {p | |p.1| < T}) (H : C(ℝ × ℝ^3, ℝ)) (f : C(ℝ, ℝ))
    (heq : ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 T → v p = H p + p.1 ^ 2 * ∫ s : I,
      (1 - (s : ℝ)) * ((∫ θ : Direction, f (v (p.1 * (s : ℝ), p.2 + p.1 •
      ((1 - (s : ℝ)) • (θ : ℝ^3)))) ∂((volume : Measure (ℝ^3)).toSphere)) / unitSphereArea 3))
    (p : {p : ℝ × ℝ^3 | |p.1| < T}) (hp : 0 ≤ p.1.1) :
    physicalCone hv p = coneField H p.1 + p.1.1 ^ 2 •
      duhamelOperator (composeCompact f (physicalCone hv p)) := by
  ext q
  have hq : (physicalPoint p.1 q).1 ∈ Ico 0 T := ⟨mul_nonneg hp (coneTime_mem q).1,
      (le_abs_self _).trans_lt ((abs_physicalPoint_time_le p.1 q).trans_lt p.2)⟩
  rw [physicalCone_apply, heq _ hq]
  simp only [BoundedContinuousFunction.add_apply, BoundedContinuousFunction.smul_apply,
    coneField_apply, duhamelOperator_apply, composeCompact_apply, physicalCone_apply,
    physicalPoint_descend, smul_eq_mul]
  congr 1
  simp only [physicalPoint, rim, coneTime, coneSpace, mul_pow, mul_assoc]

/-- Two bounded cone solutions with the same free input coincide when the
elapsed-time factor absorbs the signed-power Lipschitz constant. -/
theorem eq_of_signedPower_cone_equations {r t M : ℝ} (hr : 1 ≤ r) (a u v : Cone →ᵇ ℝ) (hu : ‖u‖ ≤ M)
    (hv : ‖v‖ ≤ M) (hsmall : t ^ 2 * ‖duhamelOperator‖ * ((2 * r) * (2 * M) ^ (r - 1)) < 1) :
    let f : C(ℝ, ℝ) := ⟨fun z ↦ -Real.signedPower r z,
      (Real.continuous_signedPower (zero_lt_one.trans_le hr)).neg⟩
    let N := composeCompact (α := Cone) f
    u = a + t ^ 2 • duhamelOperator (N u) →
    v = a + t ^ 2 • duhamelOperator (N v) → u = v := by
  intro f N he₁ he₂
  let C := (2 * r) * (2 * M) ^ (r - 1)
  have hM : 0 ≤ M := (norm_nonneg u).trans hu
  have hC : 0 ≤ C := by positivity
  have hN : ‖N u - N v‖ ≤ C * ‖u - v‖ := by
    refine (BoundedContinuousFunction.norm_le (mul_nonneg hC (norm_nonneg _))).mpr fun q ↦ ?_
    change ‖-Real.signedPower r (u q) - -Real.signedPower r (v q)‖ ≤ _
    rw [neg_sub_neg, norm_sub_rev]
    have hsum : ‖u q‖ + ‖v q‖ ≤ 2 * M := by
      have h₁ := (u.norm_coe_le_norm q).trans hu
      have h₂ := (v.norm_coe_le_norm q).trans hv
      linarith
    apply (Real.norm_signedPower_sub_le hr (u q) (v q)).trans
    exact mul_le_mul (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) hsum (sub_nonneg.mpr hr)) (by positivity))
      ((u - v).norm_coe_le_norm q) (norm_nonneg _) hC
  have he : u - v = t ^ 2 • duhamelOperator (N u - N v) := by
    calc
      u - v = (a + t ^ 2 • duhamelOperator (N u)) -
          (a + t ^ 2 • duhamelOperator (N v)) := congrArg₂ (fun x y ↦ x - y) he₁ he₂
      _ = t ^ 2 • duhamelOperator (N u - N v) := by
        rw [add_sub_add_left_eq_sub, map_sub, smul_sub]
  have hn : ‖u - v‖ ≤ (t ^ 2 * ‖duhamelOperator‖ * C) * ‖u - v‖ := by
    calc
      ‖u - v‖ = t ^ 2 * ‖duhamelOperator (N u - N v)‖ := by
        conv_lhs => rw [he]
        rw [norm_smul, Real.norm_of_nonneg (sq_nonneg t)]
      _ ≤ t ^ 2 * (‖duhamelOperator‖ * (C * ‖u - v‖)) := by
        gcongr
        exact (duhamelOperator.le_opNorm _).trans (mul_le_mul_of_nonneg_left hN (norm_nonneg _))
      _ = _ := by cas
  have hz : ‖u - v‖ = 0 := le_antisymm (by nlinarith [norm_nonneg (u - v)]) (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

/-- Bounded continuous physical trajectories with the same free field agree
at every point whose backward cone is short enough for amplitude absorption. -/
theorem eq_of_bounded_signedPower_integral_eq {r T M : ℝ} (hr : 1 ≤ r) (hM : 0 ≤ M)
    {u v : ℝ × ℝ^3 → ℝ} (hu : ContinuousOn u {q | |q.1| < T}) (hv : ContinuousOn v {q | |q.1| < T})
    (H : C(ℝ × ℝ^3, ℝ)) (huB : ∀ q : ℝ × ℝ^3, q.1 ∈ Ico 0 T → |u q| ≤ M)
    (hvB : ∀ q : ℝ × ℝ^3, q.1 ∈ Ico 0 T → |v q| ≤ M) {p : ℝ × ℝ^3} (hp : p.1 ∈ Ico 0 T)
    (hsmall : p.1 ^ 2 * ‖duhamelOperator‖ * ((2 * r) * (2 * M) ^ (r - 1)) < 1) :
    let f : C(ℝ, ℝ) := ⟨fun z ↦ -Real.signedPower r z,
      (Real.continuous_signedPower (zero_lt_one.trans_le hr)).neg⟩
    (∀ q : ℝ × ℝ^3, q.1 ∈ Ico 0 T →
      u q = H q + q.1 ^ 2 * ∫ s : I, (1 - (s : ℝ)) *
        ((∫ θ : Direction,
          f (u (q.1 * (s : ℝ), q.2 + q.1 • ((1 - (s : ℝ)) • (θ : ℝ^3))))
            ∂((volume : Measure (ℝ^3)).toSphere)) / unitSphereArea 3)) →
    (∀ q : ℝ × ℝ^3, q.1 ∈ Ico 0 T →
      v q = H q + q.1 ^ 2 * ∫ s : I, (1 - (s : ℝ)) *
        ((∫ θ : Direction,
          f (v (q.1 * (s : ℝ), q.2 + q.1 • ((1 - (s : ℝ)) • (θ : ℝ^3))))
            ∂((volume : Measure (ℝ^3)).toSphere)) / unitSphereArea 3)) → u p = v p := by
  intro f hue hve
  let q : {q : ℝ × ℝ^3 | |q.1| < T} :=
    ⟨p, by change |p.1| < T; simpa only [abs_of_nonneg hp.1] using hp.2⟩
  have htime (z : Cone) : (physicalPoint p z).1 ∈ Ico 0 T := ⟨mul_nonneg hp.1 (coneTime_mem z).1,
      (mul_le_mul_of_nonneg_left (coneTime_mem z).2 hp.1).trans_lt (by simpa using hp.2)⟩
  have huN : ‖physicalCone hu q‖ ≤ M :=
    (BoundedContinuousFunction.norm_le hM).mpr fun z ↦ huB _ (htime z)
  have hvN : ‖physicalCone hv q‖ ≤ M :=
    (BoundedContinuousFunction.norm_le hM).mpr fun z ↦ hvB _ (htime z)
  have he := eq_of_signedPower_cone_equations hr (coneField H p)
    (physicalCone hu q) (physicalCone hv q) huN hvN hsmall
    (physicalCone_eq_of_free_integral_eq hu H f hue q hp.1)
    (physicalCone_eq_of_free_integral_eq hv H f hve q hp.1)
  have hvtx := congrArg (fun w : Cone →ᵇ ℝ ↦ w vertex) he
  simpa only [physicalCone_apply, physicalPoint, vertex, coneTime, coneSpace,
    mul_one, smul_zero, add_zero] using hvtx

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
