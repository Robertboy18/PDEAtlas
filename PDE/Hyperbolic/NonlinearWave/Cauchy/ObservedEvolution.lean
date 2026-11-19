/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Duhamel.Differentiability
public import PDE.Analysis.Evolution.Semigroup.Semilinear.Restart
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Weak observations of semigroup trajectories

Suppose bounded maps `Q` and `R` satisfy `Q A = R` on the dense domain of the
generator `A`. Then every orbit satisfies the integrated equation after applying `Q`,
even when the initial state is outside that domain. The argument first integrates
domain-valued orbits and then uses density.

Continuous forcing has a right derivative after applying `Q`. Restarting the Duhamel formula reduces
this assertion to the derivative of a shrinking integral at time zero.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology Interval

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

open PDE.Analysis.Evolution

variable {E Z : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]

/-- A bounded observation of the generator determines the integrated equation for
all initial states, by density of the generator domain. -/
theorem observed_orbit_integral (S : StronglyContinuousSemigroup E) (Q R : E →L[ℝ] Z)
    (hdense : Dense (S.generatorPMap.domain : Set E))
    (hQR : ∀ x y, S.HasGeneratorAt x y → Q y = R x) (x : E) (t : NNReal) :
    (∫ s in (0 : ℝ)..(t : ℝ), R (S.realOrbit x s)) = Q (S t x) - Q x := by
  have hclosed : IsClosed {x : E | R (S.integratedOperator t x) = Q (S t x) - Q x} :=
    isClosed_eq (R.continuous.comp (S.integratedOperator t).continuous)
      ((Q.continuous.comp (S t).continuous).sub Q.continuous)
  have hall : R (S.integratedOperator t x) = Q (S t x) - Q x := by
    refine hdense.induction (fun y hy ↦ ?_) hclosed x
    let z : S.generatorPMap.domain := ⟨y, hy⟩
    have hz := S.hasGeneratorAt_generatorPMap z
    rw [← map_sub, ← S.integratedOperator_generatorPMap t z]
    simp only [StronglyContinuousSemigroup.integratedOperator_apply]
    rw [← R.intervalIntegral_comp_comm ((S.continuous_realOrbit y).intervalIntegrable _ _),
      ← Q.intervalIntegral_comp_comm
        ((S.continuous_realOrbit (S.generatorPMap z)).intervalIntegrable _ _)]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le t.coe_nonneg] at hs
    exact (hQR _ _ (hz.map s.toNNReal)).symm
  rw [StronglyContinuousSemigroup.integratedOperator_apply,
    ← R.intervalIntegral_comp_comm ((S.continuous_realOrbit x).intervalIntegrable _ _)] at hall
  exact hall

/-- The weakly observed orbit has the expected right derivative at zero for
arbitrary initial states. -/
theorem observed_orbit_derivative_zero (S : StronglyContinuousSemigroup E)
    (Q R : E →L[ℝ] Z) (hdense : Dense (S.generatorPMap.domain : Set E))
    (hQR : ∀ x y, S.HasGeneratorAt x y → Q y = R x) (x : E) :
    HasDerivWithinAt (fun t : ℝ ↦ Q (S.realOrbit x t)) (R x) (Ici 0) 0 := by
  have hc : Continuous (fun s ↦ R (S.realOrbit x s)) := R.continuous.comp (S.continuous_realOrbit x)
  have hd := ((hc.integral_hasStrictDerivAt 0 0).hasDerivAt.add_const
    (Q x)).hasDerivWithinAt (s := Ici 0)
  simp only [StronglyContinuousSemigroup.realOrbit_zero] at hd
  apply hd.congr_of_mem _ (show (0 : ℝ) ∈ Ici 0 from le_rfl)
  intro t ht
  have h := observed_orbit_integral S Q R hdense hQR x t.toNNReal
  rw [Real.coe_toNNReal _ ht] at h
  exact (eq_sub_iff_add_eq.mp h).symm

/-- Restarting a forced orbit gives its weak right derivative at every
nonnegative time, including for initial states outside the generator domain. -/
theorem observed_forced_derivative (S : StronglyContinuousSemigroup E)
    (Q R : E →L[ℝ] Z) (hdense : Dense (S.generatorPMap.domain : Set E))
    (hQR : ∀ x y, S.HasGeneratorAt x y → Q y = R x)
    {f : ℝ → E} (hf : Continuous f) (x : E) {t : ℝ} (ht : 0 ≤ t) :
    let z := fun s ↦ S.realOrbit x s + S.duhamel f s
    HasDerivWithinAt (fun s ↦ Q (z s)) (R (z t) + Q (f t)) (Ici t) t := by
  let z := fun s ↦ S.realOrbit x s + S.duhamel f s
  let g := fun s ↦ f (t + s)
  have hg : Continuous g := hf.comp (continuous_const.add continuous_id)
  have horbit := observed_orbit_derivative_zero S Q R hdense hQR (z t)
  have hforce := Q.hasFDerivAt.comp_hasDerivAt 0 (S.hasDerivAt_duhamel_zero hg)
  have hshift : HasDerivWithinAt (fun s : ℝ ↦ s - t) 1 (Ici t) t :=
    ((hasDerivAt_id t).sub_const t).hasDerivWithinAt
  have hmaps : MapsTo (fun s : ℝ ↦ s - t) (Ici t) (Ici 0) := fun s hs ↦ sub_nonneg.mpr hs
  have hd := (horbit.add hforce.hasDerivWithinAt).scomp_of_eq t hshift hmaps (sub_self t).symm
  simp only [one_smul, g, add_zero, Function.comp_def] at hd
  apply hd.congr_of_mem _ (show t ∈ Ici t from le_rfl)
  intro s hs
  have hlag : 0 ≤ s - t := sub_nonneg.mpr hs
  have hrestart : z s = S (s - t).toNNReal (z t) + S.duhamel g (s - t) := by
    have h := S.duhamel_add hf ht hlag
    rw [add_sub_cancel] at h
    change S s.toNNReal x + S.duhamel f s =
      S (s - t).toNNReal (S t.toNNReal x + S.duhamel f t) + S.duhamel g (s - t)
    rw [h, map_add, ← S.map_add_apply, ← Real.toNNReal_add hlag ht, sub_add_cancel]
    exact (add_assoc _ _ _).symm
  change Q (z s) = Q (S (s - t).toNNReal (z t)) + Q (S.duhamel g (s - t))
  rw [hrestart, map_add]

/-- The Duhamel curve satisfies the integrated equation in the weak observation
space. This connects the constructed semigroups to the weak energy formulation. -/
theorem observed_forced_integral (S : StronglyContinuousSemigroup E)
    (Q R : E →L[ℝ] Z) (hdense : Dense (S.generatorPMap.domain : Set E))
    (hQR : ∀ x y, S.HasGeneratorAt x y → Q y = R x)
    {f : ℝ → E} (hf : Continuous f) (x : E) {t : ℝ} (ht : 0 ≤ t) :
    let z := fun s ↦ S.realOrbit x s + S.duhamel f s
    (∫ s in (0 : ℝ)..t, R (z s) + Q (f s)) = Q (z t) - Q x := by
  let z := fun s ↦ S.realOrbit x s + S.duhamel f s
  have hz : Continuous z := (S.continuous_realOrbit x).add (S.continuous_duhamel hf)
  have hd (s : ℝ) (hs : s ∈ Ioo 0 t) :
      HasDerivWithinAt (fun r ↦ Q (z r)) (R (z s) + Q (f s)) (Ioi s) s :=
    (observed_forced_derivative S Q R hdense hQR hf x hs.1.le).mono Ioi_subset_Ici_self
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht
    (Q.continuous.comp hz).continuousOn hd
    (((R.continuous.comp hz).add (Q.continuous.comp hf)).intervalIntegrable 0 t)
  simpa only [Function.comp_apply, z, StronglyContinuousSemigroup.realOrbit_zero,
    StronglyContinuousSemigroup.duhamel_zero, add_zero] using h

end PDE.Hyperbolic.NonlinearWave.Cauchy
