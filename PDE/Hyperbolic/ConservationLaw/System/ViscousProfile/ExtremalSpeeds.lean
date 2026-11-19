/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Autonomous.EigenbasisTail
public import PDE.Hyperbolic.ConservationLaw.System.Characteristics.Ordered
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.FirstIntegral

/-!
# Extremal characteristic speed bounds for viscous profiles

A nonconstant viscous profile cannot approach a strict source at its right end or a
strict sink at its left end. The first integral, together with the ordered eigenbasis
at the relevant endpoint, therefore bounds its speed by the smallest right and largest
left characteristic speeds.

The field `x ↦ F(x) - F(u_l) - σ(x - u_l)` of the first integral is `G` from (13) in step 1
of the proof of Evans, §11.4.1, Theorem 1, and at either endpoint `u` its derivative
`DF(u) - σI` has the eigenvalues `λ_k(u) - σ`. The bounds say that `DG(u_r)` has an
eigenvalue `≤ 0` and `DG(u_l)` an eigenvalue `≥ 0`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.4.1, equations (10) and (13)-(15) and step 1 of the proof
  of Theorem 1.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace PDE.Hyperbolic.ConservationLaw.System

variable {m : ℕ} {flux : ℝ^(m + 1) → ℝ^(m + 1)}
  {uL uR : ℝ^(m + 1)} {speed : ℝ} {v : ℝ → ℝ^(m + 1)}

/-- A profile with distinct endpoints travels at least as fast as the smallest
characteristic speed of its right state. Only right-end hyperbolicity is needed. -/
theorem IsViscousProfile.smallest_characteristicSpeed_le (hv : IsViscousProfile flux uL uR speed v)
    (hflux : ContDiff ℝ 1 flux) (hne : uL ≠ uR) (hhyper : IsStrictlyHyperbolicAt flux uR) :
    characteristicSpeed flux 0 uR ≤ speed := by
  by_contra hle
  have hspeed : speed < characteristicSpeed flux 0 uR := lt_of_not_ge hle
  have hdiff := hflux.differentiable one_ne_zero
  let G : ℝ^(m + 1) → ℝ^(m + 1) := fun x ↦ flux x - flux uL - speed • (x - uL)
  have hG : ContDiff ℝ 1 G :=
    (hflux.sub contDiff_const).sub ((contDiff_id.sub contDiff_const).const_smul speed)
  have hzero : G uR = 0 := sub_eq_zero.mpr (hv.rankineHugoniot hdiff)
  have hGD : HasFDerivAt G (fderiv ℝ flux uR - speed • ContinuousLinearMap.id ℝ (ℝ^(m + 1))) uR :=
    ((hdiff uR).hasFDerivAt.sub_const _).sub (((hasFDerivAt_id uR).sub_const uL).const_smul speed)
  obtain ⟨horder, b, hb⟩ := characteristicSpeed_spec hhyper
  have heq : v = fun _ ↦ uR := by
    apply PDE.Analysis.Evolution.eq_const_of_tendsto_atTop_of_eigenbasis_pos b
      (a := fun k ↦ characteristicSpeed flux k uR - speed) hG.contDiffAt hzero
    · intro k
      simp only [hGD.fderiv, sub_apply, smul_apply, ContinuousLinearMap.id_apply, hb, sub_smul]
    · exact fun k ↦ sub_pos.mpr (hspeed.trans_le (horder.monotone (Fin.zero_le k)))
    · intro t
      simpa only [hv.first_integral hdiff, G] using
        (hv.contDiff.differentiable (by norm_num) t).hasDerivAt
    · exact hv.tendsto_atTop
  have hleft := hv.tendsto_atBot
  rw [heq] at hleft
  exact hne (tendsto_nhds_unique hleft tendsto_const_nhds)

/-- A profile with distinct endpoints travels at most as fast as the largest
characteristic speed of its left state. Only left-end hyperbolicity is needed. -/
theorem IsViscousProfile.le_largest_characteristicSpeed (hv : IsViscousProfile flux uL uR speed v)
    (hflux : ContDiff ℝ 1 flux) (hne : uL ≠ uR) (hhyper : IsStrictlyHyperbolicAt flux uL) :
    speed ≤ characteristicSpeed flux (Fin.last m) uL := by
  by_contra hle
  have hspeed : characteristicSpeed flux (Fin.last m) uL < speed := lt_of_not_ge hle
  have hdiff := hflux.differentiable one_ne_zero
  let G : ℝ^(m + 1) → ℝ^(m + 1) := fun x ↦ flux x - flux uL - speed • (x - uL)
  have hG : ContDiff ℝ 1 G :=
    (hflux.sub contDiff_const).sub ((contDiff_id.sub contDiff_const).const_smul speed)
  have hzero : G uL = 0 := by simp only [G, sub_self, smul_zero]
  have hGD : HasFDerivAt G (fderiv ℝ flux uL - speed • ContinuousLinearMap.id ℝ (ℝ^(m + 1))) uL :=
    ((hdiff uL).hasFDerivAt.sub_const _).sub (((hasFDerivAt_id uL).sub_const uL).const_smul speed)
  obtain ⟨horder, b, hb⟩ := characteristicSpeed_spec hhyper
  have heq : v = fun _ ↦ uL := by
    apply PDE.Analysis.Evolution.eq_const_of_tendsto_atBot_of_eigenbasis_neg b
      (a := fun k ↦ characteristicSpeed flux k uL - speed) hG.contDiffAt hzero
    · intro k
      simp only [hGD.fderiv, sub_apply, smul_apply, ContinuousLinearMap.id_apply, hb, sub_smul]
    · exact fun k ↦ sub_neg.mpr ((horder.monotone (Fin.le_last k)).trans_lt hspeed)
    · intro t
      simpa only [hv.first_integral hdiff, G] using
        (hv.contDiff.differentiable (by norm_num) t).hasDerivAt
    · exact hv.tendsto_atBot
  have hright := hv.tendsto_atTop
  rw [heq] at hright
  exact hne (tendsto_nhds_unique tendsto_const_nhds hright)

end PDE.Hyperbolic.ConservationLaw.System
