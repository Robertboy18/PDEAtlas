/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Nonuniqueness.Symmetry.Action
public import PDE.Analysis.Calculus.ParametricIntervalRegularity.Derivatives
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Averaging test fields over the axisymmetry group

The rotation average of a smooth compactly supported field is
`rotationAverage φ x = ∫₀¹ R_{2πt} φ(R_{2πt}⁻¹ x) dt`. The integrand is jointly smooth in `(x, t)`,
so the average is smooth and its derivatives are the averages of the derivatives
(`PDE.Calculus.fderiv_intervalAverage`, `PDE.Calculus.laplacian_intervalAverage`). The support
stays in the same centred ball, and the divergence of the average is the average of the
divergences, so the rotation average of a solenoidal test field is a solenoidal test field.
By periodicity of the rotations it is fixed by every rotation.

`sectorAverage odd φ = ½ (A φ + parity odd • σ (A φ) σ)`, with `A` the rotation average,
combines it with the reflection. It is again a solenoidal test field, and it lies in the
sector of its parity: even axisymmetric for `odd = false` and odd axisymmetric for `odd = true`,
at every point (`act_sectorAverage`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Real
open PDE.CoordinateSystems (axialRotation equatorialReflection)
open NavierStokes.Nonuniqueness

namespace NavierStokes.Symmetry

set_option linter.missingDocs true

variable {φ : ℝ^3 → ℝ^3}

/-! ### Rotations -/

/-- The action of a rotation is `2π`-periodic in the angle. -/
theorem act_add_two_pi (θ : ℝ) (s : Bool) (u : ℝ^3 → ℝ^3) :
    act (θ + 2 * π) s u = act θ s u := by
  funext x
  cases s <;> simp only [act_apply, groupElement_false, groupElement_true,
    PDE.CoordinateSystems.axialRotation_add_two_pi]

/-- Composing two rotation actions rotates through the sum of the angles. -/
theorem act_false_act_false (α β : ℝ) (u : ℝ^3 → ℝ^3) :
    act α false (act β false u) = act (α + β) false u := by
  funext x
  simp only [act, groupElement_false, PDE.CoordinateSystems.axialRotation_add,
    LinearIsometryEquiv.trans_apply]
  rfl

/-! ### The rotation average -/

/-- The jointly smooth family `(x, t) ↦ R_{2πt} φ(R_{2πt}⁻¹ x)` averaged by `rotationAverage`. -/
def rotationFamily (φ : ℝ^3 → ℝ^3) : ℝ^3 × ℝ → ℝ^3 :=
  fun q ↦ act (2 * π * q.2) false φ q.1

/-- The rotation family of a smooth field is jointly smooth. -/
theorem contDiff_rotationFamily (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ContDiff ℝ (⊤ : ℕ∞) (rotationFamily φ) := by
  have hangle : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ^3 × ℝ ↦ 2 * π * q.2) :=
    contDiff_const.mul contDiff_snd
  have hneg : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ^3 × ℝ ↦ -(2 * π * q.2)) := hangle.neg
  have hfst : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ^3 × ℝ ↦ q.1) := contDiff_fst
  have hpair := hneg.prodMk hfst
  have hinv := PDE.CoordinateSystems.contDiff_axialRotation_apply.comp hpair
  have hvalue := hφ.comp hinv
  have hpair' := hangle.prodMk hvalue
  have hall := PDE.CoordinateSystems.contDiff_axialRotation_apply.comp hpair'
  have hform : rotationFamily φ =
      fun q ↦ axialRotation (2 * π * q.2) (φ (axialRotation (-(2 * π * q.2)) q.1)) := by
    funext q
    simp only [rotationFamily, act_false, PDE.CoordinateSystems.axialRotation_symm]
  rw [hform]
  exact hall

/-- The average of a field over the rotations about the third axis,
`∫₀¹ R_{2πt} φ(R_{2πt}⁻¹ x) dt`. -/
def rotationAverage (φ : ℝ^3 → ℝ^3) (x : ℝ^3) : ℝ^3 :=
  ∫ t in (0 : ℝ)..1, act (2 * π * t) false φ x

/-- The rotation average is the interval average of the rotation family. -/
theorem rotationAverage_eq (φ : ℝ^3 → ℝ^3) :
    rotationAverage φ = fun x ↦ ∫ t in (0 : ℝ)..1, rotationFamily φ (x, t) :=
  rfl

/-- The divergence of a differentiable field is the sum of the diagonal coordinate derivatives
of its components. -/
private theorem divergence_eq_sum_partialDeriv {u : ℝ^3 → ℝ^3} {x : ℝ^3}
    (hu : DifferentiableAt ℝ u x) :
    PDE.divergence u x = ∑ i, (PDE.partialDeriv i u x) i := by
  unfold PDE.divergence
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  exact (PDE.partialDeriv_apply i i hu).symm

/-- The rotation average of a solenoidal test field is a solenoidal test field. -/
theorem _root_.NavierStokes.Nonuniqueness.IsSolenoidalTestField.rotationAverage
    (hφ : IsSolenoidalTestField φ) : IsSolenoidalTestField (rotationAverage φ) := by
  have hfam := contDiff_rotationFamily hφ.1
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (Symmetry.rotationAverage φ) :=
    PDE.Calculus.contDiff_intervalAverage hfam
  refine ⟨hsmooth, ?_, fun x ↦ ?_⟩
  · obtain ⟨R, hR⟩ := hφ.2.1.isCompact.isBounded.subset_closedBall (0 : ℝ^3)
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ^3) R) fun x hx ↦ ?_
    have hzero (t : ℝ) : act (2 * π * t) false φ x = 0 := by
      have hnot : (axialRotation (2 * π * t)).symm x ∉ tsupport φ := by
        intro hmem
        apply hx
        simpa only [Metric.mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map]
          using hR hmem
      simp only [act_false]
      rw [image_eq_zero_of_notMem_tsupport hnot, map_zero]
    simp only [Symmetry.rotationAverage, hzero, intervalIntegral.integral_zero]
  · have hdiff : DifferentiableAt ℝ (Symmetry.rotationAverage φ) x :=
      (hsmooth.differentiable (by simp)) x
    rw [divergence_eq_sum_partialDeriv hdiff]
    have hslice (t : ℝ) : DifferentiableAt ℝ (fun y ↦ rotationFamily φ (y, t)) x :=
      ((contDiff_act (θ := 2 * π * t) (s := false) hφ.1).differentiable (by simp)) x
    have hline : Continuous (fun t : ℝ ↦ (x, t)) := continuous_const.prodMk continuous_id
    have hcont (i : Fin 3) : Continuous
        (fun t ↦ PDE.partialDeriv i (fun y ↦ rotationFamily φ (y, t)) x) := by
      have h := (PDE.Calculus.contDiff_partialDeriv_slice hfam i).continuous.comp hline
      exact h
    have hcomp (i : Fin 3) : (PDE.partialDeriv i (Symmetry.rotationAverage φ) x) i =
        ∫ t in (0 : ℝ)..1, (PDE.partialDeriv i (fun y ↦ rotationFamily φ (y, t)) x) i := by
      rw [rotationAverage_eq, PDE.Calculus.partialDeriv_intervalAverage hfam]
      exact ((EuclideanSpace.proj i : ℝ^3 →L[ℝ] ℝ).intervalIntegral_comp_comm
        ((hcont i).intervalIntegrable (μ := volume) 0 1)).symm
    simp only [hcomp]
    have hci (i : Fin 3) : Continuous
        (fun t ↦ (PDE.partialDeriv i (fun y ↦ rotationFamily φ (y, t)) x) i) := by
      have h := (EuclideanSpace.proj i : ℝ^3 →L[ℝ] ℝ).continuous.comp (hcont i)
      exact h
    rw [← intervalIntegral.integral_finsetSum fun i _ ↦
      (hci i).intervalIntegrable (μ := volume) 0 1]
    have hdiv (t : ℝ) :
        ∑ i, (PDE.partialDeriv i (fun y ↦ rotationFamily φ (y, t)) x) i = 0 := by
      rw [← divergence_eq_sum_partialDeriv (hslice t)]
      exact (hφ.act (2 * π * t) false).2.2 x
    simp only [hdiv, intervalIntegral.integral_zero]

/-- The rotation family is continuous in the angle parameter at a fixed point. -/
private theorem continuous_rotationFamily_slice (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x : ℝ^3) :
    Continuous (fun t ↦ act (2 * π * t) false φ x) := by
  have hline : Continuous (fun t : ℝ ↦ (x, t)) := continuous_const.prodMk continuous_id
  have h := (contDiff_rotationFamily hφ).continuous.comp hline
  exact h

/-- The rotation average of a smooth field is fixed by every rotation. -/
theorem act_rotationAverage (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (α : ℝ) :
    act α false (rotationAverage φ) = rotationAverage φ := by
  funext x
  have hcomm := (groupCLM α false).intervalIntegral_comp_comm
    ((continuous_rotationFamily_slice hφ ((groupElement α false).symm x)).intervalIntegrable
      (μ := volume) 0 1)
  have hstart : act α false (rotationAverage φ) x =
      groupCLM α false (∫ t in (0 : ℝ)..1, act (2 * π * t) false φ
        ((groupElement α false).symm x)) :=
    rfl
  rw [hstart, ← hcomm]
  have hpi : (2 * π : ℝ) ≠ 0 := by positivity
  have hshift (t : ℝ) : groupCLM α false (act (2 * π * t) false φ
      ((groupElement α false).symm x)) = act (2 * π * (t + α / (2 * π))) false φ x := by
    have h := congrFun (act_false_act_false α (2 * π * t) φ) x
    have hangle : 2 * π * (t + α / (2 * π)) = α + 2 * π * t := by
      rw [mul_add, mul_div_cancel₀ α hpi, add_comm]
    rw [hangle, ← h]
    rfl
  simp only [hshift]
  rw [intervalIntegral.integral_comp_add_right (fun t ↦ act (2 * π * t) false φ x)]
  have hper : Function.Periodic (fun t ↦ act (2 * π * t) false φ x) 1 := by
    intro t
    simp only [mul_add, mul_one, act_add_two_pi]
  have h := Function.Periodic.intervalIntegral_add_eq hper (α / (2 * π)) 0
  rw [zero_add, add_comm 1, h, zero_add]
  rfl

/-! ### Sector averages -/

/-- The average of a field over the axisymmetry group with the character of the sector:
`½ (A φ + parity odd • σ (A φ) σ)` with `A` the rotation average. -/
def sectorAverage (odd : Bool) (φ : ℝ^3 → ℝ^3) : ℝ^3 → ℝ^3 :=
  (1 / 2 : ℝ) • (rotationAverage φ + parity odd • act 0 true (rotationAverage φ))

/-- The sector average of a solenoidal test field is a solenoidal test field. -/
theorem _root_.NavierStokes.Nonuniqueness.IsSolenoidalTestField.sectorAverage
    (hφ : IsSolenoidalTestField φ) (odd : Bool) :
    IsSolenoidalTestField (Symmetry.sectorAverage odd φ) :=
  (hφ.rotationAverage.add ((hφ.rotationAverage.act 0 true).smul _)).smul _

/-- The rotation-invariant field `ψ` and its reflection `σ ψ σ` are permuted by the group. -/
private theorem act_of_rotation_invariant {ψ : ℝ^3 → ℝ^3} (hψ : ∀ α, act α false ψ = ψ)
    (θ : ℝ) :
    act θ false (act 0 true ψ) = act 0 true ψ ∧ act θ true ψ = act 0 true ψ ∧
      act θ true (act 0 true ψ) = ψ := by
  have hrefl (y : ℝ^3) : act 0 true ψ y = equatorialReflection (ψ (equatorialReflection y)) := by
    rw [act_true_apply, act_zero_false]
  have h1 : act θ false (act 0 true ψ) = act 0 true ψ := by
    funext x
    have h : axialRotation θ (ψ ((axialRotation θ).symm (equatorialReflection x))) =
        ψ (equatorialReflection x) :=
      congrFun (hψ θ) (equatorialReflection x)
    have hstart : act θ false (act 0 true ψ) x =
        axialRotation θ (act 0 true ψ ((axialRotation θ).symm x)) :=
      rfl
    rw [hstart, hrefl, PDE.CoordinateSystems.equatorialReflection_axialRotation_symm,
      ← PDE.CoordinateSystems.equatorialReflection_axialRotation, h, hrefl]
  refine ⟨h1, funext fun x ↦ ?_, funext fun x ↦ ?_⟩
  · rw [act_true_apply, hψ, hrefl]
  · rw [act_true_apply, h1, hrefl,
      PDE.CoordinateSystems.equatorialReflection_equatorialReflection,
      PDE.CoordinateSystems.equatorialReflection_equatorialReflection]

/-- Every group element acts on the sector average by the character of the sector, at every
point. -/
theorem act_sectorAverage (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (odd : Bool) (θ : ℝ) (s : Bool) :
    act θ s (sectorAverage odd φ) = parity (odd && s) • sectorAverage odd φ := by
  obtain ⟨h1, h2, h3⟩ := act_of_rotation_invariant (act_rotationAverage hφ) θ
  have hψ := act_rotationAverage hφ θ
  unfold sectorAverage
  rw [act_smul, act_add, act_smul]
  cases s
  · rw [hψ, h1, Bool.and_false, parity_false, one_smul]
  · rw [h2, h3, Bool.and_true]
    cases odd
    · simp only [parity_false, one_smul]
      module
    · simp only [parity_true]
      module

/-- The sector average lies in the sector of its parity. -/
theorem isInSector_sectorAverage (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (odd : Bool) :
    IsInSector odd (sectorAverage odd φ) := fun θ s ↦
  Filter.EventuallyEq.of_eq (act_sectorAverage hφ odd θ s)

end NavierStokes.Symmetry
