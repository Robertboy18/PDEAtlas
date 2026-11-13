/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Nonuniqueness.ClassicalProfile
import PDE.Analysis.Integration.CompactByPartsCoordinates
import PDE.FDeriv.PartialDeriv.Smooth
import PDE.Analysis.MeasureTheory.Function.LocalL2

/-!
# The weak eigenvalue density of a field smooth off the origin

Let `B` be a continuous field on `ℝ³` that is `C¹` and divergence free away from the origin, and
let `v ∈ H¹(ℝ³)³` have a representative `V` with the same properties. If the classical partials
of `B` and `V` are locally integrable and those of `V` represent the weak gradient of `v`, then
the weak eigenvalue density at `μ = 0` tested with a smooth compactly supported field `φ` is
integrable, and its integral is the pairing of `V` with the formal adjoint `profileAdjoint B φ`
of the linearization at `B`
(`integral_weakEigenDensity_eq_integral_inner_profileAdjoint`). The trace term vanishes because
`div V = 0` off the origin, and the remaining derivatives of `V` are moved onto `φ` by three
integrations by parts, which the single point where `V` may fail to be smooth does not
obstruct. If `V` is moreover `C²` off the origin with locally integrable diagonal second
partials, the integral is the pairing of the linearized operator
`-½(V + ξ·∇V) + (B·∇)V + (V·∇)B - ΔV` with `φ`
(`integral_weakEigenDensity_eq_integral_inner_stationaryVelocityLinearization`).
-/

@[expose] public noncomputable section

open MeasureTheory
open MeasureTheory.LocallyIntegrable (integrable_mul_right_of_hasCompactSupport)
open scoped RealInnerProductSpace Sobolev

namespace NavierStokes.Nonuniqueness

set_option linter.missingDocs true


/-- One component of the classical eigenvalue identity: the `m`-th component of the classical
eigenvalue density at `μ = 0` is integrable, and its integral is that of the `m`-th component of
the pairing of `V` with `profileAdjoint B φ`, split into its five parts. -/
private theorem integral_eigen_component_eq {B V φ : ℝ^3 → ℝ^3} (hBc : Continuous B)
    (hB : ∀ x : ℝ^3, x ≠ 0 → ContDiffAt ℝ 1 B x)
    (hBdiv : ∀ x : ℝ^3, x ≠ 0 → PDE.divergence B x = 0)
    (hBD : ∀ j, LocallyIntegrable (PDE.partialDeriv j (fun x ↦ B x j)) volume)
    (hVc : Continuous V) (hV : ∀ x : ℝ^3, x ≠ 0 → ContDiffAt ℝ 1 V x)
    (hVD : ∀ i j, LocallyIntegrable (PDE.partialDeriv j (fun x ↦ V x i)) volume)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) (m : Fin 3) :
    ∫ x, (-(1 / 2 : ℝ) * (V x m * φ x m) -
        (1 / 2 : ℝ) * (∑ i, PDE.partialDeriv i (fun y ↦ V y m) x * (x i * φ x m)) +
        (∑ i, B x i * PDE.partialDeriv i (fun y ↦ V y m) x) * φ x m -
        (∑ i, B x m * V x i * PDE.partialDeriv i (fun y ↦ φ y m) x) +
        ∑ i, PDE.partialDeriv i (fun y ↦ V y m) x * PDE.partialDeriv i (fun y ↦ φ y m) x) =
      (∫ x, V x m * φ x m) +
        (1 / 2 : ℝ) * (∑ i, ∫ x, V x m * x i * PDE.partialDeriv i (fun y ↦ φ y m) x) -
        (∑ i, ∫ x, V x m * PDE.partialDeriv i (PDE.partialDeriv i (fun y ↦ φ y m)) x) -
        (∑ i, ∫ x, B x m * V x i * PDE.partialDeriv i (fun y ↦ φ y m) x) -
        (∑ i, ∫ x, V x m * B x i * PDE.partialDeriv i (fun y ↦ φ y m) x) ∧
      Integrable (fun x ↦ -(1 / 2 : ℝ) * (V x m * φ x m) -
        (1 / 2 : ℝ) * (∑ i, PDE.partialDeriv i (fun y ↦ V y m) x * (x i * φ x m)) +
        (∑ i, B x i * PDE.partialDeriv i (fun y ↦ V y m) x) * φ x m -
        (∑ i, B x m * V x i * PDE.partialDeriv i (fun y ↦ φ y m) x) +
        ∑ i, PDE.partialDeriv i (fun y ↦ V y m) x * PDE.partialDeriv i (fun y ↦ φ y m) x)
        volume := by
  have hVc' (k : Fin 3) : Continuous (fun x ↦ V x k) :=
    (EuclideanSpace.proj k : ℝ^3 →L[ℝ] ℝ).continuous.comp hVc
  have hBc' (k : Fin 3) : Continuous (fun x ↦ B x k) :=
    (EuclideanSpace.proj k : ℝ^3 →L[ℝ] ℝ).continuous.comp hBc
  have hVk : ∀ x : ℝ^3, x ≠ 0 → ContDiffAt ℝ 1 (fun y ↦ V y m) x := fun x hx ↦
    (EuclideanSpace.proj m : ℝ^3 →L[ℝ] ℝ).contDiff.contDiffAt.comp x (hV x hx)
  have hφi : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ φ y m) :=
    (EuclideanSpace.proj m : ℝ^3 →L[ℝ] ℝ).contDiff.comp hφ
  have hφic : HasCompactSupport (fun y ↦ φ y m) := hφc.comp_left (g := fun v : ℝ^3 ↦ v m) rfl
  have hdφ (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (PDE.partialDeriv j (fun y ↦ φ y m)) :=
    hφi.partialDeriv j (k := (⊤ : ℕ∞))
  -- the three integrations by parts
  have hI1 (i : Fin 3) := integral_mul_coord_mul_partialDeriv_eq (hVc' m) hVk i (hVD m i) hφi hφic
  have hI2 := sum_integral_mul_mul_partialDeriv_eq hBc hB hBdiv hBD (hVc' m) hVk (hVD m) hφi hφic
  have hI3 (i : Fin 3) := integral_mul_partialDeriv_eq_neg_of_contDiffAt hVk
    (hVc' m).locallyIntegrable i (hVD m i) (hdφ i) (hφic.partialDeriv i)
  -- integrability of the parts
  have i1 : Integrable (fun x ↦ V x m * φ x m) volume :=
    PDE.Analysis.integrable_mul_of_hasCompactSupport_right (hVc' m) hφi.continuous hφic
  have i2 (i : Fin 3) : Integrable
      (fun x ↦ PDE.partialDeriv i (fun y ↦ V y m) x * (x i * φ x m)) volume :=
    integrable_mul_right_of_hasCompactSupport (hVD m i)
      ((EuclideanSpace.proj i : ℝ^3 →L[ℝ] ℝ).continuous.mul hφi.continuous) hφic.mul_left
  have i3 : Integrable (fun x ↦ (∑ i, B x i * PDE.partialDeriv i (fun y ↦ V y m) x) *
      φ x m) volume := integrable_mul_right_of_hasCompactSupport
    (locallyIntegrable_finsetSum _ fun i _ ↦ (hVD m i).continuous_mul (hBc' i)) hφi.continuous hφic
  have i4 (i : Fin 3) : Integrable
      (fun x ↦ B x m * V x i * PDE.partialDeriv i (fun y ↦ φ y m) x) volume :=
    PDE.Analysis.integrable_mul_of_hasCompactSupport_right ((hBc' m).mul (hVc' i))
      (hdφ i).continuous (hφic.partialDeriv i)
  have i5 (i : Fin 3) : Integrable (fun x ↦ PDE.partialDeriv i (fun y ↦ V y m) x *
      PDE.partialDeriv i (fun y ↦ φ y m) x) volume :=
    integrable_mul_right_of_hasCompactSupport (hVD m i) (hdφ i).continuous (hφic.partialDeriv i)
  have s2 := integrable_finsetSum Finset.univ fun i (_ : i ∈ Finset.univ) ↦ i2 i
  have s4 := integrable_finsetSum Finset.univ fun i (_ : i ∈ Finset.univ) ↦ i4 i
  have s5 := integrable_finsetSum Finset.univ fun i (_ : i ∈ Finset.univ) ↦ i5 i
  have iA := (i1.const_mul (-(1 / 2 : ℝ))).sub (s2.const_mul (1 / 2 : ℝ))
  refine ⟨?_, ((iA.add i3).sub s4).add s5⟩
  rw [integral_add, integral_sub, integral_add, integral_sub, integral_const_mul,
    integral_const_mul, integral_finsetSum _ fun i _ ↦ i2 i, integral_finsetSum _ fun i _ ↦ i4 i,
    integral_finsetSum _ fun i _ ↦ i5 i]
  · simp only [Fin.sum_univ_three] at hI2 ⊢
    linarith [hI1 0, hI1 1, hI1 2, hI3 0, hI3 1, hI3 2]
  exacts [i1.const_mul _, s2.const_mul _, iA, i3, iA.add i3, s4, (iA.add i3).sub s4, s5]

/-- **Weak eigenvalue density of a field smooth off the origin.** Let `B` be continuous, `C¹` and
divergence free off the origin, and let `v ∈ H¹(ℝ³)³` have a representative `V` that is
continuous, `C¹` and divergence free off the origin, with locally integrable first partials of
`B` and `V` and with the classical partials `∂ⱼVᵢ` representing the weak gradient of `v`. Then
for a smooth compactly supported `φ` the weak eigenvalue density at `μ = 0` is integrable and its
integral is the pairing of `V` with the adjoint `profileAdjoint B φ` of the linearization at
`B`. -/
theorem integral_weakEigenDensity_eq_integral_inner_profileAdjoint {B V φ : ℝ^3 → ℝ^3}
    (hBc : Continuous B) (hB : ∀ x : ℝ^3, x ≠ 0 → ContDiffAt ℝ 1 B x)
    (hBdiv : ∀ x : ℝ^3, x ≠ 0 → PDE.divergence B x = 0)
    (hBD : ∀ i j, LocallyIntegrable (PDE.partialDeriv j (fun x ↦ B x i)) volume)
    (hVc : Continuous V) (hV : ∀ x : ℝ^3, x ≠ 0 → ContDiffAt ℝ 1 V x)
    (hVdiv : ∀ x : ℝ^3, x ≠ 0 → PDE.divergence V x = 0)
    (hVD : ∀ i j, LocallyIntegrable (PDE.partialDeriv j (fun x ↦ V x i)) volume)
    {v : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))} (hv : Stationary.representative v =ᵐ[volume] V)
    (hvD : ∀ i j, (fun x ↦ Stationary.gradientRepresentative v x i j) =ᵐ[volume]
      PDE.partialDeriv j (fun x ↦ V x i))
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    Integrable (weakEigenDensity B 0 v φ) ∧
      ∫ x, weakEigenDensity B 0 v φ x = ∫ x, ⟪V x, profileAdjoint B φ x⟫ := by
  have hcomp (m : Fin 3) := integral_eigen_component_eq hBc hB hBdiv (fun j ↦ hBD j j) hVc hV
    hVD hφ hφc m
  -- almost everywhere the density is the classical one
  have hvD' : ∀ᵐ x ∂volume, ∀ i j, Stationary.gradientRepresentative v x i j =
      PDE.partialDeriv j (fun y ↦ V y i) x :=
    ae_all_iff.2 fun i ↦ ae_all_iff.2 fun j ↦ hvD i j
  have hae : weakEigenDensity B 0 v φ =ᵐ[volume] fun x ↦ ∑ m,
      (-(1 / 2 : ℝ) * (V x m * φ x m) -
        (1 / 2 : ℝ) * (∑ i, PDE.partialDeriv i (fun y ↦ V y m) x * (x i * φ x m)) +
        (∑ i, B x i * PDE.partialDeriv i (fun y ↦ V y m) x) * φ x m -
        (∑ i, B x m * V x i * PDE.partialDeriv i (fun y ↦ φ y m) x) +
        ∑ i, PDE.partialDeriv i (fun y ↦ V y m) x * PDE.partialDeriv i (fun y ↦ φ y m) x) := by
    filter_upwards [hv, hvD', volume.ae_ne (0 : ℝ^3)] with x hx hxD hx0
    have hd := hVdiv x hx0
    rw [PDE.divergence_eq_sum] at hd
    rw [weakEigenDensity_eq_sum B 0 v (hφ.of_le (by simp)) x, hx]
    simp only [hxD, hd]
    simp only [Fin.sum_univ_three]
    ring
  refine ⟨(integrable_finsetSum _ fun m _ ↦ (hcomp m).2).congr hae.symm, ?_⟩
  -- the pairing with the adjoint, split
  have hVc' (k : Fin 3) : Continuous (fun x ↦ V x k) :=
    (EuclideanSpace.proj k : ℝ^3 →L[ℝ] ℝ).continuous.comp hVc
  have hBc' (k : Fin 3) : Continuous (fun x ↦ B x k) :=
    (EuclideanSpace.proj k : ℝ^3 →L[ℝ] ℝ).continuous.comp hBc
  have hφi (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ φ y i) :=
    (EuclideanSpace.proj i : ℝ^3 →L[ℝ] ℝ).contDiff.comp hφ
  have hφic (i : Fin 3) : HasCompactSupport (fun y ↦ φ y i) :=
    hφc.comp_left (g := fun v : ℝ^3 ↦ v i) rfl
  have hd (i j : Fin 3) : Continuous (PDE.partialDeriv j (fun y ↦ φ y i)) :=
    ((hφi i).partialDeriv j (k := 0)).continuous
  have hdd (i j : Fin 3) : Continuous
      (PDE.partialDeriv j (PDE.partialDeriv j (fun y ↦ φ y i))) :=
    (((hφi i).partialDeriv j (k := (⊤ : ℕ∞))).partialDeriv j (k := 0)).continuous
  have i1 (m : Fin 3) : Integrable (fun x ↦ V x m * φ x m) volume :=
    PDE.Analysis.integrable_mul_of_hasCompactSupport_right (hVc' m) (hφi m).continuous (hφic m)
  have i2 (m i : Fin 3) : Integrable
      (fun x ↦ V x m * x i * PDE.partialDeriv i (fun y ↦ φ y m) x) volume :=
    PDE.Analysis.integrable_mul_of_hasCompactSupport_right
      ((hVc' m).mul (EuclideanSpace.proj i : ℝ^3 →L[ℝ] ℝ).continuous) (hd m i)
      ((hφic m).partialDeriv i)
  have i3 (m i : Fin 3) : Integrable
      (fun x ↦ V x m * PDE.partialDeriv i (PDE.partialDeriv i (fun y ↦ φ y m)) x) volume :=
    PDE.Analysis.integrable_mul_of_hasCompactSupport_right (hVc' m) (hdd m i)
      (((hφic m).partialDeriv i).partialDeriv i)
  have i4 (m i : Fin 3) : Integrable
      (fun x ↦ B x m * V x i * PDE.partialDeriv i (fun y ↦ φ y m) x) volume :=
    PDE.Analysis.integrable_mul_of_hasCompactSupport_right ((hBc' m).mul (hVc' i)) (hd m i)
      ((hφic m).partialDeriv i)
  have i5 (m i : Fin 3) : Integrable
      (fun x ↦ V x m * B x i * PDE.partialDeriv i (fun y ↦ φ y m) x) volume :=
    PDE.Analysis.integrable_mul_of_hasCompactSupport_right ((hVc' m).mul (hBc' i)) (hd m i)
      ((hφic m).partialDeriv i)
  have hsum (f : Fin 3 → Fin 3 → ℝ^3 → ℝ) (hf : ∀ m i, Integrable (f m i) volume)
      (m : Fin 3) :=
    integrable_finsetSum Finset.univ fun i (_ : i ∈ Finset.univ) ↦ hf m i
  have iA (m : Fin 3) := (i1 m).add ((hsum _ i2 m).const_mul (1 / 2 : ℝ))
  have iD (m : Fin 3) := (((iA m).sub (hsum _ i3 m)).sub (hsum _ i4 m)).sub (hsum _ i5 m)
  have hpt (x : ℝ^3) : ⟪V x, profileAdjoint B φ x⟫ = ∑ m, (V x m * φ x m +
      (1 / 2 : ℝ) * (∑ i, V x m * x i * PDE.partialDeriv i (fun y ↦ φ y m) x) -
      (∑ i, V x m * PDE.partialDeriv i (PDE.partialDeriv i (fun y ↦ φ y m)) x) -
      (∑ i, B x m * V x i * PDE.partialDeriv i (fun y ↦ φ y m) x) -
      (∑ i, V x m * B x i * PDE.partialDeriv i (fun y ↦ φ y m) x)) := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, profileAdjoint_apply hφ]
    simp only [Fin.sum_univ_three]
    ring
  simp only [hpt]
  rw [integral_congr_ae hae, integral_finsetSum _ fun m _ ↦ (hcomp m).2, integral_finsetSum]
  · refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [(hcomp m).1, integral_sub, integral_sub, integral_sub, integral_add, integral_const_mul,
      integral_finsetSum _ fun i _ ↦ i2 m i, integral_finsetSum _ fun i _ ↦ i3 m i,
      integral_finsetSum _ fun i _ ↦ i4 m i, integral_finsetSum _ fun i _ ↦ i5 m i]
    exacts [i1 m, (hsum _ i2 m).const_mul _, iA m, hsum _ i3 m, (iA m).sub (hsum _ i3 m),
      hsum _ i4 m, ((iA m).sub (hsum _ i3 m)).sub (hsum _ i4 m), hsum _ i5 m]
  · exact fun m _ ↦ iD m

/-- **Weak eigenvalue density and the linearized operator.** Under the hypotheses of
`integral_weakEigenDensity_eq_integral_inner_profileAdjoint`, with `V` moreover `C²` off the
origin with locally integrable diagonal second partials, the integral of the weak eigenvalue
density at `μ = 0` against a smooth compactly supported `φ` is the pairing of the linearized
operator `-½(V + ξ·∇V) + (B·∇)V + (V·∇)B - ΔV` with `φ`. -/
theorem integral_weakEigenDensity_eq_integral_inner_stationaryVelocityLinearization
    {B V φ : ℝ^3 → ℝ^3} (hBc : Continuous B) (hB : ∀ x : ℝ^3, x ≠ 0 → ContDiffAt ℝ 1 B x)
    (hBdiv : ∀ x : ℝ^3, x ≠ 0 → PDE.divergence B x = 0)
    (hBD : ∀ i j, LocallyIntegrable (PDE.partialDeriv j (fun x ↦ B x i)) volume)
    (hVc : Continuous V) (hV : ∀ x : ℝ^3, x ≠ 0 → ContDiffAt ℝ 2 V x)
    (hVdiv : ∀ x : ℝ^3, x ≠ 0 → PDE.divergence V x = 0)
    (hVD : ∀ i j, LocallyIntegrable (PDE.partialDeriv j (fun x ↦ V x i)) volume)
    (hVH : ∀ i j, LocallyIntegrable
      (PDE.partialDeriv j (PDE.partialDeriv j (fun x ↦ V x i))) volume)
    {v : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))} (hv : Stationary.representative v =ᵐ[volume] V)
    (hvD : ∀ i j, (fun x ↦ Stationary.gradientRepresentative v x i j) =ᵐ[volume]
      PDE.partialDeriv j (fun x ↦ V x i))
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    ∫ x, weakEigenDensity B 0 v φ x = ∫ x, ⟪stationaryVelocityLinearization B V x, φ x⟫ := by
  rw [(integral_weakEigenDensity_eq_integral_inner_profileAdjoint hBc hB hBdiv hBD hVc
    (fun x hx ↦ (hV x hx).of_le (by simp)) hVdiv hVD hv hvD hφ hφc).2]
  exact integral_inner_profileAdjoint_eq_integral_inner_stationaryVelocityLinearization hBc hB
    hBdiv hBD hVc hV hVdiv hVD hVH hφ hφc

end NavierStokes.Nonuniqueness
