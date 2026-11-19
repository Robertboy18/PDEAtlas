/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.CoordinateSystems.Axisymmetric
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# First derivatives of meridian lifts at the axis

A meridian profile gives a Cartesian scalar field by replacing the radial coordinate
with the norm in the transverse plane. That norm is not differentiable at the origin.
A zero radial derivative removes its first-order contribution. If the radial derivative
vanishes along the nearby axis and the profile is C¹, the Cartesian derivative is
continuous there as well: its radial coefficient tends to zero, while the norm derivative
has operator norm at most one. Away from the axis the cylindrical radius itself is smooth.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology Asymptotics

namespace PDE.CoordinateSystems

/-- A linear functional on the parameter plane is determined by its two coordinate values. -/
private theorem pair_linear_apply (D : (ℝ × ℝ) →L[ℝ] ℝ) (q : ℝ × ℝ) :
    D q = q.1 * D (1, 0) + q.2 * D (0, 1) := by
  have hq : q = q.1 • ((1, 0) : ℝ × ℝ) + q.2 • ((0, 1) : ℝ × ℝ) := by
    ext <;> simp
  conv_lhs => rw [hq]
  simp only [map_add, map_smul, smul_eq_mul]

/-- The chain rule on the parameter plane separates into the two coordinate contributions. -/
private theorem pair_linear_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : (ℝ × ℝ) →L[ℝ] ℝ) (a b : E →L[ℝ] ℝ) :
    D.comp (a.prod b) = D (1, 0) • a + D (0, 1) • b := by
  ext x
  change D (a x, b x) = D (1, 0) * a x + D (0, 1) * b x
  rw [pair_linear_apply]
  exact congrArg₂ (· + ·) (mul_comm _ _) (mul_comm _ _)

/-- The radial coordinate value of the derivative agrees with differentiation on a radial line. -/
private theorem radial_derivative_value {f : ℝ × ℝ → ℝ} {q : ℝ × ℝ}
    {D : (ℝ × ℝ) →L[ℝ] ℝ} (hf : HasFDerivAt f D q) :
    D (1, 0) = deriv (fun r ↦ f (r, q.2)) q.1 := by
  have hline : HasDerivAt (fun r : ℝ ↦ (r, q.2)) (1, 0) q.1 :=
    (hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2)
  exact (hf.comp_hasDerivAt q.1 hline).deriv.symm

/-- A zero radial derivative removes the nondifferentiable part of the norm at the origin. -/
private theorem hasFDerivAt_norm_profile_axis {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × ℝ → ℝ} {D : (ℝ × ℝ) →L[ℝ] ℝ} {z : ℝ}
    (hf : HasFDerivAt f D (0, z)) (hr : D (1, 0) = 0) :
    HasFDerivAt (fun p : E × ℝ ↦ f (‖p.1‖, p.2))
      (D (0, 1) • ContinuousLinearMap.snd ℝ E ℝ) (0, z) := by
  have hN : Tendsto (fun p : E × ℝ ↦ (‖p.1‖, p.2))
      (𝓝 (0, z)) (𝓝 (0, z)) := by
    simpa only [norm_zero] using
      (continuous_fst.norm.prodMk continuous_snd).tendsto ((0 : E), z)
  have hO : (fun p : E × ℝ ↦ (‖p.1‖, p.2) - (0, z)) =O[𝓝 (0, z)]
      (fun p ↦ p - (0, z)) := by
    apply Asymptotics.isBigO_of_le
    intro p
    simp [Prod.norm_def]
  have hrem (p : E × ℝ) :
      D ((‖p.1‖, p.2) - (0, z)) =
        (D (0, 1) • ContinuousLinearMap.snd ℝ E ℝ) (p - (0, z)) := by
    rw [pair_linear_apply]
    change (‖p.1‖ - 0) * D (1, 0) + (p.2 - z) * D (0, 1) =
      D (0, 1) * (p.2 - z)
    rw [sub_zero, hr, mul_zero, zero_add]
    exact mul_comm _ _
  apply hasFDerivAt_iff_isLittleO.mpr
  have h := (hf.isLittleO.comp_tendsto hN).trans_isBigO hO
  simpa only [Function.comp_def, norm_zero, hrem] using h

/-- The Cartesian derivative has a bounded norm-derivative factor in its radial part. -/
private def normProfileDerivative {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ × ℝ → ℝ)
    (p : E × ℝ) : (E × ℝ) →L[ℝ] ℝ :=
  fderiv ℝ f (‖p.1‖, p.2) (1, 0) •
      (fderiv ℝ (fun x : E ↦ ‖x‖) p.1).comp (ContinuousLinearMap.fst ℝ E ℝ) +
    fderiv ℝ f (‖p.1‖, p.2) (0, 1) • ContinuousLinearMap.snd ℝ E ℝ

/-- Away from the axis this is the chain rule; on the axis the radial term vanishes. -/
private theorem hasFDerivAt_norm_profile {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : ℝ × ℝ → ℝ} (p : E × ℝ)
    (hf : DifferentiableAt ℝ f (‖p.1‖, p.2))
    (hr : deriv (fun r ↦ f (r, p.2)) 0 = 0) :
    HasFDerivAt (fun q : E × ℝ ↦ f (‖q.1‖, q.2)) (normProfileDerivative f p) p := by
  rcases p with ⟨x, z⟩
  by_cases hx : x = 0
  · subst x
    have hf0 : HasFDerivAt f (fderiv ℝ f (0, z)) (0, z) := by
      simpa only [norm_zero] using hf.hasFDerivAt
    have hzero : fderiv ℝ f (0, z) (1, 0) = 0 :=
      (radial_derivative_value hf0).trans hr
    simpa only [normProfileDerivative, norm_zero, hzero, zero_smul, zero_add] using
      (hasFDerivAt_norm_profile_axis (E := E) hf0 hzero)
  · have hnorm : DifferentiableAt ℝ (fun y : E ↦ ‖y‖) x :=
      (contDiffAt_norm ℝ hx : ContDiffAt ℝ 1 (fun y : E ↦ ‖y‖) x).differentiableAt
        one_ne_zero
    have hn : HasFDerivAt (fun q : E × ℝ ↦ (‖q.1‖, q.2))
        (((fderiv ℝ (fun y : E ↦ ‖y‖) x).comp
          (ContinuousLinearMap.fst ℝ E ℝ)).prod (ContinuousLinearMap.snd ℝ E ℝ))
        (x, z) :=
      (hnorm.hasFDerivAt.comp (x, z)
        (ContinuousLinearMap.fst ℝ E ℝ).hasFDerivAt).prodMk
          (ContinuousLinearMap.snd ℝ E ℝ).hasFDerivAt
    simpa only [pair_linear_comp, normProfileDerivative, Function.comp_def] using
      hf.hasFDerivAt.comp (x, z) hn

/-- A vanishing radial coefficient controls the derivative even where the norm is singular. -/
private theorem continuousAt_normProfileDerivative {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : ℝ × ℝ → ℝ} (p : E × ℝ)
    (hf : ContinuousAt (fderiv ℝ f) (‖p.1‖, p.2))
    (hr : p.1 = 0 → fderiv ℝ f (‖p.1‖, p.2) (1, 0) = 0) :
    ContinuousAt (normProfileDerivative (E := E) f) p := by
  let A (q : E × ℝ) := fderiv ℝ f (‖q.1‖, q.2) (1, 0)
  let B (q : E × ℝ) := fderiv ℝ f (‖q.1‖, q.2) (0, 1)
  have hN : ContinuousAt (fun q : E × ℝ ↦ (‖q.1‖, q.2)) p :=
    (continuous_fst.norm.prodMk continuous_snd).continuousAt
  have hD : ContinuousAt (fun q : E × ℝ ↦ fderiv ℝ f (‖q.1‖, q.2)) p :=
    hf.comp (f := fun q : E × ℝ ↦ (‖q.1‖, q.2)) hN
  have hA : ContinuousAt A p := hD.clm_apply continuousAt_const
  have hB : ContinuousAt B p := hD.clm_apply continuousAt_const
  have hrad : ContinuousAt (fun q : E × ℝ ↦ A q •
      (fderiv ℝ (fun x : E ↦ ‖x‖) q.1).comp (ContinuousLinearMap.fst ℝ E ℝ)) p := by
    by_cases hx : p.1 = 0
    · have hA0 : A p = 0 := hr hx
      have hbound (q : E × ℝ) :
          ‖A q • (fderiv ℝ (fun x : E ↦ ‖x‖) q.1).comp
            (ContinuousLinearMap.fst ℝ E ℝ)‖ ≤
              ‖A q‖ * ‖ContinuousLinearMap.fst ℝ E ℝ‖ := by
        apply (ContinuousLinearMap.opNorm_smul_le (A q)
          ((fderiv ℝ (fun x : E ↦ ‖x‖) q.1).comp
            (ContinuousLinearMap.fst ℝ E ℝ))).trans
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg (A q))
        calc
          ‖(fderiv ℝ (fun x : E ↦ ‖x‖) q.1).comp
              (ContinuousLinearMap.fst ℝ E ℝ)‖ ≤
              ‖fderiv ℝ (fun x : E ↦ ‖x‖) q.1‖ *
                ‖ContinuousLinearMap.fst ℝ E ℝ‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ 1 * ‖ContinuousLinearMap.fst ℝ E ℝ‖ :=
            mul_le_mul_of_nonneg_right
              (norm_fderiv_le_of_lipschitz ℝ (x₀ := q.1) lipschitzWith_one_norm)
              (ContinuousLinearMap.fst ℝ E ℝ).opNorm_nonneg
          _ = ‖ContinuousLinearMap.fst ℝ E ℝ‖ := one_mul _
      have hlim : Tendsto (fun q : E × ℝ ↦ ‖A q‖ * ‖ContinuousLinearMap.fst ℝ E ℝ‖)
          (𝓝 p) (𝓝 0) := by
        simpa only [ContinuousAt, hA0, norm_zero, zero_mul] using
          hA.norm.mul_const ‖ContinuousLinearMap.fst ℝ E ℝ‖
      have hzero : Tendsto (fun q : E × ℝ ↦ A q •
          (fderiv ℝ (fun x : E ↦ ‖x‖) q.1).comp (ContinuousLinearMap.fst ℝ E ℝ))
          (𝓝 p) (𝓝 (0 : (E × ℝ) →L[ℝ] ℝ)) :=
        squeeze_zero_norm (f := fun q : E × ℝ ↦ A q •
          (fderiv ℝ (fun x : E ↦ ‖x‖) q.1).comp (ContinuousLinearMap.fst ℝ E ℝ))
          hbound hlim
      simpa only [ContinuousAt, hA0, zero_smul] using hzero
    · have hn := (contDiffAt_norm ℝ hx :
          ContDiffAt ℝ 1 (fun x : E ↦ ‖x‖) p.1).continuousAt_fderiv one_ne_zero
      have hnorm : ContinuousAt (fun q : E × ℝ ↦ fderiv ℝ (fun x : E ↦ ‖x‖) q.1) p :=
        hn.comp (f := fun q : E × ℝ ↦ q.1) continuousAt_fst
      exact hA.smul (hnorm.clm_comp continuousAt_const)
  exact hrad.add (hB.smul continuousAt_const)

/-- Nearby zero radial traces and a C¹ germ give a C¹ Cartesian norm profile. -/
private theorem contDiffAt_norm_profile_axis {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : ℝ × ℝ → ℝ} {z : ℝ}
    (hf : ContDiffAt ℝ 1 f (0, z))
    (hr : ∀ᶠ s in 𝓝 z, deriv (fun r ↦ f (r, s)) 0 = 0) :
    ContDiffAt ℝ 1 (fun p : E × ℝ ↦ f (‖p.1‖, p.2)) (0, z) := by
  have hN : Tendsto (fun p : E × ℝ ↦ (‖p.1‖, p.2))
      (𝓝 (0, z)) (𝓝 (0, z)) := by
    simpa only [norm_zero] using
      (continuous_fst.norm.prodMk continuous_snd).tendsto ((0 : E), z)
  have hregular : ∀ᶠ p : E × ℝ in 𝓝 (0, z), ContDiffAt ℝ 1 f (‖p.1‖, p.2) :=
    hN.eventually (hf.eventually (by norm_num))
  have htrace : ∀ᶠ p : E × ℝ in 𝓝 (0, z), deriv (fun r ↦ f (r, p.2)) 0 = 0 :=
    (continuous_snd.continuousAt (x := ((0 : E), z))).eventually hr
  let S : Set (E × ℝ) := {p | ContDiffAt ℝ 1 f (‖p.1‖, p.2) ∧
    deriv (fun r ↦ f (r, p.2)) 0 = 0}
  refine contDiffAt_one_iff.mpr ⟨normProfileDerivative f, S, hregular.and htrace, ?_, ?_⟩
  · intro p hp
    apply (continuousAt_normProfileDerivative p
      (hp.1.continuousAt_fderiv one_ne_zero) ?_).continuousWithinAt
    intro hzero
    have h := radial_derivative_value (hp.1.differentiableAt one_ne_zero).hasFDerivAt
    simpa only [hzero, norm_zero, hp.2] using h
  · intro p hp
    exact hasFDerivAt_norm_profile p (hp.1.differentiableAt one_ne_zero) hp.2

/-- The usual parameter pair is a continuous linear coordinate map into the Euclidean plane. -/
private def meridianPairCLM : (ℝ × ℝ) →L[ℝ] ℝ^2 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 ↦ ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi ![ContinuousLinearMap.fst ℝ ℝ ℝ,
      ContinuousLinearMap.snd ℝ ℝ ℝ])

/-- The parameter map agrees with the vector notation used for meridian coordinates. -/
private theorem meridianPairCLM_apply (q : ℝ × ℝ) :
    meridianPairCLM q = !₂[q.1, q.2] := by
  ext i
  fin_cases i <;> simp [meridianPairCLM]

/-- Split the transverse plane and the axial coordinate without changing the Cartesian field. -/
private def meridianSplitCLM : ℝ^3 →L[ℝ] ((ℝ^2) × ℝ) :=
  (meridianPairCLM.comp
    ((EuclideanSpace.proj 0 : ℝ^3 →L[ℝ] ℝ).prod (EuclideanSpace.proj 1))).prod
      (EuclideanSpace.proj 2)

/-- The split map sends the symmetry axis to a zero transverse vector. -/
private theorem meridianSplitCLM_axis (z : ℝ) :
    meridianSplitCLM (meridianPoint 0 z) = (0, z) := by
  apply Prod.ext
  · ext i
    fin_cases i <;> simp [meridianSplitCLM, meridianPairCLM_apply, meridianPoint]
  · rfl

/-- The norm of the transverse part is the cylindrical radius. -/
private theorem meridianSplitCLM_norm (x : ℝ^3) :
    ‖(meridianSplitCLM x).1‖ = cylindricalRadius x := by
  change ‖meridianPairCLM (x 0, x 1)‖ = √(x 0 ^ 2 + x 1 ^ 2)
  rw [meridianPairCLM_apply]
  simp [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]

/-- Composing the split norm with the parameter map recovers `meridianCoordinates`. -/
private theorem meridianPairCLM_norm_split (x : ℝ^3) :
    meridianPairCLM (‖(meridianSplitCLM x).1‖, (meridianSplitCLM x).2) =
      meridianCoordinates x := by
  rw [meridianPairCLM_apply, meridianSplitCLM_norm]
  rfl

/-- At the symmetry axis the derivative of a meridian lift is purely axial.
Differentiability of the profile and its zero radial derivative are enough for this formula. -/
theorem hasFDerivAt_meridianLift_axis {f : ℝ^2 → ℝ} {z : ℝ}
    (hf : DifferentiableAt ℝ f (!₂[0, z] : ℝ^2))
    (hr : deriv (fun r ↦ f (!₂[r, z] : ℝ^2)) 0 = 0) :
    HasFDerivAt (meridianLift f)
      (deriv (fun s ↦ f (!₂[0, s] : ℝ^2)) z •
        (EuclideanSpace.proj 2 : ℝ^3 →L[ℝ] ℝ)) (meridianPoint 0 z) := by
  let F : ℝ × ℝ → ℝ := fun q ↦ f (meridianPairCLM q)
  have hf' : DifferentiableAt ℝ f (meridianPairCLM (0, z)) := by
    simpa only [meridianPairCLM_apply] using hf
  have hF : DifferentiableAt ℝ F (0, z) :=
    hf'.comp (0, z) meridianPairCLM.differentiableAt
  have hrad : fderiv ℝ F (0, z) (1, 0) = 0 := by
    rw [radial_derivative_value hF.hasFDerivAt]
    simpa only [F, meridianPairCLM_apply] using hr
  have hline : HasDerivAt (fun s : ℝ ↦ ((0 : ℝ), s)) (0, 1) z :=
    (hasDerivAt_const z (0 : ℝ)).prodMk (hasDerivAt_id z)
  have hax : fderiv ℝ F (0, z) (0, 1) =
      deriv (fun s ↦ f (!₂[0, s] : ℝ^2)) z := by
    simpa only [Function.comp_def, F, meridianPairCLM_apply] using
      (hF.hasFDerivAt.comp_hasDerivAt z hline).deriv.symm
  have hnorm := hasFDerivAt_norm_profile_axis (E := ℝ^2) hF.hasFDerivAt hrad
  have hbase : HasFDerivAt (fun p : (ℝ^2) × ℝ ↦ F (‖p.1‖, p.2))
      (fderiv ℝ F (0, z) (0, 1) • ContinuousLinearMap.snd ℝ (ℝ^2) ℝ)
      (meridianSplitCLM (meridianPoint 0 z)) := by
    rw [meridianSplitCLM_axis]
    exact hnorm
  have h := hbase.comp (meridianPoint 0 z) meridianSplitCLM.hasFDerivAt
  have hfun : (fun x : ℝ^3 ↦ F (‖(meridianSplitCLM x).1‖,
      (meridianSplitCLM x).2)) = meridianLift f := by
    funext x
    exact congrArg f (meridianPairCLM_norm_split x)
  have hlin : (fderiv ℝ F (0, z) (0, 1) •
      ContinuousLinearMap.snd ℝ (ℝ^2) ℝ).comp meridianSplitCLM =
        deriv (fun s ↦ f (!₂[0, s] : ℝ^2)) z •
          (EuclideanSpace.proj 2 : ℝ^3 →L[ℝ] ℝ) := by
    rw [hax]
    ext x
    rfl
  simpa only [Function.comp_def, hfun, hlin] using h

/-- A C¹ meridian profile lifts to a C¹ Cartesian field at the axis when its radial
first derivative vanishes along the nearby axis. The regularity assumption is an
ambient germ in the signed meridian plane, not just regularity for positive radii. -/
theorem contDiffAt_meridianLift_axis {f : ℝ^2 → ℝ} {z : ℝ}
    (hf : ContDiffAt ℝ 1 f (!₂[0, z] : ℝ^2))
    (hr : ∀ᶠ s in 𝓝 z, deriv (fun r ↦ f (!₂[r, s] : ℝ^2)) 0 = 0) :
    ContDiffAt ℝ 1 (meridianLift f) (meridianPoint 0 z) := by
  let F : ℝ × ℝ → ℝ := fun q ↦ f (meridianPairCLM q)
  have hf' : ContDiffAt ℝ 1 f (meridianPairCLM (0, z)) := by
    simpa only [meridianPairCLM_apply] using hf
  have hF : ContDiffAt ℝ 1 F (0, z) :=
    hf'.comp (0, z) meridianPairCLM.contDiff.contDiffAt
  have htrace : ∀ᶠ s in 𝓝 z, deriv (fun r ↦ F (r, s)) 0 = 0 := by
    simpa only [F, meridianPairCLM_apply] using hr
  have hnorm := contDiffAt_norm_profile_axis (E := ℝ^2) hF htrace
  have hbase : ContDiffAt ℝ 1 (fun p : (ℝ^2) × ℝ ↦ F (‖p.1‖, p.2))
      (meridianSplitCLM (meridianPoint 0 z)) := by
    rw [meridianSplitCLM_axis]
    exact hnorm
  have h := hbase.comp (meridianPoint 0 z) meridianSplitCLM.contDiff.contDiffAt
  have hfun : (fun x : ℝ^3 ↦ F (‖(meridianSplitCLM x).1‖,
      (meridianSplitCLM x).2)) = meridianLift f := by
    funext x
    exact congrArg f (meridianPairCLM_norm_split x)
  simpa only [Function.comp_def, hfun] using h

/-- The cylindrical radius is smooth off the symmetry axis. -/
theorem contDiffAt_cylindricalRadius {n : WithTop ℕ∞} {x : ℝ^3} (hx : x ∉ symmetryAxis) :
    ContDiffAt ℝ n cylindricalRadius x := by
  have hsq : cylindricalRadiusSq x ≠ 0 := by
    rw [← cylindricalRadius_sq]
    exact pow_ne_zero 2 (cylindricalRadius_pos hx).ne'
  have hcoord (i : Fin 3) : ContDiffAt ℝ n (fun y : ℝ^3 ↦ y i) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffAt
  have h : ContDiffAt ℝ n cylindricalRadiusSq x := ((hcoord 0).pow 2).add ((hcoord 1).pow 2)
  exact (Real.contDiffAt_sqrt hsq).comp x h

end PDE.CoordinateSystems
