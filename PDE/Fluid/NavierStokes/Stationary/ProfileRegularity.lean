/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Stationary.WeakRegularity
public import PDE.Fluid.NavierStokes.Nonuniqueness.WeakEquations

/-!
# `H²` regularity of weak stationary profiles

Let `W` be a smooth divergence-free background field on `ℝ³` with bounded derivatives whose
stationary operator `F_W` lies in `L²`, and let `w ∈ H¹(ℝ³)³` be divergence free with
`W + w` a weak solution of the self-similar profile equation. Integrating by parts against
smooth compactly supported divergence-free fields, the background part of the weak profile
pairing becomes `∫ F_W · φ`, and the cross terms become `∫ ((w·∇)W + (W·∇)w) · φ`. Hence `w`
solves the linearized equation `L₀ w + Π((w·∇) w) = Π G` weakly with
`G = -F_W - (w·∇)W - (W·∇)w ∈ L²(ℝ³)³`, and the `H²` regularity of that equation applies.

## References

* T. Hou, Y. Wang, and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Section 2.1, Proposition 3, p. 9,
  and Appendix F, proof of Proposition 3, pp. 67-68.
  <https://arxiv.org/abs/2509.25116v2>
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology SobolevSpace SobolevSpace.GraphSpace HeatEquation.WholeSpace
open PDE.Analysis
open scoped ENNReal NNReal Sobolev ContDiff SobolevSpace.WholeSpaceHilbert

namespace NavierStokes.Stationary

/-- Transport by a divergence-free `H¹(ℝ³)` field against a smooth weight `a`:
`∑ⱼ ∫ wⱼ a ∂ⱼψ = -∑ⱼ ∫ wⱼ (∂ⱼa) ψ`. -/
theorem sum_integral_base_mul_mul_partialDeriv_eq_neg (w : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3)))
    (hw : divergenceCLM w = 0) {a ψ : ℝ^3 → ℝ} (ha : ContDiff ℝ ∞ a) (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) :
    ∑ j, ∫ x, (wkpBaseCoordinateCLM (w j) : ℝ^3 → ℝ) x * (a x * (∂[j] ψ) x) =
      -∑ j, ∫ x, (wkpBaseCoordinateCLM (w j) : ℝ^3 → ℝ) x * ((∂[j] a) x * ψ x) := by
  have hP : ContDiff ℝ ∞ (fun x ↦ a x * ψ x) := ha.mul hψ
  have hPc : HasCompactSupport (fun x ↦ a x * ψ x) := hc.mul_left
  have h0 := sum_integral_base_mul_partialDeriv_eq_zero w hw hP hPc
  have hd : ∀ (j : Fin 3) x, (∂[j] (fun y ↦ a y * ψ y)) x =
      (∂[j] a) x * ψ x + a x * (∂[j] ψ) x := fun j x ↦
    PDE.partialDeriv_mul (ha.differentiable (by simp) x) (hψ.differentiable (by simp) x)
  have hsplit : ∀ j, ∫ x, (wkpBaseCoordinateCLM (w j) : ℝ^3 → ℝ) x *
      (∂[j] (fun y ↦ a y * ψ y)) x =
      (∫ x, (wkpBaseCoordinateCLM (w j) : ℝ^3 → ℝ) x * ((∂[j] a) x * ψ x)) +
        ∫ x, (wkpBaseCoordinateCLM (w j) : ℝ^3 → ℝ) x * (a x * (∂[j] ψ) x) := by
    intro j
    simp only [hd, mul_add]
    exact integral_add
      (integrable_base_mul (w j) ((PDE.contDiff_top_partialDeriv ha).continuous.mul hψ.continuous)
        hc.mul_left)
      (integrable_base_mul (w j) (ha.continuous.mul (PDE.contDiff_top_partialDeriv hψ).continuous)
        (hc.partialDeriv j).mul_left)
  simp only [hsplit, Finset.sum_add_distrib] at h0
  linarith

/-- Transport of an `H¹(ℝ³)` function by a smooth divergence-free field `b`:
`∑ⱼ ∫ u bⱼ ∂ⱼψ = -∑ⱼ ∫ (∂ⱼu) bⱼ ψ`. -/
theorem sum_integral_base_mul_field_mul_partialDeriv_eq_neg (U : H¹(ℝ^3)) {b : ℝ^3 → ℝ^3}
    (hb : ContDiff ℝ ∞ b) (hbdiv : ∀ x, PDE.divergence b x = 0) {ψ : ℝ^3 → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    ∑ j, ∫ x, (wkpBaseCoordinateCLM U : ℝ^3 → ℝ) x * (b x j * (∂[j] ψ) x) =
      -∑ j, ∫ x, (wkpCoordinateCLM (singleDerivIndex 3 j) U : ℝ^3 → ℝ) x * (b x j * ψ x) := by
  have hbj : ∀ j, ContDiff ℝ ∞ (fun x ↦ b x j) := contDiff_component hb
  have hper : ∀ j, ∫ x, (wkpBaseCoordinateCLM U : ℝ^3 → ℝ) x *
      (∂[j] (fun y ↦ b y j * ψ y)) x =
      -∫ x, (wkpCoordinateCLM (singleDerivIndex 3 j) U : ℝ^3 → ℝ) x * (b x j * ψ x) :=
    fun j ↦ integral_base_mul_partialDeriv U j ((hbj j).mul hψ) hc.mul_left
  have hd : ∀ (j : Fin 3) x, (∂[j] (fun y ↦ b y j * ψ y)) x =
      (∂[j] (fun y ↦ b y j)) x * ψ x + b x j * (∂[j] ψ) x := fun j x ↦
    PDE.partialDeriv_mul ((hbj j).differentiable (by simp) x) (hψ.differentiable (by simp) x)
  have hi1 : ∀ j : Fin 3, Integrable (fun x ↦ (wkpBaseCoordinateCLM U : ℝ^3 → ℝ) x *
      ((∂[j] (fun y ↦ b y j)) x * ψ x)) volume := fun j ↦
    integrable_base_mul U ((PDE.contDiff_top_partialDeriv (hbj j)).continuous.mul hψ.continuous)
      hc.mul_left
  have hsplit : ∀ j, ∫ x, (wkpBaseCoordinateCLM U : ℝ^3 → ℝ) x *
      (∂[j] (fun y ↦ b y j * ψ y)) x =
      (∫ x, (wkpBaseCoordinateCLM U : ℝ^3 → ℝ) x * ((∂[j] (fun y ↦ b y j)) x * ψ x)) +
        ∫ x, (wkpBaseCoordinateCLM U : ℝ^3 → ℝ) x * (b x j * (∂[j] ψ) x) := by
    intro j
    simp only [hd, mul_add]
    exact integral_add (hi1 j)
      (integrable_base_mul U ((hbj j).continuous.mul (PDE.contDiff_top_partialDeriv hψ).continuous)
        (hc.partialDeriv j).mul_left)
  have hdivterm : ∑ j, ∫ x, (wkpBaseCoordinateCLM U : ℝ^3 → ℝ) x *
      ((∂[j] (fun y ↦ b y j)) x * ψ x) = 0 := by
    rw [← integral_finsetSum _ fun j _ ↦ hi1 j]
    have hpt : ∀ x, ∑ j, (wkpBaseCoordinateCLM U : ℝ^3 → ℝ) x *
        ((∂[j] (fun y ↦ b y j)) x * ψ x) =
        (wkpBaseCoordinateCLM U : ℝ^3 → ℝ) x * (PDE.divergence b x * ψ x) := by
      intro x
      simp only [PDE.divergence, Finset.sum_mul, Finset.mul_sum]
    simp only [hpt, hbdiv, zero_mul, mul_zero, integral_zero]
  have h1 := Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) ↦ hsplit j
  have h2 := Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) ↦ hper j
  rw [Finset.sum_add_distrib, hdivterm, zero_add] at h1
  rw [Finset.sum_neg_distrib] at h2
  linarith

theorem memLp_stationaryVelocityOperator_component {W : ℝ^3 → ℝ^3}
    (hF : MemLp (iteratedFDeriv ℝ 0 (stationaryVelocityOperator W)) 2 volume) (i : Fin 3) :
    MemLp (fun x ↦ stationaryVelocityOperator W x i) 2 volume := by
  have hc : Continuous (fun M : ContinuousMultilinearMap ℝ (fun _ : Fin 0 ↦ ℝ^3) (ℝ^3) ↦
      M (fun _ ↦ 0) i) :=
    (EuclideanSpace.proj i : ℝ^3 →L[ℝ] ℝ).continuous.comp (continuous_eval_const _)
  have hm : AEStronglyMeasurable (fun x ↦ stationaryVelocityOperator W x i) volume :=
    (hc.comp_aestronglyMeasurable hF.aestronglyMeasurable).congr
      (Filter.Eventually.of_forall fun x ↦ by simp [iteratedFDeriv_zero_apply])
  refine hF.of_le_mul (c := 1) hm (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [norm_iteratedFDeriv_zero, one_mul]
  exact PiLp.norm_apply_le _ _

/-- The forcing of the linearized equation satisfied by a correction `w` of a background `W`:
`G = -F_W - (w·∇)W - (W·∇)w`, with `F_W` the stationary operator of `W`. -/
def profileForcing (W : ℝ^3 → ℝ^3) (w : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))) (i : Fin 3)
    (x : ℝ^3) : ℝ :=
  -stationaryVelocityOperator W x i -
    ∑ j, (wkpBaseCoordinateCLM (w j) : ℝ^3 → ℝ) x * (∂[j] (fun y ↦ W y i)) x -
    ∑ j, W x j * (wkpCoordinateCLM (singleDerivIndex 3 j) (w i) : ℝ^3 → ℝ) x

theorem memLp_profileForcing {W : ℝ^3 → ℝ^3} (hW : ContDiff ℝ ∞ W)
    (hWbd : ∀ k, ∃ C, ∀ x, ‖iteratedFDeriv ℝ k W x‖ ≤ C)
    (hF : MemLp (iteratedFDeriv ℝ 0 (stationaryVelocityOperator W)) 2 volume)
    (w : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))) (i : Fin 3) :
    MemLp (profileForcing W w i) 2 volume := by
  obtain ⟨C₀, hC₀⟩ := hWbd 0
  obtain ⟨C₁, hC₁⟩ := hWbd 1
  have hd : Differentiable ℝ W := hW.differentiable (by simp)
  have hL2 : ∀ u : DerivLp 3 2 univ, MemLp (u : ℝ^3 → ℝ) 2 volume := fun u ↦ by
    simpa [domainMeasure] using Lp.memLp u
  have hmeas : ∀ u : DerivLp 3 2 univ, AEStronglyMeasurable (u : ℝ^3 → ℝ) volume := fun u ↦
    (hL2 u).aestronglyMeasurable
  -- the stationary operator
  have hFi := memLp_stationaryVelocityOperator_component hF i
  -- transport of the background by the correction
  have hA : ∀ j : Fin 3, MemLp (fun x ↦ (wkpBaseCoordinateCLM (w j) : ℝ^3 → ℝ) x *
      (∂[j] (fun y ↦ W y i)) x) 2 volume := by
    intro j
    have hcont : Continuous (fun x ↦ (∂[j] (fun y ↦ W y i)) x) :=
      (PDE.contDiff_top_partialDeriv (contDiff_component hW i)).continuous
    refine (hL2 (wkpBaseCoordinateCLM (w j))).of_le_mul (c := C₁)
      ((hmeas _).mul hcont.aestronglyMeasurable) (Filter.Eventually.of_forall fun x ↦ ?_)
    rw [norm_mul, mul_comm]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    rw [← PDE.partialDeriv_apply j i (hd x)]
    calc ‖(∂[j] W) x i‖ ≤ ‖(∂[j] W) x‖ := PiLp.norm_apply_le _ _
      _ ≤ ‖fderiv ℝ W x‖ := PDE.norm_partialDeriv_le_norm_fderiv j W x
      _ = ‖iteratedFDeriv ℝ 1 W x‖ := (norm_iteratedFDeriv_one W).symm
      _ ≤ C₁ := hC₁ x
  -- transport of the correction by the background
  have hB : ∀ j : Fin 3, MemLp (fun x ↦ W x j *
      (wkpCoordinateCLM (singleDerivIndex 3 j) (w i) : ℝ^3 → ℝ) x) 2 volume := by
    intro j
    refine (hL2 (wkpCoordinateCLM (singleDerivIndex 3 j) (w i))).of_le_mul (c := C₀)
      ((contDiff_component hW j).continuous.aestronglyMeasurable.mul (hmeas _))
      (Filter.Eventually.of_forall fun x ↦ ?_)
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc ‖W x j‖ ≤ ‖W x‖ := PiLp.norm_apply_le _ _
      _ = ‖iteratedFDeriv ℝ 0 W x‖ := norm_iteratedFDeriv_zero.symm
      _ ≤ C₀ := hC₀ x
  exact (hFi.neg.sub (memLp_finsetSum _ fun j _ ↦ hA j)).sub (memLp_finsetSum _ fun j _ ↦ hB j)

/-- The forcing as a vector `L²` field. -/
def profileForcingL2 {W : ℝ^3 → ℝ^3} (hW : ContDiff ℝ ∞ W)
    (hWbd : ∀ k, ∃ C, ∀ x, ‖iteratedFDeriv ℝ k W x‖ ≤ C)
    (hF : MemLp (iteratedFDeriv ℝ 0 (stationaryVelocityOperator W)) 2 volume)
    (w : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))) : VectorH 3 0 :=
  WithLp.toLp 2 fun i ↦ lpToZeroOrder (n := 3) (p := 2) (Ω := univ)
    ((show MemLp (profileForcing W w i) 2 (domainMeasure 3 univ) by
      simpa [domainMeasure] using memLp_profileForcing hW hWbd hF w i).toLp _)

theorem wkpBaseCoordinateCLM_profileForcingL2_ae {W : ℝ^3 → ℝ^3} (hW : ContDiff ℝ ∞ W)
    (hWbd : ∀ k, ∃ C, ∀ x, ‖iteratedFDeriv ℝ k W x‖ ≤ C)
    (hF : MemLp (iteratedFDeriv ℝ 0 (stationaryVelocityOperator W)) 2 volume)
    (w : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))) (i : Fin 3) :
    (wkpBaseCoordinateCLM (profileForcingL2 hW hWbd hF w i) : ℝ^3 → ℝ) =ᵐ[volume]
      profileForcing W w i := by
  have hm : MemLp (profileForcing W w i) 2 (domainMeasure 3 univ) := by
    simpa [domainMeasure] using memLp_profileForcing hW hWbd hF w i
  have h := MemLp.coeFn_toLp hm
  have hb : wkpBaseCoordinateCLM (profileForcingL2 hW hWbd hF w i) = hm.toLp _ := rfl
  rw [hb]
  simpa [domainMeasure] using h

/-- Splitting an integral of the form `∫ (B + L - ∑ⱼ C₁ⱼ - ∑ⱼ C₂ⱼ - ∑ⱼ Qⱼ)`. -/
theorem integral_eq_of_decomposition {E B L : ℝ^3 → ℝ} {C₁ C₂ Q : Fin 3 → ℝ^3 → ℝ}
    (hE : ∀ x, E x = B x + L x - ∑ j, C₁ j x - ∑ j, C₂ j x - ∑ j, Q j x)
    (hB : Integrable B volume) (hL : Integrable L volume) (h₁ : ∀ j, Integrable (C₁ j) volume)
    (h₂ : ∀ j, Integrable (C₂ j) volume) (hQ : ∀ j, Integrable (Q j) volume) :
    ∫ x, E x = (∫ x, B x) + (∫ x, L x) - ∑ j, (∫ x, C₁ j x) - ∑ j, (∫ x, C₂ j x) -
      ∑ j, ∫ x, Q j x := by
  have i₁ : Integrable (fun x ↦ ∑ j, C₁ j x) volume := integrable_finsetSum _ fun j _ ↦ h₁ j
  have i₂ : Integrable (fun x ↦ ∑ j, C₂ j x) volume := integrable_finsetSum _ fun j _ ↦ h₂ j
  have i₃ : Integrable (fun x ↦ ∑ j, Q j x) volume := integrable_finsetSum _ fun j _ ↦ hQ j
  rw [integral_congr_ae (Filter.Eventually.of_forall hE),
    integral_sub (f := fun x ↦ B x + L x - ∑ j, C₁ j x - ∑ j, C₂ j x)
      (((hB.add hL).sub i₁).sub i₂) i₃,
    integral_sub (f := fun x ↦ B x + L x - ∑ j, C₁ j x) ((hB.add hL).sub i₁) i₂,
    integral_sub (f := fun x ↦ B x + L x) (hB.add hL) i₁, integral_add hB hL,
    integral_finsetSum _ fun j _ ↦ h₁ j, integral_finsetSum _ fun j _ ↦ h₂ j,
    integral_finsetSum _ fun j _ ↦ hQ j]

/-- The weak profile equation of `W + w`, in coordinates, is the linearized equation of the
correction `w` with transport by `w` and forcing `profileForcing W w`: for smooth compactly
supported divergence-free `φ`,
`∑ᵢ ∫ wᵢ (φᵢ + ½ (x·∇φ)ᵢ - Δφᵢ) = ∑ᵢ ∫ Gᵢ φᵢ + ∑ᵢⱼ ∫ wⱼ wᵢ ∂ⱼφᵢ`, `G = -F_W - (w·∇)W - (W·∇)w`. -/
theorem sum_integral_eq_profileForcing_of_weakProfileDensity (W : ℝ^3 → ℝ^3)
    (hW : ContDiff ℝ (⊤ : ℕ∞) W) (hWdiv : ∀ x, PDE.divergence W x = 0)
    (hF : MemLp (iteratedFDeriv ℝ 0 (stationaryVelocityOperator W)) 2 volume)
    (w : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))) (hw : divergenceCLM w = 0)
    (hweak : ∀ φ : ℝ^3 → ℝ^3, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∀ x, PDE.divergence φ x = 0) →
      ∫ x, (∑ i, (W x i + (wkpBaseCoordinateCLM (w i) : ℝ^3 → ℝ) x) * φ x i +
        (1 / 2 : ℝ) * ∑ i, ∑ j, (W x i + (wkpBaseCoordinateCLM (w i) : ℝ^3 → ℝ) x) * x j *
          (∂[j] (fun y ↦ φ y i)) x -
        ∑ i, ∑ j, (W x i + (wkpBaseCoordinateCLM (w i) : ℝ^3 → ℝ) x) *
          (W x j + (wkpBaseCoordinateCLM (w j) : ℝ^3 → ℝ) x) * (∂[j] (fun y ↦ φ y i)) x -
        ∑ i, (W x i + (wkpBaseCoordinateCLM (w i) : ℝ^3 → ℝ) x) *
          PDE.laplacian (fun y ↦ φ y i) x) = 0)
    {φ : ℝ^3 → ℝ^3} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hdiv : ∀ x, PDE.divergence φ x = 0) :
    ∑ i, ∫ x, (wkpBaseCoordinateCLM (w i) : ℝ^3 → ℝ) x *
        (φ x i + (1 / 2) * fderiv ℝ φ x x i - PDE.laplacian (fun y ↦ φ y i) x) =
      (∑ i, ∫ x, profileForcing W w i x * φ x i) +
        ∑ i, ∑ j, ∫ x, (wkpBaseCoordinateCLM (w j) : ℝ^3 → ℝ) x *
          (wkpBaseCoordinateCLM (w i) : ℝ^3 → ℝ) x * PDE.partialDeriv j (fun y ↦ φ y i) x := by
  have hφi : ∀ i, ContDiff ℝ ∞ (fun x ↦ φ x i) := contDiff_component hφ
  have hφc : ∀ i, HasCompactSupport (fun x ↦ φ x i) := hasCompactSupport_component hc
  have hWi : ∀ i, ContDiff ℝ ∞ (fun x ↦ W x i) := contDiff_component hW
  have hDφ : ∀ i j, Continuous (fun x ↦ (∂[j] (fun y ↦ φ y i)) x) := fun i j ↦
    (PDE.contDiff_top_partialDeriv (hφi i)).continuous
  have hDφc : ∀ i j, HasCompactSupport (fun x ↦ (∂[j] (fun y ↦ φ y i)) x) := fun i j ↦
    (hφc i).partialDeriv j
  have hX : ∀ i, Continuous (fun x ↦ fderiv ℝ φ x x i) :=
    continuous_fderiv_apply_self_component hφ
  have hXc : ∀ i, HasCompactSupport (fun x ↦ fderiv ℝ φ x x i) :=
    hasCompactSupport_fderiv_apply_self_component hc
  have hΔ : ∀ i, Continuous (fun x ↦ PDE.laplacian (fun y ↦ φ y i) x) := fun i ↦
    (PDE.contDiff_laplacian_coord (hφi i)).continuous
  have hΔc : ∀ i, HasCompactSupport (fun x ↦ PDE.laplacian (fun y ↦ φ y i) x) := fun i ↦
    hasCompactSupport_laplacian_coord (hφc i)
  have hfd : ∀ x i, fderiv ℝ φ x x i = ∑ j, x j * (∂[j] (fun y ↦ φ y i)) x := fun x i ↦
    fderiv_apply_component (hφ.differentiable (by simp) x) x i
  -- the profile equation, component by component
  have hmain := hweak φ hφ hc hdiv
  have hpt : ∀ x, (∑ i, (W x i + (wkpBaseCoordinateCLM (w i) : ℝ^3 → ℝ) x) * φ x i +
        (1 / 2 : ℝ) * ∑ i, ∑ j, (W x i + (wkpBaseCoordinateCLM (w i) : ℝ^3 → ℝ) x) * x j *
          (∂[j] (fun y ↦ φ y i)) x -
        ∑ i, ∑ j, (W x i + (wkpBaseCoordinateCLM (w i) : ℝ^3 → ℝ) x) *
          (W x j + (wkpBaseCoordinateCLM (w j) : ℝ^3 → ℝ) x) * (∂[j] (fun y ↦ φ y i)) x -
        ∑ i, (W x i + (wkpBaseCoordinateCLM (w i) : ℝ^3 → ℝ) x) *
          PDE.laplacian (fun y ↦ φ y i) x) =
      ∑ i, ((W x i * φ x i + (1 / 2) * (W x i * fderiv ℝ φ x x i) -
          W x i * PDE.laplacian (fun y ↦ φ y i) x -
          ∑ j, W x i * W x j * (∂[j] (fun y ↦ φ y i)) x) +
        (wkpBaseCoordinateCLM (w i) : ℝ^3 → ℝ) x *
          (φ x i + (1 / 2) * fderiv ℝ φ x x i - PDE.laplacian (fun y ↦ φ y i) x) -
        ∑ j, (wkpBaseCoordinateCLM (w j) : ℝ^3 → ℝ) x * (W x i * (∂[j] (fun y ↦ φ y i)) x) -
        ∑ j, (wkpBaseCoordinateCLM (w i) : ℝ^3 → ℝ) x * (W x j * (∂[j] (fun y ↦ φ y i)) x) -
        ∑ j, (wkpBaseCoordinateCLM (w j) : ℝ^3 → ℝ) x *
          (wkpBaseCoordinateCLM (w i) : ℝ^3 → ℝ) x * (∂[j] (fun y ↦ φ y i)) x) := by
    intro x
    simp only [hfd, Fin.sum_univ_three]
    ring
  -- integrability of the pieces
  have h1 (i : Fin 3) :=
    integrable_mul_of_hasCompactSupport_right (hWi i).continuous (hφi i).continuous (hφc i)
  have h2 (i : Fin 3) := integrable_mul_of_hasCompactSupport_right (hWi i).continuous (hX i) (hXc i)
  have h3 (i : Fin 3) := integrable_mul_of_hasCompactSupport_right (hWi i).continuous (hΔ i) (hΔc i)
  have h4 (i j : Fin 3) : Integrable (fun x ↦ W x i * W x j * (∂[j] (fun y ↦ φ y i)) x) volume :=
    integrable_mul_of_hasCompactSupport_right ((hWi i).continuous.mul (hWi j).continuous)
      (hDφ i j) (hDφc i j)
  have hcB : ∀ i, Integrable (fun x ↦ W x i * φ x i + (1 / 2) * (W x i * fderiv ℝ φ x x i) -
      W x i * PDE.laplacian (fun y ↦ φ y i) x -
      ∑ j, W x i * W x j * (∂[j] (fun y ↦ φ y i)) x) volume := fun i ↦
    (((h1 i).add ((h2 i).const_mul _)).sub (h3 i)).sub (integrable_finsetSum _ fun j _ ↦ h4 i j)
  have hcL : ∀ i, Integrable (fun x ↦ (wkpBaseCoordinateCLM (w i) : ℝ^3 → ℝ) x *
      (φ x i + (1 / 2) * fderiv ℝ φ x x i - PDE.laplacian (fun y ↦ φ y i) x)) volume :=
    fun i ↦ integrable_base_mul (w i) (((hφi i).continuous.add
      (continuous_const.mul (hX i))).sub (hΔ i)) (((hφc i).add (hXc i).mul_left).sub (hΔc i))
  have hc1 : ∀ i j, Integrable (fun x ↦ (wkpBaseCoordinateCLM (w j) : ℝ^3 → ℝ) x *
      (W x i * (∂[j] (fun y ↦ φ y i)) x)) volume := fun i j ↦
    integrable_base_mul (w j) ((hWi i).continuous.mul (hDφ i j)) (hDφc i j).mul_left
  have hc2 : ∀ i j, Integrable (fun x ↦ (wkpBaseCoordinateCLM (w i) : ℝ^3 → ℝ) x *
      (W x j * (∂[j] (fun y ↦ φ y i)) x)) volume := fun i j ↦
    integrable_base_mul (w i) ((hWi j).continuous.mul (hDφ i j)) (hDφc i j).mul_left
  have hcQ : ∀ i j, Integrable (fun x ↦ (wkpBaseCoordinateCLM (w j) : ℝ^3 → ℝ) x *
      (wkpBaseCoordinateCLM (w i) : ℝ^3 → ℝ) x * (∂[j] (fun y ↦ φ y i)) x) volume :=
    fun i j ↦ integrable_mulH1_mul (w j) (w i) (hDφ i j) (hDφc i j)
  -- splitting the profile equation
  set S : Fin 3 → ℝ^3 → ℝ := fun i x ↦ (W x i * φ x i + (1 / 2) * (W x i * fderiv ℝ φ x x i) -
          W x i * PDE.laplacian (fun y ↦ φ y i) x -
          ∑ j, W x i * W x j * (∂[j] (fun y ↦ φ y i)) x) +
        (wkpBaseCoordinateCLM (w i) : ℝ^3 → ℝ) x *
          (φ x i + (1 / 2) * fderiv ℝ φ x x i - PDE.laplacian (fun y ↦ φ y i) x) -
        ∑ j, (wkpBaseCoordinateCLM (w j) : ℝ^3 → ℝ) x * (W x i * (∂[j] (fun y ↦ φ y i)) x) -
        ∑ j, (wkpBaseCoordinateCLM (w i) : ℝ^3 → ℝ) x * (W x j * (∂[j] (fun y ↦ φ y i)) x) -
        ∑ j, (wkpBaseCoordinateCLM (w j) : ℝ^3 → ℝ) x *
          (wkpBaseCoordinateCLM (w i) : ℝ^3 → ℝ) x * (∂[j] (fun y ↦ φ y i)) x with hS
  have hiS : ∀ i, Integrable (S i) volume := fun i ↦
    ((((hcB i).add (hcL i)).sub (integrable_finsetSum _ fun j _ ↦ hc1 i j)).sub
      (integrable_finsetSum _ fun j _ ↦ hc2 i j)).sub (integrable_finsetSum _ fun j _ ↦ hcQ i j)
  have hSi := fun i ↦ integral_eq_of_decomposition (E := S i) (fun x ↦ rfl) (hcB i) (hcL i)
    (hc1 i) (hc2 i) (hcQ i)
  have hsum : ∑ i, ∫ x, S i x = 0 := by
    rw [← integral_finsetSum _ fun i _ ↦ hiS i, ← hmain]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦ (hpt x).symm)
  simp only [hSi] at hsum
  -- the background part
  have hBint : ∀ i, ∫ x, (W x i * φ x i + (1 / 2) * (W x i * fderiv ℝ φ x x i) -
      W x i * PDE.laplacian (fun y ↦ φ y i) x -
      ∑ j, W x i * W x j * (∂[j] (fun y ↦ φ y i)) x) =
      ∫ x, stationaryVelocityOperator W x i * φ x i := by
    intro i
    rw [← integral_background_profile_eq hW hWdiv hφ hc i,
      integral_sub (f := fun x ↦ W x i * φ x i + (1 / 2) * (W x i * fderiv ℝ φ x x i) -
        W x i * PDE.laplacian (fun y ↦ φ y i) x) (((h1 i).add ((h2 i).const_mul _)).sub (h3 i))
        (integrable_finsetSum _ fun j _ ↦ h4 i j),
      integral_sub (f := fun x ↦ W x i * φ x i + (1 / 2) * (W x i * fderiv ℝ φ x x i))
        ((h1 i).add ((h2 i).const_mul _)) (h3 i),
      integral_add (h1 i) ((h2 i).const_mul _), integral_const_mul,
      integral_finsetSum _ fun j _ ↦ h4 i j]
  -- the cross terms
  have hC1 := fun i ↦ sum_integral_base_mul_mul_partialDeriv_eq_neg w hw (hWi i) (hφi i) (hφc i)
  have hC2 := fun i ↦ sum_integral_base_mul_field_mul_partialDeriv_eq_neg (w i) hW hWdiv
    (hφi i) (hφc i)
  -- the forcing
  have hG : ∀ i, ∫ x, profileForcing W w i x * φ x i =
      -(∫ x, stationaryVelocityOperator W x i * φ x i) -
        ∑ j, (∫ x, (wkpBaseCoordinateCLM (w j) : ℝ^3 → ℝ) x *
          ((∂[j] (fun y ↦ W y i)) x * φ x i)) -
        ∑ j, ∫ x, (wkpCoordinateCLM (singleDerivIndex 3 j) (w i) : ℝ^3 → ℝ) x *
          (W x j * φ x i) := by
    intro i
    have iF : Integrable (fun x ↦ stationaryVelocityOperator W x i * φ x i) volume :=
      (memLp_stationaryVelocityOperator_component hF i).integrable_mul (q := 2)
        ((hφi i).continuous.memLp_of_hasCompactSupport (hφc i))
    have iA : ∀ j, Integrable (fun x ↦ (wkpBaseCoordinateCLM (w j) : ℝ^3 → ℝ) x *
        ((∂[j] (fun y ↦ W y i)) x * φ x i)) volume := fun j ↦
      integrable_base_mul (w j) ((PDE.contDiff_top_partialDeriv (hWi i)).continuous.mul
        (hφi i).continuous) (hφc i).mul_left
    have iB : ∀ j, Integrable (fun x ↦
        (wkpCoordinateCLM (singleDerivIndex 3 j) (w i) : ℝ^3 → ℝ) x * (W x j * φ x i))
        volume := fun j ↦ by
      have hm : MemLp (wkpCoordinateCLM (singleDerivIndex 3 j) (w i) : ℝ^3 → ℝ) 2 volume := by
        simpa [domainMeasure] using Lp.memLp (wkpCoordinateCLM (singleDerivIndex 3 j) (w i))
      exact hm.integrable_mul (q := 2) (((hWi j).continuous.mul
        (hφi i).continuous).memLp_of_hasCompactSupport (hφc i).mul_left)
    have hpt2 : ∀ x, profileForcing W w i x * φ x i =
        -(stationaryVelocityOperator W x i * φ x i) -
          ∑ j, (wkpBaseCoordinateCLM (w j) : ℝ^3 → ℝ) x * ((∂[j] (fun y ↦ W y i)) x * φ x i) -
          ∑ j, (wkpCoordinateCLM (singleDerivIndex 3 j) (w i) : ℝ^3 → ℝ) x *
            (W x j * φ x i) := by
      intro x
      simp only [profileForcing, Fin.sum_univ_three]
      ring
    simp only [hpt2]
    rw [integral_sub (f := fun x ↦ -(stationaryVelocityOperator W x i * φ x i) -
        ∑ j, (wkpBaseCoordinateCLM (w j) : ℝ^3 → ℝ) x *
          ((∂[j] (fun y ↦ W y i)) x * φ x i))
        (iF.neg.sub (integrable_finsetSum _ fun j _ ↦ iA j))
        (integrable_finsetSum _ fun j _ ↦ iB j),
      integral_sub (f := fun x ↦ -(stationaryVelocityOperator W x i * φ x i))
        iF.neg (integrable_finsetSum _ fun j _ ↦ iA j), integral_neg,
      integral_finsetSum _ fun j _ ↦ iA j, integral_finsetSum _ fun j _ ↦ iB j]
  simp only [hBint, hC1, hC2] at hsum
  simp only [hG]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib] at hsum ⊢
  linarith

/-- `H²` regularity of weak stationary profiles. Let `W` be a smooth divergence-free field on
`ℝ³` with bounded derivatives whose stationary operator lies in `L²`, and let `w ∈ H¹(ℝ³)³` be
divergence free such that `U = W + w` solves the self-similar profile equation weakly, in the
coordinate form
`∫ ∑ᵢ Uᵢ φᵢ + ½ ∑ᵢⱼ Uᵢ xⱼ ∂ⱼφᵢ - ∑ᵢⱼ Uᵢ Uⱼ ∂ⱼφᵢ - ∑ᵢ Uᵢ Δφᵢ = 0`
for smooth compactly supported divergence-free `φ`. Then every component of `w` is the
first-order part of a function in `H²(ℝ³)`. Smoothness is `C^∞`, written `ContDiff ℝ (⊤ : ℕ∞)`.
Only the bounds on `W` and `DW` and the `L²` bound on the stationary operator itself enter. -/
theorem memH2_of_weakProfileDensity (W : ℝ^3 → ℝ^3) (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (hWbd : ∀ k, ∃ C, ∀ x, ‖iteratedFDeriv ℝ k W x‖ ≤ C)
    (hWdiv : ∀ x, PDE.divergence W x = 0)
    (hF : ∀ k, MemLp (iteratedFDeriv ℝ k (stationaryVelocityOperator W)) 2 volume)
    (w : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))) (hw : divergenceCLM w = 0)
    (hweak : ∀ φ : ℝ^3 → ℝ^3, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∀ x, PDE.divergence φ x = 0) →
      ∫ x, (∑ i, (W x i + (wkpBaseCoordinateCLM (w i) : ℝ^3 → ℝ) x) * φ x i +
        (1 / 2 : ℝ) * ∑ i, ∑ j, (W x i + (wkpBaseCoordinateCLM (w i) : ℝ^3 → ℝ) x) * x j *
          (∂[j] (fun y ↦ φ y i)) x -
        ∑ i, ∑ j, (W x i + (wkpBaseCoordinateCLM (w i) : ℝ^3 → ℝ) x) *
          (W x j + (wkpBaseCoordinateCLM (w j) : ℝ^3 → ℝ) x) * (∂[j] (fun y ↦ φ y i)) x -
        ∑ i, (W x i + (wkpBaseCoordinateCLM (w i) : ℝ^3 → ℝ) x) *
          PDE.laplacian (fun y ↦ φ y i) x) = 0) :
    ∀ i, ∃ V : W^{2,2}(ℝ^3),
      lowerOrderCLM (n := 3) (p := 2) (Ω := univ) (by norm_num : 1 ≤ 2) V = w i := by
  set G := profileForcingL2 hW hWbd (hF 0) w
  suffices h : ∃ z : VectorH 3 2, vectorLower 3 1 z = w by
    obtain ⟨z, hz⟩ := h
    intro i
    exact ⟨z i, by rw [← vectorLower_apply, hz]⟩
  apply exists_vectorH2_of_weak_convection w hw w hw G
  intro φ hφ hc hdiv
  rw [sum_integral_eq_profileForcing_of_weakProfileDensity W hW hWdiv (hF 0) w hw hweak hφ hc
    hdiv]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ integral_congr_ae ?_
  filter_upwards [wkpBaseCoordinateCLM_profileForcingL2_ae hW hWbd (hF 0) w i] with x hx
  rw [hx]

/-- The weak profile equation of `W + w`, `w ∈ H¹(ℝ³)³`, in the coordinates of the
representatives of `w`. -/
theorem integral_coordinates_eq_zero_of_weakProfileEquation {W : ℝ^3 → ℝ^3}
    (w : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3)))
    (hweak : Nonuniqueness.WeakProfileEquation (W + representative w)) {φ : ℝ^3 → ℝ^3}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hdiv : ∀ x, PDE.divergence φ x = 0) :
    ∫ x, (∑ i, (W x i + (wkpBaseCoordinateCLM (w i) : ℝ^3 → ℝ) x) * φ x i +
        (1 / 2 : ℝ) * ∑ i, ∑ j, (W x i + (wkpBaseCoordinateCLM (w i) : ℝ^3 → ℝ) x) * x j *
          (∂[j] (fun y ↦ φ y i)) x -
        ∑ i, ∑ j, (W x i + (wkpBaseCoordinateCLM (w i) : ℝ^3 → ℝ) x) *
          (W x j + (wkpBaseCoordinateCLM (w j) : ℝ^3 → ℝ) x) * (∂[j] (fun y ↦ φ y i)) x -
        ∑ i, (W x i + (wkpBaseCoordinateCLM (w i) : ℝ^3 → ℝ) x) *
          PDE.laplacian (fun y ↦ φ y i) x) = 0 := by
  rw [← (hweak φ ⟨hφ, hc, hdiv⟩).2]
  apply integral_congr_ae
  filter_upwards with x
  rw [Nonuniqueness.weakProfileDensity_eq_sum _ (hφ.of_le (by simp))]
  rfl

/-- `H²` regularity of weak stationary profiles (the regularity step of Appendix F of
Hou, Wang and Yang). Let `W` be a smooth divergence-free field on `ℝ³` with bounded
derivatives of every order and all derivatives of its stationary operator in `L²`. If
`w ∈ H¹(ℝ³)³` is divergence free and `W + w` is a weak solution of the self-similar profile
equation, then every component of `w` is the first-order part of a function in `H²(ℝ³)`.
Smoothness is `C^∞`, written `ContDiff ℝ (⊤ : ℕ∞)`; with the analytic order `⊤ : WithTop ℕ∞`
the hypothesis would ask for analyticity. -/
theorem memH2_of_weak_profile (W : ℝ^3 → ℝ^3) (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (hWbd : ∀ k, ∃ C, ∀ x, ‖iteratedFDeriv ℝ k W x‖ ≤ C)
    (hWdiv : ∀ x, PDE.divergence W x = 0)
    (hF : ∀ k, MemLp (iteratedFDeriv ℝ k (stationaryVelocityOperator W)) 2 volume)
    (w : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))) (hw : divergenceCLM w = 0)
    (hweak : Nonuniqueness.WeakProfileEquation (W + representative w)) :
    ∀ i, ∃ V : W^{2,2}(ℝ^3),
      lowerOrderCLM (n := 3) (p := 2) (Ω := univ) (by norm_num : 1 ≤ 2) V = w i := by
  exact memH2_of_weakProfileDensity W hW hWbd hWdiv hF w hw fun φ hφ hc hdiv ↦
    integral_coordinates_eq_zero_of_weakProfileEquation w hweak hφ hc hdiv

end NavierStokes.Stationary
