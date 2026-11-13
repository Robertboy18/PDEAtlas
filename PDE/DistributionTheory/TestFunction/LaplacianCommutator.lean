/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.TestFunction.IntegrationByParts
public import PDE.FDeriv.Laplacian.Product
import PDE.FDeriv.Laplacian.Congruence
import PDE.Analysis.Calculus.SpaceTime.Localization.Spatial
import PDE.FDeriv.Laplacian.Continuity
import CAS.ExactTactic

/-!
# Transferring a localized Laplacian onto a test kernel

Pairing the commutator of the Laplacian and a compact cutoff against a smooth
kernel transfers all derivatives of the local field to the cutoff and kernel.
Only spatial `C²` regularity near the cutoff support is required. In particular,
the resulting pairing can be estimated using the field's L1 norm.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

namespace PDE.DistributionTheory

variable {n : ℕ}

/-- The Laplacian commutator paired with a smooth kernel contains no derivative
of the local field after integration by parts. The support and regularity
conditions imply every required integrability statement. -/
theorem integral_laplacian_commutator_mul_eq
    {Ω : Set (ℝ^n)} {χ u G : ℝ^n → ℝ}
    (hΩ : IsOpen Ω) (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ)
    (hχΩ : tsupport χ ⊆ Ω) (hu : ContDiffOn ℝ 2 u Ω)
    (hG : ContDiff ℝ 2 G) :
    (∫ x, G x * (χ x * laplacian u x - laplacian (fun y ↦ χ y * u y) x)) =
      ∫ x, (laplacian χ x * G x +
        2 * ∑ i : Fin n, (∂[i] χ) x * (∂[i] G) x) * u x := by
  have hχu : ContDiff ℝ 2 (fun x ↦ χ x * u x) := by
    simpa only [smul_eq_mul] using
      PDE.Analysis.contDiff_spatial_cutoff_smul hΩ hχ hχΩ hu
  have huc (x : ℝ^n) (hx : x ∈ tsupport χ) : ContDiffAt ℝ 2 u x :=
    hu.contDiffAt (hΩ.mem_nhds (hχΩ hx))
  have hA : Integrable (fun x ↦ χ x * G x * laplacian u x) := by
    apply hc.integrable_of_continuousOn_tsupport
    · intro x hx
      exact ((hχ.continuous.continuousAt.mul hG.continuous.continuousAt).mul
        (huc x hx).continuousAt_coordinate_laplacian).continuousWithinAt
    · intro x hx
      simp only [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  have hB : Integrable (fun x ↦ laplacian (fun y ↦ χ y * u y) x * G x) :=
    (hχu.continuous_coordinate_laplacian.mul hG.continuous).integrable_of_hasCompactSupport
      (hc.mul_right.coordinate_laplacian.mul_right)
  have hC : Integrable (fun x ↦ laplacian (fun y ↦ χ y * G y) x * u x) := by
    apply hc.integrable_of_continuousOn_tsupport
    · intro x hx
      exact ((hχ.mul hG).continuous_coordinate_laplacian.continuousAt.mul
        (huc x hx).continuousAt).continuousWithinAt
    · intro x hx
      have hL : laplacian (fun y ↦ χ y * G y) x = 0 :=
        EuclideanLaplacian.laplacian_eq_zero_of_notMem_tsupport
          (fun hy ↦ hx (tsupport_mul_subset_left hy))
      rw [hL, zero_mul]
  have hD : Integrable (fun x ↦ (χ x * u x) * laplacian G x) :=
    (hχu.continuous.mul hG.continuous_coordinate_laplacian).integrable_of_hasCompactSupport
      (hc.mul_right.mul_right)
  have hfirst := integral_mul_laplacian_eq_of_contDiffAt
    (hχ.mul hG) hc.mul_right (fun x hx ↦ huc x (tsupport_mul_subset_left hx))
  have hsecond := integral_mul_laplacian_eq G hχu hG hc.mul_right
  calc
    _ = (∫ x, χ x * G x * laplacian u x) -
        ∫ x, laplacian (fun y ↦ χ y * u y) x * G x := by
      rw [← integral_sub hA hB]
      apply integral_congr_ae
      exact Eventually.of_forall fun x ↦ by cas
    _ = (∫ x, laplacian (fun y ↦ χ y * G y) x * u x) -
        ∫ x, (χ x * u x) * laplacian G x := by rw [hfirst, hsecond]
    _ = _ := by
      rw [← integral_sub hC hD]
      apply integral_congr_ae
      exact Eventually.of_forall fun x ↦ by
        dsimp only
        rw [laplacian_mul hχ.contDiffAt hG.contDiffAt]
        cas

/-- A compact cutoff makes its Laplacian commutator integrable against any
continuous kernel. The original field only needs local spatial regularity. -/
theorem integrable_laplacian_commutator_mul
    {Ω : Set (ℝ^n)} {χ u G : ℝ^n → ℝ}
    (hΩ : IsOpen Ω) (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ)
    (hχΩ : tsupport χ ⊆ Ω) (hu : ContDiffOn ℝ 2 u Ω) (hG : Continuous G) :
    Integrable (fun x ↦
      G x * (χ x * laplacian u x - laplacian (fun y ↦ χ y * u y) x)) := by
  have hχu : ContDiff ℝ 2 (fun x ↦ χ x * u x) := by
    simpa only [smul_eq_mul] using
      PDE.Analysis.contDiff_spatial_cutoff_smul hΩ hχ hχΩ hu
  have hcont : ContinuousOn (fun x ↦
      G x * (χ x * laplacian u x - laplacian (fun y ↦ χ y * u y) x))
      (tsupport χ) := by
    intro x hx
    exact (hG.continuousAt.mul ((hχ.continuous.continuousAt.mul
      (hu.contDiffAt (hΩ.mem_nhds (hχΩ hx))).continuousAt_coordinate_laplacian).sub
        hχu.continuous_coordinate_laplacian.continuousAt)).continuousWithinAt
  apply (hcont.integrableOn_compact hc).integrable_of_forall_notMem_eq_zero
  intro x hx
  have hL : laplacian (fun y ↦ χ y * u y) x = 0 :=
    EuclideanLaplacian.laplacian_eq_zero_of_notMem_tsupport
      (fun hy ↦ hx (tsupport_mul_subset_left hy))
  rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, hL, sub_self, mul_zero]

/-- A scalar linear combination of a localized field and its Laplacian
commutator has a pairing depending only on the field itself. This is the
form used when a spatial cutoff is multiplied by a time cutoff. -/
theorem integral_linear_laplacian_commutator_mul_eq
    {Ω : Set (ℝ^n)} {χ u G : ℝ^n → ℝ}
    (hΩ : IsOpen Ω) (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ)
    (hχΩ : tsupport χ ⊆ Ω) (hu : ContDiffOn ℝ 2 u Ω)
    (hG : ContDiff ℝ 2 G) (α β : ℝ) :
    (∫ x, G x * (α * (χ x * u x) +
      β * (χ x * laplacian u x - laplacian (fun y ↦ χ y * u y) x))) =
      α * (∫ x, G x * (χ x * u x)) +
        β * ∫ x, (laplacian χ x * G x +
          2 * ∑ i : Fin n, (∂[i] χ) x * (∂[i] G) x) * u x := by
  have hχu : ContDiff ℝ 2 (fun x ↦ χ x * u x) := by
    simpa only [smul_eq_mul] using
      PDE.Analysis.contDiff_spatial_cutoff_smul hΩ hχ hχΩ hu
  have hfirst : Integrable (fun x ↦ G x * (χ x * u x)) :=
    (hG.continuous.mul hχu.continuous).integrable_of_hasCompactSupport
      hc.mul_right.mul_left
  have hsecond := integrable_laplacian_commutator_mul hΩ hχ hc hχΩ hu hG.continuous
  calc
    _ = (∫ x, α * (G x * (χ x * u x))) +
        ∫ x, β * (G x *
          (χ x * laplacian u x - laplacian (fun y ↦ χ y * u y) x)) := by
      rw [← integral_add (hfirst.const_mul α) (hsecond.const_mul β)]
      apply integral_congr_ae
      exact Eventually.of_forall fun x ↦ by cas
    _ = _ := by
      rw [integral_const_mul, integral_const_mul,
        integral_laplacian_commutator_mul_eq hΩ hχ hc hχΩ hu hG]

/-- Expanding the transferred commutator gives finitely many weighted kernel
pairings. This form separates the source, cutoff coefficients and kernel
derivatives for convolution estimates. -/
theorem integral_linear_laplacian_commutator_mul_eq_sum
    {Ω : Set (ℝ^n)} {χ u G : ℝ^n → ℝ}
    (hΩ : IsOpen Ω) (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ)
    (hχΩ : tsupport χ ⊆ Ω) (hu : ContDiffOn ℝ 2 u Ω)
    (hG : ContDiff ℝ 2 G) (α β : ℝ) :
    (∫ x, G x * (α * (χ x * u x) +
      β * (χ x * laplacian u x - laplacian (fun y ↦ χ y * u y) x))) =
      (∫ x, ((α * χ x + β * laplacian χ x) * u x) * G x) +
        ∑ i : Fin n, ∫ x, (2 * β * (∂[i] χ) x * u x) * (∂[i] G) x := by
  have huc : ContinuousOn u (tsupport χ) := hu.continuousOn.mono hχΩ
  have hpartial (i : Fin n) : Continuous (∂[i] χ) :=
    (contDiff_partialDeriv_of_succ (m := 1) hχ).continuous
  have hpartialG (i : Fin n) : Continuous (∂[i] G) :=
    (contDiff_partialDeriv_of_succ (m := 1) hG).continuous
  have hzero (i : Fin n) (x : ℝ^n) (hx : x ∉ tsupport χ) : (∂[i] χ) x = 0 := by
    simp only [partialDeriv, fderiv_of_notMem_tsupport ℝ hx, zero_apply]
  have hLzero (x : ℝ^n) (hx : x ∉ tsupport χ) : laplacian χ x = 0 := by
    exact EuclideanLaplacian.laplacian_eq_zero_of_notMem_tsupport hx
  have hA : Integrable (fun x ↦ G x * (χ x * u x)) := by
    apply hc.integrable_of_continuousOn_tsupport
      (hG.continuous.continuousOn.mul (hχ.continuous.continuousOn.mul huc))
    intro x hx
    dsimp only [Pi.mul_apply]
    rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, mul_zero]
  have hB : Integrable (fun x ↦ laplacian χ x * G x * u x) := by
    apply hc.integrable_of_continuousOn_tsupport
      ((hχ.continuous_coordinate_laplacian.mul hG.continuous).continuousOn.mul huc)
    intro x hx
    dsimp only [Pi.mul_apply]
    rw [hLzero x hx, zero_mul, zero_mul]
  have hD (i : Fin n) : Integrable (fun x ↦ (∂[i] χ) x * (∂[i] G) x * u x) := by
    apply hc.integrable_of_continuousOn_tsupport
      (((hpartial i).mul (hpartialG i)).continuousOn.mul huc)
    intro x hx
    dsimp only [Pi.mul_apply]
    rw [hzero i x hx, zero_mul, zero_mul]
  have hR : Integrable (fun x ↦
      (laplacian χ x * G x + 2 * ∑ i : Fin n, (∂[i] χ) x * (∂[i] G) x) *
        u x) := by
    convert hB.add ((integrable_finsetSum Finset.univ fun i _ ↦ hD i).const_mul 2) using 1
    ext x
    simp only [Pi.add_apply, add_mul, Finset.sum_mul, mul_assoc]
  have hmain : Integrable (fun x ↦ ((α * χ x + β * laplacian χ x) * u x) * G x) := by
    convert (hA.const_mul α).add (hB.const_mul β) using 1
    ext x
    cas
  have hsum (i : Fin n) :
      Integrable (fun x ↦ (2 * β * (∂[i] χ) x * u x) * (∂[i] G) x) := by
    convert (hD i).const_mul (2 * β) using 1
    ext x
    cas
  rw [integral_linear_laplacian_commutator_mul_eq hΩ hχ hc hχΩ hu hG,
    ← integral_const_mul, ← integral_const_mul,
    ← integral_add (hA.const_mul α) (hR.const_mul β),
    ← integral_finsetSum Finset.univ (fun i _ ↦ hsum i),
    ← integral_add hmain (integrable_finsetSum Finset.univ fun i _ ↦ hsum i)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x ↦ by
    dsimp only
    simp only [add_mul, mul_add, Finset.mul_sum, Finset.sum_mul]
    rw [← add_assoc]
    congr 1
    · cas
    · apply Finset.sum_congr rfl
      intro i _
      cas

end PDE.DistributionTheory
