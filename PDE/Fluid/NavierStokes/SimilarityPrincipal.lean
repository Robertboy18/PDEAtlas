/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Energy
import PDE.Analysis.Integration.CompactPairing
import PDE.Analysis.MeasureTheory.Lp.NonnegativeMultiplier
import PDE.FDeriv.PartialDeriv.Regularity

/-!
# The similarity principal form

For the stationary similarity equation, a matrix compensation of the velocity
gradient gives separate L2 and Dirichlet lower bounds on compact smooth test
fields. The compensation is supplied as a pointwise quadratic-form inequality;
it can therefore come from a certified numerical multiplier. On smooth test fields this is the
energy calculation behind the coercivity (4.3) of Hou, Wang and Yang. On bounded
open domains the same estimate holds on completed vector `H¹₀` with a `W^{1,∞}`
background and an almost-everywhere matrix certificate. These bounded coefficients
construct a continuous operator from vector `H¹₀` to its strong dual. Positive
mass compensation gives coercivity, including on the closed weak-divergence
kernel, where Lax–Milgram solves the linear equation for every dual load
(`existsUnique_solenoidal_similarity_principal_solution`, through
`PDE.Analysis.Variational.IsWeakSolution.existsUnique`, which is built on Mathlib's
`IsCoercive.continuousLinearEquivOfBilin`).
The global dilation drift requires a separate exhaustion argument; it is not a
bounded whole-space coefficient.

If the compensated background gradient `Db + Q` is bounded below by `-η` as a quadratic form,
the principal form is at least `((n - 2)/4 - η) ‖u‖₂² + ‖∇u‖₂²` in dimension `n`, that is
`(1/4 - η) ‖u‖₂² + ‖∇u‖₂²` in three dimensions, and it is coercive when `η < (n - 2)/4`
(`similarityPrincipalForm_lower_bound`, `similarityPrincipalForm_isCoercive`).

## References

* T. Hou, Y. Wang, and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Section 4.1, (4.1)-(4.3), p. 24.
  <https://arxiv.org/abs/2509.25116v2>
* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.2.1, Theorem 1 (Lax–Milgram Theorem), pp. 315-316.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace NavierStokes

open EuclideanSpace MeasureTheory Order
open scoped InnerProductSpace

set_option linter.missingDocs true

/-- On compact smooth tests, a certified gradient compensation gives the
principal similarity form its mass and Dirichlet coercivity. This statement
uses the unprojected weak pairing; the pressure or Leray projection term must
separately be removed against divergence-free tests in an application.

The hypotheses here concern smooth coefficients. The numerical profile's
regularity at the origin, and extension to whole-space H1 tests, are separate obligations. -/
theorem similarity_principal_pairing_lower_bound
    {n : ℕ} {u b : ℝ^n → ℝ^n} {Q : ℝ^n → ℝ^n →L[ℝ] ℝ^n} {η : ℝ}
    (hu : ContDiff ℝ 2 u) (hb : ContDiff ℝ 1 b) (hc : HasCompactSupport u)
    (hQ : Continuous Q) (hdiv : ∀ x, PDE.divergence b x = 0)
    (hcompensation : ∀ x v,
      0 ≤ ⟪(fderiv ℝ b x + Q x + η • ContinuousLinearMap.id ℝ (ℝ^n)) v, v⟫_ℝ) :
    (((n : ℝ) - 2) / 4 - η) * (∫ x, ‖u x‖ ^ 2) +
        (∑ i : Fin n, ∫ x, ‖∂[i] u x‖ ^ 2) ≤
      ∫ x, ⟪(-1 / 2 : ℝ) • u x - (1 / 2 : ℝ) • fderiv ℝ u x x -
        PDE.laplacian u x + fderiv ℝ u x (b x) + fderiv ℝ b x (u x) +
        Q x (u x), u x⟫_ℝ := by
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hsquareCompact : HasCompactSupport (fun x ↦ ‖u x‖ ^ 2) :=
    hc.comp_left (g := fun v : ℝ^n ↦ ‖v‖ ^ 2) (by simp)
  have hsquare : Integrable (fun x ↦ ‖u x‖ ^ 2) :=
    (hu.continuous.norm.pow 2).integrable_of_hasCompactSupport hsquareCompact
  have hdu : Continuous (fun x ↦ fderiv ℝ u x x) :=
    (hu1.continuous_fderiv one_ne_zero).clm_apply continuous_id
  have htransport : Continuous (fun x ↦ fderiv ℝ u x (b x)) :=
    (hu1.continuous_fderiv one_ne_zero).clm_apply hb.continuous
  have hstretch : Continuous (fun x ↦ fderiv ℝ b x (u x) + Q x (u x)) :=
    ((hb.continuous_fderiv one_ne_zero).clm_apply hu.continuous).add
      (hQ.clm_apply hu.continuous)
  have hpartial (i : Fin n) : ContDiff ℝ 1 (∂[i] u) :=
    hu.partialDeriv i (by norm_num)
  have hlaplacian : Continuous (PDE.laplacian u) :=
    continuous_finsetSum _ fun i _ ↦ (hpartial i).continuous_partialDeriv i
  let d : ℝ^n → ℝ := fun x ↦
    ⟪(-1 / 2 : ℝ) • u x - (1 / 2 : ℝ) • fderiv ℝ u x x, u x⟫_ℝ
  let l : ℝ^n → ℝ := fun x ↦ ⟪PDE.laplacian u x, u x⟫_ℝ
  let a : ℝ^n → ℝ := fun x ↦ ⟪fderiv ℝ u x (b x), u x⟫_ℝ
  let m : ℝ^n → ℝ := fun x ↦ ⟪fderiv ℝ b x (u x) + Q x (u x), u x⟫_ℝ
  have hdrift : Continuous (fun x ↦
      (-1 / 2 : ℝ) • u x - (1 / 2 : ℝ) • fderiv ℝ u x x) :=
    (hu.continuous.const_smul (-1 / 2 : ℝ)).sub (hdu.const_smul (1 / 2 : ℝ))
  have hd : Integrable d :=
    hdrift.locallyIntegrable.integrable_inner_right_of_hasCompactSupport hu.continuous hc
  have hl : Integrable l :=
    hlaplacian.locallyIntegrable.integrable_inner_right_of_hasCompactSupport hu.continuous hc
  have ha : Integrable a :=
    htransport.locallyIntegrable.integrable_inner_right_of_hasCompactSupport hu.continuous hc
  have hm : Integrable m :=
    hstretch.locallyIntegrable.integrable_inner_right_of_hasCompactSupport hu.continuous hc
  have hlower : -η * (∫ x, ‖u x‖ ^ 2) ≤ ∫ x, m x := by
    rw [← integral_const_mul]
    apply integral_mono (hsquare.const_mul (-η)) hm
    intro x
    have h := hcompensation x (u x)
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.id_apply, inner_add_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq] at h
    dsimp [m]
    rw [inner_add_left]
    linarith
  have hdvalue : (∫ x, d x) = ((n : ℝ) - 2) / 4 * ∫ x, ‖u x‖ ^ 2 :=
    PDE.Analysis.integral_inner_similarity_drift hu1 hc
  have hlvalue : (∫ x, l x) = -∑ i : Fin n, ∫ x, ‖∂[i] u x‖ ^ 2 := by
    simpa only [l, real_inner_comm] using PDE.Analysis.integral_inner_laplacian_eq_neg_sum hu hc
  have havalue : (∫ x, a x) = 0 := PDE.Analysis.integral_inner_advection_eq_zero hu1 hb hc hdiv
  have hintegrand (x : ℝ^n) :
      ⟪(-1 / 2 : ℝ) • u x - (1 / 2 : ℝ) • fderiv ℝ u x x -
        PDE.laplacian u x + fderiv ℝ u x (b x) + fderiv ℝ b x (u x) +
        Q x (u x), u x⟫_ℝ = d x - l x + a x + m x := by
    simp only [d, l, a, m, inner_sub_left, inner_add_left]
    ring
  simp_rw [hintegrand]
  change _ ≤ ∫ x, ((d - l + a) + m) x
  rw [integral_add' ((hd.sub hl).add ha) hm, integral_add' (hd.sub hl) ha,
    integral_sub' hd hl, hdvalue, hlvalue, havalue]
  linarith


open SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Sobolev

/-- The principal similarity form on completed zero-boundary fields.

The Laplacian is used in its weak Dirichlet form. The background has only weak
bounded derivatives, and the compensation is certified almost everywhere.
Pressure recovery and the whole-space exhaustion argument remain separate. -/
theorem similarity_principal_weak_pairing_lower_bound {n : ℕ} {Ω : Set (ℝ^n)}
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (A : Fin n → W^{1,∞}(Ω))
    (Q : Fin n → Fin n → DerivLp n ∞ Ω) (η : ℝ)
    (hdiv : ∑ i, (A i : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n i) = 0)
    (hcompensation : ∀ᵐ x ∂domainMeasure n Ω, ∀ v : Fin n → ℝ,
      -η * (∑ k, (v k) ^ 2) ≤
        ∑ k, ∑ j, ((A k : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n j) +
          Q k j) x * v j * v k)
    (U : H¹₀(Ω; ℝ^n)) :
    (((n : ℝ) - 2) / 4 - η) * ‖ZeroBoundaryVectorSpace.toLp U‖ ^ 2 +
        ‖ZeroBoundaryVectorSpace.gradient U‖ ^ 2 ≤
      (-1 / 2 : ℝ) * ‖ZeroBoundaryVectorSpace.toLp U‖ ^ 2 -
        (1 / 2 : ℝ) * (∑ k, ∑ i,
          ⟪((coordinateW1Top hΩ hb i : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1)) •
            derivCoordCLM i (U k), baseCoordCLM (U k)⟫_ℝ) +
        ‖ZeroBoundaryVectorSpace.gradient U‖ ^ 2 +
        (∑ k, ∑ i,
          ⟪((A i : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1)) •
            derivCoordCLM i (U k), baseCoordCLM (U k)⟫_ℝ) +
        (∑ k, ∑ j,
          ⟪((A k : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n j) + Q k j) •
            baseCoordCLM (U j), baseCoordCLM (U k)⟫_ℝ) := by
  have hdilation :
      (∑ k, ∑ i,
        ⟪((coordinateW1Top hΩ hb i : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1)) •
          derivCoordCLM i (U k), baseCoordCLM (U k)⟫_ℝ) =
        -(n : ℝ) / 2 * (∑ k, ‖baseCoordCLM (U k)‖ ^ 2) := by
    simp_rw [sum_inner_coordinate_mul_deriv_self_H10 hΩ hb]
    rw [Finset.mul_sum]
  have htransport :
      (∑ k, ∑ i,
        ⟪((A i : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1)) •
          derivCoordCLM i (U k), baseCoordCLM (U k)⟫_ℝ) = 0 := by
    simp_rw [sum_inner_mul_deriv_self_H10 hΩ A, hdiv]
    simp
  have hmatrix := MeasureTheory.Lp.sum_inner_lpSMul_matrix_self_lower_bound
    (fun k j ↦ (A k : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n j) + Q k j)
    η hcompensation (fun k ↦ baseCoordCLM (U k))
  rw [ZeroBoundaryVectorSpace.norm_toLp_sq, ZeroBoundaryVectorSpace.norm_gradient_sq,
    hdilation, htransport]
  nlinarith only [hmatrix]

/-! ## The bounded-domain stationary similarity operator -/

noncomputable section SimilarityPrincipal

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The weak stationary similarity operator, with bounded-domain dilation,
background transport, stretching, and the actual compensation multiplier. -/
def similarityPrincipalForm (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (b : Fin n → W^{1,∞}(Ω)) (Q : Fin n → Fin n → DerivLp n ∞ Ω) :
    H¹₀(Ω; ℝ^n) →L[ℝ] StrongDual ℝ (H¹₀(Ω; ℝ^n)) :=
  let π : Fin n → H¹₀(Ω; ℝ^n) →L[ℝ] H¹₀(Ω) := fun k ↦
    (ContinuousLinearMap.proj k).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ H¹₀(Ω))).toContinuousLinearMap
  let b₀ := fun i ↦ (b i : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1)
  let x₀ := fun i ↦ (coordinateW1Top hΩ hb i : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1)
  let c := fun k j ↦ (b k : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n j) + Q k j
  let scalar := dirichletForm + lowerOrderForm (fun i ↦ mulLpLeft (b₀ i)) 0 -
    (1 / 2 : ℝ) • lowerOrderForm (fun i ↦ mulLpLeft (x₀ i))
      (ContinuousLinearMap.id ℝ (DerivLp n 2 Ω))
  let pairing : DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω →L[ℝ] ℝ :=
    LinearMap.mkContinuous₂ (innerₗ (DerivLp n 2 Ω)) 1 fun u v ↦ by
      simpa only [innerₗ_apply_apply, one_mul] using norm_inner_le_norm u v
  (∑ k, scalar.bilinearComp (π k) (π k)) +
    ∑ k, ∑ j, pairing.bilinearComp
      ((mulLpLeft (c k j)).comp (baseCoordCLM.comp (π j)))
      (baseCoordCLM.comp (π k))

/-- Coordinate formula for the weak stationary similarity operator. -/
theorem similarityPrincipalForm_apply (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (b : Fin n → W^{1,∞}(Ω)) (Q : Fin n → Fin n → DerivLp n ∞ Ω)
    (U V : H¹₀(Ω; ℝ^n)) :
    similarityPrincipalForm hΩ hb b Q U V =
      (∑ k, (
        (∑ i, ⟪derivCoordCLM i (U k), derivCoordCLM i (V k)⟫_ℝ) +
        (∑ i, ⟪((b i : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1)) •
          derivCoordCLM i (U k), baseCoordCLM (V k)⟫_ℝ) -
        (1 / 2 : ℝ) *
          ((∑ i, ⟪((coordinateW1Top hΩ hb i : WkpAmbientOn n 1 ∞ Ω)
            (baseIndex n 1)) • derivCoordCLM i (U k), baseCoordCLM (V k)⟫_ℝ) +
            ⟪baseCoordCLM (U k), baseCoordCLM (V k)⟫_ℝ))) +
      ∑ k, ∑ j,
        ⟪((b k : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n j) + Q k j) •
          baseCoordCLM (U j), baseCoordCLM (V k)⟫_ℝ := by
  simp only [similarityPrincipalForm, add_apply, sum_apply,
    ContinuousLinearMap.bilinearComp_apply, sub_apply, smul_apply, smul_eq_mul,
    dirichletForm_apply, lowerOrderForm_apply, mulLpLeft_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.id_apply, zero_apply, inner_zero_left, add_zero,
    LinearMap.mkContinuous₂_apply, innerₗ_apply_apply]
  rfl

/-- Mass and Dirichlet lower bounds for the constructed stationary operator. -/
theorem similarityPrincipalForm_lower_bound (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (b : Fin n → W^{1,∞}(Ω)) (Q : Fin n → Fin n → DerivLp n ∞ Ω) (η : ℝ)
    (hdiv : ∑ i, (b i : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n i) = 0)
    (hcompensation : ∀ᵐ x ∂domainMeasure n Ω, ∀ v : Fin n → ℝ,
      -η * (∑ k, (v k) ^ 2) ≤
        ∑ k, ∑ j, ((b k : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n j) +
          Q k j) x * v j * v k)
    (U : H¹₀(Ω; ℝ^n)) :
    (((n : ℝ) - 2) / 4 - η) * ‖ZeroBoundaryVectorSpace.toLp U‖ ^ 2 +
      ‖ZeroBoundaryVectorSpace.gradient U‖ ^ 2 ≤ similarityPrincipalForm hΩ hb b Q U U := by
  have h := similarity_principal_weak_pairing_lower_bound hΩ hb b Q η hdiv hcompensation U
  rw [similarityPrincipalForm_apply]
  simp only [ZeroBoundaryVectorSpace.norm_toLp_sq,
    ZeroBoundaryVectorSpace.norm_gradient_sq] at h ⊢
  simp only [real_inner_self_eq_norm_sq, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, mul_add, ← Finset.mul_sum] at h ⊢
  linarith only [h]

/-- Positive mass compensation gives coercivity in the full Hilbert Sobolev norm. -/
theorem similarityPrincipalForm_isCoercive (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (b : Fin n → W^{1,∞}(Ω)) (Q : Fin n → Fin n → DerivLp n ∞ Ω) (η : ℝ)
    (hdiv : ∑ i, (b i : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n i) = 0)
    (hcompensation : ∀ᵐ x ∂domainMeasure n Ω, ∀ v : Fin n → ℝ,
      -η * (∑ k, (v k) ^ 2) ≤
        ∑ k, ∑ j, ((b k : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n j) +
          Q k j) x * v j * v k)
    (hη : η < ((n : ℝ) - 2) / 4) :
    IsCoercive (similarityPrincipalForm hΩ hb b Q) := by
  let c := min (((n : ℝ) - 2) / 4 - η) 1
  have hc : 0 < c := lt_min (sub_pos.mpr hη) zero_lt_one
  refine ⟨c, hc, fun U ↦ ?_⟩
  have h := similarityPrincipalForm_lower_bound hΩ hb b Q η hdiv hcompensation U
  have hmass := mul_le_mul_of_nonneg_right
    (min_le_left (((n : ℝ) - 2) / 4 - η) 1)
    (sq_nonneg ‖ZeroBoundaryVectorSpace.toLp U‖)
  have hgradient := mul_le_mul_of_nonneg_right
    (min_le_right (((n : ℝ) - 2) / 4 - η) 1)
    (sq_nonneg ‖ZeroBoundaryVectorSpace.gradient U‖)
  calc
    c * ‖U‖ * ‖U‖ = c * ‖U‖ ^ 2 := by ring
    _ = c * ‖ZeroBoundaryVectorSpace.toLp U‖ ^ 2 +
        c * ‖ZeroBoundaryVectorSpace.gradient U‖ ^ 2 := by
      rw [ZeroBoundaryVectorSpace.norm_sq, mul_add]
    _ ≤ (((n : ℝ) - 2) / 4 - η) * ‖ZeroBoundaryVectorSpace.toLp U‖ ^ 2 +
        ‖ZeroBoundaryVectorSpace.gradient U‖ ^ 2 :=
      add_le_add hmass (by simpa only [one_mul] using hgradient)
    _ ≤ similarityPrincipalForm hΩ hb b Q U U := h

local notation "Vσ" => IncompressibleFlow.SolenoidalSpace
  (ZeroBoundaryVectorSpace.divergence (n := n) (Ω := Ω))

/-- The inherited Hilbert structure on the weak-divergence kernel. -/
local instance innerProductSpaceSolenoidal : InnerProductSpace ℝ Vσ :=
  Submodule.innerProductSpace (𝕜 := ℝ) (E := H¹₀(Ω; ℝ^n))
    (ZeroBoundaryVectorSpace.divergence (n := n) (Ω := Ω)).ker

/-- Use the normed structure underlying this same inherited Hilbert structure. -/
local instance normedSpaceSolenoidal : NormedSpace ℝ Vσ :=
  innerProductSpaceSolenoidal.toNormedSpace

/-- The kernel is complete because weak divergence is continuous. -/
local instance completeSpaceSolenoidal : CompleteSpace Vσ :=
  ContinuousLinearMap.completeSpace_ker
    (ZeroBoundaryVectorSpace.divergence (n := n) (Ω := Ω))

/-- The `H¹` norm on the weak-divergence kernel. -/
local instance normedAddCommGroupSolenoidal : NormedAddCommGroup Vσ := inferInstance
/-- The seminormed group underlying `normedAddCommGroupSolenoidal`. -/
local instance seminormedAddCommGroupSolenoidal : SeminormedAddCommGroup Vσ := inferInstance

/-- Restrict the actual constructed form to the existing closed weak-divergence kernel. -/
def solenoidalSimilarityPrincipalForm (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (b : Fin n → W^{1,∞}(Ω)) (Q : Fin n → Fin n → DerivLp n ∞ Ω) :
    Vσ →L[ℝ] StrongDual ℝ Vσ :=
  PDE.Analysis.Evolution.restrictForm
    (V := H¹₀(Ω; ℝ^n))
    (ZeroBoundaryVectorSpace.divergence (n := n) (Ω := Ω)).ker
    (similarityPrincipalForm hΩ hb b Q)

/-- Coercivity survives restriction to the closed weak-divergence kernel. -/
theorem solenoidalSimilarityPrincipalForm_isCoercive
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (b : Fin n → W^{1,∞}(Ω)) (Q : Fin n → Fin n → DerivLp n ∞ Ω) (η : ℝ)
    (hdiv : ∑ i, (b i : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n i) = 0)
    (hcompensation : ∀ᵐ x ∂domainMeasure n Ω, ∀ v : Fin n → ℝ,
      -η * (∑ k, (v k) ^ 2) ≤
        ∑ k, ∑ j, ((b k : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n j) +
          Q k j) x * v j * v k)
    (hη : η < ((n : ℝ) - 2) / 4) :
    IsCoercive (solenoidalSimilarityPrincipalForm hΩ hb b Q) := by
  obtain ⟨c, hc, hbound⟩ :=
    similarityPrincipalForm_isCoercive hΩ hb b Q η hdiv hcompensation hη
  refine ⟨c, hc, fun U ↦ ?_⟩
  rw [solenoidalSimilarityPrincipalForm, PDE.Analysis.Evolution.restrictForm_apply]
  exact hbound (U : H¹₀(Ω; ℝ^n))

/-- The bounded-domain solenoidal principal equation has one solution for every dual load.
This is a linear variational solve, not the nonlinear profile or eigenpair construction. -/
theorem existsUnique_solenoidal_similarity_principal_solution
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (b : Fin n → W^{1,∞}(Ω)) (Q : Fin n → Fin n → DerivLp n ∞ Ω) (η : ℝ)
    (hdiv : ∑ i, (b i : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n i) = 0)
    (hcompensation : ∀ᵐ x ∂domainMeasure n Ω, ∀ v : Fin n → ℝ,
      -η * (∑ k, (v k) ^ 2) ≤
        ∑ k, ∑ j, ((b k : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n j) +
          Q k j) x * v j * v k)
    (hη : η < ((n : ℝ) - 2) / 4) (ell : StrongDual ℝ Vσ) :
    ∃! U : Vσ, ∀ V : Vσ, solenoidalSimilarityPrincipalForm hΩ hb b Q U V = ell V := by
  change ∃! U : Vσ, PDE.Analysis.Variational.IsWeakSolution
    (solenoidalSimilarityPrincipalForm hΩ hb b Q) ell U
  exact PDE.Analysis.Variational.IsWeakSolution.existsUnique
    (V := Vσ) (solenoidalSimilarityPrincipalForm hΩ hb b Q)
    (solenoidalSimilarityPrincipalForm_isCoercive hΩ hb b Q η hdiv hcompensation hη) ell

end SimilarityPrincipal

end NavierStokes
