/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Stokes.Ball.EigenSobolev
public import PDE.Fluid.Stokes.Ball.Normalization
public import PDE.Analysis.Variational.LowEigenfunctions
public import PDE.Spaces.Sobolev.Compactness.Rellich.VectorValues
public import PDE.Spaces.Sobolev.GraphSpace.Operators.Vector.GradientInner
public import PDE.Analysis.Matrix.EuclideanTrace
public import PDE.Analysis.MeasureTheory.Lp.L2Pairing
import PDE.Elliptic.Regularity.Interior.DeGiorgi.BallGeometry

/-!
# The tail bound for the ball modes

On the divergence-free fields of `H¹(B(0, R))³` in the sector `odd`, with no boundary condition,
let `E(u, v) = ∫_B ∇u : ∇v + η ∫_B ⟪u, v⟫` with `η > 0`. If `u` is `E`-orthogonal to every mode
`mode R k l α` of the sector with `0 < α < cut` and, in the odd sector, to `e_z`, then
`‖u‖² ≤ (η + (cut / R)²)⁻¹ E(u, u)` (`tail_bound`). The modes below the cut carry the
eigenvalues `(α / R)² < (cut / R)²` of the Neumann-type Stokes problem, and without the
orthogonality to `e_z` the bound fails for `u = e_z`. This is the analytic part of the
approximation constant `K₅` of Hou, Wang and Yang, which they evaluate as
`‖λ_max(Q)‖_∞ / (η₂ + λ_{N+1})` (Section 6.2).

## Main results

* `sectorSubmodule`, `mem_sectorSubmodule_iff`, `isClosed_sectorSubmodule`: the closed sector
  subspace of `H¹(B(0, R))³`.
* `sectorEnergyForm`, `isCoercive_sectorEnergyForm`, `isCompactOperator_ballValueCLM`.
* `energyPairing`: the pairing `E(u, ψ)` of `u ∈ H¹(B(0, R))³` with a smooth field `ψ`;
  `energyPairing_mode`, `energyPairing_zeroMode`, `energyPairing_smul`.
* `smoothSectorField`, `modeSectorField`, `zeroModeSectorField`: smooth divergence-free sector
  fields, the modes and `e_z` as elements of the sector subspace, with
  `sectorEnergyForm_smoothSectorField` (the energy form against such a field is the energy
  pairing with it, through `inner_add_inner_eq_energyPairing`).
* `mul_norm_sq_le_of_integral_inner_eq_zero`: the bound under `L²`-orthogonality.
* `tail_bound`: the bound under `E`-orthogonality to an enumeration of the modes below the cut.

## How it works

We work on the sector fields, which form a closed subspace `sectorSubmodule R odd` of the Hilbert
space `BallH1Field R = PiLp 2 (fun _ : Fin 3 ↦ H¹(B(0, R)))`, cut out by the divergence and by the
almost-everywhere symmetry identities. The form `sectorEnergyForm` of `E` is coercive there
(`isCoercive_sectorEnergyForm`) and the value map into `L²(B(0, R); ℝ³)` is compact by Rellich's
theorem (`isCompactOperator_ballValueCLM`), so by the abstract bound
`mul_norm_sq_le_of_inner_weakEigenfunction_eq_zero` it suffices that `u` is `L²`-orthogonal to every
weak eigenfunction of eigenvalue `λ < η + (cut / R)²`. Such an eigenfunction satisfies the
eigenvalue equation of `eigen_mem_closure_modes_H1` with `μ = λ - η`, so its value lies in the
closed span of `ballModes R μ odd`, and every element of `ballModes R μ odd` is a multiple of a mode
with `0 < α < cut` or of `e_z` (`inner_ballModes_eq_zero`). This gives the bound under
`L²`-orthogonality (`mul_norm_sq_le_of_integral_inner_eq_zero`). The eigenvalue equations
`E(u, ψ) = ((α / R)² + η) ∫_B ⟪u, ψ⟫` of the modes (`energyPairing_mode`) and
`E(u, e_z) = η ∫_B ⟪u, e_z⟫` (`energyPairing_zeroMode`) turn `E`-orthogonality into
`L²`-orthogonality, which gives `tail_bound`.

## References

* T. Hou, Y. Wang, and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Section 4.2.2, the definition of
  `K₅` and (4.15), p. 27, and Section 6.2, the value of `K₅` after (6.5), p. 51.
  <https://arxiv.org/abs/2509.25116v2>
-/

@[expose] public noncomputable section

open MeasureTheory Set PDE.CoordinateSystems SobolevSpace.GraphSpace PDE.Analysis.Variational
open PDE (partialDeriv)
open scoped RealInnerProductSpace ContDiff Sobolev

namespace PDE.Fluid.Stokes.Ball

/-! ### The sector subspace of `H¹(B(0, R))³` -/

/-- `H¹(B(0, R))³` with the `ℓ²` product of the `H¹` norms, a real Hilbert space: a type
synonym of `PiLp 2 (fun _ : Fin 3 ↦ H¹(B(0, R)))` whose only algebraic structure is that of its
inner product structure. On `PiLp 2 (fun _ ↦ H¹(Ω))` itself a submodule is elaborated with the
algebraic instances of `H¹(Ω)` as a submodule, and the instance `InnerProductSpace ℝ ↥S` for
the submodule `S` times out in the defeq check against the normed instances, even for `S = ⊤`;
on the synonym both agree. The synonym belongs with the Sobolev spaces (`Spaces/Sobolev`) once
other domains need it. -/
def BallH1Field (R : ℝ) : Type :=
  PiLp 2 fun _ : Fin 3 ↦ H¹(Metric.ball (0 : ℝ^3) R)

/-- The `ℓ²` norm of the three `H¹` norms. -/
instance (R : ℝ) : NormedAddCommGroup (BallH1Field R) :=
  inferInstanceAs (NormedAddCommGroup (PiLp 2 fun _ : Fin 3 ↦ H¹(Metric.ball (0 : ℝ^3) R)))

/-- The sum of the three `H¹` inner products. -/
instance (R : ℝ) : InnerProductSpace ℝ (BallH1Field R) :=
  inferInstanceAs (InnerProductSpace ℝ (PiLp 2 fun _ : Fin 3 ↦ H¹(Metric.ball (0 : ℝ^3) R)))

/-- `H¹(B(0, R))³` is complete. -/
instance (R : ℝ) : CompleteSpace (BallH1Field R) :=
  inferInstanceAs (CompleteSpace (PiLp 2 fun _ : Fin 3 ↦ H¹(Metric.ball (0 : ℝ^3) R)))

/-- A family of three `H¹(B(0, R))` functions as an element of `BallH1Field R`. -/
def toBallH1Field {R : ℝ} (u : Fin 3 → H¹(Metric.ball (0 : ℝ^3) R)) : BallH1Field R :=
  WithLp.toLp 2 u

/-- The components of an element of `BallH1Field R`, as a linear map. -/
def ballFieldsLinearMap (R : ℝ) : BallH1Field R →ₗ[ℝ] (Fin 3 → H¹(Metric.ball (0 : ℝ^3) R)) where
  toFun u := WithLp.ofLp (u : PiLp 2 fun _ : Fin 3 ↦ H¹(Metric.ball (0 : ℝ^3) R))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The components of an element of `BallH1Field R`; each has `H¹` norm at most the `ℓ²` norm. -/
def ballFieldsCLM (R : ℝ) : BallH1Field R →L[ℝ] (Fin 3 → H¹(Metric.ball (0 : ℝ^3) R)) :=
  (ballFieldsLinearMap R).mkContinuous 1 fun u ↦ by
    rw [one_mul]
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i ↦ ?_
    exact PiLp.norm_apply_le (u : PiLp 2 fun _ : Fin 3 ↦ H¹(Metric.ball (0 : ℝ^3) R)) i

/-- The components of `toBallH1Field u` are `u`. -/
@[simp]
theorem ballFieldsCLM_toBallH1Field {R : ℝ} (u : Fin 3 → H¹(Metric.ball (0 : ℝ^3) R)) :
    ballFieldsCLM R (toBallH1Field u) = u :=
  rfl

/-- The value in `L²(B(0, R); ℝ³)` of an element of `H¹(B(0, R))³`. -/
def ballValueCLM (R : ℝ) :
    BallH1Field R →L[ℝ] Lp (ℝ^3) 2 (volume.restrict (Metric.ball (0 : ℝ^3) R)) :=
  vectorWkpValueCLM.comp (ballFieldsCLM R)

/-- The weak gradient of an element of `H¹(B(0, R))³`, with `∂ⱼ uᵢ` at `finProdFinEquiv (i, j)`. -/
def ballGradientCLM (R : ℝ) :
    BallH1Field R →L[ℝ] Lp (ℝ^(3 * 3)) 2 (volume.restrict (Metric.ball (0 : ℝ^3) R)) :=
  vectorWkpGradientCLM.comp (ballFieldsCLM R)

/-- The value of an element of `BallH1Field R` is that of its components. -/
@[simp]
theorem ballValueCLM_apply {R : ℝ} (u : BallH1Field R) :
    ballValueCLM R u = vectorWkpValueCLM (ballFieldsCLM R u) :=
  rfl

/-- The gradient of an element of `BallH1Field R` is that of its components. -/
@[simp]
theorem ballGradientCLM_apply {R : ℝ} (u : BallH1Field R) :
    ballGradientCLM R u = vectorWkpGradientCLM (ballFieldsCLM R u) :=
  rfl

/-- The weak divergence `∑ᵢ ∂ᵢ uᵢ` in `L²(B(0, R))`. -/
def ballDivergenceCLM (R : ℝ) :
    BallH1Field R →L[ℝ] Lp ℝ 2 (volume.restrict (Metric.ball (0 : ℝ^3) R)) :=
  (Matrix.euclideanTraceCLM.compLpL 2 _).comp (ballGradientCLM R)

/-- The defect `U ∘ R_θ - R_θ ∘ U` of equivariance under the rotation `R_θ` about the axis. -/
def rotationDefectCLM (R θ : ℝ) :
    Lp (ℝ^3) 2 (volume.restrict (Metric.ball (0 : ℝ^3) R)) →L[ℝ]
      Lp (ℝ^3) 2 (volume.restrict (Metric.ball (0 : ℝ^3) R)) :=
  (Lp.compMeasurePreservingₗᵢ ℝ (axisRotation θ)
      (measurePreserving_axisRotation_ball R θ)).toContinuousLinearMap -
    (axialRotation θ).toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 _

/-- The defect `U ∘ σ - s σ ∘ U` of parity `s = sectorSign odd` under the equatorial
reflection `σ`. -/
def reflectionDefectCLM (R : ℝ) (odd : Bool) :
    Lp (ℝ^3) 2 (volume.restrict (Metric.ball (0 : ℝ^3) R)) →L[ℝ]
      Lp (ℝ^3) 2 (volume.restrict (Metric.ball (0 : ℝ^3) R)) :=
  (Lp.compMeasurePreservingₗᵢ ℝ equatorialReflection
      (measurePreserving_equatorialReflection_ball R)).toContinuousLinearMap -
    (sectorSign odd • equatorialReflection.toContinuousLinearEquiv.toContinuousLinearMap).compLpL
      2 _

/-- The weak divergence vanishes exactly when the trace of the weak gradient vanishes almost
everywhere. -/
theorem ballDivergenceCLM_eq_zero_iff {R : ℝ} (u : BallH1Field R) :
    ballDivergenceCLM R u = 0 ↔ ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : ℝ^3) R)),
      ∑ i, ∇ (ballFieldsCLM R u) x (finProdFinEquiv (i, i)) = 0 := by
  have h := Matrix.euclideanTraceCLM.coeFn_compLpL (p := 2) (ballGradientCLM R u)
  have htrace (x : ℝ^3) : Matrix.euclideanTraceCLM (ballGradientCLM R u x) =
      ∑ i, ∇ (ballFieldsCLM R u) x (finProdFinEquiv (i, i)) :=
    Matrix.euclideanTraceCLM_apply _
  rw [Lp.eq_zero_iff_ae_eq_zero]
  constructor
  · intro h0
    filter_upwards [h, h0] with x hx h0x
    rw [← htrace, ← hx]
    exact h0x
  · intro h0
    filter_upwards [h, h0] with x hx h0x
    change ballDivergenceCLM R u x = 0
    rw [ballDivergenceCLM, ContinuousLinearMap.comp_apply, hx, htrace]
    exact h0x

/-- The rotation defect vanishes exactly for almost-everywhere equivariant values. -/
theorem rotationDefectCLM_eq_zero_iff {R θ : ℝ}
    (U : Lp (ℝ^3) 2 (volume.restrict (Metric.ball (0 : ℝ^3) R))) :
    rotationDefectCLM R θ U = 0 ↔ ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : ℝ^3) R)),
      U (axisRotation θ x) = axisRotation θ (U x) := by
  have h1 := Lp.coeFn_compMeasurePreserving U (measurePreserving_axisRotation_ball R θ)
  have h2 := (axialRotation θ).toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLpL
    (p := 2) U
  rw [rotationDefectCLM, sub_apply, sub_eq_zero, Lp.ext_iff]
  constructor
  · intro h
    filter_upwards [h1, h2, h] with x hx1 hx2 hx
    simp only [Function.comp_apply] at hx1
    rw [← hx1, ← axialRotation_apply]
    exact hx.trans hx2
  · intro h
    filter_upwards [h1, h2, h] with x hx1 hx2 hx
    simp only [Function.comp_apply] at hx1
    refine hx1.trans (hx.trans ?_)
    rw [hx2]
    rfl

/-- The reflection defect vanishes exactly for values of parity `sectorSign odd` almost
everywhere. -/
theorem reflectionDefectCLM_eq_zero_iff {R : ℝ} {odd : Bool}
    (U : Lp (ℝ^3) 2 (volume.restrict (Metric.ball (0 : ℝ^3) R))) :
    reflectionDefectCLM R odd U = 0 ↔ ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : ℝ^3) R)),
      U (equatorialReflection x) = sectorSign odd • equatorialReflection (U x) := by
  have h1 := Lp.coeFn_compMeasurePreserving U (measurePreserving_equatorialReflection_ball R)
  have h2 := (sectorSign odd •
    equatorialReflection.toContinuousLinearEquiv.toContinuousLinearMap).coeFn_compLpL (p := 2) U
  rw [reflectionDefectCLM, sub_apply, sub_eq_zero, Lp.ext_iff]
  constructor
  · intro h
    filter_upwards [h1, h2, h] with x hx1 hx2 hx
    simp only [Function.comp_apply] at hx1
    rw [← hx1]
    exact hx.trans hx2
  · intro h
    filter_upwards [h1, h2, h] with x hx1 hx2 hx
    simp only [Function.comp_apply] at hx1
    refine hx1.trans (hx.trans ?_)
    rw [hx2]
    rfl

/-- The divergence-free elements of `H¹(B(0, R))³` whose value lies in the sector `odd`: the
kernels of the divergence and of the symmetry defects. -/
def sectorSubmodule (R : ℝ) (odd : Bool) : Submodule ℝ (BallH1Field R) :=
  LinearMap.ker (ballDivergenceCLM R).toLinearMap ⊓
    ((⨅ θ : ℝ, LinearMap.ker ((rotationDefectCLM R θ).comp (ballValueCLM R)).toLinearMap) ⊓
      LinearMap.ker ((reflectionDefectCLM R odd).comp (ballValueCLM R)).toLinearMap)

/-- Membership in the sector subspace: zero divergence and the sector condition. -/
theorem mem_sectorSubmodule_iff {R : ℝ} {odd : Bool} {u : BallH1Field R} :
    u ∈ sectorSubmodule R odd ↔
      (∀ᵐ x ∂(volume.restrict (Metric.ball (0 : ℝ^3) R)),
        ∑ i, ∇ (ballFieldsCLM R u) x (finProdFinEquiv (i, i)) = 0) ∧
      InSector R odd (vectorWkpValueCLM (ballFieldsCLM R u)) := by
  simp only [sectorSubmodule, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ballDivergenceCLM_eq_zero_iff, rotationDefectCLM_eq_zero_iff,
    reflectionDefectCLM_eq_zero_iff, ballValueCLM_apply, InSector]

/-- The sector subspace is closed. -/
theorem isClosed_sectorSubmodule (R : ℝ) (odd : Bool) :
    IsClosed (sectorSubmodule R odd : Set (BallH1Field R)) := by
  simp only [sectorSubmodule, Submodule.coe_inf, Submodule.coe_iInf]
  exact (ballDivergenceCLM R).isClosed_ker.inter ((isClosed_iInter fun θ ↦
    ((rotationDefectCLM R θ).comp (ballValueCLM R)).isClosed_ker).inter
      ((reflectionDefectCLM R odd).comp (ballValueCLM R)).isClosed_ker)

/-! ### The energy form and the compact value map -/

/-- The `H¹` product norm is controlled by the `L²` norms of the value and of the gradient. -/
theorem norm_sq_le_ballValueCLM_ballGradientCLM {R : ℝ} (u : BallH1Field R) :
    ‖u‖ ^ 2 ≤ 30 * (‖ballValueCLM R u‖ ^ 2 + ‖ballGradientCLM R u‖ ^ 2) := by
  have h1 : ‖u‖ ^ 2 ≤ 3 * ‖ballFieldsCLM R u‖ ^ 2 := by
    have hu : ‖u‖ ^ 2 = ∑ i, ‖WithLp.ofLp u i‖ ^ 2 :=
      PiLp.norm_sq_eq_of_L2 _ (u : PiLp 2 fun _ : Fin 3 ↦ H¹(Metric.ball (0 : ℝ^3) R))
    rw [hu]
    calc
      ∑ i, ‖WithLp.ofLp u i‖ ^ 2 ≤ ∑ _i : Fin 3, ‖ballFieldsCLM R u‖ ^ 2 :=
        Finset.sum_le_sum fun i _ ↦
          pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm (ballFieldsCLM R u) i) 2
      _ = 3 * ‖ballFieldsCLM R u‖ ^ 2 := by simp
  have h2 := norm_le_vectorWkpValueCLM_add_gradient (ballFieldsCLM R u)
  rw [ballValueCLM_apply, ballGradientCLM_apply]
  set a := ‖vectorWkpValueCLM (ballFieldsCLM R u)‖
  set b := ‖∇ (ballFieldsCLM R u)‖
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have h3 : ‖ballFieldsCLM R u‖ ≤ a + 3 * b := by exact_mod_cast h2
  have h4 : ‖ballFieldsCLM R u‖ ^ 2 ≤ (a + 3 * b) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h3 2
  nlinarith [sq_nonneg (3 * a - b)]

/-- The energy form `E(u, v) = ⟪∇u, ∇v⟫ + η ⟪u, v⟫` on the sector subspace. -/
def sectorEnergyForm (R η : ℝ) (odd : Bool) :
    sectorSubmodule R odd →L[ℝ] StrongDual ℝ (sectorSubmodule R odd) :=
  (innerSL ℝ).bilinearComp ((ballGradientCLM R).comp (sectorSubmodule R odd).subtypeL)
      ((ballGradientCLM R).comp (sectorSubmodule R odd).subtypeL) +
    η • (innerSL ℝ).bilinearComp ((ballValueCLM R).comp (sectorSubmodule R odd).subtypeL)
      ((ballValueCLM R).comp (sectorSubmodule R odd).subtypeL)

/-- The energy form evaluated on two sector fields. -/
theorem sectorEnergyForm_apply {R η : ℝ} {odd : Bool} (u v : sectorSubmodule R odd) :
    sectorEnergyForm R η odd u v =
      ⟪ballGradientCLM R u, ballGradientCLM R v⟫ + η * ⟪ballValueCLM R u, ballValueCLM R v⟫ := by
  simp [sectorEnergyForm]

/-- The energy form is symmetric. -/
theorem sectorEnergyForm_symm {R η : ℝ} {odd : Bool} (u v : sectorSubmodule R odd) :
    sectorEnergyForm R η odd u v = sectorEnergyForm R η odd v u := by
  rw [sectorEnergyForm_apply, sectorEnergyForm_apply, real_inner_comm (ballGradientCLM R u),
    real_inner_comm (ballValueCLM R u)]

/-- For `η > 0` the energy form is coercive on the sector subspace. -/
theorem isCoercive_sectorEnergyForm {R η : ℝ} (hη : 0 < η) (odd : Bool) :
    IsCoercive (sectorEnergyForm R η odd) := by
  refine ⟨min 1 η / 30, by positivity, fun u ↦ ?_⟩
  rw [sectorEnergyForm_apply, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  have h := norm_sq_le_ballValueCLM_ballGradientCLM (u : BallH1Field R)
  have hu : ‖u‖ = ‖(u : BallH1Field R)‖ := rfl
  have hm1 : min 1 η ≤ 1 := min_le_left _ _
  have hm2 : min 1 η ≤ η := min_le_right _ _
  have ha := sq_nonneg ‖ballValueCLM R u‖
  have hb := sq_nonneg ‖ballGradientCLM R u‖
  calc
    min 1 η / 30 * ‖u‖ * ‖u‖ = min 1 η / 30 * ‖(u : BallH1Field R)‖ ^ 2 := by rw [hu]; ring
    _ ≤ min 1 η / 30 * (30 * (‖ballValueCLM R u‖ ^ 2 + ‖ballGradientCLM R u‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = min 1 η * ‖ballValueCLM R u‖ ^ 2 + min 1 η * ‖ballGradientCLM R u‖ ^ 2 := by ring
    _ ≤ η * ‖ballValueCLM R u‖ ^ 2 + 1 * ‖ballGradientCLM R u‖ ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_right hm2 ha) (mul_le_mul_of_nonneg_right hm1 hb)
    _ = ‖ballGradientCLM R u‖ ^ 2 + η * ‖ballValueCLM R u‖ ^ 2 := by ring

/-- **Rellich.** The value map `H¹(B(0, R))³ → L²(B(0, R); ℝ³)` is compact. -/
theorem isCompactOperator_ballValueCLM {R : ℝ} (hR : 0 < R) :
    IsCompactOperator (ballValueCLM R) := by
  have : Fact (0 < 3) := ⟨by norm_num⟩
  let := Classical.choice (SobolevSpace.Boundary.nonempty_c1ExtensionAtlas_ball (0 : ℝ^3) hR)
  rw [ballValueCLM, ContinuousLinearMap.coe_comp]
  exact Rellich.vectorWkpValueCLM_isCompactOperator_of_c1Domain.comp_clm (ballFieldsCLM R)

/-! ### The energy pairing with the modes -/

/-- The energy pairing `E(u, ψ) = ∫_B ∇u : ∇ψ + η ∫_B ⟪u, ψ⟫` of `u ∈ H¹(B(0, R))³` with a
smooth field `ψ`. -/
def energyPairing (R η : ℝ) (u : Fin 3 → H¹(Metric.ball (0 : ℝ^3) R)) (ψ : ℝ^3 → ℝ^3) : ℝ :=
  (∫ x in Metric.ball (0 : ℝ^3) R, ∑ i, ∑ j,
      ∇ u x (finProdFinEquiv (i, j)) * ∂[j] (fun y ↦ ψ y i) x) +
    η * ∫ x in Metric.ball (0 : ℝ^3) R, ⟪vectorWkpValueCLM u x, ψ x⟫

/-- On a divergence-free `u`, the energy pairing with a mode of root `α` is
`((α / R)² + η) ∫_B ⟪u, ψ⟫`. -/
theorem energyPairing_mode {R η : ℝ} (hR : 0 < R) {k : ModeKind} {l : ℕ} {α : ℝ}
    (hα : boundaryFunction k l α = 0) (u : Fin 3 → H¹(Metric.ball (0 : ℝ^3) R))
    (hdiv : ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : ℝ^3) R)),
      ∑ i, ∇ u x (finProdFinEquiv (i, i)) = 0) :
    energyPairing R η u (mode R k l α) = ((α / R) ^ 2 + η) *
      ∫ x in Metric.ball (0 : ℝ^3) R, ⟪vectorWkpValueCLM u x, mode R k l α x⟫ := by
  have h := mode_weak_eigen_sobolev hR hα u hdiv
  have e1 : ∫ x in Metric.ball (0 : ℝ^3) R, ∑ i, ∑ j,
      ∇ u x (finProdFinEquiv (i, j)) * ∂[j] (fun y ↦ mode R k l α y i) x =
      ∫ x in Metric.ball (0 : ℝ^3) R, ∑ i, ∑ j,
        ∂[j] (fun y ↦ mode R k l α y i) x * ∇ u x (finProdFinEquiv (i, j)) := by
    simp_rw [mul_comm]
  have e2 : ∫ x in Metric.ball (0 : ℝ^3) R, ⟪mode R k l α x, vectorWkpValueCLM u x⟫ =
      ∫ x in Metric.ball (0 : ℝ^3) R, ⟪vectorWkpValueCLM u x, mode R k l α x⟫ := by
    simp_rw [real_inner_comm]
  rw [energyPairing, e1, h, e2]
  ring

/-- The energy pairing with the zero mode `e_z` is `η ∫_B ⟪u, e_z⟫`. -/
theorem energyPairing_zeroMode {R η : ℝ} (u : Fin 3 → H¹(Metric.ball (0 : ℝ^3) R)) :
    energyPairing R η u zeroMode =
      η * ∫ x in Metric.ball (0 : ℝ^3) R, ⟪vectorWkpValueCLM u x, zeroMode x⟫ := by
  simp [energyPairing, zeroMode, partialDeriv]

/-- The energy pairing is homogeneous in the field: `E(u, c ψ) = c E(u, ψ)`, so orthogonality to
a nonzero multiple of a mode is orthogonality to the mode. -/
theorem energyPairing_smul {R η : ℝ} (u : Fin 3 → H¹(Metric.ball (0 : ℝ^3) R)) (c : ℝ)
    (ψ : ℝ^3 → ℝ^3) : energyPairing R η u (c • ψ) = c * energyPairing R η u ψ := by
  have hψ (i j : Fin 3) (x : ℝ^3) :
      ∂[j] (fun y ↦ (c • ψ y) i) x = c * ∂[j] (fun y ↦ ψ y i) x := by
    simp only [PiLp.smul_apply, smul_eq_mul]
    exact partialDeriv_const_smul c
  have e1 : ∫ x in Metric.ball (0 : ℝ^3) R, ∑ i, ∑ j,
      ∇ u x (finProdFinEquiv (i, j)) * (c * ∂[j] (fun y ↦ ψ y i) x) =
      c * ∫ x in Metric.ball (0 : ℝ^3) R, ∑ i, ∑ j,
        ∇ u x (finProdFinEquiv (i, j)) * ∂[j] (fun y ↦ ψ y i) x := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
  simp only [energyPairing, Pi.smul_apply, hψ, inner_smul_right, integral_const_mul, e1]
  ring

/-! ### Smooth fields in the sector subspace -/

/-- **Bridge to the energy pairing.** If the value and the gradient of `V ∈ H¹(B(0, R))³` are
those of a field `ψ` almost everywhere, then `⟪∇u, ∇V⟫ + η ⟪u, V⟫ = E(u, ψ)`. -/
theorem inner_add_inner_eq_energyPairing {R η : ℝ} (u V : Fin 3 → H¹(Metric.ball (0 : ℝ^3) R))
    {ψ : ℝ^3 → ℝ^3}
    (hV1 : (vectorWkpValueCLM V : ℝ^3 → ℝ^3) =ᵐ[volume.restrict (Metric.ball (0 : ℝ^3) R)] ψ)
    (hV2 : ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : ℝ^3) R)), ∀ i j,
      ∇ V x (finProdFinEquiv (i, j)) = ∂[j] (fun y ↦ ψ y i) x) :
    ⟪∇ u, ∇ V⟫ + η * ⟪vectorWkpValueCLM u, vectorWkpValueCLM V⟫ = energyPairing R η u ψ := by
  rw [inner_vectorWkpGradientCLM, L2.inner_def, energyPairing]
  congr 1
  · refine integral_congr_ae ?_
    filter_upwards [hV2] with x hx
    simp only [hx]
  · congr 1
    refine integral_congr_ae ?_
    filter_upwards [hV1] with x hx
    simp only [hx]

/-- The `H¹(B(0, R))³` class of a smooth field, whose weak gradient is the classical one. -/
def smoothH1Field (R : ℝ) {ψ : ℝ^3 → ℝ^3} (hψ : ContDiff ℝ ∞ ψ) :
    Fin 3 → H¹(Metric.ball (0 : ℝ^3) R) :=
  (exists_H1_of_contDiff (R := R) hψ).choose

/-- The value of `smoothH1Field R hψ` is `ψ` on the ball. -/
theorem vectorWkpValueCLM_smoothH1Field (R : ℝ) {ψ : ℝ^3 → ℝ^3} (hψ : ContDiff ℝ ∞ ψ) :
    (vectorWkpValueCLM (smoothH1Field R hψ) : ℝ^3 → ℝ^3)
      =ᵐ[volume.restrict (Metric.ball (0 : ℝ^3) R)] ψ :=
  (exists_H1_of_contDiff (R := R) hψ).choose_spec.1

/-- The weak gradient of `smoothH1Field R hψ` is the classical gradient of `ψ` on the ball. -/
theorem vectorWkpGradientCLM_smoothH1Field (R : ℝ) {ψ : ℝ^3 → ℝ^3} (hψ : ContDiff ℝ ∞ ψ) :
    ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : ℝ^3) R)), ∀ i j,
      ∇ (smoothH1Field R hψ) x (finProdFinEquiv (i, j)) = ∂[j] (fun y ↦ ψ y i) x :=
  (exists_H1_of_contDiff (R := R) hψ).choose_spec.2

/-- A smooth divergence-free field of the sector `odd` (commuting with the rotations about the
axis and of parity `sectorSign odd` under the equatorial reflection) as an element of the sector
subspace on `B(0, R)`. -/
def smoothSectorField (R : ℝ) (odd : Bool) {ψ : ℝ^3 → ℝ^3} (hψ : ContDiff ℝ ∞ ψ)
    (hdiv : ∀ x, divergence ψ x = 0) (heq : IsEquivariantUnderAxisRotation ψ)
    (hpar : ∀ x, ψ (equatorialReflection x) = sectorSign odd • equatorialReflection (ψ x)) :
    sectorSubmodule R odd :=
  ⟨toBallH1Field (smoothH1Field R hψ), mem_sectorSubmodule_iff.mpr
    ⟨by
      filter_upwards [vectorWkpGradientCLM_smoothH1Field R hψ] with x hx
      simp only [ballFieldsCLM_toBallH1Field, hx]
      simpa [divergence] using hdiv x,
    inSector_of_ae_eq (vectorWkpValueCLM_smoothH1Field R hψ) heq hpar⟩⟩

/-- The components of `smoothSectorField` are `smoothH1Field`. -/
@[simp]
theorem ballFieldsCLM_smoothSectorField (R : ℝ) (odd : Bool) {ψ : ℝ^3 → ℝ^3}
    (hψ : ContDiff ℝ ∞ ψ) (hdiv : ∀ x, divergence ψ x = 0)
    (heq : IsEquivariantUnderAxisRotation ψ)
    (hpar : ∀ x, ψ (equatorialReflection x) = sectorSign odd • equatorialReflection (ψ x)) :
    ballFieldsCLM R (smoothSectorField R odd hψ hdiv heq hpar : BallH1Field R) =
      smoothH1Field R hψ :=
  rfl

/-- The energy form against a smooth sector field is the energy pairing with the field. -/
theorem sectorEnergyForm_smoothSectorField {R η : ℝ} {odd : Bool} (f : sectorSubmodule R odd)
    {ψ : ℝ^3 → ℝ^3} (hψ : ContDiff ℝ ∞ ψ) (hdiv : ∀ x, divergence ψ x = 0)
    (heq : IsEquivariantUnderAxisRotation ψ)
    (hpar : ∀ x, ψ (equatorialReflection x) = sectorSign odd • equatorialReflection (ψ x)) :
    sectorEnergyForm R η odd f (smoothSectorField R odd hψ hdiv heq hpar) =
      energyPairing R η (ballFieldsCLM R f) ψ := by
  rw [sectorEnergyForm_apply, ballGradientCLM_apply, ballGradientCLM_apply, ballValueCLM_apply,
    ballValueCLM_apply, ballFieldsCLM_smoothSectorField]
  exact inner_add_inner_eq_energyPairing _ _ (vectorWkpValueCLM_smoothH1Field R hψ)
    (vectorWkpGradientCLM_smoothH1Field R hψ)

/-- A mode of the parity of the sector `odd` as an element of the sector subspace. -/
def modeSectorField (R : ℝ) {odd : Bool} (k : ModeKind) (l : ℕ) (α : ℝ)
    (hpar : modeParity k l = sectorSign odd) : sectorSubmodule R odd :=
  smoothSectorField R odd (mode_contDiff R k l α) (mode_divergence_eq_zero R k l α)
    (mode_isEquivariantUnderAxisRotation R k l α)
    (fun x ↦ by rw [mode_equatorialReflection, hpar])

/-- The energy form against a mode is the energy pairing with the mode. -/
theorem sectorEnergyForm_modeSectorField {R η : ℝ} {odd : Bool} (f : sectorSubmodule R odd)
    (k : ModeKind) (l : ℕ) (α : ℝ) (hpar : modeParity k l = sectorSign odd) :
    sectorEnergyForm R η odd f (modeSectorField R k l α hpar) =
      energyPairing R η (ballFieldsCLM R f) (mode R k l α) :=
  sectorEnergyForm_smoothSectorField f _ _ _ _

/-- The zero mode `e_z` as an element of the odd sector subspace. -/
def zeroModeSectorField (R : ℝ) : sectorSubmodule R true :=
  smoothSectorField R true zeroMode_contDiff zeroMode_divergence_eq_zero
    zeroMode_isEquivariantUnderAxisRotation
    (fun x ↦ by rw [zeroMode_equatorialReflection, sectorSign, ite_eq_left rfl, neg_one_smul])

/-- The energy form against `e_z` is the energy pairing with `e_z`. -/
theorem sectorEnergyForm_zeroModeSectorField {R η : ℝ} (f : sectorSubmodule R true) :
    sectorEnergyForm R η true f (zeroModeSectorField R) =
      energyPairing R η (ballFieldsCLM R f) zeroMode :=
  sectorEnergyForm_smoothSectorField f _ _ _ _

/-- **The modes below the cut.** Let `U ∈ L²(B(0, R); ℝ³)` be orthogonal to every mode of the
sector `odd` with `0 < α < cut` and, in the odd sector, to `e_z`. Then `U` is orthogonal to
`ballModes R μ odd` for every `μ < (cut / R)²`: a mode of eigenvalue `μ` has `|α| < cut`, the
mode of `-α` is that of `α`, and the only root at `α = 0` of admissible degree is the
meridional one of degree one, whose mode is `(4/5) e_z` of the odd sector. -/
theorem inner_ballModes_eq_zero {R μ cut : ℝ} (hR : 0 < R) (hcut : 0 ≤ cut) {odd : Bool}
    (hμ : μ < (cut / R) ^ 2) {U : Lp (ℝ^3) 2 (volume.restrict (Metric.ball (0 : ℝ^3) R))}
    (hmode : ∀ k l α, boundaryFunction k l α = 0 → 0 < α → α < cut → Admissible k l →
      modeParity k l = sectorSign odd →
        ∫ x in Metric.ball (0 : ℝ^3) R, ⟪U x, mode R k l α x⟫ = 0)
    (hzero : odd = true → ∫ x in Metric.ball (0 : ℝ^3) R, ⟪U x, zeroMode x⟫ = 0) :
    ∀ f ∈ ballModes R μ odd, ⟪f, U⟫ = 0 := by
  have hzero' (hodd : odd = true) (c : ℝ) :
      ∫ x in Metric.ball (0 : ℝ^3) R, ⟪U x, (c • zeroMode) x⟫ = 0 := by
    simp only [Pi.smul_apply, inner_smul_right, integral_const_mul, hzero hodd, mul_zero]
  rintro f (⟨k, l, α, hroot, hμα, hl, hpar, rfl⟩ | hf)
  · rw [L2.inner_toLp_eq_integral]
    have hsq : α ^ 2 < cut ^ 2 := by
      rw [← hμα, div_pow, div_pow] at hμ
      exact (div_lt_div_iff_of_pos_right (by positivity)).mp hμ
    have habs : |α| < cut := abs_lt_of_sq_lt_sq hsq hcut
    rcases lt_trichotomy α 0 with hneg | h0 | hpos
    · rw [← mode_neg]
      refine hmode k l (-α) (by rwa [boundaryFunction_neg]) (neg_pos.mpr hneg) ?_ hl hpar
      rwa [abs_of_neg hneg] at habs
    · subst h0
      have hk : k = .meridional ∧ l = 1 := by
        by_contra hk
        exact boundaryFunction_zero_ne hl hk hroot
      obtain ⟨rfl, rfl⟩ := hk
      have hodd : odd = true := by
        cases odd
        · norm_num [modeParity, sectorSign] at hpar
        · rfl
      rw [mode_meridional_one_zero]
      exact hzero' hodd _
    · exact hmode k l α hroot hpos (by rwa [abs_of_pos hpos] at habs) hl hpar
  · split_ifs at hf with h
    · rw [Set.mem_singleton_iff] at hf
      subst hf
      rw [L2.inner_toLp_eq_integral]
      exact hzero h.2
    · exact absurd hf (Set.notMem_empty f)

/-! ### The tail bound -/

/-- **The tail bound under `L²`-orthogonality.** A divergence-free `u ∈ H¹(B(0, R))³` in the
sector `odd` that is `L²`-orthogonal to every mode of the sector with `0 < α < cut` and, in the
odd sector, to `e_z` satisfies `(η + (cut / R)²) ‖u‖² ≤ ‖∇u‖² + η ‖u‖²` for every `η > 0`. -/
theorem mul_norm_sq_le_of_integral_inner_eq_zero {R η cut : ℝ} (hR : 0 < R) (hη : 0 < η)
    (hcut : 0 ≤ cut) (odd : Bool) (u : Fin 3 → H¹(Metric.ball (0 : ℝ^3) R))
    (hdiv : ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : ℝ^3) R)),
      ∑ i, ∇ u x (finProdFinEquiv (i, i)) = 0)
    (hsec : InSector R odd (vectorWkpValueCLM u))
    (hmode : ∀ k l α, boundaryFunction k l α = 0 → 0 < α → α < cut → Admissible k l →
      modeParity k l = sectorSign odd →
        ∫ x in Metric.ball (0 : ℝ^3) R, ⟪vectorWkpValueCLM u x, mode R k l α x⟫ = 0)
    (hzero : odd = true →
      ∫ x in Metric.ball (0 : ℝ^3) R, ⟪vectorWkpValueCLM u x, zeroMode x⟫ = 0) :
    (η + (cut / R) ^ 2) * ‖vectorWkpValueCLM u‖ ^ 2 ≤
      ‖∇ u‖ ^ 2 + η * ‖vectorWkpValueCLM u‖ ^ 2 := by
  set S := sectorSubmodule R odd
  have : CompleteSpace S := (isClosed_sectorSubmodule R odd).completeSpace_coe
  set j : S →L[ℝ] Lp (ℝ^3) 2 (volume.restrict (Metric.ball (0 : ℝ^3) R)) :=
    (ballValueCLM R).comp S.subtypeL
  have hj (w : S) : j w = vectorWkpValueCLM (ballFieldsCLM R w) := rfl
  set U : S := ⟨toBallH1Field u, mem_sectorSubmodule_iff.mpr ⟨hdiv, hsec⟩⟩
  have key := mul_norm_sq_le_of_inner_weakEigenfunction_eq_zero (sectorEnergyForm R η odd)
    (isCoercive_sectorEnergyForm hη odd) sectorEnergyForm_symm j
    ((isCompactOperator_ballValueCLM hR).comp_clm S.subtypeL) (η + (cut / R) ^ 2) U ?_
  · rw [sectorEnergyForm_apply, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at key
    exact key
  intro lam w hlam hw
  obtain ⟨hdivW, hsecW⟩ := mem_sectorSubmodule_iff.mp w.2
  have heig : ∀ v : Fin 3 → H¹(Metric.ball (0 : ℝ^3) R),
      (∀ᵐ x ∂(volume.restrict (Metric.ball (0 : ℝ^3) R)),
        ∑ i, ∇ v x (finProdFinEquiv (i, i)) = 0) →
      InSector R odd (vectorWkpValueCLM v) →
      ∫ x in Metric.ball (0 : ℝ^3) R, ∑ i, ∑ j,
          ∇ (ballFieldsCLM R w) x (finProdFinEquiv (i, j)) *
            ∇ v x (finProdFinEquiv (i, j)) =
        (lam - η) * ∫ x in Metric.ball (0 : ℝ^3) R,
          ⟪vectorWkpValueCLM (ballFieldsCLM R w) x, vectorWkpValueCLM v x⟫ := by
    intro v hdivv hsecv
    have hv := hw ⟨toBallH1Field v, mem_sectorSubmodule_iff.mpr ⟨hdivv, hsecv⟩⟩
    rw [sectorEnergyForm_apply, hj, hj] at hv
    simp only [ballGradientCLM_apply, ballValueCLM_apply, ballFieldsCLM_toBallH1Field] at hv
    rw [← inner_vectorWkpGradientCLM, ← L2.inner_def]
    linarith
  have hcl := eigen_mem_closure_modes_H1 hR odd (ballFieldsCLM R w) hdivW hsecW heig
  have hμ : lam - η < (cut / R) ^ 2 := by linarith
  have hspan : Submodule.span ℝ (ballModes R (lam - η) odd) ≤ (ℝ ∙ vectorWkpValueCLM u)ᗮ :=
    Submodule.span_le.mpr fun g hg ↦ Submodule.mem_orthogonal_singleton_iff_inner_left.mpr
      (inner_ballModes_eq_zero hR hcut hμ hmode hzero g hg)
  have hjU : j U = vectorWkpValueCLM u := rfl
  rw [hj, hjU]
  exact Submodule.mem_orthogonal_singleton_iff_inner_left.mp
    (Submodule.topologicalClosure_minimal _ hspan (Submodule.isClosed_orthogonal _) hcl)

/-- **The tail bound**, the analytic part of the constant `K₅` of Hou, Wang and Yang. Let
`η > 0` and `0 ≤ cut`, and let `enum` contain every mode `(k, l, α)` of the sector `odd` with
`0 < α < cut`, admissible degree and `boundaryFunction k l α = 0`. A divergence-free
`u ∈ H¹(B(0, R))³` in the sector that is `E`-orthogonal to the modes of `enum` and, in the odd
sector, to `e_z` satisfies `‖u‖² ≤ (η + (cut / R)²)⁻¹ (‖∇u‖² + η ‖u‖²)`. The condition
`0 ≤ cut` is needed: for `cut < 0` the enumeration may be empty while the bound depends on
`cut²` only. -/
theorem tail_bound {R η cut : ℝ} (hη : 0 < η) (hcut : 0 ≤ cut) (odd : Bool)
    (enum : Finset (ModeKind × ℕ × ℝ))
    (henum : ∀ k l α, boundaryFunction k l α = 0 → 0 < α → α < cut → Admissible k l →
      modeParity k l = sectorSign odd → (k, l, α) ∈ enum)
    (u : Fin 3 → H¹(Metric.ball (0 : ℝ^3) R))
    (hdiv : ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : ℝ^3) R)),
      ∑ i, ∇ u x (finProdFinEquiv (i, i)) = 0)
    (hsec : InSector R odd (vectorWkpValueCLM u))
    (horth : ∀ e ∈ enum, energyPairing R η u (mode R e.1 e.2.1 e.2.2) = 0)
    (hzero : odd = true → energyPairing R η u zeroMode = 0) :
    ∫ x in Metric.ball (0 : ℝ^3) R, ‖vectorWkpValueCLM u x‖ ^ 2 ≤
      (η + (cut / R) ^ 2)⁻¹ * (‖∇ u‖ ^ 2 + η * ‖vectorWkpValueCLM u‖ ^ 2) := by
  have hr : 0 < η + (cut / R) ^ 2 := by positivity
  have hrhs : 0 ≤ (η + (cut / R) ^ 2)⁻¹ * (‖∇ u‖ ^ 2 + η * ‖vectorWkpValueCLM u‖ ^ 2) := by
    positivity
  by_cases hR : 0 < R
  swap
  · have hempty : Metric.ball (0 : ℝ^3) R = ∅ := Metric.ball_eq_empty.mpr (not_lt.mp hR)
    have h0 : ∫ x in Metric.ball (0 : ℝ^3) R, ‖vectorWkpValueCLM u x‖ ^ 2 = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards [ae_restrict_mem (measurableSet_ball (x := (0 : ℝ^3)) (ε := R))] with x hx
      rw [hempty] at hx
      exact absurd hx (Set.notMem_empty x)
    rw [h0]
    exact hrhs
  rw [L2.integral_norm_sq_eq_norm_sq, le_inv_mul_iff₀ hr]
  refine mul_norm_sq_le_of_integral_inner_eq_zero hR hη hcut odd u hdiv hsec ?_ ?_
  · intro k l α hroot hα hcutα hl hpar
    have h := horth (k, l, α) (henum k l α hroot hα hcutα hl hpar)
    rw [energyPairing_mode hR hroot u hdiv] at h
    exact (mul_eq_zero.mp h).resolve_left (by positivity)
  · intro hodd
    have h := hzero hodd
    rw [energyPairing_zeroMode] at h
    exact (mul_eq_zero.mp h).resolve_left hη.ne'

end PDE.Fluid.Stokes.Ball
