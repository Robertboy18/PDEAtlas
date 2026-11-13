/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Euclidean.Laplacian
import CAS.ExactTactic
public import PDE.Parabolic.Heat.MeanValue.Geometry
import PDE.FDeriv.Calculus

/-!
# Watson's phase and flux for the heat-ball mean-value formula

On the unit heat ball, use the positive backward-time variable `τ = -s`.
The logarithm of the heat kernel is

`f(τ,y) = -(n/2) log (4πτ) - |y|²/(4τ)`,

which is Evans's function `ψ` of (21) in §2.3.2 at `r = 1`. Its zero set is the lateral
heat-ball boundary, and the two identities

`∇f = -y/(2τ)`,  `f_τ - Δf = |y|²/(4τ²)`

drive Watson's divergence calculation.  For a scalar field `v`, set

`Q = (2τW - 4nf)v`,

`F = -4nf ∇v + v(Wy + 4n∇f)`,

where `W = |y|²/τ²`.  The pointwise calculation proved below is the exact
residual identity

`∂τ Q + div F = W(y · ∇v + 2τ ∂τv) - 4nf(∂τv + Δv)`.

Thus the final term vanishes for a backward-caloric field in the variable
`τ = -s`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.2, proof of Theorem 3, equations (20)-(21).
  <https://doi.org/10.1090/gsm/019>
* N. A. Watson, "A Theory of Subtemperatures in Several Variables", *Proc. London Math. Soc.*
  (3) 26 (1973), 385-417. <https://doi.org/10.1112/plms/s3-26.3.385>
-/

open scoped Gradient

@[expose] public section

open PDE (partialDeriv laplacian divergence advectiveDerivative)

noncomputable section

namespace HeatEquation

open PDE.Common

variable {n : ℕ}

/-- Watson's weight on a unit heat-ball slice in positive backward time. -/
def watsonWeight (τ : ℝ) (y : ℝ^n) : ℝ :=
  ‖y‖ ^ 2 / τ ^ 2

/-- The logarithm of the heat kernel in positive backward-time coordinates. -/
def watsonLogPhase (n : ℕ) (τ : ℝ) (y : ℝ^n) : ℝ :=
  -(n : ℝ) / 2 * Real.log (4 * Real.pi * τ) -
    ‖y‖ ^ 2 / (4 * τ)

/-- The phase is the normalized gap between the squared slice radius and
the squared spatial radius. -/
theorem watsonLogPhase_eq_sliceRadiusSq_sub
    (n : ℕ) {τ : ℝ} (hτ : 0 < τ) (y : ℝ^n) :
    watsonLogPhase n τ y =
      (heatBallSliceRadiusSq n 1 τ - ‖y‖ ^ 2) / (4 * τ) := by
  unfold watsonLogPhase heatBallSliceRadiusSq
  rw [one_pow, one_div, Real.log_inv]
  cas

/-- Watson's logarithmic phase vanishes on every lateral heat-ball slice. -/
theorem watsonLogPhase_eq_zero_of_mem_sphere
    (hn : 0 < n) {τ : ℝ}
    (hτ : τ ∈ Set.Ioo (0 : ℝ) (1 / (4 * Real.pi)))
    {y : ℝ^n}
    (hy : y ∈ Metric.sphere (0 : ℝ^n)
      (heatBallSliceRadius n 1 τ)) :
    watsonLogPhase n τ y = 0 := by
  have hradiusPos :
      0 < heatBallSliceRadiusSq n 1 τ :=
    (heatBallSliceRadiusSq_pos_iff hn zero_lt_one hτ.1).2 (by
      simpa using hτ.2)
  have hradiusSq :
      heatBallSliceRadius n 1 τ ^ 2 =
        heatBallSliceRadiusSq n 1 τ := by
    rw [heatBallSliceRadius, Real.sq_sqrt hradiusPos.le]
  have hnorm :
      ‖y‖ = heatBallSliceRadius n 1 τ := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hy
  rw [watsonLogPhase_eq_sliceRadiusSq_sub n hτ.1 y, hnorm,
    hradiusSq, sub_self, zero_div]

/-- Spatial coordinate derivative of Watson's logarithmic phase. -/
@[simp]
theorem partialDeriv_watsonLogPhase
    (n : ℕ) {τ : ℝ} (hτ : τ ≠ 0) (i : Fin n) (y : ℝ^n) :
    (∂[i] (watsonLogPhase n τ)) y =
      -y i / (2 * τ) := by
  let quadratic : ℝ^n → ℝ := fun z ↦ (4 * τ)⁻¹ • ‖z‖ ^ 2
  have hfun :
      watsonLogPhase n τ =
        fun z : ℝ^n ↦
          (-(n : ℝ) / 2 * Real.log (4 * Real.pi * τ)) -
            quadratic z := by
    funext z
    simp [watsonLogPhase, quadratic, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [hfun]
  have hconstSub :
      (∂[i] (fun z : ℝ^n ↦
          (-(n : ℝ) / 2 * Real.log (4 * Real.pi * τ)) -
            quadratic z)) y = -((∂[i] quadratic) y) := by
    unfold partialDeriv
    rw [fderiv_const_sub]
    rfl
  rw [hconstSub]
  dsimp only [quadratic]
  rw [PDE.partialDeriv_const_smul]
  have hnorm :=
    EuclideanLaplacian.partialDeriv_norm_sq (n := n) i y
  rw [hnorm]
  simp only [smul_eq_mul]
  field_simp [hτ]
  ring

/-- Spatial Laplacian of Watson's logarithmic phase. -/
@[simp]
theorem laplacian_watsonLogPhase
    (n : ℕ) {τ : ℝ} (hτ : τ ≠ 0) (y : ℝ^n) :
    laplacian (watsonLogPhase n τ) y =
      -(n : ℝ) / (2 * τ) := by
  unfold laplacian
  calc
    (∑ i : Fin n,
        (∂[i]
          (fun z : ℝ^n ↦ (∂[i] (watsonLogPhase n τ)) z)) y) =
        ∑ i : Fin n,
          (∂[i] (fun z : ℝ^n ↦ -z i / (2 * τ))) y := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      funext z
      exact partialDeriv_watsonLogPhase n hτ i z
    _ = ∑ _i : Fin n, (-(1 : ℝ) / (2 * τ)) := by
      apply Finset.sum_congr rfl
      intro i _
      have hfun :
          (fun z : ℝ^n ↦ -z i / (2 * τ)) =
            fun z : ℝ^n ↦ (-(2 * τ)⁻¹) • z i := by
        funext z
        simp [smul_eq_mul, div_eq_mul_inv, mul_comm]
      rw [hfun, PDE.partialDeriv_const_smul, PDE.partialDeriv_coord]
      simp [smul_eq_mul, div_eq_mul_inv]
    _ = -(n : ℝ) / (2 * τ) := by
      simp [div_eq_mul_inv]

/-- Positive-time derivative of Watson's logarithmic phase. -/
theorem hasDerivAt_watsonLogPhase
    (n : ℕ) {τ : ℝ} (hτ : τ ≠ 0) (y : ℝ^n) :
    HasDerivAt (fun s ↦ watsonLogPhase n s y)
      (-(n : ℝ) / (2 * τ) + ‖y‖ ^ 2 / (4 * τ ^ 2)) τ := by
  cas

/-- The parabolic phase identity used in Watson's flux computation. -/
theorem watsonLogPhase_time_sub_laplacian
    (n : ℕ) {τ : ℝ} (hτ : τ ≠ 0) (y : ℝ^n) :
    deriv (fun s ↦ watsonLogPhase n s y) τ -
        laplacian (watsonLogPhase n τ) y =
      watsonWeight τ y / 4 := by
  rw [(hasDerivAt_watsonLogPhase n hτ y).deriv,
    laplacian_watsonLogPhase n hτ y]
  unfold watsonWeight
  cas

/-- Time derivative of Watson's weight at a nonzero backward time. -/
theorem hasDerivAt_watsonWeight
    {τ : ℝ} (hτ : τ ≠ 0) (y : ℝ^n) :
    HasDerivAt (fun s ↦ watsonWeight s y)
      (-2 * watsonWeight τ y / τ) τ := by
  cas

/-- Spatial coordinate derivative of Watson's weight. -/
@[simp]
theorem partialDeriv_watsonWeight
    (τ : ℝ) (i : Fin n) (y : ℝ^n) :
    (∂[i] (watsonWeight τ)) y =
      2 * y i / τ ^ 2 := by
  have hfun :
      watsonWeight τ =
    fun z : ℝ^n ↦ (τ ^ 2)⁻¹ • ‖z‖ ^ 2 := by
    funext z
    simp [watsonWeight, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [hfun, PDE.partialDeriv_const_smul,
    EuclideanLaplacian.partialDeriv_norm_sq]
  simp only [smul_eq_mul]
  ring

/-- Watson's time density `Q` for a scalar field in positive backward time. -/
def watsonQ (n : ℕ) (v : ℝ → ℝ^n → ℝ) (τ : ℝ) (y : ℝ^n) : ℝ :=
  (2 * τ * watsonWeight τ y -
      4 * (n : ℝ) * watsonLogPhase n τ y) *
    v τ y

/-- Watson's spatial flux `F` for a scalar spatial field.

In vector notation,
`F = -4 n f ∇u + u (W y + 4 n ∇f)`, where `f` is
`watsonLogPhase` and `W` is `watsonWeight`. -/
def watsonF (n : ℕ) (τ : ℝ) (u : ℝ^n → ℝ) (y : ℝ^n) : ℝ^n :=
  (-4 * (n : ℝ) * watsonLogPhase n τ y) • ∇ u y +
    u y •
      (watsonWeight τ y • y +
        (4 * (n : ℝ)) • ∇ (watsonLogPhase n τ) y)

/-- Coordinate form of Watson's spatial flux. -/
@[simp]
theorem watsonF_apply
    (n : ℕ) (τ : ℝ) (u : ℝ^n → ℝ) (y : ℝ^n) (i : Fin n) :
    watsonF n τ u y i =
      (-4 * (n : ℝ) * watsonLogPhase n τ y) *
          (∂[i] u) y +
        u y *
          (watsonWeight τ y * y i +
            4 * (n : ℝ) *
              (∂[i] (watsonLogPhase n τ)) y) := by
  simp [watsonF, PDE.gradient_apply_eq_partialDeriv, smul_eq_mul,
    mul_add]

/-- Time derivative of Watson's density `Q` at a differentiability
point of the scalar field. -/
theorem deriv_watsonQ
    (n : ℕ) {τ : ℝ} (hτ : τ ≠ 0)
    (v : ℝ → ℝ^n → ℝ) (y : ℝ^n)
    (hv : DifferentiableAt ℝ (fun s ↦ v s y) τ) :
    deriv (fun s ↦ watsonQ n v s y) τ =
      (-2 * watsonWeight τ y -
          4 * (n : ℝ) *
            deriv (fun s ↦ watsonLogPhase n s y) τ) *
          v τ y +
        (2 * τ * watsonWeight τ y -
          4 * (n : ℝ) * watsonLogPhase n τ y) *
          deriv (fun s ↦ v s y) τ := by
  have hphase := hasDerivAt_watsonLogPhase n hτ y
  have hcoefficient :
      HasDerivAt
        (fun s : ℝ ↦
          2 * s * watsonWeight s y -
            4 * (n : ℝ) * watsonLogPhase n s y)
        (-2 * watsonWeight τ y -
          4 * (n : ℝ) *
            (-(n : ℝ) / (2 * τ) + ‖y‖ ^ 2 / (4 * τ ^ 2))) τ := by
    cas
  have hmainRaw := hcoefficient.mul hv.hasDerivAt
  have hmain := hmainRaw.congr_of_eventuallyEq
    (show
      (fun s : ℝ ↦ watsonQ n v s y) =ᶠ[nhds τ] _ from
      Filter.Eventually.of_forall fun s ↦ by
        simp [watsonQ])
  rw [hmain.deriv, hphase.deriv]

/-- Divergence of Watson's spatial flux at a `C²` point.

The three terms are respectively the radial derivative, the Laplacian
term, and the zeroth-order coefficient left by differentiating the
weight and the phase. -/
theorem divergence_watsonF
    (n : ℕ) {τ : ℝ} (hτ : τ ≠ 0)
    (u : ℝ^n → ℝ) (y : ℝ^n)
    (hu : ContDiffAt ℝ 2 u y) :
    ∇· (watsonF n τ u) y =
      watsonWeight τ y *
          advectiveDerivative (fun z : ℝ^n ↦ z) u y -
        4 * (n : ℝ) * watsonLogPhase n τ y * laplacian u y +
        (((n : ℝ) + 2) * watsonWeight τ y -
          2 * (n : ℝ) ^ 2 / τ) * u y := by
  have hnormSq : DifferentiableAt ℝ (fun z : ℝ^n ↦ ‖z‖ ^ 2) y := differentiableAt_id.norm_sq ℝ
  have huDiff : DifferentiableAt ℝ u y := hu.differentiableAt (by norm_num)
  have hphaseDiff : DifferentiableAt ℝ (watsonLogPhase n τ) y := by
    unfold watsonLogPhase
    fun_prop
  have hweightDiff : DifferentiableAt ℝ (watsonWeight τ) y := by
    unfold watsonWeight
    fun_prop
  have hcomponent (i : Fin n) :
      (∂[i] (fun z ↦ watsonF n τ u z i)) y =
        watsonWeight τ y * y i * (∂[i] u) y +
          (-4 * (n : ℝ) * watsonLogPhase n τ y) * (∂[i] (fun z ↦ (∂[i] u) z)) y +
          (2 * y i ^ 2 / τ ^ 2 + watsonWeight τ y - 2 * (n : ℝ) / τ) * u y := by
    have hpartial : DifferentiableAt ℝ (fun z ↦ (∂[i] u) z) y :=
      (PDE.contDiffAt_partialDeriv 1 hu i).differentiableAt (by norm_num)
    have hcoord : DifferentiableAt ℝ (fun z : ℝ^n ↦ z i) y :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt
    have hflux : (fun z : ℝ^n ↦ watsonF n τ u z i) = fun z ↦
        (-4 * (n : ℝ)) • (watsonLogPhase n τ z * (∂[i] u) z) +
          u z * (watsonWeight τ z * z i - (2 * (n : ℝ) / τ) • z i) := by
      funext z
      rw [watsonF_apply, partialDeriv_watsonLogPhase n hτ i z, smul_eq_mul, smul_eq_mul]
      cas
    have hb : DifferentiableAt ℝ (fun z : ℝ^n ↦ watsonWeight τ z * z i) y := by fun_prop
    have hc : DifferentiableAt ℝ (fun z : ℝ^n ↦ (2 * (n : ℝ) / τ) • z i) y := by fun_prop
    have hbc : DifferentiableAt ℝ
        (fun z : ℝ^n ↦ watsonWeight τ z * z i - (2 * (n : ℝ) / τ) • z i) y := by fun_prop
    rw [hflux, PDE.partialDeriv_add (by fun_prop) (by fun_prop),
      PDE.partialDeriv_const_smul, PDE.partialDeriv_mul hphaseDiff hpartial,
      PDE.partialDeriv_mul huDiff hbc, PDE.partialDeriv_sub hb hc,
      PDE.partialDeriv_mul hweightDiff hcoord, PDE.partialDeriv_const_smul,
      partialDeriv_watsonWeight, PDE.partialDeriv_coord, partialDeriv_watsonLogPhase n hτ]
    simp only [↓reduceIte, smul_eq_mul]
    ring
  have hsumAdvective : ∑ i : Fin n, watsonWeight τ y * y i * (∂[i] u) y =
      watsonWeight τ y * advectiveDerivative (fun z : ℝ^n ↦ z) u y := by
    simp only [PDE.advectiveDerivative_eq_sum_mul_partialDeriv, Finset.mul_sum, mul_assoc]
  have hsumZeroth :
      ∑ i : Fin n, (2 * y i ^ 2 / τ ^ 2 + watsonWeight τ y - 2 * (n : ℝ) / τ) * u y =
        (((n : ℝ) + 2) * watsonWeight τ y - 2 * (n : ℝ) ^ 2 / τ) * u y := by
    rw [← Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_div,
      ← Finset.mul_sum, ← EuclideanSpace.real_norm_sq_eq]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, watsonWeight]
    ring
  unfold divergence
  rw [Finset.sum_congr rfl fun i _ ↦ hcomponent i, Finset.sum_add_distrib, Finset.sum_add_distrib,
    hsumAdvective, hsumZeroth, ← Finset.mul_sum]
  unfold laplacian
  ring

/-- Watson's exact pointwise density-flux identity in positive backward time.

With `Q` and `F` as above, this says

`∂τ Q + div F = W(y · ∇v + 2τ ∂τv) - 4nf(∂τv + Δv)`.

It is the local calculation behind the heat-ball mean-value formula in
Evans, §2.3.2, and Watson's 1973 paper. -/
theorem deriv_watsonQ_add_divergence_watsonF
    (n : ℕ) {τ : ℝ} (hτ : τ ≠ 0)
    (v : ℝ → ℝ^n → ℝ) (y : ℝ^n)
    (hvTime : DifferentiableAt ℝ (fun s ↦ v s y) τ)
    (hvSpace : ContDiffAt ℝ 2 (v τ) y) :
    deriv (fun s ↦ watsonQ n v s y) τ +
        ∇· (watsonF n τ (v τ)) y =
      watsonWeight τ y *
          (advectiveDerivative (fun z : ℝ^n ↦ z) (v τ) y +
            2 * τ * deriv (fun s ↦ v s y) τ) -
        4 * (n : ℝ) * watsonLogPhase n τ y *
          (deriv (fun s ↦ v s y) τ + laplacian (v τ) y) := by
  rw [deriv_watsonQ n hτ v y hvTime,
    divergence_watsonF n hτ (v τ) y hvSpace]
  have hphaseTime :
      deriv (fun s ↦ watsonLogPhase n s y) τ =
        laplacian (watsonLogPhase n τ) y +
          watsonWeight τ y / 4 := by
    linarith [watsonLogPhase_time_sub_laplacian n hτ y]
  rw [hphaseTime, laplacian_watsonLogPhase n hτ y]
  ring

/-- For a backward-caloric field, Watson's residual identity reduces to its
transport term.  In the original time coordinate `s = -τ`, the hypothesis is
the usual heat equation. -/
theorem deriv_watsonQ_add_divergence_watsonF_of_backward_caloric
    (n : ℕ) {τ : ℝ} (hτ : τ ≠ 0)
    (v : ℝ → ℝ^n → ℝ) (y : ℝ^n)
    (hvTime : DifferentiableAt ℝ (fun s ↦ v s y) τ)
    (hvSpace : ContDiffAt ℝ 2 (v τ) y)
    (hcaloric :
      deriv (fun s ↦ v s y) τ + laplacian (v τ) y = 0) :
    deriv (fun s ↦ watsonQ n v s y) τ +
        ∇· (watsonF n τ (v τ)) y =
      watsonWeight τ y *
        (advectiveDerivative (fun z : ℝ^n ↦ z) (v τ) y +
          2 * τ * deriv (fun s ↦ v s y) τ) := by
  rw [deriv_watsonQ_add_divergence_watsonF
    n hτ v y hvTime hvSpace, hcaloric, mul_zero, sub_zero]

end HeatEquation
