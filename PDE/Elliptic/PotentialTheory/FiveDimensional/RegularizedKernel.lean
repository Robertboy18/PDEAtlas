/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Geometry.EuclideanBall
public import PDE.Analysis.Integration.Polar
public import PDE.Spaces.Sobolev.Approximation.Density.ClassicalDerivatives
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.MeasureTheory.Integral.PeakFunction
import CAS.ExactTactic

/-!
# Smooth regularization of the five-dimensional Newtonian kernel

The regularized kernel is (8π²)⁻¹ (‖X‖² + ε²)^(-3/2). For nonzero ε it is smooth.
Its negative Laplacian has unit mass; as ε tends to zero through positive
values, it converges to evaluation at the origin against test functions.
Two integrations by parts connect the regularized Hessian to the test Hessian.
-/

@[expose] public section

open PDE (partialDeriv iteratedPartialDeriv)

noncomputable section

open MeasureTheory Filter LineDeriv TopologicalSpace SobolevSpace
open scoped Distributions ENNReal Topology

namespace PotentialTheory

/-- Smooth Newtonian regularization used to justify two global integrations
by parts before taking the singular limit.  For nonzero `ε`, the squared norm
is shifted strictly away from zero.
-/
noncomputable def fiveDimensionalGammaRegularized
    (ε : ℝ) (X : ℝ^5) : ℝ :=
  (1 / (8 * Real.pi ^ 2)) *
    (‖X‖ ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ))

/-- Every nondegenerate regularized Newtonian kernel is smooth on all of
five-dimensional space. -/
theorem fiveDimensionalGammaRegularized_contDiff (ε : ℝ) (hε : ε ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞) (fiveDimensionalGammaRegularized ε) := by
  have hbase : ContDiff ℝ (⊤ : ℕ∞)
      (fun X : ℝ^5 ↦ ‖X‖ ^ 2 + ε ^ 2) :=
    (contDiff_id : ContDiff ℝ (⊤ : ℕ∞)
      (fun X : ℝ^5 ↦ X)).norm_sq ℝ |>.add contDiff_const
  have hne : ∀ X : ℝ^5, ‖X‖ ^ 2 + ε ^ 2 ≠ 0 := by
    intro X
    have hεpos : 0 < ε ^ 2 := sq_pos_of_ne_zero hε
    positivity
  change ContDiff ℝ (⊤ : ℕ∞) (fun X : ℝ^5 ↦
    (1 / (8 * Real.pi ^ 2)) *
      (‖X‖ ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ)))
  exact contDiff_const.mul (hbase.rpow_const_of_ne hne)

/-- Exact first Cartesian derivative of the smooth regularized kernel. -/
theorem fiveDimensionalGammaRegularized_partialDeriv
    (ε : ℝ) (hε : ε ≠ 0) (i : Fin 5)
    (X : ℝ^5) :
    (∂[i] (fiveDimensionalGammaRegularized ε)) X =
      -(3 / (8 * Real.pi ^ 2)) * X i *
        (‖X‖ ^ 2 + ε ^ 2) ^ (-(5 / 2 : ℝ)) := by
  let q : ℝ^5 → ℝ := fun Y ↦ ‖Y‖ ^ 2 + ε ^ 2
  let c : ℝ := 1 / (8 * Real.pi ^ 2)
  have hq : HasFDerivAt q (2 • innerSL ℝ X) X := by
    simpa [q] using (hasFDerivAt_id (𝕜 := ℝ) X).norm_sq.add_const (ε ^ 2)
  have hqX : q X ≠ 0 := (by positivity : 0 < ‖X‖ ^ 2 + ε ^ 2).ne'
  have hp := hq.rpow_const (p := (-(3 / 2 : ℝ))) (Or.inl hqX)
  have hc := hp.const_mul c
  have hfun : fiveDimensionalGammaRegularized ε =
      fun Y ↦ c * q Y ^ (-(3 / 2 : ℝ)) := by
    rfl
  rw [hfun]
  unfold partialDeriv
  rw [hc.fderiv]
  simp [q, c, EuclideanSpace.inner_single_right]
  field_simp [Real.pi_ne_zero]
  ring_nf

/-- Fréchet derivative of the first Cartesian derivative of the regularized kernel. -/
private theorem fiveDimensionalGammaRegularized_partialDeriv_hasFDerivAt
    (ε : ℝ) (hε : ε ≠ 0) (i : Fin 5)
    (X : ℝ^5) :
    HasFDerivAt
      (fun Y ↦ (∂[i] (fiveDimensionalGammaRegularized ε)) Y)
      ((-(3 / (8 * Real.pi ^ 2))) •
        ((X i) •
          (((-(5 / 2 : ℝ)) * (‖X‖ ^ 2 + ε ^ 2) ^ (-(5 / 2 : ℝ) - 1)) •
            (2 • innerSL ℝ X)) +
          (‖X‖ ^ 2 + ε ^ 2) ^ (-(5 / 2 : ℝ)) •
            (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 5 ↦ ℝ) i))) X := by
  let q : ℝ^5 → ℝ := fun Y ↦ ‖Y‖ ^ 2 + ε ^ 2
  let K : ℝ := 3 / (8 * Real.pi ^ 2)
  let L : ℝ^5 →L[ℝ] ℝ :=
    PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 5 ↦ ℝ) i
  let B : ℝ^5 → ℝ := fun Y ↦
    -K * Y i * q Y ^ (-(5 / 2 : ℝ))
  have hq : HasFDerivAt q (2 • innerSL ℝ X) X := by
    simpa [q] using (hasFDerivAt_id (𝕜 := ℝ) X).norm_sq.add_const (ε ^ 2)
  have hqX : q X ≠ 0 := (by positivity : 0 < ‖X‖ ^ 2 + ε ^ 2).ne'
  have hpow := hq.rpow_const (p := (-(5 / 2 : ℝ))) (Or.inl hqX)
  have hcoord : HasFDerivAt (fun Y : ℝ^5 ↦ Y i) L X := by
    simpa [L] using L.hasFDerivAt
  let P : ℝ^5 →L[ℝ] ℝ :=
    ((-(5 / 2 : ℝ)) * q X ^ (-(5 / 2 : ℝ) - 1)) • (2 • innerSL ℝ X)
  have hpow' : HasFDerivAt (fun Y ↦ q Y ^ (-(5 / 2 : ℝ))) P X := by
    simpa only [P] using hpow
  let B' : ℝ^5 →L[ℝ] ℝ :=
    (-K) • ((X i) • P + q X ^ (-(5 / 2 : ℝ)) • L)
  have hB : HasFDerivAt B B' X := by
    simpa [B, B', mul_assoc, add_comm] using (hcoord.mul hpow').const_mul (-K)
  rwa [show (fun Y ↦ (∂[i] (fiveDimensionalGammaRegularized ε)) Y) = B from
    funext (fiveDimensionalGammaRegularized_partialDeriv ε hε i)]

/-- Exact Cartesian Hessian of the smooth regularized Newtonian kernel. This
is the nonsingular approximation to the principal-value kernel appearing in
the distributional Hessian formula.
-/
theorem fiveDimensionalGammaRegularized_iteratedPartialDeriv_two
    (ε : ℝ) (hε : ε ≠ 0) (i j : Fin 5)
    (X : ℝ^5) :
    iteratedPartialDeriv (n := 5) [j, i]
        (fiveDimensionalGammaRegularized ε) X =
      (15 / (8 * Real.pi ^ 2)) * X i * X j *
          (‖X‖ ^ 2 + ε ^ 2) ^ (-(7 / 2 : ℝ)) -
        (3 / (8 * Real.pi ^ 2)) * (if i = j then 1 else 0) *
          (‖X‖ ^ 2 + ε ^ 2) ^ (-(5 / 2 : ℝ)) := by
  simp only [iteratedPartialDeriv]
  change fderiv ℝ (fun Y ↦ (∂[i]
      (fiveDimensionalGammaRegularized ε)) Y) X (EuclideanSpace.single j (1 : ℝ)) = _
  rw [(fiveDimensionalGammaRegularized_partialDeriv_hasFDerivAt ε hε i X).fderiv]
  norm_num [EuclideanSpace.inner_single_right, eq_comm]
  field_simp [Real.pi_ne_zero]
  ring

/-- The regularized Hessian has a strictly negative trace.  Its density is
the smooth radial approximation to the Dirac mass that remains after the
traceless punctured-space Hessian is integrated.
-/
theorem fiveDimensionalGammaRegularized_hessian_trace
    (ε : ℝ) (hε : ε ≠ 0) (X : ℝ^5) :
    ∑ i : Fin 5, iteratedPartialDeriv (n := 5) [i, i]
        (fiveDimensionalGammaRegularized ε) X =
      -(15 / (8 * Real.pi ^ 2)) * ε ^ 2 *
        (‖X‖ ^ 2 + ε ^ 2) ^ (-(7 / 2 : ℝ)) := by
  let q : ℝ := ‖X‖ ^ 2 + ε ^ 2
  have hqpos : 0 < q := by
    dsimp [q]
    positivity
  have hsquare : ∑ i : Fin 5, X i * X i = ‖X‖ ^ 2 := by
    simpa [pow_two] using (EuclideanSpace.real_norm_sq_eq X).symm
  have hshift : q ^ (-(5 / 2 : ℝ)) = q * q ^ (-(7 / 2 : ℝ)) := by
    calc
      q ^ (-(5 / 2 : ℝ)) = q ^ ((1 : ℝ) + (-(7 / 2 : ℝ))) := by
        congr 1
        ring
      _ = q ^ (1 : ℝ) * q ^ (-(7 / 2 : ℝ)) :=
        Real.rpow_add hqpos 1 (-(7 / 2 : ℝ))
      _ = q * q ^ (-(7 / 2 : ℝ)) := by rw [Real.rpow_one]
  simp_rw [fiveDimensionalGammaRegularized_iteratedPartialDeriv_two ε hε,
    ite_eq_left]
  rw [Finset.sum_sub_distrib]
  have hfirst :
      (∑ i : Fin 5, (15 / (8 * Real.pi ^ 2)) * X i * X i *
        q ^ (-(7 / 2 : ℝ))) =
      (15 / (8 * Real.pi ^ 2)) * (∑ i : Fin 5, X i * X i) *
        q ^ (-(7 / 2 : ℝ)) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have hsecond :
      (∑ _i : Fin 5, (3 / (8 * Real.pi ^ 2)) * 1 *
        q ^ (-(5 / 2 : ℝ))) =
      (15 / (8 * Real.pi ^ 2)) * q ^ (-(5 / 2 : ℝ)) := by
    cas
  change
    (∑ i : Fin 5, (15 / (8 * Real.pi ^ 2)) * X i * X i *
      q ^ (-(7 / 2 : ℝ))) -
      (∑ _i : Fin 5, (3 / (8 * Real.pi ^ 2)) * 1 *
        q ^ (-(5 / 2 : ℝ))) = _
  rw [hfirst, hsecond, hsquare, hshift]
  dsimp [q]
  ring

/-- Antiderivative calculation for the radial mass of the regularized
five-dimensional Newtonian kernel.
-/
theorem hasDerivAt_fiveDimensionalRegularizedMassPrimitive (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ (1 / 5 : ℝ) * y ^ 5 *
      (1 + y ^ 2) ^ (-(5 / 2 : ℝ)))
      (x ^ 4 * (1 + x ^ 2) ^ (-(7 / 2 : ℝ))) x := by
  cas

/-- For `0 < x`, `(x⁻¹ ^ 2) ^ (-(a / 2)) = x ^ a`. -/
private theorem inv_sq_rpow_neg_half {x : ℝ} (hx : 0 < x) (a : ℝ) :
    (x⁻¹ ^ 2) ^ (-(a / 2)) = x ^ a := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (inv_nonneg.2 hx.le), Real.inv_rpow hx.le,
    ← Real.rpow_neg hx.le]
  congr 1
  push_cast
  ring

/-- Exact radial integral of the normalized five-dimensional approximate
identity at unit scale.
-/
theorem integral_Ioi_fiveDimensionalRegularizedMass :
    (∫ x : ℝ in Set.Ioi 0,
      x ^ 4 * (1 + x ^ 2) ^ (-(7 / 2 : ℝ))) = 1 / 5 := by
  have hbase : Tendsto (fun x : ℝ ↦ 1 + x⁻¹ ^ 2) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add ((tendsto_inv_atTop_zero (𝕜 := ℝ)).pow 2)
  have hg : Tendsto (fun x : ℝ ↦ (1 / 5 : ℝ) * x ^ 5 * (1 + x ^ 2) ^ (-(5 / 2 : ℝ))) atTop
      (𝓝 (1 / 5 : ℝ)) := by
    have h := (hbase.rpow_const (p := -(5 / 2 : ℝ)) (Or.inl one_ne_zero)).const_mul (1 / 5 : ℝ)
    rw [Real.one_rpow, mul_one] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [show 1 + x⁻¹ ^ 2 = x⁻¹ ^ 2 * (1 + x ^ 2) by
        rw [mul_add, mul_one, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hx.ne'), add_comm],
      Real.mul_rpow (by positivity) (by positivity), inv_sq_rpow_neg_half hx 5, Real.rpow_ofNat]
    ring
  simpa using integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun x (_ : x ∈ Set.Ici 0) ↦ hasDerivAt_fiveDimensionalRegularizedMassPrimitive x)
    (fun x _ ↦ by positivity) hg

/-- The unit-scale negative trace density of the regularized Newtonian kernel
has total mass one on five-dimensional space.
-/
theorem fiveDimensionalRegularizedTraceDensity_unitMass :
    (∫ X : ℝ^5,
      (15 / (8 * Real.pi ^ 2)) *
        (‖X‖ ^ 2 + 1) ^ (-(7 / 2 : ℝ))) = 1 := by
  have hrad : (∫ r : ℝ in Set.Ioi 0, r ^ (Module.finrank ℝ ℝ^5 - 1) •
      (r ^ 2 + 1) ^ (-(7 / 2 : ℝ))) = 1 / 5 := by
    simpa [add_comm, smul_eq_mul] using integral_Ioi_fiveDimensionalRegularizedMass
  have harea : (Module.finrank ℝ ℝ^5 : ℝ) * (volume : Measure ℝ^5).real (Metric.ball 0 1) =
      8 * Real.pi ^ 2 / 3 := by
    rw [← Measure.toSphere_real_apply_univ]
    have := PDE.Analysis.unitSphereArea_eq 5
    rw [PDE.Analysis.unitSphereArea, PDE.Analysis.unitBallVolume_five] at this
    rw [measureReal_def, this]
    ring
  rw [integral_const_mul, integral_fun_norm_addHaar volume fun r ↦ (r ^ 2 + 1) ^ (-(7 / 2 : ℝ)),
    hrad, nsmul_eq_mul, smul_eq_mul, ← mul_assoc (Module.finrank ℝ ℝ^5 : ℝ), harea]
  field_simp [Real.pi_ne_zero]
  ring

/-- Scaling identity for the normalized trace density.
-/
theorem fiveDimensionalRegularizedTraceDensity_scale
    (ε : ℝ) (hε : 0 < ε) (X : ℝ^5) :
    (15 / (8 * Real.pi ^ 2)) * ε ^ 2 *
        (‖X‖ ^ 2 + ε ^ 2) ^ (-(7 / 2 : ℝ)) =
      ε⁻¹ ^ 5 * ((15 / (8 * Real.pi ^ 2)) *
        (‖ε⁻¹ • X‖ ^ 2 + 1) ^ (-(7 / 2 : ℝ))) := by
  have hεne : ε ≠ 0 := hε.ne'
  have hnorm : ‖ε⁻¹ • X‖ = ε⁻¹ * ‖X‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hε)]
  have hbase : (ε⁻¹ * ‖X‖) ^ 2 + 1 =
      ε⁻¹ ^ 2 * (‖X‖ ^ 2 + ε ^ 2) := by
    field_simp [hεne]
  have hfactor : (ε⁻¹ ^ 2) ^ (-(7 / 2 : ℝ)) = ε ^ 7 := by
    rw [inv_sq_rpow_neg_half hε 7, Real.rpow_ofNat]
  rw [hnorm, hbase, Real.mul_rpow (sq_nonneg ε⁻¹)
    (by positivity : 0 ≤ ‖X‖ ^ 2 + ε ^ 2), hfactor]
  field_simp [hεne]

/-- For every positive regularization parameter, the negative trace density
has total mass exactly one.
-/
theorem fiveDimensionalRegularizedTraceDensity_mass
    (ε : ℝ) (hε : 0 < ε) :
    (∫ X : ℝ^5,
      (15 / (8 * Real.pi ^ 2)) * ε ^ 2 *
        (‖X‖ ^ 2 + ε ^ 2) ^ (-(7 / 2 : ℝ))) = 1 := by
  let d : ℝ^5 → ℝ := fun X ↦
    (15 / (8 * Real.pi ^ 2)) *
      (‖X‖ ^ 2 + 1) ^ (-(7 / 2 : ℝ))
  have hscale : (fun X : ℝ^5 ↦
      (15 / (8 * Real.pi ^ 2)) * ε ^ 2 *
        (‖X‖ ^ 2 + ε ^ 2) ^ (-(7 / 2 : ℝ))) =
      fun X ↦ ε⁻¹ ^ 5 * d (ε⁻¹ • X) := by
    funext X
    exact fiveDimensionalRegularizedTraceDensity_scale ε hε X
  rw [hscale, MeasureTheory.integral_const_mul]
  rw [MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg
    (volume : Measure ℝ^5) d hε.le]
  have hd : (∫ X : ℝ^5, d X) = 1 := by
    simpa [d] using fiveDimensionalRegularizedTraceDensity_unitMass
  rw [hd]
  simp
  field_simp [hε.ne']

/-- The unit trace density has the decay required by mathlib's peak-function
approximate-identity theorem.
-/
theorem fiveDimensionalRegularizedTraceDensity_decay :
    Tendsto (fun X : ℝ^5 ↦
      ‖X‖ ^ Module.finrank ℝ ℝ^5 *
        ((15 / (8 * Real.pi ^ 2)) *
          (‖X‖ ^ 2 + 1) ^ (-(7 / 2 : ℝ))))
      (Bornology.cobounded ℝ^5) (nhds 0) := by
  let C : ℝ := 15 / (8 * Real.pi ^ 2)
  have hbase : Tendsto (fun r : ℝ ↦ 1 + r⁻¹ ^ 2) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add ((tendsto_inv_atTop_zero (𝕜 := ℝ)).pow 2)
  have hq : Tendsto (fun r : ℝ ↦ C * r⁻¹ ^ 2 * (1 + r⁻¹ ^ 2) ^ (-(7 / 2 : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul ((tendsto_inv_atTop_zero (𝕜 := ℝ)).pow 2)).mul
      (hbase.rpow_const (p := -(7 / 2 : ℝ)) (Or.inl one_ne_zero))
  have hscalar : Tendsto (fun r : ℝ ↦ r ^ 5 * (C * (r ^ 2 + 1) ^ (-(7 / 2 : ℝ)))) atTop (𝓝 0) := by
    refine hq.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    rw [show 1 + r⁻¹ ^ 2 = r⁻¹ ^ 2 * (r ^ 2 + 1) by
        rw [mul_add, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hr.ne'), mul_one],
      Real.mul_rpow (by positivity) (by positivity), inv_sq_rpow_neg_half hr 7, Real.rpow_ofNat]
    field_simp
  rw [show Module.finrank ℝ ℝ^5 = 5 by simp]
  exact hscalar.comp tendsto_norm_cobounded_atTop

/-- The normalized negative trace density converges to the Dirac mass at the
origin when tested against a smooth compactly supported function.
-/
theorem fiveDimensionalRegularizedTraceDensity_testFunction_tendsto
    (φ : 𝓓((⊤ : Opens ℝ^5), ℝ)) :
    Tendsto (fun ε : ℝ ↦
      ∫ X : ℝ^5,
        ((15 / (8 * Real.pi ^ 2)) * ε ^ 2 *
          (‖X‖ ^ 2 + ε ^ 2) ^ (-(7 / 2 : ℝ))) * φ.toFun X)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (φ.toFun 0)) := by
  let d : ℝ^5 → ℝ := fun X ↦
    (15 / (8 * Real.pi ^ 2)) *
      (‖X‖ ^ 2 + 1) ^ (-(7 / 2 : ℝ))
  have hdnonneg : ∀ X, 0 ≤ d X := by
    intro X
    dsimp [d]
    positivity
  have hdmass : (∫ X, d X) = 1 := by
    simpa [d] using fiveDimensionalRegularizedTraceDensity_unitMass
  have hddecay : Tendsto (fun X : ℝ^5 ↦
      ‖X‖ ^ Module.finrank ℝ ℝ^5 * d X)
      (Bornology.cobounded ℝ^5) (nhds 0) := by
    simpa [d] using fiveDimensionalRegularizedTraceDensity_decay
  have hpeak := tendsto_integral_comp_smul_smul_of_integrable
    (μ := volume) hdnonneg hdmass hddecay
      (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport)
      φ.contDiff.continuous.continuousAt
  have hcomp := hpeak.comp (tendsto_inv_nhdsGT_zero :
    Tendsto (fun ε : ℝ ↦ ε⁻¹) (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop)
  apply hcomp.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  apply integral_congr_ae
  filter_upwards [] with X
  have hscale := fiveDimensionalRegularizedTraceDensity_scale ε hε X
  simpa [d, smul_eq_mul] using
    congrArg (fun z : ℝ ↦ z * φ.toFun X) hscale.symm

/-- Distributional Poisson identity for the smooth regularizations:
`-Δ Γ_ε` converges to evaluation at the origin.
-/
theorem fiveDimensionalGammaRegularized_laplacian_tendsto_delta
    (φ : 𝓓((⊤ : Opens ℝ^5), ℝ)) :
    Tendsto (fun ε : ℝ ↦
      ∫ X : ℝ^5,
        (-(∑ i : Fin 5, iteratedPartialDeriv (n := 5) [i, i]
          (fiveDimensionalGammaRegularized ε) X)) * φ.toFun X)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (φ.toFun 0)) := by
  apply fiveDimensionalRegularizedTraceDensity_testFunction_tendsto φ |>.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  apply integral_congr_ae
  filter_upwards [] with X
  rw [fiveDimensionalGammaRegularized_hessian_trace ε hε.ne' X]
  ring

/-- Two global integrations by parts move the test Hessian onto the smooth
regularized Newtonian kernel, with no boundary term.
-/
theorem fiveDimensionalGammaRegularized_integral_by_parts
    (ε : ℝ) (hε : ε ≠ 0) (i j : Fin 5)
    (φ : 𝓓((⊤ : Opens ℝ^5), ℝ)) :
    (∫ X : ℝ^5,
      fiveDimensionalGammaRegularized ε X *
        iteratedPartialDeriv (n := 5) [i, j] φ.toFun X) =
      ∫ X : ℝ^5,
        iteratedPartialDeriv (n := 5) [j, i]
          (fiveDimensionalGammaRegularized ε) X * φ.toFun X := by
  have hreg : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fiveDimensionalGammaRegularized ε) :=
    (fiveDimensionalGammaRegularized_contDiff ε hε).of_le (by simp)
  have h := GraphSpace.integral_by_parts_iteratedPartialDeriv_rev
    (n := 5) (f := fiveDimensionalGammaRegularized ε) hreg [i, j] φ
  simpa using h

end PotentialTheory
