/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Nonuniqueness.Statement
public import PDE.Fluid.NavierStokes.ClassicalEnergy.Gradient
public import PDE.Fluid.NavierStokes.LocalEnergy.Divergence
public import PDE.Fluid.NavierStokes.WeakMomentumBounds
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import PDE.Analysis.Integration.TimeSlice
import PDE.Analysis.MeasureTheory.Lp.PairingConvergence
import PDE.FDeriv.PartialDeriv.Regularity
import PDE.FDeriv.PartialDeriv.Support
import PDE.Fluid.Incompressible.DivergenceLimits

/-!
# The weak momentum equation of a classical solution

A velocity and pressure that solve the Navier–Stokes equations classically on the open slab
`(0,T) × ℝ^n`, lie in the energy class `ClassicalEnergyClass`, and take an `L²` initial trace form a
pressure-retaining weak solution with the slice gradient as weak gradient
(`classicalPressureWeakSolution`).

## How it works

On a slice of the open slab the weak momentum integrand plus `∂ₜ(u · φ)` is a spatial divergence, so
the slice pairing is minus the spatial integral of `∂ₜ(u · φ)`
(`weakMomentumSlice_sliceGradient_eq`). Integrating over `[s,t] ⊂ (0,T)` gives
`∫ₛᵗ (pairing) = ∫ u(s) · φ(s) - ∫ u(t) · φ(t)`
(`intervalIntegral_weakMomentumSlice_sliceGradient`). As `s → 0` the first term tends to the initial
pairing by the `L²` trace, and as `t → T` the second tends to zero by `L²` continuity at `T`,
because the test vanishes at `T` (`integral_weakMomentumSlice_sliceGradient_eq_initial`).
Incompressibility holds at positive times below `T` pointwise, at time zero by the datum, and at `T`
as an `L²` limit (`distributionallyDivergenceFree_velocitySlice_of_classical`).
-/

@[expose] public noncomputable section

namespace NavierStokes

open EuclideanSpace MeasureTheory Filter IncompressibleFlow PDE PDE.Common
open scoped Topology ENNReal

set_option linter.missingDocs true

variable {n : ℕ}

/-- The pairing `u · φ` vanishes off the support of `φ`. -/
theorem tsupport_inner_subset {u φ : ℝ^(n + 1) → ℝ^n} :
    tsupport (fun z ↦ inner ℝ (u z) (φ z)) ⊆ tsupport φ := by
  apply closure_mono
  intro z hz'
  by_contra hφz
  apply hz'
  simp [Function.notMem_support.mp hφz]

section Slab

variable {nse : Problem n} {u : ℝ^(n + 1) → ℝ^n} {p : ℝ^(n + 1) → ℝ} {T : ℝ}
  {φ : ℝ^(n + 1) → ℝ^n}

/-- The pairing `u · φ` of a `C²` velocity with a smooth test is `C²` at slab points. -/
theorem contDiffAt_inner_test (hu : ∀ z ∈ finiteTimeDomain n T, ContDiffAt ℝ 2 u z)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) {z : ℝ^(n + 1)} (hz : z ∈ finiteTimeDomain n T) :
    ContDiffAt ℝ 2 (fun y ↦ inner ℝ (u y) (φ y)) z :=
  (hu z hz).inner ℝ (hφ.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))

/-- The weak momentum flux of a classical solution against a smooth test is `C¹` at slab
points. -/
theorem contDiffAt_weakMomentumFlux (hu : ∀ z ∈ finiteTimeDomain n T, ContDiffAt ℝ 2 u z)
    (hp : ∀ z ∈ finiteTimeDomain n T, ContDiffAt ℝ 1 p z) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (j : Fin n) {z : ℝ^(n + 1)} (hz : z ∈ finiteTimeDomain n T) :
    ContDiffAt ℝ 1 (weakMomentumFlux nse u p φ j) z := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hφi (i : Fin n) : ContDiffAt ℝ 1 (fun y ↦ φ y i) z :=
    ((contDiff_piLp 2).mp hφ1 i).contDiffAt
  have hui (i : Fin n) : ContDiffAt ℝ 1 (fun y ↦ u y i) z :=
    ((contDiffAt_piLp 2).mp (hu z hz) i).of_le (by norm_num)
  have hdu (i : Fin n) : ContDiffAt ℝ 1 (∂[j.succ] (fun y ↦ u y i)) z :=
    ((contDiffAt_piLp 2).mp (hu z hz) i).partialDeriv j.succ (by norm_num)
  change ContDiffAt ℝ 1 (fun y ↦ (nse.kinematicViscosity : ℝ) *
      ∑ i : Fin n, (∂[j.succ] (fun y ↦ u y i)) y * φ y i -
    ∑ i : Fin n, u y i * u y j * φ y i - p y * φ y j) z
  exact ((contDiffAt_const.mul (ContDiffAt.sum fun i _ ↦ (hdu i).mul (hφi i))).sub
    (ContDiffAt.sum fun i _ ↦ ((hui i).mul (hui j)).mul (hφi i))).sub
    ((hp z hz).mul (hφi j))

/-- On a slice of the open slab, the weak momentum pairing of a classical solution with its
slice gradient is minus the spatial integral of `∂ₜ(u · φ)`. -/
theorem weakMomentumSlice_sliceGradient_eq
    (hu : ∀ z ∈ finiteTimeDomain n T, ContDiffAt ℝ 2 u z)
    (hp : ∀ z ∈ finiteTimeDomain n T, ContDiffAt ℝ 1 p z)
    (hdiv : ∀ z ∈ finiteTimeDomain n T, DivergenceFreeAt u z)
    (hmom : ∀ z ∈ finiteTimeDomain n T, MomentumEquationAt nse u p z)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) {τ : ℝ} (hτ : τ ∈ Set.Ioo 0 T) :
    weakMomentumSlice nse u p (sliceGradient u) φ τ =
      -∫ x, (∂[0] (fun z ↦ inner ℝ (u z) (φ z))) (timeSpaceCons τ x) := by
  set K := spatialPart '' tsupport φ
  have hK : IsCompact K := isCompact_spatialPart_image_tsupport hc
  have hz := timeSpaceCons_mem_finiteTimeDomain (n := n) hτ
  have hsuppV (j : Fin n) : tsupport (weakMomentumFlux nse u p φ j) ⊆ tsupport φ := by
    apply closure_mono
    intro z hz'
    by_contra hφz
    exact hz' (weakMomentumFlux_eq_zero j (Function.notMem_support.mp hφz))
  have hsuppG := tsupport_inner_subset (u := u) (φ := φ)
  have hint (x : ℝ^n) : weakMomentumIntegrand nse u p (sliceGradient u) φ τ x =
      (∑ j : Fin n, (∂[j.succ] (weakMomentumFlux nse u p φ j)) (timeSpaceCons τ x)) -
        (∂[0] (fun z ↦ inner ℝ (u z) (φ z))) (timeSpaceCons τ x) := by
    have hsg : sliceGradient u (timeSpaceCons τ x) =
        spatialVelocityGradient n u (timeSpaceCons τ x) :=
      sliceGradient_eq_spatialVelocityGradient (by simpa using hτ.1)
        ((hu _ (hz x)).differentiableAt (by norm_num))
    have h := weakMomentumIntegrand_add_partialDeriv_inner_eq_sum (nse := nse) (hu _ (hz x))
      ((hp _ (hz x)).differentiableAt (by norm_num))
      (hφ.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)) (hdiv _ (hz x)) (hmom _ (hz x))
    have heq : weakMomentumIntegrand nse u p (sliceGradient u) φ τ x =
        weakMomentumIntegrand nse u p (spatialVelocityGradient n u) φ τ x := by
      simp only [weakMomentumIntegrand, hsg]
    rw [heq]
    linarith
  have hV (j : Fin n) (x : ℝ^n) :
      ContDiffAt ℝ 1 (weakMomentumFlux nse u p φ j) (timeSpaceCons τ x) :=
    contDiffAt_weakMomentumFlux hu hp hφ j (hz x)
  have hVc (j : Fin n) : HasCompactSupport fun x ↦ weakMomentumFlux nse u p φ j
      (timeSpaceCons τ x) :=
    HasCompactSupport.intro hK fun x hx ↦ weakMomentumFlux_eq_zero j
      (image_eq_zero_of_notMem_tsupport (timeSpaceCons_notMem_tsupport hx τ))
  have hsum : Integrable fun x ↦
      ∑ j : Fin n, (∂[j.succ] (weakMomentumFlux nse u p φ j)) (timeSpaceCons τ x) := by
    apply PDE.Analysis.integrable_timeSlice_of_continuousAt
      (F := fun z ↦ ∑ j : Fin n, (∂[j.succ] (weakMomentumFlux nse u p φ j)) z) hK τ
    · intro x
      exact tendsto_finsetSum _ fun j _ ↦ (hV j x).continuousAt_partialDeriv j.succ
    · intro x hx
      apply Finset.sum_eq_zero
      intro j _
      exact partialDeriv_eq_zero_of_notMem_tsupport j.succ
        fun h ↦ timeSpaceCons_notMem_tsupport hx τ (hsuppV j h)
  have hD : Integrable fun x ↦
      (∂[0] (fun z ↦ inner ℝ (u z) (φ z))) (timeSpaceCons τ x) := by
    apply PDE.Analysis.integrable_timeSlice_of_continuousAt
      (F := ∂[0] (fun z ↦ inner ℝ (u z) (φ z))) hK τ
    · intro x
      exact ((contDiffAt_inner_test hu hφ (hz x)).of_le (by norm_num)).continuousAt_partialDeriv 0
    · intro x hx
      exact partialDeriv_eq_zero_of_notMem_tsupport 0
        fun h ↦ timeSpaceCons_notMem_tsupport hx τ (hsuppG h)
  unfold weakMomentumSlice
  rw [integral_congr_ae (Eventually.of_forall hint), integral_sub hsum hD,
    PDE.Analysis.integral_timeSlice_sum_partialDeriv_eq_zero τ hV hVc, zero_sub]

/-- The spatial integral of `∂ₜ(u · φ)` over slices depends continuously on time in `(0,T)`. -/
theorem continuousOn_integral_partialDeriv_inner
    (hu : ∀ z ∈ finiteTimeDomain n T, ContDiffAt ℝ 2 u z)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    ContinuousOn (fun τ ↦ ∫ x, (∂[0] (fun z ↦ inner ℝ (u z) (φ z))) (timeSpaceCons τ x))
      (Set.Ioo 0 T) := by
  have hK := isCompact_spatialPart_image_tsupport hc
  have hsuppG := tsupport_inner_subset (u := u) (φ := φ)
  apply continuousOn_integral_of_compact_support hK
  · rintro ⟨τ, x⟩ ⟨hτ, -⟩
    have hz := timeSpaceCons_mem_finiteTimeDomain (n := n) hτ x
    exact (((contDiffAt_inner_test hu hφ hz).of_le (by norm_num)).continuousAt_partialDeriv
      0).comp (f := fun q : ℝ × ℝ^n ↦ timeSpaceCons q.1 q.2) (x := (τ, x))
      ((PDE.Common.contDiff_timeSpaceCons_uncurry n (m := 0)).continuous.continuousAt)
      |>.continuousWithinAt
  · intro τ x _ hx
    exact partialDeriv_eq_zero_of_notMem_tsupport 0
      fun h ↦ timeSpaceCons_notMem_tsupport hx τ (hsuppG h)

/-- Over `[s,t] ⊂ (0,T)`, the weak momentum pairing of a classical solution integrates to the
difference of the slice pairings with the test. -/
theorem intervalIntegral_weakMomentumSlice_sliceGradient
    (hu : ∀ z ∈ finiteTimeDomain n T, ContDiffAt ℝ 2 u z)
    (hp : ∀ z ∈ finiteTimeDomain n T, ContDiffAt ℝ 1 p z)
    (hdiv : ∀ z ∈ finiteTimeDomain n T, DivergenceFreeAt u z)
    (hmom : ∀ z ∈ finiteTimeDomain n T, MomentumEquationAt nse u p z)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) {s t : ℝ} (hs : 0 < s)
    (hst : s ≤ t) (ht : t < T) :
    ∫ τ in s..t, weakMomentumSlice nse u p (sliceGradient u) φ τ =
      (∫ x, inner ℝ (u (timeSpaceCons s x)) (φ (timeSpaceCons s x))) -
        ∫ x, inner ℝ (u (timeSpaceCons t x)) (φ (timeSpaceCons t x)) := by
  have hK := isCompact_spatialPart_image_tsupport hc
  have hG := PDE.Analysis.integral_timeSlice_sub_eq_intervalIntegral
    (G := fun z ↦ inner ℝ (u z) (φ z)) hK
    (fun τ x hx ↦ by
      simp [image_eq_zero_of_notMem_tsupport (timeSpaceCons_notMem_tsupport hx τ)]) hst
    (fun τ hτ x ↦ (contDiffAt_inner_test hu hφ (timeSpaceCons_mem_finiteTimeDomain
      ⟨hs.trans_le hτ.1, hτ.2.trans_lt ht⟩ x)).of_le (by norm_num))
  rw [intervalIntegral.integral_congr (g := fun τ ↦
      -∫ x, (∂[0] (fun z ↦ inner ℝ (u z) (φ z))) (timeSpaceCons τ x)),
    intervalIntegral.integral_neg, ← hG]
  · ring
  · intro τ hτ
    rw [Set.uIcc_of_le hst] at hτ
    exact weakMomentumSlice_sliceGradient_eq hu hp hdiv hmom hφ hc
      ⟨hs.trans_le hτ.1, hτ.2.trans_lt ht⟩

/-- The velocity slices of an energy-class field with square-integrable time-zero slice are
square integrable on `[0,T]`. -/
theorem memLp_velocitySlice_of_classicalEnergyClass (hclass : ClassicalEnergyClass u p T)
    (h0 : MemLp (velocitySlice u 0) 2 volume) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    MemLp (velocitySlice u t) 2 volume := by
  rcases ht.1.eq_or_lt with h | h
  · subst h
    exact h0
  · exact hclass.velocity_memLp t ⟨h, ht.2⟩

/-- The slice gradient of an energy-class field is square integrable on every slice of
`[0,T]`; it vanishes at time zero. -/
theorem memLp_sliceGradient_of_classicalEnergyClass (hclass : ClassicalEnergyClass u p T)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    MemLp (spatialGradientSlice (sliceGradient u) t) 2 volume := by
  rcases ht.1.eq_or_lt with h | h
  · subst h
    have hz : spatialGradientSlice (sliceGradient u) 0 = 0 := by
      funext x
      exact sliceGradient_of_nonpos u (by simp)
    rw [hz]
    exact MemLp.zero
  · exact memLp_spatialGradientSlice_sliceGradient h (hclass.slice_contDiff t ⟨h, ht.2⟩)
      (hclass.gradient_memLp t ⟨h, ht.2⟩)

/-- The `L²` norm of the slice gradient is at most `√n` times that of the slice derivative. -/
theorem toReal_eLpNorm_sliceGradient_le (hclass : ClassicalEnergyClass u p T) {t : ℝ}
    (ht : t ∈ Set.Ioc 0 T) :
    (eLpNorm (spatialGradientSlice (sliceGradient u) t) 2 volume).toReal ≤
      √n * (eLpNorm (fderiv ℝ (velocitySlice u t)) 2 volume).toReal := by
  have hle := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (p := 2) (μ := volume)
    (f := spatialGradientSlice (sliceGradient u) t) (g := fderiv ℝ (velocitySlice u t))
    (c := √n) (memLp_spatialGradientSlice_sliceGradient ht.1 (hclass.slice_contDiff t ht)
      (hclass.gradient_memLp t ht)).aestronglyMeasurable (Eventually.of_forall fun x ↦
      norm_sliceGradient_le ht.1 ((hclass.slice_contDiff t ht).differentiable (by norm_num) x))
  have hfin := (hclass.gradient_memLp t ht).eLpNorm_ne_top
  calc (eLpNorm (spatialGradientSlice (sliceGradient u) t) 2 volume).toReal
      ≤ (ENNReal.ofReal √n * eLpNorm (fderiv ℝ (velocitySlice u t)) 2 volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hle
    _ = _ := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]

/-- The weak momentum pairing of a classical energy-class solution is integrable in time on
`[0,T]`. -/
theorem integrableOn_weakMomentumSlice_sliceGradient (hforce : nse.forcing = 0)
    (hu : ∀ z ∈ finiteTimeDomain n T, ContDiffAt ℝ 2 u z)
    (hp : ∀ z ∈ finiteTimeDomain n T, ContDiffAt ℝ 1 p z)
    (hdiv : ∀ z ∈ finiteTimeDomain n T, DivergenceFreeAt u z)
    (hmom : ∀ z ∈ finiteTimeDomain n T, MomentumEquationAt nse u p z)
    (hclass : ClassicalEnergyClass u p T) (hφ : IncompressibleFlow.IsWeakMomentumTest T φ) :
    IntegrableOn (weakMomentumSlice nse u p (sliceGradient u) φ) (Set.Icc 0 T) := by
  obtain ⟨M, hM0, hM⟩ := exists_abs_weakMomentumSlice_le hforce hφ
  obtain ⟨C, hC⟩ := hclass.velocity_bounded
  set B := max C 0
  have hB (t : ℝ) (ht : t ∈ Set.Ioc 0 T) : (eLpNorm (velocitySlice u t) 2 volume).toReal ≤ B :=
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hC t ht)).trans
      (by rw [ENNReal.toReal_ofReal'])
  set b2 : ℝ → ℝ := fun t ↦ (eLpNorm (fderiv ℝ (velocitySlice u t)) 2 volume).toReal ^ 2
  set q : ℝ → ℝ := fun t ↦ (eLpNorm (fun x ↦ p (timeSpaceCons t x)) 2 volume).toReal
  set g : ℝ → ℝ := fun t ↦ M * (B + B ^ 2 + q t + √n * (1 + b2 t))
  have hIoc : (volume.restrict (Set.Icc (0 : ℝ) T)) = volume.restrict (Set.Ioc 0 T) :=
    Measure.restrict_congr_set Ioc_ae_eq_Icc |>.symm
  have hfinite : volume (Set.Ioc (0 : ℝ) T) ≠ ⊤ := measure_Ioc_lt_top.ne
  have hg : IntegrableOn g (Set.Ioc 0 T) := by
    have hconst (c : ℝ) : IntegrableOn (fun _ : ℝ ↦ c) (Set.Ioc 0 T) :=
      integrableOn_const hfinite
    exact (((hconst (B + B ^ 2)).add hclass.pressure_integrableOn).add
      (((hconst 1).add hclass.gradient_sq_integrableOn).const_mul √n)).const_mul M |>.congr
      (Eventually.of_forall fun t ↦ by simp only [g, q, b2, Pi.add_apply])
  have hmeas : AEStronglyMeasurable (weakMomentumSlice nse u p (sliceGradient u) φ)
      (volume.restrict (Set.Ioc 0 T)) := by
    have hIoo : (volume.restrict (Set.Ioc (0 : ℝ) T)) = volume.restrict (Set.Ioo 0 T) :=
      Measure.restrict_congr_set Ioo_ae_eq_Ioc |>.symm
    rw [hIoo]
    have hA := (continuousOn_integral_partialDeriv_inner hu hφ.1 hφ.2.1 (T := T)).neg
    refine (hA.aestronglyMeasurable measurableSet_Ioo).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with τ hτ
    exact (weakMomentumSlice_sliceGradient_eq hu hp hdiv hmom hφ.1 hφ.2.1 hτ).symm
  rw [IntegrableOn, hIoc]
  refine Integrable.mono' hg hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have hb : (eLpNorm (fderiv ℝ (velocitySlice u t)) 2 volume).toReal ≤ 1 + b2 t := by
    simp only [b2]
    nlinarith [sq_nonneg ((eLpNorm (fderiv ℝ (velocitySlice u t)) 2 volume).toReal - 1)]
  have hD := (toReal_eLpNorm_sliceGradient_le hclass ht).trans
    (mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _))
  have hu2 := hB t ht
  rw [Real.norm_eq_abs]
  refine (hM u p (sliceGradient u) t (hclass.velocity_memLp t ht)
    (hclass.pressure_memLp t ⟨ht.1.le, ht.2⟩)
    (memLp_sliceGradient_of_classicalEnergyClass hclass ⟨ht.1.le, ht.2⟩)).trans ?_
  apply mul_le_mul_of_nonneg_left _ hM0
  have hu0 : 0 ≤ (eLpNorm (velocitySlice u t) 2 volume).toReal := ENNReal.toReal_nonneg
  have hsq : (eLpNorm (velocitySlice u t) 2 volume).toReal ^ 2 ≤ B ^ 2 :=
    pow_le_pow_left₀ hu0 hu2 2
  simp only [q]
  linarith

/-- The weak momentum equation of a classical energy-class solution whose velocity slices
converge in `L²` to the initial datum. -/
theorem integral_weakMomentumSlice_sliceGradient_eq_initial (hforce : nse.forcing = 0)
    (hu : ∀ z ∈ finiteTimeDomain n T, ContDiffAt ℝ 2 u z)
    (hp : ∀ z ∈ finiteTimeDomain n T, ContDiffAt ℝ 1 p z)
    (hdiv : ∀ z ∈ finiteTimeDomain n T, DivergenceFreeAt u z)
    (hmom : ∀ z ∈ finiteTimeDomain n T, MomentumEquationAt nse u p z)
    (hclass : ClassicalEnergyClass u p T) (hu₀ : MemLp nse.initialVelocity 2 volume)
    (htrace : Tendsto (fun t ↦ eLpNorm (velocitySlice u t - nse.initialVelocity) 2 volume)
      (𝓝[>] 0) (𝓝 0))
    (hφ : IncompressibleFlow.IsWeakMomentumTest T φ) :
    ∫ τ in Set.Icc 0 T, weakMomentumSlice nse u p (sliceGradient u) φ τ =
      initialVelocityTestPairing nse.toInitialValueData (fun x ↦ φ (timeSpaceCons 0 x)) := by
  have hT := hclass.time_pos
  have hWint := integrableOn_weakMomentumSlice_sliceGradient hforce hu hp hdiv hmom hclass hφ
  have hWi (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
      IntervalIntegrable (weakMomentumSlice nse u p (sliceGradient u) φ) volume a b := by
    apply IntegrableOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact hWint.mono_set (Set.Icc_subset_Icc ha hb)
  have hFcont : ContinuousOn (fun t ↦ ∫ τ in (0 : ℝ)..t,
      weakMomentumSlice nse u p (sliceGradient u) φ τ) (Set.Icc 0 T) := by
    have h := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := 0) (b := T)
      (f := weakMomentumSlice nse u p (sliceGradient u) φ) (by rwa [Set.uIcc_of_le hT.le])
    rwa [Set.uIcc_of_le hT.le] at h
  have hφcont : Continuous φ := hφ.1.continuous
  have hPlim0 : Tendsto (fun t ↦ ∫ x, inner ℝ (u (timeSpaceCons t x)) (φ (timeSpaceCons t x)))
      (𝓝[>] 0) (𝓝 (initialVelocityTestPairing nse.toInitialValueData
        (fun x ↦ φ (timeSpaceCons 0 x)))) :=
    PDE.Analysis.tendsto_integral_inner_of_tendsto_eLpNorm (v := fun t ↦ velocitySlice u t)
      (w := nse.initialVelocity) (ψ := fun t x ↦ φ (timeSpaceCons t x))
      (ψ₀ := fun x ↦ φ (timeSpaceCons 0 x))
      (by filter_upwards [Ioc_mem_nhdsGT hT] with t ht using hclass.velocity_memLp t ht) hu₀
      (Eventually.of_forall fun t ↦ hφ.spatialSlice_memLp t) (hφ.spatialSlice_memLp 0) htrace
      ((PDE.Analysis.tendsto_eLpNorm_timeSlice_sub hφcont hφ.2.1 0).mono_left
        nhdsWithin_le_nhds)
  have hPlimT : Tendsto (fun t ↦ ∫ x, inner ℝ (u (timeSpaceCons t x)) (φ (timeSpaceCons t x)))
      (𝓝[<] T) (𝓝 0) := by
    have hvel : Tendsto (fun t ↦ eLpNorm (velocitySlice u t - velocitySlice u T) 2 volume)
        (𝓝[<] T) (𝓝 0) := by
      rw [← nhdsWithin_Ioo_eq_nhdsLT hT]
      exact (hclass.tendsto_velocity T ⟨hT, le_rfl⟩).mono_left
        (nhdsWithin_mono _ Set.Ioo_subset_Ioc_self)
    have h := PDE.Analysis.tendsto_integral_inner_of_tendsto_eLpNorm
      (v := fun t ↦ velocitySlice u t) (w := velocitySlice u T)
      (ψ := fun t x ↦ φ (timeSpaceCons t x)) (ψ₀ := fun x ↦ φ (timeSpaceCons T x))
      (by filter_upwards [Ioo_mem_nhdsLT hT] with t ht using
        hclass.velocity_memLp t ⟨ht.1, ht.2.le⟩)
      (hclass.velocity_memLp T ⟨hT, le_rfl⟩)
      (Eventually.of_forall fun t ↦ hφ.spatialSlice_memLp t) (hφ.spatialSlice_memLp T) hvel
      ((PDE.Analysis.tendsto_eLpNorm_timeSlice_sub hφcont hφ.2.1 T).mono_left
        nhdsWithin_le_nhds)
    simpa [hφ.2.2, velocitySlice] using h
  have hFt : ∀ t ∈ Set.Ioo 0 T, (∫ τ in (0 : ℝ)..t,
      weakMomentumSlice nse u p (sliceGradient u) φ τ) =
        initialVelocityTestPairing nse.toInitialValueData (fun x ↦ φ (timeSpaceCons 0 x)) -
          ∫ x, inner ℝ (u (timeSpaceCons t x)) (φ (timeSpaceCons t x)) := by
    intro t ht
    have hF0 : Tendsto (fun s ↦ ∫ τ in (0 : ℝ)..s,
        weakMomentumSlice nse u p (sliceGradient u) φ τ) (𝓝[>] 0) (𝓝 0) := by
      have h := (hFcont 0 ⟨le_rfl, hT.le⟩).tendsto
      rw [intervalIntegral.integral_same] at h
      rw [← nhdsWithin_Ioo_eq_nhdsGT hT]
      exact h.mono_left (nhdsWithin_mono _ Set.Ioo_subset_Icc_self)
    have hlim1 := hF0.const_sub (∫ τ in (0 : ℝ)..t,
      weakMomentumSlice nse u p (sliceGradient u) φ τ)
    rw [sub_zero] at hlim1
    refine tendsto_nhds_unique hlim1 ((hPlim0.sub_const _).congr' ?_)
    filter_upwards [Ioo_mem_nhdsGT ht.1] with s hs
    rw [intervalIntegral.integral_interval_sub_left (hWi 0 t le_rfl ht.1.le ht.2.le)
        (hWi 0 s le_rfl hs.1.le (hs.2.trans ht.2).le),
      intervalIntegral_weakMomentumSlice_sliceGradient hu hp hdiv hmom hφ.1 hφ.2.1 hs.1
        hs.2.le ht.2]
  have hFT : (∫ τ in (0 : ℝ)..T, weakMomentumSlice nse u p (sliceGradient u) φ τ) =
      initialVelocityTestPairing nse.toInitialValueData (fun x ↦ φ (timeSpaceCons 0 x)) := by
    have hlim1 : Tendsto (fun t ↦ ∫ τ in (0 : ℝ)..t,
        weakMomentumSlice nse u p (sliceGradient u) φ τ) (𝓝[<] T)
        (𝓝 (∫ τ in (0 : ℝ)..T, weakMomentumSlice nse u p (sliceGradient u) φ τ)) := by
      have h := (hFcont T ⟨hT.le, le_rfl⟩).tendsto
      rw [← nhdsWithin_Ioo_eq_nhdsLT hT]
      exact h.mono_left (nhdsWithin_mono _ Set.Ioo_subset_Icc_self)
    have hlim2 := (hPlimT.const_sub (initialVelocityTestPairing nse.toInitialValueData
      (fun x ↦ φ (timeSpaceCons 0 x))))
    rw [sub_zero] at hlim2
    refine tendsto_nhds_unique hlim1 (hlim2.congr' ?_)
    filter_upwards [Ioo_mem_nhdsLT hT] with t ht
    exact (hFt t ht).symm
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT.le]
  exact hFT

/-- At times in `(0,T)` the velocity slices of a classical solution are distributionally
divergence free. -/
theorem distributionallyDivergenceFree_velocitySlice_of_mem_Ioo
    (hu : ∀ z ∈ finiteTimeDomain n T, ContDiffAt ℝ 2 u z)
    (hdiv : ∀ z ∈ finiteTimeDomain n T, DivergenceFreeAt u z)
    (hclass : ClassicalEnergyClass u p T) {t : ℝ} (ht : t ∈ Set.Ioo 0 T) :
    DistributionallyDivergenceFree (velocitySlice u t) := by
  have hz := timeSpaceCons_mem_finiteTimeDomain (n := n) ht
  refine SpatialFieldDivergenceFree.distributionallyDivergenceFree (fun x ↦ ?_)
    (hclass.slice_contDiff t ⟨ht.1, ht.2.le⟩)
  rw [spatialFieldDivergence_velocitySlice t x ((hu _ (hz x)).differentiableAt (by norm_num))]
  exact hdiv _ (hz x)

/-- The velocity slices of a classical energy-class solution are distributionally divergence
free on `[0,T]` when the time-zero slice is. At `T` this is an `L²` limit. -/
theorem distributionallyDivergenceFree_velocitySlice_of_classical
    (hu : ∀ z ∈ finiteTimeDomain n T, ContDiffAt ℝ 2 u z)
    (hdiv : ∀ z ∈ finiteTimeDomain n T, DivergenceFreeAt u z)
    (hclass : ClassicalEnergyClass u p T)
    (h0 : DistributionallyDivergenceFree (velocitySlice u 0)) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    DistributionallyDivergenceFree (velocitySlice u t) := by
  have hT := hclass.time_pos
  rcases ht.1.eq_or_lt with h | h
  · subst h
    exact h0
  rcases ht.2.lt_or_eq with h' | h'
  · exact distributionallyDivergenceFree_velocitySlice_of_mem_Ioo hu hdiv hclass ⟨h, h'⟩
  subst h'
  apply DistributionallyDivergenceFree.of_tendsto_eLpNorm (l := 𝓝[<] t)
    (v := fun k ↦ velocitySlice u k)
  · filter_upwards [Ioo_mem_nhdsLT hT] with k hk using
      distributionallyDivergenceFree_velocitySlice_of_mem_Ioo hu hdiv hclass hk
  · filter_upwards [Ioo_mem_nhdsLT hT] with k hk using hclass.velocity_memLp k ⟨hk.1, hk.2.le⟩
  · exact hclass.velocity_memLp t ⟨hT, le_rfl⟩
  · rw [← nhdsWithin_Ioo_eq_nhdsLT hT]
    exact (hclass.tendsto_velocity t ⟨hT, le_rfl⟩).mono_left
      (nhdsWithin_mono _ Set.Ioo_subset_Ioc_self)

/-- A datum is square integrable when the velocity slices of an energy-class field converge to
it in `L²`. -/
theorem memLp_of_tendsto_velocitySlice {u₀ : ℝ^n → ℝ^n} (hclass : ClassicalEnergyClass u p T)
    (htrace : Tendsto (fun t ↦ eLpNorm (velocitySlice u t - u₀) 2 volume) (𝓝[>] 0) (𝓝 0)) :
    MemLp u₀ 2 volume := by
  have h1 := htrace.eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < 1 from one_pos))
  obtain ⟨t, h1t, h2t⟩ := (h1.and (Ioc_mem_nhdsGT hclass.time_pos)).exists
  have hdiff : MemLp (velocitySlice u t - u₀) 2 volume := h1t.trans ENNReal.one_lt_top
  simpa using (hclass.velocity_memLp t h2t).sub hdiff

end Slab

/-- A classical solution of the unforced Navier–Stokes equations on the open slab, in the
energy class and with an `L²` initial trace, as a pressure-retaining weak solution whose weak
gradient is the slice gradient. -/
def classicalPressureWeakSolution (nse : Problem n) (hforce : nse.forcing = 0)
    (u : ℝ^(n + 1) → ℝ^n) (p : ℝ^(n + 1) → ℝ) (T : ℝ)
    (hu : ∀ z ∈ finiteTimeDomain n T, ContDiffAt ℝ 2 u z)
    (hp : ∀ z ∈ finiteTimeDomain n T, ContDiffAt ℝ 1 p z)
    (hdiv : ∀ z ∈ finiteTimeDomain n T, DivergenceFreeAt u z)
    (hmom : ∀ z ∈ finiteTimeDomain n T, MomentumEquationAt nse u p z)
    (hclass : ClassicalEnergyClass u p T)
    (hinit : ∀ x, u (timeSpaceCons 0 x) = nse.initialVelocity x)
    (htrace : Tendsto (fun t ↦ eLpNorm (velocitySlice u t - nse.initialVelocity) 2 volume)
      (𝓝[>] 0) (𝓝 0)) :
    PressureWeakSolution nse :=
  have h0 : velocitySlice u 0 = nse.initialVelocity := funext hinit
  have hu₀ : MemLp nse.initialVelocity 2 volume := memLp_of_tendsto_velocitySlice hclass htrace
  have hvel : ∀ {t : ℝ}, t ∈ Set.Icc 0 T → MemLp (velocitySlice u t) 2 volume := fun ht ↦
    memLp_velocitySlice_of_classicalEnergyClass hclass (by rw [h0]; exact hu₀) ht
  { u := u
    p := p
    Du := sliceGradient u
    T := ⟨T, hclass.time_pos⟩
    initialVelocity_memLp := hu₀
    velocity_memLp_at := hvel
    gradient_memLp_at := fun ht ↦ memLp_spatialGradientSlice_sliceGradient ht.1
      (hclass.slice_contDiff _ ht) (hclass.gradient_memLp _ ht)
    hasWeakSpatialDerivative := fun ht i j ↦
      hasWeakDerivativeOn_sliceGradient ht.1 (hclass.slice_contDiff _ ht) i j
    pressure_memLp_at := fun ht ↦ hclass.pressure_memLp _ ht
    force_memLp_at := fun _ ↦ by
      simp only [hforce]
      exact MemLp.zero'
    weak_momentum_integrable_on := fun φ hφ ↦
      ⟨fun t ht ↦ integrable_weakMomentumIntegrand hforce (hvel ht) (hclass.pressure_memLp t ht)
        (memLp_sliceGradient_of_classicalEnergyClass hclass ht) hφ,
        integrableOn_weakMomentumSlice_sliceGradient hforce hu hp hdiv hmom hclass hφ⟩
    weak_momentum_eq := fun φ hφ ↦ integral_weakMomentumSlice_sliceGradient_eq_initial hforce
      hu hp hdiv hmom hclass hu₀ htrace hφ
    distributionallyDivergenceFree_at := fun ht ↦
      distributionallyDivergenceFree_velocitySlice_of_classical hu hdiv hclass
        (by rw [h0]; exact nse.initialVelocity_distributionallyDivergenceFree) ht }

end NavierStokes
