/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Euler.Axisymmetric.CylinderStreamSeries
public import PDE.Fluid.Euler.Axisymmetric.CylinderStream
public import PDE.Fluid.Euler.Axisymmetric.CylinderProfiles
public import PDE.FDeriv.Laplacian.Meridian
public import PDE.Fluid.Axisymmetric.AxisRegularDiffusion
import Mathlib.Analysis.PSeries

/-!
# Existence of the stream function in the cylinder

For a smooth vorticity profile `Ω(s, z)`, `s = r²`, odd and `L`-periodic in `z`, the stream
profile

```text
Ψ(s, z) = ∑_{k ≥ 1} η_k(s) Ψ_k(s) sin(μ_k z),     μ_k = 2πk / L,
```

with `Ψ_k` the mode solution of `4 s Ψ_k'' + 8 Ψ_k' - μ_k² Ψ_k = -F_k` for the sine coefficients
`F_k` of `Ω(s, ·)` and `η_k` the mode cutoffs, is smooth on the whole plane
(`contDiff_streamProfile`), odd and periodic in `z`, vanishes at `s = 1`, and solves the reduced
equation `-(8 Ψ_s + 4 s Ψ_ss + Ψ_zz) = Ω` on `0 < s < 1` (`streamProfile_equation`). Then
`φ(r, z) = r Ψ(r², z)` is a stream function of `ω^θ(r, z) = r Ω(r², z)` in the sense of
`IsStreamFunction`, smooth on the whole meridian plane, odd in `r` and in `z`
(`exists_isStreamFunction`). By `IsStreamFunction.eqOn` it is the only stream function on the closed
strip.

So the stream function is axis regular (`φ = r Ψ(r², z)` with `Ψ` smooth in `s` across `s = 0`)
and `C^∞` up to and across the wall: the regularity required of the stream function of the
meridian system by `HasWallRegularityOn`, and the spatial regularity required of the stream
profile by `ProfileSolution`. Smooth dependence on time is a separate statement.

## Main definitions

* `streamProfile`: the series `Ψ`.
* `meridianStream`: `φ(r, z) = r Ψ(r², z)`.

## Main results

* `contDiff_streamProfile`, `streamProfile_equation`, `streamProfile_wall`,
  `streamProfile_periodic`, `streamProfile_odd`.
* `exists_isStreamFunction`: existence, axis regularity and wall regularity of the stream
  function.
* `exists_isStreamFunction_of_vanishing_near_axis`: the same for angular vorticities given on
  the meridian plane and vanishing near the axis.
* `exists_periodic_extension`: periodic extension of profiles supported in a strip.

## How it works

We sum the series term by term. Each mode is smooth, with derivatives of order `n` bounded by
`D n / (1 + k)²` on the whole plane (`exists_streamMode_bounds`), so Mathlib's `contDiff_tsum` makes
`Ψ` smooth and its derivatives are the sums of those of the modes (`iteratedFDeriv_streamProfile`).
On `0 < s < 1` the cutoff `η_k` is one (`modeTerm_eventuallyEq`), so each mode solves its mode
equation times `sin(μ_k z)` (`streamMode_equation`), and the sine series of the odd periodic
function `Ω(s, ·)` (`PDE.Analysis.Fourier.SineSeries.hasSum_sineCoeff_mul_sin`) sums the right sides
to `Ω` (`streamProfile_equation`). The change of variables `s = r²` turns the reduced equation into
the stream function equation (6.3) for `φ = r Ψ(r², z)` (`streamOperator_meridianStream`).

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 6, (6.3)-(6.4).
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

open PDE (laplacian partialDeriv)

namespace Euler.Cylinder

open Set Filter EuclideanSpace
open AxisymmetricFlow (squaredRadiusMap contDiff_squaredRadiusMap)
open scoped Topology

set_option linter.missingDocs true

noncomputable section

/-- A series `D / (1 + k)²` is summable. -/
theorem summable_div_one_add_sq (D : ℝ) : Summable fun k : ℕ ↦ D / (1 + (k : ℝ)) ^ 2 := by
  have h : Summable (fun n : ℕ ↦ 1 / (n : ℝ) ^ 2) := Real.summable_one_div_nat_pow.2 (by norm_num)
  have h1 := (summable_nat_add_iff 1).2 h
  convert h1.mul_left D using 1
  funext k
  push_cast
  ring

/-- The stream profile `Ψ(s, z) = ∑ₖ η_k(s) Ψ_k(s) sin(μ_k z)` of the vorticity profile `Ω`. -/
def streamProfile (L : ℝ) (Ω : ℝ × ℝ → ℝ) (p : ℝ^2) : ℝ :=
  ∑' k, streamMode L Ω k p

section Profile

variable {L : ℝ} {Ω : ℝ × ℝ → ℝ}

/-- Uniform summable bounds for the derivatives of the stream modes. -/
theorem exists_streamMode_bounds (hL : 0 < L) (hΩ : ContDiff ℝ (⊤ : ℕ∞) Ω)
    (hper : ∀ s z, Ω (s, z + L) = Ω (s, z)) :
    ∃ D : ℕ → ℝ, ∀ n k p, ‖iteratedFDeriv ℝ n (streamMode L Ω k) p‖ ≤ D n / (1 + k) ^ 2 := by
  choose D hD using exists_norm_iteratedFDeriv_streamMode_le hL hΩ hper
  exact ⟨D, hD⟩

/-- **The stream profile is smooth.** -/
theorem contDiff_streamProfile (hL : 0 < L) (hΩ : ContDiff ℝ (⊤ : ℕ∞) Ω)
    (hper : ∀ s z, Ω (s, z + L) = Ω (s, z)) :
    ContDiff ℝ (⊤ : ℕ∞) (streamProfile L Ω) := by
  obtain ⟨D, hD⟩ := exists_streamMode_bounds hL hΩ hper
  exact contDiff_tsum (fun k ↦ contDiff_streamMode hL hΩ k)
    (fun n _ ↦ summable_div_one_add_sq (D n)) (fun n k p _ ↦ hD n k p)

/-- Derivatives of the stream profile are the sums of the derivatives of the modes. -/
theorem iteratedFDeriv_streamProfile (hL : 0 < L) (hΩ : ContDiff ℝ (⊤ : ℕ∞) Ω)
    (hper : ∀ s z, Ω (s, z + L) = Ω (s, z)) (n : ℕ) (p : ℝ^2) :
    iteratedFDeriv ℝ n (streamProfile L Ω) p = ∑' k, iteratedFDeriv ℝ n (streamMode L Ω k) p := by
  obtain ⟨D, hD⟩ := exists_streamMode_bounds hL hΩ hper
  exact iteratedFDeriv_tsum_apply (fun k ↦ contDiff_streamMode hL hΩ k)
    (fun n _ ↦ summable_div_one_add_sq (D n)) (fun n k p _ ↦ hD n k p)
    (by exact_mod_cast le_top) p

/-- The iterated derivatives of the modes at a point are summable. -/
theorem summable_iteratedFDeriv_streamMode (hL : 0 < L) (hΩ : ContDiff ℝ (⊤ : ℕ∞) Ω)
    (hper : ∀ s z, Ω (s, z + L) = Ω (s, z)) (n : ℕ) (p : ℝ^2) :
    Summable fun k ↦ iteratedFDeriv ℝ n (streamMode L Ω k) p := by
  obtain ⟨D, hD⟩ := exists_streamMode_bounds hL hΩ hper
  exact (summable_div_one_add_sq (D n)).of_norm_bounded fun k ↦ hD n k p

/-- A function of one planar coordinate is differentiable where the function is. -/
theorem differentiableAt_comp_coord {g : ℝ → ℝ} {i : Fin 2} {q : ℝ^2}
    (hg : DifferentiableAt ℝ g (q i)) : DifferentiableAt ℝ (fun p : ℝ^2 ↦ g (p i)) q :=
  hg.comp q (proj i : ℝ^2 →L[ℝ] ℝ).differentiableAt

/-- A function of one planar coordinate has the derivative of the function in that coordinate. -/
theorem partialDeriv_comp_coord_self {g : ℝ → ℝ} {i : Fin 2} {q : ℝ^2}
    (hg : DifferentiableAt ℝ g (q i)) :
    (∂[i] (fun p : ℝ^2 ↦ g (p i))) q = deriv g (q i) := by
  have hp : HasFDerivAt (fun y : ℝ^2 ↦ y i) (proj i : ℝ^2 →L[ℝ] ℝ) q :=
    (proj i : ℝ^2 →L[ℝ] ℝ).hasFDerivAt
  have h : HasFDerivAt (fun y : ℝ^2 ↦ g (y i)) (deriv g (q i) • (proj i)) q :=
    hg.hasDerivAt.comp_hasFDerivAt q hp
  rw [partialDeriv, h.fderiv]
  simp

/-- A function of one planar coordinate has zero derivative in the other coordinate. -/
theorem partialDeriv_comp_coord_ne {g : ℝ → ℝ} {i j : Fin 2} (hij : j ≠ i) {q : ℝ^2}
    (hg : DifferentiableAt ℝ g (q i)) :
    (∂[j] (fun p : ℝ^2 ↦ g (p i))) q = 0 := by
  have hp : HasFDerivAt (fun y : ℝ^2 ↦ y i) (proj i : ℝ^2 →L[ℝ] ℝ) q :=
    (proj i : ℝ^2 →L[ℝ] ℝ).hasFDerivAt
  have h : HasFDerivAt (fun y : ℝ^2 ↦ g (y i)) (deriv g (q i) • (proj i)) q :=
    hg.hasDerivAt.comp_hasFDerivAt q hp
  rw [partialDeriv, h.fderiv]
  simp [hij]

/-- The radial derivative of a planar sine term. -/
theorem partialDeriv_zero_sineTerm {a : ℝ → ℝ} (ha : Differentiable ℝ a) (μ : ℝ) :
    (∂[(0 : Fin 2)] (sineTerm a μ)) = fun q ↦ deriv a (q 0) * Real.sin (μ * q 1) := by
  funext q
  have hsin : DifferentiableAt ℝ (fun z ↦ Real.sin (μ * z)) (q 1) := by fun_prop
  unfold sineTerm
  rw [PDE.partialDeriv_mul (f := fun p : ℝ^2 ↦ a (p 0))
    (g := fun p : ℝ^2 ↦ Real.sin (μ * p 1))
    (differentiableAt_comp_coord (g := a) (i := 0) (ha (q 0)))
    (differentiableAt_comp_coord (g := fun z ↦ Real.sin (μ * z)) (i := 1) hsin),
    partialDeriv_comp_coord_self (ha (q 0)), partialDeriv_comp_coord_ne (by decide) hsin]
  ring

/-- The axial derivative of a planar sine term. -/
theorem partialDeriv_one_sineTerm {a : ℝ → ℝ} (ha : Differentiable ℝ a) (μ : ℝ) :
    (∂[(1 : Fin 2)] (sineTerm a μ)) = fun q ↦ a (q 0) * (μ * Real.cos (μ * q 1)) := by
  funext q
  have hsin : DifferentiableAt ℝ (fun z ↦ Real.sin (μ * z)) (q 1) := by fun_prop
  have hd : deriv (fun z ↦ Real.sin (μ * z)) (q 1) = μ * Real.cos (μ * q 1) := by
    have h1 : HasDerivAt (fun z : ℝ ↦ μ * z) μ (q 1) := by
      simpa using (hasDerivAt_id (q 1)).const_mul μ
    rw [h1.sin.deriv]
    ring
  unfold sineTerm
  rw [PDE.partialDeriv_mul (f := fun p : ℝ^2 ↦ a (p 0))
    (g := fun p : ℝ^2 ↦ Real.sin (μ * p 1))
    (differentiableAt_comp_coord (g := a) (i := 0) (ha (q 0)))
    (differentiableAt_comp_coord (g := fun z ↦ Real.sin (μ * z)) (i := 1) hsin),
    partialDeriv_comp_coord_ne (by decide) (ha (q 0)), partialDeriv_comp_coord_self hsin, hd]
  ring

/-- The second radial derivative of a planar sine term. -/
theorem secondPartialDeriv_zero_sineTerm {a : ℝ → ℝ} (ha : ContDiff ℝ (⊤ : ℕ∞) a) (μ : ℝ)
    (q : ℝ^2) :
    (∂[(0 : Fin 2)] (∂[(0 : Fin 2)] (sineTerm a μ))) q =
      iteratedDeriv 2 a (q 0) * Real.sin (μ * q 1) := by
  have ha1 : Differentiable ℝ a := ha.differentiable (by simp)
  have hda : Differentiable ℝ (deriv a) := by
    have := ContDiff.iterate_deriv 1 ha
    simpa using this.differentiable (by simp)
  rw [partialDeriv_zero_sineTerm ha1]
  have h := partialDeriv_zero_sineTerm hda μ
  have heq : (fun q : ℝ^2 ↦ deriv a (q 0) * Real.sin (μ * q 1)) = sineTerm (deriv a) μ := rfl
  rw [heq, h, iteratedDeriv_succ, iteratedDeriv_one]

/-- The second axial derivative of a planar sine term. -/
theorem secondPartialDeriv_one_sineTerm {a : ℝ → ℝ} (ha : Differentiable ℝ a) (μ : ℝ)
    (q : ℝ^2) :
    (∂[(1 : Fin 2)] (∂[(1 : Fin 2)] (sineTerm a μ))) q =
      -(μ ^ 2 * a (q 0) * Real.sin (μ * q 1)) := by
  rw [partialDeriv_one_sineTerm ha]
  have hcos : DifferentiableAt ℝ (fun z ↦ μ * Real.cos (μ * z)) (q 1) := by fun_prop
  have hd : deriv (fun z ↦ μ * Real.cos (μ * z)) (q 1) = -(μ ^ 2 * Real.sin (μ * q 1)) := by
    have h1 : HasDerivAt (fun z : ℝ ↦ μ * z) μ (q 1) := by
      simpa using (hasDerivAt_id (q 1)).const_mul μ
    rw [(h1.cos.const_mul μ).deriv]
    ring
  rw [PDE.partialDeriv_mul (f := fun p : ℝ^2 ↦ a (p 0))
    (g := fun p : ℝ^2 ↦ μ * Real.cos (μ * p 1))
    (differentiableAt_comp_coord (g := a) (i := 0) (ha (q 0)))
    (differentiableAt_comp_coord (g := fun z ↦ μ * Real.cos (μ * z)) (i := 1) hcos),
    partialDeriv_comp_coord_ne (by decide) (ha (q 0)), partialDeriv_comp_coord_self hcos, hd]
  ring

end Profile

section Equation

variable {L : ℝ} {Ω : ℝ × ℝ → ℝ}

/-- A coordinate derivative is the first iterated derivative on the coordinate vector. -/
theorem partialDeriv_eq_iteratedFDeriv_one (f : ℝ^2 → ℝ) (i : Fin 2) (p : ℝ^2) :
    (∂[i] f) p = iteratedFDeriv ℝ 1 f p ![single i 1] := by
  rw [iteratedFDeriv_one_apply]
  rfl

/-- The coordinate derivatives of the stream profile are the sums of those of the modes. -/
theorem hasSum_partialDeriv_streamMode (hL : 0 < L) (hΩ : ContDiff ℝ (⊤ : ℕ∞) Ω)
    (hper : ∀ s z, Ω (s, z + L) = Ω (s, z)) (i : Fin 2) (p : ℝ^2) :
    HasSum (fun k ↦ (∂[i] (streamMode L Ω k)) p) ((∂[i] (streamProfile L Ω)) p) := by
  simp only [partialDeriv_eq_iteratedFDeriv_one]
  rw [iteratedFDeriv_streamProfile hL hΩ hper]
  exact ContinuousMultilinearMap.hasSum_eval
    (summable_iteratedFDeriv_streamMode hL hΩ hper 1 p).hasSum _

/-- The second coordinate derivatives of the stream profile are the sums of those of the
modes. -/
theorem hasSum_secondPartialDeriv_streamMode (hL : 0 < L) (hΩ : ContDiff ℝ (⊤ : ℕ∞) Ω)
    (hper : ∀ s z, Ω (s, z + L) = Ω (s, z)) (i : Fin 2) (p : ℝ^2) :
    HasSum (fun k ↦ (∂[i] (∂[i] (streamMode L Ω k))) p)
      ((∂[i] (∂[i] (streamProfile L Ω))) p) := by
  have hmode : ∀ k, (∂[i] (∂[i] (streamMode L Ω k))) p =
      iteratedFDeriv ℝ 2 (streamMode L Ω k) p ![single i 1, single i 1] := fun k ↦
    PDE.secondPartialDeriv_eq_iteratedFDeriv_apply i i
      ((contDiff_streamMode hL hΩ k).contDiffAt.of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  have hsum : (∂[i] (∂[i] (streamProfile L Ω))) p =
      iteratedFDeriv ℝ 2 (streamProfile L Ω) p ![single i 1, single i 1] :=
    PDE.secondPartialDeriv_eq_iteratedFDeriv_apply i i
      ((contDiff_streamProfile hL hΩ hper).contDiffAt.of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  simp only [hmode, hsum]
  rw [iteratedFDeriv_streamProfile hL hΩ hper]
  exact ContinuousMultilinearMap.hasSum_eval
    (summable_iteratedFDeriv_streamMode hL hΩ hper 2 p).hasSum _

/-- The reduced operator of one stream mode on the open strip. -/
theorem streamMode_equation (hL : 0 < L) (hΩ : ContDiff ℝ (⊤ : ℕ∞) Ω) (k : ℕ) {p : ℝ^2}
    (hp : p 0 ∈ Ioo (0 : ℝ) 1) :
    8 * (∂[(0 : Fin 2)] (streamMode L Ω k)) p +
        4 * p 0 * (∂[(0 : Fin 2)] (∂[(0 : Fin 2)] (streamMode L Ω k))) p +
        (∂[(1 : Fin 2)] (∂[(1 : Fin 2)] (streamMode L Ω k))) p =
      -(coefficientMode L Ω k (p 0) * Real.sin (modeFrequency L k * p 1)) := by
  set μ := modeFrequency L k
  set F := coefficientMode L Ω k
  have hμ : 0 < μ := modeFrequency_pos hL k
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := contDiff_coefficientMode hΩ k
  have ha : ContDiff ℝ (⊤ : ℕ∞) (modeTerm μ F) := contDiff_modeTerm hμ hF
  have heq := modeTerm_eventuallyEq (μ := μ) (F := F) hp
  have hd1 : deriv (modeTerm μ F) (p 0) = deriv (modeSolution μ F) (p 0) := heq.deriv_eq
  have hd2 : iteratedDeriv 2 (modeTerm μ F) (p 0) = iteratedDeriv 2 (modeSolution μ F) (p 0) :=
    heq.iteratedDeriv_eq 2
  have hd0 : modeTerm μ F (p 0) = modeSolution μ F (p 0) := heq.eq_of_nhds
  have hmode := modeSolution_equation hμ hF (s := p 0) (by
    have : -4 / μ ^ 2 < 0 := div_neg_of_neg_of_pos (by norm_num) (by positivity)
    linarith [hp.1])
  simp only [streamMode]
  rw [secondPartialDeriv_zero_sineTerm ha, secondPartialDeriv_one_sineTerm
      (ha.differentiable (by simp)), partialDeriv_zero_sineTerm (ha.differentiable (by simp))]
  simp only
  rw [hd1, hd2, hd0]
  linear_combination Real.sin (μ * p 1) * hmode

/-- **The stream profile solves the reduced equation** `-(8 Ψ_s + 4 s Ψ_ss + Ψ_zz) = Ω` on the
open strip `0 < s < 1`, for `Ω` smooth, odd and `L`-periodic in `z`. -/
theorem streamProfile_equation (hL : 0 < L) (hΩ : ContDiff ℝ (⊤ : ℕ∞) Ω)
    (hper : ∀ s z, Ω (s, z + L) = Ω (s, z)) (hodd : ∀ s z, Ω (s, -z) = -Ω (s, z)) {p : ℝ^2}
    (hp : p 0 ∈ Ioo (0 : ℝ) 1) :
    8 * (∂[(0 : Fin 2)] (streamProfile L Ω)) p +
        4 * p 0 * (∂[(0 : Fin 2)] (∂[(0 : Fin 2)] (streamProfile L Ω))) p +
        (∂[(1 : Fin 2)] (∂[(1 : Fin 2)] (streamProfile L Ω))) p =
      -Ω (p 0, p 1) := by
  have h0 := hasSum_partialDeriv_streamMode hL hΩ hper 0 p
  have h00 := hasSum_secondPartialDeriv_streamMode hL hΩ hper 0 p
  have h11 := hasSum_secondPartialDeriv_streamMode hL hΩ hper 1 p
  have htot := ((h0.mul_left 8).add (h00.mul_left (4 * p 0))).add h11
  -- The sine series of `Ω(s, ·)`.
  set g : ℝ → ℝ := fun z ↦ Ω (p 0, z)
  have hg : ContDiff ℝ 2 g :=
    (hΩ.comp (contDiff_const.prodMk contDiff_id)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hgper : Function.Periodic g L := fun z ↦ hper (p 0) z
  have hgodd : ∀ z, g (-z) = -g z := fun z ↦ hodd (p 0) z
  have hser := PDE.Analysis.Fourier.SineSeries.hasSum_sineCoeff_mul_sin hL hg hgper hgodd (p 1)
  have hser' : HasSum (fun k : ℕ ↦ coefficientMode L Ω k (p 0) *
      Real.sin (modeFrequency L k * p 1)) (Ω (p 0, p 1)) := by
    have := (hasSum_nat_add_iff' 1).2 hser
    simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, mul_zero, zero_div,
      zero_mul, Real.sin_zero, sub_zero] at this
    convert this using 2 with k
    · simp only [coefficientMode, modeFrequency, g]
      push_cast
      ring_nf
  have hmodes : HasSum (fun k ↦ 8 * (∂[(0 : Fin 2)] (streamMode L Ω k)) p +
      4 * p 0 * (∂[(0 : Fin 2)] (∂[(0 : Fin 2)] (streamMode L Ω k))) p +
      (∂[(1 : Fin 2)] (∂[(1 : Fin 2)] (streamMode L Ω k))) p) (-Ω (p 0, p 1)) := by
    simp only [streamMode_equation hL hΩ _ hp]
    exact hser'.neg
  exact htot.unique hmodes

/-- The stream profile is `L`-periodic in `z`. -/
theorem streamProfile_periodic (hL : 0 < L) (p : ℝ^2) :
    streamProfile L Ω (p + single 1 L) = streamProfile L Ω p := by
  unfold streamProfile
  congr 1
  funext k
  simp only [streamMode, sineTerm]
  have h1 : (p + EuclideanSpace.single (1 : Fin 2) L : ℝ^2) 0 = p 0 := by simp
  have h2 : modeFrequency L k * (p + EuclideanSpace.single (1 : Fin 2) L : ℝ^2) 1 =
      modeFrequency L k * p 1 + (k + 1) * (2 * Real.pi) := by
    simp [modeFrequency]
    field_simp
  rw [h1, h2]
  congr 1
  have := Real.sin_add_nat_mul_two_pi (modeFrequency L k * p 1) (k + 1)
  push_cast at this
  exact this

/-- The stream profile is odd in `z`. -/
theorem streamProfile_odd (p : ℝ^2) :
    streamProfile L Ω (axialReflection p) = -streamProfile L Ω p := by
  unfold streamProfile
  rw [← tsum_neg]
  congr 1
  funext k
  simp only [streamMode, sineTerm, axialReflection_apply_zero, axialReflection_apply_one,
    mul_neg, Real.sin_neg]

/-- The stream profile vanishes at the wall `s = 1`. -/
theorem streamProfile_wall {p : ℝ^2} (hp : p 0 = 1) : streamProfile L Ω p = 0 := by
  unfold streamProfile
  simp [streamMode, sineTerm, hp, modeTerm_one]

end Equation

section Meridian

variable {L : ℝ} {Ω : ℝ × ℝ → ℝ}

/-- The angular stream function `φ(r, z) = r Ψ(r², z)` of the stream profile. -/
def meridianStream (L : ℝ) (Ω : ℝ × ℝ → ℝ) (x : ℝ^2) : ℝ :=
  x 0 * streamProfile L Ω (squaredRadiusMap x)

/-- The angular vorticity `ω^θ(r, z) = r Ω(r², z)` of a vorticity profile. -/
def meridianVorticity (Ω : ℝ × ℝ → ℝ) (x : ℝ^2) : ℝ :=
  x 0 * Ω (x 0 ^ 2, x 1)

/-- The stream function is smooth on the whole meridian plane. -/
theorem contDiff_meridianStream (hL : 0 < L) (hΩ : ContDiff ℝ (⊤ : ℕ∞) Ω)
    (hper : ∀ s z, Ω (s, z + L) = Ω (s, z)) : ContDiff ℝ (⊤ : ℕ∞) (meridianStream L Ω) :=
  (proj (0 : Fin 2) : ℝ^2 →L[ℝ] ℝ).contDiff.mul
    ((contDiff_streamProfile hL hΩ hper).comp contDiff_squaredRadiusMap)

/-- The projection `(t, s, z) ↦ (s, z)` of profile space. -/
def profileProjection : ℝ^3 →L[ℝ] ℝ^2 :=
  (proj (1 : Fin 3) : ℝ^3 →L[ℝ] ℝ).smulRight (single (0 : Fin 2) (1 : ℝ)) +
    (proj (2 : Fin 3) : ℝ^3 →L[ℝ] ℝ).smulRight (single (1 : Fin 2) (1 : ℝ))

/-- The projection of the meridian profile point is the squared-radius point. -/
theorem profileProjection_meridianProfilePoint (t : ℝ) (x : ℝ^2) :
    profileProjection (meridianProfilePoint t x) = squaredRadiusMap x := by
  ext i
  fin_cases i <;> simp [profileProjection, meridianProfilePoint, profilePoint, squaredRadiusMap]

/-- The stream function is the angular stream function of the profile fields with stream
profile `Ψ(s, z)`, at every time. -/
theorem meridianStream_eq_ofProfiles (t : ℝ) :
    (fun y ↦ (ofProfiles 0 (fun q ↦ Ω (q 1, q 2))
      (streamProfile L Ω ∘ profileProjection)).streamFunction y t) = meridianStream L Ω := by
  funext y
  simp [ofProfiles, meridianStream, profileProjection_meridianProfilePoint]

/-- **The stream function solves (6.3)** on the open strip `0 < r < 1`. -/
theorem streamOperator_meridianStream (hL : 0 < L) (hΩ : ContDiff ℝ (⊤ : ℕ∞) Ω)
    (hper : ∀ s z, Ω (s, z + L) = Ω (s, z)) (hodd : ∀ s z, Ω (s, -z) = -Ω (s, z))
    {x : ℝ^2} (hx : x ∈ meridianDomain) :
    streamOperator (meridianStream L Ω) x = meridianVorticity Ω x := by
  set A := profileProjection
  set Ψ := streamProfile L Ω
  set Ω₃ : ℝ^3 → ℝ := fun q ↦ Ω (q 1, q 2)
  have hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ := contDiff_streamProfile hL hΩ hper
  have hΨ3 : ContDiffAt ℝ 2 (Ψ ∘ A) (meridianProfilePoint 0 x) :=
    (hΨ.comp A.contDiff).contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hres := streamResidual_ofProfiles (U := 0) (Ω := Ω₃) (Ψ := Ψ ∘ A) (t := 0)
    (ne_of_gt hx.1) hΨ3
  rw [meridianStream_eq_ofProfiles] at hres
  set q := meridianProfilePoint 0 x
  have hAq : A q = squaredRadiusMap x := profileProjection_meridianProfilePoint 0 x
  have hA1 : A (single (1 : Fin 3) 1) = (1 : ℝ) • single (0 : Fin 2) 1 := by
    ext i
    fin_cases i <;> simp [A, profileProjection]
  have hA2 : A (single (2 : Fin 3) 1) = (1 : ℝ) • single (1 : Fin 2) 1 := by
    ext i
    fin_cases i <;> simp [A, profileProjection]
  have hΨA : ContDiffAt ℝ 2 Ψ (A q) :=
    hΨ.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hdiff : AxisymmetricFlow.spacetimeSquaredRadiusDiffusion (Ψ ∘ A) q = -Ω₃ q := by
    unfold AxisymmetricFlow.spacetimeSquaredRadiusDiffusion
    rw [PDE.CoordinateSystems.partialDeriv_comp_clm_of_eq A hA1
        (hΨA.differentiableAt (by norm_num)),
      PDE.CoordinateSystems.secondPartialDeriv_comp_clm_of_eq A hA1 hΨA,
      PDE.CoordinateSystems.secondPartialDeriv_comp_clm_of_eq A hA2 hΨA, hAq]
    have hsr : squaredRadiusMap x 0 ∈ Ioo (0 : ℝ) 1 := by
      have h : squaredRadiusMap x 0 = x 0 ^ 2 := by simp [squaredRadiusMap]
      rw [h]
      exact ⟨pow_pos hx.1 2, by nlinarith [hx.1, hx.2]⟩
    have heq := streamProfile_equation hL hΩ hper hodd hsr
    have hq1 : q 1 = squaredRadiusMap x 0 := by
      simp [q, meridianProfilePoint, profilePoint, squaredRadiusMap]
    rw [hq1]
    have hΩq : Ω₃ q = Ω (squaredRadiusMap x 0, squaredRadiusMap x 1) := by
      simp [Ω₃, q, meridianProfilePoint, profilePoint, squaredRadiusMap]
    rw [hΩq, ← heq]
    ring
  rw [hdiff, neg_neg, sub_self, mul_zero, sub_eq_zero] at hres
  rw [hres]
  simp [ofProfiles, meridianVorticity, Ω₃, meridianProfilePoint, profilePoint]

/-- **Existence of the stream function.** For a smooth vorticity profile `Ω(s, z)`, odd and
`L`-periodic in `z`, the function `φ(r, z) = r Ψ(r², z)` built from the stream profile is a
stream function of `ω^θ(r, z) = r Ω(r², z)` in the cylinder with period `L`. -/
theorem isStreamFunction_meridianStream (hL : 0 < L) (hΩ : ContDiff ℝ (⊤ : ℕ∞) Ω)
    (hper : ∀ s z, Ω (s, z + L) = Ω (s, z)) (hodd : ∀ s z, Ω (s, -z) = -Ω (s, z)) :
    IsStreamFunction L (meridianVorticity Ω) (meridianStream L Ω) where
  contDiffAt _ _ := (contDiff_meridianStream hL hΩ hper).contDiffAt.of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  continuousOn := (contDiff_meridianStream hL hΩ hper).continuous.continuousOn
  equation _ hx := streamOperator_meridianStream hL hΩ hper hodd hx
  axis z := by simp [meridianStream]
  wall z := by
    simp only [meridianStream, meridianPoint_apply_zero, one_mul]
    exact streamProfile_wall (by simp [squaredRadiusMap])
  periodic x := by
    simp only [meridianStream]
    have h0 : axialTranslate L x 0 = x 0 := by simp [axialTranslate]
    have hsq : squaredRadiusMap (axialTranslate L x) =
        squaredRadiusMap x + single (1 : Fin 2) L := by
      ext i
      fin_cases i <;> simp [squaredRadiusMap, axialTranslate]
    rw [h0, hsq, streamProfile_periodic hL]

/-- The stream function is odd in `r`: `φ(-r, z) = -φ(r, z)`. -/
theorem meridianStream_neg_radius (x : ℝ^2) :
    meridianStream L Ω (PDE.Common.coordinateReflection 0 x) = -meridianStream L Ω x := by
  have h0 : PDE.Common.coordinateReflection (0 : Fin 2) x 0 = -x 0 :=
    PDE.Common.coordinateReflection_apply_same 0 x
  have hsq : squaredRadiusMap (PDE.Common.coordinateReflection 0 x) = squaredRadiusMap x := by
    ext i
    fin_cases i
    · simp [squaredRadiusMap]
    · simp [squaredRadiusMap]
  simp only [meridianStream, h0, hsq, neg_mul]

/-- The stream function is odd in `z`. -/
theorem meridianStream_axialReflection (x : ℝ^2) :
    meridianStream L Ω (axialReflection x) = -meridianStream L Ω x := by
  have hsq : squaredRadiusMap (axialReflection x) = axialReflection (squaredRadiusMap x) := by
    ext i
    fin_cases i <;> simp [squaredRadiusMap]
  simp only [meridianStream, axialReflection_apply_zero, hsq, streamProfile_odd, mul_neg]

/-- **Existence, uniqueness and regularity of the stream function in the cylinder.** For a
smooth vorticity profile `Ω(s, z)`, odd and `L`-periodic in `z`, the angular vorticity
`ω^θ(r, z) = r Ω(r², z)` has a stream function `φ` in the cylinder with period `L` which is
smooth on the whole meridian plane, of the axis-regular form `φ(r, z) = r Ψ(r², z)` with `Ψ`
smooth on the plane, odd in `r` and in `z`, and which agrees on the closed strip with every
other stream function of `ω^θ`. -/
theorem exists_isStreamFunction (hL : 0 < L) (hΩ : ContDiff ℝ (⊤ : ℕ∞) Ω)
    (hper : ∀ s z, Ω (s, z + L) = Ω (s, z)) (hodd : ∀ s z, Ω (s, -z) = -Ω (s, z)) :
    ∃ φ : ℝ^2 → ℝ, IsStreamFunction L (meridianVorticity Ω) φ ∧ ContDiff ℝ (⊤ : ℕ∞) φ ∧
      (∃ Ψ : ℝ^2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) Ψ ∧ ∀ x, φ x = x 0 * Ψ (squaredRadiusMap x)) ∧
      (∀ x, φ (PDE.Common.coordinateReflection 0 x) = -φ x) ∧
      (∀ x, φ (axialReflection x) = -φ x) ∧
      ∀ φ' : ℝ^2 → ℝ, IsStreamFunction L (meridianVorticity Ω) φ' →
        Set.EqOn φ' φ closedMeridianStrip :=
  ⟨meridianStream L Ω, isStreamFunction_meridianStream hL hΩ hper hodd,
    contDiff_meridianStream hL hΩ hper,
    ⟨streamProfile L Ω, contDiff_streamProfile hL hΩ hper, fun _ ↦ rfl⟩,
    meridianStream_neg_radius, meridianStream_axialReflection,
    fun _ hφ' ↦ hφ'.eqOn hL (isStreamFunction_meridianStream hL hΩ hper hodd)⟩

/-- Meridian fields whose stream function slices are `C¹` on the plane have the wall regularity
of `HasWallRegularityOn`. -/
theorem hasWallRegularityOn_of_contDiff {f : MeridianFields} {times : Set ℝ}
    (h : ∀ t ∈ times, ContDiff ℝ 1 (fun y ↦ f.streamFunction y t)) :
    HasWallRegularityOn f times :=
  fun _ _ ht ↦ (h _ ht).contDiffAt

end Meridian

section Periodization

/-- Near a point whose reduction modulo `L` lies inside `(-L/2, L/2)`, the reduction is a
translation. -/
theorem toIcoMod_eventuallyEq {L : ℝ} (hL : 0 < L) {z₀ : ℝ}
    (h : toIcoMod hL (-(L / 2)) z₀ ≠ -(L / 2)) :
    ∀ᶠ z in 𝓝 z₀, toIcoMod hL (-(L / 2)) z = z - (z₀ - toIcoMod hL (-(L / 2)) z₀) := by
  set w := toIcoMod hL (-(L / 2)) z₀
  have hw := toIcoMod_mem_Ico hL (-(L / 2)) z₀
  have hw' : -(L / 2) < w := lt_of_le_of_ne hw.1 (Ne.symm h)
  have hw'' : w < L / 2 := by have := hw.2; linarith
  obtain ⟨n, hn⟩ : ∃ n : ℤ, z₀ - w = n • L := ⟨_, self_sub_toIcoMod hL (-(L / 2)) z₀⟩
  have hopen : Ioo (z₀ - (w + L / 2)) (z₀ + (L / 2 - w)) ∈ 𝓝 z₀ :=
    isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
  filter_upwards [hopen] with z hz
  rw [toIcoMod_eq_iff]
  refine ⟨⟨by linarith [hz.1], by linarith [hz.2]⟩, n, ?_⟩
  rw [← hn]
  ring

/-- **Periodic extension.** A smooth function on `ℝ × ℝ` vanishing for `|z| ≥ a` with
`2a < L` agrees for `|z| < L - a` with the smooth `L`-periodic function
`(s, z) ↦ f (s, z mod L)`. -/
theorem exists_periodic_extension {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {L a : ℝ}
    (ha : 0 ≤ a) (haL : 2 * a < L) (hsupp : ∀ s z, a ≤ |z| → f (s, z) = 0) :
    ∃ g : ℝ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ (∀ s z, g (s, z + L) = g (s, z)) ∧
      ∀ s z, |z| < L - a → g (s, z) = f (s, z) := by
  have hL : 0 < L := by linarith
  refine ⟨fun q ↦ f (q.1, toIcoMod hL (-(L / 2)) q.2), ?_, fun s z ↦ ?_, fun s z hz ↦ ?_⟩
  · rw [contDiff_iff_contDiffAt]
    rintro ⟨s₀, z₀⟩
    by_cases h : toIcoMod hL (-(L / 2)) z₀ = -(L / 2)
    · -- Near the seam the reduction is near `±L/2`, where `f` vanishes.
      have hev : ∀ᶠ q in 𝓝 (s₀, z₀), f (q.1, toIcoMod hL (-(L / 2)) q.2) = 0 := by
        obtain ⟨n, hn⟩ : ∃ n : ℤ, z₀ - toIcoMod hL (-(L / 2)) z₀ = n • L :=
          ⟨_, self_sub_toIcoMod hL (-(L / 2)) z₀⟩
        rw [h] at hn
        have hopen : Ioo (z₀ - (L / 2 - a)) (z₀ + (L / 2 - a)) ∈ 𝓝 z₀ :=
          isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
        filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds hopen] with q hq
        apply hsupp
        have hz := hq
        simp only [Set.mem_preimage, Set.mem_Ioo] at hz
        by_cases hd : z₀ ≤ q.2
        · have : toIcoMod hL (-(L / 2)) q.2 = q.2 - n • L := by
            rw [toIcoMod_eq_iff]
            refine ⟨⟨by rw [zsmul_eq_mul] at hn ⊢; linarith, by
              rw [zsmul_eq_mul] at hn ⊢; linarith [hz.2]⟩, n, by ring⟩
          rw [this, le_abs]
          right
          rw [zsmul_eq_mul] at hn ⊢
          linarith [hz.2]
        · rw [not_le] at hd
          have : toIcoMod hL (-(L / 2)) q.2 = q.2 - (n - 1) • L := by
            rw [toIcoMod_eq_iff]
            refine ⟨⟨by rw [zsmul_eq_mul] at hn ⊢; push_cast; linarith [hz.1], by
              rw [zsmul_eq_mul] at hn ⊢; push_cast; linarith⟩, n - 1, by ring⟩
          rw [this]
          rw [zsmul_eq_mul] at hn
          rw [le_abs]
          left
          rw [zsmul_eq_mul]
          push_cast
          linarith [hz.1]
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · have hev := toIcoMod_eventuallyEq hL h
      set d := z₀ - toIcoMod hL (-(L / 2)) z₀
      have hloc : (fun q : ℝ × ℝ ↦ f (q.1, toIcoMod hL (-(L / 2)) q.2)) =ᶠ[𝓝 (s₀, z₀)]
          fun q ↦ f (q.1, q.2 - d) := by
        filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds hev] with q hq
        simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hq
        rw [hq]
      refine ContDiffAt.congr_of_eventuallyEq ?_ hloc
      exact (hf.comp (contDiff_fst.prodMk (contDiff_snd.sub contDiff_const))).contDiffAt
  · simp only [toIcoMod_add_right]
  · simp only
    by_cases hz2 : |z| < L / 2
    · rw [(toIcoMod_eq_self hL).2 ⟨by linarith [(abs_lt.1 hz2).1], by
        linarith [(abs_lt.1 hz2).2]⟩]
    · rw [not_lt] at hz2
      rw [hsupp s z (by linarith)]
      apply hsupp
      rcases le_abs'.1 hz2 with hz' | hz'
      · rcases hz'.lt_or_eq with hz' | hz'
        swap
        · rw [hz', (toIcoMod_eq_self hL).2 ⟨le_rfl, by linarith⟩, abs_neg,
            abs_of_pos (by linarith)]
          linarith
        have : toIcoMod hL (-(L / 2)) z = z + L := by
          rw [toIcoMod_eq_iff]
          refine ⟨⟨by linarith [(abs_lt.1 hz).1], by linarith⟩, -1, by simp⟩
        rw [this, le_abs]
        left
        linarith [(abs_lt.1 hz).1]
      · have : toIcoMod hL (-(L / 2)) z = z - L := by
          rw [toIcoMod_eq_iff]
          refine ⟨⟨by linarith, by linarith [(abs_lt.1 hz).2]⟩, 1, by simp⟩
        rw [this, le_abs]
        right
        linarith [(abs_lt.1 hz).2]

end Periodization

section AxisData

variable {L : ℝ}

/-- The cutoff `s ↦ 1 - χ(1 + 4 (s - r₀²/4) / r₀²)`: zero for `s ≤ r₀²/4`, one for
`s ≥ r₀²/2`. -/
def axisProfileCutoff (r₀ s : ℝ) : ℝ :=
  1 - modeStep (1 + 4 * (s - r₀ ^ 2 / 4) / r₀ ^ 2)

/-- The vorticity profile `Ω(s, z) = η(s) ω(√s, z) / √s` of an angular vorticity vanishing near
the axis. -/
def axisProfile (r₀ : ℝ) (ω : ℝ^2 → ℝ) (q : ℝ × ℝ) : ℝ :=
  axisProfileCutoff r₀ q.1 * ω (WithLp.toLp 2 ![Real.sqrt q.1, q.2]) / Real.sqrt q.1

/-- The profile of a smooth angular vorticity is smooth. -/
theorem contDiff_axisProfile {r₀ : ℝ} (hr₀ : 0 < r₀) {ω : ℝ^2 → ℝ}
    (hω : ContDiff ℝ (⊤ : ℕ∞) ω) : ContDiff ℝ (⊤ : ℕ∞) (axisProfile r₀ ω) := by
  have hvec : ∀ u v : ℝ, (WithLp.toLp 2 ![u, v] : ℝ^2) =
      u • single (0 : Fin 2) (1 : ℝ) + v • single (1 : Fin 2) 1 := by
    intro u v
    ext i
    fin_cases i <;> simp
  have hη : ContDiff ℝ (⊤ : ℕ∞) (axisProfileCutoff r₀) :=
    contDiff_const.sub (contDiff_modeStep.comp (contDiff_const.add
      ((contDiff_const.mul (contDiff_id.sub contDiff_const)).div_const _)))
  rw [contDiff_iff_contDiffAt]
  rintro ⟨s₀, z₀⟩
  by_cases hs : 0 < s₀
  · have hsqrt : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ ↦ Real.sqrt q.1) (s₀, z₀) :=
      (Real.contDiffAt_sqrt hs.ne').comp _ contDiff_fst.contDiffAt
    have hpt : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ ↦
        (WithLp.toLp 2 ![Real.sqrt q.1, q.2] : ℝ^2)) (s₀, z₀) := by
      simp only [hvec]
      exact (hsqrt.smul contDiffAt_const).add (contDiff_snd.contDiffAt.smul contDiffAt_const)
    exact ((hη.comp contDiff_fst).contDiffAt.mul (hω.contDiffAt.comp _ hpt)).div hsqrt
      (Real.sqrt_pos.2 hs).ne'
  · rw [not_lt] at hs
    have hev : axisProfile r₀ ω =ᶠ[𝓝 (s₀, z₀)] fun _ ↦ 0 := by
      have hopen : Iio (r₀ ^ 2 / 4) ∈ 𝓝 s₀ := Iio_mem_nhds (by
        have : 0 < r₀ ^ 2 / 4 := by positivity
        linarith)
      filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds hopen] with q hq
      simp only [Set.mem_preimage, Set.mem_Iio] at hq
      have hr2 : 0 < r₀ ^ 2 := by positivity
      have : axisProfileCutoff r₀ q.1 = 0 := by
        rw [axisProfileCutoff, modeStep_of_le, sub_self]
        have : 4 * (q.1 - r₀ ^ 2 / 4) / r₀ ^ 2 ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (by linarith) hr2.le
        linarith
      rw [axisProfile, this, zero_mul, zero_div]
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-- **Existence for vorticities vanishing near the axis.** A smooth angular vorticity `ω`, odd and
`L`-periodic in `z` and vanishing for `0 ≤ r < r₀`, has a stream function in the cylinder with
period `L` which is smooth on the meridian plane, of the axis-regular form `r Ψ(r², z)` with `Ψ`
smooth, odd in `r` and in `z`, and unique on the closed strip. -/
theorem exists_isStreamFunction_of_vanishing_near_axis (hL : 0 < L) {ω : ℝ^2 → ℝ}
    (hω : ContDiff ℝ (⊤ : ℕ∞) ω) (hper : ∀ x, ω (axialTranslate L x) = ω x)
    (hodd : ∀ x, ω (axialReflection x) = -ω x) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (haxis : ∀ x : ℝ^2, 0 ≤ x 0 → x 0 < r₀ → ω x = 0) :
    ∃ φ : ℝ^2 → ℝ, IsStreamFunction L ω φ ∧ ContDiff ℝ (⊤ : ℕ∞) φ ∧
      (∃ Ψ : ℝ^2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) Ψ ∧ ∀ x, φ x = x 0 * Ψ (squaredRadiusMap x)) ∧
      (∀ x, φ (PDE.Common.coordinateReflection 0 x) = -φ x) ∧
      (∀ x, φ (axialReflection x) = -φ x) ∧
      ∀ φ' : ℝ^2 → ℝ, IsStreamFunction L ω φ' → Set.EqOn φ' φ closedMeridianStrip := by
  set Ω := axisProfile r₀ ω
  have hΩ : ContDiff ℝ (⊤ : ℕ∞) Ω := contDiff_axisProfile hr₀ hω
  have hΩper : ∀ s z, Ω (s, z + L) = Ω (s, z) := by
    intro s z
    simp only [Ω, axisProfile]
    have := hper (WithLp.toLp 2 ![Real.sqrt s, z])
    have hpt : axialTranslate L (WithLp.toLp 2 ![Real.sqrt s, z]) =
        (WithLp.toLp 2 ![Real.sqrt s, z + L] : ℝ^2) := by
      ext i
      fin_cases i <;> simp [axialTranslate, add_comm]
    rw [hpt] at this
    rw [this]
  have hΩodd : ∀ s z, Ω (s, -z) = -Ω (s, z) := by
    intro s z
    simp only [Ω, axisProfile]
    have := hodd (WithLp.toLp 2 ![Real.sqrt s, z])
    have hpt : axialReflection (WithLp.toLp 2 ![Real.sqrt s, z]) =
        (WithLp.toLp 2 ![Real.sqrt s, -z] : ℝ^2) := by
      ext i
      fin_cases i <;> simp
    rw [hpt] at this
    rw [this]
    ring
  have hEq : Set.EqOn (meridianVorticity Ω) ω meridianDomain := by
    intro x hx
    have hsq : Real.sqrt (x 0 ^ 2) = x 0 := Real.sqrt_sq hx.1.le
    have hpt : (WithLp.toLp 2 ![x 0, x 1] : ℝ^2) = x := by
      ext i
      fin_cases i <;> simp
    simp only [meridianVorticity, Ω, axisProfile, hsq, hpt]
    by_cases hr : x 0 < r₀
    · rw [haxis x hx.1.le hr]
      simp
    · rw [not_lt] at hr
      have hη : axisProfileCutoff r₀ (x 0 ^ 2) = 1 := by
        have hr2 : 0 < r₀ ^ 2 := by positivity
        rw [axisProfileCutoff, modeStep_of_ge, sub_zero]
        have : 1 ≤ 4 * (x 0 ^ 2 - r₀ ^ 2 / 4) / r₀ ^ 2 := by
          rw [le_div_iff₀ hr2]
          nlinarith
        linarith
      rw [hη, one_mul]
      field_simp [hx.1.ne']
  obtain ⟨φ, hφ, hφs, hΨ, hodd_r, hodd_z, huniq⟩ := exists_isStreamFunction hL hΩ hΩper hΩodd
  refine ⟨φ, hφ.congr_vorticity hEq, hφs, hΨ, hodd_r, hodd_z, fun φ' hφ' ↦ ?_⟩
  exact huniq φ' (hφ'.congr_vorticity hEq.symm)

end AxisData

end

end Euler.Cylinder
