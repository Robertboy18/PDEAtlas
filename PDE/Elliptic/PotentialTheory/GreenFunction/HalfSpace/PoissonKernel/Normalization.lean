/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.PoissonKernel.Definitions
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import PDE.Analysis.Integration.Polar
import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.GreenKernel -- shake: keep
import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.PoissonKernel.Integrability

/-!
# Normalization of the half-space Poisson kernel

The half-space Poisson kernel has total mass one: for every `x` in the upper half-space,

`∫_{ℝ^(n-1)} 2 xₙ / (n α(n) ‖x - (y', 0)‖ⁿ) dy' = 1`,

so the Poisson extension of the constant boundary datum `1` is identically `1`. This is the identity
(34) in step 2 of the proof of Evans's §2.2.4(b), Theorem 14, whose calculation he omits.

## Main results

* `integral_distance_pow_inv_eLast`: `∫_{ℝ^(n-1)} ‖eₙ - (y', 0)‖⁻ⁿ dy' = n α(n) / 2`, where `eₙ` is
  the unit vector in the last coordinate.
* `poissonHalfSpaceExtension_one_eq_one`: `poissonHalfSpaceExtension (fun _ => 1) x = 1` for every
  `x ∈ ℝ^n₊`.
* `halfSpaceEmb_add`, `distance_smul_single_last`: the algebraic identities behind the translation
  and scaling reductions.

## How it works

We translate in the tangential variable to remove `x'` and scale `y' ↦ xₙ y'` to reduce the height
to `1`, so everything comes down to the single integral

`∫_{ℝ^(n-1)} (1 + ‖y'‖²)^{-n/2} dy' = n α(n) / 2`.

For `n ≥ 2`, polar coordinates on `ℝ^(n-1)` reduce this to `∫₀^∞ rⁿ⁻² (1 + r²)^{-n/2} dr`, which the
substitution `u = r²` turns into half of the Beta integral
`∫₀^∞ u^{a-1} (1 + u)^{-(a+b)} du = Γ(a) Γ(b) / Γ(a + b)` with `a = (n-1)/2` and `b = 1/2` (DLMF
(5.12.1) and (5.12.3)); the Gamma factors then recombine with the sphere-area normalization
`n α(n) = 2 π^{n/2} / Γ(n/2)`. The case `n = 1` is a zero-dimensional boundary integral and is
handled separately.

## Implementation notes

The Beta integral on `(0, ∞)` is derived from Mathlib's `Complex.betaIntegral` on `(0, 1)` by the
change of variables `u = x / (1 + x)`. The polar-coordinate step uses
`integral_polar_addHaar_iterated_sphereFirst` and the value `unitSphereArea` from `PDE.Analysis`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.4(b), Poisson's kernel `K`, p. 37, and step 2 of the
  proof of Theorem 14 (Poisson's formula for half-space), (34), p. 38.
  <https://doi.org/10.1090/gsm/019>
* *NIST Digital Library of Mathematical Functions*, Release 1.2.8, 2026, §5.12 (Beta Function),
  (5.12.1) and (5.12.3).
  <https://dlmf.nist.gov/5.12>
-/

@[expose] public section

namespace GreenFunction

open LaplacianEquation
open PDE.Analysis
open PotentialTheory
open MeasureTheory
open Set

section PoissonHalfSpaceNormalization

open MeasureTheory Filter Topology
open scoped BigOperators InnerProductSpace

variable {n : ℕ}

/-- The boundary parametrization preserves addition. -/
theorem halfSpaceEmb_add (y z : ℝ^(n - 1)) :
    halfSpaceEmb (n := n) (y + z) = halfSpaceEmb (n := n) y + halfSpaceEmb (n := n) z := by
  classical
  ext i
  by_cases hi : (i : ℕ) < n - 1
  · simp [halfSpaceEmb, hi]
  · simp [halfSpaceEmb, hi]

private theorem halfSpaceEmb_smul (c : ℝ) (y : ℝ^(n - 1)) :
    halfSpaceEmb (n := n) (c • y) = c • halfSpaceEmb (n := n) y := by
  classical
  ext i
  by_cases hi : (i : ℕ) < n - 1
  · simp [halfSpaceEmb, hi]
  · simp [halfSpaceEmb, hi]

private theorem integral_distance_pow_inv_translate (x : ℝ^n) (a : ℝ^(n - 1)) :
    (∫ y : ℝ^(n - 1), (dist x (halfSpaceEmb (n := n) y) ^ n)⁻¹ ∂(volume : Measure ℝ^(n - 1))) =
      ∫ y : ℝ^(n - 1),
        (dist (x - halfSpaceEmb (n := n) a) (halfSpaceEmb (n := n) y) ^ n)⁻¹
          ∂(volume : Measure ℝ^(n - 1)) := by
  rw [← integral_add_left_eq_self (μ := (volume : Measure ℝ^(n - 1)))
    (fun y ↦ (dist x (halfSpaceEmb (n := n) y) ^ n)⁻¹) a]
  congr 1 with y
  rw [dist_eq_norm, dist_eq_norm, halfSpaceEmb_add, sub_sub]


private theorem integral_distance_pow_inv_horizontal_indep (x : ℝ^n) :
    (∫ y : ℝ^(n - 1), (dist x (halfSpaceEmb (n := n) y) ^ n)⁻¹ ∂(volume : Measure ℝ^(n - 1))) =
      ∫ y : ℝ^(n - 1),
        (dist
            (x - halfSpaceEmb (n := n) (halfSpaceProj (n := n) x))
            (halfSpaceEmb (n := n) y) ^ n)⁻¹
          ∂(volume : Measure ℝ^(n - 1)) := by
  simpa using
    (integral_distance_pow_inv_translate (n := n) x (halfSpaceProj (n := n) x))

variable [Fact (0 < n)]

/-- The unit vector in the last coordinate of `ℝ^n`. -/
noncomputable def eLast : ℝ^n :=
  EuclideanSpace.single (PDE.Common.lastIndex (n := n)) (1 : ℝ)

/-- Subtracting the boundary projection leaves the vertical component. -/
theorem sub_halfSpaceEmb_halfSpaceProj_eq (x : ℝ^n) :
    x - halfSpaceEmb (n := n) (halfSpaceProj (n := n) x) =
      (x PDE.Common.lastIndex) • eLast (n := n) := by
  classical
  ext i
  by_cases hi : (i : ℕ) < n - 1
  · have : i ≠ PDE.Common.lastIndex (n := n) := fun h ↦ by simp [h, PDE.Common.lastIndex] at hi
    simp [halfSpaceEmb, halfSpaceProj, hi, eLast, this]
  · obtain rfl : i = PDE.Common.lastIndex (n := n) :=
      Fin.ext (by have := i.isLt; simp only [PDE.Common.lastIndex]; omega)
    simp [eLast, halfSpaceEmb, PDE.Common.lastIndex]


/-- Simultaneous scaling in the vertical and boundary coordinates scales distance by `|t|`. -/
theorem distance_smul_single_last (t : ℝ) (y : ℝ^(n - 1)) :
    dist (t • eLast (n := n)) (halfSpaceEmb (n := n) (t • y)) =
      |t| * dist (eLast (n := n)) (halfSpaceEmb (n := n) y) := by
  rw [dist_comm, dist_eq_norm, halfSpaceEmb_smul, ← smul_sub, norm_smul, Real.norm_eq_abs,
    dist_comm, dist_eq_norm]


private theorem integral_distance_pow_inv_scale (t : ℝ) (ht : 0 < t) :
    (∫ y : ℝ^(n - 1),
        (dist (t • eLast (n := n)) (halfSpaceEmb (n := n) y) ^ n)⁻¹
          ∂(volume : Measure ℝ^(n - 1))) =
      t⁻¹ *
        ∫ y : ℝ^(n - 1),
          (dist (eLast (n := n)) (halfSpaceEmb (n := n) y) ^ n)⁻¹
            ∂(volume : Measure ℝ^(n - 1)) := by
  have h := Measure.integral_comp_smul_of_nonneg (hR := ht.le) (volume : Measure ℝ^(n - 1))
    (fun y ↦ (dist (t • eLast (n := n)) (halfSpaceEmb (n := n) y) ^ n)⁻¹) t
  simp only [distance_smul_single_last, abs_of_pos ht, mul_pow, mul_inv, integral_const_mul,
    finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul] at h
  rw [show t ^ n = t ^ (n - 1) * t by rw [← pow_succ, Nat.sub_add_cancel (Fact.out : 0 < n)],
    mul_inv, mul_assoc] at h
  exact (mul_left_cancel₀ (by positivity) h).symm


private theorem integral_Ioi_betaPrime {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ x : ℝ in Ioi 0, x ^ (a - 1) * (1 + x) ^ (-(a + b))) =
      Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
  have hbeta :
      (∫ x : ℝ in Ioo 0 1, x ^ (a - 1) * (1 - x) ^ (b - 1)) =
        Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
    calc
      (∫ x : ℝ in Ioo 0 1, x ^ (a - 1) * (1 - x) ^ (b - 1)) =
          (Complex.betaIntegral a b).re := by
        rw [Complex.betaIntegral, intervalIntegral.integral_of_le (by norm_num),
          ← integral_Ioc_eq_integral_Ioo, ← RCLike.re_to_complex, ← integral_re]
        · refine setIntegral_congr_fun measurableSet_Ioc fun x hx ↦ ?_
          rcases hx with ⟨hx0, hx1⟩
          norm_cast
          rw [← Complex.ofReal_cpow, ← Complex.ofReal_cpow,
            RCLike.re_to_complex, Complex.re_mul_ofReal, Complex.ofReal_re]
          · linarith
          · exact hx0.le
        convert! Complex.betaIntegral_convergent (u := a) (v := b)
          (by simpa) (by simpa)
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by simp), IntegrableOn]
      _ = Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
        rw [Complex.betaIntegral_eq_Gamma_mul_div]
        · simp_rw [← Complex.ofReal_add a b, Complex.Gamma_ofReal]
          norm_cast
        all_goals simpa
  let f : ℝ → ℝ := fun u ↦ u / (1 - u)
  let f' : ℝ → ℝ := fun u ↦ 1 / (1 - u) ^ 2
  have himage : f '' Ioo (0 : ℝ) 1 = Ioi 0 := by
    refine Set.ext fun x ↦ ⟨?_, fun (hx : 0 < x) ↦ ⟨x / (1 + x), ⟨by positivity,
      (div_lt_one (by positivity)).2 (by linarith)⟩, ?_⟩⟩
    · rintro ⟨u, ⟨hu0, hu1⟩, rfl⟩
      exact div_pos hu0 (sub_pos.mpr hu1)
    · have : 1 + x ≠ 0 := by positivity
      dsimp only [f]
      field_simp
      ring
  have hderiv (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) : HasDerivWithinAt f (f' u) (Ioo 0 1) u := by
    have hne : 1 - u ≠ 0 := (sub_pos.mpr hu.2).ne'
    refine (((hasDerivAt_id u).div ((hasDerivAt_const u 1).sub (hasDerivAt_id u))
      hne).congr_deriv ?_).hasDerivWithinAt
    simp only [id_eq, Pi.sub_apply, f']
    field_simp
    ring
  have hinj : InjOn f (Ioo (0 : ℝ) 1) := fun u hu v hv huv ↦ by
    have := (div_eq_div_iff (sub_pos.mpr hu.2).ne' (sub_pos.mpr hv.2).ne').mp huv
    linarith
  rw [← himage, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj]
  refine (setIntegral_congr_fun measurableSet_Ioo fun u hu ↦ ?_).trans hbeta
  have hd : 0 < 1 - u := sub_pos.mpr hu.2
  have hd' := hd.ne'
  have hone : 1 + u / (1 - u) = (1 - u)⁻¹ := by
    field_simp
    ring
  have hpow : (1 - u) ^ (a + b) = (1 - u) ^ 2 * (1 - u) ^ (a - 1) * (1 - u) ^ (b - 1) := by
    rw [← Real.rpow_natCast (1 - u) 2, ← Real.rpow_add hd, ← Real.rpow_add hd]
    congr 1
    ring
  simp only [smul_eq_mul, f, f', abs_of_pos (by positivity : 0 < 1 / (1 - u) ^ 2), hone,
    Real.div_rpow hu.1.le hd.le, Real.inv_rpow hd.le, Real.rpow_neg hd.le, inv_inv, hpow]
  field_simp

private theorem inv_distance_pow_eLast_eq_rpow (y : ℝ^(n - 1)) :
    (dist (eLast (n := n)) (halfSpaceEmb (n := n) y) ^ n)⁻¹ =
      (1 + ‖y‖ ^ 2) ^ (-((n : ℝ) / 2)) := by
  let d := dist (eLast (n := n)) (halfSpaceEmb (n := n) y)
  have hsq : d ^ 2 = 1 + ‖y‖ ^ 2 := by
    dsimp only [d]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := (Fact.out : 0 < n); omega⟩
    have hlast : PDE.Common.lastIndex (n := m + 1) = Fin.last m :=
      Fin.ext (by simp [PDE.Common.lastIndex])
    rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
      Fin.sum_univ_castSucc]
    simp [eLast, hlast, halfSpaceEmb, add_comm]
  have hd : 0 < d := by nlinarith [dist_nonneg (x := eLast (n := n)) (y := halfSpaceEmb y)]
  rw [← hsq, ← Real.rpow_two, ← Real.rpow_mul hd.le, show 2 * -((n : ℝ) / 2) = -(n : ℝ) by ring,
    Real.rpow_neg hd.le, Real.rpow_natCast]


private theorem integral_Ioi_poisson_radial {m : ℕ} (hm : 2 ≤ m) :
    (∫ r : ℝ in Ioi 0,
      r ^ (m - 2) * (1 + r ^ 2) ^ (-((m : ℝ) / 2))) =
        Real.Gamma (((m : ℝ) - 1) / 2) * Real.Gamma (1 / 2) /
          (2 * Real.Gamma ((m : ℝ) / 2)) := by
  let a : ℝ := ((m : ℝ) - 1) / 2
  let b : ℝ := 1 / 2
  let g : ℝ → ℝ := fun x ↦ x ^ (a - 1) * (1 + x) ^ (-(a + b))
  have ha : 0 < a := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    simp only [a]
    linarith
  have hpoint (r : ℝ) (hr : r ∈ Ioi (0 : ℝ)) :
      (2 * r ^ ((2 : ℝ) - 1)) • g (r ^ (2 : ℝ)) =
        2 * (r ^ (m - 2) * (1 + r ^ 2) ^ (-((m : ℝ) / 2))) := by
    have hr0 : 0 < r := hr
    simp only [smul_eq_mul]
    dsimp [g, a, b]
    rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
    rw [← Real.rpow_mul hr0.le]
    rw [Real.rpow_two]
    have hmul :
        r * r ^ (2 * (((m : ℝ) - 1) / 2 - 1)) =
          r ^ ((m : ℝ) - 2) := by
      nth_rewrite 1 [← Real.rpow_one r]
      rw [← Real.rpow_add hr0]
      congr 1
      ring
    have hcast : (((m - 2 : ℕ) : ℝ)) = (m : ℝ) - 2 := by
      rw [Nat.cast_sub hm]
      norm_num
    have hrpow : r ^ ((m : ℝ) - 2) = r ^ (m - 2) := by
      rw [← hcast, Real.rpow_natCast]
    rw [hrpow] at hmul
    rw [show -((((m : ℝ) - 1) / 2) + 1 / 2) =
        -((m : ℝ) / 2) by ring]
    ring_nf at hmul ⊢
    rw [hmul]
  have h := (integral_comp_rpow_Ioi_of_pos (g := g) (p := 2) two_pos).trans
    (integral_Ioi_betaPrime ha (by norm_num : (0 : ℝ) < b))
  rw [setIntegral_congr_fun measurableSet_Ioi hpoint, integral_const_mul] at h
  simp only [a, b, show ((m : ℝ) - 1) / 2 + 1 / 2 = (m : ℝ) / 2 by ring] at h
  rw [mul_comm 2 (Real.Gamma _), ← div_div, ← h]
  ring

/--
The inverse `n`th-power boundary-distance integral at unit height is half the
surface-area normalization `n * unitBallVolume n`.

For `n ≥ 2`, polar coordinates reduce the integral to
`∫₀∞ r^(n-2) (1+r²)^(-n/2) dr`. The substitution `u = r²` and Mathlib's Beta
integral evaluate the radial factor. The case `n = 1` is the zero-dimensional
boundary integral.
-/
theorem integral_distance_pow_inv_eLast :
    (∫ y : ℝ^(n - 1),
      (dist (eLast (n := n))
        (halfSpaceEmb (n := n) y) ^ n)⁻¹) =
      (n : ℝ) * unitBallVolume n / 2 := by
  by_cases hnOne : n = 1
  · subst n
    let _ : IsEmpty (Fin (1 - 1)) := ⟨fun i ↦ by
      have hi := i.isLt
      norm_num at hi⟩
    rw [volume_euclideanSpace_eq_dirac]
    simp [eLast, PDE.Common.lastIndex, halfSpaceEmb, dist_eq_norm,
      EuclideanSpace.norm_eq, unitBallVolume_one]
  · have hnPos : 0 < n := Fact.out
    have hn : 2 ≤ n := by omega
    let _ : Fact (0 < n - 1) := ⟨by omega⟩
    let _ : Nonempty (Fin (n - 1)) := ⟨⟨0, by omega⟩⟩
    rw [integral_polar_addHaar_iterated_sphereFirst _ _ (integrable_inv_distance_pow (n := n) eLast
      (by simp [SobolevSpace.HalfSpace.upper, eLast, PDE.Common.lastIndex]))]
    have hradial (ω : Metric.sphere (0 : ℝ^(n - 1)) 1) :
        (∫ r in Ioi (0 : ℝ), r ^ (Module.finrank ℝ ℝ^(n - 1) - 1) •
          (dist (eLast (n := n)) (halfSpaceEmb (n := n) (r • (ω : ℝ^(n - 1)))) ^ n)⁻¹) =
          ∫ r in Ioi (0 : ℝ), r ^ (n - 2) * (1 + r ^ 2) ^ (-((n : ℝ) / 2)) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) ↦ ?_
      have hω : ‖(ω : ℝ^(n - 1))‖ = 1 := by simp
      rw [finrank_euclideanSpace, Fintype.card_fin, show n - 1 - 1 = n - 2 by omega,
        inv_distance_pow_eLast_eq_rpow, norm_smul, Real.norm_eq_abs, abs_of_pos hr, hω, mul_one,
        smul_eq_mul]
    rw [integral_congr_ae (ae_of_all _ hradial), integral_const, smul_eq_mul,
      integral_Ioi_poisson_radial hn]
    change unitSphereArea (n - 1) * _ = _
    have hnReal : (0 : ℝ) < n := by exact_mod_cast hnPos
    have hnm1Real : (0 : ℝ) < (n : ℝ) - 1 := by
      have : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
      linarith
    have hGammaPred :
        Real.Gamma (((n : ℝ) - 1) / 2 + 1) =
          (((n : ℝ) - 1) / 2) *
            Real.Gamma (((n : ℝ) - 1) / 2) :=
      Real.Gamma_add_one (by positivity)
    have hGammaN :
        Real.Gamma ((n : ℝ) / 2 + 1) =
          ((n : ℝ) / 2) * Real.Gamma ((n : ℝ) / 2) :=
      Real.Gamma_add_one (by positivity)
    have hGammaPredNe :
        Real.Gamma (((n : ℝ) - 1) / 2) ≠ 0 :=
      (Real.Gamma_pos_of_pos (by positivity)).ne'
    have hGammaNNe :
        Real.Gamma ((n : ℝ) / 2) ≠ 0 :=
      (Real.Gamma_pos_of_pos (by positivity)).ne'
    have hsqrtNe : Real.sqrt Real.pi ≠ 0 :=
      (Real.sqrt_pos.2 Real.pi_pos).ne'
    have hpow :
        Real.sqrt Real.pi ^ n =
          Real.sqrt Real.pi ^ (n - 1) * Real.sqrt Real.pi := by
      nth_rewrite 1 [← Nat.sub_add_cancel (show 1 ≤ n by omega)]
      exact pow_succ _ _
    rw [unitSphereArea_eq, unitBallVolume, unitBallVolume,
      Real.Gamma_one_half_eq]
    simp only [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one]
    rw [hGammaPred, hGammaN, hpow]
    field_simp [hGammaPredNe, hGammaNNe, hsqrtNe]

/--
The half-space Poisson extension preserves the constant boundary value one in
every positive dimension.

Translation removes the tangential component of the field point, scaling
reduces its height to one, and `integral_distance_pow_inv_eLast` supplies the
exact sphere-volume normalization.
-/
theorem poissonHalfSpaceExtension_one_eq_one
    (x : ℝ^n)
    (hx : x ∈ SobolevSpace.HalfSpace.upper n) :
    poissonHalfSpaceExtension (n := n)
      (fun _ : ℝ^n ↦ (1 : ℝ)) x = 1 := by
  have ht : 0 < x PDE.Common.lastIndex := by simpa [SobolevSpace.HalfSpace.upper] using hx
  rw [poissonHalfSpaceExtension_eq_integral (n := n) (fun _ : ℝ^n ↦ (1 : ℝ)) measurable_const x]
  simp only [one_div]
  change (2 * x PDE.Common.lastIndex) / ((n : ℝ) * unitBallVolume n) *
    (∫ y : ℝ^(n - 1), (dist x (halfSpaceEmb (n := n) y) ^ n)⁻¹) = 1
  rw [integral_distance_pow_inv_horizontal_indep, sub_halfSpaceEmb_halfSpaceProj_eq,
    integral_distance_pow_inv_scale _ ht, integral_distance_pow_inv_eLast]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : 0 < n).ne'
  have := (unitBallVolume_pos n).ne'
  field_simp


end PoissonHalfSpaceNormalization

end GreenFunction
