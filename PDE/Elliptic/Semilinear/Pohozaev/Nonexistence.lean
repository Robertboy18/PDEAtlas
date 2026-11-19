/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Semilinear.Pohozaev.Boundary
public import PDE.Analysis.Calculus.PowerPotential.Classical
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Normal.Flux.StarConvex

/-!
# Strict-supercritical nonexistence on star-shaped domains

Let `n ≥ 3` and `p > (n+2)/(n-2)`, and let `Ω` be a bounded open set with `C¹` graph boundary whose
closure is star-shaped with respect to a point `c`. A solution of `-Δu = |u|^{p-1} u` that is `C²`
up to the boundary and vanishes on the boundary vanishes on the closure
(`eq_zero_on_closure_of_supercritical_power`). The solution may change sign, the star center may lie
on the boundary, and no strict normal sign or connectedness is assumed. The critical exponent is not
included.

This is Evans's §9.4.2, Theorem 3, for the problem (11) with the exponent range (13). The hypothesis
`StarConvex ℝ c (closure Ω)` is his definition of a star-shaped open set, with center `c` in place
of `0`. His range (13) needs `n ≥ 3`, which is an explicit hypothesis.

## How it works

As in Evans's proof, the boundary Pohozaev identity for the potential `|u|^{p+1}/(p+1)`
(`pohozaev_identity_of_zero_boundary`) gives his (18) and the identity `∫ |Du|² = ∫ |u|^{p+1}`. The
boundary integral is nonnegative when the closure is star-shaped
(`integral_normalFlux_smul_sub_nonneg_of_starConvex_closure`), the integrated form of his
Lemma (Normals to a star-shaped region), and this gives (19). Since `n/(p+1) < (n-2)/2`, the
integral of `|u|^{p+1}` vanishes, and continuity gives `u = 0` on the closure.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.4.2 (Derrick-Pohozaev identity), (11) and (13) and the
  definition of star-shaped sets, p. 551, the Lemma (Normals to a star-shaped region), p. 552, and
  Theorem 3 (Nonexistence of nontrivial solution) and its proof, (14)-(19), pp. 552-554.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

namespace PDE.Elliptic.Semilinear

open Set MeasureTheory SobolevSpace Boundary Trace.C1 Geometry.SurfaceMeasure

/-- Every C² closure Dirichlet solution of the strict-supercritical real
power equation on a bounded open C¹ graph domain with star-shaped closure is
zero on the entire closure. The atlas and all integral identities are derived. -/
theorem eq_zero_on_closure_of_supercritical_power
    {m : ℕ} (hn : 3 ≤ m + 1) {Ω : Set (ℝ^(m + 1))}
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : HasC1GraphBoundary Ω) {c : ℝ^(m + 1)}
    (hstar : StarConvex ℝ c (closure Ω)) {p : ℝ}
    (hp : (((m + 1 : ℕ) : ℝ) + 2) / (((m + 1 : ℕ) : ℝ) - 2) < p)
    {u : ℝ^(m + 1) → ℝ} (hu : ContDiffUpToBoundary 2 u Ω)
    (hc : ContinuousOn u (closure Ω)) (hzero : ∀ x ∈ frontier Ω, u x = 0)
    (hpde : ∀ x ∈ Ω, -laplacian u x = |u x| ^ (p - 1) * u x) :
    EqOn u 0 (closure Ω) := by
  let := hgraph.c1ExtensionAtlas hopen hbounded
  have hnreal : (3 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast hn
  have hden : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) - 2 := by linarith
  have hpbound := (div_lt_iff₀ hden).mp hp
  have hpone : 1 ≤ p := by
    by_contra h
    have hlt : p < 1 := lt_of_not_ge h
    have := mul_lt_mul_of_pos_right hlt hden
    nlinarith
  have hppos : 0 < p + 1 := by linarith
  have hderiv (s : ℝ) : deriv (Real.signedPowerPotential p) s =
      Real.signedPower p s := (Real.hasDerivAt_signedPowerPotential hpone s).deriv
  obtain ⟨_, hv, hs, _, he, hpo⟩ := pohozaev_identity_of_zero_boundary hgraph hu hc hzero
    (Real.contDiff_one_signedPowerPotential hpone) (Real.signedPowerPotential_zero hpone)
      (fun x hx ↦ by simpa only [hderiv, Real.signedPower] using hpde x hx) c
  simp only [hderiv, Real.mul_signedPower_eq_abs_rpow hpone] at hs he
  have hpotential : (∫ x in Ω, Real.signedPowerPotential p (u x)) =
      (∫ x in Ω, |u x| ^ (p + 1)) / (p + 1) := by
    simp only [Real.signedPowerPotential, integral_div]
  rw [hpotential, he] at hpo
  have hq := integral_normalFlux_smul_sub_nonneg_of_starConvex_closure
    hstar (fun x _ ↦ sq_nonneg
      (‖(hu.of_le (show 1 ≤ 2 by omega)).completedGradient x‖))
  have hP : 0 ≤ ∫ x in Ω, |u x| ^ (p + 1) :=
    integral_nonneg fun x ↦ Real.rpow_nonneg (abs_nonneg (u x)) _
  have hcoef : ((m + 1 : ℕ) : ℝ) / (p + 1) < (((m + 1 : ℕ) : ℝ) - 2) / 2 := by
    apply (div_lt_iff₀ hppos).mpr
    nlinarith
  have hPzero : (∫ x in Ω, |u x| ^ (p + 1)) = 0 := by
    have hprod : (0 : ℝ) ≤
        ((((m + 1 : ℕ) : ℝ) - 2) / 2 - ((m + 1 : ℕ) : ℝ) / (p + 1)) *
          (∫ x in Ω, |u x| ^ (p + 1)) :=
      mul_nonneg (sub_nonneg.mpr hcoef.le) hP
    have halgebra : ((m + 1 : ℕ) : ℝ) *
        ((∫ x in Ω, |u x| ^ (p + 1)) / (p + 1)) =
          (((m + 1 : ℕ) : ℝ) / (p + 1)) * (∫ x in Ω, |u x| ^ (p + 1)) := by ring
    rw [halgebra] at hpo
    nlinarith
  have hpae : (fun x ↦ |u x| ^ (p + 1)) =ᵐ[volume.restrict Ω] 0 :=
    (integral_eq_zero_iff_of_nonneg
      (fun x ↦ Real.rpow_nonneg (abs_nonneg (u x)) _) hs).mp hPzero
  have huae : u =ᵐ[volume.restrict Ω] 0 := by
    filter_upwards [hpae] with x hx
    have hz : |u x| = 0 := by
      by_contra h
      exact (ne_of_gt (Real.rpow_pos_of_pos (lt_of_le_of_ne (abs_nonneg _) (Ne.symm h))
        (p + 1))) hx
    exact abs_eq_zero.mp hz
  have huΩ : EqOn u 0 Ω :=
    Measure.eqOn_open_of_ae_eq huae hopen (hc.mono subset_closure) continuousOn_const
  exact huΩ.of_subset_closure hc continuousOn_const subset_closure Subset.rfl

end PDE.Elliptic.Semilinear
