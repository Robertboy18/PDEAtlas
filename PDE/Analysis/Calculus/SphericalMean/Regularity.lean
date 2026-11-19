/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.CompactParametricIntegral.ContDiff
public import PDE.Analysis.Calculus.SphericalMean

/-!
# Joint regularity of spherical means

Integration over the fixed unit sphere preserves finite differentiability in
the center and signed radius. Compactness supplies the local bounds needed for
differentiation under the integral; the initial data need no global derivative
bounds or support assumptions.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace PDE.Analysis

variable {n k : ℕ}

/-- Spherical averaging preserves joint finite regularity in the center and
signed radius, including radius zero. -/
theorem contDiff_unitSphereAverage {f : ℝ^n → ℝ} (hf : ContDiff ℝ k f) :
    ContDiff ℝ k (fun p : ℝ^n × ℝ ↦ unitSphereAverage n f p.1 p.2) := by
  have hfamily : ContDiff ℝ k
      (fun p : (ℝ^n × ℝ) × ℝ^n ↦ f (p.1.1 + p.1.2 • p.2)) :=
    hf.comp ((contDiff_fst.fst).add ((contDiff_fst.snd).smul contDiff_snd))
  exact (contDiff_integral_compact_parametrization
    (μ := (volume : Measure (ℝ^n)).toSphere) hfamily continuous_subtype_val).div_const _

/-- A center derivative passes through spherical averaging. -/
theorem partialDeriv_unitSphereAverage {f : ℝ^n → ℝ} (hf : ContDiff ℝ 1 f)
    (i : Fin n) (x : ℝ^n) (r : ℝ) :
    (∂[i] (fun y ↦ unitSphereAverage n f y r)) x =
      unitSphereAverage n (∂[i] f) x r := by
  let μ := (volume : Measure (ℝ^n)).toSphere
  let D : ℝ^n → Metric.sphere (0 : ℝ^n) 1 → ℝ^n →L[ℝ] ℝ :=
    fun y ω ↦ fderiv ℝ f (y + r • (ω : ℝ^n))
  have hp : Continuous
      (fun p : ℝ^n × Metric.sphere (0 : ℝ^n) 1 ↦ p.1 + r • (p.2 : ℝ^n)) := by
    fun_prop
  have hD : Continuous D.uncurry := (hf.continuous_fderiv one_ne_zero).comp hp
  have hd (y : ℝ^n) (ω : Metric.sphere (0 : ℝ^n) 1) :
      HasFDerivAt (fun z ↦ f (z + r • (ω : ℝ^n))) (D y ω) y := by
    convert
      (hf.differentiable one_ne_zero _).hasFDerivAt.comp y
        ((hasFDerivAt_id y).add_const (r • (ω : ℝ^n))) using 1 <;> rfl
  have hi := hasFDerivAt_integral_of_compact (μ := μ)
    (f := fun y ω ↦ f (y + r • (ω : ℝ^n))) (D := D)
    (hf.continuous.comp hp) hD hd x
  have hDi : Integrable (D x) μ := by
    exact (hD.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (fun _ _ ↦ Set.mem_univ _))
  unfold partialDeriv unitSphereAverage
  simp only [div_eq_mul_inv]
  rw [(hi.mul_const (unitSphereArea n)⁻¹).fderiv]
  rw [smul_apply, smul_eq_mul]
  rw [ContinuousLinearMap.integral_apply hDi]
  exact mul_comm _ _

/-- The center Laplacian commutes with spherical averaging for `C²` data. -/
theorem laplacian_unitSphereAverage {f : ℝ^n → ℝ} (hf : ContDiff ℝ 2 f)
    (x : ℝ^n) (r : ℝ) :
    laplacian (fun y ↦ unitSphereAverage n f y r) x =
      unitSphereAverage n (laplacian f) x r := by
  have hd (i : Fin n) : ContDiff ℝ 1 (∂[i] f) :=
    contDiff_partialDeriv_of_succ (m := 1) hf
  unfold laplacian
  simp_rw [partialDeriv_unitSphereAverage (hf.of_le (by norm_num)),
    partialDeriv_unitSphereAverage (hd _)]
  unfold unitSphereAverage
  rw [← Finset.sum_div, ← integral_finsetSum]
  intro i _
  have hc : Continuous (∂[i] (∂[i] f)) :=
    (contDiff_partialDeriv_of_succ (m := 0) (hd i)).continuous
  exact (hc.comp (by fun_prop)).integrable_of_hasCompactSupport
    (isCompact_univ.of_isClosed_subset isClosed_closure (fun _ _ ↦ Set.mem_univ _))

/-- In dimension three, multiplication by the radius removes the first-order
term in the radial Laplacian. -/
theorem secondDeriv_radius_mul_unitSphereAverage {f : ℝ^3 → ℝ}
    (hf : ContDiff ℝ 2 f) (x : ℝ^3) {r : ℝ} (hr : 0 < r) :
    deriv (deriv (fun s ↦ s * unitSphereAverage 3 f x s)) r =
      r * unitSphereAverage 3 (laplacian f) x r := by
  let M := unitSphereAverage 3 f x
  have hM : ContDiff ℝ 2 M :=
    (contDiff_unitSphereAverage hf).comp (contDiff_const.prodMk contDiff_id)
  have hd (s : ℝ) := (hM.differentiable (by norm_num) s).hasDerivAt
  have hdd := (hM.deriv'.differentiable one_ne_zero r).hasDerivAt
  have hfirst : deriv (fun s ↦ s * M s) = fun s ↦ M s + s * deriv M s := by
    funext s
    simpa using ((hasDerivAt_id s).fun_mul (hd s)).deriv
  rw [hfirst]
  have hsecond := ((hd r).fun_add ((hasDerivAt_id r).fun_mul hdd)).deriv
  simp only [id_eq, one_mul] at hsecond
  have hrad := radialLaplacian_unitSphereAverage f x hr hf
  change deriv (deriv M) r + (↑(3 - 1 : ℕ) / r) * deriv M r =
    unitSphereAverage 3 (laplacian f) x r at hrad
  rw [hsecond]
  norm_num only [Nat.reduceSub, Nat.cast_ofNat] at hrad
  have hr0 : r ≠ 0 := hr.ne'
  field_simp at hrad
  linear_combination hrad

end PDE.Analysis
