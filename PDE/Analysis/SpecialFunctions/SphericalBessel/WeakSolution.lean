/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.SphericalBessel.Uniqueness
public import PDE.Analysis.SpecialFunctions.SphericalBessel.SquaredArgument
public import PDE.Analysis.SpecialFunctions.SphericalBessel.Lommel
import PDE.Analysis.Evolution.Time.WeakDerivative.LocalConstant
import PDE.Analysis.Evolution.Time.WeakDerivative.Primitive
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Distributional solutions of the radial Bessel equation

A locally integrable function `c` on `(0, R)` solves `(r² c')' + q c = 0` in the sense of
distributions when `∫ c ((r² φ')' + q φ) = 0` for every smooth `φ` with compact support in
`(0, R)`. For continuous `q` such a `c` agrees almost everywhere with a function `f` that is
differentiable on `(0, R)` and for which `r² f'` is differentiable with derivative `-q f`: the
primitive `P` of `q c` gives `∫ c (r² φ')' = ∫ P φ'`, testing with `r² φ' = χ - (∫ χ / r²) ρ`
for a fixed bump `ρ` shows that `c` has the weak derivative `-(P + λ) / r²`, which is continuous,
and a function with zero weak derivative on an interval is constant.

The radial part of an axisymmetric test field `F(‖x‖²) q(x)`, with `q` a harmonic polynomial
homogeneous of degree `l`, is `φ r = r^l F(r²)`, and
`(r² φ')' - l (l + 1) φ = r^{l+2} (4 r² F''(r²) + (4l + 6) F'(r²))`. Every test function with
compact support in `(0, R)` has this form. For `q r = μ r² - l (l + 1)` with `μ` real, tests
`F` that are smooth at `0` exclude the solution that is singular at the origin: a test equal to
the regular solution `r^l G_l(μ r²)` near `0` makes the Wronskian of the two solutions vanish
there, and the solution is a multiple of `r^l G_l(μ r²)` on `(0, R)`.

For the first-order system `(r² α)' = r β`, `(r β)' = l (l + 1) α` of the curl-free and
divergence-free meridional fields, `r α` solves the radial equation with `μ = 0`, so
`r² α = C r^{l+1} + D r^{-l}`; integrability of `r² α` at the origin forces `D = 0`.

## Main results

* `exists_hasDerivAt_of_weak_radial`: distributional solutions are classical.
* `radial_pow_mul_comp_sq`: the radial operator on `r^l F(r²)`.
* `ae_eq_smul_radialSolution_of_weak`: distributional solutions tested with `r^l F(r²)` are
  almost everywhere multiples of the regular solution `r^l G_l(μ r²)`.
* `ae_eq_pow_of_weak_harmonic`: distributional solutions of the harmonic system with `r² α`
  integrable are `α = C r^{l-1}`, `β = C (l + 1) r^{l-1}`.
* `setIntegral_mul_deriv_eq_neg`, `ae_eq_mul_deriv_of_weak`: integration by parts against tests
  in `(0, R)`, and `e = r g'` when `r a` has the weak derivative `a + e` with `a = g`
  almost everywhere; `exists_test_pow_mul_comp_sq` builds the tests `r^m K(r²)`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace PDE.Analysis.SpecialFunctions

/-- A compact subset of an open interval and one more point of it lie in a closed subinterval. -/
theorem exists_Icc_subset_Ioo_of_isCompact {a b x : ℝ} {K : Set ℝ} (hK : IsCompact K)
    (hKab : K ⊆ Ioo a b) (hx : x ∈ Ioo a b) :
    ∃ α β, a < α ∧ β < b ∧ x ∈ Icc α β ∧ K ⊆ Icc α β := by
  have hK' : IsCompact (insert x K) := hK.insert x
  have hne : (insert x K).Nonempty := insert_nonempty x K
  have hsub : insert x K ⊆ Ioo a b := insert_subset hx hKab
  have hle := subset_Icc_csInf_csSup hK'.bddBelow hK'.bddAbove
  exact ⟨_, _, (hsub (hK'.sInf_mem hne)).1, (hsub (hK'.sSup_mem hne)).2, hle (mem_insert x K),
    fun y hy ↦ hle (mem_insert_of_mem x hy)⟩

/-- The primitive `P r = ∫_{r₀}^r g` of a function locally integrable on an open interval is a
weak primitive there: `∫ P φ' = -∫ g φ` for every test function supported in the interval. -/
theorem integral_primitive_mul_deriv {a b r₀ : ℝ} {g : ℝ → ℝ}
    (hg : LocallyIntegrableOn g (Ioo a b)) (hr₀ : r₀ ∈ Ioo a b) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hcs : HasCompactSupport φ) (hsupp : tsupport φ ⊆ Ioo a b) :
    ∫ r, (∫ t in r₀..r, g t) * deriv φ r = -∫ r, g r * φ r := by
  obtain ⟨α, β, haα, hβb, hr₀αβ, hKαβ⟩ := exists_Icc_subset_Ioo_of_isCompact hcs hsupp hr₀
  set g' := (Icc α β).indicator g with hg'
  have hg'int : Integrable g' := (integrable_indicator_iff measurableSet_Icc).mpr
    (hg.integrableOn_compact_subset (Icc_subset_Ioo haα hβb) isCompact_Icc)
  have h := (Evolution.hasWeakTimeDerivativeOn_intervalPrimitive hg'int.locallyIntegrable
    r₀).integral_smul_eq hφ hcs (subset_univ _)
  have h1 : ∫ r, (∫ t in r₀..r, g t) * deriv φ r = ∫ r, deriv φ r • ∫ t in r₀..r, g' t := by
    refine integral_congr_ae (ae_of_all _ fun r ↦ ?_)
    by_cases hr : r ∈ Icc α β
    · simp only [intervalIntegral.integral_congr fun t ht ↦
        (indicator_of_mem (uIcc_subset_Icc hr₀αβ hr ht) g).symm, hg', smul_eq_mul, mul_comm]
    · simp [image_eq_zero_of_notMem_tsupport fun h ↦ hr (hKαβ (tsupport_deriv_subset h))]
  have h2 : ∫ r, g r * φ r = ∫ r, φ r • g' r := by
    refine integral_congr_ae (ae_of_all _ fun r ↦ ?_)
    by_cases hr : r ∈ Icc α β
    · simp [hg', hr, mul_comm]
    · simp [image_eq_zero_of_notMem_tsupport fun h ↦ hr (hKαβ h)]
  rw [h1, h2, h, neg_neg]

/-- The primitive of a function locally integrable on an open interval is continuous there. -/
theorem continuousOn_primitive_of_locallyIntegrableOn {a b r₀ : ℝ} {g : ℝ → ℝ}
    (hg : LocallyIntegrableOn g (Ioo a b)) (hr₀ : r₀ ∈ Ioo a b) :
    ContinuousOn (fun r ↦ ∫ t in r₀..r, g t) (Ioo a b) := by
  intro r hr
  obtain ⟨ε, hε, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (isOpen_Ioo.mem_nhds hr)
  rw [Real.closedBall_eq_Icc] at hsub
  obtain ⟨α, β, haα, hβb, hr₀αβ, hK⟩ := exists_Icc_subset_Ioo_of_isCompact isCompact_Icc hsub hr₀
  have hle : α ≤ β := hr₀αβ.1.trans hr₀αβ.2
  have hcont := intervalIntegral.continuousOn_primitive_interval'
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hle).mpr
      (hg.integrableOn_compact_subset (Icc_subset_Ioo haα hβb) isCompact_Icc))
    (by rwa [uIcc_of_le hle])
  rw [uIcc_of_le hle] at hcont
  have hα := (hK (left_mem_Icc.2 (by linarith : r - ε ≤ r + ε))).1
  have hβ := (hK (right_mem_Icc.2 (by linarith : r - ε ≤ r + ε))).2
  exact (hcont.continuousAt (Icc_mem_nhds (by linarith) (by linarith))).continuousWithinAt

/-- Dividing a smooth function that vanishes near the origin by `r²` gives a smooth function. -/
theorem contDiff_div_sq {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (h0 : (0 : ℝ) ∉ tsupport χ) :
    ContDiff ℝ ∞ (fun r ↦ χ r / r ^ 2) := by
  refine contDiff_iff_contDiffAt.mpr fun x ↦ ?_
  rcases eq_or_ne x 0 with rfl | hx
  · exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      ((notMem_tsupport_iff_eventuallyEq.mp h0).mono fun r hr ↦ by simp [hr])
  · exact hχ.contDiffAt.div (contDiffAt_id.pow 2) (pow_ne_zero 2 hx)

/-- A test function supported in `(0, R)` divided by `r²` is again such a test function. -/
theorem tsupport_div_sq_subset {χ : ℝ → ℝ} {s : Set ℝ} (h : tsupport χ ⊆ s) :
    tsupport (fun r ↦ χ r / r ^ 2) ⊆ s :=
  tsupport_mul_subset_left.trans h

/-- The derivative of `s ↦ s²`. -/
private theorem hasDerivAt_sq (x : ℝ) : HasDerivAt (fun s : ℝ ↦ s ^ 2) (2 * x) x := by
  simpa using hasDerivAt_pow 2 x

/-- **Regularity of distributional radial solutions.** Let `q` be continuous on `(0, R)` and let
`c` be locally integrable there with `∫ c ((r² φ')' + q φ) = 0` for every smooth `φ` with compact
support in `(0, R)`. Then `c` agrees almost everywhere on `(0, R)` with a function `f` that is
differentiable on `(0, R)` and for which `r² f'` is differentiable with derivative `-q f`. -/
theorem exists_hasDerivAt_of_weak_radial {R : ℝ} (hR : 0 < R) {q c : ℝ → ℝ}
    (hq : ContinuousOn q (Ioo 0 R)) (hc : LocallyIntegrableOn c (Ioo 0 R))
    (hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioo 0 R →
      ∫ r, c r * (r ^ 2 * deriv (deriv φ) r + 2 * r * deriv φ r + q r * φ r) = 0) :
    ∃ f : ℝ → ℝ, c =ᵐ[volume.restrict (Ioo 0 R)] f ∧ ∀ r ∈ Ioo 0 R,
      HasDerivAt f (deriv f r) r ∧ HasDerivAt (fun s ↦ s ^ 2 * deriv f s) (-(q r * f r)) r := by
  have htest {w φ : ℝ → ℝ} (hw : LocallyIntegrableOn w (Ioo 0 R)) (hφc : Continuous φ)
      (hφcs : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioo 0 R) :
      Integrable (fun r ↦ w r * φ r) :=
    Evolution.HasWeakTimeDerivativeOn.integrable_mul_test hw hφc hφcs hφs
  have hdtest {w φ : ℝ → ℝ} (hw : LocallyIntegrableOn w (Ioo 0 R)) (hφ : ContDiff ℝ ∞ φ)
      (hcs : HasCompactSupport φ) (hsupp : tsupport φ ⊆ Ioo 0 R) :
      Integrable (fun r ↦ w r * deriv φ r) :=
    htest hw (hφ.continuous_deriv (by simp)) hcs.deriv (tsupport_deriv_subset.trans hsupp)
  set r₀ := R / 2 with hr₀def
  have hr₀ : r₀ ∈ Ioo 0 R := ⟨by positivity, by linarith⟩
  set g : ℝ → ℝ := fun r ↦ q r * c r with hgdef
  have hg : LocallyIntegrableOn g (Ioo 0 R) := hc.continuousOn_mul hq isOpen_Ioo.isLocallyClosed
  set P : ℝ → ℝ := fun r ↦ ∫ t in r₀..r, g t with hPdef
  have hPcont : ContinuousOn P (Ioo 0 R) := continuousOn_primitive_of_locallyIntegrableOn hg hr₀
  have hPloc : LocallyIntegrableOn P (Ioo 0 R) := hPcont.locallyIntegrableOn measurableSet_Ioo
  let b : ContDiffBump r₀ := ⟨R / 8, R / 4, by positivity, by linarith⟩
  set ρ₁ : ℝ → ℝ := b.normed volume with hρ₁
  have hρ₁s : ContDiff ℝ ∞ ρ₁ := b.contDiff_normed
  have hρ₁cs : HasCompactSupport ρ₁ := b.hasCompactSupport_normed
  have hρ₁supp : tsupport ρ₁ ⊆ Ioo 0 R := by
    rw [hρ₁, b.tsupport_normed_eq, Real.closedBall_eq_Icc]
    exact Icc_subset_Ioo (by simp only [b]; linarith) (by simp only [b]; linarith)
  set ρ : ℝ → ℝ := fun r ↦ r ^ 2 * ρ₁ r with hρ
  have hρs : ContDiff ℝ ∞ ρ := (contDiff_id.pow 2).mul hρ₁s
  have hρcs : HasCompactSupport ρ := hρ₁cs.mul_left
  have hρsupp : tsupport ρ ⊆ Ioo 0 R := tsupport_mul_subset_right.trans hρ₁supp
  set lam : ℝ := (∫ r, c r * deriv ρ r) - ∫ r, P r * ρ₁ r with hlam
  have hkey : ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ Ioo 0 R →
      ∫ r, c r * deriv χ r = ∫ r, (P r + lam) / r ^ 2 * χ r := by
    intro χ hχ hχcs hχsupp
    have h0χ : (0 : ℝ) ∉ tsupport χ := fun h ↦ (lt_irrefl _ (hχsupp h).1)
    set k := ∫ r, χ r / r ^ 2 with hk
    have hχd : ContDiff ℝ ∞ (fun r ↦ χ r / r ^ 2) := contDiff_div_sq hχ h0χ
    have hχdcs : HasCompactSupport (fun r ↦ χ r / r ^ 2) := hχcs.mul_right
    have hχdsupp : tsupport (fun r ↦ χ r / r ^ 2) ⊆ Ioo 0 R := tsupport_div_sq_subset hχsupp
    set ψ : ℝ → ℝ := fun r ↦ χ r / r ^ 2 - k * ρ₁ r with hψ
    have hψs : ContDiff ℝ ∞ ψ := hχd.sub (contDiff_const.mul hρ₁s)
    have hψsupp : tsupport ψ ⊆ Ioo 0 R :=
      (tsupport_sub _ _).trans (union_subset hχdsupp (tsupport_mul_subset_right.trans hρ₁supp))
    have hχdi : Integrable (fun r ↦ χ r / r ^ 2) :=
      hχd.continuous.integrable_of_hasCompactSupport hχdcs
    obtain ⟨φ, hφ, hφcs, hφsupp, hdφ⟩ :=
      exists_compactSupport_antiderivative_on_Ioo_of_integral_eq_zero hψs
        (hχdcs.sub hρ₁cs.mul_left) hψsupp <| by
          rw [integral_sub hχdi (b.integrable_normed.const_mul k),
            integral_const_mul, b.integral_normed, mul_one, sub_self]
    have hderiv : deriv φ = ψ := funext fun x ↦ (hdφ x).deriv
    have hsq : ∀ r, r ^ 2 * ψ r = χ r - k * ρ r := by
      intro r
      rcases eq_or_ne r 0 with rfl | hr
      · simp [hρ, image_eq_zero_of_notMem_tsupport h0χ]
      · simp only [hψ, hρ]
        field_simp
    have hd2 (r : ℝ) : r ^ 2 * deriv (deriv φ) r + 2 * r * deriv φ r =
        deriv χ r - k * deriv ρ r := by
      have hL := (hasDerivAt_sq r).fun_mul (hψs.differentiable (by simp) r).hasDerivAt
      rw [funext hsq] at hL
      rw [hderiv, ← hL.unique ((hχ.differentiable (by simp) r).hasDerivAt.sub
        ((hρs.differentiable (by simp) r).hasDerivAt.const_mul k))]
      ring
    have hcρ := hdtest hc hρs hρcs hρsupp
    have hPχ := htest hPloc hχd.continuous hχdcs hχdsupp
    have hsplit : ∫ r, c r * (r ^ 2 * deriv (deriv φ) r + 2 * r * deriv φ r + q r * φ r) =
        (∫ r, c r * deriv χ r) - k * (∫ r, c r * deriv ρ r) + ∫ r, g r * φ r := by
      rw [← integral_const_mul, ← integral_sub (hdtest hc hχ hχcs hχsupp) (hcρ.const_mul k),
        ← integral_add (f := fun r ↦ c r * deriv χ r - k * (c r * deriv ρ r))
          ((hdtest hc hχ hχcs hχsupp).sub (hcρ.const_mul k))
          (htest hg hφ.continuous hφcs hφsupp)]
      refine integral_congr_ae (ae_of_all _ fun r ↦ ?_)
      simp only [hgdef]
      linear_combination c r * hd2 r
    have hPψ : ∫ r, (∫ t in r₀..r, g t) * deriv φ r =
        (∫ r, P r * (χ r / r ^ 2)) - k * ∫ r, P r * ρ₁ r := by
      rw [hderiv, ← integral_const_mul,
        ← integral_sub hPχ ((htest hPloc hρ₁s.continuous hρ₁cs hρ₁supp).const_mul k)]
      refine integral_congr_ae (ae_of_all _ fun r ↦ ?_)
      simp only [hPdef, hψ]
      ring
    have hR : ∫ r, (P r + lam) / r ^ 2 * χ r = (∫ r, P r * (χ r / r ^ 2)) + lam * k := by
      rw [hk, ← integral_const_mul, ← integral_add hPχ (hχdi.const_mul lam)]
      exact integral_congr_ae (ae_of_all _ fun r ↦ by ring)
    linear_combination hweak φ hφ hφcs hφsupp - hsplit -
      integral_primitive_mul_deriv hg hr₀ hφ hφcs hφsupp + hPψ - hR - k * hlam
  set D : ℝ → ℝ := fun r ↦ -((P r + lam) / r ^ 2) with hD
  have hDcont : ContinuousOn D (Ioo 0 R) :=
    ((hPcont.add continuousOn_const).div (continuousOn_pow 2)
      fun r hr ↦ pow_ne_zero 2 hr.1.ne').neg
  have hsub {r : ℝ} (hr : r ∈ Ioo 0 R) : uIcc r₀ r ⊆ Ioo 0 R :=
    (ordConnected_Ioo (a := (0 : ℝ)) (b := R)).uIcc_subset hr₀ hr
  have hftc {u : ℝ → ℝ} (hu : ContinuousOn u (Ioo 0 R)) {r : ℝ} (hr : r ∈ Ioo 0 R) :
      HasDerivAt (fun s ↦ ∫ t in r₀..s, u t) (u r) r :=
    intervalIntegral.integral_hasDerivAt_right ((hu.mono (hsub hr)).intervalIntegrable)
      (hu.stronglyMeasurableAtFilter isOpen_Ioo r hr) (hu.continuousAt (isOpen_Ioo.mem_nhds hr))
  set F : ℝ → ℝ := fun r ↦ ∫ t in r₀..r, D t with hF
  have hFcont : ContinuousOn F (Ioo 0 R) := fun r hr ↦
    (hftc hDcont hr).continuousAt.continuousWithinAt
  have hFloc : LocallyIntegrableOn F (Ioo 0 R) := hFcont.locallyIntegrableOn measurableSet_Ioo
  have hFweak (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcs : HasCompactSupport φ)
      (hsupp : tsupport φ ⊆ Ioo 0 R) : ∫ r, F r * deriv φ r = -∫ r, D r * φ r :=
    integral_primitive_mul_deriv (hDcont.locallyIntegrableOn measurableSet_Ioo) hr₀ hφ hcs hsupp
  have hcF : Evolution.HasWeakTimeDerivativeOn (Ioo 0 R) (fun r ↦ c r - F r) 0 := by
    refine Evolution.HasWeakTimeDerivativeOn.of_integral_smul_eq (hc.sub hFloc)
      locallyIntegrableOn_zero fun φ hφ hcs hsupp ↦ ?_
    simp only [Pi.zero_apply, smul_eq_mul, mul_zero, integral_zero, neg_zero]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [image_eq_zero_of_notMem_tsupport fun h ↦ hx (hsupp (tsupport_deriv_subset h)), zero_mul]]
    calc ∫ r, deriv φ r * (c r - F r) = ∫ r, (c r * deriv φ r - F r * deriv φ r) :=
          integral_congr_ae (ae_of_all _ fun r ↦ by ring)
      _ = 0 := by
        rw [integral_sub (hdtest hc hφ hcs hsupp) (hdtest hFloc hφ hcs hsupp),
          hkey φ hφ hcs hsupp, hFweak φ hφ hcs hsupp]
        simp only [hD, neg_mul, integral_neg, neg_neg, sub_self]
  obtain ⟨C, hC⟩ := Evolution.HasWeakTimeDerivativeOn.exists_ae_eq_const_on_Ioo_of_zero hR hcF
  set f : ℝ → ℝ := fun r ↦ F r + C with hf
  have hcf : c =ᵐ[volume.restrict (Ioo 0 R)] f := hC.mono fun r hr ↦ sub_eq_iff_eq_add'.mp hr
  have hfd (r : ℝ) (hr : r ∈ Ioo 0 R) : HasDerivAt f (D r) r := (hftc hDcont hr).add_const C
  have hqf : ContinuousOn (fun t ↦ q t * f t) (Ioo 0 R) := hq.mul (hFcont.add continuousOn_const)
  have hcf' := (ae_restrict_iff' measurableSet_Ioo).mp hcf
  refine ⟨f, hcf, fun r hr ↦ ⟨(hfd r hr).differentiableAt.hasDerivAt, ?_⟩⟩
  have hPP' (s : ℝ) (hs : s ∈ Ioo 0 R) : P s = ∫ t in r₀..s, q t * f t := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hcf'] with t ht hts
    simp only [hgdef]
    rw [ht (hsub hs (uIoc_subset_uIcc hts))]
  have hev : (fun s ↦ s ^ 2 * deriv f s) =ᶠ[𝓝 r] fun s ↦ -((∫ t in r₀..s, q t * f t) + lam) := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with s hs
    rw [(hfd s hs).deriv, hD]
    dsimp only
    rw [hPP' s hs]
    field_simp [hs.1.ne']
  exact (((hftc hqf hr).add_const lam).neg).congr_of_eventuallyEq hev

/-! ### Functions of the form `r^l F(r²)` -/

/-- The radial derivative of `r^l F(r²)`: `r (r^l F(r²))' = r^l (l F(r²) + 2 r² F'(r²))`. -/
theorem mul_deriv_pow_mul_comp_sq {F : ℝ → ℝ} (hF : Differentiable ℝ F) (l : ℕ) (r : ℝ) :
    r * deriv (fun s ↦ s ^ l * F (s ^ 2)) r =
      r ^ l * (l * F (r ^ 2) + 2 * r ^ 2 * deriv F (r ^ 2)) := by
  have hd : HasDerivAt (fun s ↦ s ^ l * F (s ^ 2))
      (l * r ^ (l - 1) * F (r ^ 2) + r ^ l * (deriv F (r ^ 2) * (2 * r))) r :=
    (hasDerivAt_pow l r).mul ((hF (r ^ 2)).hasDerivAt.comp r (hasDerivAt_sq r))
  rw [hd.deriv]
  rcases l with _ | m
  · push_cast
    ring
  · simp only [Nat.add_sub_cancel]
    push_cast
    ring

/-- **The radial operator on `r^l F(r²)`.** For `φ r = r^l F(r²)` with `F` of class `C²`,
`(r² φ')' - l (l + 1) φ = r^{l+2} (4 r² F''(r²) + (4l + 6) F'(r²))`. This is the radial part of
`Δ(F(‖x‖²) q) = (4 ‖x‖² F'' + (4l + 6) F') q` for a harmonic polynomial `q` homogeneous of degree
`l`. -/
theorem radial_pow_mul_comp_sq {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) (l : ℕ) (r : ℝ) :
    r ^ 2 * deriv (deriv fun s ↦ s ^ l * F (s ^ 2)) r +
        2 * r * deriv (fun s ↦ s ^ l * F (s ^ 2)) r - l * (l + 1) * (r ^ l * F (r ^ 2)) =
      r ^ (l + 2) * (4 * r ^ 2 * deriv (deriv F) (r ^ 2) + (4 * l + 6) * deriv F (r ^ 2)) := by
  set φ : ℝ → ℝ := fun s ↦ s ^ l * F (s ^ 2) with hφ
  have hF1 : ∀ t, HasDerivAt F (deriv F t) t := fun t ↦
    (hF.differentiable (by norm_num) t).hasDerivAt
  have hφC : ContDiff ℝ 2 φ := (contDiff_id.pow l).mul (hF.comp (contDiff_id.pow 2))
  have hsq : (fun s ↦ s ^ 2 * deriv φ s) =
      fun s ↦ l * s ^ (l + 1) * F (s ^ 2) + 2 * s ^ (l + 3) * deriv F (s ^ 2) := by
    funext s
    rw [show s ^ 2 * deriv φ s = s * (s * deriv φ s) by ring,
      mul_deriv_pow_mul_comp_sq (hF.differentiable (by norm_num)) l s]
    ring
  have hprod := (hasDerivAt_sq r).fun_mul (hφC.differentiable_deriv_two r).hasDerivAt
  have hexpl : HasDerivAt
      (fun s ↦ l * s ^ (l + 1) * F (s ^ 2) + 2 * s ^ (l + 3) * deriv F (s ^ 2))
      (l * ((l + 1) * r ^ l * F (r ^ 2) + r ^ (l + 1) * (deriv F (r ^ 2) * (2 * r))) +
        2 * ((l + 3) * r ^ (l + 2) * deriv F (r ^ 2) +
          r ^ (l + 3) * (deriv (deriv F) (r ^ 2) * (2 * r)))) r := by
    have h1 := ((hasDerivAt_pow (l + 1) r).mul ((hF1 (r ^ 2)).comp r (hasDerivAt_sq r))).const_mul
      (l : ℝ)
    have h2 := ((hasDerivAt_pow (l + 3) r).mul
      ((hF.differentiable_deriv_two (r ^ 2)).hasDerivAt.comp r (hasDerivAt_sq r))).const_mul
        (2 : ℝ)
    convert h1.add h2 using 1
    · funext s
      simp only [Pi.add_apply, Pi.mul_apply, Function.comp_apply]
      ring
    · rw [Nat.add_sub_cancel, show l + 3 - 1 = l + 2 by omega]
      simp only [Function.comp_apply]
      push_cast
      ring
  rw [hsq] at hprod
  linear_combination hprod.unique hexpl

/-- A smooth function with compact support in `(0, R)` equals `r^l F(r²)` for `r > 0`, with
`F s = φ(√s) / √s^l` smooth and of compact support in `(-∞, R²)`. -/
theorem exists_pow_mul_comp_sq_eq {R : ℝ} (hR : 0 < R) {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hcs : HasCompactSupport φ) (hsupp : tsupport φ ⊆ Ioo 0 R) (l : ℕ) :
    ∃ F : ℝ → ℝ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧ tsupport F ⊆ Iio (R ^ 2) ∧
      (0 : ℝ) ∉ tsupport F ∧ ∀ r, 0 < r → r ^ l * F (r ^ 2) = φ r := by
  obtain ⟨α, β, h0α, hβR, hxαβ, hK⟩ :=
    exists_Icc_subset_Ioo_of_isCompact hcs hsupp (show R / 2 ∈ Ioo 0 R from ⟨by positivity,
      by linarith⟩)
  have hβ0 : 0 < β := by linarith [hxαβ.2]
  set F : ℝ → ℝ := fun s ↦ φ (√s) / √s ^ l with hF
  have hφ0 {x : ℝ} (hx : x ∉ Icc α β) : φ x = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦ hx (hK h)
  have hsupF : Function.support F ⊆ Icc (α ^ 2) (β ^ 2) := fun s hs ↦ by
    have hmem : √s ∈ Icc α β := by
      by_contra h
      exact hs (by simp only [hF, hφ0 h, zero_div])
    exact ⟨(Real.le_sqrt' h0α).mp hmem.1,
      (Real.sqrt_le_left (h0α.le.trans (hmem.1.trans hmem.2))).mp hmem.2⟩
  have hlow {s : ℝ} (hs : s < α ^ 2) : F s = 0 :=
    Function.notMem_support.mp fun h ↦ not_lt.mpr (hsupF h).1 hs
  have htsupp : tsupport F ⊆ Icc (α ^ 2) (β ^ 2) := closure_minimal hsupF isClosed_Icc
  refine ⟨F, ?_, isCompact_Icc.of_isClosed_subset (isClosed_tsupport F) htsupp,
    htsupp.trans fun s hs ↦ ?_, fun h ↦ ?_, fun r hr ↦ ?_⟩
  · refine contDiff_iff_contDiffAt.mpr fun s ↦ ?_
    by_cases hs : s < α ^ 2
    · exact contDiffAt_const.congr_of_eventuallyEq
        (eventually_of_mem (Iio_mem_nhds hs) fun t (ht : t < α ^ 2) ↦ hlow ht)
    · have hpos : 0 < s := (by positivity : 0 < α ^ 2).trans_le (not_lt.mp hs)
      exact (hφ.contDiffAt.comp s (Real.contDiffAt_sqrt hpos.ne')).div
        ((Real.contDiffAt_sqrt hpos.ne').pow l)
        (pow_ne_zero l (Real.sqrt_ne_zero'.mpr hpos))
  · exact hs.2.trans_lt (by nlinarith)
  · linarith [(htsupp h).1, (by positivity : 0 < α ^ 2)]
  · simp only [hF, Real.sqrt_sq hr.le]
    field_simp

/-- For `φ r = r^l F(r²)` the radial operator `(r² φ')' + (μ r² - l (l + 1)) φ` is
`r^{l+2} (4 r² F''(r²) + (4l + 6) F'(r²) + μ F(r²))`. -/
theorem radial_pow_mul_comp_sq_add {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) (l : ℕ) (μ r : ℝ) :
    r ^ 2 * deriv (deriv fun s ↦ s ^ l * F (s ^ 2)) r +
        2 * r * deriv (fun s ↦ s ^ l * F (s ^ 2)) r +
        (μ * r ^ 2 - l * (l + 1)) * (r ^ l * F (r ^ 2)) =
      r ^ (l + 2) * (4 * r ^ 2 * deriv (deriv F) (r ^ 2) + (4 * l + 6) * deriv F (r ^ 2) +
        μ * F (r ^ 2)) := by
  have h := radial_pow_mul_comp_sq hF l r
  linear_combination h

/-- The solution `r^l G_l(μ r²)` of the radial equation `(r² φ')' + (μ r² - l (l + 1)) φ = 0`
that is regular at the origin. For `μ = κ² > 0` it is `κ^{-l} j_l(κ r)`; it is the radial
profile of the azimuthal ball modes. -/
def radialSolution (l : ℕ) (μ r : ℝ) : ℝ :=
  r ^ l * reducedSphericalBesselJSq l (μ * r ^ 2)

/-- The regular radial solution is smooth. -/
theorem contDiff_radialSolution (l : ℕ) (μ : ℝ) : ContDiff ℝ ∞ (radialSolution l μ) :=
  (contDiff_id.pow l).mul ((contDiff_reducedSphericalBesselJSq l).comp
    (contDiff_const.mul (contDiff_id.pow 2)))

private theorem hasDerivAt_reduced_mul (l : ℕ) (μ s : ℝ) :
    HasDerivAt (fun s ↦ reducedSphericalBesselJSq l (μ * s))
      (μ * deriv (reducedSphericalBesselJSq l) (μ * s)) s := by
  have hl : HasDerivAt (fun y : ℝ ↦ μ * y) μ s := by
    simpa using (hasDerivAt_id s).const_mul μ
  exact (((contDiff_reducedSphericalBesselJSq l (n := 1)).differentiable one_ne_zero
    (μ * s)).hasDerivAt.comp s hl).congr_deriv (mul_comm _ _)

private theorem hasDerivAt_deriv_reduced_mul (l : ℕ) (μ s : ℝ) :
    HasDerivAt (fun s ↦ μ * deriv (reducedSphericalBesselJSq l) (μ * s))
      (μ * (μ * deriv (deriv (reducedSphericalBesselJSq l)) (μ * s))) s := by
  have hl : HasDerivAt (fun y : ℝ ↦ μ * y) μ s := by
    simpa using (hasDerivAt_id s).const_mul μ
  have hG2 : Differentiable ℝ (deriv (reducedSphericalBesselJSq l)) :=
    (contDiff_reducedSphericalBesselJSq l (n := 2)).differentiable_deriv_two
  exact ((hG2 (μ * s)).hasDerivAt.comp s hl).const_mul μ |>.congr_deriv (by ring)

/-- The regular radial solution solves `(r² φ')' + (μ r² - l (l + 1)) φ = 0`. -/
theorem radialSolution_ode (l : ℕ) (μ r : ℝ) :
    r ^ 2 * deriv (deriv (radialSolution l μ)) r + 2 * r * deriv (radialSolution l μ) r +
      (μ * r ^ 2 - l * (l + 1)) * radialSolution l μ r = 0 := by
  set F : ℝ → ℝ := fun s ↦ reducedSphericalBesselJSq l (μ * s) with hF
  have hFC : ContDiff ℝ ∞ F := (contDiff_reducedSphericalBesselJSq l).comp
    (contDiff_const.mul contDiff_id)
  have hd1 : deriv F = fun s ↦ μ * deriv (reducedSphericalBesselJSq l) (μ * s) :=
    funext fun s ↦ (hasDerivAt_reduced_mul l μ s).deriv
  have hd2 : deriv (deriv F) = fun s ↦ μ * (μ * deriv (deriv (reducedSphericalBesselJSq l))
      (μ * s)) := by
    rw [hd1]
    exact funext fun s ↦ (hasDerivAt_deriv_reduced_mul l μ s).deriv
  have h := radial_pow_mul_comp_sq_add (hFC.of_le (by simp)) l μ r
  rw [hd2, hd1] at h
  have hfun : radialSolution l μ = fun s ↦ s ^ l * F (s ^ 2) := rfl
  rw [hfun]
  beta_reduce
  rw [h]
  have hode := reducedSphericalBesselJSq_ode l (μ * r ^ 2)
  simp only [hF]
  linear_combination r ^ (l + 2) * μ * hode

/-- The regular radial solution is positive near the origin. -/
theorem exists_radialSolution_pos (l : ℕ) (μ : ℝ) :
    ∃ δ > 0, ∀ r ∈ Ioo 0 δ, 0 < radialSolution l μ r := by
  have hcont : ContinuousAt (fun r : ℝ ↦ reducedSphericalBesselJSq l (μ * r ^ 2)) 0 :=
    ((contDiff_reducedSphericalBesselJSq l (n := 0)).continuous.comp
      (continuous_const.mul (continuous_pow 2))).continuousAt
  have hG0 : reducedSphericalBesselJSq l 0 = reducedSphericalBesselJ l 0 := by
    rw [reducedSphericalBesselJ_eq_sq]
    norm_num
  have h0 : 0 < reducedSphericalBesselJSq l (μ * 0 ^ 2) := by
    rw [zero_pow two_ne_zero, mul_zero, hG0]
    exact reducedSphericalBesselJ_zero_pos l
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (hcont.eventually (lt_mem_nhds h0))
  exact ⟨δ, hδ, fun r hr ↦ mul_pos (pow_pos hr.1 l)
    (hball (by rw [Real.dist_eq, sub_zero, abs_of_pos hr.1]; exact hr.2))⟩

/-- If a smooth function vanishes near `0`, the radial operator of `F` vanishes near `0`. -/
theorem exists_radialOperator_eq_zero_of_notMem_tsupport {F : ℝ → ℝ} (hF : (0 : ℝ) ∉ tsupport F)
    (l : ℕ) (μ : ℝ) : ∃ δ > 0, ∀ s ∈ Ioo 0 δ,
      4 * s * deriv (deriv F) s + (4 * l + 6) * deriv F s + μ * F s = 0 := by
  have h0 := notMem_tsupport_iff_eventuallyEq.mp hF
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (h0.and (h0.deriv.and h0.deriv.deriv))
  refine ⟨δ, hδ, fun s hs ↦ ?_⟩
  obtain ⟨e0, e1, e2⟩ := hball (by rw [Real.dist_eq, sub_zero, abs_of_pos hs.1]; exact hs.2)
  simp [e0, e1, e2]

/-- The first and second derivatives of a smooth function exist. -/
private theorem hasDerivAt_deriv_of_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (x : ℝ) :
    HasDerivAt f (deriv f x) x ∧ HasDerivAt (deriv f) (deriv (deriv f) x) x :=
  ⟨(hf.differentiable (by simp) x).hasDerivAt,
    ((hf.of_le (by simp)).differentiable_deriv_two x).hasDerivAt⟩

/-- The radial operator of a test supported in `(0, R)` vanishes outside `(0, R)`. -/
private theorem integral_radialOp_eq_setIntegral {R : ℝ} {c q φ : ℝ → ℝ}
    (hsupp : tsupport φ ⊆ Ioo 0 R) :
    ∫ r, c r * (r ^ 2 * deriv (deriv φ) r + 2 * r * deriv φ r + q r * φ r) =
      ∫ r in Ioo 0 R, c r * (r ^ 2 * deriv (deriv φ) r + 2 * r * deriv φ r + q r * φ r) := by
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ ?_).symm
  have h1 : deriv φ x = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦ hx (hsupp (tsupport_deriv_subset h))
  have h2 : deriv (deriv φ) x = 0 := image_eq_zero_of_notMem_tsupport fun h ↦
    hx (hsupp (tsupport_deriv_subset (tsupport_deriv_subset h)))
  simp [image_eq_zero_of_notMem_tsupport fun h ↦ hx (hsupp h), h1, h2]

/-- **Distributional solutions of the radial Bessel equation.** Let `c` be locally integrable
on `(0, R)`. Suppose that `∫₀^R r^{l+2} K_F(r²) c(r) dr = 0` with
`K_F(s) = 4 s F''(s) + (4l + 6) F'(s) + μ F(s)`, for every smooth `F` with compact support in
`(-∞, R²)` whose `K_F` vanishes near `0`; these are the tests `F(‖x‖²) q(x)` of `Δ + μ` against
a field whose component along a harmonic polynomial `q` of degree `l` is `c`. Then `c` is
almost everywhere a multiple of the regular solution `r^l G_l(μ r²)` on `(0, R)`. Tests
supported away from the origin make `c` a classical solution; a test equal to the regular
solution near the origin makes their Wronskian vanish there, which excludes the solution
singular at the origin, and the uniqueness theorem for the radial equation extends the
identity to `(0, R)`. -/
theorem ae_eq_smul_radialSolution_of_weak {l : ℕ} {μ R : ℝ} (hR : 0 < R)
    {c : ℝ → ℝ} (hc : LocallyIntegrableOn c (Ioo 0 R))
    (hweak : ∀ F : ℝ → ℝ, ContDiff ℝ ∞ F → HasCompactSupport F → tsupport F ⊆ Iio (R ^ 2) →
      (∃ δ > 0, ∀ s ∈ Ioo 0 δ,
        4 * s * deriv (deriv F) s + (4 * l + 6) * deriv F s + μ * F s = 0) →
      ∫ r in Ioo 0 R, r ^ (l + 2) * (4 * r ^ 2 * deriv (deriv F) (r ^ 2) +
        (4 * l + 6) * deriv F (r ^ 2) + μ * F (r ^ 2)) * c r = 0) :
    ∃ A : ℝ, c =ᵐ[volume.restrict (Ioo 0 R)] fun r ↦ A * radialSolution l μ r := by
  set q : ℝ → ℝ := fun r ↦ μ * r ^ 2 - l * (l + 1) with hq
  have hqc : Continuous q := by simp only [hq]; fun_prop
  -- the tests of the regularity theorem
  have hweak' : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioo 0 R →
      ∫ r, c r * (r ^ 2 * deriv (deriv φ) r + 2 * r * deriv φ r + q r * φ r) = 0 := by
    intro φ hφ hcs hsupp
    obtain ⟨F, hF, hFcs, hFsupp, hF0, hFφ⟩ := exists_pow_mul_comp_sq_eq hR hφ hcs hsupp l
    rw [integral_radialOp_eq_setIntegral hsupp]
    refine (setIntegral_congr_fun measurableSet_Ioo fun r hr ↦ ?_).trans
      (hweak F hF hFcs hFsupp (exists_radialOperator_eq_zero_of_notMem_tsupport hF0 l μ))
    have hev : (fun s ↦ s ^ l * F (s ^ 2)) =ᶠ[𝓝 r] φ := eventually_of_mem (Ioi_mem_nhds hr.1) hFφ
    have h := radial_pow_mul_comp_sq_add (hF.of_le (by simp)) l μ r
    rw [hev.deriv_eq, hev.deriv.deriv_eq, hFφ r hr.1] at h
    simp only [hq]
    linear_combination c r * h
  obtain ⟨f, hcf, hf⟩ := exists_hasDerivAt_of_weak_radial hR hqc.continuousOn hc hweak'
  have hcf' := (ae_restrict_iff' measurableSet_Ioo).mp hcf
  have hfcont : ContinuousOn f (Ioo 0 R) := fun r hr ↦
    (hf r hr).1.continuousAt.continuousWithinAt
  -- the regular solution
  set φ₀ : ℝ → ℝ := radialSolution l μ with hφ₀
  have hφ₀d := hasDerivAt_deriv_of_contDiff (contDiff_radialSolution l μ)
  have hφ₀ode (r : ℝ) : r ^ 2 * deriv (deriv φ₀) r + 2 * r * deriv φ₀ r + q r * φ₀ r = 0 :=
    radialSolution_ode l μ r
  -- the Wronskian of `f` and `φ₀` vanishes near the origin
  have hW : ∀ r₁ ∈ Ioo 0 (R / 4),
      r₁ ^ 2 * (deriv φ₀ r₁ * f r₁ - φ₀ r₁ * deriv f r₁) = 0 := by
    intro r₁ hr₁
    have hr₁R : 2 * r₁ < R / 2 := by linarith [hr₁.2]
    let χ : ContDiffBump (0 : ℝ) :=
      ⟨(2 * r₁) ^ 2, (R / 2) ^ 2, by have := hr₁.1; positivity, by nlinarith [hr₁.1]⟩
    set G : ℝ → ℝ := fun s ↦ reducedSphericalBesselJSq l (μ * s) with hG
    have hGC : ContDiff ℝ ∞ G :=
      (contDiff_reducedSphericalBesselJSq l).comp (contDiff_const.mul contDiff_id)
    set FW : ℝ → ℝ := fun s ↦ χ s * G s with hFWdef
    have hFW : ContDiff ℝ ∞ FW := χ.contDiff.mul hGC
    have hFWsupp : tsupport FW ⊆ Iio (R ^ 2) := tsupport_mul_subset_left.trans <| by
      rw [χ.tsupport_eq, Real.closedBall_eq_Icc]
      exact fun s hs ↦ hs.2.trans_lt (by simp only [zero_add, χ]; nlinarith)
    set ψ : ℝ → ℝ := fun s ↦ s ^ l * FW (s ^ 2) with hψdef
    have hψC : ContDiff ℝ ∞ ψ := (contDiff_id.pow l).mul (hFW.comp (contDiff_id.pow 2))
    have hψ (s : ℝ) : ψ s = χ (s ^ 2) * φ₀ s := by
      simp only [hψdef, hFWdef, hG, hφ₀, radialSolution]
      ring
    have hnear : ∀ r ∈ Ioo 0 (2 * r₁), ψ =ᶠ[𝓝 r] φ₀ := by
      intro r hr
      filter_upwards [Ioo_mem_nhds (show -(2 * r₁) < r by linarith [hr.1, hr₁.1]) hr.2]
        with s hs
      rw [hψ, χ.one_of_mem_closedBall, one_mul]
      rw [Real.closedBall_eq_Icc]
      simp only [mem_Icc, zero_sub, zero_add, χ]
      constructor <;> nlinarith [hs.1, hs.2]
    have hfar : ∀ r, R / 2 < r → ψ =ᶠ[𝓝 r] fun _ ↦ (0 : ℝ) := fun r hr ↦ by
      filter_upwards [Ioi_mem_nhds hr] with s (hs : R / 2 < s)
      rw [hψ, χ.zero_of_le_dist, zero_mul]
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
      simp only [χ]
      nlinarith
    set Lψ : ℝ → ℝ := fun r ↦ r ^ 2 * deriv (deriv ψ) r + 2 * r * deriv ψ r + q r * ψ r
      with hLψ
    have hLnear : ∀ r ∈ Ioo 0 (2 * r₁), Lψ r = 0 := fun r hr ↦ by
      have hev := hnear r hr
      simp only [hLψ, hev.deriv_eq, hev.deriv.deriv_eq, hev.eq_of_nhds]
      exact hφ₀ode r
    have hLfar : ∀ r, R / 2 < r → Lψ r = 0 := fun r hr ↦ by
      have hev := hfar r hr
      simp only [hLψ, hev.deriv_eq, hev.deriv.deriv_eq, hev.eq_of_nhds, deriv_const']
      ring
    have hrad (r : ℝ) : Lψ r = r ^ (l + 2) * (4 * r ^ 2 * deriv (deriv FW) (r ^ 2) +
        (4 * l + 6) * deriv FW (r ^ 2) + μ * FW (r ^ 2)) := by
      rw [← radial_pow_mul_comp_sq_add (hFW.of_le (by simp)) l μ r]
    have hK0 : ∃ δ > 0, ∀ s ∈ Ioo 0 δ,
        4 * s * deriv (deriv FW) s + (4 * l + 6) * deriv FW s + μ * FW s = 0 := by
      refine ⟨(2 * r₁) ^ 2, by have := hr₁.1; positivity, fun s hs ↦ ?_⟩
      have hsr : √s ∈ Ioo 0 (2 * r₁) :=
        ⟨Real.sqrt_pos.mpr hs.1, (Real.sqrt_lt' (by linarith [hr₁.1])).mpr hs.2⟩
      have h := hLnear (√s) hsr
      rw [hrad, Real.sq_sqrt hs.1.le] at h
      exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hsr.1.ne')
    have h1 : ∫ r in Ioo 0 R, Lψ r * f r = 0 := by
      refine Eq.trans ?_ (hweak FW hFW χ.hasCompactSupport.mul_right hFWsupp hK0)
      refine setIntegral_congr_ae measurableSet_Ioo ?_
      filter_upwards [hcf'] with r hr hrI
      rw [← hr hrI, hrad]
    set b := 3 * R / 4 with hb
    have hr₁b : r₁ ≤ b := by linarith [hr₁.2]
    have hIcc : Icc r₁ b ⊆ Ioo 0 R := Icc_subset_Ioo hr₁.1 (by linarith)
    have h2 : ∫ r in Ioo 0 R, Lψ r * f r = ∫ r in r₁..b, Lψ r * f r := by
      rw [intervalIntegral.integral_of_le hr₁b]
      refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioo
        (Ioc_subset_Icc_self.trans hIcc) fun x hx ↦ ?_
      rcases le_or_gt x r₁ with hxr | hxr
      · rw [hLnear x ⟨hx.1.1, by linarith [hr₁.1]⟩, zero_mul]
      · rw [hLfar x (by linarith [lt_of_not_ge fun h ↦ hx.2 ⟨hxr, h⟩]), zero_mul]
    set Λ : ℝ → ℝ := fun r ↦ r ^ 2 * deriv ψ r * f r - ψ r * (r ^ 2 * deriv f r) with hΛ
    have hΛd : ∀ x ∈ uIcc r₁ b, HasDerivAt Λ (Lψ x * f x) x := by
      intro x hx
      have hxI := hIcc (by rwa [uIcc_of_le hr₁b] at hx)
      obtain ⟨hψ1, hψ2⟩ := hasDerivAt_deriv_of_contDiff hψC x
      convert (((hasDerivAt_sq x).mul hψ2).mul (hf x hxI).1).sub (hψ1.mul (hf x hxI).2) using 1
      simp only [hLψ, Pi.mul_apply]
      ring
    have hint : IntervalIntegrable (fun r ↦ Lψ r * f r) volume r₁ b := by
      have h1 : Continuous (deriv ψ) := hψC.continuous_deriv (by simp)
      have h2 : Continuous (deriv (deriv ψ)) := (hψC.iterate_deriv 1).continuous_deriv (by simp)
      have hLc : Continuous Lψ := by simp only [hLψ]; fun_prop
      exact (hLc.continuousOn.mul (hfcont.mono hIcc)).intervalIntegrable_of_Icc hr₁b
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hΛd hint
    have hΛb : Λ b = 0 := by
      have hev := hfar b (by linarith)
      simp only [hΛ, hev.deriv_eq, hev.eq_of_nhds, deriv_const']
      ring
    have hΛr₁ : Λ r₁ = r₁ ^ 2 * (deriv φ₀ r₁ * f r₁ - φ₀ r₁ * deriv f r₁) := by
      have hev := hnear r₁ ⟨hr₁.1, by linarith [hr₁.1]⟩
      simp only [hΛ, hev.deriv_eq, hev.eq_of_nhds]
      ring
    rw [← hΛr₁]
    linarith [h1, h2, hftc, hΛb]
  -- near the origin `f` is a multiple of `φ₀`
  obtain ⟨δ₀, hδ₀, hpos⟩ := exists_radialSolution_pos l μ
  set δ := min (R / 4) δ₀ with hδ
  have hδpos : 0 < δ := lt_min (by positivity) hδ₀
  have hδR : δ ≤ R / 4 := min_le_left _ _
  have hφ₀pos : ∀ r ∈ Ioo 0 δ, 0 < φ₀ r := fun r hr ↦
    hpos r ⟨hr.1, hr.2.trans_le (min_le_right _ _)⟩
  have hsubδ : Ioo 0 δ ⊆ Ioo 0 R := Ioo_subset_Ioo_right (by linarith)
  set Q : ℝ → ℝ := fun r ↦ f r / φ₀ r with hQ
  have hQd : ∀ r ∈ Ioo 0 δ, HasDerivAt Q 0 r := fun r hr ↦ by
    have hw := (mul_eq_zero.mp (hW r ⟨hr.1, hr.2.trans_le hδR⟩)).resolve_left
      (pow_ne_zero 2 hr.1.ne')
    refine (((hf r (hsubδ hr)).1).div (hφ₀d r).1 (hφ₀pos r hr).ne').congr_deriv ?_
    exact div_eq_zero_iff.2 (Or.inl (by linear_combination -hw))
  have hQconst : ∀ x ∈ Ioo 0 δ, ∀ y ∈ Ioo 0 δ, Q x = Q y := fun x hx y hy ↦
    isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun r hr ↦ (hQd r hr).differentiableAt.differentiableWithinAt)
      (fun r hr ↦ (hQd r hr).deriv) hx hy
  set A := Q (δ / 2) with hA
  have hδ2 : δ / 2 ∈ Ioo 0 δ := ⟨by positivity, by linarith⟩
  have hfA : ∀ r ∈ Ioo 0 δ, f r = A * φ₀ r := fun r hr ↦ by
    rw [hA, ← hQconst r hr _ hδ2]
    exact (div_mul_cancel₀ _ (hφ₀pos r hr).ne').symm
  clear_value A
  -- second derivative of `f`
  set f₂ : ℝ → ℝ := fun r ↦ (-(q r * f r) - 2 * r * deriv f r) / r ^ 2 with hf₂
  have hf2 : ∀ r ∈ Ioo 0 R, HasDerivAt (deriv f) (f₂ r) r := fun r hr ↦ by
    have hev : deriv f =ᶠ[𝓝 r] fun s ↦ s ^ 2 * deriv f s / s ^ 2 :=
      eventually_of_mem (Ioi_mem_nhds hr.1) fun s (hs : 0 < s) ↦
        (mul_div_cancel_left₀ _ (pow_pos hs 2).ne').symm
    refine (((hf r hr).2.div (hasDerivAt_sq r) (pow_ne_zero 2 hr.1.ne')).congr_of_eventuallyEq
      hev).congr_deriv ?_
    simp only [hf₂]
    field_simp
  -- uniqueness for the radial equation
  set d : ℝ → ℝ := fun r ↦ f r - A * φ₀ r with hd
  have hdode : ∀ x ∈ Ioo 0 R, x ^ 2 * (f₂ x - A * deriv (deriv φ₀) x) +
      2 * x * (deriv f x - A * deriv φ₀ x) + (μ * x ^ 2 - l * (l + 1)) * d x = 0 := by
    intro x hx
    have h0 := hφ₀ode x
    have hf2x : x ^ 2 * f₂ x = -(q x * f x) - 2 * x * deriv f x := by
      simp only [hf₂]
      field_simp [hx.1.ne']
    simp only [hd, hq] at h0 hf2x ⊢
    linear_combination hf2x - A * h0
  have hloc : f =ᶠ[𝓝 (δ / 2)] fun s ↦ A * φ₀ s :=
    eventually_of_mem (isOpen_Ioo.mem_nhds hδ2) hfA
  have hzero := eqOn_zero_of_radial_ode (h := d)
    (fun x hx ↦ ((hf x hx).1).sub ((hφ₀d x).1.const_mul A))
    (fun x hx ↦ (hf2 x hx).sub ((hφ₀d x).2.const_mul A)) hdode (hsubδ hδ2)
    (by simp only [hd, hfA _ hδ2, sub_self])
    (by rw [hloc.deriv_eq, deriv_const_mul _ (hφ₀d _).1.differentiableAt, sub_self])
  refine ⟨A, ?_⟩
  filter_upwards [hcf, ae_restrict_mem measurableSet_Ioo] with r hr hrI
  rw [hr]
  exact sub_eq_zero.mp (hzero r hrI)

/-- **The radial operator against the regular solution on `[0, R]`.** For `φ r = r^l G(r²)`
with `G` smooth, `∫₀^R ((r² φ')' + (μ r² - l (l + 1)) φ) f dr`, where `f` is the regular radial
solution, reduces to the boundary term `R² (φ'(R) f(R) - φ(R) f'(R))`: `f` solves the equation
and the weight `r²` kills the term at the origin. -/
theorem integral_radial_mul_radialSolution (l : ℕ) (μ : ℝ) {R : ℝ} (hR : 0 ≤ R)
    {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) :
    ∫ r in Ioo 0 R, r ^ (l + 2) * (4 * r ^ 2 * deriv (deriv G) (r ^ 2) +
        (4 * l + 6) * deriv G (r ^ 2) + μ * G (r ^ 2)) * radialSolution l μ r =
      R ^ 2 * (deriv (fun s ↦ s ^ l * G (s ^ 2)) R * radialSolution l μ R -
        R ^ l * G (R ^ 2) * deriv (radialSolution l μ) R) := by
  set φ : ℝ → ℝ := fun s ↦ s ^ l * G (s ^ 2) with hφ
  have hφC : ContDiff ℝ ∞ φ := (contDiff_id.pow l).mul (hG.comp (contDiff_id.pow 2))
  set j := radialSolution l μ with hj
  have hjC : ContDiff ℝ ∞ j := contDiff_radialSolution l μ
  set Λ : ℝ → ℝ := fun r ↦ r ^ 2 * deriv φ r * j r - φ r * (r ^ 2 * deriv j r) with hΛ
  have hΛd (r : ℝ) : HasDerivAt Λ (r ^ (l + 2) * (4 * r ^ 2 * deriv (deriv G) (r ^ 2) +
      (4 * l + 6) * deriv G (r ^ 2) + μ * G (r ^ 2)) * j r) r := by
    obtain ⟨hφ1, hφ2⟩ := hasDerivAt_deriv_of_contDiff hφC r
    obtain ⟨hj1, hj2⟩ := hasDerivAt_deriv_of_contDiff hjC r
    have h := (((hasDerivAt_sq r).mul hφ2).mul hj1).sub (hφ1.mul ((hasDerivAt_sq r).mul hj2))
    have hode := radialSolution_ode l μ r
    have hrad := radial_pow_mul_comp_sq_add (hG.of_le (by simp)) l μ r
    convert h using 1
    rw [← hrad]
    simp only [hj, hφ, Pi.mul_apply] at hode ⊢
    linear_combination (r ^ l * G (r ^ 2)) * hode
  have h1 : Continuous (deriv G) := hG.continuous_deriv (by simp)
  have h2 : Continuous (deriv (deriv G)) := (hG.iterate_deriv 1).continuous_deriv (by simp)
  have hcont : Continuous fun r : ℝ ↦ r ^ (l + 2) * (4 * r ^ 2 * deriv (deriv G) (r ^ 2) +
      (4 * l + 6) * deriv G (r ^ 2) + μ * G (r ^ 2)) * j r := by
    have hjc : Continuous j := hjC.continuous
    fun_prop
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hR,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ ↦ hΛd r)
      (hcont.intervalIntegrable _ _)]
  simp only [hΛ, hφ]
  ring

/-- The reduced function `G_l(t)` is positive for `t ≤ 0`: every term of its series is
nonnegative there and the first one is positive. -/
theorem reducedSphericalBesselJSq_pos_of_nonpos (l : ℕ) {t : ℝ} (ht : t ≤ 0) :
    0 < reducedSphericalBesselJSq l t := by
  have hD (k : ℕ) : (0 : ℝ) < k.factorial * ((2 * l + 2 * k + 1).doubleFactorial : ℝ) := by
    have h2 := Nat.doubleFactorial_pos (2 * l + 2 * k + 1)
    positivity
  have hterm (k : ℕ) : reducedSphericalBesselCoeff l k * t ^ k =
      (-t / 2) ^ k / (k.factorial * ((2 * l + 2 * k + 1).doubleFactorial : ℝ)) := by
    unfold reducedSphericalBesselCoeff
    rw [div_mul_eq_mul_div, ← mul_pow]
    ring
  have hsum : Summable fun k ↦ reducedSphericalBesselCoeff l k * t ^ k := by
    refine Summable.of_norm_bounded (Real.summable_pow_div_factorial (|t| / 2)) fun k ↦ ?_
    rw [hterm, Real.norm_eq_abs, abs_div, abs_pow, abs_div, abs_neg, abs_two,
      abs_of_pos (hD k)]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (le_mul_of_one_le_right (by positivity) (by exact_mod_cast Nat.doubleFactorial_pos _))
  refine hsum.tsum_pos (fun k ↦ ?_) 0 (by rw [hterm]; simpa using hD 0)
  rw [hterm]
  exact div_nonneg (pow_nonneg (by linarith) k) (hD k).le

/-- The radial derivative of the regular solution:
`r φ'(r) = r^l (l G_l(μ r²) - μ r² G_{l+1}(μ r²))`. -/
theorem mul_deriv_radialSolution (l : ℕ) (μ r : ℝ) :
    r * deriv (radialSolution l μ) r = r ^ l * (l * reducedSphericalBesselJSq l (μ * r ^ 2) -
      μ * r ^ 2 * reducedSphericalBesselJSq (l + 1) (μ * r ^ 2)) := by
  have hF : Differentiable ℝ fun s ↦ reducedSphericalBesselJSq l (μ * s) :=
    fun s ↦ (hasDerivAt_reduced_mul l μ s).differentiableAt
  have h := mul_deriv_pow_mul_comp_sq hF l r
  have hfun : radialSolution l μ = fun s ↦ s ^ l * reducedSphericalBesselJSq l (μ * s ^ 2) :=
    rfl
  rw [hfun, h, (hasDerivAt_reduced_mul l μ (r ^ 2)).deriv, deriv_reducedSphericalBesselJSq]
  ring

/-- Integration by parts against a test with compact support in `(0, R)`:
`∫₀^R U φ' = -∫₀^R U' φ` for `U` with continuous derivative `U'`. -/
theorem setIntegral_mul_deriv_eq_neg {R : ℝ} (hR : 0 < R) {U U' φ : ℝ → ℝ}
    (hU : ∀ r, HasDerivAt U (U' r) r) (hU' : Continuous U') (hφ : ContDiff ℝ ∞ φ)
    (hsupp : tsupport φ ⊆ Ioo 0 R) :
    ∫ r in Ioo 0 R, U r * deriv φ r = -∫ r in Ioo 0 R, U' r * φ r := by
  have hφ0 : φ 0 = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ lt_irrefl _ (hsupp h).1
  have hφR : φ R = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ lt_irrefl _ (hsupp h).2
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := R)
    (u := U) (v := φ) (u' := U') (v' := deriv φ) (fun r _ ↦ hU r)
    (fun r _ ↦ (hφ.differentiable (by simp) r).hasDerivAt) (hU'.intervalIntegrable _ _)
    ((hφ.continuous_deriv (by simp)).intervalIntegrable _ _)
  rw [hφ0, hφR, mul_zero, mul_zero, sub_zero, zero_sub,
    intervalIntegral.integral_of_le hR.le, intervalIntegral.integral_of_le hR.le,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo] at hibp
  exact hibp

/-- **Regular harmonic profiles.** Let `l ≥ 1` and let `α`, `β` be locally integrable on
`(0, R)` with `r² α` integrable there. If `(r² α)' = r β` and `(r β)' = l (l + 1) α` in the sense
of distributions on `(0, R)`, then `α = C r^{l-1}` and `β = C (l + 1) r^{l-1}` almost
everywhere. The solutions of the system are `r² α = C r^{l+1} + D r^{-l}`, and the integrability
of `r² α` at the origin excludes `r^{-l}`. -/
theorem ae_eq_pow_of_weak_harmonic {R : ℝ} (hR : 0 < R) {l : ℕ} (hl : 1 ≤ l) {α β : ℝ → ℝ}
    (hα : LocallyIntegrableOn α (Ioo 0 R)) (hβ : LocallyIntegrableOn β (Ioo 0 R))
    (hαi : IntegrableOn (fun r ↦ r ^ 2 * α r) (Ioo 0 R))
    (h1 : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioo 0 R →
      ∫ r in Ioo 0 R, r ^ 2 * α r * deriv φ r = -∫ r in Ioo 0 R, r * β r * φ r)
    (h2 : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioo 0 R →
      ∫ r in Ioo 0 R, r * β r * deriv φ r = -∫ r in Ioo 0 R, l * (l + 1) * α r * φ r) :
    ∃ C : ℝ, α =ᵐ[volume.restrict (Ioo 0 R)] (fun r ↦ C * r ^ (l - 1)) ∧
      β =ᵐ[volume.restrict (Ioo 0 R)] (fun r ↦ C * (l + 1) * r ^ (l - 1)) := by
  set L : ℝ := l * (l + 1) with hL
  have htest {q φ : ℝ → ℝ} (hq : LocallyIntegrableOn q (Ioo 0 R)) (hφc : Continuous φ)
      (hφcs : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioo 0 R) :
      Integrable (fun r ↦ q r * φ r) :=
    Evolution.HasWeakTimeDerivativeOn.integrable_mul_test hq hφc hφcs hφs
  -- the profile `r α` solves the radial equation with `q = -l (l + 1)`
  set c : ℝ → ℝ := fun r ↦ r * α r with hc
  have hcl : LocallyIntegrableOn c (Ioo 0 R) :=
    hα.continuousOn_mul (g := fun r : ℝ ↦ r) continuousOn_id isOpen_Ioo.isLocallyClosed
  have hweak : ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ Ioo 0 R →
      ∫ r, c r * (r ^ 2 * deriv (deriv χ) r + 2 * r * deriv χ r + (fun _ ↦ -L) r * χ r) = 0 := by
    intro χ hχ hχcs hχs
    set φ : ℝ → ℝ := fun r ↦ r * χ r with hφ
    have hχ1 : ContDiff ℝ ∞ (deriv χ) := hχ.iterate_deriv 1
    have hφd : deriv φ = fun r ↦ χ r + r * deriv χ r := funext fun r ↦
      ((hasDerivAt_id' r).fun_mul (hχ.differentiable (by simp) r).hasDerivAt).deriv.trans (by ring)
    have hφdd : deriv (deriv φ) = fun r ↦ 2 * deriv χ r + r * deriv (deriv χ) r := by
      rw [hφd]
      exact funext fun r ↦ ((hχ.differentiable (by simp) r).hasDerivAt.fun_add
        ((hasDerivAt_id' r).fun_mul (hχ1.differentiable (by simp) r).hasDerivAt)).deriv.trans
          (by ring)
    have hφC : ContDiff ℝ ∞ φ := contDiff_id.mul hχ
    have hφcs : HasCompactSupport φ := hχcs.mul_left
    have hφs : tsupport φ ⊆ Ioo 0 R := tsupport_mul_subset_right.trans hχs
    have hA := h1 (deriv φ) (hφC.iterate_deriv 1) hφcs.deriv (tsupport_deriv_subset.trans hφs)
    have hB := h2 φ hφC hφcs hφs
    rw [integral_radialOp_eq_setIntegral hχs]
    have hddφ : Continuous fun r ↦ r ^ 2 * deriv (deriv φ) r := by
      rw [hφdd]
      exact (continuous_pow 2).mul ((continuous_const.mul hχ1.continuous).add
        (continuous_id.mul (hχ1.continuous_deriv (by simp))))
    have hI1 : Integrable fun r ↦ α r * (r ^ 2 * deriv (deriv φ) r) :=
      htest hα hddφ (hφcs.deriv.deriv.mul_left)
        (tsupport_mul_subset_right.trans (tsupport_deriv_subset.trans
          (tsupport_deriv_subset.trans hφs)))
    have hI2 : Integrable fun r ↦ α r * (L * φ r) :=
      htest hα (continuous_const.mul hφC.continuous) hφcs.mul_left
        (tsupport_mul_subset_right.trans hφs)
    calc _ = ∫ r in Ioo 0 R, (α r * (r ^ 2 * deriv (deriv φ) r) - α r * (L * φ r)) := by
          refine setIntegral_congr_fun measurableSet_Ioo fun r _ ↦ ?_
          rw [hφdd]
          simp only [hc, hφ]
          ring
      _ = (∫ r in Ioo 0 R, r ^ 2 * α r * deriv (deriv φ) r) -
            ∫ r in Ioo 0 R, L * α r * φ r := by
          rw [integral_sub hI1.integrableOn hI2.integrableOn]
          congr 1 <;> exact integral_congr_ae (ae_of_all _ fun r ↦ by ring)
      _ = 0 := by rw [hA, hB]; ring
  obtain ⟨f, hcf, hf⟩ := exists_hasDerivAt_of_weak_radial hR continuousOn_const hcl hweak
  -- the Wronskian with `r^l` is constant
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  set W : ℝ → ℝ := fun r ↦ (m + 1) * r ^ (m + 2) * f r - r ^ (m + 1) * (r ^ 2 * deriv f r)
    with hW
  have hWd : ∀ r ∈ Ioo 0 R, HasDerivAt W 0 r := fun r hr ↦ by
    convert (((hasDerivAt_pow (m + 2) r).const_mul ((m : ℝ) + 1)).mul (hf r hr).1).sub
      ((hasDerivAt_pow (m + 1) r).mul (hf r hr).2) using 1
    simp only [Nat.add_sub_cancel, hL]
    push_cast
    ring
  obtain ⟨W₀, hW₀⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun r hr ↦ (hWd r hr).differentiableAt.differentiableWithinAt)
    (fun r hr ↦ (hWd r hr).deriv)
  -- the quotient by `r^l`
  set D : ℝ := W₀ / (2 * m + 3) with hD
  set g : ℝ → ℝ := fun r ↦ f r / r ^ (m + 1) - D * (r ^ (2 * m + 3))⁻¹ with hg
  have hgd : ∀ r ∈ Ioo 0 R, HasDerivAt g 0 r := fun r hr ↦ by
    have hr0 : r ≠ 0 := hr.1.ne'
    convert ((hf r hr).1.div (hasDerivAt_pow (m + 1) r) (pow_ne_zero _ hr0)).sub
      (((hasDerivAt_pow (2 * m + 3) r).inv (pow_ne_zero _ hr0)).const_mul D) using 1
    have hWr := hW₀ r hr
    simp only [hW] at hWr
    simp only [Nat.add_sub_cancel, hD]
    field_simp
    push_cast
    ring_nf
    ring_nf at hWr
    linear_combination (2 * (m : ℝ) + 3) * r ^ 4 * r ^ (m * 4) * hWr
  obtain ⟨C, hC⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun r hr ↦ (hgd r hr).differentiableAt.differentiableWithinAt)
    (fun r hr ↦ (hgd r hr).deriv)
  have hfeq : ∀ r ∈ Ioo 0 R, f r = C * r ^ (m + 1) + D * (r ^ (m + 2))⁻¹ := fun r hr ↦ by
    have h := hC r hr
    have hr0 : r ≠ 0 := hr.1.ne'
    simp only [hg] at h
    rw [← h]
    field_simp
    ring
  -- integrability at the origin excludes `r^{-l}`
  have hD0 : D = 0 := by
    by_contra hD0
    have hpoly : IntegrableOn (fun r ↦ C * r ^ (m + 2)) (Ioo 0 R) :=
      ((continuous_const.mul (continuous_pow _)).integrableOn_Icc (a := 0) (b := R)).mono_set
        Ioo_subset_Icc_self
    have hae : (fun r ↦ r ^ 2 * α r - C * r ^ (m + 2)) =ᵐ[volume.restrict (Ioo 0 R)]
        fun r ↦ D * r ^ (-((m : ℝ) + 1)) := by
      filter_upwards [hcf, ae_restrict_mem measurableSet_Ioo] with r (hr : r * α r = f r) hrI
      rw [Real.rpow_neg hrI.1.le, show ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast, show r ^ 2 * α r = r * (r * α r) by ring, hr, hfeq r hrI]
      field_simp [hrI.1.ne']
      ring
    have hint : IntegrableOn (fun r ↦ D⁻¹ * (D * r ^ (-((m : ℝ) + 1)))) (Ioo 0 R) :=
      ((hαi.sub hpoly).congr_fun_ae hae).const_mul D⁻¹
    replace hint : IntegrableOn (fun r ↦ r ^ (-((m : ℝ) + 1))) (Ioo 0 R) :=
      hint.congr_fun (fun r _ ↦ inv_mul_cancel_left₀ hD0 _) measurableSet_Ioo
    linarith [(intervalIntegral.integrableOn_Ioo_rpow_iff hR).mp hint,
      (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hαeq : α =ᵐ[volume.restrict (Ioo 0 R)] fun r ↦ C * r ^ (m + 1 - 1) := by
    filter_upwards [hcf, ae_restrict_mem measurableSet_Ioo] with r (hr : r * α r = f r) hrI
    refine mul_left_cancel₀ hrI.1.ne' ?_
    rw [hr, hfeq r hrI, hD0, Nat.add_sub_cancel]
    ring
  refine ⟨C, hαeq, ?_⟩
  -- the polar profile from `(r² α)' = r β`
  set q : ℝ → ℝ := fun r ↦ r * β r - C * ((m : ℝ) + 2) * r ^ (m + 1) with hq
  have hql : LocallyIntegrableOn q (Ioo 0 R) :=
    (hβ.continuousOn_mul (g := fun r : ℝ ↦ r) continuousOn_id isOpen_Ioo.isLocallyClosed).sub
      ((continuous_const.mul (continuous_pow _)).locallyIntegrable.locallyIntegrableOn _)
  have hq0 := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hql fun φ hφ hφcs hφs ↦ by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioo 0 R) fun x hx ↦ by
      rw [image_eq_zero_of_notMem_tsupport fun h ↦ hx (hφs h), zero_smul]]
    -- integration by parts against `C r^{l+1}`
    have hibp := setIntegral_mul_deriv_eq_neg hR (U := fun r ↦ C * r ^ (m + 2))
      (U' := fun r ↦ C * ((m : ℝ) + 2) * r ^ (m + 1))
      (fun r ↦ ((hasDerivAt_pow (m + 2) r).const_mul C).congr_deriv (by push_cast; ring))
      (by fun_prop) hφ hφs
    have hA' : ∫ r in Ioo 0 R, r ^ 2 * α r * deriv φ r =
        ∫ r in Ioo 0 R, C * r ^ (m + 2) * deriv φ r := by
      refine setIntegral_congr_ae measurableSet_Ioo ?_
      filter_upwards [(ae_restrict_iff' measurableSet_Ioo).mp hαeq] with r hr hrI
      rw [hr hrI, Nat.add_sub_cancel]
      ring
    have hIβ : IntegrableOn (fun r ↦ r * β r * φ r) (Ioo 0 R) := by
      have h := htest hβ (continuous_id.mul hφ.continuous) hφcs.mul_left
        (tsupport_mul_subset_right.trans hφs)
      exact (h.congr (ae_of_all _ fun r ↦ by simp only [Pi.mul_apply, id]; ring)).integrableOn
    have hIp : IntegrableOn (fun r ↦ C * ((m : ℝ) + 2) * r ^ (m + 1) * φ r) (Ioo 0 R) :=
      ((continuous_const.mul (continuous_pow _)).mul hφ.continuous).integrableOn_Icc.mono_set
        Ioo_subset_Icc_self
    calc ∫ r in Ioo 0 R, φ r • q r
        = (∫ r in Ioo 0 R, r * β r * φ r) -
            ∫ r in Ioo 0 R, C * ((m : ℝ) + 2) * r ^ (m + 1) * φ r := by
          rw [← integral_sub hIβ hIp]
          exact integral_congr_ae (ae_of_all _ fun r ↦ by simp only [hq, smul_eq_mul]; ring)
      _ = 0 := by
          rw [← neg_neg (∫ r in Ioo 0 R, r * β r * φ r), ← h1 φ hφ hφcs hφs, hA', hibp, neg_neg,
            sub_self]
  filter_upwards [(ae_restrict_iff' measurableSet_Ioo).mpr hq0,
    ae_restrict_mem measurableSet_Ioo] with r hr hrI
  refine mul_left_cancel₀ hrI.1.ne' ?_
  simp only [hq, Nat.add_sub_cancel] at hr ⊢
  push_cast
  linear_combination hr

/-- Tests with compact support in `(0, R)` against a locally integrable function are integrable
on `(0, R)`. -/
theorem integrableOn_mul_test {R : ℝ} {q ψ : ℝ → ℝ} (hq : LocallyIntegrableOn q (Ioo 0 R))
    (hψ : Continuous ψ) (hψcs : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ Ioo 0 R) :
    IntegrableOn (fun r ↦ q r * ψ r) (Ioo 0 R) :=
  (Evolution.HasWeakTimeDerivativeOn.integrable_mul_test hq hψ hψcs hψs).integrableOn

/-- If `r a` has the weak derivative `a + e` on `(0, R)` and `a` agrees almost everywhere with a
`C¹` function `g`, then `e = r g'` almost everywhere on `(0, R)`. -/
theorem ae_eq_mul_deriv_of_weak {R : ℝ} (hR : 0 < R) {a e g : ℝ → ℝ}
    (he : LocallyIntegrableOn e (Ioo 0 R))
    (hg : ContDiff ℝ 1 g) (hag : a =ᵐ[volume.restrict (Ioo 0 R)] g)
    (hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioo 0 R →
      ∫ r in Ioo 0 R, r * a r * deriv φ r = -∫ r in Ioo 0 R, (a r + e r) * φ r) :
    e =ᵐ[volume.restrict (Ioo 0 R)] fun r ↦ r * deriv g r := by
  have hg1 : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have hgd (r : ℝ) : HasDerivAt g (deriv g r) r := (hg.differentiable one_ne_zero r).hasDerivAt
  set q : ℝ → ℝ := fun r ↦ e r - r * deriv g r with hq
  have hql : LocallyIntegrableOn q (Ioo 0 R) :=
    he.sub ((continuous_id.mul hg1).locallyIntegrable.locallyIntegrableOn _)
  have hq0 := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hql fun φ hφ hφcs hφs ↦ by
    have hzero {x : ℝ} (hx : x ∉ Ioo 0 R) : φ x • q x = 0 := by
      rw [image_eq_zero_of_notMem_tsupport fun h ↦ hx (hφs h), zero_smul]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioo 0 R) fun x hx ↦ hzero hx]
    have hw := hweak φ hφ hφcs hφs
    have h1 : ∫ r in Ioo 0 R, r * a r * deriv φ r = ∫ r in Ioo 0 R, r * g r * deriv φ r := by
      refine setIntegral_congr_ae measurableSet_Ioo ?_
      filter_upwards [(ae_restrict_iff' measurableSet_Ioo).mp hag] with r hr hrI
      rw [hr hrI]
    have h2 : ∫ r in Ioo 0 R, (a r + e r) * φ r = ∫ r in Ioo 0 R, (g r + e r) * φ r := by
      refine setIntegral_congr_ae measurableSet_Ioo ?_
      filter_upwards [(ae_restrict_iff' measurableSet_Ioo).mp hag] with r hr hrI
      rw [hr hrI]
    have h3 := setIntegral_mul_deriv_eq_neg hR (U := fun r ↦ r * g r)
      (U' := fun r ↦ g r + r * deriv g r)
      (fun r ↦ ((hasDerivAt_id' r).mul (hgd r)).congr_deriv (by ring))
      (hg.continuous.add (continuous_id.mul hg1)) hφ hφs
    rw [h1, h2, h3] at hw
    have hIg : IntegrableOn (fun r ↦ (g r + r * deriv g r) * φ r) (Ioo 0 R) :=
      ((hg.continuous.add (continuous_id.mul hg1)).mul hφ.continuous).integrableOn_Icc.mono_set
        Ioo_subset_Icc_self
    have hIe : IntegrableOn (fun r ↦ (g r + e r) * φ r) (Ioo 0 R) := integrableOn_mul_test
      ((hg.continuous.locallyIntegrable.locallyIntegrableOn _).add he) hφ.continuous hφcs hφs
    have h4 : ∫ r in Ioo 0 R, φ r • q r =
        (∫ r in Ioo 0 R, (g r + e r) * φ r) - ∫ r in Ioo 0 R, (g r + r * deriv g r) * φ r := by
      rw [← integral_sub hIe hIg]
      exact integral_congr_ae (ae_of_all _ fun r ↦ by simp only [hq, smul_eq_mul]; ring)
    rw [h4]
    linarith
  filter_upwards [(ae_restrict_iff' measurableSet_Ioo).mpr hq0] with r hr
  simp only [hq] at hr
  linarith

/-- A smooth function `K` with compact support in `(-∞, R²)` that vanishes on `(0, δ)` gives the
test function `r ↦ r^m K(r²)` on `(0, ∞)`, extended by zero, smooth with compact support in
`(0, R)`. -/
theorem exists_test_pow_mul_comp_sq {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) {K : ℝ → ℝ}
    (hK : ContDiff ℝ ∞ K) (hKcs : HasCompactSupport K) (hKsupp : tsupport K ⊆ Iio (R ^ 2))
    (hK0 : ∀ s ∈ Ioo 0 δ, K s = 0) (m : ℕ) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ioo 0 R ∧
      ∀ r, 0 < r → φ r = r ^ m * K (r ^ 2) := by
  set φ : ℝ → ℝ := fun r ↦ if 0 < r then r ^ m * K (r ^ 2) else 0 with hφ
  have hlow : ∀ r < √δ, φ r = 0 := fun r hr ↦ by
    simp only [hφ]
    split_ifs with h
    · rw [hK0 _ ⟨by positivity, (Real.lt_sqrt h.le).mp hr⟩, mul_zero]
    · rfl
  obtain ⟨s₁, hs₁, hKs₁⟩ : ∃ s₁ < R ^ 2, ∀ s, s₁ < s → K s = 0 := by
    rcases (tsupport K).eq_empty_or_nonempty with he | hne
    · exact ⟨0, by positivity, fun s _ ↦ image_eq_zero_of_notMem_tsupport (by simp [he])⟩
    · obtain ⟨s₀, hs₀, hmax⟩ := hKcs.exists_isMaxOn hne continuous_id.continuousOn
      refine ⟨max s₀ 0, max_lt (hKsupp hs₀) (by positivity), fun s hs ↦ ?_⟩
      refine image_eq_zero_of_notMem_tsupport fun h ↦ ?_
      have h2 : s ≤ s₀ := hmax h
      linarith [le_max_left s₀ 0]
  have hhigh : ∀ r, √s₁ < r → φ r = 0 := fun r hr ↦ by
    have hr0 : 0 < r := (Real.sqrt_nonneg _).trans_lt hr
    simp only [hφ, hr0, ↓reduceIte, hKs₁ _ ((Real.sqrt_lt' hr0).mp hr), mul_zero]
  have hts : tsupport φ ⊆ Icc (√δ) (√s₁) := closure_minimal (fun r hr ↦
    ⟨not_lt.mp fun h ↦ hr (hlow r h), not_lt.mp fun h ↦ hr (hhigh r h)⟩) isClosed_Icc
  refine ⟨φ, ?_, isCompact_Icc.of_isClosed_subset (isClosed_tsupport φ) hts,
    hts.trans fun r hr ↦ ⟨(Real.sqrt_pos.mpr hδ).trans_le hr.1,
      hr.2.trans_lt ((Real.sqrt_lt' hR).mpr hs₁)⟩, fun r hr ↦ by simp only [hφ, hr, ↓reduceIte]⟩
  refine contDiff_iff_contDiffAt.mpr fun r ↦ ?_
  by_cases hr : r < √δ
  · exact contDiffAt_const.congr_of_eventuallyEq (eventually_of_mem (Iio_mem_nhds hr) hlow)
  · have hr0 : 0 < r := (Real.sqrt_pos.mpr hδ).trans_le (not_lt.mp hr)
    refine ((contDiff_id.pow m).mul (hK.comp (contDiff_id.pow 2))).contDiffAt.congr_of_eventuallyEq
      (eventually_of_mem (Ioi_mem_nhds hr0) fun t (ht : 0 < t) ↦ ?_)
    simp only [hφ, ht, ↓reduceIte, Function.comp_apply, id_eq]

end PDE.Analysis.SpecialFunctions
