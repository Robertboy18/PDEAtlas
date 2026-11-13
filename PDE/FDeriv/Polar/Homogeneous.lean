/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Polar.Profile
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Homogeneous polar profiles up to the horizontal boundary

A separated profile `f = χ(r) r^m g(β)`, with a cutoff `χ` vanishing near the origin and equal to
one beyond a radius `R`, is positively homogeneous of degree `m` outside the disk of radius `R`.
On the closed upper half-plane it agrees with the function built from the polar angle of the
point rotated by `-π/2`, shifted by `π/2`. That chart has its branch cut on the negative vertical
axis, so the representative is `C^n` on an open neighbourhood of the closed upper half-plane
whenever `χ` and `g` are `C^n` on the line. Compactness of a closed half annulus and the scaling
law then bound the derivatives.

## Main results

* `contDiffAt_polarCoord`: the forward polar chart is smooth on its source.
* `exists_contDiffOn_extension_profileFromPolar_cutoff_rpow_mul`: the `C^n` representative on an
  open neighbourhood of the closed upper half-plane.
* `exists_norm_iteratedFDeriv_profileFromPolar_cutoff_rpow_mul_le`: the decay
  `‖Dʲ f(x)‖ ≤ C (1 + |x|)^(m - j)` on the open upper half-plane.
* `exists_lipschitzOnWith_iteratedFDeriv_profileFromPolar_cutoff_rpow_mul`: for `m ≤ k + 1` the
  `k`-th derivative is Lipschitz on the open upper half-plane.
* `exists_norm_iteratedFDeriv_le_mul_rpow_of_hasCompactSupport`: the same weighted bound, with
  any exponent, for a compactly supported field.
-/

@[expose] public noncomputable section

open Set Filter Metric
open scoped Topology

namespace PDE.FDeriv

/-- On `[0, L]`, the weight `(1 + a)^s` is at least `(1 + L)^(-|s|)`. -/
private theorem one_le_rpow_abs_mul_rpow {a L s : ℝ} (ha : 0 ≤ a) (haL : a ≤ L) :
    1 ≤ (1 + L) ^ |s| * (1 + a) ^ s := by
  have h1a : 1 ≤ 1 + a := by linarith
  have hlow : (1 + L) ^ (-|s|) ≤ (1 + a) ^ s :=
    (Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by simp)).trans
      (Real.rpow_le_rpow_of_exponent_le h1a (neg_abs_le s))
  have hpos : 0 < (1 + L) ^ |s| := Real.rpow_pos_of_pos (by linarith) _
  calc
    (1 : ℝ) = (1 + L) ^ |s| * (1 + L) ^ (-|s|) := by
      rw [Real.rpow_neg (by linarith), mul_inv_cancel₀ hpos.ne']
    _ ≤ (1 + L) ^ |s| * (1 + a) ^ s := mul_le_mul_of_nonneg_left hlow hpos.le

/-- For `a ≥ 1`, the power `a^s` is at most `2^|s| (1 + a)^s`. -/
private theorem rpow_le_two_rpow_abs_mul_one_add_rpow {a : ℝ} (ha : 1 ≤ a) (s : ℝ) :
    a ^ s ≤ 2 ^ |s| * (1 + a) ^ s := by
  rcases le_or_gt 0 s with hs | hs
  · have h2 : (1 : ℝ) ≤ 2 ^ |s| := Real.one_le_rpow (by norm_num) (abs_nonneg s)
    calc
      a ^ s ≤ (1 + a) ^ s := Real.rpow_le_rpow (by linarith) (by linarith) hs
      _ = 1 * (1 + a) ^ s := (one_mul _).symm
      _ ≤ 2 ^ |s| * (1 + a) ^ s :=
        mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (by linarith) _)
  · have habs : |s| = -s := abs_of_neg hs
    have hle : (2 * a) ^ s ≤ (1 + a) ^ s :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) hs.le
    rw [Real.mul_rpow (by norm_num) (by linarith)] at hle
    have h2pos : 0 < (2 : ℝ) ^ (-s) := Real.rpow_pos_of_pos (by norm_num) _
    calc
      a ^ s = 2 ^ (-s) * (2 ^ s * a ^ s) := by
        rw [← mul_assoc, ← Real.rpow_add (by norm_num), neg_add_cancel, Real.rpow_zero,
          one_mul]
      _ ≤ 2 ^ |s| * (1 + a) ^ s := by
        rw [habs]
        exact mul_le_mul_of_nonneg_left hle h2pos.le

/-- The forward polar chart is `C^n` at every point of its source, for every order `n`. -/
theorem contDiffAt_polarCoord {n : WithTop ℕ∞} {p : ℝ × ℝ} (hp : p ∈ polarCoord.source) :
    ContDiffAt ℝ n polarCoord p := by
  have hq : polarCoord p ∈ polarCoord.target := polarCoord.map_source hp
  have hr : (polarCoord p).1 ≠ 0 := ne_of_gt hq.1
  have hderiv : HasFDerivAt (polarCoord.symm : ℝ × ℝ → ℝ × ℝ)
      (polarCoordSymmFDerivEquiv (polarCoord p) hr : (ℝ × ℝ) →L[ℝ] ℝ × ℝ) (polarCoord p) := by
    rw [polarCoordSymmFDerivEquiv_coe]
    exact hasFDerivAt_polarCoord_symm _
  have hsmooth : ContDiff ℝ n (polarCoord.symm : ℝ × ℝ → ℝ × ℝ) := by
    change ContDiff ℝ n (fun q : ℝ × ℝ ↦ (q.1 * Real.cos q.2, q.1 * Real.sin q.2))
    fun_prop
  exact polarCoord.symm.contDiffAt_symm hp hderiv hsmooth.contDiffAt

/-- The polar angle of the point rotated by `-π/2`, shifted by `π/2`: a chart angle whose branch
cut is the negative vertical axis. -/
private def rotatedAngle (x : ℝ^2) : ℝ :=
  (polarCoord (x 1, -x 0)).2 + Real.pi / 2

/-- On the closed upper half-plane away from the origin the rotated angle is the chart angle. -/
private theorem rotatedAngle_eq {x : ℝ^2} (hx : 0 ≤ x 1) (hne : x ≠ 0) :
    rotatedAngle x = (polarCoord (pointPair x)).2 := by
  let z : ℂ := Complex.equivRealProd.symm (pointPair x)
  have hw : Complex.equivRealProd.symm (x 1, -x 0) = -Complex.I * z := by
    apply Complex.ext <;>
      simp [z, Complex.equivRealProd_symm_apply, pointPair, CoordinateSystems.meridianR,
        CoordinateSystems.meridianZ]
  have hz : z ≠ 0 := by
    intro h0
    apply hne
    have hre : x 0 = 0 := by
      simpa [z, Complex.equivRealProd_symm_apply, pointPair, CoordinateSystems.meridianR,
        CoordinateSystems.meridianZ] using congrArg Complex.re h0
    have him : x 1 = 0 := by
      simpa [z, Complex.equivRealProd_symm_apply, pointPair, CoordinateSystems.meridianR,
        CoordinateSystems.meridianZ] using congrArg Complex.im h0
    ext i
    fin_cases i
    · exact hre
    · exact him
  have him : 0 ≤ z.im := by
    simpa [z, Complex.equivRealProd_symm_apply, pointPair, CoordinateSystems.meridianR,
      CoordinateSystems.meridianZ] using hx
  have hnonneg : 0 ≤ z.arg := Complex.arg_nonneg_iff.mpr him
  have harg : (-Complex.I * z).arg = (-Complex.I).arg + z.arg := by
    rw [Complex.arg_mul_eq_add_arg_iff (neg_ne_zero.mpr Complex.I_ne_zero) hz,
      Complex.arg_neg_I]
    constructor
    · linarith [Real.pi_pos]
    · linarith [Complex.arg_le_pi z, Real.pi_pos]
  simp only [rotatedAngle, polarCoord_apply]
  change (Complex.equivRealProd.symm (x 1, -x 0)).arg + Real.pi / 2 = z.arg
  rw [hw, harg, Complex.arg_neg_I]
  ring

/-- Positive dilations do not change the rotated angle. -/
private theorem rotatedAngle_smul {t : ℝ} (ht : 0 < t) (x : ℝ^2) :
    rotatedAngle (t • x) = rotatedAngle x := by
  have hw : Complex.equivRealProd.symm ((t • x) 1, -(t • x) 0) =
      (t : ℂ) * Complex.equivRealProd.symm (x 1, -x 0) := by
    apply Complex.ext <;> simp [Complex.equivRealProd_symm_apply]
  simp only [rotatedAngle, polarCoord_apply]
  rw [hw, Complex.arg_real_mul _ ht]

/-- The representative `χ(|x|) |x|^m g(rotated angle)` of a separated polar profile. -/
private def rep (χ g : ℝ → ℝ) (m : ℝ) (x : ℝ^2) : ℝ :=
  χ ‖x‖ * (‖x‖ ^ m * g (rotatedAngle x))

/-- The representative agrees with the profile on the closed upper half-plane. -/
private theorem rep_eqOn {χ g : ℝ → ℝ} (m : ℝ) (hχ0 : χ 0 = 0) :
    EqOn (rep χ g m) (profileFromPolar (fun r β ↦ χ r * (r ^ m * g β))) {x | 0 ≤ x 1} := by
  intro x hx
  by_cases hx0 : x = 0
  · subst hx0
    simp only [rep, profileFromPolar, polarCoord_pointPair_fst, norm_zero, hχ0, zero_mul]
  · simp only [rep, profileFromPolar, polarCoord_pointPair_fst, rotatedAngle_eq hx hx0]

/-- The open neighbourhood of the closed upper half-plane on which the representative is smooth:
the complement of the closed negative vertical axis together with a disk around the origin. -/
private def repDomain (ε : ℝ) : Set (ℝ^2) :=
  {x | 0 < x 1} ∪ {x | x 0 ≠ 0} ∪ ball 0 ε

/-- The domain `repDomain ε` is open. -/
private theorem isOpen_repDomain (ε : ℝ) : IsOpen (repDomain ε) := by
  have h1 : Continuous fun x : ℝ^2 ↦ x 1 := by fun_prop
  have h0 : Continuous fun x : ℝ^2 ↦ x 0 := by fun_prop
  exact ((isOpen_lt continuous_const h1).union (isOpen_ne_fun h0 continuous_const)).union
    isOpen_ball

/-- For `ε > 0` the closed upper half-plane `{x | 0 ≤ x 1}` lies in `repDomain ε`. -/
private theorem subset_repDomain {ε : ℝ} (hε : 0 < ε) : {x : ℝ^2 | 0 ≤ x 1} ⊆ repDomain ε := by
  intro x hx
  by_cases h1 : 0 < x 1
  · exact Or.inl (Or.inl h1)
  by_cases h0 : x 0 = 0
  · right
    have hx1 : x 1 = 0 := le_antisymm (not_lt.mp h1) hx
    have hzero : x = 0 := by
      ext i
      fin_cases i
      · exact h0
      · exact hx1
    simpa [hzero] using hε
  · exact Or.inl (Or.inr h0)

/-- The representative is `C^n` on its domain. -/
private theorem rep_contDiffOn {n : WithTop ℕ∞} {χ g : ℝ → ℝ} (hχ : ContDiff ℝ n χ)
    (hg : ContDiff ℝ n g) (m : ℝ) {ε : ℝ} (hzero : ∀ r, |r| < ε → χ r = 0) :
    ContDiffOn ℝ n (rep χ g m) (repDomain ε) := by
  intro x hx
  apply ContDiffAt.contDiffWithinAt
  rcases hx with hx | hx
  · have hsrc : ((x 1, -x 0) : ℝ × ℝ) ∈ polarCoord.source := by
      rw [polarCoord_source]
      rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr (neg_ne_zero.mpr hx)
    have hne : x ≠ 0 := by
      rintro rfl
      rcases hx with hx | hx <;> simp at hx
    have hnorm : ContDiffAt ℝ n (fun y : ℝ^2 ↦ ‖y‖) x := contDiffAt_norm ℝ hne
    have hpow : ContDiffAt ℝ n (fun y : ℝ^2 ↦ ‖y‖ ^ m) x :=
      (Real.contDiffAt_rpow_const_of_ne (norm_ne_zero_iff.mpr hne)).comp x hnorm
    have hrot : ContDiff ℝ n fun y : ℝ^2 ↦ ((y 1, -y 0) : ℝ × ℝ) := by fun_prop
    have hangle : ContDiffAt ℝ n rotatedAngle x := by
      have hchart := (contDiffAt_polarCoord (n := n) hsrc).comp x hrot.contDiffAt
      exact (contDiffAt_snd.comp x hchart).add contDiffAt_const
    exact (hχ.contDiffAt.comp x hnorm).mul (hpow.mul (hg.contDiffAt.comp x hangle))
  · have hball : ball (0 : ℝ^2) ε ∈ 𝓝 x := isOpen_ball.mem_nhds hx
    have heq : rep χ g m =ᶠ[𝓝 x] fun _ ↦ 0 := by
      filter_upwards [hball] with y hy
      have hy' : |‖y‖| < ε := by simpa [abs_of_nonneg (norm_nonneg y)] using hy
      simp [rep, hzero _ hy']
    exact contDiffAt_const.congr_of_eventuallyEq heq

/-- Beyond the radius where the cutoff equals one, the representative is homogeneous of
degree `m` under dilations by `t ≥ 1`. -/
private theorem rep_smul {χ g : ℝ → ℝ} (m : ℝ) {R : ℝ} (hone : ∀ r, R ≤ r → χ r = 1) {t : ℝ}
    (ht : 1 ≤ t) {x : ℝ^2} (hx : R ≤ ‖x‖) :
    rep χ g m (t • x) = t ^ m * rep χ g m x := by
  have htpos : 0 < t := by linarith
  have hnorm : ‖t • x‖ = t * ‖x‖ := by rw [norm_smul, Real.norm_of_nonneg htpos.le]
  have hle : ‖x‖ ≤ t * ‖x‖ := le_mul_of_one_le_left (norm_nonneg x) ht
  simp only [rep, hnorm, rotatedAngle_smul htpos, hone _ hx, hone _ (hx.trans hle),
    Real.mul_rpow htpos.le (norm_nonneg x)]
  ring

/-- A cut off homogeneous polar profile agrees on the closed upper half-plane with a function
that is `C^n` on an open neighbourhood of the closed upper half-plane, when the cutoff and the
angular factor are `C^n` on the line and the cutoff vanishes near zero. -/
theorem exists_contDiffOn_extension_profileFromPolar_cutoff_rpow_mul {n : WithTop ℕ∞}
    {χ g : ℝ → ℝ} (hχ : ContDiff ℝ n χ) (hg : ContDiff ℝ n g)
    (hflat : χ =ᶠ[𝓝 0] fun _ ↦ 0) (m : ℝ) :
    ∃ U : Set (ℝ^2), IsOpen U ∧ {x : ℝ^2 | 0 ≤ x 1} ⊆ U ∧ ∃ h : ℝ^2 → ℝ,
      ContDiffOn ℝ n h U ∧
        EqOn h (profileFromPolar (fun r β ↦ χ r * (r ^ m * g β))) {x | 0 ≤ x 1} := by
  obtain ⟨ε, hε, hzero⟩ := Metric.eventually_nhds_iff.mp hflat
  have hzero' : ∀ r, |r| < ε → χ r = 0 := fun r hr ↦ hzero (by simpa using hr)
  exact ⟨repDomain ε, isOpen_repDomain ε, subset_repDomain hε, rep χ g m,
    rep_contDiffOn hχ hg m hzero', rep_eqOn m hflat.eq_of_nhds⟩

end PDE.FDeriv

namespace PDE.FDeriv

/-- A compactly supported `C^j` field has its `j`-th derivative bounded by `C (1 + |x|)^s` for
every real exponent `s`. -/
theorem exists_norm_iteratedFDeriv_le_mul_rpow_of_hasCompactSupport {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {j : ℕ} (hf : ContDiff ℝ j f) (hc : HasCompactSupport f) (s : ℝ) :
    ∃ C, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ C * (1 + ‖x‖) ^ s := by
  have hcj : HasCompactSupport (iteratedFDeriv ℝ j f) := hc.iteratedFDeriv j
  obtain ⟨M, hM⟩ := (hf.continuous_iteratedFDeriv le_rfl).bounded_above_of_compact_support hcj
  obtain ⟨L, hL⟩ := hcj.isCompact.isBounded.subset_closedBall 0
  refine ⟨max M 0 * (1 + max L 0) ^ |s|, fun x ↦ ?_⟩
  have hw : 0 ≤ (1 + ‖x‖) ^ s := Real.rpow_nonneg (by positivity) _
  by_cases hx : x ∈ tsupport (iteratedFDeriv ℝ j f)
  · have hxL : ‖x‖ ≤ max L 0 := by
      have := hL hx
      rw [mem_closedBall, dist_zero_right] at this
      exact this.trans (le_max_left _ _)
    have hone := one_le_rpow_abs_mul_rpow (s := s) (norm_nonneg x) hxL
    calc
      ‖iteratedFDeriv ℝ j f x‖ ≤ max M 0 * 1 := by
        rw [mul_one]
        exact (hM x).trans (le_max_left _ _)
      _ ≤ max M 0 * ((1 + max L 0) ^ |s| * (1 + ‖x‖) ^ s) :=
        mul_le_mul_of_nonneg_left hone (le_max_right _ _)
      _ = _ := by ring
  · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero]
    exact mul_nonneg (mul_nonneg (le_max_right _ _)
      (Real.rpow_nonneg (by positivity) _)) hw

/-- A cut off homogeneous polar profile has its `j`-th derivative bounded by `C (1 + |x|)^(m - j)`
on the open upper half-plane, when the cutoff and the angular factor are `C^j` on the line, the
cutoff vanishes near zero and equals one beyond a radius `R`. -/
theorem exists_norm_iteratedFDeriv_profileFromPolar_cutoff_rpow_mul_le {χ g : ℝ → ℝ} {j : ℕ}
    (hχ : ContDiff ℝ j χ) (hg : ContDiff ℝ j g) (hflat : χ =ᶠ[𝓝 0] fun _ ↦ 0) {R : ℝ}
    (hone : ∀ r, R ≤ r → χ r = 1) (m : ℝ) :
    ∃ C, ∀ x : ℝ^2, 0 < x 1 →
      ‖iteratedFDeriv ℝ j (profileFromPolar (fun r β ↦ χ r * (r ^ m * g β))) x‖ ≤
        C * (1 + ‖x‖) ^ (m - j) := by
  obtain ⟨ε, hε, hzero⟩ := Metric.eventually_nhds_iff.mp hflat
  have hzero' : ∀ r, |r| < ε → χ r = 0 := fun r hr ↦ hzero (by simpa using hr)
  set f := profileFromPolar (fun r β ↦ χ r * (r ^ m * g β))
  set h := rep χ g m
  set U := repDomain ε
  have hU : ContDiffOn ℝ j h U := rep_contDiffOn hχ hg m hzero'
  have hUo : IsOpen U := isOpen_repDomain ε
  have hsub : {x : ℝ^2 | 0 ≤ x 1} ⊆ U := subset_repDomain hε
  have hc1 : Continuous fun x : ℝ^2 ↦ x 1 := by fun_prop
  have heq : ∀ x : ℝ^2, 0 < x 1 → iteratedFDeriv ℝ j f x = iteratedFDeriv ℝ j h x := by
    intro x hx
    have hgerm : f =ᶠ[𝓝 x] h := by
      filter_upwards [(isOpen_lt continuous_const hc1).mem_nhds hx] with y hy
      exact (rep_eqOn m hflat.eq_of_nhds (le_of_lt hy)).symm
    exact (hgerm.iteratedFDeriv ℝ j).eq_of_nhds
  set R' : ℝ := 2 * max R 1
  have hR'1 : 1 ≤ R' := by
    have := le_max_right R 1
    simp only [R']
    linarith
  have hRR' : R < R' := by
    have := le_max_left R 1
    have := le_max_right R 1
    simp only [R']
    linarith
  set K := {x : ℝ^2 | 0 ≤ x 1} ∩ closedBall 0 R'
  have hK : IsCompact K := (isCompact_closedBall 0 R').inter_left (isClosed_le continuous_const hc1)
  have hKU : K ⊆ U := fun x hx ↦ hsub hx.1
  have hcont : ContinuousOn (fun x ↦ iteratedFDeriv ℝ j h x) U := fun x hx ↦
    ((hU.contDiffAt (hUo.mem_nhds hx)).continuousAt_iteratedFDeriv le_rfl).continuousWithinAt
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hcont.mono hKU)
  set M' := max M 0
  have hM' : ∀ x ∈ K, ‖iteratedFDeriv ℝ j h x‖ ≤ M' := fun x hx ↦ (hM x hx).trans (le_max_left _ _)
  set s : ℝ := m - j
  have hpow : 0 < R' ^ s := Real.rpow_pos_of_pos (by linarith) _
  refine ⟨M' * (1 + R') ^ |s| + M' * (R' ^ s)⁻¹ * 2 ^ |s|, fun y hy ↦ ?_⟩
  rw [heq y hy]
  have hw : 0 ≤ (1 + ‖y‖) ^ s := Real.rpow_nonneg (by positivity) _
  have hM'0 : 0 ≤ M' := le_max_right _ _
  have hfar0 : 0 ≤ M' * (R' ^ s)⁻¹ * 2 ^ |s| * (1 + ‖y‖) ^ s := by positivity
  have hnear0 : 0 ≤ M' * (1 + R') ^ |s| * (1 + ‖y‖) ^ s := by positivity
  rw [add_mul]
  by_cases hyR : ‖y‖ ≤ R'
  · have hyK : y ∈ K := ⟨le_of_lt hy, by simpa using hyR⟩
    have hone' := one_le_rpow_abs_mul_rpow (s := s) (norm_nonneg y) hyR
    calc
      ‖iteratedFDeriv ℝ j h y‖ ≤ M' * 1 := by rw [mul_one]; exact hM' y hyK
      _ ≤ M' * ((1 + R') ^ |s| * (1 + ‖y‖) ^ s) := mul_le_mul_of_nonneg_left hone' hM'0
      _ = M' * (1 + R') ^ |s| * (1 + ‖y‖) ^ s := by ring
      _ ≤ _ := le_add_of_nonneg_right hfar0
  · push Not at hyR
    have hypos : 0 < ‖y‖ := lt_trans (by linarith) hyR
    set t : ℝ := ‖y‖ / R'
    have htpos : 0 < t := div_pos hypos (by linarith)
    have ht1 : 1 ≤ t := by rw [le_div_iff₀ (by linarith)]; linarith
    set z : ℝ^2 := t⁻¹ • y
    have hzy : t • z = y := by simp [z, smul_smul, htpos.ne']
    have hznorm : ‖z‖ = R' := by
      simp only [z, t, norm_smul, norm_inv, Real.norm_of_nonneg (div_nonneg hypos.le
        (by linarith : (0 : ℝ) ≤ R'))]
      field_simp
    have hz1 : 0 < z 1 := by
      simp only [z, PiLp.smul_apply, smul_eq_mul]
      exact mul_pos (inv_pos.mpr htpos) hy
    have hzK : z ∈ K := ⟨le_of_lt hz1, by simp [hznorm]⟩
    have hzU : z ∈ U := hKU hzK
    let L : ℝ^2 ≃L[ℝ] ℝ^2 :=
      (LinearEquiv.smulOfNeZero ℝ (ℝ^2) t htpos.ne').toContinuousLinearEquiv
    have hL : ∀ w, L w = t • w := fun w ↦ rfl
    have hcomp : iteratedFDeriv ℝ j (h ∘ L) z =
        (iteratedFDeriv ℝ j h y).compContinuousLinearMap fun _ ↦ (L : ℝ^2 →L[ℝ] ℝ^2) := by
      have := L.iteratedFDerivWithin_comp_right h uniqueDiffOn_univ (mem_univ (L z)) j
      rw [preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ, hL, hzy] at this
      exact this
    have hcompNorm : ‖(iteratedFDeriv ℝ j h y).compContinuousLinearMap
        fun _ ↦ (L : ℝ^2 →L[ℝ] ℝ^2)‖ = t ^ j * ‖iteratedFDeriv ℝ j h y‖ := by
      have hsm : (iteratedFDeriv ℝ j h y).compContinuousLinearMap
          (fun _ ↦ (L : ℝ^2 →L[ℝ] ℝ^2)) = t ^ j • iteratedFDeriv ℝ j h y := by
        ext v
        simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
          ContinuousLinearEquiv.coe_coe, hL, smul_apply]
        rw [ContinuousMultilinearMap.map_smul_univ]
        simp
      rw [hsm, norm_smul, Real.norm_of_nonneg (pow_nonneg htpos.le _)]
    have hscale : h ∘ L =ᶠ[𝓝 z] fun w ↦ t ^ m • h w := by
      have hopen : IsOpen {w : ℝ^2 | R < ‖w‖} := isOpen_lt continuous_const continuous_norm
      filter_upwards [hopen.mem_nhds (show R < ‖z‖ by rw [hznorm]; exact hRR')] with w hw
      simp only [Function.comp_apply, hL, smul_eq_mul]
      exact rep_smul m hone ht1 (le_of_lt hw)
    have hhz : ContDiffAt ℝ j h z := hU.contDiffAt (hUo.mem_nhds hzU)
    have hident : t ^ j * ‖iteratedFDeriv ℝ j h y‖ = t ^ m * ‖iteratedFDeriv ℝ j h z‖ := by
      rw [← hcompNorm, ← hcomp, (hscale.iteratedFDeriv ℝ j).eq_of_nhds,
        iteratedFDeriv_const_smul_apply' hhz, norm_smul,
        Real.norm_of_nonneg (Real.rpow_nonneg htpos.le _)]
    have htj : 0 < t ^ j := pow_pos htpos j
    have hy_eq : ‖iteratedFDeriv ℝ j h y‖ = t ^ s * ‖iteratedFDeriv ℝ j h z‖ := by
      have hts : t ^ s = t ^ m / t ^ j := by
        rw [Real.rpow_sub htpos, Real.rpow_natCast]
      rw [hts, div_mul_eq_mul_div, eq_div_iff htj.ne', mul_comm, hident]
    have htpow : t ^ s = ‖y‖ ^ s * (R' ^ s)⁻¹ := by
      rw [Real.div_rpow hypos.le (by linarith), div_eq_mul_inv]
    have hy1 : 1 ≤ ‖y‖ := le_trans hR'1 hyR.le
    have hfar := rpow_le_two_rpow_abs_mul_one_add_rpow hy1 s
    calc
      ‖iteratedFDeriv ℝ j h y‖ = t ^ s * ‖iteratedFDeriv ℝ j h z‖ := hy_eq
      _ ≤ t ^ s * M' := mul_le_mul_of_nonneg_left (hM' z hzK) (Real.rpow_nonneg htpos.le _)
      _ = M' * (R' ^ s)⁻¹ * ‖y‖ ^ s := by rw [htpow]; ring
      _ ≤ M' * (R' ^ s)⁻¹ * (2 ^ |s| * (1 + ‖y‖) ^ s) :=
        mul_le_mul_of_nonneg_left hfar (by positivity)
      _ = M' * (R' ^ s)⁻¹ * 2 ^ |s| * (1 + ‖y‖) ^ s := by ring
      _ ≤ _ := le_add_of_nonneg_left hnear0

/-- When `m ≤ k + 1`, the `k`-th derivative of a cut off homogeneous polar profile is Lipschitz on
the open upper half-plane: its derivative, the `(k + 1)`-th derivative, is bounded there. -/
theorem exists_lipschitzOnWith_iteratedFDeriv_profileFromPolar_cutoff_rpow_mul {χ g : ℝ → ℝ}
    (k : ℕ) (hχ : ContDiff ℝ (k + 1 : ℕ) χ) (hg : ContDiff ℝ (k + 1 : ℕ) g)
    (hflat : χ =ᶠ[𝓝 0] fun _ ↦ 0) {R : ℝ} (hone : ∀ r, R ≤ r → χ r = 1) {m : ℝ}
    (hm : m ≤ k + 1) :
    ∃ K, LipschitzOnWith K
      (iteratedFDeriv ℝ k (profileFromPolar (fun r β ↦ χ r * (r ^ m * g β))))
      {x : ℝ^2 | 0 < x 1} := by
  set f := profileFromPolar (fun r β ↦ χ r * (r ^ m * g β))
  obtain ⟨C, hC⟩ :=
    exists_norm_iteratedFDeriv_profileFromPolar_cutoff_rpow_mul_le hχ hg hflat hone m
  obtain ⟨U, hUo, hsub, h, hU, hEq⟩ :=
    exists_contDiffOn_extension_profileFromPolar_cutoff_rpow_mul hχ hg hflat m
  have hc1 : Continuous fun x : ℝ^2 ↦ x 1 := by fun_prop
  have hdiff : ∀ x : ℝ^2, 0 < x 1 → DifferentiableAt ℝ (iteratedFDeriv ℝ k f) x := by
    intro x hx
    have hgerm : f =ᶠ[𝓝 x] h := by
      filter_upwards [(isOpen_lt continuous_const hc1).mem_nhds hx] with y hy
      exact (hEq (le_of_lt hy)).symm
    have hfx : ContDiffAt ℝ (k + 1 : ℕ) f x :=
      (hU.contDiffAt (hUo.mem_nhds (hsub (le_of_lt hx)))).congr_of_eventuallyEq hgerm
    exact hfx.differentiableAt_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self k)
  let K : NNReal := ⟨max C 0, le_max_right _ _⟩
  refine ⟨K, Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (f' := fun x ↦ fderiv ℝ (iteratedFDeriv ℝ k f) x) (fun x hx ↦
      (hdiff x hx).hasFDerivAt.hasFDerivWithinAt) (fun x hx ↦ ?_) ?_⟩
  · rw [← NNReal.coe_le_coe, coe_nnnorm, norm_fderiv_iteratedFDeriv]
    have hs : m - ((k + 1 : ℕ) : ℝ) ≤ 0 := by push_cast; linarith
    have hle1 : (1 + ‖x‖) ^ (m - ((k + 1 : ℕ) : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg x]) hs
    have hw : 0 ≤ (1 + ‖x‖) ^ (m - ((k + 1 : ℕ) : ℝ)) := Real.rpow_nonneg (by positivity) _
    calc
      ‖iteratedFDeriv ℝ (k + 1) f x‖ ≤ C * (1 + ‖x‖) ^ (m - ((k + 1 : ℕ) : ℝ)) := hC x hx
      _ ≤ max C 0 * (1 + ‖x‖) ^ (m - ((k + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hw
      _ ≤ max C 0 * 1 := mul_le_mul_of_nonneg_left hle1 (le_max_right _ _)
      _ = K := mul_one _
  · exact convex_halfSpace_gt (f := fun x : ℝ^2 ↦ x 1)
      ⟨fun x y ↦ by simp, fun c x ↦ by simp⟩ 0

end PDE.FDeriv
