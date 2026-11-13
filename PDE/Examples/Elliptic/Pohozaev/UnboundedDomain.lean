/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import PDE.FDeriv.Operators
public import PDE.Spaces.Sobolev.Boundary.Atlas.Geometric.GraphBoundary
public import PDE.Spaces.Sobolev.Calculus.Differentiation.UniformBoundaryData
import PDE.FDeriv.PartialDeriv.Energy
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# An unbounded-domain supercritical solution

The three-dimensional critical profile, extended independently of the fourth coordinate,
is a positive smooth solution of `-Δu = u^5` on `ℝ^4`. The exponent is strictly above the
four-dimensional critical value `(4 + 2) / (4 - 2) = 3`. The function and its derivatives
through order two are uniformly continuous on the whole space.

`exists_unbounded_supercritical_solution` satisfies every hypothesis of the bounded star-shaped
nonexistence theorem, Evans, §9.4.2, Theorem 3, except boundedness. The theorem does not list that
bound, but its proof integrates by parts over `U` with the formulas of Appendix C.2, which assume a
bounded open set. The domain `ℝ^4` is connected and nonempty, but its frontier is empty, so the
smooth graph boundary condition and the zero Dirichlet condition hold vacuously.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.4.2, (11), (13) and Theorem 3
  (Nonexistence of nontrivial solution), pp. 551-554, and Appendix C.2, pp. 711-712.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set

namespace PDE.Examples.Pohozaev

/-- The three-dimensional critical profile extended independently of the fourth coordinate. -/
def cylindricalProfile (x : ℝ^4) : ℝ :=
  (1 + (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) / 3) ^ (-(1 : ℝ) / 2)

private theorem profile_base_pos (x : ℝ^4) :
    0 < 1 + (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) / 3 := by positivity

/-- The profile is everywhere positive. -/
theorem cylindricalProfile_pos (x : ℝ^4) : 0 < cylindricalProfile x :=
  Real.rpow_pos_of_pos (profile_base_pos x) _

/-- The profile is smooth on the whole ambient space. -/
theorem contDiff_cylindricalProfile : ContDiff ℝ (⊤ : ℕ∞) cylindricalProfile := by
  have h : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : ℝ^4 ↦ 1 + (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) / 3) := by fun_prop
  exact h.rpow_const_of_ne fun x ↦ (profile_base_pos x).ne'

/-- The fifth-power equation holds in four dimensions. -/
theorem neg_laplacian_cylindricalProfile (x : ℝ^4) :
    -laplacian cylindricalProfile x = cylindricalProfile x ^ 5 := by
  have hp := profile_base_pos x
  rw [neg_eq_iff_eq_neg]
  unfold cylindricalProfile
  cas using hp

private theorem profile_sq (x : ℝ^4) :
    cylindricalProfile x ^ 2 =
      (1 + (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) / 3)⁻¹ := by
  unfold cylindricalProfile
  rw [← Real.rpow_mul_natCast (profile_base_pos x).le]
  norm_num [Real.rpow_neg_one]

private theorem profile_le_one (x : ℝ^4) : cylindricalProfile x ≤ 1 := by
  have hb : 1 ≤ 1 + (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) / 3 := by
    linarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]
  have hsq : cylindricalProfile x ^ 2 ≤ 1 := by
    rw [profile_sq]
    exact inv_le_one_of_one_le₀ hb
  nlinarith [cylindricalProfile_pos x]

private theorem coordinate_profile_le_two (i : Fin 3) (x : ℝ^4) :
    |x i.castSucc * cylindricalProfile x| ≤ 2 := by
  have hb : x i.castSucc ^ 2 ≤ x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
    fin_cases i
    · change x 0 ^ 2 ≤ _
      nlinarith [sq_nonneg (x 1), sq_nonneg (x 2)]
    · change x 1 ^ 2 ≤ _
      nlinarith [sq_nonneg (x 0), sq_nonneg (x 2)]
    · change x 2 ^ 2 ≤ _
      nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
  have hs : (x i.castSucc * cylindricalProfile x) ^ 2 ≤ 3 := by
    rw [mul_pow, profile_sq, ← div_eq_mul_inv]
    apply (div_le_iff₀ (profile_base_pos x)).mpr
    linarith
  have ha := sq_abs (x i.castSucc * cylindricalProfile x)
  nlinarith [abs_nonneg (x i.castSucc * cylindricalProfile x)]

private theorem partial_profile_raw (i : Fin 4) (x : ℝ^4) :
    (∂[i] cylindricalProfile) x = if i = 3 then 0 else
      -x i / 3 * (1 + (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) / 3) ^ (-(3 : ℝ) / 2) := by
  have hp := profile_base_pos x
  fin_cases i <;> norm_num only [Fin.reduceEq, ite_false, ite_true] <;>
    unfold cylindricalProfile <;> cas using hp

private theorem partial_profile (i : Fin 4) (x : ℝ^4) :
    (∂[i] cylindricalProfile) x =
      if i = 3 then 0 else -(x i * cylindricalProfile x) * cylindricalProfile x ^ 2 / 3 := by
  rw [partial_profile_raw]
  split_ifs
  · rfl
  · have hc : cylindricalProfile x ^ 3 =
        (1 + (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) / 3) ^ (-(3 : ℝ) / 2) := by
      unfold cylindricalProfile
      rw [← Real.rpow_mul_natCast (profile_base_pos x).le]
      norm_num
    rw [← hc]
    cas

private theorem abs_partial_profile_le_one (i : Fin 4) (x : ℝ^4) :
    |(∂[i] cylindricalProfile) x| ≤ 1 := by
  rw [partial_profile]
  split_ifs with hi
  · norm_num
  · have hi' : i.val < 3 := by omega
    have hc := coordinate_profile_le_two ⟨i.val, hi'⟩ x
    have hc' : |x i * cylindricalProfile x| ≤ 2 := hc
    rw [abs_div, abs_mul, abs_neg, abs_pow,
      abs_of_pos (cylindricalProfile_pos x)]
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    have hu := profile_le_one x
    have hz := (cylindricalProfile_pos x).le
    have hsq : cylindricalProfile x ^ 2 ≤ 1 := by nlinarith
    have h := mul_le_mul hc' hsq (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    linarith

private theorem uniformContinuous_of_partial_bound {g : ℝ^4 → ℝ}
    (hg : Differentiable ℝ g) (hb : ∀ i x, |(∂[i] g) x| ≤ 3) :
    UniformContinuous g := by
  apply LipschitzWith.uniformContinuous (K := 12)
  apply lipschitzWith_of_nnnorm_fderiv_le hg
  intro x
  rw [← NNReal.coe_le_coe]
  change ‖fderiv ℝ g x‖ ≤ 12
  calc
    ‖fderiv ℝ g x‖ ≤ ∑ i : Fin 4, ‖(∂[i] g) x‖ :=
      (fderiv ℝ g x).norm_le_sum_norm_apply_single
    _ ≤ ∑ _ : Fin 4, (3 : ℝ) := Finset.sum_le_sum fun i _ ↦ by
      simpa only [Real.norm_eq_abs] using hb i x
    _ = 12 := by norm_num

private theorem uniformContinuous_profile : UniformContinuous cylindricalProfile := by
  apply uniformContinuous_of_partial_bound
    (contDiff_cylindricalProfile.differentiable (by norm_num))
  intro i x
  exact (abs_partial_profile_le_one i x).trans (by norm_num)

private theorem uniformContinuous_coordinate_profile (i : Fin 3) :
    UniformContinuous (fun x : ℝ^4 ↦ x i.castSucc * cylindricalProfile x) := by
  have hd := contDiff_cylindricalProfile.differentiable (by norm_num)
  apply uniformContinuous_of_partial_bound ((EuclideanSpace.proj i.castSucc).differentiable.mul hd)
  intro j x
  change |(∂[j] (fun y : ℝ^4 ↦ y i.castSucc * cylindricalProfile y)) x| ≤ 3
  rw [partialDeriv_mul (show DifferentiableAt ℝ (fun y : ℝ^4 ↦ y i.castSucc) x by fun_prop) (hd x),
    partialDeriv_coord, partial_profile]
  by_cases hj : j = 3
  · subst j
    have hi3 : (3 : Fin 4) ≠ i.castSucc := (Fin.castSucc_ne_last i).symm
    simp [hi3]
  · rw [ite_eq_right hj]
    have hj' : j.val < 3 := by omega
    have hi := coordinate_profile_le_two i x
    have hjb : |x j * cylindricalProfile x| ≤ 2 :=
      coordinate_profile_le_two ⟨j.val, hj'⟩ x
    have hu := profile_le_one x
    have hu0 := (cylindricalProfile_pos x).le
    have heq : (if j = i.castSucc then 1 else 0) * cylindricalProfile x +
        x i.castSucc * (-(x j * cylindricalProfile x) * cylindricalProfile x ^ 2 / 3) =
        (if j = i.castSucc then cylindricalProfile x else 0) -
          (x i.castSucc * cylindricalProfile x) *
          (x j * cylindricalProfile x) * cylindricalProfile x / 3 := by
      split_ifs <;> cas
    rw [heq]
    have ht : |(x i.castSucc * cylindricalProfile x) *
        (x j * cylindricalProfile x) * cylindricalProfile x / 3| ≤ 4 / 3 := by
      rw [abs_div, abs_mul, abs_mul, abs_of_nonneg hu0]
      norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 3)]
      have hh := mul_le_mul
        (mul_le_mul hi hjb (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2))
        hu hu0 (by norm_num : (0 : ℝ) ≤ 2 * 2)
      linarith
    have hf : |if j = i.castSucc then cylindricalProfile x else 0| ≤ 1 := by
      split_ifs <;> simp [abs_of_nonneg hu0, hu]
    exact (abs_sub _ _).trans ((add_le_add hf ht).trans (by norm_num))

private theorem second_partial_profile (i j : Fin 4) (x : ℝ^4) :
    (∂[i] (∂[j] cylindricalProfile)) x = if i = 3 ∨ j = 3 then 0 else
      ((x i * cylindricalProfile x) * (x j * cylindricalProfile x) -
        (if i = j then 1 else 0)) * cylindricalProfile x ^ 3 / 3 := by
  by_cases hj : j = 3
  · have hz : (∂[j] cylindricalProfile) = fun _ ↦ 0 := by
      funext y
      simp [partial_profile, hj]
    rw [hz, partialDeriv_const]
    simp [hj]
  · have hfirst : (∂[j] cylindricalProfile) =
        fun y ↦ (-(1 : ℝ) / 3) • (y j * cylindricalProfile y ^ 3) := by
      funext y
      rw [partial_profile, ite_eq_right hj]
      simp only [smul_eq_mul]
      cas
    have hd := contDiff_cylindricalProfile.differentiable (by norm_num)
    have hpow : (∂[i] (fun y ↦ cylindricalProfile y ^ 3)) x =
        3 * cylindricalProfile x ^ 2 * (∂[i] cylindricalProfile) x := by
      change fderiv ℝ (fun y ↦ cylindricalProfile y ^ 3) x
        (EuclideanSpace.single i 1) = _
      rw [fderiv_fun_pow 3 (hd x)]
      simp only [smul_apply, smul_eq_mul, nsmul_eq_mul]
      rfl
    rw [hfirst, partialDeriv_const_smul,
      partialDeriv_mul (show DifferentiableAt ℝ (fun y : ℝ^4 ↦ y j) x by fun_prop)
        ((hd x).hasFDerivAt.pow 3).differentiableAt, partialDeriv_coord, hpow, partial_profile]
    simp only [smul_eq_mul]
    by_cases hi : i = 3
    · subst i
      simp [hj, Ne.symm hj]
    · simp only [hi, hj, false_or, ite_false]
      split_ifs <;> cas

private theorem uniformContinuous_profile_polynomial
    {p : (Fin 4 → ℝ) → ℝ} (hp : Continuous p) :
    UniformContinuous (fun x : ℝ^4 ↦ p (fun i ↦
      if i = 3 then cylindricalProfile x else x i * cylindricalProfile x)) := by
  let v : ℝ^4 → Fin 4 → ℝ := fun x i ↦
    if i = 3 then cylindricalProfile x else x i * cylindricalProfile x
  have hv : UniformContinuous v := by
    apply uniformContinuous_pi.mpr
    intro i
    by_cases hi : i = 3
    · simpa only [v, hi, ite_true] using uniformContinuous_profile
    · have hi' : i.val < 3 := by omega
      have he : (⟨i.val, hi'⟩ : Fin 3).castSucc = i := by ext; rfl
      simpa only [v, hi, ite_false, he] using
        uniformContinuous_coordinate_profile ⟨i.val, hi'⟩
  have hb : MapsTo v univ (Set.pi univ fun _ ↦ Icc (-2 : ℝ) 2) := by
    intro x _ i _
    apply abs_le.mp
    by_cases hi : i = 3
    · simpa only [v, hi, ite_true, abs_of_pos (cylindricalProfile_pos x)] using
        (profile_le_one x).trans (by norm_num : (1 : ℝ) ≤ 2)
    · have hi' : i.val < 3 := by omega
      simp only [v, hi, ite_false]
      exact coordinate_profile_le_two ⟨i.val, hi'⟩ x
  exact uniformContinuousOn_univ.mp
    (((isCompact_univ_pi fun _ : Fin 4 ↦ isCompact_Icc).uniformContinuousOn_of_continuous
      hp.continuousOn).comp hv.uniformContinuousOn hb)

private theorem uniformContinuous_partial_profile (i : Fin 4) :
    UniformContinuous (∂[i] cylindricalProfile) := by
  have h := uniformContinuous_profile_polynomial
    (p := fun y ↦ if i = 3 then 0 else -y i * y 3 ^ 2 / 3) (by split_ifs <;> fun_prop)
  convert h using 1
  funext x
  rw [partial_profile]
  by_cases hi : i = 3 <;> simp [hi]

private theorem uniformContinuous_second_partial_profile (i j : Fin 4) :
    UniformContinuous (∂[i] (∂[j] cylindricalProfile)) := by
  have h := uniformContinuous_profile_polynomial
    (p := fun y ↦ if i = 3 ∨ j = 3 then 0 else
      (y i * y j - (if i = j then 1 else 0)) * y 3 ^ 3 / 3) (by split_ifs <;> fun_prop)
  convert h using 1
  funext x
  rw [second_partial_profile]
  by_cases hi : i = 3 <;> by_cases hj : j = 3 <;> simp [hi, hj]

/-- The function and all derivatives through order two are uniformly continuous globally. -/
theorem contDiffUpToBoundary_cylindricalProfile :
    SobolevSpace.ContDiffUpToBoundary 2 cylindricalProfile univ := by
  refine ⟨(contDiff_cylindricalProfile.of_le (by norm_num)).contDiffOn, ?_⟩
  intro α hα
  cases α with
  | nil => exact uniformContinuous_profile.uniformContinuousOn
  | cons i α =>
    cases α with
    | nil => exact (uniformContinuous_partial_profile i).uniformContinuousOn
    | cons j α =>
      have hnil : α = [] := by simpa using hα
      subst α
      exact (uniformContinuous_second_partial_profile i j).uniformContinuousOn

/-- Positivity identifies the fifth-power equation with the signed real-power convention. -/
theorem neg_laplacian_cylindricalProfile_signed_power (x : ℝ^4) :
    -laplacian cylindricalProfile x =
      |cylindricalProfile x| ^ ((5 : ℝ) - 1) * cylindricalProfile x := by
  rw [neg_laplacian_cylindricalProfile, abs_of_pos (cylindricalProfile_pos x)]
  rw [show (5 : ℝ) - 1 = (4 : ℕ) by norm_num, Real.rpow_natCast, pow_succ]

/-- Without boundedness the Pohozaev nonexistence theorem fails: `Ω = ℝ⁴` is open,
connected, unbounded and star-convex, and carries a positive smooth solution of
`-Δu = |u|^(p - 1) u` with the supercritical exponent `p = 5`, whose derivatives through
order two are uniformly continuous. The frontier of `Ω` is empty, so the graph boundary
and zero boundary conditions hold vacuously. -/
theorem exists_unbounded_supercritical_solution :
    ∃ (Ω : Set (ℝ^4)) (u : ℝ^4 → ℝ),
      IsOpen Ω ∧ IsConnected Ω ∧ ¬Bornology.IsBounded Ω ∧
      StarConvex ℝ (0 : ℝ^4) Ω ∧ StarConvex ℝ (0 : ℝ^4) (closure Ω) ∧
      SobolevSpace.Boundary.HasContDiffGraphBoundary ⊤ Ω ∧
      SobolevSpace.Boundary.HasC1GraphBoundary Ω ∧
      ContDiff ℝ (⊤ : ℕ∞) u ∧ SobolevSpace.ContDiffUpToBoundary 2 u Ω ∧
      ContinuousOn u (closure Ω) ∧ (∀ x ∈ Ω, 0 < u x) ∧
      (∀ x ∈ frontier Ω, u x = 0) ∧
      ((4 : ℝ) + 2) / ((4 : ℝ) - 2) < 5 ∧
      (∀ x ∈ Ω, -laplacian u x = |u x| ^ ((5 : ℝ) - 1) * u x) ∧
      ¬EqOn u 0 (closure Ω) := by
  refine ⟨univ, cylindricalProfile, isOpen_univ, isConnected_univ,
    NormedSpace.unbounded_univ ℝ (ℝ^4), starConvex_univ _, ?_, ?_, ?_,
    contDiff_cylindricalProfile, contDiffUpToBoundary_cylindricalProfile,
    contDiff_cylindricalProfile.continuous.continuousOn,
    fun x _ ↦ cylindricalProfile_pos x, ?_, by norm_num,
    fun x _ ↦ neg_laplacian_cylindricalProfile_signed_power x, ?_⟩
  · simpa only [closure_univ] using (starConvex_univ (𝕜 := ℝ) (0 : ℝ^4))
  · simp [SobolevSpace.Boundary.HasContDiffGraphBoundary]
  · simp [SobolevSpace.Boundary.HasC1GraphBoundary]
  · simp
  · intro hzero
    exact (cylindricalProfile_pos 0).ne' (hzero (by simp))

end PDE.Examples.Pohozaev
