/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.OneDimensional.BoundaryLayer.Variable.Existence
import CAS.ExactTactic

/-!
# The reduced solution and its exact boundary correction

Local C¹ coefficients and a positive drift lower bound determine the reduced
solution by integration from the right endpoint. Compactness bounds its second
derivative independently of ε. Subtracting the constructed homogeneous correction
leaves a zero-trace residual, controlled by the affine comparison barrier.
-/

@[expose] public section

noncomputable section

namespace PDE.Elliptic.BoundaryLayer.Variable

open Set
open scoped Topology

/-- Positivity on the interval gives an open neighborhood where the raw quotient is C¹.
Continuity is required only on U, so openness uses the relative preimage theorem. -/
theorem quotient_domain {L α : ℝ} (hα : 0 < α) {U : Set ℝ} (hU : IsOpen U)
    (hIU : Icc 0 L ⊆ U) (a f : ℝ → ℝ)
    (ha : ContDiffOn ℝ 1 a U) (hf : ContDiffOn ℝ 1 f U)
    (hlower : ∀ x ∈ Icc 0 L, α ≤ a x) :
    ∃ V : Set ℝ, IsOpen V ∧ Icc 0 L ⊆ V ∧
      ContDiffOn ℝ 1 (fun x ↦ f x / a x) V := by
  let V : Set ℝ := U ∩ a ⁻¹' ({0} : Set ℝ)ᶜ
  have hV : IsOpen V := ha.continuousOn.isOpen_inter_preimage hU isClosed_singleton.isOpen_compl
  have hIV : Icc 0 L ⊆ V := by
    intro x hx
    refine ⟨hIU hx, ?_⟩
    change a x ≠ 0
    exact (hα.trans_le (hlower x hx)).ne'
  refine ⟨V, hV, hIV, ?_⟩
  exact (hf.mono inter_subset_left).div (ha.mono inter_subset_left)
    (fun x hx ↦ by simpa only [mem_preimage, mem_compl_iff, mem_singleton_iff] using hx.2)

/-- Compactness derives an ε-independent quotient-derivative bound from raw C¹ data. -/
theorem quotient_deriv_bound {L α : ℝ} (hα : 0 < α) {U : Set ℝ} (hU : IsOpen U)
    (hIU : Icc 0 L ⊆ U) (a f : ℝ → ℝ)
    (ha : ContDiffOn ℝ 1 a U) (hf : ContDiffOn ℝ 1 f U)
    (hlower : ∀ x ∈ Icc 0 L, α ≤ a x) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Icc 0 L, |deriv (fun y ↦ f y / a y) x| ≤ M := by
  obtain ⟨V, hV, hIV, hq⟩ := quotient_domain hα hU hIU a f ha hf hlower
  have hdc : ContinuousOn (deriv (fun y ↦ f y / a y)) (Icc 0 L) :=
    (hq.continuousOn_deriv_of_isOpen hV le_rfl).mono hIV
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hdc
  refine ⟨max C 0, le_max_right _ _, fun x hx ↦ ?_⟩
  have hbound : |deriv (fun y ↦ f y / a y) x| ≤ C := by
    simpa only [Real.norm_eq_abs] using hC x hx
  exact hbound.trans (le_max_left _ _)

/-- An integral of the clamped quotient is continuous up to both endpoints and is a C²
outer solution in the interior. Its integral formula uses the original coefficient values. -/
theorem exists_outer {L : ℝ} (hL : 0 < L) {V : Set ℝ}
    (hIV : Icc 0 L ⊆ V) (q : ℝ → ℝ) (hq : ContDiffOn ℝ 1 q V) (B : ℝ) :
    ∃ v : ℝ → ℝ, Continuous v ∧ ContDiffOn ℝ 2 v (Ioo 0 L) ∧ v L = B ∧
      (∀ x ∈ Icc 0 L, v x = B - ∫ t in x..L, q t) ∧
      (∀ x ∈ Ioo 0 L, deriv v x = q x) ∧
      ∀ x ∈ Ioo 0 L, deriv (deriv v) x = deriv q x := by
  let qe : ℝ → ℝ := IccExtend hL.le (fun x : Icc 0 L ↦ q x)
  have hqc : Continuous qe := (hq.continuousOn.mono hIV).domRestrict.Icc_extend'
  have heq (x : ℝ) (hx : x ∈ Icc 0 L) : qe x = q x :=
    IccExtend_of_mem hL.le _ hx
  let v : ℝ → ℝ := fun x ↦ B + ∫ t in L..x, qe t
  have hd (x : ℝ) : HasDerivAt v (qe x) x :=
    ((hqc.integral_hasStrictDerivAt L x).hasDerivAt).const_add B
  have hdc : Continuous v := Differentiable.continuous (fun x ↦ (hd x).differentiableAt)
  have hd_eq : deriv v = qe := funext fun x ↦ (hd x).deriv
  have hqe₁ : ContDiffOn ℝ 1 qe (Ioo 0 L) :=
    (hq.mono (Ioo_subset_Icc_self.trans hIV)).congr
      (fun x hx ↦ heq x (Ioo_subset_Icc_self hx))
  have hv₂ : ContDiffOn ℝ 2 v (Ioo 0 L) := by
    apply (contDiffOn_succ_iff_deriv_of_isOpen (n := 1) isOpen_Ioo).mpr
    refine ⟨fun x _ ↦ (hd x).differentiableAt.differentiableWithinAt, ?_, ?_⟩
    · norm_num
    · rw [hd_eq]
      exact hqe₁
  refine ⟨v, hdc, hv₂, ?_, ?_, ?_, ?_⟩
  · simp [v]
  · intro x hx
    have hint : (∫ t in x..L, qe t) = ∫ t in x..L, q t := by
      apply intervalIntegral.integral_congr
      intro y hy
      rw [uIcc_of_le hx.2] at hy
      exact heq y ⟨hx.1.trans hy.1, hy.2⟩
    dsimp [v]
    rw [intervalIntegral.integral_symm, hint]
    rfl
  · intro x hx
    rw [hd_eq]
    exact heq x (Ioo_subset_Icc_self hx)
  · intro x hx
    rw [hd_eq]
    have hnear : qe =ᶠ[𝓝 x] q := by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
      exact heq y (Ioo_subset_Icc_self hy)
    exact hnear.deriv_eq

/-- Subtracting the constructed homogeneous correction cancels the endpoint mismatch and
leaves only the ε-scaled second derivative of the outer solution. -/
theorem composite_error {L ε α M : ℝ} (hL : 0 < L) (hε : 0 < ε)
    (hα : 0 < α) (hM : 0 ≤ M) (a f q u v H : ℝ → ℝ) (A B : ℝ)
    (ha : ∀ x ∈ Ioo 0 L, α ≤ a x)
    (hu : ContDiff ℝ 2 u) (hv : ContinuousOn v (Icc 0 L))
    (hv₂ : ContDiffOn ℝ 2 v (Ioo 0 L)) (hH : ContDiff ℝ 2 H)
    (hu0 : u 0 = A) (huL : u L = B) (hvL : v L = B)
    (hH0 : H 0 = 1) (hHL : H L = 0)
    (hopu : ∀ x ∈ Ioo 0 L, ε * deriv (deriv u) x + a x * deriv u x = f x)
    (hopH : ∀ x ∈ Ioo 0 L, ε * deriv (deriv H) x + a x * deriv H x = 0)
    (hvfirst : ∀ x ∈ Ioo 0 L, a x * deriv v x = f x)
    (hvsecond : ∀ x ∈ Ioo 0 L, deriv (deriv v) x = deriv q x)
    (hqbound : ∀ x ∈ Ioo 0 L, |deriv q x| ≤ M) :
    ∀ x ∈ Icc 0 L, |u x - v x - (A - v 0) * H x| ≤ ε * M * (L - x) / α := by
  let D : ℝ := A - v 0
  let r : ℝ → ℝ := fun x ↦ u x - v x - D * H x
  have hr : ContinuousOn r (Icc 0 L) :=
    (hu.continuous.continuousOn.sub hv).sub (hH.continuous.const_mul D).continuousOn
  have hvr (x : ℝ) (hx : x ∈ Ioo 0 L) : ContDiffAt ℝ 2 v x :=
    hv₂.contDiffAt (isOpen_Ioo.mem_nhds hx)
  have hr₂ (x : ℝ) (hx : x ∈ Ioo 0 L) : ContDiffAt ℝ 2 r x :=
    (hu.contDiffAt.sub (hvr x hx)).sub (hH.contDiffAt.const_smul D)
  have hres (x : ℝ) (hx : x ∈ Ioo 0 L) :
      ε * deriv (deriv r) x + a x * deriv r x = -ε * deriv q x := by
    let σ : ℝ → Unit → ℝ := fun _ _ ↦ 1
    let b : ℝ → ℝ := fun y ↦ -(a y / ε)
    let c : ℝ → ℝ := fun _ ↦ 0
    have hQ (z : ℝ → ℝ) : EllipticMaximum.factoredOperator σ b c z x =
        -(ε * deriv (deriv z) x + a x * deriv z x) / ε := by
      rw [scalar_operator]
      have hid (b d e : ℝ) : -e - (b / ε) * d = -(ε * e + b * d) / ε := by
        cas using hε.ne'
      exact hid _ _ _
    have hlin := EllipticMaximum.factoredOperator_sub σ b c
      (hu.contDiffAt.sub (hvr x hx)) (hH.contDiffAt.const_smul D)
    simp only [smul_eq_mul] at hlin
    rw [EllipticMaximum.factoredOperator_sub σ b c hu.contDiffAt (hvr x hx),
      EllipticMaximum.factoredOperator_const_mul σ b c
        (hH.contDiffAt.differentiableAt (by norm_num)) D] at hlin
    change EllipticMaximum.factoredOperator σ b c r x = _ at hlin
    rw [hQ, hQ, hQ, hQ, hopu x hx, hopH x hx, hvsecond x hx, hvfirst x hx] at hlin
    have hscaled := congrArg (fun t : ℝ ↦ ε * t) hlin
    field_simp [hε.ne'] at hscaled
    linarith
  apply residual_bound hL hε hα hM a ha hr hr₂
  · intro x hx
    rw [hres x hx, abs_mul, abs_neg, abs_of_pos hε]
    exact mul_le_mul_of_nonneg_left (hqbound x hx) hε.le
  · dsimp [r, D]
    rw [hu0, hH0]
    ring
  · simp [r, huL, hvL, hHL]

/-- Raw local C¹ coefficients determine the outer solution and an ε-independent error
constant before any ε-dependent solution is constructed. -/
theorem raw_outer_approximation {L α : ℝ} (hL : 0 < L) (hα : 0 < α)
    {U : Set ℝ} (hU : IsOpen U) (hIU : Icc 0 L ⊆ U) (a f : ℝ → ℝ)
    (ha : ContDiffOn ℝ 1 a U) (hf : ContDiffOn ℝ 1 f U)
    (hlower : ∀ x ∈ Icc 0 L, α ≤ a x) (A B : ℝ) :
    ∃ v : ℝ → ℝ, Continuous v ∧ v L = B ∧
      (∀ x ∈ Icc 0 L, v x = B - ∫ t in x..L, f t / a t) ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ ε : ℝ, 0 < ε →
        ∃ u H : ℝ → ℝ, ContDiff ℝ 2 u ∧ ContDiff ℝ 2 H ∧
          u 0 = A ∧ u L = B ∧ H 0 = 1 ∧ H L = 0 ∧
          (∀ x ∈ Icc 0 L, ε * deriv (deriv u) x + a x * deriv u x = f x) ∧
          (∀ x ∈ Icc 0 L, ε * deriv (deriv H) x + a x * deriv H x = 0) ∧
          (∀ x ∈ Icc 0 L, 0 ≤ H x ∧ H x ≤ Real.exp (-α * x / ε)) ∧
          (∀ x ∈ Icc 0 L,
            |u x - v x - (A - v 0) * H x| ≤ ε * M * (L - x) / α) ∧
          ∀ x ∈ Icc 0 L,
            |u x - v x| ≤ |A - v 0| * Real.exp (-α * x / ε) + ε * M * (L - x) / α := by
  obtain ⟨V, _, hIV, hq⟩ := quotient_domain hα hU hIU a f ha hf hlower
  obtain ⟨v, hv, hv₂, hvL, hvformula, hvderiv, hvsecond⟩ :=
    exists_outer hL hIV (fun x ↦ f x / a x) hq B
  obtain ⟨M, hM, hqbound⟩ := quotient_deriv_bound hα hU hIU a f ha hf hlower
  refine ⟨v, hv, hvL, hvformula, M, hM, fun ε hε ↦ ?_⟩
  obtain ⟨u, hu, hu0, huL, hopu⟩ :=
    exists_solution_continuousOn hL hε a f
      (ha.continuousOn.mono hIU) (hf.continuousOn.mono hIU) A B
  have haopen (x : ℝ) (hx : x ∈ Ioo 0 L) : α ≤ a x :=
    hlower x (Ioo_subset_Icc_self hx)
  obtain ⟨H, hH, hH0, hHL, hopH, hHbound⟩ :=
    exists_localized_layer hL hε hα a
      (ha.continuousOn.mono hIU) haopen
  have hvfirst (x : ℝ) (hx : x ∈ Ioo 0 L) : a x * deriv v x = f x := by
    rw [hvderiv x hx]
    exact mul_div_cancel₀ _ (hα.trans_le (haopen x hx)).ne'
  have herror := composite_error hL hε hα hM a f (fun x ↦ f x / a x) u v H A B
    haopen hu hv.continuousOn hv₂ hH hu0 huL hvL hH0 hHL
    (fun x hx ↦ hopu x (Ioo_subset_Icc_self hx))
    (fun x hx ↦ hopH x (Ioo_subset_Icc_self hx)) hvfirst hvsecond
    (fun x hx ↦ hqbound x (Ioo_subset_Icc_self hx))
  refine ⟨u, H, hu, hH, hu0, huL, hH0, hHL, hopu, hopH, hHbound, herror, ?_⟩
  intro x hx
  have hsplit : u x - v x = (u x - v x - (A - v 0) * H x) + (A - v 0) * H x := by
    ring
  calc
    |u x - v x| = |(u x - v x - (A - v 0) * H x) + (A - v 0) * H x| :=
      congrArg abs hsplit
    _ ≤ |u x - v x - (A - v 0) * H x| + |(A - v 0) * H x| := abs_add_le _ _
    _ = |u x - v x - (A - v 0) * H x| + |A - v 0| * H x := by
      rw [abs_mul, abs_of_nonneg (hHbound x hx).1]
    _ ≤ ε * M * (L - x) / α + |A - v 0| * Real.exp (-α * x / ε) :=
      add_le_add (herror x hx)
        (mul_le_mul_of_nonneg_left (hHbound x hx).2 (abs_nonneg _))
    _ = |A - v 0| * Real.exp (-α * x / ε) + ε * M * (L - x) / α := add_comm _ _

end PDE.Elliptic.BoundaryLayer.Variable
