/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.WeakComparison
public import PDE.Analysis.Order.LpCompactIteration
public import PDE.Analysis.MeasureTheory.Lp.Superposition
public import PDE.Spaces.Sobolev.Variational.Spaces.GelfandTriple.H10L2
public import PDE.Spaces.Sobolev.Compactness.Rellich.ZeroExtension

/-!
# Monotone iteration between L² interval endpoints

The shifted divergence solver and scalar superposition give one compact
monotone iteration engine. Its interval endpoints are L² functions; boundary
comparison belongs to the callers that prove the shifted interval invariant.
This separates the common nonlinear argument from the trace class of barriers.
-/

open scoped Sobolev

@[expose] public noncomputable section

namespace PDE.Elliptic.Semilinear

open SobolevSpace SobolevSpace.GraphSpace

open Filter MeasureTheory Set
open PDE.Analysis.Variational
open scoped ENNReal InnerProductSpace NNReal Topology

variable {n : ℕ} {Ω : Set (ℝ^n)}

local notation "μ" => domainMeasure n Ω
local notation "L2" => DerivLp n 2 Ω

/-- Adding a slope at least the Lipschitz constant makes a real function increasing. -/
theorem monotone_add_mass
    {g : ℝ → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {mu : ℝ} (hmu : (K : ℝ) ≤ mu) :
    Monotone (fun s ↦ g s + mu * s) := by
  intro s t hst
  have h := hg.norm_sub_le t s
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hst)] at h
  have hneg := (abs_le.mp h).1
  have hm := mul_le_mul_of_nonneg_right hmu (sub_nonneg.mpr hst)
  nlinarith

/-- Ordered scalar loads are ordered on every nonnegative Sobolev test function. -/
private theorem scalar_load_le
    {f g : L2} (hfg : f ≤ g) (v : H¹₀(Ω))
    (hv : ∀ᵐ x ∂μ, 0 ≤ baseCoordCLM v x) :
    loadFunctional f v ≤ loadFunctional g v := by
  have hfg' : ∀ᵐ x ∂μ, f x ≤ g x := AEEqFun.coeFn_le.mpr hfg
  rw [loadFunctional_apply, loadFunctional_apply]
  apply sub_nonpos.mp
  rw [← inner_sub_left, MeasureTheory.L2.inner_def]
  apply integral_nonpos_of_ae
  filter_upwards [hfg', hv, Lp.coeFn_sub f g] with x hx hvx hsub
  change (f - g) x = f x - g x at hsub
  rw [hsub, Real.inner_apply]
  exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) hvx

/-- The represented nonlinear load is the integrable tested nonlinear density. -/
private theorem scalar_superposition_pairing
    (g : ℝ → ℝ) (hmem : ∀ w : L2, MemLp (fun x ↦ g (w x)) 2 μ)
    (w : L2) (v : H¹₀(Ω)) :
    loadFunctional (Lp.superposition (fun _ ↦ g) hmem w) v =
      ∫ x, g (w x) * baseCoordCLM v x ∂μ := by
  rw [loadFunctional_apply, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_superposition (fun _ ↦ g) hmem w] with x hx
  rw [hx, Real.inner_apply]

/-- A linear pointwise bound controls the nonlinear load in `L²`.
The offset is measured in `L²`, and no sign condition on the growth coefficient is needed. -/
private theorem norm_scalar_superposition_le
    (g : ℝ → ℝ) {A C : ℝ}
    (hconst : MemLp (fun _ : ℝ^n ↦ A) 2 μ)
    (hmem : ∀ w : L2, MemLp (fun x ↦ g (w x)) 2 μ)
    (hgrowth : ∀ s, ‖g s‖ ≤ A + C * ‖s‖) (w : L2) :
    ‖Lp.superposition (fun _ ↦ g) hmem w‖ ≤
      ‖hconst.toLp (fun _ ↦ A)‖ + |C| * ‖w‖ := by
  let q : L2 := hconst.toLp (fun _ ↦ A)
  let W : L2 := lipschitzWith_one_norm.compLp (_root_.norm_zero) w
  have hW : ‖W‖ ≤ ‖w‖ := by
    simpa only [W, NNReal.coe_one, one_mul] using
      lipschitzWith_one_norm.norm_compLp_le (_root_.norm_zero) w
  have hdom : q + C • W =ᵐ[μ] fun x ↦ A + C * ‖w x‖ := by
    filter_upwards [Lp.coeFn_add q (C • W), hconst.coeFn_toLp,
      Lp.coeFn_smul C W,
      lipschitzWith_one_norm.coeFn_compLp (_root_.norm_zero) w]
      with x hadd hq hsmul hnorm
    simp only [hadd, Pi.add_apply, q, hq, hsmul, Pi.smul_apply, W, hnorm,
      Function.comp_apply, smul_eq_mul]
  have hbound : ‖Lp.superposition (fun _ ↦ g) hmem w‖ ≤ ‖q + C • W‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [Lp.coeFn_superposition (fun _ ↦ g) hmem w, hdom] with x hgx hx
    calc
      ‖Lp.superposition (fun _ ↦ g) hmem w x‖ = ‖g (w x)‖ := congrArg norm hgx
      _ ≤ A + C * ‖w x‖ := hgrowth _
      _ ≤ ‖(q + C • W) x‖ := by
        rw [hx, Real.norm_eq_abs]
        exact le_abs_self _
  calc
    ‖Lp.superposition (fun _ ↦ g) hmem w‖ ≤ ‖q + C • W‖ := hbound
    _ ≤ ‖q‖ + ‖C • W‖ := norm_add_le _ _
    _ = ‖q‖ + |C| * ‖W‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖q‖ + |C| * ‖w‖ :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hW (abs_nonneg C))

private theorem exists_monotone_shiftedSolver
    (hΩ : MeasurableSet Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω)
    {alpha beta gamma : ℝ}
    (hA : IntegratedElliptic (multiplicationCoefficientOperator a) alpha)
    (hbc : LowerOrderBounds (multiplicationFirstOrderOperator b)
      (multiplicationZeroOrderOperator c) beta gamma)
    (mu : ℝ) (hshift : coerciveShift (n := n) alpha beta gamma ≤ mu) :
    ∃ R : L2 →L[ℝ] H¹₀(Ω),
      (∀ f, IsWeakSolution
        (shiftedDivergenceForm (multiplicationCoefficientOperator a)
          (multiplicationFirstOrderOperator b) (multiplicationZeroOrderOperator c) mu)
        (loadFunctional f) (R f)) ∧
      Monotone (fun f ↦ baseCoordCLM (R f)) := by
  let Bmu : H¹₀(Ω) →L[ℝ] H¹₀(Ω) →L[ℝ] ℝ :=
    shiftedDivergenceForm (multiplicationCoefficientOperator a)
      (multiplicationFirstOrderOperator b) (multiplicationZeroOrderOperator c) mu
  have hBmu : IsCoercive Bmu :=
    shiftedDivergenceForm_isCoercive_of_coerciveShift_le
      (n := n) (Ω := Ω) _ _ _ hA hbc hshift
  let S : StrongDual ℝ H¹₀(Ω) →L[ℝ] H¹₀(Ω) := solveCLM (V := H¹₀(Ω)) Bmu hBmu
  let L : L2 →L[ℝ] StrongDual ℝ H¹₀(Ω) := loadFunctionalCLM (n := n) (Ω := Ω)
  let R : L2 →L[ℝ] H¹₀(Ω) := S.comp L
  have hR (f : L2) : IsWeakSolution Bmu (loadFunctional f) (R f) := by
    intro v
    exact solveCLM.isWeakSolution (V := H¹₀(Ω)) Bmu hBmu (L f) v
  refine ⟨R, hR, ?_⟩
  intro w z hwz
  apply AEEqFun.coeFn_le.mp
  exact base_le_ae_of_isWeakSolution_shiftedDivergenceForm hΩ a b c hA hbc hshift
    (loadFunctional w) (loadFunctional z) (R w) (R z) (hR w) (hR z)
    (scalar_load_le hwz)

private theorem exists_fixedPoint_between_barriers
    (hΩ : MeasurableSet Ω) (hΩbounded : Bornology.IsBounded Ω)
    (R : L2 →L[ℝ] H¹₀(Ω)) (N : L2 → L2) (hNcont : Continuous N)
    (A C : ℝ) (hC : 0 ≤ C) (hbound : ∀ w, ‖N w‖ ≤ A + C * ‖w‖)
    (hmono : Monotone (fun w ↦ baseCoordCLM (R (N w))))
    (lower upper : L2) (hlr : lower ≤ upper)
    (hlower : lower ≤ baseCoordCLM (R (N (lower))))
    (hupper : baseCoordCLM (R (N (upper))) ≤ upper) :
    ∃ u : H¹₀(Ω), lower ≤ baseCoordCLM u ∧
      baseCoordCLM u ≤ upper ∧ u = R (N (baseCoordCLM u)) := by
  obtain ⟨w, hw, _, _⟩ :=
    @PDE.OrderInterval.exists_tendsto_iterate_of_compact_factor
      (ℝ^n) H¹₀(Ω) inferInstance μ 2 inferInstance inferInstance inferInstance baseCoordCLM
      (baseCoordCLM.isCompactOperator_of_bounded (n := n) (Ω := Ω) hΩ hΩbounded)
      R N hNcont A C hC hbound hmono
      (lower) (upper) hlr hlower hupper
  let u : H¹₀(Ω) := R (N w)
  have hu : baseCoordCLM u = w := hw.1.2
  refine ⟨u, ?_, ?_, ?_⟩
  · simpa only [hu] using hw.1.1.1
  · simpa only [hu] using hw.1.1.2
  · rw [hu]

/-- A represented shifted scalar load has the original integral plus the mass pairing.
The representation itself supplies integrability of the unshifted source. -/
theorem loadFunctional_eq_integral_add_mass (g : ℝ → ℝ) (w f : L2) (mu : ℝ)
    (hf : f =ᵐ[μ] fun x ↦ g (w x) + mu * w x) (v : H¹₀(Ω)) :
    loadFunctional f v = (∫ x, g (w x) * baseCoordCLM v x ∂μ) +
      mu * inner ℝ w (baseCoordCLM v) := by
  apply eq_add_of_sub_eq
  rw [loadFunctional_apply, ← real_inner_smul_left, ← inner_sub_left,
    MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf, Lp.coeFn_sub f (mu • w), Lp.coeFn_smul mu w] with x hx hs hm
  simp only [Pi.smul_apply, smul_eq_mul] at hm
  rw [Real.inner_apply, hs, Pi.sub_apply, hm, hx]
  simp

/-- An invariant ordered L² interval for every sufficiently large mass shift
contains a solution of the original semilinear equation. The scalar source
is continuous, has linear growth, and has a monotone linear shift. -/
theorem exists_weak_solution_of_shifted_interval_invariant
    (hΩ : MeasurableSet Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω)
    {alpha beta gamma : ℝ}
    (hA : IntegratedElliptic (multiplicationCoefficientOperator a) alpha)
    (hbc : LowerOrderBounds (multiplicationFirstOrderOperator b)
      (multiplicationZeroOrderOperator c) beta gamma)
    (g : ℝ → ℝ) (hg : Continuous g) {A C M : ℝ}
    (hgrowth : ∀ s, ‖g s‖ ≤ A + C * ‖s‖)
    (hmono : Monotone (fun s ↦ g s + M * s))
    (lower upper : L2)
    (hlr : ∀ᵐ x ∂μ, lower x ≤ upper x)
    (hlower : ∀ mu : ℝ, coerciveShift (n := n) alpha beta gamma ≤ mu → M ≤ mu →
      ∀ f : L2, (f =ᵐ[μ] fun x ↦ g (lower x) + mu * lower x) →
      ∀ u : H¹₀(Ω), IsWeakSolution
        (shiftedDivergenceForm (multiplicationCoefficientOperator a)
          (multiplicationFirstOrderOperator b) (multiplicationZeroOrderOperator c) mu)
        (loadFunctional f) u → lower ≤ baseCoordCLM u)
    (hupper : ∀ mu : ℝ, coerciveShift (n := n) alpha beta gamma ≤ mu → M ≤ mu →
      ∀ f : L2, (f =ᵐ[μ] fun x ↦ g (upper x) + mu * upper x) →
      ∀ u : H¹₀(Ω), IsWeakSolution
        (shiftedDivergenceForm (multiplicationCoefficientOperator a)
          (multiplicationFirstOrderOperator b) (multiplicationZeroOrderOperator c) mu)
        (loadFunctional f) u → baseCoordCLM u ≤ upper) :
    ∃ u : H¹₀(Ω),
      (∀ᵐ x ∂μ, lower x ≤ baseCoordCLM u x) ∧
      (∀ᵐ x ∂μ, baseCoordCLM u x ≤ upper x) ∧
      MemLp (fun x ↦ g (baseCoordCLM u x)) 2 μ ∧
      ∀ v : H¹₀(Ω),
        fullDivergenceForm (multiplicationCoefficientOperator a)
          (multiplicationFirstOrderOperator b) (multiplicationZeroOrderOperator c) u v =
        ∫ x, g (baseCoordCLM u x) * baseCoordCLM v x ∂μ := by
  let : IsFiniteMeasure μ := isFiniteMeasure_domainMeasure_of_isBounded hΩbounded
  let J : H¹₀(Ω) →L[ℝ] L2 := baseCoordCLM
  let B : H¹₀(Ω) →L[ℝ] H¹₀(Ω) →L[ℝ] ℝ := fullDivergenceForm (multiplicationCoefficientOperator a)
    (multiplicationFirstOrderOperator b) (multiplicationZeroOrderOperator c)
  let mu : ℝ := max (coerciveShift (n := n) alpha beta gamma) M
  have hshift : coerciveShift (n := n) alpha beta gamma ≤ mu := le_max_left _ _
  have hMmu : M ≤ mu := le_max_right _ _
  let Bmu : H¹₀(Ω) →L[ℝ] H¹₀(Ω) →L[ℝ] ℝ :=
    shiftedDivergenceForm (multiplicationCoefficientOperator a)
    (multiplicationFirstOrderOperator b) (multiplicationZeroOrderOperator c) mu
  obtain ⟨R, hR, hRmono⟩ :=
    exists_monotone_shiftedSolver hΩ a b c hA hbc mu hshift
  have hconst : MemLp (fun _ : ℝ^n ↦ A) 2 μ := memLp_const A
  have hG : Measurable (fun z : (ℝ^n) × ℝ ↦ g z.2) :=
    hg.measurable.comp measurable_snd
  have hpoint : ∀ᵐ x ∂μ, ∀ s, ‖g s‖ ≤ A + C * ‖s‖ :=
    Eventually.of_forall fun _ ↦ hgrowth
  have hmem (w : L2) : MemLp (fun x ↦ g (w x)) 2 μ :=
    (Lp.memLp w).comp_of_norm_le hG hconst hpoint
  let F : L2 → L2 := Lp.superposition (fun _ ↦ g) hmem
  have hFcont : Continuous F :=
    Lp.continuous_superposition (by simp) hmem
      (Eventually.of_forall fun _ ↦ hg) hconst hpoint
  let N : L2 → L2 := fun w ↦ F w + mu • w
  have hNcont : Continuous N :=
    hFcont.add (continuous_id.const_smul mu)
  have hNrep (w : L2) :
      N w =ᵐ[μ] fun x ↦ g (w x) + mu * w x := by
    filter_upwards [Lp.coeFn_add (F w) (mu • w),
      Lp.coeFn_superposition (fun _ ↦ g) hmem w, Lp.coeFn_smul mu w]
      with x hadd hF hsmul
    simp only [N, hadd, Pi.add_apply, F, hF, hsmul, Pi.smul_apply, smul_eq_mul]
  have hNmono : Monotone N := by
    intro w z hwz
    have horder : ∀ᵐ x ∂μ, w x ≤ z x := AEEqFun.coeFn_le.mpr hwz
    apply AEEqFun.coeFn_le.mp
    filter_upwards [hNrep w, hNrep z, horder] with x hw hz hx
    rw [hw, hz]
    have hm : g (w x) + M * w x ≤ g (z x) + M * z x := hmono hx
    have hd := mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr hMmu)
    nlinarith
  let q : L2 := hconst.toLp (fun _ ↦ A)
  have hFbound (w : L2) : ‖F w‖ ≤ ‖q‖ + |C| * ‖w‖ :=
    norm_scalar_superposition_le g hconst hmem hgrowth w
  have hNbound (w : L2) : ‖N w‖ ≤ ‖q‖ + (|C| + |mu|) * ‖w‖ := by
    have := norm_add_le (F w) (mu • w)
    rw [norm_smul, Real.norm_eq_abs] at this
    linarith [hFbound w]
  have hlowerStep : lower ≤ J (R (N lower)) :=
    hlower mu hshift hMmu (N lower) (hNrep lower) (R (N lower)) (hR _)
  have hupperStep : J (R (N upper)) ≤ upper :=
    hupper mu hshift hMmu (N upper) (hNrep upper) (R (N upper)) (hR _)
  obtain ⟨u, hlowerU, hupperU, hu⟩ :=
    exists_fixedPoint_between_barriers hΩ hΩbounded R N hNcont ‖q‖ (|C| + |mu|)
      (add_nonneg (abs_nonneg C) (abs_nonneg mu)) hNbound
      (hRmono.comp hNmono) lower upper (AEEqFun.coeFn_le.mp hlr)
      hlowerStep hupperStep
  refine ⟨u, AEEqFun.coeFn_le.mpr hlowerU, AEEqFun.coeFn_le.mpr hupperU,
    hmem (J u), ?_⟩
  intro v
  have heq := hR (N (J u)) v
  rw [← hu] at heq
  change Bmu u v = loadFunctional (F (J u) + mu • J u) v at heq
  rw [shiftedDivergenceForm_apply, loadFunctional_add, add_apply,
    loadFunctional_smul, smul_apply, smul_eq_mul,
    loadFunctional_apply (J u)] at heq
  have hcancel : B u v = loadFunctional (F (J u)) v := add_right_cancel heq
  rw [scalar_superposition_pairing g hmem (J u) v] at hcancel
  exact hcancel


end PDE.Elliptic.Semilinear
