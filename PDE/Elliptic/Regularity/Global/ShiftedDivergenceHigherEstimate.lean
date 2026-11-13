/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Global.ShiftedDivergenceHigher
public import PDE.Elliptic.Regularity.Global.ShiftedDivergenceSolver
public import PDE.Elliptic.Regularity.SolutionOperator.H2

/-!
# Quantitative global regularity for the full operator

The all-order regularity induction yields `‖u‖_{H^{m+2}} ≤ K (‖f‖_{H^m} + ‖u‖_{L²})` for every
scalar shift, including noncoercive shifts
(`exists_global_higherOrder_estimate_of_weak_shifted_full_divergence_solution`). The constant is
independent of the solution and forcing. At shift zero this is the estimate (77) of Evans's §6.3.2,
Theorem 5 (Higher boundary regularity).

## How it works

Evans obtains (77) by carrying the constants through his proof. We obtain the constant from the
closed graph theorem instead. Pairs `(f, u)` are realized as the kernel of a bounded map on
`H^m × L²`, using a coercive shifted inverse, and this kernel is complete. Uniqueness of weak
derivatives makes the regularity lift linear, and its graph is closed because the base coordinate is
continuous. The proof does not give an explicit constant uniform over coefficient families. The
operational boundary atlas and ambient smooth principal representatives are inherited from the
qualitative theorem.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, Theorem 5 (Higher boundary regularity), (72)-(77),
  pp. 340-341.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace SobolevSpace.GraphSpace.BoundaryRegularity

open Filter MeasureTheory Set
open scoped ENNReal Topology

variable {n : ℕ} [Fact (0 < n)] {Omega : Set (ℝ^n)}

/-- Global full-operator regularity with the `L²` remainder needed at arbitrary
shifts. The constant is fixed before the forcing and weak solution are chosen.
No coercivity or uniqueness at `lambda` is required. -/
theorem exists_global_higherOrder_estimate_of_weak_shifted_full_divergence_solution
    (m : ℕ)
    (hOmega : SobolevSpace.C2BoundaryAtlas n Omega)
    (hChart : ∀ i : Fin hOmega.toC1ExtensionAtlas.N,
      ContDiff ℝ (m + 2) (fun x ↦ hOmega.toC1ExtensionAtlas.chart i x))
    (hChartSymm : ∀ i : Fin hOmega.toC1ExtensionAtlas.N,
      ContDiff ℝ (m + 1) (fun y ↦ (hOmega.toC1ExtensionAtlas.chart i).symm y))
    (A : Fin n → Fin n → W^{m + 1,∞}(Omega))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j,
      ⇑(wkpBaseCoordinateCLM (A i j)) =ᵐ[domainMeasure n Omega] fun x ↦ a x i j)
    (haContDiff : ∀ i j, ContDiff ℝ (m + 1) (fun x ↦ a x i j))
    (B : Fin n → W^{m,∞}(Omega))
    (C : W^{m,∞}(Omega))
    (lambda alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Omega, MatrixEllipticLowerBound (a x) alpha) :
    ∃ K : ℝ, 0 < K ∧ ∀ (F : W^{m,2}(Omega)) (u : H¹₀(Omega)),
      IsWeakShiftedFullDivergenceSolution
        (fun i j ↦ wkpBaseCoordinateCLM (A i j))
        (fun i ↦ wkpBaseCoordinateCLM (B i)) (wkpBaseCoordinateCLM C)
        lambda (wkpBaseCoordinateCLM F) 0 u →
      ∃ W : W^{m + 2,2}(Omega),
        wkpBaseCoordinateCLM W = baseCoordCLM u ∧
        ‖W‖ ≤ K * (‖F‖ + ‖baseCoordCLM u‖) := by
  classical
  let coeffA := fun i j ↦ wkpBaseCoordinateCLM (A i j)
  let coeffB := fun i ↦ wkpBaseCoordinateCLM (B i)
  let coeffC := wkpBaseCoordinateCLM C
  let A1 := fun i j ↦ lowerOrderCLM
    (n := n) (k := 1) (m := m + 1) (p := ∞) (Ω := Omega) (by omega) (A i j)
  have hA : IntegratedElliptic (multiplicationCoefficientOperator coeffA) alpha :=
    integratedElliptic_multiplication_of_ae coeffA
      (coefficientBase_aeUniformlyElliptic hOmega.toC1ExtensionAtlas.isOpen.measurableSet
        A1 a (fun i j ↦ by simpa [A1] using haRep i j) alpha halpha hElliptic)
  let mu := coerciveShift (n := n) alpha ‖coeffB‖ ‖coeffC‖
  let S := fullDivergenceWeakSolveCLM coeffA coeffB coeffC hA
    (norm_nonneg _) (norm_nonneg _) (fun i ↦ norm_le_pi_norm coeffB i) le_rfl
    (mu := mu) le_rfl
  let fst : (W^{m,2}(Omega) × DerivLp n 2 Omega) →L[ℝ]
      W^{m,2}(Omega) := ContinuousLinearMap.fst ℝ _ _
  let snd : (W^{m,2}(Omega) × DerivLp n 2 Omega) →L[ℝ]
      DerivLp n 2 Omega := ContinuousLinearMap.snd ℝ _ _
  let T := S.comp (wkpBaseCoordinateCLM.comp fst + (mu - lambda) • snd)
  let R := baseCoordCLM.comp T - snd
  let Z := R.ker
  let instZNorm : NormedAddCommGroup Z := inferInstance
  let instZSemiNorm : SeminormedAddCommGroup Z := instZNorm.toSeminormedAddCommGroup
  let instZSpace : NormedSpace ℝ Z := inferInstance
  let instZComplete : CompleteSpace Z := inferInstanceAs (CompleteSpace R.ker)
  let zbase : Z →L[ℝ] DerivLp n 2 Omega := snd.comp R.ker.subtypeL
  have hreg (z : Z) : ∃ W : W^{m + 2,2}(Omega),
      wkpBaseCoordinateCLM W = zbase z := by
    have hz : baseCoordCLM (T z.val) = z.val.2 := sub_eq_zero.mp z.property
    have hweakMu := fullDivergenceWeakSolveCLM_isWeakSolution coeffA coeffB coeffC hA
      (norm_nonneg _) (norm_nonneg _) (fun i ↦ norm_le_pi_norm coeffB i) le_rfl
      (mu := mu) le_rfl hOmega.toC1ExtensionAtlas.isOpen
      (wkpBaseCoordinateCLM z.val.1 + (mu - lambda) • z.val.2)
    have hweak : IsWeakShiftedFullDivergenceSolution coeffA coeffB coeffC
        lambda (wkpBaseCoordinateCLM z.val.1) 0 (T z.val) :=
      (isWeakShiftedFullDivergenceSolution_change_shift coeffA coeffB coeffC lambda mu _ _).2
        (by rw [hz]; exact hweakMu)
    obtain ⟨W, hW⟩ :=
      globalHigherRegularity.exists_of_weak_shifted_full_divergence_solution
        m hOmega hChart hChartSymm A a haRep haContDiff B C lambda z.val.1
        (T z.val) hweak alpha halpha hElliptic
    exact ⟨W, (Lp.ext hW).trans hz⟩
  choose W hW using hreg
  let g : Z →ₗ[ℝ] W^{m + 2,2}(Omega) :=
    { toFun := W
      map_add' := fun x y ↦ by
        apply wkpBaseCoordinateCLM_injective hOmega.toC1ExtensionAtlas.isOpen
        simp only [map_add, hW]
      map_smul' := fun c x ↦ by
        apply wkpBaseCoordinateCLM_injective hOmega.toC1ExtensionAtlas.isOpen
        simp only [map_smul, hW, RingHom.id_apply] }
  let lift : Z →L[ℝ] W^{m + 2,2}(Omega) :=
    ContinuousLinearMap.ofSeqClosedGraph (𝕜 := ℝ) (g := g) fun zs z V hzs hV ↦ by
      have hOut := (wkpBaseCoordinateCLM
        (n := n) (m := m + 2) (p := 2) (Ω := Omega)).continuous.tendsto V |>.comp hV
      change Tendsto (fun k ↦ wkpBaseCoordinateCLM (g (zs k))) _ _ at hOut
      rw [show (fun k ↦ wkpBaseCoordinateCLM (g (zs k))) = fun k ↦ zbase (zs k) from
        funext fun k ↦ hW (zs k)] at hOut
      exact wkpBaseCoordinateCLM_injective hOmega.toC1ExtensionAtlas.isOpen
        ((tendsto_nhds_unique hOut ((zbase.continuous.tendsto z).comp hzs)).trans (hW z).symm)
  refine ⟨‖lift‖ + 1, by positivity, ?_⟩
  intro F u hu
  have hueq : u = T (F, baseCoordCLM u) :=
    eq_fullDivergenceWeakSolveCLM coeffA coeffB coeffC hA
      (norm_nonneg _) (norm_nonneg _) (fun i ↦ norm_le_pi_norm coeffB i) le_rfl
      (mu := mu) le_rfl _
      ((isWeakShiftedFullDivergenceSolution_change_shift
        coeffA coeffB coeffC lambda mu _ u).1 hu)
  let z : Z := ⟨(F, baseCoordCLM u), by
    change baseCoordCLM (T (F, baseCoordCLM u)) - baseCoordCLM u = 0
    rw [← hueq, sub_self]⟩
  refine ⟨lift z, hW z, ?_⟩
  have hz : ‖z‖ ≤ ‖F‖ + ‖baseCoordCLM u‖ :=
    max_le (le_add_of_nonneg_right (norm_nonneg _))
      (le_add_of_nonneg_left (norm_nonneg _))
  calc
    ‖lift z‖ ≤ ‖lift‖ * ‖z‖ := lift.le_opNorm z
    _ ≤ (‖lift‖ + 1) * (‖F‖ + ‖baseCoordCLM u‖) := by gcongr; linarith

end SobolevSpace.GraphSpace.BoundaryRegularity
