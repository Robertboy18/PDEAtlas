/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.DivergenceForm.Energy
public import PDE.Spaces.Sobolev.GraphSpace.Operators.BaseInjectivity
import PDE.Analysis.Normed.Operator.InjectiveLift

/-!
# Uniform estimates from interior Sobolev regularity

The pairs of forcing and H¹ state satisfying the full weak equation form a closed
linear subspace. Once local higher regularity has been proved on a fixed subdomain,
uniqueness of weak derivatives and the closed graph theorem give a uniform bound
with the original H¹ norm as remainder. A separate interior energy estimate is needed
to replace that remainder by the L² norm.
-/

@[expose] public noncomputable section

open scoped Sobolev

open MeasureTheory Set
open scoped ENNReal

namespace SobolevSpace.GraphSpace

variable {n m k : ℕ} {Ω V : Set (ℝ^n)}

/-- Qualitative regularity on a fixed subdomain gives a uniform Sobolev estimate
on the closed space of weak solutions. The remainder at this stage is the H¹ norm. -/
theorem exists_interior_estimate_of_regularizing
    (hΩ : IsOpen Ω) (hV : IsOpen V) (hVΩ : V ⊆ Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω)
    (hreg : ∀ (F : W^{m,2}(Ω)) (u : H¹(Ω)),
      IsInteriorWeakFullDivergenceSolution a b c (wkpBaseCoordinateCLM F) u →
      ∃ W : W^{k,2}(V),
        wkpBaseCoordinateCLM W = restrictDerivLp hVΩ (wkpBaseCoordinateCLM u)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : W^{m,2}(Ω)) (u : H¹(Ω)),
      IsInteriorWeakFullDivergenceSolution a b c (wkpBaseCoordinateCLM F) u →
      ∃ W : W^{k,2}(V),
        wkpBaseCoordinateCLM W = restrictDerivLp hVΩ (wkpBaseCoordinateCLM u) ∧
        ‖W‖ ≤ C * (‖F‖ + ‖u‖) := by
  let E := W^{m,2}(Ω) × H¹(Ω)
  let P : E →L[ℝ] W^{m,2}(Ω) := ContinuousLinearMap.fst ℝ _ _
  let Q : E →L[ℝ] H¹(Ω) := ContinuousLinearMap.snd ℝ _ _
  let R : E →L[ℝ] StrongDual ℝ (H¹₀(Ω)) :=
    (interiorFullDivergenceOperator a b c).comp Q -
      loadFunctionalCLM.comp (wkpBaseCoordinateCLM.comp P)
  let Z := R.ker
  let instZNorm : NormedAddCommGroup Z := inferInstance
  let instZSemiNorm : SeminormedAddCommGroup Z := instZNorm.toSeminormedAddCommGroup
  let instZSpace : NormedSpace ℝ Z := inferInstance
  let instZComplete : CompleteSpace Z := inferInstanceAs (CompleteSpace R.ker)
  let B : Z →L[ℝ] DerivLp n 2 V :=
    (restrictDerivLp hVΩ).comp (wkpBaseCoordinateCLM.comp (Q.comp Z.subtypeL))
  have hweak (z : Z) :
      IsInteriorWeakFullDivergenceSolution a b c
        (wkpBaseCoordinateCLM (P z)) (Q z) := by
    refine ⟨hΩ, ?_⟩
    have hz := z.property
    change interiorFullDivergenceOperator a b c (Q z) -
      loadFunctional (wkpBaseCoordinateCLM (P z)) = 0 at hz
    exact sub_eq_zero.mp hz
  obtain ⟨T, hT⟩ := ContinuousLinearMap.exists_lift_of_injective
    (wkpBaseCoordinateCLM (n := n) (m := k) (p := 2) (Ω := V)) B
    (wkpBaseCoordinateCLM_injective hV) (fun z ↦ hreg (P z) (Q z) (hweak z))
  refine ⟨‖T‖ + 1, by positivity, ?_⟩
  intro F u hu
  have hz : (F, u) ∈ Z := by
    change interiorFullDivergenceOperator a b c u -
      loadFunctional (wkpBaseCoordinateCLM F) = 0
    exact sub_eq_zero.mpr hu.2
  let z : Z := ⟨(F, u), hz⟩
  refine ⟨T z, DFunLike.congr_fun hT z, ?_⟩
  have hn : ‖z‖ ≤ ‖F‖ + ‖u‖ := by
    change max ‖F‖ ‖u‖ ≤ _
    exact max_le (le_add_of_nonneg_right (norm_nonneg u))
      (le_add_of_nonneg_left (norm_nonneg F))
  calc
    ‖T z‖ ≤ ‖T‖ * ‖z‖ := T.le_opNorm z
    _ ≤ ‖T‖ * (‖F‖ + ‖u‖) := mul_le_mul_of_nonneg_left hn (norm_nonneg T)
    _ ≤ (‖T‖ + 1) * (‖F‖ + ‖u‖) :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (by positivity)

/-- Interior energy removes the H¹ remainder from a proved local regularity result.
The regularity hypothesis is used on a larger interior set; no bound is assumed. -/
theorem exists_interior_estimate_with_L2_remainder
    (hΩ : IsOpen Ω) (hV : IsOpen V)
    (hcompact : IsCompact (closure V)) (hVΩ : closure V ⊆ Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω)
    {alpha : ℝ} (ha : AEUniformlyElliptic a alpha)
    (hreg : ∀ (N : Set (ℝ^n)), IsOpen N →
      IsCompact (closure N) → ∀ (hNΩ : closure N ⊆ Ω) (hVN : closure V ⊆ N),
      ∀ (F : W^{m,2}(N)) (u : H¹(N)),
      IsInteriorWeakFullDivergenceSolution
        (fun i j ↦ restrictDerivLp (subset_closure.trans hNΩ) (a i j))
        (fun i ↦ restrictDerivLp (subset_closure.trans hNΩ) (b i))
        (restrictDerivLp (subset_closure.trans hNΩ) c) (wkpBaseCoordinateCLM F) u →
      ∃ W : W^{k,2}(V),
        wkpBaseCoordinateCLM W =
          restrictDerivLp (subset_closure.trans hVN) (wkpBaseCoordinateCLM u)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : W^{m,2}(Ω)) (u : H¹(Ω)),
      IsInteriorWeakFullDivergenceSolution a b c (wkpBaseCoordinateCLM F) u →
      ∃ W : W^{k,2}(V),
        wkpBaseCoordinateCLM W =
          restrictDerivLp (subset_closure.trans hVΩ) (wkpBaseCoordinateCLM u) ∧
        ‖W‖ ≤ C * (‖F‖ + ‖wkpBaseCoordinateCLM u‖) := by
  obtain ⟨N, hN, hVN, hNΩ, hNc⟩ :=
    exists_open_between_and_isCompact_closure hcompact hΩ hVΩ
  let hsub : N ⊆ Ω := subset_closure.trans hNΩ
  obtain ⟨C₁, hC₁, henergy⟩ := exists_interior_h1_estimate a b c ha hN hNc hNΩ
  obtain ⟨C₂, hC₂, hbound⟩ := exists_interior_estimate_of_regularizing
    hN hV (subset_closure.trans hVN)
    (fun i j ↦ restrictDerivLp hsub (a i j))
    (fun i ↦ restrictDerivLp hsub (b i)) (restrictDerivLp hsub c)
    (hreg N hN hNc hNΩ hVN)
  refine ⟨C₂ * (1 + C₁), by positivity, ?_⟩
  intro F u hu
  let FN := restrictCLM hN.measurableSet hsub F
  let uN := restrictCLM hN.measurableSet hsub u
  obtain ⟨W, hW, hnorm⟩ := hbound FN uN (hu.restrict hN hsub)
  refine ⟨W, ?_, ?_⟩
  · rw [hW]
    apply Lp.ext
    filter_upwards [restrictDerivLp_apply_ae (subset_closure.trans hVN)
      (wkpBaseCoordinateCLM uN),
      ae_mono (domainMeasure_le (subset_closure.trans hVN))
        (restrictCLM_apply_ae hN.measurableSet hsub u (baseIndex n 1)),
      restrictDerivLp_apply_ae (subset_closure.trans hVΩ) (wkpBaseCoordinateCLM u)]
      with x hx hy hz
    exact hx.trans (hy.trans hz.symm)
  · have hfn : ‖FN‖ ≤ ‖F‖ := norm_restrictCLM_apply_le hN.measurableSet hsub F
    have hun : ‖uN‖ ≤ C₁ * (‖F‖ + ‖wkpBaseCoordinateCLM u‖) :=
      (henergy (wkpBaseCoordinateCLM F) u hu).trans
        (mul_le_mul_of_nonneg_left
          (add_le_add (wkpBaseCoordinateCLM_norm_le F) le_rfl) hC₁.le)
    calc
      ‖W‖ ≤ C₂ * (‖FN‖ + ‖uN‖) := hnorm
      _ ≤ C₂ * (‖F‖ + C₁ * (‖F‖ + ‖wkpBaseCoordinateCLM u‖)) := by gcongr
      _ ≤ C₂ * (1 + C₁) * (‖F‖ + ‖wkpBaseCoordinateCLM u‖) := by
        nlinarith [mul_nonneg hC₂.le (norm_nonneg (wkpBaseCoordinateCLM u))]

end SobolevSpace.GraphSpace
