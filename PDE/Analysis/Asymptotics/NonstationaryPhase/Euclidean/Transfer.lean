/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Asymptotics.OscillatoryIntegral.Calculus
public import PDE.Analysis.Integration.CompactByParts
public import PDE.FDeriv.PartialDeriv.Support
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Transferring derivatives for a Euclidean nonstationary phase

Normalize the gradient by its squared length and multiply by the amplitude.
Only the product needs to be smooth: at critical points outside the amplitude's
topological support it is locally zero. Taking its divergence preserves support,
so this construction can be iterated without assuming a globally noncritical phase.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.NonstationaryPhase

open MeasureTheory Set
open scoped Topology

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The amplitude weighted by one coordinate of the normalized phase gradient.
Division is total; smoothness will only require noncriticality on the support. -/
def normalizedAmplitude (φ : ℝ^n → ℝ) (f : ℝ^n → E) (i : Fin n) (x : ℝ^n) : E :=
  ((∂[i] φ) x / ∑ j : Fin n, (∂[j] φ) x ^ 2) • f x

private theorem gradient_sq_ne_zero {φ : ℝ^n → ℝ} {x : ℝ^n}
    (hφ : fderiv ℝ φ x ≠ 0) :
    (∑ j : Fin n, (∂[j] φ) x ^ 2) ≠ 0 := by
  intro hzero
  have hz : ∀ j : Fin n, (∂[j] φ) x = 0 :=
    fun j ↦ (Finset.sum_sq_eq_zero_iff _ _).mp hzero j (Finset.mem_univ j)
  apply hφ
  rw [fderiv_eq_sum_partialDeriv_smul_proj]
  simp only [hz, zero_smul, Finset.sum_const_zero]

/-- Normalizing the amplitude does not enlarge its topological support. -/
theorem tsupport_normalizedAmplitude_subset (φ : ℝ^n → ℝ) (f : ℝ^n → E) (i : Fin n) :
    tsupport (normalizedAmplitude φ f i) ⊆ tsupport f :=
  tsupport_smul_subset_right _ _

/-- The normalized product is smooth even if the phase has critical points
away from the amplitude's support. -/
theorem contDiff_normalizedAmplitude {φ : ℝ^n → ℝ} {f : ℝ^n → E}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hne : ∀ x ∈ tsupport f, fderiv ℝ φ x ≠ 0) (i : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (normalizedAmplitude φ f i) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport f
  · exact ((contDiff_top_partialDeriv hφ).contDiffAt.div
      ((ContDiff.sum fun j _ ↦ (contDiff_top_partialDeriv hφ).pow 2).contDiffAt)
      (gradient_sq_ne_zero (hne x hx))).smul hf.contDiffAt
  · apply (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx] with y hy
    simp only [normalizedAmplitude, image_eq_zero_of_notMem_tsupport hy, smul_zero]

/-- Divergence of the amplitude multiplied by the normalized phase gradient.
One integration by parts introduces its negative and one inverse frequency. -/
def transferAmplitude (φ : ℝ^n → ℝ) (f : ℝ^n → E) (x : ℝ^n) : E :=
  ∑ i : Fin n, (∂[i] (normalizedAmplitude φ f i)) x

/-- Transferring one derivative preserves smoothness. -/
theorem contDiff_transferAmplitude {φ : ℝ^n → ℝ} {f : ℝ^n → E}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hne : ∀ x ∈ tsupport f, fderiv ℝ φ x ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞) (transferAmplitude φ f) :=
  ContDiff.sum fun i _ ↦
    contDiff_top_partialDeriv (contDiff_normalizedAmplitude hφ hf hne i)

/-- Transferring derivatives cannot create support outside the original amplitude. -/
theorem tsupport_transferAmplitude_subset (φ : ℝ^n → ℝ) (f : ℝ^n → E) :
    tsupport (transferAmplitude φ f) ⊆ tsupport f := by
  apply closure_minimal _ (isClosed_tsupport f)
  intro x hx
  by_contra hxf
  apply hx
  apply Finset.sum_eq_zero
  intro i _
  exact partialDeriv_eq_zero_of_notMem_tsupport i
    (fun hi ↦ hxf (tsupport_normalizedAmplitude_subset φ f i hi))

private theorem sum_partialDeriv_smul_normalizedAmplitude
    (φ : ℝ^n → ℝ) (f : ℝ^n → E)
    (hne : ∀ x ∈ tsupport f, fderiv ℝ φ x ≠ 0) (x : ℝ^n) :
    (∑ i : Fin n, (∂[i] φ) x • normalizedAmplitude φ f i x) = f x := by
  by_cases hx : f x = 0
  · simp only [normalizedAmplitude, hx, smul_zero, Finset.sum_const_zero]
  · have hden := gradient_sq_ne_zero (hne x (subset_closure hx))
    simp only [normalizedAmplitude, smul_smul, ← mul_div_assoc, ← sq,
      ← Finset.sum_smul, ← Finset.sum_div, div_self hden, one_smul]

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

omit [IsScalarTower ℝ ℂ E] in
/-- One integration by parts transfers the normalized gradient to the amplitude.
Noncriticality is required only on its compact support. -/
theorem integral_osc_smul_transferAmplitude {φ : ℝ^n → ℝ} {f : ℝ^n → E}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hcompact : HasCompactSupport f)
    (hne : ∀ x ∈ tsupport f, fderiv ℝ φ x ≠ 0) (ξ : ℝ) :
    ((ξ : ℂ) * Complex.I) • (∫ x, osc ξ (φ x) • f x) =
      -(∫ x, osc ξ (φ x) • transferAmplitude φ f x) := by
  have hosc : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ osc ξ (φ x)) := by
    unfold osc
    exact Complex.contDiff_exp.comp
      ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hφ)).mul contDiff_const)
  have hnc (i : Fin n) : HasCompactSupport (normalizedAmplitude φ f i) :=
    hcompact.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_normalizedAmplitude_subset φ f i)
  have hnd (i : Fin n) := contDiff_normalizedAmplitude hφ hf hne i
  have hleft (i : Fin n) : Integrable
      (fun x ↦ (∂[i] (fun y ↦ osc ξ (φ y))) x • normalizedAmplitude φ f i x) :=
    ((contDiff_top_partialDeriv hosc).continuous.smul
      (hnd i).continuous).integrable_of_hasCompactSupport (hnc i).smul_left
  have hright (i : Fin n) : Integrable
      (fun x ↦ osc ξ (φ x) • (∂[i] (normalizedAmplitude φ f i)) x) :=
    (hosc.continuous.smul (contDiff_top_partialDeriv
      (hnd i)).continuous).integrable_of_hasCompactSupport ((hnc i).partialDeriv i).smul_left
  have hparts (i : Fin n) :
      (∫ x, (∂[i] (fun y ↦ osc ξ (φ y))) x • normalizedAmplitude φ f i x) =
        -(∫ x, osc ξ (φ x) • (∂[i] (normalizedAmplitude φ f i)) x) :=
    integral_bilinear_partialDeriv_eq_neg
      (ContinuousLinearMap.lsmul ℝ ℂ).flip i ((hnd i).of_le (by simp))
      (hosc.of_le (by simp)) (hnc i)
  have hsum (x : ℝ^n) :
      (∑ i : Fin n, (∂[i] (fun y ↦ osc ξ (φ y))) x • normalizedAmplitude φ f i x) =
        ((ξ : ℂ) * Complex.I) • (osc ξ (φ x) • f x) := by
    simp_rw [PDE.Analysis.partialDeriv_osc_comp (hφ.differentiable (by simp) x),
      smul_assoc, smul_comm ((∂[_] φ) x), ← Finset.smul_sum]
    rw [sum_partialDeriv_smul_normalizedAmplitude φ f hne x, mul_smul]
  calc
    ((ξ : ℂ) * Complex.I) • (∫ x, osc ξ (φ x) • f x) =
        ∫ x, ∑ i : Fin n,
          (∂[i] (fun y ↦ osc ξ (φ y))) x • normalizedAmplitude φ f i x := by
      rw [← integral_smul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦ (hsum x).symm)
    _ = ∑ i : Fin n, ∫ x,
        (∂[i] (fun y ↦ osc ξ (φ y))) x • normalizedAmplitude φ f i x :=
      integral_finsetSum _ (fun i _ ↦ hleft i)
    _ = -(∑ i : Fin n, ∫ x,
        osc ξ (φ x) • (∂[i] (normalizedAmplitude φ f i)) x) := by
      simp only [hparts, Finset.sum_neg_distrib]
    _ = -(∫ x, osc ξ (φ x) • transferAmplitude φ f x) := by
      simp only [transferAmplitude, Finset.smul_sum]
      rw [integral_finsetSum _ (fun i _ ↦ hright i)]

end PDE.Analysis.NonstationaryPhase
