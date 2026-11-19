/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Time.WeakDerivative.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Localization of weak time derivatives

If `g` is the weak time derivative of the Banach-valued trajectory `f` on an open set
`U ⊆ ℝ` and `χ : ℝ → ℝ` is smooth, then `χ f` has weak derivative `χ g + χ' f` on `U`. This
is the product rule for weak derivatives (Evans §5.2.3, Theorem 1(iv), here in one variable
with values in a Banach space); its proof is the classical
Leibniz rule applied to the scalar test `χ φ`, which is again a smooth compactly supported
test in `U`. When `χ` itself has compact support inside `U`, the product `χ f` is a weak
evolution on all of `ℝ` with compactly supported derivative. This is how the global
Lions–Magenes regularity theorem is brought to bear on a finite-interval trajectory: cut
off inside `(a, b)`, apply the global theorem, and discard the cutoff on a compact
subinterval where `χ = 1`.

## Main results

* `HasWeakTimeDerivativeOn.smul_contDiff`: the weak Leibniz rule
  `(χ f)' = χ g + χ' f` on an open set `U`.
* `HasWeakTimeDerivativeOn.smul_contDiff_global`: for `χ ∈ C_c^∞` with support in `U`,
  the cut-off trajectory is a weak evolution on `Set.univ`.

## Implementation notes

Openness of `U` is needed for the local statement so that `χ φ` still has topological
support in `U` and so that local integrability of `χ f`, `χ g`, `χ' f` on `U` follows from
that of `f` and `g`. In the global statement openness is not required, since the support
of `χ` is compact and contained in `U`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.2.3, Theorem 1(iv) (Leibniz's formula).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory
open scoped ENNReal Topology

namespace PDE.Analysis.Evolution

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

namespace HasWeakTimeDerivativeOn

/-- Leibniz pairing behind `smul_contDiff` and `smul_contDiff_global`: testing
the weak derivative against `χ φ` gives the tested product rule for `χ f`. -/
private theorem integral_leibniz_pairing
    {U : Set ℝ} {f g : ℝ → X}
    (h : HasWeakTimeDerivativeOn U f g)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (ell : StrongDual ℝ X) (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hθcompact : HasCompactSupport (χ * φ))
    (hθsupp : closure (Function.support (χ * φ)) ⊆ U)
    (hB : Integrable (fun t ↦ ell (f t) * (deriv χ t * φ t)))
    (hD : Integrable (fun t ↦ ell (f t) * (χ t * deriv φ t))) :
    (∫ t, (χ t * ell (g t) + deriv χ t * ell (f t)) * φ t) =
      -(∫ t, χ t * ell (f t) * deriv φ t) := by
  let qf : ℝ → ℝ := ell ∘ f
  let qg : ℝ → ℝ := ell ∘ g
  change Integrable (fun t ↦ qf t * (deriv χ t * φ t)) at hB
  change Integrable (fun t ↦ qf t * (χ t * deriv φ t)) at hD
  have hqg : LocallyIntegrableOn qg U (volume : Measure ℝ) :=
    ell.locallyIntegrableOn_comp h.locallyIntegrable_g
  let θ : ℝ → ℝ := χ * φ
  have hθ : ContDiff ℝ (⊤ : ℕ∞) θ := hχ.mul hφ
  have hA : Integrable (fun t ↦ qg t * (χ t * φ t)) :=
    integrable_mul_test hqg hθ.continuous hθcompact hθsupp
  have hbase := h.integral_eq ell θ hθ hθcompact hθsupp
  have hbase' : (∫ t, qg t * (χ t * φ t)) =
      -(∫ t, qf t * deriv θ t) := by
    simpa [qf, qg, θ] using hbase
  have hderivθ (t : ℝ) :
      deriv θ t = deriv χ t * φ t + χ t * deriv φ t := by
    have hχt := (hχ.differentiable (by simp) t).hasDerivAt
    have hφt := (hφ.differentiable (by simp) t).hasDerivAt
    simpa [θ] using (hχt.mul hφt).deriv
  have hderivIntegral :
      (∫ t, qf t * deriv θ t) =
        (∫ t, qf t * (deriv χ t * φ t)) +
          ∫ t, qf t * (χ t * deriv φ t) := by
    calc
      (∫ t, qf t * deriv θ t) =
          ∫ t, (qf t * (deriv χ t * φ t) +
            qf t * (χ t * deriv φ t)) := by
              apply integral_congr_ae
              filter_upwards with t
              rw [hderivθ]
              ring
      _ = _ := integral_add hB hD
  have hscalar :
      (∫ t, (qg t * (χ t * φ t) +
        qf t * (deriv χ t * φ t))) =
        -(∫ t, qf t * (χ t * deriv φ t)) := by
    rw [integral_add hA hB, hbase', hderivIntegral]
    ring
  calc
    (∫ t, (χ t * ell (g t) + deriv χ t * ell (f t)) * φ t) =
        ∫ t, (qg t * (χ t * φ t) +
          qf t * (deriv χ t * φ t)) := by
            apply integral_congr_ae
            filter_upwards with t
            simp [qf, qg]
            ring
    _ = -(∫ t, qf t * (χ t * deriv φ t)) := hscalar
    _ = -(∫ t, χ t * ell (f t) * deriv φ t) := by
          congr 1
          apply integral_congr_ae
          filter_upwards with t
          simp [qf]
          ring

/-- Weak Leibniz rule for multiplication by a smooth scalar cutoff.  This is
the localization mechanism for Banach-valued weak evolutions:
`(χ f)' = χ g + χ' f` in distributions on `U`. -/
theorem smul_contDiff
    {U : Set ℝ} (hU : IsOpen U) {f g : ℝ → X}
    (h : HasWeakTimeDerivativeOn U f g)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) :
    HasWeakTimeDerivativeOn U
      (fun t ↦ χ t • f t)
      (fun t ↦ χ t • g t + deriv χ t • f t) := by
  have hUlc : IsLocallyClosed U := hU.isLocallyClosed
  refine ⟨
    MeasureTheory.LocallyIntegrableOn.continuousOn_smul hUlc
      h.locallyIntegrable_f hχ.continuous.continuousOn,
    ?_, ?_⟩
  · exact
      (MeasureTheory.LocallyIntegrableOn.continuousOn_smul hUlc
        h.locallyIntegrable_g
        hχ.continuous.continuousOn).add
      (MeasureTheory.LocallyIntegrableOn.continuousOn_smul hUlc
        h.locallyIntegrable_f
        (contDiff_infty_iff_deriv.mp hχ).2.continuous.continuousOn)
  · intro ell φ hφ hφcompact hsupp
    let qf : ℝ → ℝ := ell ∘ f
    have hqf : LocallyIntegrableOn qf U (volume : Measure ℝ) :=
      ell.locallyIntegrableOn_comp h.locallyIntegrable_f
    have hdχ : ContDiff ℝ (⊤ : ℕ∞) (deriv χ) :=
      (contDiff_infty_iff_deriv.mp hχ).2
    have hdφ : ContDiff ℝ (⊤ : ℕ∞) (deriv φ) :=
      (contDiff_infty_iff_deriv.mp hφ).2
    let θ : ℝ → ℝ := χ * φ
    have hθcompact : HasCompactSupport θ := hφcompact.mul_left
    have hθsupp : closure (Function.support θ) ⊆ U := by
      have hsub : closure (Function.support θ) ⊆
          closure (Function.support φ) := by
        change closure (Function.support (χ * φ)) ⊆
          closure (Function.support φ)
        exact tsupport_mul_subset_right
      exact hsub.trans hsupp
    have hB : Integrable (fun t ↦ qf t * (deriv χ t * φ t)) := by
      apply integrable_mul_test hqf
      · exact (hdχ.mul hφ).continuous
      · exact hφcompact.mul_left
      · have hsub : closure (Function.support (fun t ↦ deriv χ t * φ t)) ⊆
            closure (Function.support φ) :=
          tsupport_mul_subset_right
        exact hsub.trans hsupp
    have hD : Integrable (fun t ↦ qf t * (χ t * deriv φ t)) := by
      apply integrable_mul_test hqf
      · exact (hχ.mul hdφ).continuous
      · exact hφcompact.deriv.mul_left
      · have hsub₁ : closure (Function.support (fun t ↦ χ t * deriv φ t)) ⊆
            closure (Function.support (deriv φ)) :=
          tsupport_mul_subset_right
        exact hsub₁.trans (tsupport_deriv_subset.trans hsupp)
    simp only [map_add, map_smul, smul_eq_mul]
    exact integral_leibniz_pairing h χ hχ ell φ hφ hθcompact hθsupp hB hD

/-- A smooth cutoff compactly supported in `U` turns a local weak evolution
into a globally defined compactly supported weak evolution.  This is the
precise localization step used to reduce finite-interval Lions–Magenes
regularity to the global theorem. -/
theorem smul_contDiff_global
    {U : Set ℝ} {f g : ℝ → X}
    (h : HasWeakTimeDerivativeOn U f g)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχcompact : HasCompactSupport χ)
    (hχsupp : closure (Function.support χ) ⊆ U) :
    HasWeakTimeDerivativeOn Set.univ
      (fun t ↦ χ t • f t)
      (fun t ↦ χ t • g t + deriv χ t • f t) := by
  have hdχ : ContDiff ℝ (⊤ : ℕ∞) (deriv χ) :=
    (contDiff_infty_iff_deriv.mp hχ).2
  have hdχcompact : HasCompactSupport (deriv χ) := hχcompact.deriv
  have hdχsupp : closure (Function.support (deriv χ)) ⊆ U :=
    tsupport_deriv_subset.trans hχsupp
  have hFint : Integrable (fun t ↦ χ t • f t) :=
    integrable_smul_test h.locallyIntegrable_f hχ.continuous hχcompact hχsupp
  have hG₁int : Integrable (fun t ↦ χ t • g t) :=
    integrable_smul_test h.locallyIntegrable_g hχ.continuous hχcompact hχsupp
  have hG₂int : Integrable (fun t ↦ deriv χ t • f t) :=
    integrable_smul_test h.locallyIntegrable_f hdχ.continuous
      hdχcompact hdχsupp
  refine ⟨hFint.locallyIntegrable.locallyIntegrableOn Set.univ,
    (hG₁int.add hG₂int).locallyIntegrable.locallyIntegrableOn Set.univ, ?_⟩
  intro ell φ hφ hφcompact _hsuppUniv
  let qf : ℝ → ℝ := ell ∘ f
  have hqf : LocallyIntegrableOn qf U (volume : Measure ℝ) :=
    ell.locallyIntegrableOn_comp h.locallyIntegrable_f
  have hdφ : ContDiff ℝ (⊤ : ℕ∞) (deriv φ) :=
    (contDiff_infty_iff_deriv.mp hφ).2
  let θ : ℝ → ℝ := χ * φ
  have hθcompact : HasCompactSupport θ := hχcompact.mul_right
  have hθsupp : closure (Function.support θ) ⊆ U := by
    have hsub : closure (Function.support θ) ⊆
        closure (Function.support χ) := by
      change closure (Function.support (χ * φ)) ⊆
        closure (Function.support χ)
      exact tsupport_mul_subset_left
    exact hsub.trans hχsupp
  have hB : Integrable (fun t ↦ qf t * (deriv χ t * φ t)) := by
    apply integrable_mul_test hqf
    · exact (hdχ.mul hφ).continuous
    · exact hdχcompact.mul_right
    · have hsub : closure (Function.support (fun t ↦ deriv χ t * φ t)) ⊆
          closure (Function.support (deriv χ)) :=
        tsupport_mul_subset_left
      exact hsub.trans hdχsupp
  have hD : Integrable (fun t ↦ qf t * (χ t * deriv φ t)) := by
    apply integrable_mul_test hqf
    · exact (hχ.mul hdφ).continuous
    · exact hχcompact.mul_right
    · have hsub : closure (Function.support (fun t ↦ χ t * deriv φ t)) ⊆
          closure (Function.support χ) :=
        tsupport_mul_subset_left
      exact hsub.trans hχsupp
  simp only [map_add, map_smul, smul_eq_mul]
  exact integral_leibniz_pairing h χ hχ ell φ hφ hθcompact hθsupp hB hD

end HasWeakTimeDerivativeOn

end PDE.Analysis.Evolution
