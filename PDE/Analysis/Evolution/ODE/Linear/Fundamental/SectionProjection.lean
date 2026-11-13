/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Linear.Fundamental.Interval
public import PDE.Common.Euclidean

/-!
# Transport to a fixed terminal section

Let `γ` solve a smooth autonomous equation `γ' = f(γ)` in `ℝ³` on `[a, b]`, and let
`S` be a fundamental solution of the linearized equation `Φ' = Df(γ(t)) Φ`. The
tangent `v = f ∘ γ` solves the linearized equation, so the propagator carries it to
the terminal time: `U(b, t) v(t) = v(b)`. If `L : ℝ³ → ℝ²` has kernel spanned by
`v(b)`, then `π(t) = L ∘ U(b, t)` is a smooth family of surjections with
`ker π(t)` spanned by `v(t)`. The propagator `t ↦ U(T, t)` with fixed final time
is `Cⁿ` on `[a, b]` when the coefficient is.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace PDE.Analysis.Evolution.FundamentalSolution

/-- Smoothness in the starting time of the interval propagator, with its final time
fixed: if the coefficient is `Cⁿ` on `[a, b]`, so is `t ↦ U(T, t)`, for any `T`.
This follows from the equation `Ψ' = -Ψ C` of the inverse fundamental path. The
smoothness is relative to the closed interval, including its endpoints. -/
theorem contDiffOn_propagator_right_Icc
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    {C : ℝ → A} {a b t₀ : ℝ} {n : ℕ∞}
    (S : FundamentalSolution C t₀ (Icc a b))
    (hC : ContDiffOn ℝ n C (Icc a b)) (T : ℝ) :
    ContDiffOn ℝ n (fun t ↦ S.propagator T t) (Icc a b) := by
  have hfield : ContDiffOn ℝ n
      (Function.uncurry (fun (t : ℝ) (x : A) ↦ -(x * C t)))
      ((Icc a b) ×ˢ (univ : Set A)) := by
    exact (contDiffOn_snd.mul
      (hC.comp contDiffOn_fst (fun _ hp ↦ hp.1))).neg
  have hbackward : ContDiffOn ℝ n S.backward (Icc a b) :=
    ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt hfield
      S.backward_hasDerivWithinAt (fun _ _ ↦ mem_univ _)
  simpa only [propagator] using
    (contDiffOn_const.mul hbackward :
      ContDiffOn ℝ n (fun t ↦ S.forward T * S.backward t) (Icc a b))

end PDE.Analysis.Evolution.FundamentalSolution

namespace PDE.Analysis.Evolution

/-- The fixed-section projection for an autonomous orbit `γ` in `ℝ³` and a fundamental
solution of its linearization. With `v = f ∘ γ` and `π(t) = L ∘ U(b, t)`, the
orbit, `v` and `π` are smooth on `[a, b]` (relative to the interval), `π` is smooth
at interior times, `π(b) = L`, and for every `t ∈ [a, b]` one has `γ'(t) = v(t)`,
`v' = Df(γ) v`, `U(b, t) v(t) = v(b)`, `ker π(t) = span {v(t)}`, `v(t) ≠ 0`, and
`π(t)` is surjective of rank two. The kernel condition `ker L = span {v(b)}`
forces the last three properties. -/
theorem finite_section_projection_of_autonomous
    {f : (ℝ^3) → ℝ^3} {γ : ℝ → ℝ^3} {Ω : Set (ℝ^3)}
    {a b t₀ : ℝ} (hab : a ≤ b) (hΩ : IsOpen Ω)
    (hf : ContDiffOn ℝ ∞ f Ω)
    (hmem : MapsTo γ (Icc a b) Ω)
    (hode : ∀ t ∈ Icc a b, HasDerivAt γ (f (γ t)) t)
    (S : FundamentalSolution (fun t ↦ fderiv ℝ f (γ t)) t₀ (Icc a b))
    (L : (ℝ^3) →L[ℝ] (ℝ^2))
    (hL : LinearMap.ker L.toLinearMap =
      Submodule.span ℝ ({f (γ b)} : Set (ℝ^3))) :
    let v := fun t ↦ f (γ t)
    let π := fun t ↦ L.comp (S.propagator b t)
    ContDiffOn ℝ ∞ γ (Icc a b) ∧
    ContDiffOn ℝ ∞ v (Icc a b) ∧
    ContDiffOn ℝ ∞ π (Icc a b) ∧
    (∀ t ∈ Ioo a b, ContDiffAt ℝ ∞ π t) ∧
    π b = L ∧
    ∀ t ∈ Icc a b,
      deriv γ t = v t ∧
      HasDerivAt v (fderiv ℝ f (γ t) (v t)) t ∧
      S.propagator b t (v t) = v b ∧
      LinearMap.ker (π t).toLinearMap = Submodule.span ℝ ({v t} : Set (ℝ^3)) ∧
      v t ≠ 0 ∧
      Module.finrank ℝ (LinearMap.range (π t).toLinearMap) = 2 ∧
      Function.Surjective (π t) := by
  let v := fun t ↦ f (γ t)
  let π := fun t ↦ L.comp (S.propagator b t)
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hfield : ContDiffOn ℝ ∞ (Function.uncurry (fun (_ : ℝ) (x : ℝ^3) ↦ f x))
      ((Icc a b) ×ˢ Ω) := hf.comp contDiffOn_snd (fun _ hp ↦ hp.2)
  have hγ : ContDiffOn ℝ ∞ γ (Icc a b) := ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt (n := ⊤)
    hfield (fun t ht ↦ (hode t ht).hasDerivWithinAt) hmem
  have hv : ContDiffOn ℝ ∞ v (Icc a b) := hf.comp hγ hmem
  have hπ : ContDiffOn ℝ ∞ π (Icc a b) := contDiffOn_const.clm_comp
    (S.contDiffOn_propagator_right_Icc (n := ⊤) ((hf.fderiv_of_isOpen hΩ (by simp)).comp hγ hmem) b)
  have hvd (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt v (fderiv ℝ f (γ t) (v t)) t :=
    ((hf.differentiableOn (by simp) (γ t) (hmem ht)).differentiableAt
      (hΩ.mem_nhds (hmem ht))).hasFDerivAt.comp_hasDerivAt t (hode t ht)
  have htransport (t : ℝ) (ht : t ∈ Icc a b) : S.propagator b t (v t) = v b := by
    have hsub : Icc t b ⊆ Icc a b := Icc_subset_Icc ht.1 le_rfl
    have heq : v b = S.solution (fun _ ↦ 0) t (v t) b :=
      S.eq_solution_of_hasDerivWithinAt_of_subset ht.2 hsub (hv.continuousOn.mono hsub)
        continuousOn_const fun r hr ↦ by
          simpa only [add_zero] using (hvd r (hsub ⟨hr.1.le, hr.2.le⟩)).hasDerivWithinAt
    simpa only [FundamentalSolution.solution, map_zero, intervalIntegral.integral_zero, add_zero,
      FundamentalSolution.propagator, mul_apply_eq_comp] using heq.symm
  refine ⟨hγ, hv, hπ, fun t ht ↦ hπ.contDiffAt (Icc_mem_nhds ht.1 ht.2), ?_, fun t ht ↦ ?_⟩
  · dsimp only [π]
    rw [S.propagator_self_of_mem hb]
    exact ContinuousLinearMap.comp_id L
  have hleft : S.propagator t b * S.propagator b t = 1 :=
    (S.propagator_mul_of_mem t t hb).trans (S.propagator_self_of_mem ht)
  have hinverse : Function.LeftInverse (S.propagator t b) (S.propagator b t) := fun x ↦ by
    rw [← mul_apply_eq_comp, hleft]
    rfl
  have hker : LinearMap.ker (π t).toLinearMap = Submodule.span ℝ ({v t} : Set (ℝ^3)) := by
    ext x
    change S.propagator b t x ∈ LinearMap.ker L.toLinearMap ↔
      x ∈ Submodule.span ℝ ({v t} : Set (ℝ^3))
    simp only [hL, Submodule.mem_span_singleton]
    exact exists_congr fun c ↦ by
      rw [show f (γ b) = v b from rfl, ← htransport t ht, ← map_smul,
        hinverse.injective.eq_iff]
  have hvne : v t ≠ 0 := fun hz ↦ LinearMap.ker_ne_bot_of_finrank_lt
    (f := (π t).toLinearMap) (by simp) (by rw [hker, hz, Submodule.span_zero_singleton])
  have hrank : Module.finrank ℝ (LinearMap.range (π t).toLinearMap) = 2 := by
    have hdim := (π t).toLinearMap.finrank_range_add_finrank_ker
    rw [hker, finrank_span_singleton hvne, finrank_euclideanSpace_fin] at hdim
    omega
  exact ⟨(hode t ht).deriv, hvd t ht, htransport t ht, hker, hvne, hrank,
    (LinearMap.range_eq_top (f := (π t).toLinearMap)).mp
      (Submodule.eq_top_of_finrank_eq (by simpa using hrank))⟩

end PDE.Analysis.Evolution
