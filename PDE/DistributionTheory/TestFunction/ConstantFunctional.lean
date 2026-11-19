/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.TestFunction.PartialIntegral
public import PDE.DistributionTheory.TestFunction.IntegrationByParts
import PDE.Common.Euclidean.SpaceTime
import PDE.DistributionTheory.TestFunction.Integral
import PDE.DistributionTheory.TestFunction.LinearChange
import PDE.DistributionTheory.TestFunction.Derivative.Commutation

/-!
# Algebraic functionals with vanishing derivatives

On an open rectangular box, the space of linear functionals on compact tests
which annihilate all directional derivatives has dimension at most one.
Continuity of the functional is not assumed. The proof eliminates one
coordinate at a time by a compactly supported primitive.
-/

@[expose] public noncomputable section

open MeasureTheory Set TopologicalSpace PDE.Common
open scoped Distributions

namespace TestFunction

/-- Directional differentiation is the coordinate expansion in the direction vector. -/
theorem lineDerivCLM_eq_sum_coordinate {n : ℕ} (v : ℝ^n)
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    lineDerivCLM (k := ⊤) ℝ v φ =
      ∑ i : Fin n, v i • lineDerivCLM ℝ (EuclideanSpace.single i (1 : ℝ)) φ := by
  classical
  have hv : v = ∑ i : Fin n, v i • EuclideanSpace.single i (1 : ℝ) := by
    ext j
    simp [Pi.single_apply]
  ext x
  simp only [lineDerivCLM_apply_eq_fderiv, sum_apply, smul_apply, smul_eq_mul]
  conv_lhs => rw [hv]
  simp

private theorem apply_eq_tensor_integralFst
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} {U : Set E}
    (q : 𝓓((⊤ : Opens (ℝ × E)), ℝ) →ₗ[ℝ] ℝ)
    (hq : ∀ ψ : 𝓓((⊤ : Opens (ℝ × E)), ℝ), tsupport ψ ⊆ Ioo a b ×ˢ U →
      q (lineDerivCLM ℝ (1, 0) ψ) = 0)
    (ρ : 𝓓((⊤ : Opens ℝ), ℝ)) (hρ : tsupport ρ ⊆ Ioo a b)
    (hρint : ∫ t, ρ t = 1)
    (φ : 𝓓((⊤ : Opens (ℝ × E)), ℝ)) (hφ : tsupport φ ⊆ Ioo a b ×ˢ U) :
    q φ = q (tensorProduct ρ (integralFst φ)) := by
  obtain ⟨ψ, hψ, hd⟩ :=
    exists_lineDeriv_eq_sub_tensor_integralFst ρ hρ hρint φ hφ
  have h := hq ψ hψ
  rw [hd, map_sub, sub_eq_zero] at h
  exact h

/-- On a rectangular box, two algebraic functionals annihilating derivatives
are proportional, provided the second functional is nonzero there. That nonzero value comes
from a nonzero test function supported in the box, so the box is not empty. -/
theorem exists_eq_mul_of_lineDeriv_eq_zero_on_box
    (n : ℕ) (a b : Fin n → ℝ)
    (q r : 𝓓((⊤ : Opens (ℝ^n)), ℝ) →ₗ[ℝ] ℝ)
    (hq : ∀ v : ℝ^n, ∀ φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ),
      tsupport φ ⊆ {x | ∀ i, x i ∈ Ioo (a i) (b i)} →
      q (lineDerivCLM ℝ v φ) = 0)
    (hr : ∀ v : ℝ^n, ∀ φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ),
      tsupport φ ⊆ {x | ∀ i, x i ∈ Ioo (a i) (b i)} →
      r (lineDerivCLM ℝ v φ) = 0)
    (hne : ∃ φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ),
      tsupport φ ⊆ {x | ∀ i, x i ∈ Ioo (a i) (b i)} ∧ r φ ≠ 0) :
    ∃ c : ℝ, ∀ φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ),
      tsupport φ ⊆ {x | ∀ i, x i ∈ Ioo (a i) (b i)} → q φ = c * r φ := by
  induction n with
  | zero =>
    obtain ⟨ψ, _, hψ⟩ := hne
    have hψ0 : ψ 0 ≠ 0 := by
      intro hz
      apply hψ
      have heq : ψ = 0 := by
        ext x
        rw [Subsingleton.elim x 0]
        exact hz
      rw [heq, map_zero]
    have heq (φ : 𝓓((⊤ : Opens (ℝ^0)), ℝ)) :
        φ = (φ 0 / ψ 0) • ψ := by
      ext x
      rw [Subsingleton.elim x 0]
      change φ 0 = (φ 0 / ψ 0) * ψ 0
      rw [div_mul_cancel₀ _ hψ0]
    refine ⟨q ψ / r ψ, fun φ _ ↦ ?_⟩
    conv_lhs => rw [heq φ, map_smul]
    conv_rhs => rw [heq φ, map_smul]
    simp only [smul_eq_mul]
    field_simp
  | succ n ih =>
    have hab : ∀ i, a i < b i := by
      obtain ⟨φ, hφ, hrφ⟩ := hne
      obtain ⟨x, hx⟩ : ∃ x, φ x ≠ 0 := by
        by_contra h
        simp only [not_exists, not_not] at h
        exact hrφ (by rw [show φ = 0 by ext x; simpa using h x, map_zero])
      intro i
      have hxi := hφ (subset_tsupport _ hx) i
      exact hxi.1.trans hxi.2
    let e := timeSpaceContinuousLinearEquiv n
    let A := precompLinearEquiv e
    let U : Set (ℝ^n) := {x | ∀ i, x i ∈ Ioo (a i.succ) (b i.succ)}
    let B : Set (ℝ^(n + 1)) := {x | ∀ i, x i ∈ Ioo (a i) (b i)}
    have hB : B = e ⁻¹' (Ioo (a 0) (b 0) ×ˢ U) := by
      ext x
      constructor
      · intro hx
        exact ⟨hx 0, fun i ↦ hx i.succ⟩
      · rintro ⟨h0, hs⟩ i
        exact Fin.cases h0 hs i
    have hsupp (φ : 𝓓((⊤ : Opens (ℝ × ℝ^n)), ℝ))
        (hφ : tsupport φ ⊆ Ioo (a 0) (b 0) ×ˢ U) :
        tsupport (A φ) ⊆ B := by
      rw [hB]
      exact (tsupport_precompLinearEquiv_subset e φ).trans
        (preimage_mono hφ)
    have hback (φ : 𝓓((⊤ : Opens (ℝ^(n + 1))), ℝ))
        (hφ : tsupport φ ⊆ B) :
        tsupport (precompLinearEquiv e.symm φ) ⊆ Ioo (a 0) (b 0) ×ˢ U := by
      intro x hx
      have hm := hφ (tsupport_precompLinearEquiv_subset e.symm φ hx)
      rw [hB] at hm
      simpa using hm
    let Q := q.comp A.toLinearMap
    let R := r.comp A.toLinearMap
    have hQ (v : ℝ × ℝ^n) (φ : 𝓓((⊤ : Opens (ℝ × ℝ^n)), ℝ))
        (hφ : tsupport φ ⊆ Ioo (a 0) (b 0) ×ˢ U) :
        Q (lineDerivCLM ℝ v φ) = 0 := by
      change q (A (lineDerivCLM ℝ v φ)) = 0
      rw [show A (lineDerivCLM ℝ v φ) =
        lineDerivCLM ℝ (e.symm v) (A φ) by
          simpa [A] using (lineDerivCLM_precompLinearEquiv e (e.symm v) φ).symm]
      exact hq _ _ (hsupp φ hφ)
    have hR (v : ℝ × ℝ^n) (φ : 𝓓((⊤ : Opens (ℝ × ℝ^n)), ℝ))
        (hφ : tsupport φ ⊆ Ioo (a 0) (b 0) ×ˢ U) :
        R (lineDerivCLM ℝ v φ) = 0 := by
      change r (A (lineDerivCLM ℝ v φ)) = 0
      rw [show A (lineDerivCLM ℝ v φ) =
        lineDerivCLM ℝ (e.symm v) (A φ) by
          simpa [A] using (lineDerivCLM_precompLinearEquiv e (e.symm v) φ).symm]
      exact hr _ _ (hsupp φ hφ)
    obtain ⟨ρ, hρ, hρint, _⟩ :=
      exists_integral_eq_one (volume : Measure ℝ) isOpen_Ioo
        (nonempty_Ioo.mpr (hab 0))
    let Q' := Q.comp (tensorProductLeftCLM ρ).toLinearMap
    let R' := R.comp (tensorProductLeftCLM ρ).toLinearMap
    have hQ'app (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
        Q' φ = Q (tensorProduct ρ φ) := by
      simp [Q']
    have hR'app (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
        R' φ = R (tensorProduct ρ φ) := by
      simp [R']
    have htensor (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hφ : tsupport φ ⊆ U) :
        tsupport (tensorProduct ρ φ) ⊆ Ioo (a 0) (b 0) ×ˢ U :=
      (tsupport_tensorProduct_subset ρ φ).trans (prod_mono hρ hφ)
    have hQ' (v : ℝ^n) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
        (hφ : tsupport φ ⊆ U) : Q' (lineDerivCLM ℝ v φ) = 0 := by
      rw [hQ'app, ← lineDerivCLM_tensorProduct_snd]
      exact hQ _ _ (htensor φ hφ)
    have hR' (v : ℝ^n) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
        (hφ : tsupport φ ⊆ U) : R' (lineDerivCLM ℝ v φ) = 0 := by
      rw [hR'app, ← lineDerivCLM_tensorProduct_snd]
      exact hR _ _ (htensor φ hφ)
    have hint (φ : 𝓓((⊤ : Opens (ℝ × ℝ^n)), ℝ))
        (hφ : tsupport φ ⊆ Ioo (a 0) (b 0) ×ˢ U) :
        tsupport (integralFst φ) ⊆ U := by
      rintro x hx
      obtain ⟨p, hp, rfl⟩ := tsupport_integralFst_subset φ hx
      exact (hφ hp).2
    have hne' : ∃ φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ),
        tsupport φ ⊆ U ∧ R' φ ≠ 0 := by
      obtain ⟨φ, hφ, hne⟩ := hne
      let ψ := precompLinearEquiv e.symm φ
      have hψ := hback φ hφ
      refine ⟨integralFst ψ, hint ψ hψ, ?_⟩
      have heq := apply_eq_tensor_integralFst R (hR (1, 0)) ρ hρ hρint ψ hψ
      have hround : A ψ = φ := by ext x; simp [A, ψ]
      rw [hR'app, ← heq]
      change r (A ψ) ≠ 0
      rwa [hround]
    obtain ⟨c, hc⟩ := ih (fun i ↦ a i.succ) (fun i ↦ b i.succ)
      Q' R' hQ' hR' hne'
    refine ⟨c, fun φ hφ ↦ ?_⟩
    let ψ := precompLinearEquiv e.symm φ
    have hψ := hback φ hφ
    have hround : A ψ = φ := by ext x; simp [A, ψ]
    have hqeq := apply_eq_tensor_integralFst Q (hQ (1, 0)) ρ hρ hρint ψ hψ
    have hreq := apply_eq_tensor_integralFst R (hR (1, 0)) ρ hρ hρint ψ hψ
    rw [← hQ'app] at hqeq
    rw [← hR'app] at hreq
    have hmain := hc (integralFst ψ) (hint ψ hψ)
    rw [← hqeq, ← hreq] at hmain
    change q (A ψ) = c * r (A ψ) at hmain
    rwa [hround] at hmain

/-- An algebraic functional which annihilates coordinate derivatives on an open
box is integration against a constant there. No continuity assumption is needed. -/
theorem exists_eq_mul_integral_of_partialDeriv_eq_zero_on_box
    {n : ℕ} (a b : Fin n → ℝ) (hab : ∀ i, a i < b i)
    (q : 𝓓((⊤ : Opens (ℝ^n)), ℝ) →ₗ[ℝ] ℝ)
    (hq : ∀ i : Fin n, ∀ φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ),
      tsupport φ ⊆ {x | ∀ j, x j ∈ Ioo (a j) (b j)} →
      q (lineDerivCLM ℝ (EuclideanSpace.single i (1 : ℝ)) φ) = 0) :
    ∃ c : ℝ, ∀ φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ),
      tsupport φ ⊆ {x | ∀ i, x i ∈ Ioo (a i) (b i)} →
      q φ = c * ∫ x, φ x := by
  have hdir (v : ℝ^n) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
      (hφ : tsupport φ ⊆ {x | ∀ j, x j ∈ Ioo (a j) (b j)}) :
      q (lineDerivCLM ℝ v φ) = 0 := by
    rw [lineDerivCLM_eq_sum_coordinate, map_sum]
    simp [map_smul, hq _ φ hφ]
  have hint (v : ℝ^n) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
      integralLinearMap volume (lineDerivCLM ℝ v φ) = 0 := by
    rw [lineDerivCLM_eq_sum_coordinate, map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [map_smul]
    have hz : integralLinearMap volume
        (lineDerivCLM ℝ (EuclideanSpace.single i (1 : ℝ)) φ) = 0 := by
      change (∫ x, fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) = 0
      exact PDE.DistributionTheory.integral_partialDeriv_eq_zero_of_hasCompactSupport
        i (φ.contDiff.of_le (by simp)) φ.hasCompactSupport
    rw [hz, smul_zero]
  have hopen : IsOpen {x : ℝ^n | ∀ i, x i ∈ Ioo (a i) (b i)} := by
    simpa only [ofPred_forall, EuclideanSpace.coe_proj, Set.preimage, Set.mem_Ioo] using
      isOpen_iInter_of_finite (fun i : Fin n ↦
        isOpen_Ioo.preimage (EuclideanSpace.proj i).continuous)
  obtain ⟨φ, hφ, hφint, _⟩ := exists_integral_eq_one (volume : Measure (ℝ^n)) hopen
    ⟨WithLp.toLp 2 (fun i ↦ (a i + b i) / 2),
      fun i ↦ ⟨by dsimp; linarith [hab i], by dsimp; linarith [hab i]⟩⟩
  exact exists_eq_mul_of_lineDeriv_eq_zero_on_box n a b q (integralLinearMap volume)
    hdir (fun v ψ _ ↦ hint v ψ) ⟨φ, hφ, by simp [hφint]⟩

end TestFunction
