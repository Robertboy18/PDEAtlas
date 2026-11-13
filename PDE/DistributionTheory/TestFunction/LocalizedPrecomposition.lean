/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.TestFunction.ProperPrecomposition

/-!
# Localized precomposition of test functions

For a smooth map `f : D → E` that is not proper, `φ ∘ f` need not have compact support, so
`φ ↦ φ ∘ f` does not act on test functions. Multiplying by a fixed test function `χ` on `D`
repairs this: `φ ↦ χ · (φ ∘ f)` sends `𝓓(E)` to `𝓓(D)` with support inside `tsupport χ`. The
motivating example is the addition map `E × E → E`, whose localized pullback is what defines the
convolution of compactly carried distributions.

The localized pullback is continuous for the canonical LF topologies.
A linear map out of an LF space is continuous as soon as its restriction to each Fréchet stage
`𝓓_K` is (Trèves, *Topological Vector Spaces, Distributions and Kernels*, the chapter on
LF-spaces), and on a fixed stage continuity amounts to seminorm estimates. Those follow from the
Leibniz bound for iterated derivatives of a product together with the Faà di Bruno-type bound
`norm_iteratedFDeriv_comp_le` for a composition, with the derivatives of `χ` and `f` bounded
on the compact set `tsupport χ`.

## Main results

* `precompLocalized`: the localized pullback `χ · (φ ∘ f)` as a test function.
* `tsupport_precompLocalized_subset`: its support lies in `tsupport χ`.
* `precompLocalizedCLM`: the same operator as a continuous linear map `𝓓(E) →L[ℝ] 𝓓(D)`.
-/

@[expose] public section

open Function Set TopologicalSpace
open scoped Distributions Topology

noncomputable section

namespace TestFunction

variable {D E : Type*}
variable [NormedAddCommGroup D] [NormedSpace ℝ D]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Pull a test function back along a smooth map and localize it by a fixed cutoff. -/
def precompLocalized
    (f : D → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (χ : 𝓓((⊤ : Opens D), ℝ))
    (φ : 𝓓((⊤ : Opens E), ℝ)) :
    𝓓((⊤ : Opens D), ℝ) where
  toFun := fun x ↦ χ x * φ (f x)
  contDiff' := χ.contDiff.mul (φ.contDiff.comp hf)
  hasCompactSupport' := χ.hasCompactSupport.mul_right
  tsupport_subset' := subset_univ _

/-- Pointwise formula for the localized pullback: `(χ · f^*φ)(x) = χ x * φ (f x)`. -/
@[simp]
theorem precompLocalized_apply
    (f : D → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (χ : 𝓓((⊤ : Opens D), ℝ))
    (φ : 𝓓((⊤ : Opens E), ℝ)) (x : D) :
    precompLocalized f hf χ φ x = χ x * φ (f x) :=
  rfl

/-- Localized precomposition is supported inside the fixed cutoff support. -/
theorem tsupport_precompLocalized_subset
    (f : D → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (χ : 𝓓((⊤ : Opens D), ℝ))
    (φ : 𝓓((⊤ : Opens E), ℝ)) :
    tsupport (precompLocalized f hf χ φ) ⊆ tsupport χ :=
  tsupport_mul_subset_left

/-- Localized precomposition on a fixed compact-support stage, as a continuous linear map into
the functions supported in the support of the cutoff. -/
def precompLocalizedSupportedCLM
    (f : D → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (χ : 𝓓((⊤ : Opens D), ℝ))
    (K : Compacts E) :
    𝓓_{K}(E, ℝ) →L[ℝ]
      ContDiffMapSupportedIn D ℝ (⊤ : ℕ∞) (tsupportCompacts χ) :=
  let Kχ := tsupportCompacts χ
  letI Φ : 𝓓_{K}(E, ℝ) →ₗ[ℝ]
      ContDiffMapSupportedIn D ℝ (⊤ : ℕ∞) Kχ :=
    { toFun := fun φ ↦
        { toFun := fun x ↦ χ x * φ (f x)
          contDiff' := χ.contDiff.mul (φ.contDiff.comp hf)
          zero_on_compl' := fun x hx ↦ by
            have hχ : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
            simp [hχ] }
      map_add' := fun φ ψ ↦ ContDiffMapSupportedIn.ext fun x ↦ by
        change χ x * (φ (f x) + ψ (f x)) =
          χ x * φ (f x) + χ x * ψ (f x)
        ring
      map_smul' := fun c φ ↦ ContDiffMapSupportedIn.ext fun x ↦ by
        change χ x * (c * φ (f x)) = c * (χ x * φ (f x))
        ring }
  { toLinearMap := Φ
    cont := show Continuous Φ by
      refine WithSeminorms.continuous_of_isBounded
        (ContDiffMapSupportedIn.withSeminorms ℝ E ℝ ⊤ K)
        (ContDiffMapSupportedIn.withSeminorms ℝ D ℝ ⊤ Kχ) _
        (.of_real fun k ↦ ?_)
      have hχcont : Continuous fun x ↦
          (Finset.range (k + 1)).sup' Finset.nonempty_range_add_one
            (fun i ↦ ‖iteratedFDeriv ℝ i (fun y ↦ χ y) x‖) :=
        Continuous.finset_sup'_apply Finset.nonempty_range_add_one fun i hi ↦
          (χ.contDiff.continuous_iteratedFDeriv (mod_cast le_top)).norm
      obtain ⟨Cχ₀, hCχ₀⟩ :=
        Kχ.isCompact.exists_bound_of_continuousOn hχcont.continuousOn
      let Cχ : ℝ := max 0 ‖Cχ₀‖
      have hCχ : 0 ≤ Cχ := le_max_left _ _
      have hχC :
          ∀ i, i ≤ k → ∀ x ∈ Kχ,
            ‖iteratedFDeriv ℝ i (fun y ↦ χ y) x‖ ≤ Cχ := by
        intro i hik x hx
        exact
          (Finset.le_sup'
            (fun j ↦ ‖iteratedFDeriv ℝ j (fun y ↦ χ y) x‖)
            (Finset.mem_range_succ_iff.2 hik)).trans
            ((Real.le_norm_self _).trans
              ((hCχ₀ x hx).trans
                ((Real.le_norm_self Cχ₀).trans (le_max_right _ _))))
      have hfcont : Continuous fun x ↦
          (Finset.range (k + 1)).sup' Finset.nonempty_range_add_one
            (fun i ↦ ‖iteratedFDeriv ℝ i f x‖) :=
        Continuous.finset_sup'_apply Finset.nonempty_range_add_one fun i hi ↦
          (hf.continuous_iteratedFDeriv (mod_cast le_top)).norm
      obtain ⟨Cf₀, hCf₀⟩ :=
        Kχ.isCompact.exists_bound_of_continuousOn hfcont.continuousOn
      let Cf : ℝ := max 1 ‖Cf₀‖
      have hCf : 1 ≤ Cf := le_max_left _ _
      have hfC :
          ∀ i, 1 ≤ i → i ≤ k → ∀ x ∈ Kχ,
            ‖iteratedFDeriv ℝ i f x‖ ≤ Cf ^ i := by
        intro i hi hik x hx
        have hderiv : ‖iteratedFDeriv ℝ i f x‖ ≤ ‖Cf₀‖ := by
          exact
            (Finset.le_sup'
              (fun j ↦ ‖iteratedFDeriv ℝ j f x‖)
              (Finset.mem_range_succ_iff.2 hik)).trans
              ((Real.le_norm_self _).trans
                ((hCf₀ x hx).trans (Real.le_norm_self Cf₀)))
        exact hderiv.trans <|
          (le_max_right (1 : ℝ) ‖Cf₀‖).trans
            (le_self_pow₀ hCf (Nat.one_le_iff_ne_zero.mp hi))
      let A : ℝ :=
        ∑ i ∈ Finset.range (k + 1),
          (k.choose i : ℝ) * Cχ * ((k - i).factorial * Cf ^ (k - i))
      have hA : 0 ≤ A := by
        dsimp [A]
        positivity
      refine ⟨Finset.Iic k, A, fun φ ↦ ?_⟩
      refine
        ((Φ φ).seminorm_top_le_iff ℝ
          (mul_nonneg hA (apply_nonneg _ _)) k).2 ?_
      intro x hx
      change ‖iteratedFDeriv ℝ k
        (fun y ↦ χ y * φ (f y)) x‖ ≤
          A * ((Finset.Iic k).sup
            (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K)) φ
      refine (norm_iteratedFDeriv_mul_le χ.contDiff
        (φ.contDiff.comp hf) x (mod_cast le_top)).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum ?_
      intro i hi
      simp only [Finset.mem_range] at hi
      have hik : i ≤ k := Nat.le_of_lt_succ hi
      let P : ℝ :=
        ((Finset.Iic k).sup
          (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K)) φ
      have hP : 0 ≤ P := apply_nonneg _ _
      have hcomp :
          ‖iteratedFDeriv ℝ (k - i) (⇑φ ∘ f) x‖ ≤
            (k - i).factorial * P * Cf ^ (k - i) := by
        exact norm_iteratedFDeriv_comp_le φ.contDiff hf
          (by
            change (((k - i : ℕ) : ℕ∞) : WithTop ℕ∞) ≤
              ((⊤ : ℕ∞) : WithTop ℕ∞)
            exact WithTop.coe_le_coe.mpr le_top) x
          (fun j hj ↦
            (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ).trans
              (Seminorm.le_finset_sup_apply
                (Finset.mem_Iic.2 (hj.trans (Nat.sub_le k i)))))
          (fun j hj hjki ↦
            hfC j hj (hjki.trans (Nat.sub_le k i)) x hx)
      have hterm :
          (k.choose i : ℝ) *
              ‖iteratedFDeriv ℝ i (fun y ↦ χ y) x‖ *
              ‖iteratedFDeriv ℝ (k - i) (⇑φ ∘ f) x‖ ≤
            ((k.choose i : ℝ) * Cχ *
                ((k - i).factorial * Cf ^ (k - i))) * P := by
        calc
          _ ≤ (k.choose i : ℝ) * Cχ *
              ((k - i).factorial * P * Cf ^ (k - i)) := by
                gcongr
                exact hχC i hik x hx
          _ = ((k.choose i : ℝ) * Cχ *
                ((k - i).factorial * Cf ^ (k - i))) * P := by
                ring
      simpa [P] using hterm }

/-- Localized pullback along a smooth map as a continuous linear map of LF test-function spaces. -/
def precompLocalizedCLM
    (f : D → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (χ : 𝓓((⊤ : Opens D), ℝ)) :
    𝓓((⊤ : Opens E), ℝ) →L[ℝ] 𝓓((⊤ : Opens D), ℝ) :=
  TestFunction.limitCLM ℝ
    (precompLocalized f hf χ)
    (fun K _Ksub ↦
      TestFunction.ofSupportedInCLM ℝ (subset_univ _) ∘L
        precompLocalizedSupportedCLM f hf χ K)
    (by
      intro K _Ksub φ
      ext x
      rfl)

/-- The continuous linear operator agrees with the plain localized pullback `precompLocalized`;
only the continuity proof for the LF topology is added. -/
@[simp]
theorem precompLocalizedCLM_apply
    (f : D → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (χ : 𝓓((⊤ : Opens D), ℝ))
    (φ : 𝓓((⊤ : Opens E), ℝ)) :
    precompLocalizedCLM f hf χ φ = precompLocalized f hf χ φ := by
  ext x
  rfl

end TestFunction
