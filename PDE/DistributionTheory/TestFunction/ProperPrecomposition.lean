/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.TestFunction

/-!
# Proper precomposition of test functions

A smooth proper map `f : D → E` pulls compactly supported smooth functions on `E` back to
compactly supported smooth functions on `D`, and this pullback is continuous for
the canonical LF topologies on test-function spaces.

The continuity proof first bounds precomposition on every fixed compact-support stage using
Mathlib's seminorm description of `ContDiffMapSupportedIn`. It then applies the LF universal
property `TestFunction.limitCLM`.
-/

@[expose] public section

open Function Set TopologicalSpace
open scoped Distributions Topology

noncomputable section

namespace TestFunction

variable {D E : Type*}
variable [NormedAddCommGroup D] [NormedSpace ℝ D]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The preimage of a compact set under a proper map, bundled as a compact set. -/
def properPreimageCompact
    (f : D → E) (hproper : IsProperMap f) (K : Compacts E) : Compacts D :=
  ⟨f ⁻¹' (K : Set E), hproper.isCompact_preimage K.isCompact⟩

/-- The topological support of a test function, bundled as a compact set. -/
def tsupportCompacts {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens E}
    {n : ℕ∞} (φ : 𝓓^{n}(Ω, F)) : Compacts E :=
  ⟨tsupport φ, φ.hasCompactSupport⟩

/-- Pull a test function back along a smooth proper map. -/
def precompProper
    (f : D → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hproper : IsProperMap f)
    (φ : 𝓓((⊤ : Opens E), ℝ)) : 𝓓((⊤ : Opens D), ℝ) where
  toFun := fun x ↦ φ (f x)
  contDiff' := φ.contDiff.comp hf
  hasCompactSupport' := by
    apply HasCompactSupport.of_support_subset_isCompact
      (hproper.isCompact_preimage φ.hasCompactSupport)
    intro x hx
    exact subset_tsupport φ hx
  tsupport_subset' := subset_univ _

/-- The pullback is composition: `(f^* φ)(x) = φ (f x)`. -/
@[simp]
theorem precompProper_apply
    (f : D → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hproper : IsProperMap f)
    (φ : 𝓓((⊤ : Opens E), ℝ)) (x : D) :
    precompProper f hf hproper φ x = φ (f x) :=
  rfl

/-- Pullback along a smooth proper map on a fixed compact-support stage, as a continuous linear
map into the functions supported in the preimage of that stage. -/
def precompProperSupportedCLM
    (f : D → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hproper : IsProperMap f)
    (K : Compacts E) :
    𝓓_{K}(E, ℝ) →L[ℝ]
      ContDiffMapSupportedIn D ℝ (⊤ : ℕ∞) (properPreimageCompact f hproper K) :=
  let Kpre := properPreimageCompact f hproper K
  letI Φ : 𝓓_{K}(E, ℝ) →ₗ[ℝ] ContDiffMapSupportedIn D ℝ (⊤ : ℕ∞) Kpre :=
    { toFun := fun φ ↦
        { toFun := fun x ↦ φ (f x)
          contDiff' := φ.contDiff.comp hf
          zero_on_compl' := fun x hx ↦ φ.zero_on_compl hx }
      map_add' := fun φ ψ ↦ ContDiffMapSupportedIn.ext fun _ ↦ rfl
      map_smul' := fun c φ ↦ ContDiffMapSupportedIn.ext fun _ ↦ rfl }
  { toLinearMap := Φ
    cont := show Continuous Φ by
      refine WithSeminorms.continuous_of_isBounded
        (ContDiffMapSupportedIn.withSeminorms ℝ E ℝ ⊤ K)
        (ContDiffMapSupportedIn.withSeminorms ℝ D ℝ ⊤ Kpre) _
        (.of_real fun k ↦ ?_)
      let Kpre := properPreimageCompact f hproper K
      have hcont : Continuous fun x ↦
          (Finset.range (k + 1)).sup' Finset.nonempty_range_add_one
            (fun i ↦ ‖iteratedFDeriv ℝ i f x‖) :=
        Continuous.finset_sup'_apply Finset.nonempty_range_add_one fun i hi ↦
          (hf.continuous_iteratedFDeriv (mod_cast le_top)).norm
      obtain ⟨C₀, hC₀⟩ :=
        Kpre.isCompact.exists_bound_of_continuousOn hcont.continuousOn
      let C : ℝ := max 1 ‖C₀‖
      have hC : 1 ≤ C := le_max_left _ _
      have hfC :
          ∀ i, 1 ≤ i → i ≤ k → ∀ x ∈ Kpre,
            ‖iteratedFDeriv ℝ i f x‖ ≤ C ^ i := by
        intro i hi _hik x hx
        have hderiv : ‖iteratedFDeriv ℝ i f x‖ ≤ ‖C₀‖ := by
          exact
            (Finset.le_sup'
              (fun j ↦ ‖iteratedFDeriv ℝ j f x‖)
              (Finset.mem_range_succ_iff.2 _hik)).trans
              ((Real.le_norm_self _).trans
                ((hC₀ x hx).trans (Real.le_norm_self C₀)))
        exact hderiv.trans <|
          (le_max_right (1 : ℝ) ‖C₀‖).trans
            (le_self_pow₀ hC (Nat.one_le_iff_ne_zero.mp hi))
      refine ⟨Finset.Iic k, k.factorial * C ^ k, fun φ ↦ ?_⟩
      refine
        ((Φ φ).seminorm_top_le_iff ℝ
          (mul_nonneg (by positivity) (apply_nonneg _ _)) k).2 ?_
      intro x hx
      change ‖iteratedFDeriv ℝ k (⇑φ ∘ f) x‖ ≤
        k.factorial * C ^ k *
          ((Finset.Iic k).sup
            (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K)) φ
      have hcomp := norm_iteratedFDeriv_comp_le (n := k) φ.contDiff hf
        (mod_cast le_top) x
        (C := ((Finset.Iic k).sup
          (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K)) φ)
        (D := C)
        (fun i hi ↦
          (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ).trans
            (Seminorm.le_finset_sup_apply (Finset.mem_Iic.2 hi)))
        (fun i hi hik ↦ hfC i hi hik x hx)
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hcomp }

/-- Pullback along a smooth proper map as a continuous linear map of LF test-function spaces. -/
def precompProperCLM
    (f : D → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hproper : IsProperMap f) :
    𝓓((⊤ : Opens E), ℝ) →L[ℝ] 𝓓((⊤ : Opens D), ℝ) :=
  TestFunction.limitCLM ℝ
    (precompProper f hf hproper)
    (fun K _Ksub ↦
      TestFunction.ofSupportedInCLM ℝ (subset_univ _) ∘L
        precompProperSupportedCLM f hf hproper K)
    (by
      intro K _Ksub φ
      ext x
      rfl)

/-- The continuous linear pullback agrees with the plain pullback `precompProper`; the two
differ only in that the former carries the continuity proof for the LF topology. -/
@[simp]
theorem precompProperCLM_apply
    (f : D → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hproper : IsProperMap f)
    (φ : 𝓓((⊤ : Opens E), ℝ)) :
    precompProperCLM f hf hproper φ = precompProper f hf hproper φ := by
  ext x
  rfl

end TestFunction
