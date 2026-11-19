/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.TemperedDistribution.LocalSobolev.FirstOrder
public import PDE.DistributionTheory.TemperedDistribution.LocalSobolev.Representatives
import PDE.DistributionTheory.TemperedDistribution.LocalSobolev

/-!
# Interior first derivatives for divergence-form Poisson data

An L² state whose distributional Laplacian is a divergence of L² fields has an
H¹ representative near every compact subset of the testing domain. The weak
identity differentiates the test function and includes its distributional minus
sign. No first derivative of the state is assumed.

The directions may be any finite family. This form covers right-hand
sides that are differences of two force derivatives, as well as an ordinary
divergence.
-/

@[expose] public noncomputable section

open MeasureTheory Set TopologicalSpace TemperedDistribution
open scoped ENNReal SchwartzMap LineDeriv Laplacian Topology

namespace PDE.Elliptic.Interior

variable {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] [Fintype ι]

/-- Testing the divergence equation on compact Schwartz functions
supplies first-order Sobolev regularity after every compact localization. -/
theorem memSobolev_one_cutoff_of_distributional_divergence
    {Ω : Set E} (T : 𝓢'(E, F)) (G : ι → 𝓢'(E, F)) (v : ι → E)
    (hT : ∀ a : 𝓢(E, ℂ), HasCompactSupport a → tsupport a ⊆ Ω →
      MemSobolev 0 2 (smulLeftCLM F a T))
    (hG : ∀ i, ∀ a : 𝓢(E, ℂ), HasCompactSupport a → tsupport a ⊆ Ω →
      MemSobolev 0 2 (smulLeftCLM F a (G i)))
    (hweak : ∀ φ : 𝓢(E, ℂ), HasCompactSupport φ → tsupport φ ⊆ Ω →
      T (Δ φ) = ∑ i, (∂_{v i} (G i) : 𝓢'(E, F)) φ)
    (a : 𝓢(E, ℂ)) (ha : HasCompactSupport a) (haΩ : tsupport a ⊆ Ω) :
    MemSobolev 1 2 (smulLeftCLM F a T) := by
  apply memSobolev_one_smulLeftCLM_of_local_divergence G v hT hG _ a ha haΩ
  intro χ hχ hχΩ
  ext φ
  have hsub : tsupport (SchwartzMap.smulLeftCLM ℂ χ φ) ⊆ tsupport χ := by
    apply closure_minimal ?_ (isClosed_tsupport (χ : E → ℂ))
    intro x hx
    apply subset_tsupport χ
    intro hx0
    apply hx
    rw [SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth, hx0, zero_smul]
  have hcs : HasCompactSupport (SchwartzMap.smulLeftCLM ℂ χ φ) :=
    hχ.of_isClosed_subset
      (isClosed_tsupport (SchwartzMap.smulLeftCLM ℂ χ φ : E → ℂ)) hsub
  simpa only [TemperedDistribution.smulLeftCLM_apply_apply,
    TemperedDistribution.laplacian_apply_apply, sum_apply] using
    hweak _ hcs (hsub.trans hχΩ)

/-- Global L² data need satisfy the divergence equation only on an open set.
The resulting H¹ representative agrees with the state near the given compact set. -/
theorem exists_memSobolev_one_ae_eq_near_compact_of_lp_divergence_eq
    {Ω : Set E} (hΩ : IsOpen Ω) (u : Lp F 2 (volume : Measure E))
    (f : ι → Lp F 2 (volume : Measure E)) (v : ι → E)
    (hweak : ∀ φ : 𝓢(E, ℂ), HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ x, (Δ φ) x • u x) = -∑ i, ∫ x, (∂_{v i} φ : 𝓢(E, ℂ)) x • f i x)
    (K : Set E) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧ V ⊆ Ω ∧
      ∃ U : Lp F 2 (volume : Measure E),
        MemSobolev 1 2 (U : 𝓢'(E, F)) ∧ (U : E → F) =ᵐ[volume.restrict V] u := by
  obtain ⟨χ, hχcs, hχΩ, hχflat⟩ :=
    SchwartzMap.exists_eq_one_near_compact hΩ hK hKΩ
  have hlocal (g : Lp F 2 (volume : Measure E)) (a : 𝓢(E, ℂ)) :
      MemSobolev 0 2 (smulLeftCLM F a (g : 𝓢'(E, F))) :=
    ((memSobolev_zero_iff (E := E) (F := F) (p := 2)).mpr ⟨g, rfl⟩).zero_smulLeftCLM a
  have hone : MemSobolev 1 2 (smulLeftCLM F χ (u : 𝓢'(E, F))) := by
    apply memSobolev_one_cutoff_of_distributional_divergence
      (u : 𝓢'(E, F)) (fun i ↦ (f i : 𝓢'(E, F))) v
      (fun a _ _ ↦ hlocal u a) (fun i a _ _ ↦ hlocal (f i) a) _ χ hχcs hχΩ
    intro φ hφ hφΩ
    simpa only [TemperedDistribution.lineDerivOp_apply_apply,
      Lp.toTemperedDistribution_apply, neg_apply, neg_smul, integral_neg,
      ← Finset.sum_neg_distrib] using hweak φ hφ hφΩ
  let V : Set E := Ω ∩ interior {x | χ x = 1}
  have hV : IsOpen V := hΩ.inter isOpen_interior
  have hKV : K ⊆ V := by
    intro x hx
    exact ⟨hKΩ hx, mem_interior_iff_mem_nhds.mpr (hχflat x hx)⟩
  obtain ⟨U, hU, hUeq⟩ := exists_memSobolev_ae_eq_of_cutoff χ u hV.measurableSet
    (fun _ hx ↦
      (interior_subset : interior {x : E | χ x = 1} ⊆ {x : E | χ x = 1}) hx.2) hone
  exact ⟨V, hV, hKV, inter_subset_left, U, hU, hUeq⟩

end PDE.Elliptic.Interior
