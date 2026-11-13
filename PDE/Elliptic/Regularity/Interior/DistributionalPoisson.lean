/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.TemperedDistribution.LocalSobolev
import PDE.DistributionTheory.TemperedDistribution.LocalSobolev.Representatives

/-!
# Local H² regularity for distributional Poisson solutions

Let `u` and `f` be locally L² on an open set, and suppose `Δu = f` against every
smooth compactly supported test function. Near each compact subset of that open
set, `u` agrees almost everywhere with a global H² function. First derivatives
are derived by an H⁻¹ cutoff argument, rather than required of the solution.

The data may take values in a complete complex Hilbert space. Local L² means L²
on every compact subset, with Lebesgue measure. Compactly supported Schwartz
functions are used as the smooth tests; their Laplacian is the bundled classical
Laplacian. The representative belongs to Mathlib's Bessel space H². No continuity
of `u`, boundary condition, boundary atlas, or global growth bound is imposed.
-/

@[expose] public noncomputable section

open MeasureTheory Set TopologicalSpace TemperedDistribution
open scoped ENNReal SchwartzMap LineDeriv Laplacian Topology

namespace PDE.Elliptic.Interior

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- A locally L² distribution solving `ΔT = G` on an open set is H² after every
compact cutoff there, provided `G` is locally L². The equation is tested only on
compact supports in that open set. -/
theorem memSobolev_two_cutoff_of_distributional_poisson
    {Ω : Set E} (hΩ : IsOpen Ω) (T G : 𝓢'(E, F))
    (hT : ∀ a : 𝓢(E, ℂ), HasCompactSupport a → tsupport a ⊆ Ω →
      MemSobolev 0 2 (smulLeftCLM F a T))
    (hG : ∀ a : 𝓢(E, ℂ), HasCompactSupport a → tsupport a ⊆ Ω →
      MemSobolev 0 2 (smulLeftCLM F a G))
    (hweak : ∀ φ : 𝓢(E, ℂ), HasCompactSupport φ → tsupport φ ⊆ Ω → T (Δ φ) = G φ)
    (a : 𝓢(E, ℂ)) (ha : HasCompactSupport a) (haΩ : tsupport a ⊆ Ω) :
    MemSobolev 2 2 (smulLeftCLM F a T) := by
  apply memSobolev_two_smulLeftCLM_of_local_laplacian hΩ hT _ a ha haΩ
  intro χ hχ hχΩ
  have heq : smulLeftCLM F χ (Δ T) = smulLeftCLM F χ G := by
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
    change (Δ T) (SchwartzMap.smulLeftCLM ℂ χ φ) = G (SchwartzMap.smulLeftCLM ℂ χ φ)
    rw [TemperedDistribution.laplacian_apply_apply]
    exact hweak _ hcs (hsub.trans hχΩ)
  rw [heq]
  exact hG χ hχ hχΩ

/-- Localizing both data preserves the Poisson pairing against a test supported
where the cutoff is one, since the test Laplacian has the same support bound. -/
private theorem cutoff_laplacian_pairing (η : 𝓢(E, ℂ)) (u f : E → F)
    (huη : MemLp (fun x ↦ η x • u x) 2 volume)
    (hfη : MemLp (fun x ↦ η x • f x) 2 volume)
    (φ : 𝓢(E, ℂ)) (hηflat : ∀ x ∈ tsupport φ, η x = 1)
    (hweak : (∫ x, (Δ φ) x • u x) = ∫ x, φ x • f x) :
    ((huη.toLp (fun x ↦ η x • u x) : Lp F 2 volume) : 𝓢'(E, F)) (Δ φ) =
      ((hfη.toLp (fun x ↦ η x • f x) : Lp F 2 volume) : 𝓢'(E, F)) φ := by
  calc
    _ = ∫ x, (Δ φ) x • u x :=
      cutoff_pairing η u huη (Δ φ)
        (fun x hx ↦ hηflat x (SchwartzMap.tsupport_laplacian_subset φ hx))
    _ = ∫ x, φ x • f x := hweak
    _ = _ := (cutoff_pairing η f hfη φ hηflat).symm

/-- Global L² data need satisfy the Poisson equation only on the open set to
give H² after a compact cutoff there. Their order-zero membership supplies both
local hypotheses of the distributional cutoff theorem. -/
private theorem memSobolev_two_cutoff_of_lp_laplacian_eq
    {Ω : Set E} (hΩ : IsOpen Ω) (u f : Lp F 2 (volume : Measure E))
    (hweak : ∀ φ : 𝓢(E, ℂ), HasCompactSupport φ → tsupport φ ⊆ Ω →
      (u : 𝓢'(E, F)) (Δ φ) = (f : 𝓢'(E, F)) φ)
    (χ : 𝓢(E, ℂ)) (hχcs : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω) :
    MemSobolev 2 2 (smulLeftCLM F χ (u : 𝓢'(E, F))) := by
  have hzero (g : Lp F 2 (volume : Measure E)) :
      MemSobolev 0 2 (g : 𝓢'(E, F)) :=
    (memSobolev_zero_iff (E := E) (F := F) (p := 2)
      (f := (g : 𝓢'(E, F)))).mpr ⟨g, rfl⟩
  have hlocal (g : Lp F 2 (volume : Measure E)) (a : 𝓢(E, ℂ)) :
      MemSobolev 0 2 (smulLeftCLM F a (g : 𝓢'(E, F))) :=
    TemperedDistribution.MemSobolev.zero_smulLeftCLM
      (E := E) (F := F) (p := 2) (T := (g : 𝓢'(E, F))) (hzero g) a
  exact memSobolev_two_cutoff_of_distributional_poisson
    (E := E) (F := F) (Ω := Ω) hΩ (u : 𝓢'(E, F)) (f : 𝓢'(E, F))
    (fun a _ _ ↦ hlocal u a) (fun a _ _ ↦ hlocal f a) hweak χ hχcs hχΩ

/-- Global L² data satisfying the Poisson equation only on an open set yield an
H² representative near each compact subset. Multiplication supplies local
order-zero membership, and the distributional cutoff theorem supplies H². -/
private theorem exists_memSobolev_two_ae_eq_near_compact_of_lp_laplacian_eq
    {Ω : Set E} (hΩ : IsOpen Ω) (u f : Lp F 2 (volume : Measure E))
    (hweak : ∀ φ : 𝓢(E, ℂ), HasCompactSupport φ → tsupport φ ⊆ Ω →
      (u : 𝓢'(E, F)) (Δ φ) = (f : 𝓢'(E, F)) φ)
    (K : Set E) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧ V ⊆ Ω ∧
      ∃ U : Lp F 2 (volume : Measure E),
        MemSobolev 2 2 (U : 𝓢'(E, F)) ∧ (U : E → F) =ᵐ[volume.restrict V] u := by
  obtain ⟨χ, hχcs, hχΩ, hχflat⟩ :=
    SchwartzMap.exists_eq_one_near_compact hΩ hK hKΩ
  have htwo : MemSobolev 2 2 (smulLeftCLM F χ (u : 𝓢'(E, F))) :=
    memSobolev_two_cutoff_of_lp_laplacian_eq hΩ u f hweak χ hχcs hχΩ
  let V : Set E := Ω ∩ interior {x | χ x = 1}
  have hV : IsOpen V := hΩ.inter isOpen_interior
  have hKV : K ⊆ V := by
    intro x hx
    refine ⟨hKΩ hx, mem_interior_iff_mem_nhds.mpr ?_⟩
    exact hχflat x hx
  have hχone : ∀ x ∈ V, χ x = 1 := by
    intro x hx
    exact (interior_subset : interior {y : E | χ y = 1} ⊆ {y : E | χ y = 1}) hx.2
  obtain ⟨U, hU, hUeq⟩ :=
    exists_memSobolev_ae_eq_of_cutoff χ u hV.measurableSet hχone htwo
  exact ⟨V, hV, hKV, inter_subset_left, U, hU, hUeq⟩

/-- A locally L² distributional Poisson solution has a global H² representative
near each compact subset of its open domain. Equality with the original function
is almost everywhere; no pointwise regularity or first weak derivative is assumed. -/
theorem exists_memSobolev_two_ae_eq_near_compact_of_integral_laplacian_eq
    {Ω : Set E} (hΩ : IsOpen Ω) {u f : E → F}
    (hu : ∀ K : Set E, IsCompact K → K ⊆ Ω → MemLp u 2 (volume.restrict K))
    (hf : ∀ K : Set E, IsCompact K → K ⊆ Ω → MemLp f 2 (volume.restrict K))
    (hweak : ∀ φ : 𝓢(E, ℂ), HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ x, (Δ φ) x • u x) = ∫ x, φ x • f x)
    (K : Set E) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧ V ⊆ Ω ∧
      ∃ U : Lp F 2 (volume : Measure E),
        MemSobolev 2 2 (U : 𝓢'(E, F)) ∧ (U : E → F) =ᵐ[volume.restrict V] u := by
  obtain ⟨η, hηcs, hηΩ, hηflat⟩ :=
    SchwartzMap.exists_eq_one_near_compact hΩ hK hKΩ
  have huη := memLp_cutoff_of_locally_memLp hu η hηcs hηΩ
  have hfη := memLp_cutoff_of_locally_memLp hf η hηcs hηΩ
  let uη : Lp F 2 volume := huη.toLp (fun x ↦ η x • u x)
  let fη : Lp F 2 volume := hfη.toLp (fun x ↦ η x • f x)
  let W : Set E := Ω ∩ interior {x | η x = 1}
  have hW : IsOpen W := hΩ.inter isOpen_interior
  have hKW : K ⊆ W := by
    intro x hx
    refine ⟨hKΩ hx, mem_interior_iff_mem_nhds.mpr ?_⟩
    exact hηflat x hx
  have hηone : ∀ x ∈ W, η x = 1 := by
    intro x hx
    exact (interior_subset : interior {y : E | η y = 1} ⊆ {y : E | η y = 1}) hx.2
  have hweakW : ∀ φ : 𝓢(E, ℂ), HasCompactSupport φ → tsupport φ ⊆ W →
      (uη : 𝓢'(E, F)) (Δ φ) = (fη : 𝓢'(E, F)) φ := by
    intro φ hφ hφW
    exact cutoff_laplacian_pairing η u f huη hfη φ
      (fun x hx ↦ hηone x (hφW hx)) (hweak φ hφ (fun x hx ↦ (hφW hx).1))
  obtain ⟨V, hV, hKV, hVW, U, hU, hUeq⟩ :=
    exists_memSobolev_two_ae_eq_near_compact_of_lp_laplacian_eq
      hW uη fη hweakW K hK hKW
  have huηeq : (uη : E → F) =ᵐ[volume.restrict V] u := by
    filter_upwards [ae_restrict_mem hV.measurableSet,
      ae_restrict_of_ae huη.coeFn_toLp] with x hx huηx
    calc
      uη x = η x • u x := huηx
      _ = u x := by rw [hηone x (hVW hx), one_smul]
  exact ⟨V, hV, hKV, fun x hx ↦ (hVW hx).1, U, hU, hUeq.trans huηeq⟩

end PDE.Elliptic.Interior
