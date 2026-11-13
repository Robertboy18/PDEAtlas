/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.TemperedDistribution.LocalSobolev.FirstOrder
import PDE.DistributionTheory.TestFunction.CompactCutoff

/-!
# Local L² regularity of the distributional Laplacian

If a distribution and its Laplacian are locally L² on an open set, every smooth
compact localization belongs to H². First the divergence form of the cutoff
identity puts its Laplacian in H⁻¹. The whole-space Bessel theorem then gives H¹.
An outer cutoff supplies these first derivatives on the support of a smaller
cutoff; the usual product rule and a second Bessel step give H².

Local L² membership is expressed by L² membership after every compact Schwartz
multiplier supported in the open set. This avoids imposing global L² bounds on
the distribution. The function-level application constructs the localized
distributions from data that need not be tempered on the whole space.
-/

@[expose] public noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal SchwartzMap LineDeriv Laplacian Topology Distributions

namespace SchwartzMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

/-- A compactly supported Schwartz cutoff can equal one near any compact subset
of an open set. This is the test-function cutoff, viewed in Schwartz space. -/
theorem exists_eq_one_near_compact {Ω K : Set E}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ a : 𝓢(E, ℂ), HasCompactSupport a ∧ tsupport a ⊆ Ω ∧
      ∀ x ∈ K, (a : E → ℂ) =ᶠ[𝓝 x] 1 := by
  obtain ⟨ψ, hψΩ, _, hψflat, _⟩ :=
    TestFunction.exists_eq_one_on_compact_finiteDimensional hΩ hK hKΩ
  have hcs : HasCompactSupport (fun x : E ↦ (ψ x : ℂ)) :=
    ψ.hasCompactSupport.comp_left (g := Complex.ofRealCLM) (by simp)
  let a : 𝓢(E, ℂ) := hcs.toSchwartzMap (Complex.ofRealCLM.contDiff.comp ψ.contDiff)
  have hsupp : tsupport a ⊆ tsupport ψ := by
    apply closure_minimal ?_ (isClosed_tsupport (ψ : E → ℝ))
    intro x hx
    apply subset_tsupport ψ
    change (ψ x : ℂ) ≠ 0 at hx
    change ψ x ≠ 0
    simpa only [ne_eq, Complex.ofReal_eq_zero] using hx
  refine ⟨a, hcs, hsupp.trans hψΩ, ?_⟩
  intro x hx
  filter_upwards [hψflat x hx] with y hy
  change (ψ y : ℂ) = 1
  simpa only [TestFunction.toFun_eq_coe, Pi.one_apply, Complex.ofReal_one] using
    congrArg Complex.ofReal hy

end SchwartzMap

namespace TemperedDistribution

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F]

variable [InnerProductSpace ℂ F] [CompleteSpace F]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
/-- After multiplication by `a`, differentiating `ηT` agrees with differentiating `T`
when `η` equals one near `tsupport a`. The derivative of `η` vanishes there. -/
private theorem smulLeftCLM_lineDeriv_cutoff (a η : 𝓢(E, ℂ))
    (hη : ∀ x ∈ tsupport a, (η : E → ℂ) =ᶠ[𝓝 x] 1)
    (T : 𝓢'(E, F)) (v : E) :
    smulLeftCLM F a (∂_{v} (smulLeftCLM F η T)) = smulLeftCLM F a (∂_{v} T) := by
  have hprod : (η : E → ℂ) * (a : E → ℂ) = a := by
    ext x
    by_cases hx : a x = 0
    · simp [hx]
    · have hflat : η x = 1 := (hη x (subset_tsupport a hx)).self_of_nhds
      change η x * a x = a x
      rw [hflat, one_mul]
  have hderiv : ((∂_{v} η : 𝓢(E, ℂ)) : E → ℂ) * (a : E → ℂ) = 0 := by
    ext x
    by_cases hx : a x = 0
    · simp [hx]
    · have hflat := (hη x (subset_tsupport a hx)).fderiv_eq (𝕜 := ℝ)
      have hd : (∂_{v} η : 𝓢(E, ℂ)) x = 0 := by
        rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, hflat]
        simp
      simp [hd]
  have hzero : smulLeftCLM F (0 : E → ℂ) T = 0 := by
    have hfun : (0 : E → ℂ) = fun _ : E ↦ (0 : ℂ) := by
      funext x
      rfl
    rw [hfun, smulLeftCLM_const, zero_smul]
  rw [lineDerivOp_smulLeftCLM, map_add,
    smulLeftCLM_smulLeftCLM_apply (∂_{v} η : 𝓢(E, ℂ)).hasTemperateGrowth a.hasTemperateGrowth,
    smulLeftCLM_smulLeftCLM_apply η.hasTemperateGrowth a.hasTemperateGrowth,
    hderiv, hprod, hzero, zero_add]

/-- A distribution with locally L² Laplacian is locally H² when it is itself locally L².
The first-order regularity used in the second cutoff identity is derived on an outer cutoff. -/
theorem memSobolev_two_smulLeftCLM_of_local_laplacian
    {Ω : Set E} (hΩ : IsOpen Ω) {T : 𝓢'(E, F)}
    (hT : ∀ a : 𝓢(E, ℂ), HasCompactSupport a → tsupport a ⊆ Ω →
      MemSobolev 0 2 (smulLeftCLM F a T))
    (hΔ : ∀ a : 𝓢(E, ℂ), HasCompactSupport a → tsupport a ⊆ Ω →
      MemSobolev 0 2 (smulLeftCLM F a (Δ T)))
    (a : 𝓢(E, ℂ)) (ha : HasCompactSupport a) (haΩ : tsupport a ⊆ Ω) :
    MemSobolev 2 2 (smulLeftCLM F a T) := by
  obtain ⟨η, hηcs, hηΩ, hηflat⟩ :=
    SchwartzMap.exists_eq_one_near_compact hΩ ha haΩ
  have hηone := memSobolev_one_smulLeftCLM_of_local_laplacian hT
    (fun b hb hbΩ ↦ MemSobolev.mono (by norm_num) (hΔ b hb hbΩ)) η hηcs hηΩ
  let b := stdOrthonormalBasis ℝ E
  have hgrad (v : E) : MemSobolev 0 2 (smulLeftCLM F (∂_{v} a : 𝓢(E, ℂ)) (∂_{v} T)) := by
    have hd : MemSobolev 0 2 (∂_{v} (smulLeftCLM F η T)) := by
      convert hηone.lineDerivOp (m := v) using 1
      norm_num
    have hh := hd.zero_smulLeftCLM (∂_{v} a : 𝓢(E, ℂ))
    rwa [smulLeftCLM_lineDeriv_cutoff (∂_{v} a : 𝓢(E, ℂ)) η
      (fun x hx ↦ hηflat x (SchwartzMap.tsupport_lineDerivOp_subset v a hx)) T v] at hh
  have hcutΔ : MemSobolev 0 2 (Δ (smulLeftCLM F a T)) := by
    rw [laplacian_smulLeftCLM b]
    apply (hΔ a ha haΩ).add
    apply MemSobolev.sum
    intro i _
    apply (hT _ (SchwartzMap.hasCompactSupport_lineDerivOp
      (SchwartzMap.hasCompactSupport_lineDerivOp ha (b i)) (b i))
      (((SchwartzMap.tsupport_lineDerivOp_subset (b i) (∂_{b i} a : 𝓢(E, ℂ))).trans
        (SchwartzMap.tsupport_lineDerivOp_subset (b i) a)).trans haΩ)).add
    exact (hgrad (b i)).smul 2
  simpa using (hT a ha haΩ).add_two_of_laplacian hcutΔ

end TemperedDistribution
