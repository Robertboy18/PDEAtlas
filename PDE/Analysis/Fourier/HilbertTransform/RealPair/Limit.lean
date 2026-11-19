/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.RealPair

/-!
# Passing the concrete Biot–Savart relation to an L² limit

Real L² functions embed continuously into complex L². The model's Hilbert pair
is exactly equality with the concrete spectral transform after this embedding.
Consequently the relation passes to strong L² limits. In fact convergence of
the input alone constructs the real output limit: the Hilbert transform is
continuous and the real subspace is closed.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory PDE.Analysis
open scoped Topology

namespace PDE.Analysis

/-- The concrete Hilbert pair is an equality between the complex embeddings
of the two real L² classes. -/
theorem isHilbertPair_iff_compLp_eq
    {f g : ℝ → ℝ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    IsHilbertPair f g ↔
      Complex.ofRealCLM.compLp (hg.toLp g) =
        hilbertTransform (Complex.ofRealCLM.compLp (hf.toLp f)) := by
  have hleft :
      (fun x ↦ (f x : ℂ)) =ᵐ[volume] Complex.ofRealCLM.compLp (hf.toLp f) := by
    filter_upwards [hf.coeFn_toLp, Complex.ofRealCLM.coeFn_compLp (hf.toLp f)]
      with x hx hy
    simpa only [Complex.ofRealCLM_apply, hx] using hy.symm
  have hright :
      (fun x ↦ (g x : ℂ)) =ᵐ[volume] Complex.ofRealCLM.compLp (hg.toLp g) := by
    filter_upwards [hg.coeFn_toLp, Complex.ofRealCLM.coeFn_compLp (hg.toLp g)]
      with x hx hy
    simpa only [Complex.ofRealCLM_apply, hx] using hy.symm
  constructor
  · rintro ⟨F, hF, hH⟩
    have heq : F = Complex.ofRealCLM.compLp (hf.toLp f) :=
      Lp.ext (hF.symm.trans hleft)
    subst F
    exact Lp.ext (hright.symm.trans hH)
  · intro heq
    exact ⟨_, hleft, heq ▸ hright⟩

/-- Strong L² convergence of both real representatives preserves the
spectral Hilbert relation. The index may be any nontrivial filter. -/
theorem IsHilbertPair.of_tendsto_Lp
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {f g : ι → ℝ → ℝ} {f₀ g₀ : ℝ → ℝ}
    (hf : ∀ i, MemLp (f i) 2 volume) (hg : ∀ i, MemLp (g i) 2 volume)
    (hf₀ : MemLp f₀ 2 volume) (hg₀ : MemLp g₀ 2 volume)
    (hpair : ∀ i, IsHilbertPair (f i) (g i))
    (hflim : Tendsto (fun i ↦ (hf i).toLp (f i)) l (𝓝 (hf₀.toLp f₀)))
    (hglim : Tendsto (fun i ↦ (hg i).toLp (g i)) l (𝓝 (hg₀.toLp g₀))) :
    IsHilbertPair f₀ g₀ := by
  apply (isHilbertPair_iff_compLp_eq hf₀ hg₀).mpr
  have hleft := (Complex.ofRealCLM.compLpL 2 volume).continuous.continuousAt.tendsto.comp
    hglim
  have hright := hilbertTransform.continuous.continuousAt.tendsto.comp
    ((Complex.ofRealCLM.compLpL 2 volume).continuous.continuousAt.tendsto.comp hflim)
  apply tendsto_nhds_unique hleft
  apply hright.congr'
  exact .of_forall fun i ↦ ((isHilbertPair_iff_compLp_eq (hf i) (hg i)).mp (hpair i)).symm

/-- Convergence of the vorticity in L² constructs the real Hilbert-transform
limit and forces convergence of its given real representatives. There is no
assumed output limit or assumed limiting Biot–Savart relation. -/
theorem exists_hilbertPair_limit_of_tendsto_Lp
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {f g : ι → ℝ → ℝ} {f₀ : ℝ → ℝ}
    (hf : ∀ i, MemLp (f i) 2 volume)
    (hf₀ : MemLp f₀ 2 volume) (hpair : ∀ i, IsHilbertPair (f i) (g i))
    (hflim : Tendsto (fun i ↦ (hf i).toLp (f i)) l (𝓝 (hf₀.toLp f₀))) :
    ∃ G : Lp ℝ 2 (volume : Measure ℝ),
      IsHilbertPair f₀ G ∧
        Tendsto (fun i ↦ (hpair i).memLp_right.toLp (g i)) l (𝓝 G) := by
  let embed := Complex.ofRealCLM.compLpL 2 (volume : Measure ℝ)
  let realPart := Complex.reCLM.compLpL 2 (volume : Measure ℝ)
  let F : ComplexL2 := embed (hf₀.toLp f₀)
  let G : Lp ℝ 2 (volume : Measure ℝ) := realPart (hilbertTransform F)
  have hreal (u : Lp ℝ 2 (volume : Measure ℝ)) : realPart (embed u) = u := by
    apply Lp.ext
    filter_upwards [Complex.ofRealCLM.coeFn_compLp u,
      Complex.reCLM.coeFn_compLp (embed u)] with x hx hy
    change (embed u : ℝ → ℂ) x = (u x : ℂ) at hx
    change (realPart (embed u) : ℝ → ℝ) x = (embed u x).re at hy
    rw [hy, hx, Complex.ofReal_re]
  have hid (i : ι) :
      realPart (hilbertTransform (embed ((hf i).toLp (f i)))) =
        (hpair i).memLp_right.toLp (g i) := by
    have heq : embed ((hpair i).memLp_right.toLp (g i)) =
        hilbertTransform (embed ((hf i).toLp (f i))) :=
      (isHilbertPair_iff_compLp_eq (hf i) (hpair i).memLp_right).mp (hpair i)
    rw [← heq]
    exact hreal _
  have hGlim :
      Tendsto (fun i ↦ (hpair i).memLp_right.toLp (g i)) l (𝓝 G) := by
    have hh := realPart.continuous.continuousAt.tendsto.comp
      (hilbertTransform.continuous.continuousAt.tendsto.comp
        (embed.continuous.continuousAt.tendsto.comp hflim))
    exact hh.congr' (.of_forall hid)
  refine ⟨G, ?_, hGlim⟩
  apply IsHilbertPair.of_tendsto_Lp hf (fun i ↦ (hpair i).memLp_right)
    hf₀ (Lp.memLp G) hpair hflim
  simpa only [Lp.toLp_coeFn] using hGlim

end PDE.Analysis
