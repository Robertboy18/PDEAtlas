/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.VectorValued.Density.UpToBoundary.Translation
public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Restriction
import PDE.Spaces.Sobolev.Approximation.Density.UpToBoundary.Translation
import PDE.Spaces.Sobolev.Approximation.VectorValued.Mollification.WeakDerivatives.Local

/-!
# Banach-valued Sobolev approximation on an inward translation patch

Translate the center of convolution into the domain before smoothing. The inward
closed-ball condition identifies every classical derivative with a translated
mollification of the corresponding weak derivative, extended by zero in `Lp`.
Translation continuity then gives convergence in the full finite-order Sobolev graph.

The codomain is any real Banach space, and the dimension and derivative order may
be zero. Zero extension is used only for the individual `Lp` rows, never as a
Sobolev extension across the boundary, and the approximants need not have compact support.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Set Filter TopologicalSpace
open scoped ENNReal Topology Sobolev

namespace SobolevSpace.VectorValued.UpToBoundary

open Approximation GraphSpace

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Uniform inward translations yield globally smooth local approximants converging
in the full `W^{k,p}` norm, with every derivative row represented classically. -/
theorem local_approximation {Ω V : Opens ℝ^n}
    (hp : p ≠ ∞) (U : W^{k,p}(Ω; F)) (v : ℝ^n) {δ : ℝ} (hδ : 0 < δ)
    (hball : ∀ ε ∈ Ioo 0 δ, ∀ x ∈ (V ⊓ Ω : Opens ℝ^n),
      Metric.closedBall (x + ε • v) ε ⊆ Ω) :
    ∃ f : ℕ → ℝ^n → F, (∀ m, ContDiff ℝ (⊤ : ℕ∞) (f m)) ∧
      ∃ A : ℕ → W^{k,p}(V ⊓ Ω; F),
        (∀ m a, ((A m).val a : ℝ^n → F) =ᵐ[domainMeasure n (V ⊓ Ω)]
          iteratedPartialDeriv a.toList (f m)) ∧
        Tendsto A atTop (𝓝 (restrictCLM (inf_le_right : V ⊓ Ω ≤ Ω) U)) := by
  let μ := standardMollifier n
  obtain ⟨R₀, hR₀⟩ := μ.compactSupport.isBounded.subset_closedBall (0 : ℝ^n)
  let R := max R₀ 1
  have hRpos : 0 < R := zero_lt_one.trans_le (le_max_right _ _)
  have hR : tsupport μ.ρ ⊆ Metric.closedBall (0 : ℝ^n) R :=
    hR₀.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  let t (m : ℕ) := δ / ((m : ℝ) + 2)
  have htpos (m : ℕ) : 0 < t m := div_pos hδ (by positivity)
  have htδ (m : ℕ) : t m < δ :=
    div_lt_self hδ (lt_add_of_nonneg_of_lt (Nat.cast_nonneg m) one_lt_two)
  have ht0 : Tendsto t atTop (𝓝 0) :=
    (tendsto_atTop_add_const_right atTop (2 : ℝ)
      tendsto_natCast_atTop_atTop).const_div_atTop δ
  let ε (m : ℕ) := t m / R
  have hεpos (m : ℕ) : 0 < ε m := div_pos (htpos m) hRpos
  have hε0 : Tendsto ε atTop (𝓝 0) := by
    simpa only [zero_div] using ht0.div_const R
  let g (a : DerivIndex n k) : ℝ^n → F := U.val a
  have hg (a : DerivIndex n k) : MemLp ((Ω : Set ℝ^n).indicator (g a)) p volume :=
    (memLp_indicator_iff_restrict Ω.isOpen.measurableSet.nullMeasurableSet).mpr (Lp.memLp _)
  let f (m : ℕ) (x : ℝ^n) : F :=
    mollifyVector μ (ε m) ((Ω : Set ℝ^n).indicator (g (baseIndex n k))) (x + t m • v)
  have hf (m : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (f m) :=
    (mollifyVector_contDiff_of_pos μ (hεpos m) _ ((hg _).locallyIntegrable Fact.out)).comp
      (contDiff_id.add contDiff_const)
  have hD (m : ℕ) (a : DerivIndex n k) (x : ℝ^n) (hx : x ∈ (V ⊓ Ω : Opens ℝ^n)) :
      iteratedPartialDeriv a.toList (f m) x =
        mollifyVector μ (ε m) ((Ω : Set ℝ^n).indicator (g a)) (x + t m • v) := by
    rw [Approximation.UpToBoundary.iteratedPartialDeriv_comp_add]
    apply iteratedPartialDeriv_mollifyVector_indicator_eq μ (hεpos m) hR
      ((hg _).locallyIntegrable Fact.out) ((hg _).locallyIntegrable Fact.out) (U.property a)
    simpa only [ε, div_mul_cancel₀ _ hRpos.ne'] using
      hball (t m) ⟨htpos m, htδ m⟩ x hx
  have hmem (m : ℕ) (a : DerivIndex n k) :
      MemLp (iteratedPartialDeriv a.toList (f m)) p (domainMeasure n (V ⊓ Ω)) := by
    have hshift : MemLp (fun x : ℝ^n ↦
        mollifyVector μ (ε m) ((Ω : Set ℝ^n).indicator (g a)) (x + t m • v)) p volume :=
      (memLp_mollifyVector μ (hεpos m) hp (hg a)).comp_measurePreserving
        (measurePreserving_add_right volume (t m • v))
    exact (memLp_congr_ae (ae_restrict_of_forall_mem (V ⊓ Ω).isOpen.measurableSet (hD m a))).mpr
      (hshift.mono_measure Measure.restrict_le_self)
  have hweak (m : ℕ) (a : DerivIndex n k) :
      HasWeakDerivativeOn (V ⊓ Ω) a.toList
        (iteratedPartialDeriv (baseIndex n k).toList (f m))
        (iteratedPartialDeriv a.toList (f m)) := by
    simpa only [baseIndex_toList, iteratedPartialDeriv] using
      hasWeakDerivativeOn_iteratedPartialDeriv (Ω := V ⊓ Ω) (hf m) a.toList
  let A (m : ℕ) : W^{k,p}(V ⊓ Ω; F) := ofWeakDerivatives (Ω := V ⊓ Ω) (p := p)
    (fun a : DerivIndex n k ↦ iteratedPartialDeriv a.toList (f m)) (hmem m) (hweak m)
  have hA (m : ℕ) (a : DerivIndex n k) :
      ((A m).val a : ℝ^n → F) =ᵐ[domainMeasure n (V ⊓ Ω)]
        iteratedPartialDeriv a.toList (f m) :=
    ofWeakDerivatives_apply_ae (Ω := V ⊓ Ω) (p := p) _ (hmem m) (hweak m) a
  have hcoord (a : DerivIndex n k) :
      Tendsto (fun m ↦ eLpNorm (fun x ↦ iteratedPartialDeriv a.toList (f m) x - g a x)
        p (domainMeasure n (V ⊓ Ω))) atTop (𝓝 0) := by
    have hglob := mollifyVector_translate_converges_Lp μ hp (hg a) ε hεpos hε0
      (fun m ↦ t m • v) (by simpa only [zero_smul] using ht0.smul_const v)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hglob
      (fun _ ↦ zero_le) (fun m ↦ ?_)
    have heq :
        (fun x ↦ iteratedPartialDeriv a.toList (f m) x - g a x)
          =ᵐ[domainMeasure n (V ⊓ Ω)] fun x ↦
            mollifyVector μ (ε m) ((Ω : Set ℝ^n).indicator (g a)) (x + t m • v) -
              (Ω : Set ℝ^n).indicator (g a) x :=
      ae_restrict_of_forall_mem (V ⊓ Ω).isOpen.measurableSet fun x hx ↦
        congrArg₂ (· - ·) (hD m a x hx) (indicator_of_mem hx.2 (g a)).symm
    exact (eLpNorm_congr_ae heq).trans_le (eLpNorm_restrict_le _ _ _ _)
  refine ⟨f, hf, A, hA, tendsto_subtype_rng.mpr <| ((PiLp.homeomorph p (fun _ : DerivIndex n k ↦
    Lp F p (domainMeasure n (V ⊓ Ω)))).symm.continuous.tendsto _).comp <|
      tendsto_pi_nhds.mpr fun a ↦ ?_⟩
  refine (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mpr
    ((hcoord a).congr fun m ↦ eLpNorm_congr_ae ?_)
  filter_upwards [hA m a, restrictCLM_apply_ae (inf_le_right : V ⊓ Ω ≤ Ω) U a]
    with x ha hw
  exact congrArg₂ (· - ·) ha.symm hw.symm

end SobolevSpace.VectorValued.UpToBoundary
