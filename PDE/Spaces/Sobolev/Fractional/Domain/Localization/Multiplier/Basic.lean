/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Localization.Estimates
public import PDE.Spaces.Sobolev.Fractional.Domain.Slobodeckij.Graph.Realization

/-!
# Scalar cutoff action on the intrinsic fractional graph

A bounded Lipschitz scalar acts on the normed-valued Gagliardo space by
multiplication of its physical representative. The construction is independent of
the chosen bounds. It needs neither completeness of the codomain nor regularity of
the domain, and includes dimension zero and exponent one.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped NNReal ENNReal FractionalSobolev

namespace SobolevSpace.Fractional.GagliardoSpace

variable {n : ℕ} {s : ℝ} {Ω : Set (ℝ^n)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {φ : ℝ^n → ℝ} {L M : ℝ≥0}

variable (hs0 : 0 < s) (hs1 : s < 1) (hp : p ≠ ∞)
  (hL : LipschitzWith L φ) (hM : ∀ x, ‖φ x‖ ≤ M)

/-- Multiply the physical representative by a bounded Lipschitz scalar. -/
def smulCutoff (u : W^{s,p}(Ω; F)) :
    W^{s,p}(Ω; F) :=
  ofFunction (fun x ↦ φ x • toLp n s Ω u x)
    (Localization.memGagliardo_smul_cutoff hs0 hs1 hL hM
      (memGagliardo_toLp u) (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)) hp)

/-- The cutoff action has the expected physical representative on the domain. -/
theorem toLp_smulCutoff_apply_ae (u : W^{s,p}(Ω; F)) :
    (toLp n s Ω (smulCutoff hs0 hs1 hp hL hM u) : ℝ^n → F) =ᵐ[volume.restrict Ω]
      fun x ↦ φ x • toLp n s Ω u x :=
  toLp_ofFunction_apply_ae _ _

/-- Scalar cutoff multiplication preserves addition of graph elements. -/
theorem smulCutoff_add (u v : W^{s,p}(Ω; F)) :
    smulCutoff hs0 hs1 hp hL hM (u + v) =
      smulCutoff hs0 hs1 hp hL hM u + smulCutoff hs0 hs1 hp hL hM v := by
  apply toLp_injective
  apply Lp.ext
  have hin := Lp.coeFn_add (toLp n s Ω u) (toLp n s Ω v)
  have hout := Lp.coeFn_add
    (toLp n s Ω (smulCutoff hs0 hs1 hp hL hM u))
    (toLp n s Ω (smulCutoff hs0 hs1 hp hL hM v))
  simp only [map_add]
  filter_upwards [toLp_smulCutoff_apply_ae hs0 hs1 hp hL hM (u + v),
    toLp_smulCutoff_apply_ae hs0 hs1 hp hL hM u,
    toLp_smulCutoff_apply_ae hs0 hs1 hp hL hM v, hin, hout] with x hsum hu hv hi ho
  simp only [map_add] at hsum
  rw [hsum, hi, ho]
  simp only [Pi.add_apply]
  rw [hu, hv, smul_add]

/-- Scalar cutoff multiplication commutes with the real vector-space action. -/
theorem smulCutoff_smul (c : ℝ) (u : W^{s,p}(Ω; F)) :
    smulCutoff hs0 hs1 hp hL hM (c • u) = c • smulCutoff hs0 hs1 hp hL hM u := by
  apply toLp_injective
  apply Lp.ext
  have hin := Lp.coeFn_smul c (toLp n s Ω u)
  have hout := Lp.coeFn_smul c (toLp n s Ω (smulCutoff hs0 hs1 hp hL hM u))
  simp only [map_smul]
  filter_upwards [toLp_smulCutoff_apply_ae hs0 hs1 hp hL hM (c • u),
    toLp_smulCutoff_apply_ae hs0 hs1 hp hL hM u, hin, hout] with x hcu hu hi ho
  simp only [map_smul] at hcu
  rw [hcu, hi, ho]
  simp only [Pi.smul_apply]
  rw [hu, smul_comm]

/-- Different valid Lipschitz and uniform bounds give the same graph element. -/
theorem smulCutoff_eq {L' M' : ℝ≥0}
    (hL' : LipschitzWith L' φ) (hM' : ∀ x, ‖φ x‖ ≤ M')
    (u : W^{s,p}(Ω; F)) :
    smulCutoff hs0 hs1 hp hL hM u = smulCutoff hs0 hs1 hp hL' hM' u := by
  apply toLp_injective
  apply Lp.ext
  exact (toLp_smulCutoff_apply_ae hs0 hs1 hp hL hM u).trans
    (toLp_smulCutoff_apply_ae hs0 hs1 hp hL' hM' u).symm

/-- The action agrees with pointwise multiplication of any Gagliardo representative. -/
theorem smulCutoff_ofFunction {f : ℝ^n → F} (hf : MemGagliardo n s Ω f (p := p)) :
    smulCutoff hs0 hs1 hp hL hM (ofFunction f hf) =
      ofFunction (fun x ↦ φ x • f x)
        (Localization.memGagliardo_smul_cutoff hs0 hs1 hL hM hf
          (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)) hp) := by
  apply toLp_injective
  apply Lp.ext
  filter_upwards [toLp_smulCutoff_apply_ae hs0 hs1 hp hL hM (ofFunction f hf),
    toLp_ofFunction_apply_ae f hf,
    toLp_ofFunction_apply_ae _ (Localization.memGagliardo_smul_cutoff hs0 hs1 hL hM hf
      (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)) hp)] with x hx hi ho
  rw [hx, hi, ho]

end SobolevSpace.Fractional.GagliardoSpace
