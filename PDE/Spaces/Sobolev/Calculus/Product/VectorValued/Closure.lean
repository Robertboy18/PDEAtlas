/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Topology

/-!
# Stability of the bilinear weak product identity

Hölder multiplication is continuous on the `Lp` quotients. Together with the
closed weak-derivative graph, this passes a bilinear Leibniz identity to simultaneous
Sobolev limits, including either infinity endpoint.
-/

@[expose] public noncomputable section

open Filter MeasureTheory TopologicalSpace
open scoped ENNReal Sobolev Topology

namespace SobolevSpace.VectorValued

open GraphSpace

variable {n : ℕ} {Ω : Opens ℝ^n} {F G H : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
  {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]
  [ENNReal.HolderTriple p q r]

omit [CompleteSpace H] in
private theorem tendsto_holder_coordinates
    (B : F →L[ℝ] G →L[ℝ] H) {Us : ℕ → W^{1,p}(Ω; F)} {Vs : ℕ → W^{1,q}(Ω; G)}
    {U : W^{1,p}(Ω; F)} {V : W^{1,q}(Ω; G)}
    (hU : Tendsto Us atTop (𝓝 U)) (hV : Tendsto Vs atTop (𝓝 V))
    (a b : DerivIndex n 1) :
    Tendsto (fun j ↦ B.holder r ((Us j).val a) ((Vs j).val b)) atTop
      (𝓝 (B.holder r (U.val a) (V.val b))) := by
  have ha : Tendsto (fun j ↦ (Us j).val a) atTop (𝓝 (U.val a)) :=
    ((coordinateCLM a).continuous.tendsto U).comp hU
  have hb : Tendsto (fun j ↦ (Vs j).val b) atTop (𝓝 (V.val b)) :=
    ((coordinateCLM b).continuous.tendsto V).comp hV
  have ht := ((B.holderL (domainMeasure n Ω) p q r).continuous₂.tendsto
    (U.val a, V.val b)).comp (ha.prodMk_nhds hb)
  simpa only [Function.comp_def, Function.uncurry_apply_pair,
    ContinuousLinearMap.holderL_apply_apply] using ht

omit [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)] in
private theorem weak_bilinear_iff_holder
    (B : F →L[ℝ] G →L[ℝ] H) (U : W^{1,p}(Ω; F)) (V : W^{1,q}(Ω; G))
    (i : Fin n) :
    HasWeakDerivativeOn Ω [i]
      (fun x ↦ B (U.val (baseIndex n 1) x) (V.val (baseIndex n 1) x))
      (fun x ↦ B (U.val (singleDerivIndex n i) x) (V.val (baseIndex n 1) x) +
        B (U.val (baseIndex n 1) x) (V.val (singleDerivIndex n i) x)) ↔
    HasWeakDerivativeOn Ω [i]
      (B.holder r (U.val (baseIndex n 1)) (V.val (baseIndex n 1)))
      ((B.holder r (U.val (singleDerivIndex n i)) (V.val (baseIndex n 1)) +
        B.holder r (U.val (baseIndex n 1)) (V.val (singleDerivIndex n i)) :
          Lp H r (domainMeasure n Ω)) : ℝ^n → H) := by
  have hb := B.coeFn_holder (r := r) (U.val (baseIndex n 1)) (V.val (baseIndex n 1))
  have hd :
      ((B.holder r (U.val (singleDerivIndex n i)) (V.val (baseIndex n 1)) +
        B.holder r (U.val (baseIndex n 1)) (V.val (singleDerivIndex n i)) :
          Lp H r (domainMeasure n Ω)) : ℝ^n → H) =ᵐ[domainMeasure n Ω]
      fun x ↦ B (U.val (singleDerivIndex n i) x) (V.val (baseIndex n 1) x) +
        B (U.val (baseIndex n 1) x) (V.val (singleDerivIndex n i) x) := by
    filter_upwards [Lp.coeFn_add
      (B.holder r (U.val (singleDerivIndex n i)) (V.val (baseIndex n 1)))
      (B.holder r (U.val (baseIndex n 1)) (V.val (singleDerivIndex n i))),
      B.coeFn_holder (r := r) (U.val (singleDerivIndex n i)) (V.val (baseIndex n 1)),
      B.coeFn_holder (r := r) (U.val (baseIndex n 1)) (V.val (singleDerivIndex n i))]
      with x hadd h₁ h₂
    simp only [hadd, Pi.add_apply, h₁, h₂]
  exact ⟨fun h ↦ h.congr_ae hb.symm hd.symm, fun h ↦ h.congr_ae hb hd⟩

include r in
/-- A bilinear weak Leibniz identity passes to simultaneous Sobolev limits whenever
the three exponents satisfy Hölder's identity. -/
theorem hasWeakDerivativeOn_bilinear_of_tendsto
    (B : F →L[ℝ] G →L[ℝ] H) {Us : ℕ → W^{1,p}(Ω; F)} {Vs : ℕ → W^{1,q}(Ω; G)}
    {U : W^{1,p}(Ω; F)} {V : W^{1,q}(Ω; G)}
    (hU : Tendsto Us atTop (𝓝 U)) (hV : Tendsto Vs atTop (𝓝 V)) (i : Fin n)
    (hweak : ∀ j, HasWeakDerivativeOn Ω [i]
      (fun x ↦ B ((Us j).val (baseIndex n 1) x) ((Vs j).val (baseIndex n 1) x))
      (fun x ↦ B ((Us j).val (singleDerivIndex n i) x) ((Vs j).val (baseIndex n 1) x) +
        B ((Us j).val (baseIndex n 1) x) ((Vs j).val (singleDerivIndex n i) x))) :
    HasWeakDerivativeOn Ω [i]
      (fun x ↦ B (U.val (baseIndex n 1) x) (V.val (baseIndex n 1) x))
      (fun x ↦ B (U.val (singleDerivIndex n i) x) (V.val (baseIndex n 1) x) +
        B (U.val (baseIndex n 1) x) (V.val (singleDerivIndex n i) x)) := by
  apply (weak_bilinear_iff_holder (r := r) B U V i).mpr
  apply (isClosed_hasWeakDerivativeOn (F := H) (p := r) Ω [i]).mem_of_tendsto
    ((tendsto_holder_coordinates B hU hV (baseIndex n 1) (baseIndex n 1)).prodMk_nhds
      ((tendsto_holder_coordinates B hU hV (singleDerivIndex n i) (baseIndex n 1)).add
        (tendsto_holder_coordinates B hU hV (baseIndex n 1) (singleDerivIndex n i))))
  exact Eventually.of_forall fun j ↦
    (weak_bilinear_iff_holder (r := r) B (Us j) (Vs j) i).mp (hweak j)

end SobolevSpace.VectorValued
