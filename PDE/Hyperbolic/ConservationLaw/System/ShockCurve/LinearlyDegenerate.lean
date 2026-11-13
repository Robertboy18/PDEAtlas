/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ShockCurve.Regularity
public import PDE.Hyperbolic.ConservationLaw.System.Characteristics.Flow.LinearlyDegenerate

/-!
# Linearly degenerate shock and integral-curve germs

An integral curve of a linearly degenerate characteristic field has constant
speed and satisfies Rankine–Hugoniot. Local classification and spectral separation
identify its shock family. A normalized coordinate then identifies the parameter;
a nonzero coordinate derivative gives the same two-way germ comparison for other
normalizations. All statements are local. The first statement is the proof of Theorem 3 of
Evans, §11.2.3, and the identification of the shock family is its part (i), `Rₖ(z₀) = Sₖ(z₀)`,
near the base state.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.2.3, Theorem 3 and its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System

open Filter Metric Set
open scoped ContDiff Topology

/-- A continuous curve of jumps with one fixed characteristic speed selects
the corresponding local shock branch. Its parameter is recovered from the
state coordinate, including points with zero displacement. -/
theorem eventually_eq_shock_curve_of_constant_speed {m : ℕ} {flux : ℝ^m → ℝ^m} {u₀ : ℝ^m}
    (b : Module.Basis (Fin m) ℝ (ℝ^m)) {eig : Fin m → ℝ} {S : Fin m → ℝ → ℝ^m}
    {speed : Fin m → ℝ → ℝ} {I : Set ℝ} {V : Set (ℝ^m)} (horder : StrictMono eig) (hV : IsOpen V)
    (huV : u₀ ∈ V) (hS₀ : ∀ j, S j 0 = u₀) (ha₀ : ∀ j, speed j 0 = eig j)
    (ha : ∀ j, ContinuousAt (speed j) 0) (hcoord : ∀ j s, s ∈ I → b.equivFun (S j s - u₀) j = s)
    (hclass : ∀ u ∈ V, ∀ a : ℝ, u ≠ u₀ →
      (RankineHugoniot flux u₀ u a ↔ ∃ j s, s ∈ I ∧ s ≠ 0 ∧ u = S j s ∧ a = speed j s))
    {k : Fin m} {R : ℝ → ℝ^m} (hR₀ : R 0 = u₀) (hR : ContinuousAt R 0)
    (hRH : ∀ᶠ s in 𝓝 0, RankineHugoniot flux u₀ (R s) (eig k)) :
    ∀ᶠ s in 𝓝 0, R s = S k (b.equivFun (R s - u₀) k) ∧
      speed k (b.equivFun (R s - u₀) k) = eig k := by
  let c (j : Fin m) : ℝ^m →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj j).comp b.equivFunL.toContinuousLinearMap
  have hother (j : Fin m) :
      ∀ᶠ s in 𝓝 0, j ≠ k → speed j (c j (R s - u₀)) ≠ eig k := by
    by_cases hj : j = k
    · exact Filter.Eventually.of_forall fun _ h ↦ (h hj).elim
    · have hc₀ : c j (R 0 - u₀) = 0 := by rw [hR₀, sub_self, map_zero]
      have hs : ContinuousAt (fun s ↦ speed j (c j (R s - u₀))) 0 :=
        (show ContinuousAt (speed j) (c j (R 0 - u₀)) by rw [hc₀]; exact ha j).comp
          (f := fun s : ℝ ↦ c j (R s - u₀))
          ((c j).continuous.continuousAt.comp (hR.sub continuousAt_const))
      exact (hs.eventually_ne (by rw [hc₀, ha₀ j]; exact horder.injective.ne hj)).mono fun _ h _ ↦ h
  have hRV : ∀ᶠ s in 𝓝 0, R s ∈ V := hR (hR₀.symm ▸ hV.mem_nhds huV)
  filter_upwards [hRH, hRV, Filter.eventually_all.mpr hother] with s hs hsV hsep
  by_cases hzero : R s = u₀
  · simp only [hzero, sub_self, map_zero, Pi.zero_apply, hS₀ k, ha₀ k, and_self]
  · obtain ⟨j, t, ht, _htne, hstate, hspeed⟩ := (hclass _ hsV _ hzero).mp hs
    have htcoord : c j (R s - u₀) = t := hstate ▸ hcoord j t ht
    have hj : j = k := Classical.byContradiction fun h ↦ hsep j h (htcoord.symm ▸ hspeed.symm)
    subst j
    change b.equivFun (R s - u₀) k = t at htcoord
    exact ⟨htcoord ▸ hstate, htcoord ▸ hspeed.symm⟩

/-- The local shock branch of a linearly degenerate family is a
normalized characteristic integral curve, with constant characteristic and
shock speed. Equality holds on a common parameter neighborhood and hence in
both directions on its image. The complete classification of nearby nonzero
jumps is retained for all families. -/
theorem exists_local_shock_curves_eq_linearly_degenerate_flow {m : ℕ} {flux : ℝ^m → ℝ^m} {u₀ : ℝ^m}
    {k : Fin m} (hflux : ContDiff ℝ 2 flux) (hhyper : IsStrictlyHyperbolicAt flux u₀)
    (hld : IsLinearlyDegenerateFamily flux k) :
    ∃ b : Module.Basis (Fin m) ℝ (ℝ^m),
    ∃ S : Fin m → ℝ → ℝ^m, ∃ speed : Fin m → ℝ → ℝ,
    ∃ I : Set ℝ, ∃ V : Set (ℝ^m), ∃ r : ℝ^m → ℝ^m,
    ∃ R : ℝ → ℝ^m, ∃ W : Set (ℝ^m),
      IsOpen I ∧ 0 ∈ I ∧ IsOpen V ∧ u₀ ∈ V ∧ IsOpen W ∧ u₀ ∈ W ∧
      (∀ j, fderiv ℝ flux u₀ (b j) = characteristicSpeed flux j u₀ • b j) ∧
      (∀ j, S j 0 = u₀ ∧ speed j 0 = characteristicSpeed flux j u₀ ∧
        ContDiffOn ℝ 1 (S j) I ∧ ContDiffOn ℝ 1 (speed j) I ∧
        HasDerivAt (S j) (b j) 0 ∧
        ∀ s ∈ I, RankineHugoniot flux u₀ (S j s) (speed j s) ∧
          b.equivFun (S j s - u₀) j = s) ∧
      (∀ u ∈ V, ∀ a : ℝ, u ≠ u₀ →
        (RankineHugoniot flux u₀ u a ↔
          ∃ j s, s ∈ I ∧ s ≠ 0 ∧ u = S j s ∧ a = speed j s)) ∧
      ContDiffOn ℝ 1 r W ∧ r u₀ = b k ∧
      (∀ u ∈ W, Module.End.HasEigenvector (fderiv ℝ flux u).toLinearMap
        (characteristicSpeed flux k u) (r u) ∧ b.equivFun (r u) k = 1) ∧
      R 0 = u₀ ∧ ContDiffOn ℝ 1 R I ∧
      (∀ s ∈ I, R s = S k s ∧ R s ∈ W ∧ HasDerivAt R (r (R s)) s ∧
        speed k s = characteristicSpeed flux k (R s) ∧
        characteristicSpeed flux k (R s) = characteristicSpeed flux k u₀) ∧
      R '' I = S k '' I := by
  obtain ⟨b, eig, S, speed, I₀, V₀, horder, heigen, hI₀, hzero, hV₀, huV₀,
      _hV₀U, hcurves, hclass⟩ :=
    exists_local_shock_curves isOpen_univ (mem_univ u₀) hflux.contDiffOn hhyper
  have hcanonical (j : Fin m) : characteristicSpeed flux j u₀ = eig j :=
    congrFun (characteristicSpeed_eq_of_eigenbasis b horder heigen) j
  have heigen' (j : Fin m) :
      fderiv ℝ flux u₀ (b j) = characteristicSpeed flux j u₀ • b j := hcanonical j ▸ heigen j
  obtain ⟨r, R, W, ε, hW, huW, hε, hr, hr₀, hR₀, hRreg, hfield, hflow⟩ :=
    exists_normalized_linearly_degenerate_flow hflux hhyper hld b heigen'
  have hεzero : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_lt_zero.mpr hε, hε⟩
  have hRH : ∀ᶠ s in 𝓝 0, RankineHugoniot flux u₀ (R s) (eig k) := by
    filter_upwards [isOpen_Ioo.mem_nhds hεzero] with s hs
    simpa only [hcanonical k] using (hflow s hs).2.2.2.2
  have hselect := eventually_eq_shock_curve_of_constant_speed b horder hV₀ huV₀
    (fun j ↦ (hcurves j).1) (fun j ↦ (hcurves j).2.1)
    (fun j ↦ ((hcurves j).2.2.2.1.contDiffAt (hI₀.mem_nhds hzero)).continuousAt)
    (fun j s hs ↦ ((hcurves j).2.2.2.2.2 s hs).2.2) hclass hR₀
    (hRreg.contDiffAt (isOpen_Ioo.mem_nhds hεzero)).continuousAt hRH
  have heq : ∀ᶠ s in 𝓝 0,
      s ∈ Ioo (-ε) ε ∧ R s = S k s ∧ speed k s = characteristicSpeed flux k u₀ := by
    filter_upwards [isOpen_Ioo.mem_nhds hεzero, hselect] with s hs hsel
    exact ⟨hs, by simpa only [(hflow s hs).2.2.1] using hsel.1,
      by simpa only [(hflow s hs).2.2.1, hcanonical k] using hsel.2⟩
  obtain ⟨I, hIsub, hI, hIzero⟩ := _root_.mem_nhds_iff.mp
    (Filter.inter_mem (hI₀.mem_nhds hzero) heq)
  obtain ⟨V, hV, huV, _hVV₀, hclassI⟩ :=
    exists_shock_classification_on_parameter_neighborhood b hI hIzero
      (fun s hs ↦ (hIsub hs).1) hV₀ huV₀ (fun j s hs ↦ ((hcurves j).2.2.2.2.2 s hs).2.2) hclass
  refine ⟨b, S, speed, I, V, r, R, W, hI, hIzero, hV, huV, hW, huW, heigen', fun j ↦
    ⟨(hcurves j).1, (hcurves j).2.1.trans (hcanonical j).symm,
      (hcurves j).2.2.1.mono (fun s hs ↦ (hIsub hs).1),
      (hcurves j).2.2.2.1.mono (fun s hs ↦ (hIsub hs).1), (hcurves j).2.2.2.2.1,
      fun s hs ↦ ((hcurves j).2.2.2.2.2 s (hIsub hs).1).2⟩, hclassI, hr, hr₀, hfield, hR₀,
    hRreg.mono (fun s hs ↦ (hIsub hs).2.1), fun s hs ↦ ?_,
    Set.image_congr fun s hs ↦ (hIsub hs).2.2.1⟩
  have hf := hflow s (hIsub hs).2.1
  exact ⟨(hIsub hs).2.2.1, hf.1, hf.2.1, (hIsub hs).2.2.2.trans hf.2.2.2.1.symm, hf.2.2.2.1⟩

/-- A differently normalized characteristic integral curve has the
same local shock germ. The state coordinate is a local `C¹` change of parameter,
with a constructed inverse. In particular every sufficiently small shock
parameter is attained by the integral curve, not just conversely. -/
theorem exists_local_reparametrization_of_linearly_degenerate_integralCurve {m : ℕ}
    {flux : ℝ^m → ℝ^m} {u₀ : ℝ^m} {k : Fin m} (hflux : Differentiable ℝ flux)
    (hhyper : IsStrictlyHyperbolicAt flux u₀) (hld : IsLinearlyDegenerateFamily flux k)
    (b : Module.Basis (Fin m) ℝ (ℝ^m))
    (heigen : ∀ j, fderiv ℝ flux u₀ (b j) = characteristicSpeed flux j u₀ • b j)
    {S : Fin m → ℝ → ℝ^m} {speed : Fin m → ℝ → ℝ} {I : Set ℝ} {V : Set (ℝ^m)} (hV : IsOpen V)
    (huV : u₀ ∈ V) (hS₀ : ∀ j, S j 0 = u₀) (ha₀ : ∀ j, speed j 0 = characteristicSpeed flux j u₀)
    (ha : ∀ j, ContinuousAt (speed j) 0) (hcoord : ∀ j s, s ∈ I → b.equivFun (S j s - u₀) j = s)
    (hclass : ∀ u ∈ V, ∀ a : ℝ, u ≠ u₀ →
      (RankineHugoniot flux u₀ u a ↔ ∃ j s, s ∈ I ∧ s ≠ 0 ∧ u = S j s ∧ a = speed j s))
    {R : ℝ → ℝ^m} {r : ℝ^m → ℝ^m} (hR₀ : R 0 = u₀) (hR : ContDiffAt ℝ 1 R 0)
    (hflow : ∀ᶠ s in 𝓝 0, HasDerivAt R (r (R s)) s)
    (hfield : ∀ᶠ u in 𝓝 u₀, Module.End.HasEigenvector (fderiv ℝ flux u).toLinearMap
      (characteristicSpeed flux k u) (r u)) :
    let α : ℝ → ℝ := fun t ↦ b.equivFun (R t - u₀) k
    ∃ β : ℝ → ℝ,
      α 0 = 0 ∧ β 0 = 0 ∧ ContDiffAt ℝ 1 α 0 ∧ ContDiffAt ℝ 1 β 0 ∧
      HasDerivAt α (b.equivFun (r u₀) k) 0 ∧ b.equivFun (r u₀) k ≠ 0 ∧
      (∀ᶠ t in 𝓝 0, R t = S k (α t) ∧ speed k (α t) = characteristicSpeed flux k u₀) ∧
      (∀ᶠ s in 𝓝 0, α (β s) = s ∧ S k s = R (β s) ∧
        speed k s = characteristicSpeed flux k u₀) ∧
      (∀ᶠ t in 𝓝 0, β (α t) = t) := by
  let c : ℝ^m →L[ℝ] ℝ := (ContinuousLinearMap.proj k).comp b.equivFunL.toContinuousLinearMap
  let α : ℝ → ℝ := fun t ↦ c (R t - u₀)
  have hα₀ : α 0 = 0 := by simp only [α, hR₀, sub_self, map_zero]
  have hα : ContDiffAt ℝ 1 α 0 := c.contDiff.contDiffAt.comp 0 (hR.sub contDiffAt_const)
  have hdα : HasDerivAt α (c (r u₀)) 0 := c.hasFDerivAt.comp_hasDerivAt 0
    ((show HasDerivAt R (r u₀) 0 from hR₀ ▸ hflow.self_of_nhds).sub_const u₀)
  have hcne : c (r u₀) ≠ 0 := by
    have hv := hfield.self_of_nhds
    obtain ⟨j, hj, hrj⟩ := b.exists_eq_smul_of_apply_eq_smul
      (fderiv ℝ flux u₀).toLinearMap (fun j ↦ characteristicSpeed flux j u₀)
      (characteristicSpeed_spec hhyper).1.injective heigen hv.2 hv.apply_eq_smul
    have hjk : j = k := (characteristicSpeed_spec hhyper).1.injective hj.symm
    subst j
    exact fun hc ↦ hv.2 (by simpa only [show b.equivFun (r u₀) k = 0 from hc, zero_smul] using hrj)
  have hnear := hflow.and
    ((show Tendsto R (𝓝 0) (𝓝 u₀) by
      simpa only [ContinuousAt, hR₀] using hR.continuousAt).eventually hfield)
  obtain ⟨l, u, hzero, hball⟩ := mem_nhds_iff_exists_Ioo_subset.mp hnear
  have hRH : ∀ᶠ s in 𝓝 0,
      RankineHugoniot flux u₀ (R s) (characteristicSpeed flux k u₀) := by
    filter_upwards [isOpen_Ioo.mem_nhds hzero] with s hs
    simpa only [hR₀] using (constant_speed_rankineHugoniot_of_integralCurve
      isOpen_Ioo isPreconnected_Ioo (fun t _ ↦ hflux (R t)) (fun _ ht ↦ (hball ht).1)
      (fun t ht ↦ ⟨(hld (R t)).1, (hld (R t)).2 _ (hball ht).2,
        (hball ht).2.apply_eq_smul⟩) hs hzero).2
  have hforward := eventually_eq_shock_curve_of_constant_speed b
    (characteristicSpeed_spec hhyper).1 hV huV hS₀ ha₀ ha hcoord hclass hR₀ hR.continuousAt hRH
  obtain ⟨inverse, hi₀, hi, hright, hleft⟩ := PDE.Analysis.exists_implicit_inverse_family
      (f := fun p : ℝ × ℝ ↦ α p.1) (q₀ := 0)
      (hα.comp (f := Prod.fst) (0, 0) contDiffAt_fst) hdα hcne
  simp only [hα₀] at hi₀ hi hright
  let β : ℝ → ℝ := fun s ↦ inverse (s, 0)
  have hβ₀ : β 0 = 0 := hi₀
  have hβ : ContDiffAt ℝ 1 β 0 := hi.comp (f := fun s : ℝ ↦ (s, (0 : ℝ))) 0
      (contDiffAt_id.prodMk contDiffAt_const)
  have hβα : ∀ᶠ t in 𝓝 0, β (α t) = t :=
    (continuousAt_id.prodMk continuousAt_const).tendsto.eventually hleft
  have hαβ : ∀ᶠ s in 𝓝 0, α (β s) = s :=
    (continuousAt_id.prodMk continuousAt_const).tendsto.eventually hright
  refine ⟨β, hα₀, hβ₀, hα, hβ, hdα, hcne, hforward, ?_, hβα⟩
  have hback := (show Tendsto β (𝓝 0) (𝓝 0) by
    simpa only [ContinuousAt, hβ₀] using hβ.continuousAt).eventually hforward
  filter_upwards [hαβ, hback] with s hs hbs
  exact ⟨hs, by simpa only [show b.equivFun (R (β s) - u₀) k = s from hs] using hbs.1.symm,
    by simpa only [show b.equivFun (R (β s) - u₀) k = s from hs] using hbs.2⟩

end PDE.Hyperbolic.ConservationLaw.System
