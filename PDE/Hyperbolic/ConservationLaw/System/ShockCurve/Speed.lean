/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ShockCurve.Regularity
public import PDE.Hyperbolic.ConservationLaw.System.Characteristics.Ordered
public import PDE.Analysis.Calculus.AveragedFDeriv.Asymptotics

/-!
# Shock-speed derivatives and quadratic midpoint expansion

A continuous physical shock speed agrees with an analytic eigenvalue branch of
the averaged Jacobian. The diagonal restriction of that same operator branch is
the canonical ordered characteristic speed. Thus the averaged-derivative calculus
gives both the half-factor in the speed derivative and the quadratic midpoint
estimate in the state displacement. These are (31) and Theorem 2 (iii) of Evans, §11.2.3.
Evans differentiates (26) twice and compares with the rarefaction curve, (27)-(31); we use the
averaged Jacobian instead.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.2.3, Theorem 2 (iii) and its proof,
  equations (26)-(31).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System

open Filter Set
open scoped ContDiff Topology

private theorem exists_shock_speed_operator_germ {m : ℕ} {flux : ℝ^m → ℝ^m} {U : Set (ℝ^m)}
    {u₀ : ℝ^m} (hU : IsOpen U) (hu₀ : u₀ ∈ U) (hflux : ContDiffOn ℝ 2 flux U)
    (b : Module.Basis (Fin m) ℝ (ℝ^m)) (eig : Fin m → ℝ) (horder : StrictMono eig)
    (heigen : ∀ k, fderiv ℝ flux u₀ (b k) = eig k • b k) {k : Fin m} {S : ℝ → ℝ^m} {speed : ℝ → ℝ}
    (hS₀ : S 0 = u₀) (ha₀ : speed 0 = eig k) (hS : ContinuousAt S 0) (ha : ContinuousAt speed 0)
    (hshock : ∀ᶠ s in 𝓝 0, RankineHugoniot flux u₀ (S s) (speed s) ∧ b.equivFun (S s - u₀) k = s) :
    ∃ a : (ℝ^m →L[ℝ] ℝ^m) → ℝ, ContDiffAt ℝ ω a (fderiv ℝ flux u₀) ∧
      characteristicSpeed flux k =ᶠ[𝓝 u₀] (fun u ↦ a (fderiv ℝ flux u)) ∧
      speed =ᶠ[𝓝 0] (fun s ↦ a (PDE.Analysis.averagedFDeriv flux u₀ (S s))) := by
  obtain ⟨ψ, hbase, W, hW, hAW, hframe⟩ :=
    PDE.Analysis.Calculus.SimpleEigenpair.exists_local_spectral_frame
      b (fderiv ℝ flux u₀) eig heigen horder
  obtain ⟨V, hV, huV, _hVU, hB, hinc⟩ :=
    PDE.Analysis.exists_local_contDiff_averagedFDeriv (n := 1) hU hu₀ hflux
  let B := PDE.Analysis.averagedFDeriv flux u₀
  have hB₀ : B u₀ = fderiv ℝ flux u₀ := PDE.Analysis.averagedFDeriv_self flux u₀
  have hT : ContinuousAt (fun s ↦ B (S s)) 0 :=
    (show ContinuousAt B (S 0) by rw [hS₀]; exact (hB.contDiffAt (hV.mem_nhds huV)).continuousAt
      ).comp hS
  have hT₀ : B (S 0) = fderiv ℝ flux u₀ := by rw [hS₀, hB₀]
  have heigennear : ∀ᶠ s in 𝓝 0, B (S s) (S s - u₀) = speed s • (S s - u₀) ∧
        b.equivFun (S s - u₀) k = s := by
    filter_upwards [hshock, hS (hS₀.symm ▸ hV.mem_nhds huV)] with s hs hsV
    exact ⟨(hinc (S s) hsV).trans hs.1, hs.2⟩
  have hray := PDE.Analysis.Calculus.SimpleEigenpair.eventually_eq_normalized_eigenline
    (B := id) hbase horder (hW.mem_nhds hAW) (fun j ↦ ((hframe _ hAW).2.1 j).1.continuousAt)
    (fun A hA ↦ ⟨(hframe A hA).1, fun j ↦ ((hframe A hA).2.1 j).2, (hframe A hA).2.2⟩)
    hT hT₀ ha ha₀ heigennear
  refine ⟨fun A ↦ (ψ k A).2, ((hframe _ hAW).2.1 k).1.snd, ?_, hray.mono (fun _ h ↦ h.2)⟩
  filter_upwards [((hflux.contDiffAt (hU.mem_nhds hu₀)).fderiv_right (m := 1) (by norm_num)
    ).continuousAt (hW.mem_nhds hAW)] with u hu
  obtain ⟨hord, hvec, c, hc⟩ := hframe _ hu
  exact congrFun (characteristicSpeed_eq_of_eigenbasis c hord
    (fun j ↦ by rw [hc j]; exact (hvec j).2.1.apply_eq_smul)) k

/-- The derivative of a physical shock speed is half the directional
derivative of the canonical characteristic speed. Local `C²` flux regularity
and the tangent suffice. -/
theorem hasDerivAt_shock_speed {m : ℕ} {flux : ℝ^m → ℝ^m} {U : Set (ℝ^m)} {u₀ : ℝ^m} (hU : IsOpen U)
    (hu₀ : u₀ ∈ U) (hflux : ContDiffOn ℝ 2 flux U) (b : Module.Basis (Fin m) ℝ (ℝ^m))
    (eig : Fin m → ℝ) (horder : StrictMono eig) (heigen : ∀ k, fderiv ℝ flux u₀ (b k) = eig k • b k)
    {k : Fin m} {S : ℝ → ℝ^m} {speed : ℝ → ℝ} (hS₀ : S 0 = u₀) (ha₀ : speed 0 = eig k)
    (hS : HasDerivAt S (b k) 0) (ha : ContinuousAt speed 0)
    (hshock : ∀ᶠ s in 𝓝 0, RankineHugoniot flux u₀ (S s) (speed s) ∧ b.equivFun (S s - u₀) k = s) :
    HasDerivAt speed ((1 / 2 : ℝ) * fderiv ℝ (characteristicSpeed flux k) u₀ (b k)) 0 := by
  obtain ⟨a, hreg, hdiag, havg⟩ := exists_shock_speed_operator_germ
    hU hu₀ hflux b eig horder heigen hS₀ ha₀ hS.continuousAt ha hshock
  have hd := PDE.Analysis.hasFDerivAt_comp_averagedFDeriv_self_of_contDiffAt
    (hflux.contDiffAt (hU.mem_nhds hu₀)) (hreg.differentiableAt (by simp))
  rw [← hdiag.fderiv_eq] at hd
  have hd' := (hS₀.symm ▸ hd).comp_hasDerivAt 0 hS
  refine HasDerivAt.congr_of_eventuallyEq ?_ havg
  simpa only [hS₀, Function.comp_def, smul_apply, smul_eq_mul] using hd'

/-- The physical shock-speed midpoint remainder is quadratic in the norm of
the jump. This does not replace that norm by a chosen curve parameter. -/
theorem exists_shock_speed_midpoint_bound {m : ℕ} {flux : ℝ^m → ℝ^m} {U : Set (ℝ^m)} {u₀ : ℝ^m}
    (hU : IsOpen U) (hu₀ : u₀ ∈ U) (hflux : ContDiffOn ℝ 3 flux U)
    (b : Module.Basis (Fin m) ℝ (ℝ^m)) (eig : Fin m → ℝ) (horder : StrictMono eig)
    (heigen : ∀ k, fderiv ℝ flux u₀ (b k) = eig k • b k) {k : Fin m} {S : ℝ → ℝ^m} {speed : ℝ → ℝ}
    (hS₀ : S 0 = u₀) (ha₀ : speed 0 = eig k) (hS : ContinuousAt S 0) (ha : ContinuousAt speed 0)
    (hshock : ∀ᶠ s in 𝓝 0, RankineHugoniot flux u₀ (S s) (speed s) ∧ b.equivFun (S s - u₀) k = s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ s in 𝓝 0, |speed s - (characteristicSpeed flux k (S s) + characteristicSpeed flux k u₀) /
        2| ≤ C * ‖S s - u₀‖ ^ 2 := by
  obtain ⟨a, hreg, hdiag, havg⟩ := exists_shock_speed_operator_germ
    hU hu₀ (hflux.of_le (by norm_num)) b eig horder heigen hS₀ ha₀ hS ha hshock
  obtain ⟨C, hC, hbound⟩ := PDE.Analysis.exists_abs_comp_averagedFDeriv_sub_mean_le
    (hflux.contDiffAt (hU.mem_nhds hu₀)) (hreg.of_le (by simp))
  have hT : Tendsto S (𝓝 0) (𝓝 u₀) := by simpa only [ContinuousAt, hS₀] using hS
  refine ⟨C, hC, ?_⟩
  filter_upwards [hT.eventually hbound, hT.eventually hdiag, havg] with s hs hdiagS hsavg
  simpa only [hsavg, hdiagS, hdiag.self_of_nhds] using hs

/-- Local shock curves with the full quadratic speed expansion. All objects,
the common neighborhood and its nonnegative remainder constant are constructed
from the locally smooth flux and strict hyperbolicity at the base state.

For finite `n`, `C^(n+1)` flux regularity gives `C^n` curves. The infinite-order
case uses the same common neighborhood. Classification excludes zero jumps,
where the Rankine–Hugoniot equation itself allows arbitrary speeds. -/
theorem exists_local_shock_curves_with_quadratic_speed {m : ℕ} {n : ℕ∞} {flux : ℝ^m → ℝ^m}
    {U : Set (ℝ^m)} {u₀ : ℝ^m} (hn : 2 ≤ n) (hU : IsOpen U) (hu₀ : u₀ ∈ U)
    (hflux : ContDiffOn ℝ ((n : ℕ∞ω) + 1) flux U) (hhyper : IsStrictlyHyperbolicAt flux u₀) :
    ∃ b : Module.Basis (Fin m) ℝ (ℝ^m),
    ∃ S : Fin m → ℝ → ℝ^m, ∃ speed : Fin m → ℝ → ℝ,
    ∃ I : Set ℝ, ∃ V : Set (ℝ^m), ∃ C : ℝ,
      0 ≤ C ∧
      (∀ k, fderiv ℝ flux u₀ (b k) = characteristicSpeed flux k u₀ • b k) ∧
      IsOpen I ∧ 0 ∈ I ∧ IsOpen V ∧ u₀ ∈ V ∧ V ⊆ U ∧
      (∀ k,
        S k 0 = u₀ ∧ speed k 0 = characteristicSpeed flux k u₀ ∧
        ContDiffOn ℝ n (S k) I ∧ ContDiffOn ℝ n (speed k) I ∧
        HasDerivAt (S k) (b k) 0 ∧
        HasDerivAt (speed k)
          ((1 / 2 : ℝ) * fderiv ℝ (characteristicSpeed flux k) u₀ (b k)) 0 ∧
        ∀ s ∈ I, S k s ∈ U ∧
          RankineHugoniot flux u₀ (S k s) (speed k s) ∧
          b.equivFun (S k s - u₀) k = s ∧
          |speed k s -
            (characteristicSpeed flux k (S k s) + characteristicSpeed flux k u₀) / 2|
              ≤ C * ‖S k s - u₀‖ ^ 2) ∧
      ∀ u ∈ V, ∀ a : ℝ, u ≠ u₀ →
        (RankineHugoniot flux u₀ u a ↔
          ∃ k s, s ∈ I ∧ s ≠ 0 ∧ u = S k s ∧ a = speed k s) := by
  have hn₁ : (1 : ℕ∞) ≤ n := le_trans (by norm_num) hn
  have hthree : (3 : ℕ∞ω) ≤ (n : ℕ∞ω) + 1 := by
    have hn₂ : (2 : ℕ∞ω) ≤ n := by
      simpa using (WithTop.coe_le_coe.mpr hn : ((2 : ℕ∞) : ℕ∞ω) ≤ n)
    calc
      (3 : ℕ∞ω) = 2 + 1 := rfl
      _ ≤ (n : ℕ∞ω) + 1 := add_le_add hn₂ le_rfl
  have hflux₃ : ContDiffOn ℝ 3 flux U := hflux.of_le hthree
  have hflux₂ : ContDiffOn ℝ 2 flux U := hflux₃.of_le (by norm_num)
  obtain ⟨b, eig, S, speed, I₀, V₀, horder, heigen, hI₀, hzero, hV₀, huV₀, hV₀U, hcurves, hclass⟩ :=
    exists_local_shock_curves_of_contDiffOn hn₁ hU hu₀ hflux hhyper
  have hcanonical : (fun k ↦ characteristicSpeed flux k u₀) = eig :=
    characteristicSpeed_eq_of_eigenbasis b horder heigen
  have hshock (k : Fin m) : ∀ᶠ s in 𝓝 0,
      RankineHugoniot flux u₀ (S k s) (speed k s) ∧ b.equivFun (S k s - u₀) k = s :=
    eventually_of_mem (hI₀.mem_nhds hzero) fun s hs ↦ ((hcurves k).2.2.2.2.2 s hs).2
  have hbound (k : Fin m) := exists_shock_speed_midpoint_bound
    hU hu₀ hflux₃ b eig horder heigen (hcurves k).1 (hcurves k).2.1
    ((hcurves k).2.2.1.contDiffAt (hI₀.mem_nhds hzero)).continuousAt
    ((hcurves k).2.2.2.1.contDiffAt (hI₀.mem_nhds hzero)).continuousAt (hshock k)
  choose c hc hcbound using hbound
  let C : ℝ := ∑ k, c k
  have hC : 0 ≤ C := Finset.sum_nonneg fun k _ ↦ hc k
  have hcC (k : Fin m) : c k ≤ C := Finset.single_le_sum (fun j _ ↦ hc j) (Finset.mem_univ k)
  obtain ⟨I, hIsub, hI, hIzero⟩ := _root_.mem_nhds_iff.mp
    (Filter.inter_mem (hI₀.mem_nhds hzero) (Filter.eventually_all.mpr hcbound))
  obtain ⟨V, hV, huV, hVV₀, hclassI⟩ :=
    exists_shock_classification_on_parameter_neighborhood b hI hIzero
      (fun s hs ↦ (hIsub hs).1) hV₀ huV₀ (fun k s hs ↦ ((hcurves k).2.2.2.2.2 s hs).2.2) hclass
  refine ⟨b, S, speed, I, V, C, hC, fun k ↦ by rw [congrFun hcanonical k]; exact heigen k, hI,
    hIzero, hV, huV, fun u hu ↦ hV₀U (hVV₀ hu), fun k ↦ ⟨(hcurves k).1,
      (hcurves k).2.1.trans (congrFun hcanonical k).symm,
      (hcurves k).2.2.1.mono (fun s hs ↦ (hIsub hs).1),
      (hcurves k).2.2.2.1.mono (fun s hs ↦ (hIsub hs).1), (hcurves k).2.2.2.2.1,
      hasDerivAt_shock_speed hU hu₀ hflux₂ b eig horder heigen
        (hcurves k).1 (hcurves k).2.1 (hcurves k).2.2.2.2.1
        ((hcurves k).2.2.2.1.contDiffAt (hI₀.mem_nhds hzero)).continuousAt (hshock k),
      fun s hs ↦ ?_⟩, hclassI⟩
  obtain ⟨hsU, hsRH, hscoord⟩ := (hcurves k).2.2.2.2.2 s (hIsub hs).1
  exact ⟨hsU, hsRH, hscoord,
    ((hIsub hs).2 k).trans (mul_le_mul_of_nonneg_right (hcC k) (sq_nonneg _))⟩

end PDE.Hyperbolic.ConservationLaw.System
