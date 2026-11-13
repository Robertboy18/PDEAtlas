/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Linear.Fundamental

import PDE.Analysis.Calculus.Composition
import PDE.Analysis.Calculus.ImplicitFunction.LevelDerivative
import PDE.Analysis.Calculus.Prod.ParameterDerivative
import PDE.Analysis.ODE.SmoothDependence.Variation.Response

/-!
# Second response at a moving section from any data anchor

Two supplied flows solve `f - μ • id` and `f + P - μ • id` and agree as speed germs
at any anchor in a common closed interval. First-jet agreement of the fields along
the zero-speed orbit identifies that orbit and its first speed variation on both
sides of the anchor. The supplied smooth event times meet the same transverse
affine section at a common interior reference time.

The full second event chain rule determines the difference of the moving section
points. A continuous linear map annihilating the terminal velocity gives the
oriented propagator integral from the data anchor to the reference event time,
with coefficient one. No order between these two times is required. The original
left-anchor statement is retained as a specialization.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open PDE.Analysis.Evolution
open scoped ContDiff Topology

namespace PDE.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- Evaluate the existing second chain rule on the actual event graph. This stays
-- private: the general composition and mixed-derivative APIs already have owners.
private theorem hasDerivAt_deriv_event_chain
    {Q : ℝ → ℝ → E} {τ : ℝ → ℝ}
    (hQ : ContDiff ℝ 2 Q.uncurry) (hτ : ContDiffAt ℝ 2 τ 0) :
    HasDerivAt (deriv (fun μ ↦ Q (τ μ) μ))
      (deriv (deriv (Q (τ 0))) 0 +
        (2 * deriv τ 0) • deriv (fun s ↦ deriv (Q s) 0) (τ 0) +
        (deriv τ 0 * deriv τ 0) • deriv (deriv (fun s ↦ Q s 0)) (τ 0) +
        deriv (deriv τ) 0 • deriv (fun s ↦ Q s 0) (τ 0)) 0 := by
  let r : ℝ → ℝ × ℝ := fun μ ↦ (τ μ, μ)
  let K := fderiv ℝ (fderiv ℝ Q.uncurry) (τ 0, 0)
  have hQat : ContDiffAt ℝ 2 Q.uncurry (τ 0, 0) := hQ.contDiffAt
  have hD : DifferentiableAt ℝ (fderiv ℝ Q.uncurry) (τ 0, 0) :=
    (hQat.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have hparam (s μ : ℝ) : deriv (Q s) μ = fderiv ℝ Q.uncurry (s, μ) (0, 1) :=
    deriv_prod_timeSlice Q.uncurry s μ (hQ.differentiable (by norm_num) (s, μ))
  have htime (s : ℝ) :
      deriv (fun u ↦ Q u 0) s = fderiv ℝ Q.uncurry (s, 0) (1, 0) :=
    PDE.Analysis.deriv_parameter_eq (hQ.differentiable (by norm_num) (s, 0))
  have hDμ : HasDerivAt (fun μ ↦ fderiv ℝ Q.uncurry (τ 0, μ)) (K (0, 1)) 0 :=
    hD.hasFDerivAt.comp_hasDerivAt 0
      ((hasDerivAt_const 0 (τ 0)).prodMk (hasDerivAt_id 0))
  have hDt : HasDerivAt (fun s ↦ fderiv ℝ Q.uncurry (s, 0)) (K (1, 0)) (τ 0) :=
    hD.hasFDerivAt.comp_hasDerivAt (τ 0)
      ((hasDerivAt_id (τ 0)).prodMk (hasDerivAt_const (τ 0) (0 : ℝ)))
  -- the second partial derivatives of `Q` at `(τ 0, 0)` as entries of `K`
  have happly {g : ℝ → ℝ × ℝ →L[ℝ] E} {g' : ℝ × ℝ →L[ℝ] E} {x : ℝ} (hg : HasDerivAt g g' x)
      (w : ℝ × ℝ) : HasDerivAt (fun μ ↦ g μ w) (g' w) x := by
    simpa only [map_zero, add_zero] using hg.clm_apply (hasDerivAt_const x w)
  have hμμ : deriv (deriv (Q (τ 0))) 0 = K (0, 1) (0, 1) :=
    ((happly hDμ (0, 1)).congr_of_eventuallyEq (.of_forall (hparam (τ 0)))).deriv
  have htμ : deriv (fun s ↦ deriv (Q s) 0) (τ 0) = K (1, 0) (0, 1) :=
    ((happly hDt (0, 1)).congr_of_eventuallyEq (.of_forall fun s ↦ hparam s 0)).deriv
  have htt : deriv (deriv (fun s ↦ Q s 0)) (τ 0) = K (1, 0) (1, 0) :=
    ((happly hDt (1, 0)).congr_of_eventuallyEq (.of_forall htime)).deriv
  have hsym : K (0, 1) (1, 0) = K (1, 0) (0, 1) :=
    (hQat.isSymmSndFDerivAt (by norm_num)).eq (0, 1) (1, 0)
  have hquad : K (deriv τ 0, 1) (deriv τ 0, 1) =
      K (0, 1) (0, 1) + (2 * deriv τ 0) • K (1, 0) (0, 1) +
        (deriv τ 0 * deriv τ 0) • K (1, 0) (1, 0) := by
    rw [show (deriv τ 0, (1 : ℝ)) =
      deriv τ 0 • ((1, 0) : ℝ × ℝ) + (0, 1) by simp]
    simp only [map_add, map_smul, add_apply,
      smul_apply, smul_add, smul_smul]
    rw [hsym]
    simp only [two_mul, add_smul]
    abel
  have hr : ContDiffAt ℝ 2 r 0 := hτ.prodMk contDiffAt_id
  have hrfirst : deriv r 0 = (deriv τ 0, 1) :=
    ((hτ.differentiableAt (by norm_num)).hasDerivAt.prodMk (hasDerivAt_id 0)).deriv
  have hrnear : deriv r =ᶠ[𝓝 (0 : ℝ)] fun μ ↦ (deriv τ μ, 1) := by
    filter_upwards [hτ.eventually (by norm_num)] with μ hμ
    exact ((hμ.differentiableAt (by norm_num)).hasDerivAt.prodMk
      (hasDerivAt_id μ)).deriv
  have hrsecond : deriv (deriv r) 0 = (deriv (deriv τ) 0, 0) := by
    rw [hrnear.deriv_eq]
    exact (((hτ.derivWithin (m := 1) (by norm_num)).differentiableAt_one).hasDerivAt.prodMk
      (hasDerivAt_const 0 (1 : ℝ))).deriv
  have hsecond : deriv (deriv (fun μ ↦ Q (τ μ) μ)) 0 =
      K (deriv r 0) (deriv r 0) +
        fderiv ℝ Q.uncurry (τ 0, 0) (deriv (deriv r) 0) := by
    simpa only [r, K, Function.comp_def, Function.uncurry, fderiv_apply_one_eq_deriv] using
      PDE.Analysis.fderiv_fderiv_comp_apply (f := Q.uncurry) (g := r) (x := 0)
        hQat hr (1 : ℝ) (1 : ℝ)
  have hcurve : ContDiffAt ℝ 2 (fun μ ↦ Q (τ μ) μ) 0 := hQat.comp (f := r) 0 hr
  apply ((hcurve.derivWithin (m := 1) (by norm_num)).differentiableAt_one).hasDerivAt.congr_deriv
  rw [hsecond, hrfirst, hrsecond, hquad]
  rw [show (deriv (deriv τ) 0, (0 : ℝ)) =
    deriv (deriv τ) 0 • ((1, 0) : ℝ × ℝ) by simp, map_smul]
  rw [← hμμ, ← htμ, ← htt, ← htime (τ 0)]

variable [CompleteSpace E]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- For actual flows with the same speed germ at any anchor in the closed slab,
the second change of the moving section point is the fixed-time second response
projected along the terminal velocity. A continuous linear map killing that
velocity gives the oriented coefficient-one integral from the data anchor to the
event time; the anchor may lie before, at, or after that time.

The supplied event times have `C²` germs and meet the same transverse affine
section near speed zero. Their common base time lies strictly inside the slab.
Event slopes and the full second event chain are derived from these data; no
trajectory response or event derivative is assumed. -/
theorem exists_projected_movingEvent_secondSpeedVariation_response_of_mem_Icc
    {F G : ℝ → ℝ → E} {f P : E → E} {a b c t₀ level : ℝ}
    {τ υ : ℝ → ℝ} (hc : c ∈ Icc a b) (ht₀ : t₀ ∈ Ioo a b)
    (hF : ContDiff ℝ 3 F.uncurry) (hG : ContDiff ℝ 3 G.uncurry)
    (hf : ContDiff ℝ 2 f) (hP : ContDiff ℝ 2 P)
    (hodeF : ∀ t ∈ Icc a b, ∀ᶠ μ in 𝓝 (0 : ℝ),
      HasDerivAt (fun s ↦ F s μ) (f (F t μ) - μ • F t μ) t)
    (hodeG : ∀ t ∈ Icc a b, ∀ᶠ μ in 𝓝 (0 : ℝ),
      HasDerivAt (fun s ↦ G s μ) (f (G t μ) + P (G t μ) - μ • G t μ) t)
    (hinit : G c =ᶠ[𝓝 (0 : ℝ)] F c)
    (hjet : ∀ t ∈ Icc a b, P (F t 0) = 0 ∧ fderiv ℝ P (F t 0) = 0)
    (hτ : ContDiffAt ℝ 2 τ 0) (hυ : ContDiffAt ℝ 2 υ 0)
    (hτ₀ : τ 0 = t₀) (hυ₀ : υ 0 = t₀)
    (ell : E →L[ℝ] ℝ)
    (hsectionF : ∀ᶠ μ in 𝓝 (0 : ℝ), ell (F (τ μ) μ) = level)
    (hsectionG : ∀ᶠ μ in 𝓝 (0 : ℝ), ell (G (υ μ) μ) = level)
    (htransverse : ell (f (F t₀ 0)) ≠ 0)
    (L : E →L[ℝ] V) (hL : L (f (F t₀ 0)) = 0) :
    let R : ℝ → E := fun μ ↦ G (υ μ) μ - F (τ μ) μ
    let Δ : E := deriv (deriv (G t₀)) 0 - deriv (deriv (F t₀)) 0
    ∃ S : FundamentalSolution (fun t ↦ fderiv ℝ f (F t 0)) c (Icc a b),
      deriv υ 0 = deriv τ 0 ∧
      HasDerivAt (deriv R) (Δ - (ell Δ / ell (f (F t₀ 0))) • f (F t₀ 0)) 0 ∧
      L (deriv (deriv R) 0) =
        ∫ s in c..t₀, L (S.propagator t₀ s
          (fderiv ℝ (fderiv ℝ P) (F s 0) (deriv (F s) 0) (deriv (F s) 0))) := by
  intro R Δ
  have ht₀c : t₀ ∈ Icc a b := Ioo_subset_Icc_self ht₀
  obtain ⟨S, hbase, hfirst, hfixed⟩ :=
    exists_projected_secondSpeedVariation_response_of_mem_Icc hc
      hF hG hf hP hodeF hodeG hinit hjet L
  have hF₂ : ContDiff ℝ 2 F.uncurry := hF.of_le (by norm_num)
  have hG₂ : ContDiff ℝ 2 G.uncurry := hG.of_le (by norm_num)
  let v : E := f (F t₀ 0)
  have hbaseNear : (fun t ↦ G t 0) =ᶠ[𝓝 t₀] fun t ↦ F t 0 :=
    eventually_of_mem (isOpen_Ioo.mem_nhds ht₀) fun _ ht ↦ hbase (Ioo_subset_Icc_self ht)
  have hfirstNear : (fun t ↦ deriv (G t) 0) =ᶠ[𝓝 t₀] fun t ↦ deriv (F t) 0 :=
    eventually_of_mem (isOpen_Ioo.mem_nhds ht₀) fun _ ht ↦ hfirst (Ioo_subset_Icc_self ht)
  have hvelF : HasDerivAt (fun s ↦ F s 0) v t₀ := by
    simpa only [zero_smul, sub_zero] using (hodeF t₀ ht₀c).self_of_nhds
  have hvelG : HasDerivAt (fun s ↦ G s 0) v t₀ :=
    hvelF.congr_of_eventuallyEq hbaseNear
  -- Reuse the level-event derivative rule, as in the existing terminal owner.
  have hslope {Q : ℝ → ℝ → E} {e : ℝ → ℝ}
      (hQ : ContDiff ℝ 2 Q.uncurry) (he : ContDiffAt ℝ 2 e 0) (he₀ : e 0 = t₀)
      (hsection : ∀ᶠ μ in 𝓝 (0 : ℝ), ell (Q (e μ) μ) = level)
      (hvel : HasDerivAt (fun s ↦ Q s 0) v t₀) :
      deriv e 0 = -(ell (deriv (Q t₀) 0)) / ell v := by
    have hR : ContDiff ℝ 2 (fun u : ℝ × ℝ ↦ ell (Q u.2 u.1)) :=
      ell.contDiff.comp (hQ.comp (contDiff_snd.prodMk contDiff_fst))
    have htime : HasDerivAt (fun s ↦ ell (Q s 0)) (ell v) (e 0) := by
      rw [he₀]
      exact ell.hasFDerivAt.comp_hasDerivAt t₀ hvel
    have hnum : deriv (fun μ ↦ ell (Q t₀ μ)) 0 = ell (deriv (Q t₀) 0) :=
      (ell.hasFDerivAt.comp_hasDerivAt 0
        (((hQ.comp (contDiff_const.prodMk contDiff_id)).differentiable
          (by norm_num) 0).hasDerivAt)).deriv
    have h := PDE.Analysis.fderiv_level_event_apply
      (f := fun u : ℝ × ℝ ↦ ell (Q u.2 u.1)) (τ := e)
      (p₀ := 0) (c := level) (v := ell v)
      (hR.differentiable (by norm_num) (0, e 0))
      (he.differentiableAt (by norm_num)) hsection htime htransverse (1 : ℝ)
    simpa only [fderiv_apply_one_eq_deriv, he₀, hnum] using h
  have hκF := hslope hF₂ hτ hτ₀ hsectionF hvelF
  have hκG := hslope hG₂ hυ hυ₀ hsectionG hvelG
  have hW : deriv (G t₀) 0 = deriv (F t₀) 0 := hfirst ht₀c
  have hκ : deriv υ 0 = deriv τ 0 := by rw [hκG, hκF, hW]
  let qF : ℝ → E := fun μ ↦ F (τ μ) μ
  let qG : ℝ → E := fun μ ↦ G (υ μ) μ
  let C : E := (2 * deriv τ 0) • deriv (fun s ↦ deriv (F s) 0) t₀ +
    (deriv τ 0 * deriv τ 0) • deriv (deriv (fun s ↦ F s 0)) t₀
  have hqF : ContDiffAt ℝ 2 qF 0 := hF₂.contDiffAt.comp 0 (hτ.prodMk contDiffAt_id)
  have hqG : ContDiffAt ℝ 2 qG 0 := hG₂.contDiffAt.comp 0 (hυ.prodMk contDiffAt_id)
  -- The common time germ identifies acceleration and mixed terms, not just values.
  have hchainF : HasDerivAt (deriv qF)
      (deriv (deriv (F t₀)) 0 + C + deriv (deriv τ) 0 • v) 0 := by
    simpa only [qF, C, hτ₀, hvelF.deriv, add_assoc] using
      hasDerivAt_deriv_event_chain hF₂ hτ
  have hchainG : HasDerivAt (deriv qG)
      (deriv (deriv (G t₀)) 0 + C + deriv (deriv υ) 0 • v) 0 := by
    simpa only [qG, C, hυ₀, hκ, hfirstNear.deriv_eq,
      hbaseNear.deriv.deriv_eq, hbaseNear.deriv_eq, hvelF.deriv, add_assoc] using
      hasDerivAt_deriv_event_chain hG₂ hυ
  have hraw : HasDerivAt (fun μ ↦ deriv qG μ - deriv qF μ)
      (Δ + (deriv (deriv υ) 0 - deriv (deriv τ) 0) • v) 0 :=
    (hchainG.fun_sub hchainF).congr_deriv (by dsimp only [Δ]; rw [sub_smul]; abel)
  -- Differentiate the actual constant-section identity twice. The second event
  -- times need not agree: their difference is fixed by the section equation.
  have hsectionD {q : ℝ → E} (hq : ContDiffAt ℝ 2 q 0)
      (hsection : ∀ᶠ μ in 𝓝 (0 : ℝ), ell (q μ) = level) :
      (fun μ ↦ ell (deriv q μ)) =ᶠ[𝓝 (0 : ℝ)] fun _ ↦ 0 := by
    filter_upwards [hq.eventually (by norm_num), hsection.eventually_nhds] with μ hqμ hμ
    have h := ell.hasFDerivAt.comp_hasDerivAt μ
      (hqμ.differentiableAt (by norm_num)).hasDerivAt
    exact h.unique ((hasDerivAt_const μ level).congr_of_eventuallyEq hμ)
  have hsectionF' := hsectionD hqF hsectionF
  have hsectionG' := hsectionD hqG hsectionG
  have hsectionZero : (fun μ ↦ ell (deriv qG μ - deriv qF μ)) =ᶠ[𝓝 (0 : ℝ)] fun _ ↦ 0 :=
    (hsectionG'.and hsectionF').mono fun μ h ↦ by simp only [map_sub, h.1, h.2, sub_zero]
  have hzero := (ell.hasFDerivAt.comp_hasDerivAt 0 hraw).unique
    ((hasDerivAt_const 0 (0 : ℝ)).congr_of_eventuallyEq hsectionZero)
  have hη : deriv (deriv υ) 0 - deriv (deriv τ) 0 = -(ell Δ) / ell v := by
    apply (eq_div_iff htransverse).2
    simp only [map_add, map_smul, smul_eq_mul] at hzero
    linarith only [hzero]
  have hRnear : deriv R =ᶠ[𝓝 (0 : ℝ)] fun μ ↦ deriv qG μ - deriv qF μ := by
    filter_upwards [hqG.eventually (by norm_num), hqF.eventually (by norm_num)] with μ hGμ hFμ
    exact deriv_fun_sub (hGμ.differentiableAt (by norm_num))
      (hFμ.differentiableAt (by norm_num))
  have hsecond : HasDerivAt (deriv R) (Δ - (ell Δ / ell v) • v) 0 := by
    simpa only [hη, neg_div, neg_smul, sub_eq_add_neg] using hraw.congr_of_eventuallyEq hRnear
  -- `L` kills the velocity, so `L R'' = L Δ`, the fixed-time second response
  refine ⟨S, hκ, hsecond, ?_⟩
  rw [hsecond.deriv, map_sub, map_smul, hL, smul_zero, sub_zero]
  exact hfixed t₀ ht₀c

/-- For two actual speed-dependent flows from the same initial germ, the second
change of the moving section point is the fixed-time second response projected
along the terminal velocity onto the section. Any continuous linear map killing
that velocity therefore gives the coefficient-one propagator integral.

The supplied event times need only have `C²` germs and constant-section identities
near speed zero. Their common base time lies strictly inside the shared forward
slab; no event derivatives, variational equations, or response formula are assumed. -/
theorem exists_projected_movingEvent_secondSpeedVariation_response
    {F G : ℝ → ℝ → E} {f P : E → E} {a b t₀ level : ℝ}
    {τ υ : ℝ → ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (hF : ContDiff ℝ 3 F.uncurry) (hG : ContDiff ℝ 3 G.uncurry)
    (hf : ContDiff ℝ 2 f) (hP : ContDiff ℝ 2 P)
    (hodeF : ∀ t ∈ Icc a b, ∀ᶠ μ in 𝓝 (0 : ℝ),
      HasDerivAt (fun s ↦ F s μ) (f (F t μ) - μ • F t μ) t)
    (hodeG : ∀ t ∈ Icc a b, ∀ᶠ μ in 𝓝 (0 : ℝ),
      HasDerivAt (fun s ↦ G s μ) (f (G t μ) + P (G t μ) - μ • G t μ) t)
    (hinit : G a =ᶠ[𝓝 (0 : ℝ)] F a)
    (hjet : ∀ t ∈ Icc a b, P (F t 0) = 0 ∧ fderiv ℝ P (F t 0) = 0)
    (hτ : ContDiffAt ℝ 2 τ 0) (hυ : ContDiffAt ℝ 2 υ 0)
    (hτ₀ : τ 0 = t₀) (hυ₀ : υ 0 = t₀)
    (ell : E →L[ℝ] ℝ)
    (hsectionF : ∀ᶠ μ in 𝓝 (0 : ℝ), ell (F (τ μ) μ) = level)
    (hsectionG : ∀ᶠ μ in 𝓝 (0 : ℝ), ell (G (υ μ) μ) = level)
    (htransverse : ell (f (F t₀ 0)) ≠ 0)
    (L : E →L[ℝ] V) (hL : L (f (F t₀ 0)) = 0) :
    let R : ℝ → E := fun μ ↦ G (υ μ) μ - F (τ μ) μ
    let Δ : E := deriv (deriv (G t₀)) 0 - deriv (deriv (F t₀)) 0
    ∃ S : FundamentalSolution (fun t ↦ fderiv ℝ f (F t 0)) a (Icc a b),
      deriv υ 0 = deriv τ 0 ∧
      HasDerivAt (deriv R) (Δ - (ell Δ / ell (f (F t₀ 0))) • f (F t₀ 0)) 0 ∧
      L (deriv (deriv R) 0) =
        ∫ s in a..t₀, L (S.propagator t₀ s
          (fderiv ℝ (fderiv ℝ P) (F s 0) (deriv (F s) 0) (deriv (F s) 0))) := by
  exact exists_projected_movingEvent_secondSpeedVariation_response_of_mem_Icc
    (c := a) ⟨le_rfl, ht₀.1.le.trans ht₀.2.le⟩ ht₀ hF hG hf hP hodeF hodeG hinit hjet
    hτ hυ hτ₀ hυ₀ ell hsectionF hsectionG htransverse L hL

end PDE.Analysis.ODE
