/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Evolution.HigherOrder.Continuity

/-!
# The forcing derivatives for higher parabolic regularity

At order `m`, the forcing data are the finite tuple
`f₀ ∈ L²(H^{2m}), …, fₘ ∈ L²(L²)`. Adjacent entries are linked by
weak time derivatives after restriction of the spatial order. With the
recursive tuple, the forcing data of the differentiated problem is the tail.

Forcing traces come from the mixed Sobolev time-continuity theorem, so no
trace, extension, approximant or solution trajectory is part of the forcing
data.
-/

@[expose] public noncomputable section

open scoped Sobolev

open MeasureTheory Set
open scoped ENNReal

namespace PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity.HigherOrder

open PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}

/-- The forcing tuple, stored from highest to lowest spatial regularity. -/
def ForcingJet (n : ℕ) (Ω : Set (ℝ^n)) (a b : ℝ) : ℕ → Type
  | 0 => Lp (W^{0,2}(Ω)) 2 (volume.restrict (Ioc a b))
  | m + 1 => Lp (W^{(2 * (m + 1)),2}(Ω)) 2 (volume.restrict (Ioc a b)) ×
      ForcingJet n Ω a b m

namespace ForcingJet

/-- The undifferentiated forcing field. -/
def head : {m : ℕ} → ForcingJet n Ω a b m →
    Lp (W^{(2 * m),2}(Ω)) 2 (volume.restrict (Ioc a b))
  | 0, F => F
  | _ + 1, F => F.1

/-- The forcing as a Bochner field in the pivot space. -/
def headBase {m : ℕ} (F : ForcingJet n Ω a b m) :
    Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b)) :=
  (wkpBaseCoordinateCLM (n := n) (m := 2 * m) (p := 2) (Ω := Ω)).compLpL
    2 (volume.restrict (Ioc a b)) F.head

/-- The pivot forcing represents the base coordinate of its Sobolev field. -/
theorem headBase_ae {m : ℕ} (F : ForcingJet n Ω a b m) :
    (fun t ↦ F.headBase t) =ᵐ[volume.restrict (Ioc a b)]
      fun t ↦ wkpBaseCoordinateCLM (F.head t) :=
  (wkpBaseCoordinateCLM (n := n) (m := 2 * m) (p := 2) (Ω := Ω)).coeFn_compLpL F.head

/-- Passing to the pivot field does not increase the forcing norm. -/
theorem norm_headBase_le {m : ℕ} (F : ForcingJet n Ω a b m) :
    ‖F.headBase‖ ≤ ‖F.head‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [F.headBase_ae] with t ht
  rw [ht]
  exact wkpBaseCoordinateCLM_norm_le _

/-- The sum of all forcing norms, including the last `L²(L²)` norm. -/
def normSum : {m : ℕ} → ForcingJet n Ω a b m → ℝ
  | 0, F => ‖head F‖
  | _ + 1, F => ‖F.1‖ + normSum F.2

/-- Every term in the forcing norm sum is nonnegative. -/
theorem normSum_nonneg {m : ℕ} (F : ForcingJet n Ω a b m) : 0 ≤ F.normSum := by
  induction m with
  | zero => exact norm_nonneg F.head
  | succ m ih => exact add_nonneg (norm_nonneg F.1) (ih F.2)

/-- The head forcing norm is bounded by the sum of the data norms. -/
theorem norm_head_le_normSum {m : ℕ} (F : ForcingJet n Ω a b m) :
    ‖F.head‖ ≤ F.normSum := by
  cases m with
  | zero => exact le_rfl
  | succ m =>
    change ‖F.1‖ ≤ ‖F.1‖ + F.2.normSum
    exact le_add_of_nonneg_right F.2.normSum_nonneg

/-- Each forcing entry is the weak time derivative of the previous one, tested in the
spatial order of the lower entry. The base case requires no time derivative. -/
def HasWeakDerivatives : {m : ℕ} → ForcingJet n Ω a b m → Prop
  | 0, _ => True
  | m + 1, F =>
      HasWeakTimeDerivativeOn (Ioo a b)
        (fun t ↦ lowerOrderCLM (show 2 * m ≤ 2 * (m + 1) by omega) (F.1 t))
        (fun t ↦ F.2.head t) ∧ HasWeakDerivatives F.2

/-- In the pivot space, the head of the tail is the weak derivative of the
head, by applying the spatial base-coordinate map. -/
theorem HasWeakDerivatives.headBase {m : ℕ} {F : ForcingJet n Ω a b (m + 1)}
    (hF : F.HasWeakDerivatives) :
    HasWeakTimeDerivativeOn (Ioo a b)
      (fun t ↦ F.headBase t) (fun t ↦ F.2.headBase t) := by
  have h := hF.1.map (wkpBaseCoordinateCLM (n := n) (m := 2 * m) (p := 2) (Ω := Ω))
  apply h.congr_ae_restrict measurableSet_Ioo
  · filter_upwards [(F.headBase_ae).filter_mono
      (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self))] with t ht
    exact ht.symm
  · exact F.2.headBase_ae.symm.filter_mono
      (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self))

/-- A pivot weak derivative between Sobolev fields is the derivative in
the common lower Sobolev order. Injectivity of the spatial base coordinate
identifies the vector-valued distributional identities. -/
theorem HasWeakDerivatives.cons_of_base (hopen : IsOpen Ω) {m : ℕ}
    (U : Lp (W^{(2 * (m + 1)),2}(Ω)) 2 (volume.restrict (Ioc a b)))
    {V : ForcingJet n Ω a b m} (hV : V.HasWeakDerivatives)
    (hweak : HasWeakTimeDerivativeOn (Ioo a b)
      (fun t ↦ wkpBaseCoordinateCLM (U t))
      (fun t ↦ wkpBaseCoordinateCLM (V.head t))) :
    HasWeakDerivatives (m := m + 1) (U, V) := by
  refine ⟨?_, hV⟩
  have hU : LocallyIntegrableOn (fun t ↦ U t) (Ioo a b) volume :=
    (locallyIntegrableOn_of_locallyIntegrable_restrict
      ((Lp.memLp U).locallyIntegrable (by norm_num))).mono_set Ioo_subset_Ioc_self
  have hhead : LocallyIntegrableOn (fun t ↦ V.head t) (Ioo a b) volume :=
    (locallyIntegrableOn_of_locallyIntegrable_restrict
      ((Lp.memLp V.head).locallyIntegrable (by norm_num))).mono_set Ioo_subset_Ioc_self
  exact HasWeakTimeDerivativeOn.of_map
    (wkpBaseCoordinateCLM (n := n) (m := 2 * m) (p := 2) (Ω := Ω))
    (wkpBaseCoordinateCLM_injective (n := n) (r := 2 * m) (p := 2) hopen)
    ((lowerOrderCLM (n := n) (Ω := Ω) (p := 2)
      (show 2 * m ≤ 2 * (m + 1) by omega)).locallyIntegrableOn_comp hU)
    hhead hweak

/-- The mixed Sobolev time theorem constructs the head forcing trace.
Its constant is chosen before the entire forcing tuple. -/
theorem exists_trace_bound [Fact (0 < n)] (m : ℕ)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary 2 Ω) (hab : a < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : ForcingJet n Ω a b (m + 1),
      F.HasWeakDerivatives →
      ∃ v : ℝ → W^{(2 * m + 1),2}(Ω), ContinuousOn v (Icc a b) ∧
        v =ᵐ[volume.restrict (Ioc a b)]
          (fun t ↦ lowerOrderCLM (show 2 * m + 1 ≤ 2 * (m + 1) by omega) (F.1 t)) ∧
        ∀ t ∈ Icc a b, ‖v t‖ ≤ C * (‖F.1‖ + ‖F.2.head‖) := by
  have htrace :
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ (f : Lp (W^{(2 * (m + 1)),2}(Ω)) 2 (volume.restrict (Ioc a b)))
          (df : Lp (W^{(2 * m),2}(Ω)) 2 (volume.restrict (Ioc a b))),
          HasWeakTimeDerivativeOn (Ioo a b)
            (fun t ↦ lowerOrderCLM (show 2 * m ≤ 2 * (m + 1) by omega) (f t))
            (fun t ↦ df t) →
          ∃ v : ℝ → W^{(2 * m + 1),2}(Ω), ContinuousOn v (Icc a b) ∧
            v =ᵐ[volume.restrict (Ioc a b)]
              (fun t ↦ lowerOrderCLM (show 2 * m + 1 ≤ 2 * (m + 1) by omega) (f t)) ∧
            ∀ t ∈ Icc a b, ‖v t‖ ≤ C * (‖f‖ + ‖df‖) := by
    simpa only [Nat.mul_succ] using
      exists_continuous_higher_sobolev_representative (2 * m) hopen hbounded hgraph hab
  obtain ⟨C, hC, htrace⟩ := htrace
  exact ⟨C, hC, fun F hF ↦ htrace F.1 F.2.head hF.1⟩

/-- The forcing trace constant depends only on the domain, order and interval. -/
def traceConstant [Fact (0 < n)] (m : ℕ)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary 2 Ω) (hab : a < b) : ℝ :=
  (exists_trace_bound m hopen hbounded hgraph hab).choose

/-- The constructed trace constant is nonnegative. -/
theorem traceConstant_nonneg [Fact (0 < n)] (m : ℕ)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary 2 Ω) (hab : a < b) :
    0 ≤ traceConstant m hopen hbounded hgraph hab :=
  (exists_trace_bound m hopen hbounded hgraph hab).choose_spec.1

/-- The chosen continuous representative of the head forcing. -/
def trace [Fact (0 < n)] {m : ℕ}
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary 2 Ω) (hab : a < b)
    (F : ForcingJet n Ω a b (m + 1)) (hF : F.HasWeakDerivatives) :
    ℝ → W^{(2 * m + 1),2}(Ω) :=
  ((exists_trace_bound m hopen hbounded hgraph hab).choose_spec.2 F hF).choose

/-- The forcing trace is continuous, represents the head forcing, and
satisfies the uniform estimate of the mixed Sobolev theorem. -/
theorem trace_spec [Fact (0 < n)] {m : ℕ}
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary 2 Ω) (hab : a < b)
    (F : ForcingJet n Ω a b (m + 1)) (hF : F.HasWeakDerivatives) :
    ContinuousOn (F.trace hopen hbounded hgraph hab hF) (Icc a b) ∧
      F.trace hopen hbounded hgraph hab hF =ᵐ[volume.restrict (Ioc a b)]
        (fun t ↦ lowerOrderCLM (show 2 * m + 1 ≤ 2 * (m + 1) by omega) (F.1 t)) ∧
      ∀ t ∈ Icc a b, ‖F.trace hopen hbounded hgraph hab hF t‖ ≤
        traceConstant m hopen hbounded hgraph hab * (‖F.1‖ + ‖F.2.head‖) :=
  ((exists_trace_bound m hopen hbounded hgraph hab).choose_spec.2 F hF).choose_spec

/-- Any continuous representative of the same Sobolev field agrees with the
constructed trace on the entire closed interval, including its endpoints. -/
theorem trace_eqOn [Fact (0 < n)] {m : ℕ}
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary 2 Ω) (hab : a < b)
    (F : ForcingJet n Ω a b (m + 1)) (hF : F.HasWeakDerivatives)
    {v : ℝ → W^{(2 * m + 1),2}(Ω)} (hv : ContinuousOn v (Icc a b))
    (hvAE : v =ᵐ[volume.restrict (Ioc a b)]
      fun t ↦ lowerOrderCLM (show 2 * m + 1 ≤ 2 * (m + 1) by omega) (F.1 t)) :
    EqOn (F.trace hopen hbounded hgraph hab hF) v (Icc a b) := by
  have htrace := F.trace_spec hopen hbounded hgraph hab hF
  apply Measure.eqOn_Icc_of_ae_eq volume hab.ne _ htrace.1 hv
  rw [← Measure.restrict_congr_set Ioc_ae_eq_Icc]
  exact htrace.2.1.trans hvAE.symm

end ForcingJet

end PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity.HigherOrder
