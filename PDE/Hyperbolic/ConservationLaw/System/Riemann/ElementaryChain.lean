/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.Riemann
public import PDE.Hyperbolic.ConservationLaw.System.WaveCurve.Construction

/-!
# Elementary wave chains for the local Riemann solver

The local solver in the proof of Theorem 4 of Evans, §11.2.4, applies the characteristic
families in increasing order, (45); we index them `0, ..., m - 1`. We describe the
intermediate states `z₁, ..., zₘ` of that composition and turn the inverse-function-theorem
strength vector into an explicit chain of elementary waves.

The states are prefixes of the ordered wave map, and physical admissibility is supplied by
`LocalWaveFamily.IsElementary`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.2.4, proof of Theorem 4, equations (44)-(47).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System

open Filter Metric Set
open scoped Topology

variable {m : ℕ}
variable {flux : ℝ^m → ℝ^m}
variable {fields : Fin m → CharacteristicField flux}
variable {states : Set (ℝ^m)}

namespace LocalWaveFamily

/-- State obtained after applying the first `j` characteristic families.

For `j ≥ m`, taking the prefix returns the whole family list, so the state is
the final composed wave state. The useful indices are `0, ..., m`. -/
def intermediateState
    (W : LocalWaveFamily flux fields states)
    (left strength : ℝ^m) (j : ℕ) : ℝ^m :=
  W.waveMapAlong ((List.finRange m).take j) (strength, left)

/-- Before any family is applied, the intermediate state is the left state. -/
@[simp]
theorem intermediateState_zero (W : LocalWaveFamily flux fields states) (left strength : ℝ^m) :
    W.intermediateState left strength 0 = left := by
  rfl

/-- Adding family `k` to the prefix applies exactly the `k`th wave
transformation to the preceding intermediate state. -/
theorem intermediateState_succ (W : LocalWaveFamily flux fields states) (left strength : ℝ^m)
    (k : Fin m) :
    W.intermediateState left strength (k + 1) =
      W.curve k (strength k) (W.intermediateState left strength k) := by
  have hk : (k : ℕ) < (List.finRange m).length := by
    rw [List.length_finRange]
    exact k.isLt
  rw [intermediateState, intermediateState, ← List.take_concat_get' (List.finRange m) k hk]
  simp [waveMapAlong, List.getElem_finRange]

/-- After all `m` families, the intermediate-state construction is the
ordered wave map used by the local inverse theorem. -/
@[simp]
theorem intermediateState_eq_composedWaveMap (W : LocalWaveFamily flux fields states)
    (left strength : ℝ^m) :
    W.intermediateState left strength m = W.composedWaveMap left strength := by
  have htake : (List.finRange m).take m = List.finRange m :=
    (List.take_eq_self_iff _).2 (by simp)
  rw [intermediateState, composedWaveMap, htake]

/-- At zero strengths every prefix is the left state. -/
@[simp]
theorem intermediateState_zero_strength
    (W : LocalWaveFamily flux fields states) (left : ℝ^m) (j : ℕ) :
    W.intermediateState left 0 j = left :=
  W.waveMapAlong_zero _ left

/-- Every finite prefix depends continuously on the strengths at zero.
Only the local derivatives at the base state are needed. -/
theorem continuousAt_intermediateState (W : LocalWaveFamily flux fields states) (left : ℝ^m)
    (hleft : left ∈ states) (j : ℕ) :
    ContinuousAt (fun strength ↦ W.intermediateState left strength j) 0 :=
  (W.hasStrictFDerivAt_waveMapAlong ((List.finRange m).take j) left hleft).continuousAt.comp
      (f := fun strength : ℝ^m ↦ (strength, left)) (continuousAt_id.prodMk continuousAt_const :
        ContinuousAt (fun strength : ℝ^m ↦ (strength, left)) 0)

/-- All wave steps satisfy any prescribed local construction condition when
the strengths are small. Each step uses its preceding prefix state. -/
theorem eventually_intermediate_steps (W : LocalWaveFamily flux fields states) (left : ℝ^m)
    (hleft : left ∈ states) {P : Fin m → ℝ × ℝ^m → Prop}
    (hP : ∀ᶠ p in 𝓝 ((0 : ℝ), left), ∀ k, P k p) :
    ∀ᶠ strength in 𝓝 (0 : ℝ^m), ∀ k, P k (strength k, W.intermediateState left strength k) := by
  refine eventually_all.mpr fun k ↦ ?_
  have hc : Continuous (fun strength : ℝ^m ↦ strength k) :=
    PiLp.continuous_apply 2 (fun _ : Fin m ↦ ℝ) k
  have ht : Tendsto (fun strength : ℝ^m ↦
      (strength k, W.intermediateState left strength k)) (𝓝 0) (𝓝 (0, left)) := by
    simpa only [ContinuousAt, W.intermediateState_zero_strength, PiLp.zero_apply]
      using hc.continuousAt.prodMk (W.continuousAt_intermediateState left hleft k)
  exact ht.eventually (hP.mono fun _ h ↦ h k)

/-- Every consecutive pair of prefix states is an admissible elementary
connection when the wave family is elementary. -/
theorem isElementaryConnection_intermediateState (W : LocalWaveFamily flux fields states)
    (hW : W.IsElementary) (left strength : ℝ^m) (k : Fin m) :
    IsElementaryConnection fields k (W.intermediateState left strength k)
      (W.intermediateState left strength (k + 1)) := by
  rw [W.intermediateState_succ]
  exact hW k (strength k) (W.intermediateState left strength k)

/-- Intermediate states selected by the local inverse for a nearby right
state. -/
def localRiemannState
    (W : LocalWaveFamily flux fields states) (left : ℝ^m) (hleft : left ∈ states)
    (basis : Module.Basis (Fin m) ℝ (ℝ^m))
    (hbasis :
      ∀ k, (fields k).rightEigenvector left = basis k)
    (right : ℝ^m) (j : ℕ) : ℝ^m :=
  W.intermediateState left (W.localRiemannStrength left hleft basis hbasis right) j

/-- The chain selected for a nearby right state starts at the left state. -/
@[simp]
theorem localRiemannState_zero (W : LocalWaveFamily flux fields states) (left : ℝ^m)
    (hleft : left ∈ states) (basis : Module.Basis (Fin m) ℝ (ℝ^m))
    (hbasis : ∀ k, (fields k).rightEigenvector left = basis k) (right : ℝ^m) :
    W.localRiemannState left hleft basis hbasis right 0 = left := by
  simp [localRiemannState]

/-- The last state of the selected local chain is the prescribed right
state. -/
theorem localRiemannState_eq_right (W : LocalWaveFamily flux fields states) (left : ℝ^m)
    (hleft : left ∈ states) (basis : Module.Basis (Fin m) ℝ (ℝ^m))
    (hbasis : ∀ k, (fields k).rightEigenvector left = basis k) {right : ℝ^m}
    (hright : right ∈ (W.localRiemannHomeomorph left hleft basis hbasis).target) :
    W.localRiemannState left hleft basis hbasis right m = right := by
  rw [localRiemannState, W.intermediateState_eq_composedWaveMap]
  exact W.composedWaveMap_localRiemannStrength left hleft basis hbasis hright

/-- The selected local inverse keeps every intermediate wave step in one
common construction neighborhood. Thus no curve is evaluated outside the
domain where its regularity, speed bounds, and differential equation were proved. -/
theorem eventually_localRiemann_steps (W : LocalWaveFamily flux fields states) (left : ℝ^m)
    (hleft : left ∈ states) (basis : Module.Basis (Fin m) ℝ (ℝ^m))
    (hbasis : ∀ k, (fields k).rightEigenvector left = basis k) {P : Fin m → ℝ × ℝ^m → Prop}
    (hP : ∀ᶠ p in 𝓝 ((0 : ℝ), left), ∀ k, P k p) :
    ∀ᶠ right in 𝓝 left, ∀ k, P k (W.localRiemannStrength left hleft basis hbasis right k,
      W.localRiemannState left hleft basis hbasis right k) :=
  (W.tendsto_localRiemannStrength left hleft basis hbasis).eventually
    (W.eventually_intermediate_steps left hleft hP)

/-- Consecutive states of the selected local chain are elementary waves in
characteristic-family order. -/
theorem isElementaryConnection_localRiemannState (W : LocalWaveFamily flux fields states)
    (hW : W.IsElementary) (left : ℝ^m) (hleft : left ∈ states)
    (basis : Module.Basis (Fin m) ℝ (ℝ^m))
    (hbasis : ∀ k, (fields k).rightEigenvector left = basis k) (right : ℝ^m) (k : Fin m) :
    IsElementaryConnection fields k (W.localRiemannState left hleft basis hbasis right k)
      (W.localRiemannState left hleft basis hbasis right (k + 1)) :=
  W.isElementaryConnection_intermediateState hW left
    (W.localRiemannStrength left hleft basis hbasis right) k

/-- Nearby right states admit a unique ordered strength vector, and its
prefix states form an elementary wave chain from the left state to the
right state.

Uniqueness concerns the strength vector inside the inverse-function-theorem
source neighborhood. The intermediate states are then determined by that
vector. -/
theorem existsUnique_localRiemann_strength_with_elementary_connections
    (W : LocalWaveFamily flux fields states) (hW : W.IsElementary) (left : ℝ^m)
    (hleft : left ∈ states) (basis : Module.Basis (Fin m) ℝ (ℝ^m))
    (hbasis : ∀ k, (fields k).rightEigenvector left = basis k) :
    ∃ source target : Set (ℝ^m),
      IsOpen source ∧ IsOpen target ∧
      0 ∈ source ∧ left ∈ target ∧
      ∀ right ∈ target,
        ∃! strength : ℝ^m,
          strength ∈ source ∧
            W.composedWaveMap left strength = right ∧
            ∀ k : Fin m,
              IsElementaryConnection fields k
                (W.intermediateState left strength k)
                (W.intermediateState left strength (k + 1)) := by
  rcases W.existsUnique_localRiemann_strength left hleft basis hbasis with
    ⟨source, target, hopenSource, hopenTarget, hzero, hleft, hsolve⟩
  refine ⟨source, target, hopenSource, hopenTarget, hzero, hleft, fun right hright ↦ ?_⟩
  rcases hsolve right hright with
    ⟨strength, ⟨hsource, hmap⟩, hunique⟩
  refine ⟨strength, ⟨hsource, hmap, ?_⟩, ?_⟩
  · exact fun k ↦ W.isElementaryConnection_intermediateState hW left strength k
  · exact fun candidate hcandidate ↦ hunique candidate ⟨hcandidate.1, hcandidate.2.1⟩

end LocalWaveFamily

/-- Strict hyperbolicity and the family alternatives construct an ordered
elementary chain between every sufficiently close pair of states. Local uniqueness is the uniqueness
of the strength vector in the inverse chart. -/
theorem exists_local_elementary_chain (hflux : ContDiff ℝ 2 flux)
    (hhyper : ∀ q, IsStrictlyHyperbolicAt flux q)
    (hfamilies : ∀ k, IsGenuinelyNonlinearFamily flux k ∨ IsLinearlyDegenerateFamily flux k)
    (left : ℝ^m) :
    ∃ fields : Fin m → CharacteristicField flux,
      (∀ k, (fields k).speed = characteristicSpeed flux k) ∧
      ∃ states : Set (ℝ^m), IsOpen states ∧ left ∈ states ∧
      ∃ W : LocalWaveFamily flux fields states, W.IsElementary ∧
      ∃ source target : Set (ℝ^m),
        IsOpen source ∧ IsOpen target ∧ 0 ∈ source ∧ left ∈ target ∧
        ∀ right ∈ target, ∃! strength : ℝ^m,
          strength ∈ source ∧ W.composedWaveMap left strength = right ∧
          ∀ k : Fin m, IsElementaryConnection fields k
            (W.intermediateState left strength k)
            (W.intermediateState left strength (k + 1)) := by
  obtain ⟨fields, hcanonical, states, hopen, hleft, W, hW, b, hb, _hcurves⟩ :=
    exists_local_elementary_wave_family hflux hhyper hfamilies left
  exact ⟨fields, hcanonical, states, hopen, hleft, W, hW,
    W.existsUnique_localRiemann_strength_with_elementary_connections hW left hleft
      b (fun k ↦ (hb k).symm)⟩

end PDE.Hyperbolic.ConservationLaw.System
