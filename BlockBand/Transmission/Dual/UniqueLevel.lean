module

public import BlockBand.Transmission.Dual.UniquePad
public import BlockBand.Transmission.Dual.MPConverse
public import BlockBand.SourceProcess.Stochastic.Uniqueness.Main

/-!
# The level-`p` dual as a flat martingale problem

* `IsDualFrom`: the class for the level induction. It is `IsDualDeletionProcess` with the start
  point replaced by "level `p` a.s." (any law of the start in `𝒞_p`), with deletion paths at
  **every** `ω` and `N₀ ≤ p` at every `ω` (normalized form, `exists_normalized`).
* `padPath`: the front-padded flat state `V_t ∈ ℝ^{p+p}`, adapted and continuous at every `ω`.
* `isTestMPSolution_padPath`: `V` solves the `C_c^∞`-test martingale problem for the flat
  coefficients in `flatChamber p` (its test martingale *is* the level-`p` `dualMartingale`,
  pathwise on `{N₀ = p}`).
* `IsDualFrom.isMPSolutionOn`: `V` solves the localized martingale problem in `flatChamber p`;
  this is the input of `map_stopped_padPath_eq`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.Uniqueness BlockBand.SourceProcess.Stochastic.SemimartingaleIto
open scoped NNReal ENNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

/-- The internal class of the level induction: `IsDualDeletionProcess` from a random start at
level `p`, in normalized form.
-/
structure IsDualFrom {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) (D0 : ℝ) (p : ℕ)
    (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ) : Prop where
  prob : IsProbabilityMeasure P
  adapted : ∀ t, Measurable[𝓖 t] (N t) ∧ Measurable[𝓖 t] (X t) ∧ Measurable[𝓖 t] (Y t)
  start : ∀ᵐ ω ∂P, N 0 ω = p
  bound : ∀ ω, N 0 ω ≤ p
  paths : ∀ ω, IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω)
  martingale : ∀ q : ℕ, 1 ≤ q → q ≤ p → ∀ f : DualCoord q → ℝ, ContDiff ℝ (⊤ : ℕ∞) f →
    HasCompactSupport f → tsupport f ⊆ dualChamber q →
    Martingale (dualMartingale D0 q f N X Y) 𝓖 P

variable {p : ℕ}

/-- The front-padded flat state path. -/
def padPath {Ω : Type*} (p : ℕ) (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ) :
    ℝ≥0 → Ω → Fin (p + p) → ℝ :=
  fun t ω => padState p (N t ω) (X t ω) (Y t ω)

theorem measurable_padState_uncurry :
    Measurable fun z : (ℕ → ℝ) × (ℕ → ℝ) × ℕ => padState p z.2.2 z.1 z.2.1 := by
  have e : (fun z : (ℕ → ℝ) × (ℕ → ℝ) × ℕ => padState p z.2.2 z.1 z.2.1) =
      (fun w : ((ℕ → ℝ) × (ℕ → ℝ)) × ℕ => padState p w.2 w.1.1 w.1.2) ∘
        (fun z => ((z.1, z.2.1), z.2.2)) := rfl
  rw [e]
  refine Measurable.comp (measurable_from_prod_countable_left fun n => ?_)
    ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd)
  refine measurable_pi_iff.2 fun k => ?_
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k
  · simp only [padState, Fin.append_left, padX]
    split_ifs
    · exact (measurable_pi_apply _).comp measurable_fst
    · exact measurable_const
  · simp only [padState, Fin.append_right, padX]
    split_ifs
    · exact (measurable_pi_apply _).comp measurable_snd
    · exact measurable_const

section Path

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω}
  {𝓖 : Filtration ℝ≥0 m} {D0 : ℝ} {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}

theorem IsDualFrom.continuous_padPath (h : IsDualFrom P 𝓖 D0 p N X Y) (ω : Ω) :
    Continuous fun t => padPath p N X Y t ω :=
  continuous_padState (h.paths ω) (h.bound ω)

theorem IsDualFrom.measurable_padPath (h : IsDualFrom P 𝓖 D0 p N X Y) (t : ℝ≥0) :
    Measurable[𝓖 t] (padPath p N X Y t) := by
  obtain ⟨hN, hX, hY⟩ := h.adapted t
  exact (measurable_padState_uncurry (p := p)).comp (hX.prodMk (hY.prodMk hN))

theorem IsDualFrom.level_le (h : IsDualFrom P 𝓖 D0 p N X Y) (t : ℝ≥0) (ω : Ω) :
    N t ω ≤ p :=
  ((h.paths ω).antitone zero_le).trans (h.bound ω)

theorem IsDualFrom.padPath_mem_iff (h : IsDualFrom P 𝓖 D0 p N X Y) (t : ℝ≥0) (ω : Ω) :
    padPath p N X Y t ω ∈ flatChamber p ↔ N t ω = p :=
  padState_mem_flatChamber_iff (h.level_le t ω) ((h.paths ω).chamber t)

/-- The exit time of `V` from the flat chamber is the first deletion time `σ_{p−1}`. -/
theorem IsDualFrom.exitTime_eq (h : IsDualFrom P 𝓖 D0 p N X Y) (hp : 1 ≤ p) (ω : Ω) :
    exitTimeFrom (flatChamber p) (padPath p N X Y) ω = entryTime (fun t => N t ω) (p - 1) := by
  have hc : ∀ t, padPath p N X Y t ω ∉ flatChamber p ↔ N t ω ≤ p - 1 := fun t => by
    rw [h.padPath_mem_iff]
    have hle := h.level_le t ω
    exact ⟨fun h1 => by omega, fun h1 h2 => by omega⟩
  simp only [exitTimeFrom, entryTime, hc]

end Path

/-!
## The level-`p` test martingale problem
-/

/-- `DualCoord p ≃ₜ ℝ^{p+p}`. -/
def flatHomeo (p : ℕ) : DualCoord p ≃ₜ (Fin (p + p) → ℝ) where
  toFun z := Fin.append z.1 z.2
  invFun w := ofFlat p w
  left_inv z := Prod.ext (funext fun i => Fin.append_left _ _ i)
    (funext fun j => Fin.append_right _ _ j)
  right_inv w := Fin.append_castAdd_natAdd
  continuous_toFun := by
    refine continuous_pi fun k => Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simp only [Fin.append_left]; exact (continuous_apply i).comp continuous_fst
    · simp only [Fin.append_right]; exact (continuous_apply j).comp continuous_snd
  continuous_invFun := (ofFlat p).continuous

theorem contDiff_flatHomeo : ContDiff ℝ (⊤ : ℕ∞) (flatHomeo p) := by
  refine contDiff_pi.2 fun k => Fin.addCases (fun i => ?_) (fun j => ?_) k
  · show ContDiff ℝ _ fun z : DualCoord p => Fin.append z.1 z.2 (Fin.castAdd p i)
    simp only [Fin.append_left]; exact (contDiff_apply ℝ ℝ i).comp contDiff_fst
  · show ContDiff ℝ _ fun z : DualCoord p => Fin.append z.1 z.2 (Fin.natAdd p j)
    simp only [Fin.append_right]; exact (contDiff_apply ℝ ℝ j).comp contDiff_snd

theorem flatHomeo_dualCoordOf (x y : ℕ → ℝ) :
    flatHomeo p (dualCoordOf p x y) = padState p p x y := by
  show Fin.append _ _ = Fin.append _ _
  rw [padX_self, padX_self]; rfl

theorem mpGenerator_eq_zero_of_notMem {d : ℕ} (b : (Fin d → ℝ) → Fin d → ℝ)
    (a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ) {φ : (Fin d → ℝ) → ℝ} {w : Fin d → ℝ}
    (hw : w ∉ tsupport φ) : mpGenerator b a φ w = 0 := by
  have h1 : fderiv ℝ φ w = 0 := Function.notMem_support.1 fun h => hw (support_fderiv_subset ℝ h)
  have h2 : fderiv ℝ (fderiv ℝ φ) w = 0 := Function.notMem_support.1 fun h =>
    hw (tsupport_fderiv_subset ℝ (support_fderiv_subset ℝ h))
  simp [mpGenerator, h1, h2]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {D0 : ℝ}
  {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}

/-- Pathwise, the flat test martingale of `V` is the level-`p` martingale of `IsDualFrom`. -/
theorem testMart_padPath_eq (h : IsDualFrom P 𝓖 D0 p N X Y) {φ : (Fin (p + p) → ℝ) → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφs : tsupport φ ⊆ flatChamber p) {ω : Ω} (h0 : N 0 ω = p)
    (t : ℝ≥0) :
    testMart (flatDrift D0 p) (flatDiff D0 p) φ (padPath p N X Y) t ω =
      dualMartingale D0 p (φ ∘ flatHomeo p) N X Y t ω := by
  have hf : ContDiff ℝ 2 (φ ∘ flatHomeo p) := hφ.comp (contDiff_flatHomeo.of_le (by simp))
  have hval : ∀ s, φ (padPath p N X Y s ω) = dualLift (φ ∘ flatHomeo p) (N s ω) (X s ω) (Y s ω) :=
    fun s => by
      by_cases hs : N s ω = p
      · simp only [dualLift, hs, ↓reduceIte, Function.comp_apply, flatHomeo_dualCoordOf,
          padPath]
      · have hnot : padPath p N X Y s ω ∉ flatChamber p := fun hm => hs ((h.padPath_mem_iff s ω).1 hm)
        simp only [dualLift, hs, ↓reduceIte]
        exact image_eq_zero_of_notMem_tsupport fun hm => hnot (hφs hm)
  have hgen : ∀ s, mpGenerator (flatDrift D0 p) (flatDiff D0 p) φ (padPath p N X Y s ω) =
      dualLift (dualGenerator D0 (φ ∘ flatHomeo p)) (N s ω) (X s ω) (Y s ω) := fun s => by
    by_cases hs : N s ω = p
    · simp only [dualLift, hs, ↓reduceIte]
      have e : φ = (φ ∘ flatHomeo p) ∘ ofFlat p := by
        funext w; exact (congrArg φ ((flatHomeo p).apply_symm_apply w)).symm
      have := mpGenerator_flat D0 hf (padPath p N X Y s ω)
      rw [← e] at this
      rw [this]
      simp only [padPath, hs, ofFlat_padState_self]
    · have hnot : padPath p N X Y s ω ∉ flatChamber p := fun hm => hs ((h.padPath_mem_iff s ω).1 hm)
      simp only [dualLift, hs, ↓reduceIte]
      exact mpGenerator_eq_zero_of_notMem _ _ fun hm => hnot (hφs hm)
  simp only [testMart, dualMartingale, hval, hgen]
  rw [dualEntranceValue_of_start _ t ω h0]
  simp only [dualLift, h0, ↓reduceIte]

/-- **`V` solves the level-`p` test martingale problem** in the flat chamber. -/
theorem isTestMPSolution_padPath (h : IsDualFrom P 𝓖 D0 p N X Y) (hp : 1 ≤ p) :
    IsTestMPSolution P 𝓖 (flatDrift D0 p) (flatDiff D0 p) (flatChamber p) (padPath p N X Y) where
  adapted t := (h.measurable_padPath t).stronglyMeasurable
  continuous := Eventually.of_forall h.continuous_padPath
  mart φ hφ hφc hφs := by
    have hsub : tsupport (φ ∘ flatHomeo p) ⊆ dualChamber p := by
      refine closure_minimal (fun z hz => ?_) ((isClosed_tsupport φ).preimage
        (flatHomeo p).continuous |>.preimage continuous_id) |>.trans ?_
      · exact subset_tsupport φ hz
      · intro z hz
        have : (flatHomeo p).symm (flatHomeo p z) ∈ dualChamber p := hφs hz
        rwa [Homeomorph.symm_apply_apply] at this
    refine ⟨_, h.martingale p hp le_rfl (φ ∘ flatHomeo p)
      (hφ.comp contDiff_flatHomeo) (hφc.comp_homeomorph (flatHomeo p)) hsub, fun t => ?_⟩
    filter_upwards [h.start] with ω hω
    exact (testMart_padPath_eq h (hφ.of_le (by simp)) hφs hω t).symm

theorem isMPSolutionOn_mono {d : ℕ} {b : (Fin d → ℝ) → Fin d → ℝ}
    {a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ} {U W : Set (Fin d → ℝ)} {Z : ℝ≥0 → Ω → Fin d → ℝ}
    (hZ : IsMPSolutionOn P 𝓖 b a U Z) (hWU : W ⊆ U) : IsMPSolutionOn P 𝓖 b a W Z where
  adapted := hZ.adapted
  continuous := hZ.continuous
  drift W' hW' := hZ.drift W' ⟨hW'.1, hW'.2.1, hW'.2.2.trans hWU⟩
  bracket W' hW' := hZ.bracket W' ⟨hW'.1, hW'.2.1, hW'.2.2.trans hWU⟩

theorem IsDualFrom.isMPSolutionOn (h : IsDualFrom P 𝓖 D0 p N X Y) (hp : 1 ≤ p) :
    IsMPSolutionOn P 𝓖 (flatDrift D0 p) (flatDiff D0 p) (flatChamber p) (padPath p N X Y) :=
  have := h.prob
  isMPSolutionOn_of_test (isOpen_flatChamber p) (continuousOn_flatDrift D0)
    (contDiffOn_flatDiff D0).continuousOn (fun w _ i j => flatDiff_symm D0 w i j)
    (isTestMPSolution_padPath h hp)

end BlockBand.Transmission.Dual
