module
public import BlockBand.SourceProcess.Stochastic.SemimartingaleIto.InstHyp
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The localized Itô formula)

Under `LocData Q 𝓖 Y β α U W φ σ T c ys` and given martingale modifications of the
`σ`-stopped compensated coordinates and products of `Y`, the `σ`-stopped processes
`X_t = φ(t, Y_t) - φ(0, Y_0) - ∫_0^t itoDrift` and `X_t² - ∫_0^t itoBracket` have
`𝓖`-martingale modifications (`LocData.ito_local`).

Proof: the integral-bound Taylor scheme (`IHyp.exists_martingale_schemeProc'`) applied to the
augmented instance (`LocData.ihyp`) with the test functions `hAug φ` and `hAug φ · hAug φ`;
their generators are `0` and `1_{u ≤ σ} itoBracket` (`schemeGen_hAug`, `schemeGen_sq`,
`bracket_hAug`), and the scheme processes are the stopped targets on good paths.
-/

namespace BlockBand.SourceProcess.Stochastic.SemimartingaleIto
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.Internal.Contracts.Transmission
open scoped NNReal

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {d : ℕ}
  {Q : Measure Ω} {𝓖 : Filtration ℝ≥0 m₀}
  {Y β : ℝ≥0 → Ω → Fin d → ℝ} {α : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ}
  {U W : Set (Fin d → ℝ)} {φ : ℝ × (Fin d → ℝ) → ℝ} {σ : Ω → WithTop ℝ≥0} {T : ℝ≥0} {c : ℝ}
  {ys : Fin d → ℝ}

/-- The one-dimensional target process `φ(t, Y_t)`. -/
def itoY (φ : ℝ × (Fin d → ℝ) → ℝ) (Y : ℝ≥0 → Ω → Fin d → ℝ) : ℝ≥0 → Ω → Fin 1 → ℝ :=
  fun t ω _ => φ ((t : ℝ), Y t ω)

/-- Its drift. -/
def itoβ (φ : ℝ × (Fin d → ℝ) → ℝ) (Y β : ℝ≥0 → Ω → Fin d → ℝ)
    (α : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ) : ℝ≥0 → Ω → Fin 1 → ℝ :=
  fun t ω _ => itoDrift φ (Y t ω) t (β t ω) (α t ω)

/-- Its covariance. -/
def itoα (φ : ℝ × (Fin d → ℝ) → ℝ) (Y : ℝ≥0 → Ω → Fin d → ℝ)
    (α : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ) : ℝ≥0 → Ω → Matrix (Fin 1) (Fin 1) ℝ :=
  fun t ω => Matrix.of fun _ _ => itoBracket φ (Y t ω) t (α t ω)

theorem smCompensated_ito (t : ℝ≥0) (ω : Ω) :
    smCompensated (itoY φ Y) (itoβ φ Y β α) 0 t ω = φ ((t : ℝ), Y t ω) - φ (0, Y 0 ω) -
      ∫ v in Ioc (0 : ℝ) t, driftPath φ Y β α v.toNNReal ω := by
  simp [smCompensated, itoY, itoβ, driftPath]

theorem LocData.mem_W_of_le (D : LocData Q 𝓖 Y β α U W φ σ T c ys) {ω : Ω} {u : ℝ≥0}
    (hu : 0 < u) (h : (u : WithTop ℝ≥0) ≤ σ ω) : Y 0 ω ∈ W := by
  by_contra hG
  rw [D.off ω hG] at h
  exact absurd (WithTop.coe_le_coe.1 h) (not_le.2 hu)

section Path

variable (D : LocData Q 𝓖 Y β α U W φ σ T c ys) {ω : Ω} (hω : LGood Y β α U W σ c ω)
include D hω

theorem LGood.augZ_mem (u : ℝ≥0) : augZ φ Y β α σ W ys u ω ∈ augSet U := by
  classical
  refine ⟨mem_univ _, ?_⟩
  show (if Y 0 ω ∈ W then Y (stopTime (σ ω) u) ω else ys) ∈ U
  split_ifs with hG
  · exact D.hWU (hω.2.2.2.1 hG u)
  · exact D.hys

theorem LGood.schemeGen_hAug_eq {u : ℝ≥0} (hu : 0 < u) :
    schemeGen (hAug φ) (augZ φ Y β α σ W ys) (augβ φ Y β α σ) (augα α σ) u ω = 0 := by
  classical
  rw [schemeGen_hAug D.hU D.hφ _ _ _ (hω.augZ_mem D u) rfl rfl]
  by_cases h : (u : WithTop ℝ≥0) ≤ σ ω
  · have hG := D.mem_W_of_le hu h
    have e : projL d (augZ φ Y β α σ W ys u ω) = ((u : ℝ), Y u ω) := by
      show ((stopTime (σ ω) u : ℝ), if Y 0 ω ∈ W then Y (stopTime (σ ω) u) ω else ys) = _
      simp only [hG, ↓reduceIte, stopTime_eq_of_le h]
    rw [e]
    simp only [switchAfter_of_le h, matF, driftPath, itoDrift, one_mul]
    ring
  · simp [switchAfter_of_not_le h, matF]

theorem LGood.schemeGen_sq_eq {u : ℝ≥0} (hu : 0 < u) :
    schemeGen (fun y => hAug φ y * hAug φ y) (augZ φ Y β α σ W ys) (augβ φ Y β α σ)
      (augα α σ) u ω = switchAfter σ (bracketPath φ Y α) u ω := by
  classical
  rw [schemeGen_sq (isOpen_augSet D.hU) (contDiffOn_hAug D.hφ) _ _ _ (hω.augZ_mem D u),
    hω.schemeGen_hAug_eq D hu, mul_zero, zero_add]
  show ∑ k, ∑ l, embA (matF (switchAfter σ α) u ω) k l * _ * _ = _
  rw [bracket_hAug D.hU D.hφ (hω.augZ_mem D u)]
  by_cases h : (u : WithTop ℝ≥0) ≤ σ ω
  · have hG := D.mem_W_of_le hu h
    have e : projL d (augZ φ Y β α σ W ys u ω) = ((u : ℝ), Y u ω) := by
      show ((stopTime (σ ω) u : ℝ), if Y 0 ω ∈ W then Y (stopTime (σ ω) u) ω else ys) = _
      simp only [hG, ↓reduceIte, stopTime_eq_of_le h]
    rw [e]
    simp only [matF, switchAfter_of_le h]
    rfl
  · simp [switchAfter_of_not_le h, matF]

theorem LGood.integral_schemeGen_hAug (t : ℝ≥0) :
    ∫ v in Ioc (0 : ℝ) t, schemeGen (hAug φ) (augZ φ Y β α σ W ys) (augβ φ Y β α σ)
      (augα α σ) v.toNNReal ω = 0 := by
  rw [setIntegral_congr_fun measurableSet_Ioc fun v hv =>
    hω.schemeGen_hAug_eq D (Real.toNNReal_pos.2 hv.1)]
  simp

theorem LGood.integral_schemeGen_sq (t : ℝ≥0) :
    ∫ v in Ioc (0 : ℝ) t, schemeGen (fun y => hAug φ y * hAug φ y) (augZ φ Y β α σ W ys)
      (augβ φ Y β α σ) (augα α σ) v.toNNReal ω =
        ∫ v in Ioc (0 : ℝ) (stopTime (σ ω) t), bracketPath φ Y α v.toNNReal ω := by
  rw [setIntegral_congr_fun measurableSet_Ioc fun v hv =>
    hω.schemeGen_sq_eq D (Real.toNNReal_pos.2 hv.1), integral_switch_path]

omit hω in
/-- `hAug φ (Z_t) - hAug φ (Z_0)` is the stopped target; `hAug φ (Z_0) = 0` on the window. -/
theorem LocData.hAug_augZ (t : ℝ≥0) :
    hAug φ (augZ φ Y β α σ W ys t ω) - hAug φ (augZ φ Y β α σ W ys 0 ω) =
      stoppedProcess (smCompensated (itoY φ Y) (itoβ φ Y β α) 0) σ t ω ∧
    (Y 0 ω ∈ W → hAug φ (augZ φ Y β α σ W ys 0 ω) = 0) ∧
    (Y 0 ω ∉ W → hAug φ (augZ φ Y β α σ W ys t ω) = hAug φ (augZ φ Y β α σ W ys 0 ω)) := by
  classical
  have e : ∀ s, hAug φ (augZ φ Y β α σ W ys s ω) =
      φ ((stopTime (σ ω) s : ℝ), if Y 0 ω ∈ W then Y (stopTime (σ ω) s) ω else ys) -
        ((if Y 0 ω ∈ W then φ (0, Y 0 ω) else 0) +
          ∫ v in Ioc (0 : ℝ) (stopTime (σ ω) s), driftPath φ Y β α v.toNNReal ω) := by
    intro s
    show φ _ - augA φ Y β α σ W s ω = _
    unfold augA
    rw [integral_switch_path]
    rfl
  rw [stoppedProcess_eq_stopTime, smCompensated_ito, e, e]
  simp only [stopTime_zero', NNReal.coe_zero, Ioc_self, Measure.restrict_empty,
    integral_zero_measure, add_zero]
  by_cases hG : Y 0 ω ∈ W
  · refine ⟨?_, fun _ => ?_, fun h => absurd hG h⟩
    · simp only [hG, ↓reduceIte]; ring
    · simp only [hG, ↓reduceIte]; ring
  · refine ⟨?_, fun h => absurd h hG, fun _ => ?_⟩
    · simp only [hG, ↓reduceIte, D.off ω hG, stopTime_of_eq_zero', NNReal.coe_zero, Ioc_self,
        Measure.restrict_empty, integral_zero_measure, add_zero]
      ring
    · simp [hG, D.off ω hG, stopTime_of_eq_zero']

end Path

variable [IsProbabilityMeasure Q]

/-- **The localized Itô formula.** -/
theorem LocData.ito_local (D : LocData Q 𝓖 Y β α U W φ σ T c ys)
    (hMN' : ∀ i, HasMartingaleModification Q 𝓖 (stoppedProcess (smCompensated Y β i) σ))
    (hMB' : ∀ i j, HasMartingaleModification Q 𝓖 (stoppedProcess (fun t ω =>
      smCompensated Y β i t ω * smCompensated Y β j t ω -
        ∫ s in Ioc (0 : ℝ) t, α s.toNNReal ω i j) σ)) :
    HasMartingaleModification Q 𝓖
        (stoppedProcess (smCompensated (itoY φ Y) (itoβ φ Y β α) 0) σ) ∧
      HasMartingaleModification Q 𝓖 (stoppedProcess (fun t ω =>
        smCompensated (itoY φ Y) (itoβ φ Y β α) 0 t ω *
          smCompensated (itoY φ Y) (itoβ φ Y β α) 0 t ω -
        ∫ s in Ioc (0 : ℝ) t, itoα φ Y α s.toNNReal ω 0 0) σ) := by
  choose MN hMN hMNeq using hMN'
  choose MB hMB hMBeq using hMB'
  obtain ⟨M, hM0, hM⟩ := D.bound
  have hc0 : ContinuousOn (fun y => φ (0, y)) (closure W) :=
    D.hφ.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      fun y hy => ⟨mem_univ _, D.hWU hy⟩
  obtain ⟨M₀', hM₀'⟩ := D.hWc.exists_bound_of_continuousOn hc0
  have hM₀ : ∀ y ∈ closure W, |φ (0, y)| ≤ max M₀' 0 := fun y hy =>
    (le_of_eq (Real.norm_eq_abs _).symm).trans ((hM₀' y hy).trans (le_max_left _ _))
  have H := D.ihyp hM0 hM (le_max_right _ _) hM₀ hMN hMNeq hMB hMBeq
  have hK := augK_subset (T := T) (L := max M₀' 0 + M * (T + c)) D.hWU D.hys
  have hO := isOpen_augSet (d := d) D.hU
  have hh := contDiffOn_hAug D.hφ
  obtain ⟨M1, hM1, hM1eq⟩ := H.exists_martingale_schemeProc' hO hK hh
  obtain ⟨M2, hM2, hM2eq⟩ := H.exists_martingale_schemeProc' hO hK (hh.mul hh)
  refine ⟨⟨M1, hM1, fun t => (hM1eq t).trans ?_⟩, ⟨M2, hM2, fun t => (hM2eq t).trans ?_⟩⟩
  · filter_upwards [D.ae_good] with ω hω
    rw [schemeProc, hω.integral_schemeGen_hAug D t, sub_zero]
    exact (D.hAug_augZ (ω := ω) t).1
  · filter_upwards [D.ae_good] with ω hω
    rw [schemeProc, hω.integral_schemeGen_sq D t]
    obtain ⟨h1, h2, h3⟩ := D.hAug_augZ (ω := ω) t
    rw [stoppedProcess_eq_stopTime]
    rw [stoppedProcess_eq_stopTime] at h1
    have hI : ∫ s in Ioc (0 : ℝ) (stopTime (σ ω) t), itoα φ Y α s.toNNReal ω 0 0 =
        ∫ v in Ioc (0 : ℝ) (stopTime (σ ω) t), bracketPath φ Y α v.toNNReal ω := rfl
    rw [hI, ← h1]
    by_cases hG : Y 0 ω ∈ W
    · rw [h2 hG]; ring
    · have h0 : stopTime (σ ω) t = 0 := by rw [D.off ω hG, stopTime_of_eq_zero']
      rw [h3 hG, h0]
      simp

end BlockBand.SourceProcess.Stochastic.SemimartingaleIto
