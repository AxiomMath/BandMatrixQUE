module

public import BlockBand.SourceProcess.FullSourceGenerator.GenBounds

/-!
# The tested increment along the path at fixed `W`

`tested_le`: at fixed `W`, the increment of `Φ - Σ_j W⁻¹𝒜Φ` over a window `[j₀, j₁]`, tested
against a square-integrable `𝓕_{j₀}`-measurable `ξ` bounded on the survival event, is bounded by
the summed drift and carré du champ errors (`driftSum`, `carreSum`), the probability of the stop
event and the fourth moment of `ξ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceGenerator

open MeasureTheory MvPolynomial Finset
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers
open BlockBand.SourceProcess.FullSourceStops
open scoped ENNReal

variable {W nT nI : ℕ}

/-- The window sum of the first `EarlySummed` integrand. -/
def driftSum (b E : ℝ) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (K ε : ℝ) (W : ℕ)
    (Φ : TracePoly nT nI) (j₀ j₁ : ℕ) : ℝ≥0∞ :=
  ∑ j ∈ Ico j₀ j₁, ∫⁻ ω, ‖(alive b E k q K ε W j).indicator (fun ω =>
    (growthPathLaw W b)[(alive b E k q K ε W j).indicator (fun ω =>
      polyValue b E k q W (j + 1) ω Φ - polyValue b E k q W j ω Φ) | growthSigma W j] ω -
    (W : ℂ)⁻¹ * polyValue b E k q W j ω
      (wordGenerator b E q (((j + 1 : ℕ) : ℝ) / W) Φ)) ω‖ₑ ∂growthPathLaw W b

/-- The window sum of the second `EarlySummed` integrand. -/
def carreSum (b E : ℝ) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (K ε : ℝ) (W : ℕ)
    (Φ : TracePoly nT nI) (j₀ j₁ : ℕ) : ℝ≥0∞ :=
  ∑ j ∈ Ico j₀ j₁, ∫⁻ ω, ‖(alive b E k q K ε W j).indicator (fun ω =>
    (growthPathLaw W b)[(alive b E k q K ε W j).indicator (fun ω =>
      (polyValue b E k q W (j + 1) ω Φ - polyValue b E k q W j ω Φ) ^ 2) | growthSigma W j] ω -
    (W : ℂ)⁻¹ * polyValue b E k q W j ω (wordCarre b E Φ)) ω‖ₑ ∂growthPathLaw W b

/-- The stop event on `[εW, TW]`. -/
def stopEvent (b E : ℝ) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (K ε T : ℝ) (W : ℕ) :
    Set (GrowthPath W) :=
  {ω | ∃ j : ℕ, ε * W ≤ j ∧ (j : ℝ) ≤ T * W ∧ K < traceLoad b E k q W j ω}

theorem measurableSet_stopEvent (b E : ℝ) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (K ε T : ℝ) :
    MeasurableSet (stopEvent b E k q K ε T W) := by
  have e : stopEvent b E k q K ε T W = ⋃ j : ℕ, {ω | ε * W ≤ j ∧ (j : ℝ) ≤ T * W ∧
      K < traceLoad b E k q W j ω} := by ext ω; simp [stopEvent]
  rw [e]
  refine MeasurableSet.iUnion fun j => ?_
  by_cases h : ε * W ≤ j ∧ (j : ℝ) ≤ T * W
  · have : {ω : GrowthPath W | ε * W ≤ j ∧ (j : ℝ) ≤ T * W ∧ K < traceLoad b E k q W j ω} =
        {ω | K < traceLoad b E k q W j ω} := by ext ω; simp [h.1, h.2]
    rw [this]
    exact measurableSet_lt measurable_const
      ((ContractingWords.measurable_traceLoad_past b E k q le_rfl).mono (growthSigma_le' W j) le_rfl)
  · have : {ω : GrowthPath W | ε * W ≤ j ∧ (j : ℝ) ≤ T * W ∧ K < traceLoad b E k q W j ω} = ∅ := by
      ext ω; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h' => h ⟨h'.1, h'.2.1⟩
    rw [this]; exact MeasurableSet.empty

theorem alive_anti {b E : ℝ} {k : Fin nT → ℕ} {q : Fin nI → ℝ → ℝ} {K ε : ℝ} {i j : ℕ}
    (h : i ≤ j) : alive b E k q K ε W j ⊆ alive b E k q K ε W i := fun _ hω => by
  simp only [alive, Set.mem_ofPred_eq] at hω ⊢
  exact lt_of_le_of_lt (Nat.cast_le.mpr h) hω

theorem norm_inv_natCast_sq_mul_le {n : ℕ} {T : ℝ} (hW : 1 ≤ W) (hn : (n : ℝ) ≤ T * W) :
    ‖(W : ℂ)⁻¹‖ ^ 2 * (n * n) ≤ T ^ 2 := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  rw [norm_inv, Complex.norm_natCast]
  have h1 : (n : ℝ) / W ≤ T := (div_le_iff₀ hW0).mpr hn
  have h0 : 0 ≤ (n : ℝ) / W := by positivity
  calc (W : ℝ)⁻¹ ^ 2 * (n * n) = ((n : ℝ) / W) ^ 2 := by field_simp
    _ ≤ T ^ 2 := pow_le_pow_left₀ h0 h1 2

/-- **The tested increment at fixed `W`.** -/
theorem tested_le {b E : ℝ} (hW : 1 ≤ W) {q : Fin nI → ℝ → ℝ} (hq : IsIntervalTests q) {t₀ : ℝ}
    (hq0 : ∀ a t, t₀ < t → q a t = 0) {Φ : TracePoly nT nI} (hΦ : IsOrdinaryPoly Φ)
    (k : Fin nT → ℕ) (K ε T : ℝ) {j₀ j₁ : ℕ} (hε₀ : ε * W ≤ j₀) (ht₀ : t₀ * W < j₀ + 1)
    (hj : j₀ ≤ j₁) (hj₁ : (j₁ : ℝ) ≤ T * W) {CX Cg CR CI : ℝ} (hCX : 0 ≤ CX) (hCg : 0 ≤ Cg)
    (hCR : 0 ≤ CR) (hCI : 0 ≤ CI)
    (hX : ∀ j : ℕ, ε * W ≤ j → (j : ℝ) ≤ T * W →
      ∫⁻ ω, ‖polyValue b E k q W j ω Φ‖ₑ ^ 2 ∂growthPathLaw W b ≤ ENNReal.ofReal CX)
    (hg : ∀ j : ℕ, ε * W ≤ j → (j : ℝ) ≤ T * W → ∫⁻ ω, ‖polyValue b E k q W j ω
      (wordGenerator b E q (t₀ + 1) Φ)‖ₑ ^ 2 ∂growthPathLaw W b ≤ ENNReal.ofReal Cg)
    (hR : ∀ j : ℕ, ε * W ≤ j → (j : ℝ) ≤ T * W → ∫⁻ ω, ‖polyValue b E k q W j ω
      (wordCarre b E (rePart Φ))‖ₑ ^ 1 ∂growthPathLaw W b ≤ ENNReal.ofReal CR)
    (hI : ∀ j : ℕ, ε * W ≤ j → (j : ℝ) ≤ T * W → ∫⁻ ω, ‖polyValue b E k q W j ω
      (wordCarre b E (imPart Φ))‖ₑ ^ 1 ∂growthPathLaw W b ≤ ENNReal.ofReal CI)
    {ξ : GrowthPath W → ℂ} (hξm : StronglyMeasurable[growthSigma W j₀] ξ)
    (hξ2 : MemLp ξ 2 (growthPathLaw W b)) {BK : ℝ} (hBK : 0 ≤ BK)
    (hξK : ∀ᵐ ω ∂growthPathLaw W b, ω ∈ alive b E k q K ε W j₀ → ‖ξ ω‖ ≤ BK)
    {lam kap : ℝ} (hl : 0 < lam) (hk : 0 < kap) :
    ‖∫ ω, ξ ω * (polyValue b E k q W j₁ ω Φ - polyValue b E k q W j₀ ω Φ -
      ∑ j ∈ Ico j₀ j₁, (W : ℂ)⁻¹ * polyValue b E k q W j ω (wordGenerator b E q (t₀ + 1) Φ))
        ∂growthPathLaw W b‖ₑ ≤
      ENNReal.ofReal BK * driftSum b E k q K ε W Φ j₀ j₁ +
      ENNReal.ofReal lam * (ENNReal.ofReal (6 * CX + 3 * (T ^ 2 * Cg)) +
        4 * (carreSum b E k q K ε W (rePart Φ) j₀ j₁ + carreSum b E k q K ε W (imPart Φ) j₀ j₁ +
          ENNReal.ofReal (T * (CR + CI)))) +
      ENNReal.ofReal (1 / (4 * lam * kap)) * growthPathLaw W b (stopEvent b E k q K ε T W) +
      ENNReal.ofReal (kap / (4 * lam)) * ∫⁻ ω, ‖ξ ω‖ₑ ^ 4 ∂growthPathLaw W b := by
  set μ := growthPathLaw W b
  set 𝒜 := wordGenerator b E q (t₀ + 1) Φ
  set A : ℕ → Set (GrowthPath W) := alive b E k q K ε W
  set Xc : ℕ → GrowthPath W → ℂ := fun j ω =>
    if j₀ ≤ j ∧ j ≤ j₁ then polyValue b E k q W j ω Φ else 0
  set gc : ℕ → GrowthPath W → ℂ := fun j ω =>
    if j₀ ≤ j ∧ j < j₁ then polyValue b E k q W j ω 𝒜 else 0
  have hwin : ∀ j : ℕ, j₀ ≤ j → j ≤ j₁ → ε * W ≤ j ∧ (j : ℝ) ≤ T * W := fun j h1 h2 =>
    ⟨hε₀.trans (Nat.cast_le.mpr h1), (Nat.cast_le.mpr h2).trans hj₁⟩
  have hGm : Monotone (growthSigma W) := fun _ _ h => FullSource.growthSigma_mono h
  have hle : ∀ j, growthSigma W j ≤ _ := fun j => growthSigma_le' W j
  have hpm : ∀ (j : ℕ) (Ψ : TracePoly nT nI),
      StronglyMeasurable[growthSigma W j] fun ω => polyValue b E k q W j ω Ψ := fun j Ψ =>
    (measurable_polyValue_past b E k q le_rfl Ψ).stronglyMeasurable
  have hXm : ∀ j, StronglyMeasurable[growthSigma W j] (Xc j) := by
    intro j; by_cases h : j₀ ≤ j ∧ j ≤ j₁
    · simp only [Xc, h, and_self, ↓reduceIte]; exact hpm j Φ
    · simp only [Xc, h, ↓reduceIte]; exact stronglyMeasurable_const
  have hgm : ∀ j, StronglyMeasurable[growthSigma W j] (gc j) := by
    intro j; by_cases h : j₀ ≤ j ∧ j < j₁
    · simp only [gc, h, and_self, ↓reduceIte]; exact hpm j 𝒜
    · simp only [gc, h, ↓reduceIte]; exact stronglyMeasurable_const
  have hX2 : ∀ j, MemLp (Xc j) 2 μ := by
    intro j; by_cases h : j₀ ≤ j ∧ j ≤ j₁
    · simp only [Xc, h, and_self, ↓reduceIte]
      exact memLp_two_of_lintegral ((hpm j Φ).mono (hle j)).aestronglyMeasurable
        (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hX j (hwin j h.1 h.2).1 (hwin j h.1 h.2).2))
    · simp only [Xc, h, ↓reduceIte]; exact memLp_const 0
  have hg2 : ∀ j, MemLp (gc j) 2 μ := by
    intro j; by_cases h : j₀ ≤ j ∧ j < j₁
    · simp only [gc, h, and_self, ↓reduceIte]
      have hw := hwin j h.1 h.2.le
      exact memLp_two_of_lintegral ((hpm j 𝒜).mono (hle j)).aestronglyMeasurable
        (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hg j hw.1 hw.2))
    · simp only [gc, h, ↓reduceIte]; exact memLp_const 0
  have hA : ∀ j, MeasurableSet[growthSigma W j] (A j) := fun j =>
    ContractingWords.measurableSet_alive b E k q K ε j
  have hB : ∀ ω, ω ∉ stopEvent b E k q K ε T W → ∀ j ∈ Ico j₀ j₁, ω ∈ A j := by
    intro ω hω j hjm
    exact mem_alive_of_notMem_stop hω ((Nat.cast_le.mpr (Finset.mem_Ico.mp hjm).2.le).trans hj₁)
  have key := norm_integral_tested_le (growthSigma W) Xc gc A ((W : ℂ)⁻¹) hGm hle hXm hX2 hA
    hgm hg2 hj (fun j hjm => alive_anti (Finset.mem_Ico.mp hjm).1)
    (measurableSet_stopEvent b E k q K ε T) hB hξm hξ2 hBK hξK hl hk
  -- identify the cut-off sequences on the window
  have hXc : ∀ j, j₀ ≤ j → j ≤ j₁ → Xc j = fun ω => polyValue b E k q W j ω Φ := fun j h1 h2 => by
    simp only [Xc, h1, h2, and_self, ↓reduceIte]
  have hgc : ∀ j ∈ Ico j₀ j₁, gc j = fun ω => polyValue b E k q W j ω 𝒜 := fun j hjm => by
    have h := Finset.mem_Ico.mp hjm
    simp only [gc, h, and_self, ↓reduceIte]
  have hInc : ∀ j ∈ Ico j₀ j₁, stopInc Xc A j = (A j).indicator (fun ω =>
      polyValue b E k q W (j + 1) ω Φ - polyValue b E k q W j ω Φ) := fun j hjm => by
    have h := Finset.mem_Ico.mp hjm
    simp only [stopInc, hXc (j + 1) (by omega) (by omega), hXc j h.1 h.2.le]
  have hM : ∀ ω, Xc j₁ ω - Xc j₀ ω - ∑ j ∈ Ico j₀ j₁, (W : ℂ)⁻¹ * gc j ω =
      polyValue b E k q W j₁ ω Φ - polyValue b E k q W j₀ ω Φ -
        ∑ j ∈ Ico j₀ j₁, (W : ℂ)⁻¹ * polyValue b E k q W j ω 𝒜 := fun ω => by
    rw [hXc j₁ hj le_rfl, hXc j₀ le_rfl hj]
    congr 1
    exact Finset.sum_congr rfl fun j hjm => by rw [hgc j hjm]
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hgen : ∀ j ∈ Ico j₀ j₁, wordGenerator b E q (((j + 1 : ℕ) : ℝ) / W) Φ = 𝒜 := by
    intro j hjm
    have h := Finset.mem_Ico.mp hjm
    have ht : t₀ < ((j + 1 : ℕ) : ℝ) / W := by
      rw [lt_div_iff₀ hW0]
      have : (j₀ : ℝ) + 1 ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ h.1
      linarith
    exact wordGenerator_congr_time b E q (fun a => by rw [hq0 a _ ht, hq0 a _ (by linarith)]) Φ
  have hn : ((Ico j₀ j₁).card : ℝ) ≤ T * W := by
    rw [Nat.card_Ico]
    exact (Nat.cast_le.mpr (Nat.sub_le j₁ j₀)).trans hj₁
  calc _ = ‖∫ ω, ξ ω * (Xc j₁ ω - Xc j₀ ω - ∑ j ∈ Ico j₀ j₁, (W : ℂ)⁻¹ * gc j ω) ∂μ‖ₑ := by
        simp_rw [hM]
    _ ≤ _ := key
    _ ≤ _ := by
      gcongr ENNReal.ofReal BK * ?_ + ENNReal.ofReal lam * (?_ + ?_) + _ + _
      · -- the drift errors
        refine le_of_eq (Finset.sum_congr rfl fun j hjm => ?_)
        simp only [stopErr, A]
        rw [hInc j hjm, hgc j hjm, hgen j hjm]
      · -- second moment of the tested increment
        have mX : ∀ j, AEMeasurable (Xc j) μ := fun j =>
          ((hXm j).mono (hle j)).measurable.aemeasurable
        have mg : ∀ j, AEMeasurable (gc j) μ := fun j =>
          ((hgm j).mono (hle j)).measurable.aemeasurable
        refine (lintegral_sq_incr_le (Ico j₀ j₁) ((W : ℂ)⁻¹) (mX j₁) (mX j₀) mg).trans ?_
        have e1 : ∫⁻ ω, ‖Xc j₁ ω‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal CX := by
          rw [hXc j₁ hj le_rfl]; exact hX j₁ (hwin j₁ hj le_rfl).1 (hwin j₁ hj le_rfl).2
        have e0 : ∫⁻ ω, ‖Xc j₀ ω‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal CX := by
          rw [hXc j₀ le_rfl hj]; exact hX j₀ (hwin j₀ le_rfl hj).1 (hwin j₀ le_rfl hj).2
        have eg : ∑ j ∈ Ico j₀ j₁, ∫⁻ ω, ‖gc j ω‖ₑ ^ 2 ∂μ ≤
            ENNReal.ofReal ((Ico j₀ j₁).card * Cg) := by
          refine (Finset.sum_le_sum (g := fun _ => ENNReal.ofReal Cg) fun j hjm => ?_).trans
            (le_of_eq ?_)
          · rw [hgc j hjm]
            have h := Finset.mem_Ico.mp hjm
            exact hg j (hwin j h.1 h.2.le).1 (hwin j h.1 h.2.le).2
          · rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
              ENNReal.ofReal_natCast]
        have hreal : ENNReal.ofReal (‖(W : ℂ)⁻¹‖ ^ 2 * (Ico j₀ j₁).card) *
            ENNReal.ofReal ((Ico j₀ j₁).card * Cg) ≤ ENNReal.ofReal (T ^ 2 * Cg) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have := norm_inv_natCast_sq_mul_le hW hn
          calc _ = ‖(W : ℂ)⁻¹‖ ^ 2 * (((Ico j₀ j₁).card : ℝ) * (Ico j₀ j₁).card) * Cg := by ring
            _ ≤ T ^ 2 * Cg := mul_le_mul_of_nonneg_right this hCg
        calc _ ≤ 3 * ENNReal.ofReal CX + 3 * ENNReal.ofReal CX +
              3 * (ENNReal.ofReal (‖(W : ℂ)⁻¹‖ ^ 2 * (Ico j₀ j₁).card) *
                ENNReal.ofReal ((Ico j₀ j₁).card * Cg)) := by
              rw [mul_assoc]; gcongr
          _ ≤ 3 * ENNReal.ofReal CX + 3 * ENNReal.ofReal CX + 3 * ENNReal.ofReal (T ^ 2 * Cg) := by
              gcongr
          _ = _ := by
              rw [show (6 : ℝ) * CX + 3 * (T ^ 2 * Cg) = 3 * CX + 3 * CX + 3 * (T ^ 2 * Cg) by ring,
                ENNReal.ofReal_add (by positivity) (by positivity),
                ENNReal.ofReal_add (by positivity) (by positivity)]
              simp only [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 3 by norm_num), ENNReal.ofReal_ofNat]
      · -- the martingale part, through `EarlySummed`'s second clause for `Re Φ`, `Im Φ`
        refine (lintegral_sq_mart_D_le (growthSigma W) Xc A hGm hle hXm hX2 hA j₀ j₁).trans ?_
        gcongr 4 * ?_
        have hpL : ∀ j : ℕ, j₀ ≤ j → j ≤ j₁ → MemLp (fun ω => polyValue b E k q W j ω Φ) 2 μ := by
          intro j h1 h2
          have h := hX2 j
          rwa [hXc j h1 h2] at h
        have hstep : ∀ j ∈ Ico j₀ j₁, ∫⁻ ω, ‖stopInc Xc A j ω‖ₑ ^ 2 ∂μ ≤
            (∫⁻ ω, ‖(A j).indicator (fun ω => μ[(A j).indicator (fun ω =>
              (polyValue b E k q W (j + 1) ω (rePart Φ) - polyValue b E k q W j ω (rePart Φ)) ^ 2) |
                growthSigma W j] ω - (W : ℂ)⁻¹ * polyValue b E k q W j ω (wordCarre b E (rePart Φ)))
                  ω‖ₑ ∂μ +
            ∫⁻ ω, ‖(A j).indicator (fun ω => μ[(A j).indicator (fun ω =>
              (polyValue b E k q W (j + 1) ω (imPart Φ) - polyValue b E k q W j ω (imPart Φ)) ^ 2) |
                growthSigma W j] ω - (W : ℂ)⁻¹ * polyValue b E k q W j ω (wordCarre b E (imPart Φ)))
                  ω‖ₑ ∂μ) +
            ENNReal.ofReal (W : ℝ)⁻¹ * (ENNReal.ofReal CR + ENNReal.ofReal CI) := by
          intro j hjm
          have h := Finset.mem_Ico.mp hjm
          have hw := hwin j h.1 h.2.le
          rw [hInc j hjm]
          refine (lintegral_sq_stopInc_le hq hΦ (A j) (hA j)
            ((hpL (j + 1) (by omega) (by omega)).sub (hpL j h.1 h.2.le))).trans ?_
          gcongr
          · simpa only [pow_one] using hR j hw.1 hw.2
          · simpa only [pow_one] using hI j hw.1 hw.2
        refine (Finset.sum_le_sum hstep).trans ?_
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
        gcongr ?_ + ?_ + ?_
        · exact le_rfl
        · exact le_rfl
        · rw [← ENNReal.ofReal_add hCR hCI, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (inv_nonneg.mpr hW0.le), ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [← mul_assoc]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [← div_eq_mul_inv, div_le_iff₀ hW0]; exact hn

end BlockBand.SourceProcess.FullSourceGenerator
