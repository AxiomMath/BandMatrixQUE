module

public import BlockBand.SourceProcess.PhysApprox.B3MartMax

/-!
# `KUnclosedMax` reduced to two per-step estimates

Target: `KUnclosedMax`, `E ⨆_{n_s ≤ j < ⌊WT⌋}|(𝒦_{j+1})_{ij}|⁴ ≤ C` along the
path, no stop. With the unclosed step `Z_i = (𝒦_{i+1} − 𝒦_i)_{ij}` (`kUncStep`), its mean
`e_i = E[Z_i | b3Sigma i]` (`kUncMean`) and the telescoping
`𝒦_{j+1} = 𝒦_{n_s} + Σ_{n_s ≤ i ≤ j} Z_i`:

* the start `𝒦_{n_s}`: fixed length, `RawTagMoments` (`lintegral_kUnclosed_le`);
* the centred non-birth sum: Doob + crude Burkholder (`lintegral_runMax_martSum_le`), from the
  **per-step estimate `KUncStepFour`** (`W Σ_{non-birth} E|Z_i|⁴ ≤ C`; centred `L^p` size
  `C_p/√W`, so `E|Z_i|⁴ = O(W⁻²)` and the `≤ TW` steps give `O(W⁻¹)`); the `W` cancels as in
  `targetMartMax_holds`. Adaptedness: `Z_i` is `b3Sigma (i + 1)`-measurable
  (`measurable_kUncStep_past`, no a.e. issue: no alive set);
* the summed means: **the estimate `KUncMeanSum`** (mean `C(δ₀ + W⁻¹)`, Minkowski);
* the births: from `RawTagMoments` (`kUncBirthSum_of_raw`): at most `np` birth steps,
  each with fixed-length fourth moments.

**`kUnclosedMax_of_parts`**: `RawTagMoments + KUncStepFour + KUncMeanSum ⇒
KUnclosedMax`; `kUnclosedMax_of_baseContracts` with `RawTag.rawTagMoments_holds`.

The two estimates are hypotheses here: they need the identification of `E[Z_i | b3Sigma i]` with
the fresh-layer mean `a*(E_FΔ_i)c` (Fubini over the fresh layer, independent of the past, the
probes and the phase), then `RawTag.delta_fresh_bounds` with `‖δ₀‖_{16m} ≤ C/W` and the
`L^{16m}` frame bounds, in the masses of `tagForm_eq_rawForm`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.ComplexSourceLaw
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open scoped NNReal ENNReal

variable {W np : ℕ}

/-!
## The unclosed steps
-/

/-- The unclosed step `Z_i = (𝒦_{i+1} − 𝒦_i)_{ij}` on the closed sample space. -/
def kUncStep (b E : ℝ) (τ m : Fin np → ℝ) (W i : ℕ) (ij : Fin np × Fin np)
    (y : ProbedPath W np × ℝ) : ℂ :=
  complexSourceK b E W (i + 1) τ m y.1 ij.1 ij.2 - complexSourceK b E W i τ m y.1 ij.1 ij.2

/-- Its conditional mean `e_i = E[Z_i | b3Sigma i]` under `closedLaw`. -/
def kUncMean (b E : ℝ) (τ m : Fin np → ℝ) (W i : ℕ) (ij : Fin np × Fin np) :
    ProbedPath W np × ℝ → ℂ :=
  (closedLaw b W np)[kUncStep b E τ m W i ij | b3Sigma W i np]

theorem measurable_kUncStep (b E : ℝ) (τ m : Fin np → ℝ) (W i : ℕ) (ij : Fin np × Fin np) :
    Measurable (kUncStep b E τ m W i ij) :=
  (((measurable_complexSourceK b E W (i + 1) τ m).eval_matrix).comp measurable_fst).sub
    (((measurable_complexSourceK b E W i τ m).eval_matrix).comp measurable_fst)

theorem measurable_kUncMean (b E : ℝ) (τ m : Fin np → ℝ) (W i : ℕ) (ij : Fin np × Fin np) :
    Measurable (kUncMean b E τ m W i ij) :=
  (stronglyMeasurable_condExp.mono (b3Sigma_le i)).measurable

theorem complexSourceK_b3Ext (b E : ℝ) (τ m : Fin np → ℝ) {n j : ℕ} (hnj : n ≤ j)
    (y : ProbedPath W np × ℝ) :
    complexSourceK b E W n τ m (b3Ext W j y).1 = complexSourceK b E W n τ m y.1 := by
  simp only [b3Ext, complexSourceK, fullInverse_b3Ext hnj]

/-- **Adaptedness of the unclosed step**: `Z_i` is `b3Sigma (i + 1)`-measurable. -/
theorem measurable_kUncStep_past (b E : ℝ) (τ m : Fin np → ℝ) (W i : ℕ)
    (ij : Fin np × Fin np) : Measurable[b3Sigma W (i + 1) np] (kUncStep b E τ m W i ij) :=
  measurable_b3Sigma_of_inv (measurable_kUncStep b E τ m W i ij) fun y => by
    simp only [kUncStep, complexSourceK_b3Ext b E τ m le_rfl y,
      complexSourceK_b3Ext b E τ m (Nat.le_succ i) y]

/-!
## The estimates
-/

/-- **`KUncStepFour`** (centred `L^p` size `C_p/√W` of the
raw-form increment at `p = 4`): `W` times the summed fourth moments of the unclosed non-birth
steps is bounded. The unclosed analogue of `KStopStepFour` (no stop). -/
def KUncStepFour : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T : ℝ), ComplexSourceLawDomain b E τ m T → ∀ s : ℝ,
    ∃ C : ℝ, ∀ᶠ W in atTop, ∀ ij : Fin np × Fin np,
      ((W : ℕ) : ℝ≥0∞) * ∑ i ∈ (Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊).filter
          (fun i => ¬ IsBirthStep τ W i), ∫⁻ y, ‖kUncStep b E τ m W i ij y‖ₑ ^ 4 ∂closedLaw b W np
        ≤ ENNReal.ofReal C

/-- **`KUncMeanSum`** (mean `C(δ₀ + W⁻¹)`, "Hölder and Minkowski
control the means"): the fourth moment of the summed conditional means of the unclosed non-birth
steps is bounded. The unclosed analogue of `KStopMeanSum`. -/
def KUncMeanSum : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T : ℝ), ComplexSourceLawDomain b E τ m T → ∀ s : ℝ,
    ∃ C : ℝ, ∀ᶠ W in atTop, ∀ ij : Fin np × Fin np,
      ∫⁻ y, (∑ i ∈ (Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊).filter
          (fun i => ¬ IsBirthStep τ W i), ‖kUncMean b E τ m W i ij y‖ₑ) ^ 4 ∂closedLaw b W np
        ≤ ENNReal.ofReal C

/-!
## The births from the fixed-length moments
-/

theorem sum_pow_four_le {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) :
    (∑ i ∈ s, f i) ^ 4 ≤ (s.card : ℝ≥0∞) ^ 3 * ∑ i ∈ s, f i ^ 4 := by
  have h := ENNReal.rpow_sum_le_const_mul_sum_rpow (s := s) (f := f) (p := 4) (by norm_num)
  have e : ∀ x : ℝ≥0∞, x ^ (4 : ℝ) = x ^ (4 : ℕ) := fun x => by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  simp only [e] at h
  rwa [show (4 : ℝ) - 1 = ((3 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast] at h

theorem card_birth_le (τ : Fin np → ℝ) (W a N : ℕ) :
    ((Finset.Ico a N).filter (fun i => IsBirthStep τ W i)).card ≤ np := by
  calc ((Finset.Ico a N).filter (fun i => IsBirthStep τ W i)).card
      ≤ (Finset.univ.image fun k : Fin np => ⌊(W : ℝ) * τ k⌋₊).card := by
        refine Finset.card_le_card fun i hi => ?_
        obtain ⟨k, hk⟩ := (Finset.mem_filter.1 hi).2
        exact Finset.mem_image.2 ⟨k, Finset.mem_univ _, hk⟩
    _ ≤ (Finset.univ : Finset (Fin np)).card := Finset.card_image_le
    _ = np := by rw [Finset.card_univ, Fintype.card_fin]

/-- **The summed birth steps of the unclosed `𝒦`** have bounded fourth moment (from
`RawTagMoments`): at most `np` birth steps, `E|Z_i|⁴ ≤ 8(E|𝒦_{i+1}|⁴ + E|𝒦_i|⁴)`. -/
theorem kUncBirthSum_of_raw (hR : RawTagMoments) :
    ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T : ℝ), ComplexSourceLawDomain b E τ m T → ∀ s : ℝ,
      ∃ C : ℝ, ∀ᶠ W in atTop, ∀ ij : Fin np × Fin np,
        ∫⁻ y, (∑ i ∈ (Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊).filter
            (fun i => IsBirthStep τ W i), ‖kUncStep b E τ m W i ij y‖ₑ) ^ 4 ∂closedLaw b W np
          ≤ ENNReal.ofReal C := by
  intro b E np τ m T hD s
  obtain ⟨C₀, W₀, hC₀⟩ := lintegral_kUnclosed_le hR hD
  refine ⟨(np : ℝ) ^ 3 * (np * (16 * max C₀ 0)), ?_⟩
  filter_upwards [eventually_ge_atTop W₀] with W hW0 ij
  set B := (Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊).filter (fun i => IsBirthStep τ W i)
  set μ := closedLaw b W np
  have hcard := card_birth_le τ W (closeLen s W) ⌊(W : ℝ) * T⌋₊
  have hstep : ∀ i ∈ B, ∫⁻ y, ‖kUncStep b E τ m W i ij y‖ₑ ^ 4 ∂μ ≤
      16 * ENNReal.ofReal (max C₀ 0) := by
    intro i hi
    have hi2 := (Finset.mem_Ico.1 (Finset.mem_filter.1 hi).1).2
    have hn1 := succ_le_mul_of_lt_floor hi2
    have hn0 : (i : ℝ) ≤ T * W := le_trans (by push_cast; linarith) hn1
    have e1 := (hC₀ W hW0 (i + 1) hn1 ij).trans (ENNReal.ofReal_le_ofReal (le_max_left C₀ 0))
    have e0 := (hC₀ W hW0 i hn0 ij).trans (ENNReal.ofReal_le_ofReal (le_max_left C₀ 0))
    have hm : Measurable fun y : ProbedPath W np × ℝ =>
        ‖complexSourceK b E W (i + 1) τ m y.1 ij.1 ij.2‖ₑ ^ 4 :=
      (measurable_enorm_complexSourceK_pow b E (i + 1) τ m ij.1 ij.2).comp measurable_fst
    calc ∫⁻ y, ‖kUncStep b E τ m W i ij y‖ₑ ^ 4 ∂μ
        ≤ ∫⁻ y, 8 * (‖complexSourceK b E W (i + 1) τ m y.1 ij.1 ij.2‖ₑ ^ 4 +
            ‖complexSourceK b E W i τ m y.1 ij.1 ij.2‖ₑ ^ 4) ∂μ :=
          lintegral_mono fun y => (pow_le_pow_left₀ zero_le enorm_sub_le 4).trans
            (add_pow_four_le _ _)
      _ = 8 * (∫⁻ y, ‖complexSourceK b E W (i + 1) τ m y.1 ij.1 ij.2‖ₑ ^ 4 ∂μ +
            ∫⁻ y, ‖complexSourceK b E W i τ m y.1 ij.1 ij.2‖ₑ ^ 4 ∂μ) := by
          rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_left hm]
      _ ≤ 8 * (ENNReal.ofReal (max C₀ 0) + ENNReal.ofReal (max C₀ 0)) := by gcongr
      _ = 16 * ENNReal.ofReal (max C₀ 0) := by ring
  calc ∫⁻ y, (∑ i ∈ B, ‖kUncStep b E τ m W i ij y‖ₑ) ^ 4 ∂μ
      ≤ ∫⁻ y, (B.card : ℝ≥0∞) ^ 3 * ∑ i ∈ B, ‖kUncStep b E τ m W i ij y‖ₑ ^ 4 ∂μ :=
        lintegral_mono fun y => sum_pow_four_le B _
    _ = (B.card : ℝ≥0∞) ^ 3 * ∑ i ∈ B, ∫⁻ y, ‖kUncStep b E τ m W i ij y‖ₑ ^ 4 ∂μ := by
        rw [lintegral_const_mul' _ _ (by simp), lintegral_finsetSum _ fun i _ =>
          (measurable_kUncStep b E τ m W i ij).enorm.pow_const 4]
    _ ≤ (np : ℝ≥0∞) ^ 3 * ∑ _i ∈ B, 16 * ENNReal.ofReal (max C₀ 0) := by
        gcongr with i hi
        exact hstep i hi
    _ ≤ (np : ℝ≥0∞) ^ 3 * ((np : ℝ≥0∞) * (16 * ENNReal.ofReal (max C₀ 0))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        gcongr
    _ = ENNReal.ofReal ((np : ℝ) ^ 3 * (np * (16 * max C₀ 0))) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow (by positivity),
          ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]

/-!
## The pointwise split
-/

theorem telescope_Ico (X : ℕ → ℂ) {a j : ℕ} (hj : a ≤ j) :
    X (j + 1) = X a + ∑ i ∈ Finset.Ico a (j + 1), (X (i + 1) - X i) := by
  induction j, hj using Nat.le_induction with
  | base => rw [Nat.Ico_succ_singleton, Finset.sum_singleton]; ring
  | succ j hj ih =>
      rw [Finset.sum_Ico_succ_top (by omega), ← add_assoc, ← ih]
      ring

/-- The sum of steps up to `n ≤ N` is split into its centred non-birth part, the non-birth means
and the births. -/
theorem enorm_sum_split_le (Z e : ℕ → ℂ) (p : ℕ → Prop) [DecidablePred p] {a n N : ℕ}
    (hn : n ≤ N) :
    ‖∑ i ∈ Finset.Ico a n, Z i‖ₑ ≤ ‖∑ i ∈ (Finset.Ico a n).filter (fun i => ¬ p i), (Z i - e i)‖ₑ +
      (∑ i ∈ (Finset.Ico a N).filter (fun i => ¬ p i), ‖e i‖ₑ +
        ∑ i ∈ (Finset.Ico a N).filter (fun i => p i), ‖Z i‖ₑ) := by
  have hsub : Finset.Ico a n ⊆ Finset.Ico a N := Finset.Ico_subset_Ico_right hn
  have hsplit : ∑ i ∈ Finset.Ico a n, Z i =
      ∑ i ∈ (Finset.Ico a n).filter (fun i => ¬ p i), (Z i - e i) +
        (∑ i ∈ (Finset.Ico a n).filter (fun i => ¬ p i), e i +
          ∑ i ∈ (Finset.Ico a n).filter (fun i => p i), Z i) := by
    rw [← add_assoc, ← Finset.sum_add_distrib, add_comm,
      ← Finset.sum_filter_add_sum_filter_not _ (fun i => p i)]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsplit]
  refine (enorm_add_le _ _).trans (add_le_add le_rfl ((enorm_add_le _ _).trans
    (add_le_add ?_ ?_)))
  · exact (enorm_sum_le _ _).trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset_filter _ hsub) fun _ _ _ => zero_le)
  · exact (enorm_sum_le _ _).trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset_filter _ hsub) fun _ _ _ => zero_le)

theorem add_pow_four_le_four (a c d f : ℝ≥0∞) :
    (a + (c + (d + f))) ^ 4 ≤ 64 * (a ^ 4 + (c ^ 4 + (d ^ 4 + f ^ 4))) := by
  calc (a + (c + (d + f))) ^ 4 = ((a + c) + (d + f)) ^ 4 := by ring
    _ ≤ 8 * ((a + c) ^ 4 + (d + f) ^ 4) := add_pow_four_le _ _
    _ ≤ 8 * (8 * (a ^ 4 + c ^ 4) + 8 * (d ^ 4 + f ^ 4)) := by
        gcongr <;> exact add_pow_four_le _ _
    _ = 64 * (a ^ 4 + (c ^ 4 + (d ^ 4 + f ^ 4))) := by ring

/-!
## The reduction
-/

/-- **`KUnclosedMax` from the raw moments and the two per-step estimates** (Doob + crude Burkholder
for the centred non-birth sum, `RawTagMoments` for the start and the births). -/
theorem kUnclosedMax_of_parts (hR : RawTagMoments) (hS : KUncStepFour) (hE : KUncMeanSum) :
    KUnclosedMax := by
  intro b E np τ m T hD s
  obtain ⟨C₀, W₀, hC₀⟩ := lintegral_kUnclosed_le hR hD
  obtain ⟨C₁, h₁⟩ := hS b E np τ m T hD s
  obtain ⟨C₂, h₂⟩ := hE b E np τ m T hD s
  obtain ⟨C₃, h₃⟩ := kUncBirthSum_of_raw hR b E np τ m T hD s
  refine ⟨64 * (max C₀ 0 + (4096 * (max T 0 + 1) * max C₁ 0 + (max C₂ 0 + max C₃ 0))), ?_⟩
  filter_upwards [h₁, h₂, h₃, eventually_ge_atTop W₀, eventually_ge_atTop 1] with
    W hW1 hW2 hW3 hW0 hW1' ij
  set N := ⌊(W : ℝ) * T⌋₊ with hN
  set S := (Finset.Ico (closeLen s W) N).filter (fun i => ¬ IsBirthStep τ W i) with hS
  set μ := closedLaw b W np with hμ
  set Z : ℕ → ProbedPath W np × ℝ → ℂ := fun i => kUncStep b E τ m W i ij with hZ
  have hpos : 0 ≤ 64 * (max C₀ 0 + (4096 * (max T 0 + 1) * max C₁ 0 + (max C₂ 0 + max C₃ 0))) := by
    positivity
  by_cases hlt : closeLen s W < N
  swap
  · rw [Finset.Ico_eq_empty (by omega)]
    simp
  have hZm : ∀ i ∈ S, StronglyMeasurable[b3Filt W np (i + 1)] (Z i) := fun i _ =>
    (measurable_kUncStep_past b E τ m W i ij).stronglyMeasurable
  have hW' := hW1 ij
  have hfin : ∀ i ∈ S, ∫⁻ y, ‖Z i y‖ₑ ^ 4 ∂μ ≠ ⊤ := by
    intro i hi
    refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_trans ?_ hW')
    calc ∫⁻ y, ‖Z i y‖ₑ ^ 4 ∂μ ≤ ∑ i ∈ S, ∫⁻ y, ‖Z i y‖ₑ ^ 4 ∂μ :=
          Finset.single_le_sum (f := fun i => ∫⁻ y, ‖Z i y‖ₑ ^ 4 ∂μ) (fun _ _ => zero_le) hi
      _ ≤ ((W : ℕ) : ℝ≥0∞) * ∑ i ∈ S, ∫⁻ y, ‖Z i y‖ₑ ^ 4 ∂μ :=
          le_mul_of_one_le_left zero_le (by exact_mod_cast hW1')
  have hZ4 : ∀ i ∈ S, MemLp (Z i) 4 μ := fun i hi =>
    memLp_four_of_lintegral (measurable_kUncStep b E τ m W i ij).aestronglyMeasurable
      (hfin i hi)
  have hM := martingale_martSum (μ := μ) hZm fun i hi => (hZ4 i hi).integrable (by norm_num)
  have key := lintegral_runMax_martSum_le (μ := μ) (ℱ := b3Filt W np) hZm hZ4 N
  set fA : ProbedPath W np × ℝ → ℝ≥0∞ := fun y =>
    ‖complexSourceK b E W (closeLen s W) τ m y.1 ij.1 ij.2‖ₑ ^ 4 with hfA
  set fM : ProbedPath W np × ℝ → ℝ≥0∞ := fun y =>
    ‖(Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
      (fun k => ‖martSum (b3Filt W np) μ S Z k y‖)‖ₑ ^ 4 with hfM
  set fE : ProbedPath W np × ℝ → ℝ≥0∞ := fun y =>
    (∑ i ∈ S, ‖kUncMean b E τ m W i ij y‖ₑ) ^ 4 with hfE
  set fB : ProbedPath W np × ℝ → ℝ≥0∞ := fun y =>
    (∑ i ∈ (Finset.Ico (closeLen s W) N).filter (fun i => IsBirthStep τ W i),
      ‖kUncStep b E τ m W i ij y‖ₑ) ^ 4 with hfB
  have hpt : ∀ y, (⨆ j ∈ Finset.Ico (closeLen s W) N,
      ‖complexSourceK b E W (j + 1) τ m y.1 ij.1 ij.2‖ₑ ^ 4) ≤
      64 * (fA y + (fM y + (fE y + fB y))) := by
    intro y
    refine iSup₂_le fun j hj => ?_
    obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.1 hj
    have ht := telescope_Ico (fun n => complexSourceK b E W n τ m y.1 ij.1 ij.2) hj1
    have hsp := enorm_sum_split_le (fun i => Z i y) (fun i => kUncMean b E τ m W i ij y)
      (fun i => IsBirthStep τ W i) (a := closeLen s W) (n := j + 1) (N := N) hj2
    have hset := filter_Ico_eq_range_filter (a := closeLen s W)
      (fun i => ¬ IsBirthStep τ W i) hj2
    have hms : ∑ i ∈ (Finset.Ico (closeLen s W) (j + 1)).filter (fun i => ¬ IsBirthStep τ W i),
        (Z i y - kUncMean b E τ m W i ij y) = martSum (b3Filt W np) μ S Z (j + 1) y := by
      rw [hset, martSum, Finset.sum_apply]
      rfl
    have hle : ‖martSum (b3Filt W np) μ S Z (j + 1) y‖ₑ ≤
        ‖(Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
          (fun k => ‖martSum (b3Filt W np) μ S Z k y‖)‖ₑ := by
      rw [← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal ((Finset.le_sup' (fun k => ‖martSum (b3Filt W np) μ S Z k y‖)
        (Finset.mem_range.2 (by omega))).trans (Real.le_norm_self _))
    rw [hms] at hsp
    have hb : ‖complexSourceK b E W (j + 1) τ m y.1 ij.1 ij.2‖ₑ ≤
        ‖complexSourceK b E W (closeLen s W) τ m y.1 ij.1 ij.2‖ₑ +
          (‖(Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
            (fun k => ‖martSum (b3Filt W np) μ S Z k y‖)‖ₑ +
          (∑ i ∈ S, ‖kUncMean b E τ m W i ij y‖ₑ +
            ∑ i ∈ (Finset.Ico (closeLen s W) N).filter (fun i => IsBirthStep τ W i),
              ‖kUncStep b E τ m W i ij y‖ₑ)) := by
      rw [ht]
      refine (enorm_add_le _ _).trans (add_le_add le_rfl ?_)
      refine hsp.trans (add_le_add hle le_rfl)
    exact (pow_le_pow_left₀ zero_le hb 4).trans (add_pow_four_le_four _ _ _ _)
  have hmA : Measurable fA :=
    (measurable_enorm_complexSourceK_pow b E (closeLen s W) τ m ij.1 ij.2).comp measurable_fst
  have hmM : Measurable fM :=
    ((Finset.measurable_range_sup'' fun k _ =>
      ((hM.stronglyMeasurable k).mono ((b3Filt W np).le k)).norm.measurable).enorm).pow_const 4
  have hmE : Measurable fE :=
    (Finset.measurable_sum _ fun i _ =>
      (measurable_kUncMean b E τ m W i ij).enorm).pow_const 4
  have iA : ∫⁻ y, fA y ∂μ ≤ ENNReal.ofReal (max C₀ 0) := by
    have hn := succ_le_mul_of_lt_floor hlt
    have hn0 : (closeLen s W : ℝ) ≤ T * W := le_trans (by push_cast; linarith) hn
    exact (hC₀ W hW0 (closeLen s W) hn0 ij).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have iM : ∫⁻ y, fM y ∂μ ≤ 4096 * ENNReal.ofReal (max T 0 + 1) * ENNReal.ofReal (max C₁ 0) := by
    have hfilt : (Finset.range N).filter (· ∈ S) = S :=
      (filter_Ico_eq_range_filter (a := closeLen s W) _ le_rfl).symm
    have hNW := floor_add_one_le_mul hW1' T
    calc ∫⁻ y, fM y ∂μ ≤ 4096 * ((N : ℝ≥0∞) + 1) * ∑ i ∈ (Finset.range N).filter (· ∈ S),
          ∫⁻ y, ‖Z i y‖ₑ ^ 4 ∂μ := key
      _ = 4096 * ((N : ℝ≥0∞) + 1) * ∑ i ∈ S, ∫⁻ y, ‖Z i y‖ₑ ^ 4 ∂μ := by rw [hfilt]
      _ ≤ 4096 * (((W : ℕ) : ℝ≥0∞) * ENNReal.ofReal (max T 0 + 1)) *
            ∑ i ∈ S, ∫⁻ y, ‖Z i y‖ₑ ^ 4 ∂μ := by gcongr
      _ = 4096 * ENNReal.ofReal (max T 0 + 1) *
            (((W : ℕ) : ℝ≥0∞) * ∑ i ∈ S, ∫⁻ y, ‖Z i y‖ₑ ^ 4 ∂μ) := by ring
      _ ≤ 4096 * ENNReal.ofReal (max T 0 + 1) * ENNReal.ofReal (max C₁ 0) := by
          gcongr
          exact hW'.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have iE : ∫⁻ y, fE y ∂μ ≤ ENNReal.ofReal (max C₂ 0) :=
    (hW2 ij).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have iB : ∫⁻ y, fB y ∂μ ≤ ENNReal.ofReal (max C₃ 0) :=
    (hW3 ij).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_left hmA, lintegral_add_left hmM,
    lintegral_add_left hmE]
  calc 64 * (∫⁻ y, fA y ∂μ + (∫⁻ y, fM y ∂μ + (∫⁻ y, fE y ∂μ + ∫⁻ y, fB y ∂μ)))
      ≤ 64 * (ENNReal.ofReal (max C₀ 0) + (4096 * ENNReal.ofReal (max T 0 + 1) *
          ENNReal.ofReal (max C₁ 0) + (ENNReal.ofReal (max C₂ 0) +
            ENNReal.ofReal (max C₃ 0)))) := by gcongr
    _ = ENNReal.ofReal
          (64 * (max C₀ 0 + (4096 * (max T 0 + 1) * max C₁ 0 + (max C₂ 0 + max C₃ 0)))) := by
        rw [ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_add (p := max C₀ 0) (by positivity) (by positivity),
          ENNReal.ofReal_add (p := 4096 * (max T 0 + 1) * max C₁ 0) (by positivity)
            (by positivity),
          ENNReal.ofReal_add (p := max C₂ 0) (by positivity) (by positivity),
          ENNReal.ofReal_mul (p := 4096 * (max T 0 + 1)) (by positivity),
          ENNReal.ofReal_mul (p := 4096) (by norm_num), ENNReal.ofReal_ofNat,
          ENNReal.ofReal_ofNat]

/-- **`KUnclosedMax` from the input hypotheses and the two per-step estimates.** -/
theorem kUnclosedMax_of_baseContracts (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract) (hMT : MatchedTracesContract)
    (hS : KUncStepFour) (hE : KUncMeanSum) : KUnclosedMax :=
  kUnclosedMax_of_parts (RawTag.rawTagMoments_holds hGA hLp hSR hMT) hS hE

end BlockBand.SourceProcess.PhysApprox.B3
