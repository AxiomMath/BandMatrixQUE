module

public import BlockBand.SourceProcess.PhysApprox.B3BirthMCrossAlg

/-!
# The closed Gram overlaps of a newborn column

At the birth length `n = j + 1` of the tag `i`, let `F_c` be any other closed column (`c ≠ i`) and
`Q ∈ {1, P}`. Every new non-diagonal Gram coordinate is `⟨F_k, QF_l⟩` with one of `k, l` equal to
`i`, so its modulus is `|⟨QF_c, F_i⟩|` (`norm_gramEntry_eq`). With `F_i = V_i + L_i`:
* the probe `g_i` is independent of `F_c` and of the alive set at `j` (`closedCol_updProbe`,
  `b3AliveM_updProbe`), so `E_{g_i}|⟨u, V_i⟩| ≤ (m/W)^{1/2}‖Rᴴu‖` and
  `‖Rᴴu‖² ≤ ‖Y‖_HS ‖u‖²` (`lintegral_dot_le`, `re_dot_mulVec_le`);
* `|⟨u, L_i⟩| ≤ ‖u‖‖L_i‖` and `E‖L_i‖² ≤ 2E‖(1−P)V_i‖² → 0` (`lintegral_closed_leak_le`).
Both need the one-step moment `E[1_{A_j}‖F_c(j+1)‖²] ≤ C`: the estimate
`ComplexBirthOtherColL2`. **`complexBirthCrossGram_of`**: under `MatchedTracesContract`
and `GaussianAbsorptionContract`, `ComplexBirthOtherColL2` implies `ComplexBirthCrossGram`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosingLeak
open BlockBand.SourceProcess.ClosingAux BlockBand.SourceProcess.ClosedLimit
open BlockBand.SourceProcess.ClosedPath BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.Transmission.Bridge
open BlockBand.SourceProcess.ClosedSum
open scoped NNReal ENNReal ComplexConjugate ComplexOrder

namespace BirthM

variable {W : ℕ}

/-!
## Independence of the newborn probe
-/

theorem probeColumns_update {np l : ℕ} (τ m : Fin np → ℝ) {i : Fin np}
    (hi : l ≤ ⌊(W : ℝ) * τ i⌋₊) (g : Fin np → Fin W → ℂ) (a : Fin W → ℂ) :
    probeColumns W l τ m (Function.update g i a) = probeColumns W l τ m g := by
  funext x i'
  simp only [probeColumns]
  by_cases h : i' = i
  · subst h
    have : ¬ ⌊(W : ℝ) * τ i'⌋₊ < l := by omega
    simp [this]
  · rw [Function.update_of_ne h]

theorem probeColumns_col_update {np n : ℕ} (τ m : Fin np → ℝ) {i i' : Fin np} (h : i' ≠ i)
    (g : Fin np → Fin W → ℂ) (a : Fin W → ℂ) (x : Fin n × Fin W) :
    probeColumns W n τ m (Function.update g i a) x i' = probeColumns W n τ m g x i' := by
  simp only [probeColumns, Function.update_of_ne h]

theorem b3ClosedGramAt_updProbe (b E s h : ℝ) {np K l : ℕ} (τ m : Fin np → ℝ) {i : Fin np}
    (hi : l ≤ ⌊(W : ℝ) * τ i⌋₊) (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (y : ProbedPath W np × ℝ) (a : Fin W → ℂ) :
    b3ClosedGramAt b E s h τ m W l Vs (updProbe i y a) = b3ClosedGramAt b E s h τ m W l Vs y := by
  simp only [b3ClosedGramAt, b3ClosedFrameAt, b3OpenFrameAt, probeFrame, updProbe,
    probeColumns_update τ m hi]

theorem b3AliveM_updProbe (b E s h : ℝ) {np K j : ℕ} (τ m : Fin np → ℝ) (R : ℝ) {i : Fin np}
    (hi : j ≤ ⌊(W : ℝ) * τ i⌋₊) (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (y : ProbedPath W np × ℝ) (a : Fin W → ℂ) :
    updProbe i y a ∈ b3AliveM b E s h τ m R W j Vs ↔ y ∈ b3AliveM b E s h τ m R W j Vs := by
  simp only [b3AliveM, b3TraceOK, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun l hl1 hl2 => by
      rw [← b3ClosedGramAt_updProbe b E s h τ m (hl2.trans hi) Vs y a]; exact h2 l hl1 hl2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun l hl1 hl2 => by
      rw [b3ClosedGramAt_updProbe b E s h τ m (hl2.trans hi) Vs y a]; exact h2 l hl1 hl2⟩

/-- Every closed column other than the newborn's is independent of the newborn probe. -/
theorem closedCol_updProbe (b E s h : ℝ) {np K n : ℕ} (τ m : Fin np → ℝ) {i : Fin np}
    {c : SrcCol K (Fin np)} (hc : c ≠ Sum.inr i)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (y : ProbedPath W np × ℝ)
    (a : Fin W → ℂ) :
    (fun z => b3ClosedFrameAt b E s h τ m W n Vs (updProbe i y a) z c) =
      fun z => b3ClosedFrameAt b E s h τ m W n Vs y z c := by
  funext z
  simp only [b3ClosedFrameAt, mul_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  congr 1
  rcases c with k | i'
  · simp [b3OpenFrameAt, updProbe]
  · have hi' : i' ≠ i := fun e => hc (by rw [e])
    simp only [b3OpenFrameAt, of_apply, Sum.elim_inr, probeFrame, mul_apply, updProbe]
    exact Finset.sum_congr rfl fun x _ => by rw [probeColumns_col_update τ m hi']

theorem probeFrame_col_updProbe (b E : ℝ) {np n : ℕ} (τ m : Fin np → ℝ) (i : Fin np)
    (hi : ⌊(W : ℝ) * τ i⌋₊ < n) (y : ProbedPath W np × ℝ) (a : Fin W → ℂ) :
    (fun w => probeFrame b E W n τ m (updProbe i y a).1 w i) =
      ((Real.sqrt (m i / W) : ℝ) : ℂ) •
        (newR b E W n ⟨n - 1 - ⌊(W : ℝ) * τ i⌋₊, by omega⟩ y.1.1 *ᵥ a) := by
  rw [probeFrame_col b E τ m i hi]
  simp [updProbe]

/-!
## The Gram coordinates as overlaps
-/

/-- `Q_σ = 1` for `M`, `P` for `B`. -/
def gramQ (W : ℕ) (σ : Fin 2) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  if σ = 0 then 1 else nearPortProj W

theorem gramQ_conjTranspose (σ : Fin 2) : (gramQ W σ)ᴴ = gramQ W σ := by
  unfold gramQ; split_ifs
  · exact conjTranspose_one
  · exact nearPortProj_conjTranspose

theorem l2_gramQ_le (σ : Fin 2) (v : Fin 2 × Fin W → ℂ) : l2 (gramQ W σ *ᵥ v) ≤ l2 v := by
  unfold gramQ; split_ifs
  · rw [one_mulVec]
  · exact l2_near_le v

theorem gramEntry_gramPair {c : Type*} [Fintype c] (σ : Fin 2) (k l : c)
    (F : Matrix (Fin 2 × Fin W) c ℂ) :
    gramEntry (σ, k, l) (gramPair (nearPortProj W) F) =
      star (fun z => F z k) ⬝ᵥ (gramQ W σ *ᵥ fun z => F z l) := by
  simp only [gramEntry, gramPair, sourceGram, nearGram, gramQ]
  split_ifs
  · rw [one_mulVec]
    simp only [mul_apply, conjTranspose_apply, dotProduct, Pi.star_apply]
  · simp only [mul_apply, conjTranspose_apply, dotProduct, Pi.star_apply, mulVec,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun w _ => by ring

theorem dot_herm {ι : Type*} [Fintype ι] {Q : Matrix ι ι ℂ} (hQ : Qᴴ = Q) (x v : ι → ℂ) :
    star x ⬝ᵥ (Q *ᵥ v) = star (Q *ᵥ x) ⬝ᵥ v := by
  rw [star_mulVec, ← dotProduct_mulVec, hQ]

theorem norm_dot_comm {ι : Type*} [Fintype ι] (x v : ι → ℂ) :
    ‖star x ⬝ᵥ v‖ = ‖star v ⬝ᵥ x‖ := by
  have e : star x ⬝ᵥ v = conj (star v ⬝ᵥ x) := by
    simp only [dotProduct, Pi.star_apply, map_sum, map_mul, RCLike.star_def, Complex.conj_conj]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [e, Complex.norm_conj]

/-- **The new non-diagonal Gram coordinates as overlaps with the newborn column.** -/
theorem norm_gramEntry_eq {c : Type*} [Fintype c] (σ : Fin 2) (k l : c)
    (F : Matrix (Fin 2 × Fin W) c ℂ) :
    ‖gramEntry (σ, k, l) (gramPair (nearPortProj W) F)‖ =
        ‖star (gramQ W σ *ᵥ fun z => F z k) ⬝ᵥ fun z => F z l‖ ∧
      ‖gramEntry (σ, k, l) (gramPair (nearPortProj W) F)‖ =
        ‖star (gramQ W σ *ᵥ fun z => F z l) ⬝ᵥ fun z => F z k‖ := by
  have e := dot_herm (gramQ_conjTranspose (W := W) σ) (fun z => F z k) (fun z => F z l)
  rw [gramEntry_gramPair]
  refine ⟨by rw [e], ?_⟩
  rw [norm_dot_comm]

/-- `√A·x ≤ (δ/2)x² + A/(2δ)`. -/
theorem sqrt_mul_le_amgm {A x δ : ℝ} (hA : 0 ≤ A) (hδ : 0 < δ) :
    Real.sqrt A * x ≤ δ / 2 * x ^ 2 + A / (2 * δ) := by
  have h := sq_nonneg (δ * x - Real.sqrt A)
  have hs := Real.sq_sqrt hA
  rw [show δ / 2 * x ^ 2 + A / (2 * δ) = (δ ^ 2 * x ^ 2 + A) / (2 * δ) by field_simp,
    le_div_iff₀ (by positivity)]
  nlinarith

/-!
## Averaging over the newborn probe
-/

theorem dot_mulVec_eq {κ : Type*} [Fintype κ] (u : Fin 2 × Fin W → ℂ)
    (R : Matrix (Fin 2 × Fin W) κ ℂ) (a : κ → ℂ) :
    star u ⬝ᵥ (R *ᵥ a) = star (Rᴴ *ᵥ u) ⬝ᵥ a := by
  rw [star_mulVec, conjTranspose_conjTranspose, ← dotProduct_mulVec]

/-- **The newborn probe average of an overlap**: for a set and a vector independent of the probe
`g_i`, `E[1_S|⟨u, V_i⟩|] ≤ E[1_S (m/W)^{1/2}‖Rᴴu‖]`. -/
theorem lintegral_resample_le (b E : ℝ) {np n : ℕ} (τ m : Fin np → ℝ) (i : Fin np)
    (hi : ⌊(W : ℝ) * τ i⌋₊ < n) {S : Set (ProbedPath W np × ℝ)} (hS : MeasurableSet S)
    (hSu : ∀ y a, updProbe i y a ∈ S ↔ y ∈ S) {u : ProbedPath W np × ℝ → Fin 2 × Fin W → ℂ}
    (hu : Measurable u) (huu : ∀ y a, u (updProbe i y a) = u y) :
    ∫⁻ y, S.indicator (fun y => ENNReal.ofReal
        ‖star (u y) ⬝ᵥ fun w => probeFrame b E W n τ m y.1 w i‖) y ∂closedLaw b W np ≤
      ∫⁻ y, S.indicator (fun y => ENNReal.ofReal (Real.sqrt (m i / W) *
        l2 ((newR b E W n ⟨n - 1 - ⌊(W : ℝ) * τ i⌋₊, by omega⟩ y.1.1)ᴴ *ᵥ u y))) y
        ∂closedLaw b W np := by
  set p : Fin n := ⟨n - 1 - ⌊(W : ℝ) * τ i⌋₊, by omega⟩
  have hV := measurable_probeFrame_col (W := W) b E (n := n) τ m i
  have hG : Measurable fun y : ProbedPath W np × ℝ => S.indicator (fun y => ENNReal.ofReal
      ‖star (u y) ⬝ᵥ fun w => probeFrame b E W n τ m y.1 w i‖) y := by
    refine Measurable.indicator ?_ hS
    simp only [dotProduct, Pi.star_apply]
    exact (Finset.measurable_sum _ fun z _ => ((Complex.continuous_conj.measurable.comp
      ((measurable_pi_apply z).comp hu)).mul ((measurable_pi_apply z).comp
        (hV.comp measurable_fst)))).norm.ennreal_ofReal
  rw [lintegral_closedLaw_update b i hG]
  refine lintegral_mono fun y => ?_
  by_cases hy : y ∈ S
  · rw [Set.indicator_of_mem hy]
    have e : ∀ a, S.indicator (fun y => ENNReal.ofReal
        ‖star (u y) ⬝ᵥ fun w => probeFrame b E W n τ m y.1 w i‖) (updProbe i y a) =
          ENNReal.ofReal (Real.sqrt (m i / W)) *
            ENNReal.ofReal ‖star ((newR b E W n p y.1.1)ᴴ *ᵥ u y) ⬝ᵥ a‖ := by
      intro a
      rw [Set.indicator_of_mem ((hSu y a).2 hy), huu, probeFrame_col_updProbe b E τ m i hi,
        dotProduct_smul, dot_mulVec_eq, smul_eq_mul, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (Real.sqrt_nonneg _), ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    simp_rw [e]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    exact mul_le_mul_right (lintegral_dot_le _) _
  · simp only [Set.indicator_of_notMem hy]
    have e : ∀ a, S.indicator (fun y => ENNReal.ofReal
        ‖star (u y) ⬝ᵥ fun w => probeFrame b E W n τ m y.1 w i‖) (updProbe i y a) = 0 :=
      fun a => Set.indicator_of_notMem (fun h => hy ((hSu y a).1 h)) _
    simp_rw [e, lintegral_zero]
    exact le_rfl

/-- `‖Rᴴu‖ ≤ (Re Tr Y²)^{1/4}‖u‖` for `RRᴴ = Y`. -/
theorem l2_conj_mulVec_le {κ : Type*} [Fintype κ] {R : Matrix (Fin 2 × Fin W) κ ℂ}
    {Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hR : R * Rᴴ = Y) (u : Fin 2 × Fin W → ℂ) :
    l2 (Rᴴ *ᵥ u) ≤ Real.sqrt (Real.sqrt (Y * Y).trace.re) * l2 u := by
  have h1 : (star u ⬝ᵥ (Y *ᵥ u)).re = l2 (Rᴴ *ᵥ u) ^ 2 := by
    rw [← hR, ← conjTranspose_conjTranspose R, conjTranspose_conjTranspose Rᴴ, dot_conj_mul_eq,
      Complex.ofReal_re]
  have hYh : Yᴴ = Y := by rw [← hR, conjTranspose_mul, conjTranspose_conjTranspose]
  have h2 := re_dot_mulVec_le Y u
  rw [hYh] at h2
  have h3 : l2 (Rᴴ *ᵥ u) ^ 2 ≤ (Real.sqrt (Real.sqrt (Y * Y).trace.re) * l2 u) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Real.sqrt_nonneg _)]; linarith
  exact (pow_le_pow_iff_left₀ (l2_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (l2_nonneg _))
    two_ne_zero).mp h3

end BirthM

/-!
## The estimates
-/

/-- **One-step moment of the other columns at a birth**: one step after the birth of `i`,
every other closed column `c ≠ i` (current, old probe, or another newborn) has
`E[1_{A_j}‖F_c(j+1)‖²] ≤ C`, uniformly over the birth steps. For an old column it is the alive
bound `M_cc(j) ≤ R` plus the one-step increment (`ComplexBirthOldL2`); for another newborn it is
the newborn squared norm (`lintegral_newborn_sq_sub_le`). -/
def ComplexBirthOtherColL2 : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ (R : ℝ) (i : Fin np) (c : SrcCol K (Fin np)),
      c ≠ Sum.inr i → ∃ C : ℝ, ∀ᶠ W : ℕ in atTop,
        ∀ j, closeLen s W ≤ j → j < ⌊(W : ℝ) * T⌋₊ → ⌊(W : ℝ) * τ i⌋₊ = j →
          ∫⁻ y, (b3Alive b E s h τ m R W j (Vs W)).indicator (fun y => ENNReal.ofReal
              (l2 (fun z => b3ClosedFrameAt b E s h τ m W (j + 1) (Vs W) y z c) ^ 2)) y
            ∂closedLaw b W np ≤ ENNReal.ofReal C

open BirthM

variable {W : ℕ}

/-- **The overlap of the newborn column with another closed column** tends to `0` on the alive
set (both Gram coordinates `Q = 1, P`). -/
theorem lintegral_cross_core (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hX : ComplexBirthOtherColL2) {b E : ℝ} {np : ℕ} {τ m : Fin np → ℝ} {T s h : ℝ} {K : ℕ}
    {Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hD : FrameDomain b E τ m T s h K Vs) (R θ : ℝ) (hθ : 0 < θ) (i : Fin np)
    {c : SrcCol K (Fin np)} (hc : c ≠ Sum.inr i) (σ : Fin 2) :
    ∀ᶠ W : ℕ in atTop, ∀ j, closeLen s W ≤ j → j < ⌊(W : ℝ) * T⌋₊ → ⌊(W : ℝ) * τ i⌋₊ = j →
      ∫⁻ y, (b3Alive b E s h τ m R W j (Vs W)).indicator (fun y => ENNReal.ofReal
          ‖star (gramQ W σ *ᵥ fun z => b3ClosedFrameAt b E s h τ m W (j + 1) (Vs W) y z c) ⬝ᵥ
            fun z => b3ClosedFrameAt b E s h τ m W (j + 1) (Vs W) y z (Sum.inr i)‖) y
        ∂closedLaw b W np ≤ ENNReal.ofReal θ := by
  obtain ⟨CX, hCX⟩ := hX b E np τ m T s h K Vs hD R i c hc
  obtain ⟨⟨hb0, hb, hE1, hE2, -, -, hm0, hτT⟩, hs, hsτ, hh0, hh1, hTS⟩ := hD
  have hm := hm0 i
  have hTB := TagBirth.tagBirthValue_holds hMT hGA
    BlockBand.GaussianCalculus.gaussianLpGradient_holds
  set K' := max CX 0 with hK'def
  have hK' : 0 ≤ K' := le_max_right _ _
  set δ := θ / (2 * (K' + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  set θ₁ := θ * δ / (3 * m i + 1) with hθ₁def
  have hθ₁ : 0 < θ₁ := by positivity
  have hsT : s / 2 < T := by linarith [hsτ i, hτT i]
  obtain ⟨C, Ws, hWs⟩ := hTB.square b hb0 hb E hE1 hE2 (s / 2) T (by positivity) hsT
  set C' := max C 0
  filter_upwards [newbornFarMass_holds hMT hGA b hb0 hb E hE1 hE2 s T hs θ₁ hθ₁, hCX, hTS,
    eventually_ge_atTop (max Ws (max (⌈2 / s⌉₊ + 1) (⌈C' / θ₁ ^ 2⌉₊ + 1)))]
    with W hFar hCXW hTSW hW j hj1 hj2 hij
  have hXW := hCXW j hj1 hj2 hij
  subst hij
  set k := ⌊(W : ℝ) * τ i⌋₊ with hkdef
  have hWs' : Ws ≤ W := le_trans (by simp) hW
  have hW2 : ⌈2 / s⌉₊ + 1 ≤ W := le_trans (by simp) hW
  have hWC : ⌈C' / θ₁ ^ 2⌉₊ + 1 ≤ W := le_trans (by simp) hW
  have hW1 : 1 ≤ W := by omega
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW1
  have hWsr : 2 ≤ (W : ℝ) * s := by
    have : 2 / s ≤ W := (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈2 / s⌉₊ ≤ W))
    rw [div_le_iff₀ hs] at this; linarith
  have hns : (W : ℝ) * s - 1 < ⌊(W : ℝ) * s⌋₊ := Nat.sub_one_lt_floor _
  have hkε : s / 2 * W ≤ k := by
    have : ((⌊(W : ℝ) * s⌋₊ : ℕ) : ℝ) ≤ k := by exact_mod_cast hj1
    nlinarith
  have hkT : ((k + 1 : ℕ) : ℝ) ≤ T * W := by
    have hpos : 0 < ⌊(W : ℝ) * T⌋₊ := by omega
    have h1 : (1 : ℝ) ≤ W * T := Nat.floor_pos.mp hpos
    have h2 : ((⌊(W : ℝ) * T⌋₊ : ℕ) : ℝ) ≤ W * T := Nat.floor_le (by linarith)
    have h3 : k + 1 ≤ ⌊(W : ℝ) * T⌋₊ := hj2
    have h4 : ((k + 1 : ℕ) : ℝ) ≤ ⌊(W : ℝ) * T⌋₊ := by exact_mod_cast h3
    linarith [mul_comm (W : ℝ) T]
  have hlt : k < k + 1 := Nat.lt_succ_self k
  have hSq := lintegral_sqrt_trace_sq_le b E hlt (hWs W hWs' k hkε hkT)
  have hsq : Real.sqrt (C' / W) ≤ θ₁ := by
    have hc' : C' / θ₁ ^ 2 ≤ W := by
      have := Nat.le_ceil (C' / θ₁ ^ 2)
      have h2 : ((⌈C' / θ₁ ^ 2⌉₊ : ℕ) : ℝ) ≤ W := by
        exact_mod_cast (by omega : ⌈C' / θ₁ ^ 2⌉₊ ≤ W)
      linarith
    have : C' / W ≤ θ₁ ^ 2 := by
      rw [div_le_iff₀ hWr]; rw [div_le_iff₀ (by positivity)] at hc'; linarith
    calc Real.sqrt (C' / W) ≤ Real.sqrt (θ₁ ^ 2) := Real.sqrt_le_sqrt this
      _ = θ₁ := Real.sqrt_sq hθ₁.le
  have hF := hFar k hj1 hj2
  -- the objects
  have hVs : Measurable (Vs W) := hTSW.1.mono (Transmission.Generator.growthSigma_le W _) le_rfl
  set A := b3Alive b E s h τ m R W k (Vs W)
  set A' := b3AliveM b E s h τ m R W k (Vs W)
  have hAA : A =ᵐ[closedLaw b W np] A' :=
    b3Alive_ae_eq (by linarith) hE1 hE2 s h τ m R W k (Vs W)
  have hA' : MeasurableSet A' := measurableSet_b3AliveM b E s h τ m R W k hVs
  have hFm := measurable_b3ClosedFrameAt b E s h τ m W (k + 1) hVs
  set Fc := fun (y : ProbedPath W np × ℝ) (z : Fin 2 × Fin W) =>
    b3ClosedFrameAt b E s h τ m W (k + 1) (Vs W) y z c with hFcdef
  have hFc : Measurable Fc := measurable_pi_iff.2 fun _ => hFm.eval_matrix
  set u := fun y => gramQ W σ *ᵥ Fc y with hudef
  have hu : Measurable u := RawTag.measurable_mulVec' measurable_const hFc
  set V := fun (y : ProbedPath W np × ℝ) (w : Fin 2 × Fin W) => probeFrame b E W (k + 1) τ m y.1 w i
  have hVm : Measurable V := (measurable_probeFrame_col (W := W) b E τ m i).comp measurable_fst
  set Cm := fun y : ProbedPath W np × ℝ => physClosingMapAt b E s h W (k + 1) y.1.1 (phase y.2)
  have hCm : Measurable Cm := measurable_physClosingMapAt_comp b E s h (k + 1)
    (measurable_fst.comp measurable_fst) (measurable_phase.comp measurable_snd)
  set ℓ := fun y => l2 ((Cm y)ᴴ *ᵥ V y - V y)
  have hℓ : Measurable ℓ := continuous_l2.measurable.comp ((RawTag.measurable_mulVec'
    (measurable_matrix_conjTranspose' hCm) hVm).sub hVm)
  set p : Fin (k + 1) := ⟨k + 1 - 1 - k, by omega⟩
  set lam := fun ω : GrowthPath W =>
    Real.sqrt (tagResponse b E W (k + 1) k ω * tagResponse b E W (k + 1) k ω).trace.re
  have hlam : Measurable lam := Real.continuous_sqrt.measurable.comp (Complex.measurable_re.comp
    ((continuous_id.matrix_trace).measurable.comp (measurable_matrix_mul'
      (FullSourceStops.measurable_tagResponse b E (k + 1) k)
      (FullSourceStops.measurable_tagResponse b E (k + 1) k))))
  -- the LHS on the Borel alive set
  have hLHS : ∫⁻ y, A.indicator (fun y => ENNReal.ofReal ‖star (u y) ⬝ᵥ
      fun z => b3ClosedFrameAt b E s h τ m W (k + 1) (Vs W) y z (Sum.inr i)‖) y
        ∂closedLaw b W np =
      ∫⁻ y, A'.indicator (fun y => ENNReal.ofReal ‖star (u y) ⬝ᵥ (Cm y)ᴴ *ᵥ V y‖) y
        ∂closedLaw b W np := by
    have hfg : (fun y => ENNReal.ofReal ‖star (u y) ⬝ᵥ
        fun z => b3ClosedFrameAt b E s h τ m W (k + 1) (Vs W) y z (Sum.inr i)‖) =
          fun y => ENNReal.ofReal ‖star (u y) ⬝ᵥ (Cm y)ᴴ *ᵥ V y‖ :=
      funext fun y => by rw [b3ClosedFrameAt_col]
    rw [hfg]
    exact lintegral_congr_ae (indicator_ae_eq_of_ae_eq_set hAA)
  have hX' : ∫⁻ y, A'.indicator (fun y => ENNReal.ofReal (l2 (Fc y) ^ 2)) y ∂closedLaw b W np ≤
      ENNReal.ofReal K' := by
    rw [← lintegral_congr_ae (indicator_ae_eq_of_ae_eq_set hAA)]
    exact hXW.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hΛ : ∫⁻ y, ENNReal.ofReal ((W : ℝ)⁻¹ * lam y.1.1) ∂closedLaw b W np ≤
      ENNReal.ofReal θ₁ := by
    have hm1 : Measurable fun x : ProbedPath W np => ENNReal.ofReal ((W : ℝ)⁻¹ * lam x.1) :=
      (measurable_const.mul (hlam.comp measurable_fst)).ennreal_ofReal
    rw [Birth.lintegral_closedLaw_fst hm1, Birth.lintegral_probedPathLaw_fst
      (f := fun ω => ENNReal.ofReal ((W : ℝ)⁻¹ * lam ω)) (measurable_const.mul hlam).ennreal_ofReal]
    exact hSq.trans (ENNReal.ofReal_le_ofReal hsq)
  have hL : ∫⁻ y, ENNReal.ofReal (ℓ y ^ 2) ∂closedLaw b W np ≤
      ENNReal.ofReal (2 * (m i * θ₁)) := by
    refine (lintegral_closed_leak_le hb0 hb hE1 hE2 hW1 s h hh0 hh1 (by omega) τ m i).trans ?_
    rw [lintegral_newborn_far_eq b E τ m i hm hlt, ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_mul hm]
    exact mul_le_mul_right (mul_le_mul_right hF _) _
  -- the pointwise split
  have hpt : ∀ y, A'.indicator (fun y => ENNReal.ofReal ‖star (u y) ⬝ᵥ (Cm y)ᴴ *ᵥ V y‖) y ≤
      A'.indicator (fun y => ENNReal.ofReal ‖star (u y) ⬝ᵥ V y‖) y +
        ENNReal.ofReal (δ / 2) * A'.indicator (fun y => ENNReal.ofReal (l2 (Fc y) ^ 2)) y +
        ENNReal.ofReal (1 / (2 * δ)) * ENNReal.ofReal (ℓ y ^ 2) := by
    intro y
    by_cases hy : y ∈ A'
    · simp only [Set.indicator_of_mem hy]
      have h1 : ‖star (u y) ⬝ᵥ (Cm y)ᴴ *ᵥ V y‖ ≤ ‖star (u y) ⬝ᵥ V y‖ + l2 (u y) * ℓ y := by
        rw [show (Cm y)ᴴ *ᵥ V y = V y + ((Cm y)ᴴ *ᵥ V y - V y) by abel, dotProduct_add]
        exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_dot_le _ _))
      have h2 : l2 (u y) * ℓ y ≤ l2 (Fc y) * ℓ y :=
        mul_le_mul_of_nonneg_right (l2_gramQ_le σ _) (l2_nonneg _)
      have h3 : l2 (Fc y) * ℓ y ≤ δ / 2 * l2 (Fc y) ^ 2 + 1 / (2 * δ) * ℓ y ^ 2 := by
        have := sq_nonneg (δ * l2 (Fc y) - ℓ y)
        rw [show δ / 2 * l2 (Fc y) ^ 2 + 1 / (2 * δ) * ℓ y ^ 2 =
          (δ ^ 2 * l2 (Fc y) ^ 2 + ℓ y ^ 2) / (2 * δ) by field_simp,
          le_div_iff₀ (by positivity)]
        nlinarith
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    · simp only [Set.indicator_of_notMem hy, zero_add, mul_zero]
      exact zero_le
  -- the overlap with the unclosed column
  have hSu : ∀ y a, updProbe i y a ∈ A' ↔ y ∈ A' := fun y a =>
    b3AliveM_updProbe b E s h τ m R le_rfl (Vs W) y a
  have huu : ∀ y a, u (updProbe i y a) = u y := by
    intro y a
    show gramQ W σ *ᵥ (fun z => b3ClosedFrameAt b E s h τ m W (k + 1) (Vs W) (updProbe i y a) z c) =
      gramQ W σ *ᵥ (fun z => b3ClosedFrameAt b E s h τ m W (k + 1) (Vs W) y z c)
    rw [closedCol_updProbe b E s h τ m hc]
  have hT1 : ∫⁻ y, A'.indicator (fun y => ENNReal.ofReal ‖star (u y) ⬝ᵥ V y‖) y
      ∂closedLaw b W np ≤
      ENNReal.ofReal (δ / 2) * ∫⁻ y, A'.indicator (fun y => ENNReal.ofReal (l2 (Fc y) ^ 2)) y
        ∂closedLaw b W np +
      ENNReal.ofReal (m i / (2 * δ)) * ∫⁻ y, ENNReal.ofReal ((W : ℝ)⁻¹ * lam y.1.1)
        ∂closedLaw b W np := by
    refine (lintegral_resample_le b E τ m i hlt hA' hSu hu huu).trans ?_
    have hX2 : Measurable fun y => A'.indicator (fun y => ENNReal.ofReal (l2 (Fc y) ^ 2)) y :=
      ((continuous_l2.measurable.comp hFc).pow_const 2).ennreal_ofReal.indicator hA'
    have hlm : Measurable fun y : ProbedPath W np × ℝ => ENNReal.ofReal ((W : ℝ)⁻¹ * lam y.1.1) :=
      (measurable_const.mul (hlam.comp (measurable_fst.comp measurable_fst))).ennreal_ofReal
    rw [← lintegral_const_mul _ hX2, ← lintegral_const_mul (ENNReal.ofReal (m i / (2 * δ))) hlm,
      ← lintegral_add_left (hX2.const_mul _)]
    refine lintegral_mono fun y => ?_
    by_cases hy : y ∈ A'
    · simp only [Set.indicator_of_mem hy]
      have h1 := l2_conj_mulVec_le (newR_mul_conj b E hlt y.1.1) (u y)
      have h2 : l2 (u y) ≤ l2 (Fc y) := l2_gramQ_le σ _
      have hl0 : 0 ≤ lam y.1.1 := Real.sqrt_nonneg _
      have hmW : 0 ≤ m i / W := div_nonneg hm (Nat.cast_nonneg W)
      have h3 : Real.sqrt (m i / W) * l2 ((newR b E W (k + 1) p y.1.1)ᴴ *ᵥ u y) ≤
          Real.sqrt (m i / W * lam y.1.1) * l2 (u y) := by
        rw [Real.sqrt_mul hmW, mul_assoc]
        exact mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
      have h4 := sqrt_mul_le_amgm (x := l2 (u y)) (mul_nonneg hmW hl0) hδ
      have h5 : δ / 2 * l2 (u y) ^ 2 ≤ δ / 2 * l2 (Fc y) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (l2_nonneg _) h2 2) (by positivity)
      have h6 : m i / W * lam y.1.1 / (2 * δ) = m i / (2 * δ) * ((W : ℝ)⁻¹ * lam y.1.1) := by
        field_simp
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    · simp only [Set.indicator_of_notMem hy, mul_zero, zero_add]
      exact zero_le
  -- assembly
  rw [hLHS]
  refine (lintegral_mono hpt).trans ?_
  have hm1 : Measurable fun y => A'.indicator (fun y => ENNReal.ofReal ‖star (u y) ⬝ᵥ V y‖) y := by
    refine Measurable.indicator ?_ hA'
    simp only [dotProduct, Pi.star_apply]
    exact (Finset.measurable_sum _ fun z _ => ((Complex.continuous_conj.measurable.comp
      ((measurable_pi_apply z).comp hu)).mul
        ((measurable_pi_apply z).comp hVm))).norm.ennreal_ofReal
  have hX2 : Measurable fun y => A'.indicator (fun y => ENNReal.ofReal (l2 (Fc y) ^ 2)) y :=
    ((continuous_l2.measurable.comp hFc).pow_const 2).ennreal_ofReal.indicator hA'
  rw [lintegral_add_left (f := fun y => A'.indicator (fun y => ENNReal.ofReal
      ‖star (u y) ⬝ᵥ V y‖) y + ENNReal.ofReal (δ / 2) *
        A'.indicator (fun y => ENNReal.ofReal (l2 (Fc y) ^ 2)) y) (hm1.add (hX2.const_mul _)),
    lintegral_add_left (f := fun y => A'.indicator (fun y => ENNReal.ofReal
      ‖star (u y) ⬝ᵥ V y‖) y) hm1,
    lintegral_const_mul _ hX2, lintegral_const_mul _ (hℓ.pow_const 2).ennreal_ofReal]
  calc _ ≤ (ENNReal.ofReal (δ / 2) * ENNReal.ofReal K' +
          ENNReal.ofReal (m i / (2 * δ)) * ENNReal.ofReal θ₁) +
        ENNReal.ofReal (δ / 2) * ENNReal.ofReal K' +
        ENNReal.ofReal (1 / (2 * δ)) * ENNReal.ofReal (2 * (m i * θ₁)) := by
        refine add_le_add (add_le_add (hT1.trans ?_) (mul_le_mul_right hX' _))
          (mul_le_mul_right hL _)
        exact add_le_add (mul_le_mul_right hX' _) (mul_le_mul_right hΛ _)
    _ = ENNReal.ofReal (δ / 2 * K' + m i / (2 * δ) * θ₁ + δ / 2 * K' +
          1 / (2 * δ) * (2 * (m i * θ₁))) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
            (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal θ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have e1 : δ / 2 * K' + δ / 2 * K' = θ / 2 * (K' / (K' + 1)) := by
          rw [hδdef]; field_simp; ring
        have e2 : m i / (2 * δ) * θ₁ + 1 / (2 * δ) * (2 * (m i * θ₁)) =
            θ / 2 * (3 * m i / (3 * m i + 1)) := by
          rw [hθ₁def]; field_simp; ring
        have h1 : θ / 2 * (K' / (K' + 1)) ≤ θ / 2 :=
          mul_le_of_le_one_right (by positivity) ((div_le_one (by positivity)).mpr (by linarith))
        have h2 : θ / 2 * (3 * m i / (3 * m i + 1)) ≤ θ / 2 :=
          mul_le_of_le_one_right (by positivity) ((div_le_one (by positivity)).mpr (by linarith))
        linarith

theorem enorm_indicator_gramEntry (b E s h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (n : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (A : Set (ProbedPath W np × ℝ)) (σ : Fin 2) (k l : SrcCol K (Fin np))
    (y : ProbedPath W np × ℝ) :
    ‖A.indicator (fun y => gramEntry (σ, k, l) (b3ClosedGramAt b E s h τ m W n Vs y)) y‖ₑ =
        A.indicator (fun y => ENNReal.ofReal ‖star (gramQ W σ *ᵥ
          fun z => b3ClosedFrameAt b E s h τ m W n Vs y z k) ⬝ᵥ
            fun z => b3ClosedFrameAt b E s h τ m W n Vs y z l‖) y ∧
      ‖A.indicator (fun y => gramEntry (σ, k, l) (b3ClosedGramAt b E s h τ m W n Vs y)) y‖ₑ =
        A.indicator (fun y => ENNReal.ofReal ‖star (gramQ W σ *ᵥ
          fun z => b3ClosedFrameAt b E s h τ m W n Vs y z l) ⬝ᵥ
            fun z => b3ClosedFrameAt b E s h τ m W n Vs y z k‖) y := by
  have hN := norm_gramEntry_eq σ k l (b3ClosedFrameAt b E s h τ m W n Vs y)
  by_cases hy : y ∈ A
  · simp only [Set.indicator_of_mem hy]
    rw [← ofReal_norm]
    exact ⟨by rw [← hN.1]; rfl, by rw [← hN.2]; rfl⟩
  · simp [Set.indicator_of_notMem hy]

/-- **`ComplexBirthCrossGram`** from the input hypotheses and the one-step moment hypothesis
`ComplexBirthOtherColL2`. -/
theorem complexBirthCrossGram_of (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hX : ComplexBirthOtherColL2) : ComplexBirthCrossGram := by
  intro b E np τ m T s h K Vs hD R θ hθ e
  obtain ⟨σ, k, l⟩ := e
  have core := fun (i : Fin np) (c : SrcCol K (Fin np)) (hc : c ≠ Sum.inr i) =>
    lintegral_cross_core hMT hGA hX hD R θ hθ i hc σ
  rcases k with k | ik <;> rcases l with l | il
  · exact Eventually.of_forall fun W j _ _ hc _ => absurd hc (by simp [IsNewCoord, IsNewCol])
  · filter_upwards [core il (Sum.inl k) Sum.inl_ne_inr] with W hW j hj1 hj2 hc _
    have hij : ⌊(W : ℝ) * τ il⌋₊ = j := by
      rcases hc with hc | hc
      · exact absurd hc (by simp [IsNewCol])
      · exact hc
    refine le_trans (le_of_eq (lintegral_congr fun y => ?_)) (hW j hj1 hj2 hij)
    exact (enorm_indicator_gramEntry b E s h τ m (j + 1) (Vs W) _ σ _ _ y).1
  · filter_upwards [core ik (Sum.inl l) Sum.inl_ne_inr] with W hW j hj1 hj2 hc _
    have hij : ⌊(W : ℝ) * τ ik⌋₊ = j := by
      rcases hc with hc | hc
      · exact hc
      · exact absurd hc (by simp [IsNewCol])
    refine le_trans (le_of_eq (lintegral_congr fun y => ?_)) (hW j hj1 hj2 hij)
    exact (enorm_indicator_gramEntry b E s h τ m (j + 1) (Vs W) _ σ _ _ y).2
  · by_cases hii : ik = il
    · subst hii
      refine Eventually.of_forall fun W j _ _ hc hd => absurd ?_ hd
      have hij : ⌊(W : ℝ) * τ ik⌋₊ = j := by rcases hc with hc | hc <;> exact hc
      exact ⟨ik, hij, Or.inr ⟨σ, rfl⟩⟩
    · have h1 : (Sum.inr ik : SrcCol K (Fin np)) ≠ Sum.inr il := fun e => hii (Sum.inr_injective e)
      have h2 : (Sum.inr il : SrcCol K (Fin np)) ≠ Sum.inr ik := fun e => h1 e.symm
      filter_upwards [core il (Sum.inr ik) h1, core ik (Sum.inr il) h2] with W hW1 hW2 j hj1 hj2
        hc _
      rcases hc with hc | hc
      · refine le_trans (le_of_eq (lintegral_congr fun y => ?_)) (hW2 j hj1 hj2 hc)
        exact (enorm_indicator_gramEntry b E s h τ m (j + 1) (Vs W) _ σ _ _ y).2
      · refine le_trans (le_of_eq (lintegral_congr fun y => ?_)) (hW1 j hj1 hj2 hc)
        exact (enorm_indicator_gramEntry b E s h τ m (j + 1) (Vs W) _ σ _ _ y).1

end BlockBand.SourceProcess.PhysApprox.B3
