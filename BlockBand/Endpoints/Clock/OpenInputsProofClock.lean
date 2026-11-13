module

public import BlockBand.Endpoints.Clock.OpenInputsProofJet
public import BlockBand.Endpoints.Clock.OpenInputsProofDefs
public import BlockBand.Endpoints.Clock.ClockMixingStep

/-!
# The open-inputs lemma: iteration of the clock moments

This is the iteration of the clock moments in the proof of the open-inputs lemma (Step 6, before
the exit, and Step 7, the crude bound and the exit set, in the paper's proof). From the
conditional clock-moment step `ClockStepBound`, with `u_j = W⁻¹ Re Tr Y_j^q` (`clockU`) along the
one-ended path, we prove `clock_moment_raw`: for `j ≤ TW`,
`E u_j^P ≤ (A(j+1))^P + G^j P(G_jᶜ)^{1/2}`, where `G_j = goodSet` is the "no exit" event.
* Crude bound (Step 7, from the unrestricted fresh norm bounds): `E u_j^m ≤ G_m^j` at every order,
  by iterating `E(u₊^m | 𝓕_j) ≤ C(u_j^m + 1)` (`crude_iter`).
* Before the exit (Step 6): `M_j = E[1_{G_j}(1 + Kδ₀(X_j)) u_j^P]` satisfies
  `M_{J+n} ≤ ((1+C/W)ⁿ (A₀ + nC'))^P` (`weighted_iter`). A Hölder step
  `E[1_G u^{P-1}] ≤ M^{1-1/P}` is replaced by the elementary bound `u^{P-1} ≤ u^P/a + a^{P-1}`
  at the current majorant `a` (with the same conclusion: `M_j^{1/p}` grows by at most a constant
  per step); `(1+C/W)ⁿ ≤ e^{CT}` for `n ≤ TW`.
* The exit set: Cauchy–Schwarz with the crude `2P`-th moment (Step 7).

The conversion of the exceptional term into `O(W⁻¹)` (the exit probability) is done in the
assembly.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
  BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal NNReal Matrix.Norms.L2Operator ComplexOrder

namespace OpenInputsProof

/-!
## Lintegrals along the chain
-/

section Generic

variable {S : Type*} [MeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν]

/-- `ω ↦ (init ω, last ω)` is a measurable embedding. -/
theorem measurableEmbedding_initLast (j : ℕ) :
    MeasurableEmbedding (fun ω : Fin (j + 1) → S => (Fin.init ω, ω (Fin.last j))) := by
  have h := ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (j + 1) => S) (Fin.last j)).trans
    MeasurableEquiv.prodComm).measurableEmbedding
  convert h using 1
  funext ω
  refine Prod.ext ?_ ?_
  · funext k
    simp [MeasurableEquiv.piFinSuccAbove, Fin.init, MeasurableEquiv.prodComm]
  · simp [MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodComm]

/-- **Tonelli along the chain** (an inequality, no measurability needed). -/
theorem lintegral_chain_le (j : ℕ) {F : (Fin (j + 1) → S) → ℝ≥0∞}
    {H : (Fin j → S) × S → ℝ≥0∞}
    (hFH : ∀ᵐ ω ∂(Measure.pi fun _ : Fin (j + 1) => ν), F ω ≤ H (Fin.init ω, ω (Fin.last j))) :
    ∫⁻ ω, F ω ∂(Measure.pi fun _ : Fin (j + 1) => ν) ≤
      ∫⁻ x, ∫⁻ y, H (x, y) ∂ν ∂(Measure.pi fun _ : Fin j => ν) := by
  refine (lintegral_mono_ae hFH).trans ?_
  rw [(ZeroEntranceProb.measurePreserving_initLast ν j).lintegral_comp_emb
    (measurableEmbedding_initLast j) H]
  exact lintegral_prod_le H

/-- `∫⁻ (a f + c) ≤ a ∫⁻ f + c` on a probability space. -/
theorem lintegral_affine_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f g : α → ℝ≥0∞} {a c : ℝ≥0∞} (ha : a ≠ ∞)
    (h : ∀ᵐ x ∂μ, g x ≤ a * f x + c) : ∫⁻ x, g x ∂μ ≤ a * ∫⁻ x, f x ∂μ + c := by
  refine (lintegral_mono_ae h).trans (le_of_eq ?_)
  rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ ha, lintegral_const,
    measure_univ, mul_one]

end Generic

/-!
## Real inequalities
-/

theorem young_pow {u a : ℝ} (hu : 0 ≤ u) (ha : 0 < a) {P : ℕ} (hP : 1 ≤ P) :
    u ^ (P - 1) ≤ u ^ P / a + a ^ (P - 1) := by
  have hPe : P = (P - 1) + 1 := by omega
  rcases le_or_gt u a with h | h
  · have h1 : u ^ (P - 1) ≤ a ^ (P - 1) := pow_le_pow_left₀ hu h _
    have h2 : 0 ≤ u ^ P / a := by positivity
    linarith
  · have h1 : u ^ (P - 1) ≤ u ^ P / a := by
      rw [le_div_iff₀ ha]
      conv_rhs => rw [hPe, pow_succ]
      exact mul_le_mul_of_nonneg_left h.le (by positivity)
    have h2 : 0 ≤ a ^ (P - 1) := by positivity
    linarith

theorem bernoulli_pow {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) {P : ℕ} (hP : 1 ≤ P) :
    a ^ P + P * c * a ^ (P - 1) ≤ (a + c) ^ P := by
  have hPe : P = (P - 1) + 1 := by omega
  have hca : 0 ≤ c / a := by positivity
  have h1 := one_add_mul_le_pow (a := c / a) (by linarith) P
  have h2 : (a + c) ^ P = a ^ P * (1 + c / a) ^ P := by
    rw [← mul_pow]; congr 1; field_simp
  have h3 : a ^ P * (1 + P * (c / a)) = a ^ P + P * c * a ^ (P - 1) := by
    have : a ^ P = a ^ (P - 1) * a := by conv_lhs => rw [hPe, pow_succ]
    rw [this]; field_simp
  rw [h2, ← h3]
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

/-!
## The clock along the chain
-/

section Clock

variable {W : ℕ} (b E : ℝ) (q : ℝ → ℝ) (D : Matrix (Fin W) (Fin W) ℂ)

theorem clockU_succ (j : ℕ) (ω : Fin (j + 1) → OneEndedLayer W) :
    clockU (oneEndedY b E q D (j + 1) ω) =
      nextClockU b E (q (((j + 1 : ℕ) : ℝ) / W)) (oneEndedX E D j (Fin.init ω))
        (oneEndedY b E q D j (Fin.init ω)) (ω (Fin.last j)) := rfl

theorem measurable_clockU_chain (j : ℕ) :
    Measurable (fun ω => clockU (oneEndedY b E q D j ω)) :=
  measurable_const.mul (Complex.measurable_re.comp
    (ClockMixingProb.meas_trace (ClockMixingProb.meas_Y b E q D j)))

variable {b E q D}

theorem clockU_nonneg' {Y : Matrix (Fin W) (Fin W) ℂ} (hY : Y.PosSemidef) : 0 ≤ clockU Y := by
  unfold clockU
  have h := (Complex.nonneg_iff.mp hY.trace_nonneg).1
  have : (0 : ℝ) ≤ (W : ℝ)⁻¹ := by positivity
  exact mul_nonneg this h

theorem clockU_chain_nonneg (hq0 : ∀ x, 0 ≤ q x) (j : ℕ) (ω : Fin j → OneEndedLayer W) :
    0 ≤ clockU (oneEndedY b E q D j ω) :=
  clockU_nonneg' (ClockMixingProb.Y_posSemidef b E hq0 D j ω)

/-- **Crude moments** (Step 7): `E u_j^m ≤ (2 max(C,1))^j` from the unrestricted step. -/
theorem crude_iter (hq0 : ∀ x, 0 ≤ q x) {Kq : ℝ} (hqK : ∀ x, q x ≤ Kq) {m : ℕ} {C : ℝ}
    (hcr : ∀ X : Matrix (Fin W) (Fin W) ℂ, X.IsHermitian →
      ∀ Y : Matrix (Fin W) (Fin W) ℂ, Y.PosSemidef → ∀ w : ℝ, 0 ≤ w → w ≤ Kq →
        ∫⁻ ω, ENNReal.ofReal (nextClockU b E w X Y ω ^ m) ∂freshLaw W b ≤
          ENNReal.ofReal (C * (clockU Y ^ m + 1)))
    (hD : D.IsHermitian) :
    ∀ j : ℕ, ∫⁻ ω, ENNReal.ofReal (clockU (oneEndedY b E q D j ω) ^ m) ∂oneEndedLaw W b j ≤
      ENNReal.ofReal ((2 * max C 1) ^ j) := by
  have hc1 : 1 ≤ max C 1 := le_max_right _ _
  intro j
  induction j with
  | zero =>
    have h0 : ∀ ω : Fin 0 → OneEndedLayer W, clockU (oneEndedY b E q D 0 ω) = 0 := by
      intro ω; simp [clockU, oneEndedY]
    simp only [h0, pow_zero]
    refine (lintegral_mono fun _ => ENNReal.ofReal_le_ofReal
      (pow_le_one₀ (le_refl 0) zero_le_one)).trans ?_
    rw [lintegral_const, measure_univ, mul_one]
  | succ j ih =>
    have hstep := lintegral_chain_le (freshLaw W b) j
      (F := fun ω => ENNReal.ofReal (clockU (oneEndedY b E q D (j + 1) ω) ^ m))
      (H := fun xy => ENNReal.ofReal (nextClockU b E (q (((j + 1 : ℕ) : ℝ) / W))
        (oneEndedX E D j xy.1) (oneEndedY b E q D j xy.1) xy.2 ^ m))
      (Eventually.of_forall fun ω => le_rfl)
    refine hstep.trans ?_
    have h2 : ∫⁻ x, ∫⁻ y, ENNReal.ofReal (nextClockU b E (q (((j + 1 : ℕ) : ℝ) / W))
        (oneEndedX E D j x) (oneEndedY b E q D j x) y ^ m) ∂freshLaw W b ∂oneEndedLaw W b j ≤
        ENNReal.ofReal (max C 1) * ∫⁻ x, ENNReal.ofReal (clockU (oneEndedY b E q D j x) ^ m)
          ∂oneEndedLaw W b j + ENNReal.ofReal (max C 1) := by
      refine lintegral_affine_le ENNReal.ofReal_ne_top ?_
      filter_upwards [ZeroEntranceProb.ae_X_isHermitian b E hD j] with x hx
      refine (hcr _ hx _ (ClockMixingProb.Y_posSemidef b E hq0 D j x) _ (hq0 _) (hqK _)).trans ?_
      have hu := pow_nonneg (clockU_chain_nonneg (b := b) (E := E) (D := D) hq0 j x) m
      rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_add (by positivity) (by linarith)]
      refine ENNReal.ofReal_le_ofReal ?_
      have : C * (clockU (oneEndedY b E q D j x) ^ m + 1) ≤
          max C 1 * (clockU (oneEndedY b E q D j x) ^ m + 1) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
      linarith
    refine h2.trans ?_
    have hG : 1 ≤ (2 * max C 1) ^ j := one_le_pow₀ (by linarith)
    calc ENNReal.ofReal (max C 1) * ∫⁻ x, ENNReal.ofReal (clockU (oneEndedY b E q D j x) ^ m)
          ∂oneEndedLaw W b j + ENNReal.ofReal (max C 1)
        ≤ ENNReal.ofReal (max C 1) * ENNReal.ofReal ((2 * max C 1) ^ j) +
            ENNReal.ofReal (max C 1) := by gcongr
      _ = ENNReal.ofReal (max C 1 * (2 * max C 1) ^ j + max C 1) := by
          rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_add (by positivity)
            (by linarith)]
      _ ≤ ENNReal.ofReal ((2 * max C 1) ^ (j + 1)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [pow_succ]
          nlinarith

end Clock

/-- The algebra of one weighted step at the majorant `a ≥ 1`. -/
theorem weighted_real {u δ K C W a : ℝ} (hu : 0 ≤ u) (hδ : 0 ≤ δ) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hW : 0 < W) (ha : 1 ≤ a) {P : ℕ} (hP : 1 ≤ P) :
    (1 + C / W) * (1 + K * δ) * u ^ P + C * (u ^ (P - 1) + 1) ≤
      (1 + C / W + C / a) * ((1 + K * δ) * u ^ P) + 2 * C * a ^ (P - 1) := by
  have ha0 : 0 < a := by linarith
  have hy := young_pow hu ha0 hP
  have h1 : 1 ≤ a ^ (P - 1) := one_le_pow₀ ha
  have hKd : 1 ≤ 1 + K * δ := by have := mul_nonneg hK hδ; linarith
  have huP : 0 ≤ u ^ P := pow_nonneg hu P
  have h2 : u ^ P / a ≤ (1 + K * δ) * u ^ P / a := by
    apply div_le_div_of_nonneg_right _ ha0.le
    nlinarith
  have h3 : C * (u ^ (P - 1) + 1) ≤ C * ((1 + K * δ) * u ^ P / a) + 2 * C * a ^ (P - 1) := by
    have : u ^ (P - 1) + 1 ≤ (1 + K * δ) * u ^ P / a + 2 * a ^ (P - 1) := by linarith
    have := mul_le_mul_of_nonneg_left this hC
    linarith
  have e : (1 + C / W + C / a) * ((1 + K * δ) * u ^ P) =
      (1 + C / W) * (1 + K * δ) * u ^ P + C * ((1 + K * δ) * u ^ P / a) := by
    field_simp
  linarith

/-- The majorant recursion: `(1+c)a^P + 3C a^{P-1} ≤ ((1+c)(a + C'))^P` when `PC' ≥ 3C`. -/
theorem majorant_step {a c C C' : ℝ} (ha : 1 ≤ a) (hc : 0 ≤ c) (hC : 0 ≤ C) (hC' : 0 ≤ C')
    {P : ℕ}
    (hP : 1 ≤ P) (hPC : 3 * C ≤ P * C') :
    (1 + c) * a ^ P + 3 * C * a ^ (P - 1) ≤ ((1 + c) * (a + C')) ^ P := by
  have ha0 : 0 < a := by linarith
  have hb := bernoulli_pow ha0 hC' hP
  have h1 : 3 * C * a ^ (P - 1) ≤ P * C' * a ^ (P - 1) :=
    mul_le_mul_of_nonneg_right hPC (by positivity)
  have h2 : (1 + c) * a ^ P + 3 * C * a ^ (P - 1) ≤ (1 + c) * (a + C') ^ P := by
    have : a ^ P + 3 * C * a ^ (P - 1) ≤ (a + C') ^ P := by linarith
    have hx : 0 ≤ 3 * C * a ^ (P - 1) := by positivity
    have h3 : 3 * C * a ^ (P - 1) ≤ (1 + c) * (3 * C * a ^ (P - 1)) := by
      nlinarith [mul_nonneg hc hx]
    have h5 : (1 + c) * (a ^ P + 3 * C * a ^ (P - 1)) ≤ (1 + c) * (a + C') ^ P :=
      mul_le_mul_of_nonneg_left this (by linarith)
    nlinarith [mul_nonneg hc (pow_nonneg ha0.le P)]
  have h4 : (1 + c) ≤ (1 + c) ^ P := le_self_pow₀ (by linarith) (by omega)
  rw [mul_pow]
  exact h2.trans (mul_le_mul_of_nonneg_right h4 (by positivity))

section Weighted

variable {W : ℕ} {b E : ℝ} {q : ℝ → ℝ} {D : Matrix (Fin W) (Fin W) ℂ}

/-- `M_j`'s integrand: `1_{G_j} (1 + K δ₀(X_j)) u_j^P`. -/
def weightFun (b E : ℝ) (q : ℝ → ℝ) (D : Matrix (Fin W) (Fin W) ℂ) (r₀ : ℝ) (J : ℕ) (K : ℝ)
    (P : ℕ) (j : ℕ) (ω : Fin j → OneEndedLayer W) : ℝ≥0∞ :=
  (goodSet b E D r₀ J j).indicator
    (fun ω => ENNReal.ofReal ((1 + K * chainD0 b E D j ω) * clockU (oneEndedY b E q D j ω) ^ P)) ω

/-- **Step 6 iterated before the exit**: `M_{J+n} ≤ ((1+C/W)ⁿ (A₀ + nC'))^P`. -/
theorem weighted_iter (hq0 : ∀ x, 0 ≤ q x) {Kq : ℝ} (hqK : ∀ x, q x ≤ Kq) {K C r₀ : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hW : 0 < W) {P : ℕ} (hP : 1 ≤ P)
    (hwt : ∀ X : Matrix (Fin W) (Fin W) ℂ, X.IsHermitian → jetDistance0 b E X ≤ r₀ →
      ∀ Y : Matrix (Fin W) (Fin W) ℂ, Y.PosSemidef → ∀ w : ℝ, 0 ≤ w → w ≤ Kq →
        ∫⁻ ω, ENNReal.ofReal ((1 + K * jetDistance0 b E (freshSchur E X ω)) *
            nextClockU b E w X Y ω ^ P) ∂freshLaw W b ≤
          ENNReal.ofReal ((1 + C / W) * (1 + K * jetDistance0 b E X) * clockU Y ^ P +
            C * (clockU Y ^ (P - 1) + 1)))
    (hD : D.IsHermitian) (J : ℕ) {A₀ C' : ℝ} (hA₀ : 1 ≤ A₀) (hC' : 0 ≤ C')
    (hPC : 3 * C ≤ P * C')
    (h0 : ∫⁻ ω, weightFun b E q D r₀ J K P J ω ∂oneEndedLaw W b J ≤ ENNReal.ofReal (A₀ ^ P)) :
    ∀ n : ℕ, ∫⁻ ω, weightFun b E q D r₀ J K P (J + n) ω ∂oneEndedLaw W b (J + n) ≤
      ENNReal.ofReal (((1 + C / W) ^ n * (A₀ + n * C')) ^ P) := by
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hcW : 0 ≤ C / W := by positivity
  intro n
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    set a := (1 + C / W) ^ n * (A₀ + n * C') with ha
    have ha1 : 1 ≤ a := by
      have h1 : 1 ≤ (1 + C / W) ^ n := one_le_pow₀ (by linarith)
      have hnC : 0 ≤ (n : ℝ) * C' := by positivity
      have h2 : 1 ≤ A₀ + n * C' := by linarith
      nlinarith
    set j := J + n with hj
    set w := q (((j + 1 : ℕ) : ℝ) / W) with hw
    -- Tonelli along the chain
    have hstep := lintegral_chain_le (freshLaw W b) j
      (F := fun ω => weightFun b E q D r₀ J K P (j + 1) ω)
      (H := fun xy => (goodSet b E D r₀ J j).indicator (fun x => ENNReal.ofReal
        ((1 + K * jetDistance0 b E (freshSchur E (oneEndedX E D j x) xy.2)) *
          nextClockU b E w (oneEndedX E D j x) (oneEndedY b E q D j x) xy.2 ^ P)) xy.1)
      (Eventually.of_forall fun ω => ?_)
    swap
    · unfold weightFun
      by_cases hω : ω ∈ goodSet b E D r₀ J (j + 1)
      · rw [Set.indicator_of_mem hω, Set.indicator_of_mem (init_mem_goodSet hω)]
        exact le_rfl
      · rw [Set.indicator_of_notMem hω]; exact zero_le
    -- the conditional bound
    have hcond : ∫⁻ x, ∫⁻ y, (goodSet b E D r₀ J j).indicator (fun x => ENNReal.ofReal
        ((1 + K * jetDistance0 b E (freshSchur E (oneEndedX E D j x) y)) *
          nextClockU b E w (oneEndedX E D j x) (oneEndedY b E q D j x) y ^ P)) x
          ∂freshLaw W b ∂oneEndedLaw W b j ≤
        ENNReal.ofReal (1 + C / W + C / a) *
          ∫⁻ x, weightFun b E q D r₀ J K P j x ∂oneEndedLaw W b j +
          ENNReal.ofReal (2 * C * a ^ (P - 1)) := by
      refine lintegral_affine_le ENNReal.ofReal_ne_top ?_
      filter_upwards [ZeroEntranceProb.ae_X_isHermitian b E hD j] with x hx
      unfold weightFun
      by_cases hg : x ∈ goodSet b E D r₀ J j
      · simp only [Set.indicator_of_mem hg]
        have hδ := chainD0_le_of_mem_goodSet hg (by omega)
        have hY := ClockMixingProb.Y_posSemidef b E hq0 D j x
        refine (hwt _ hx hδ _ hY w (hq0 _) (hqK _)).trans ?_
        have hu := clockU_nonneg' hY
        have hδ0 : 0 ≤ chainD0 b E D j x := norm_nonneg _
        have hreal := weighted_real hu hδ0 hK hC hWr ha1 hP
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
        exact ENNReal.ofReal_le_ofReal hreal
      · simp only [Set.indicator_of_notMem hg, lintegral_zero]
        exact zero_le
    refine hstep.trans (hcond.trans ?_)
    calc ENNReal.ofReal (1 + C / W + C / a) *
          ∫⁻ x, weightFun b E q D r₀ J K P j x ∂oneEndedLaw W b j +
          ENNReal.ofReal (2 * C * a ^ (P - 1))
        ≤ ENNReal.ofReal (1 + C / W + C / a) * ENNReal.ofReal (a ^ P) +
            ENNReal.ofReal (2 * C * a ^ (P - 1)) := by gcongr
      _ = ENNReal.ofReal ((1 + C / W + C / a) * a ^ P + 2 * C * a ^ (P - 1)) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
            (by positivity)]
      _ ≤ ENNReal.ofReal (((1 + C / W) ^ (n + 1) * (A₀ + ((n + 1 : ℕ) : ℝ) * C')) ^ P) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have ha0 : 0 < a := by linarith
          have hPe : P = (P - 1) + 1 := by omega
          have e1 : C / a * a ^ P = C * a ^ (P - 1) := by
            conv_lhs => rw [hPe, pow_succ]
            field_simp
          have h1 : (1 + C / W + C / a) * a ^ P + 2 * C * a ^ (P - 1) =
              (1 + C / W) * a ^ P + 3 * C * a ^ (P - 1) := by
            rw [add_mul, e1]; ring
          rw [h1]
          refine (majorant_step ha1 hcW hC hC' hP hPC).trans ?_
          refine pow_le_pow_left₀ (by positivity) ?_ P
          have hpow : 1 ≤ (1 + C / W) ^ n := one_le_pow₀ (by linarith)
          rw [ha, pow_succ]
          push_cast
          have : (1 + C / W) * C' ≤ (1 + C / W) * ((1 + C / W) ^ n * C') := by
            refine mul_le_mul_of_nonneg_left ?_ (by linarith)
            nlinarith
          nlinarith

end Weighted

section Final

variable {W : ℕ} {b E : ℝ} {q : ℝ → ℝ} {D : Matrix (Fin W) (Fin W) ℂ}

/-- The exceptional part by Cauchy–Schwarz and the crude `2P`-th moment. -/
theorem exceptional_part (hq0 : ∀ x, 0 ≤ q x) {r₀ : ℝ} {J P j : ℕ} {G₂ : ℝ} (hG₂ : 1 ≤ G₂)
    (h2 : ∫⁻ ω, ENNReal.ofReal (clockU (oneEndedY b E q D j ω) ^ (2 * P)) ∂oneEndedLaw W b j ≤
      ENNReal.ofReal (G₂ ^ j)) :
    ∫⁻ ω in (goodSet b E D r₀ J j)ᶜ, ENNReal.ofReal (clockU (oneEndedY b E q D j ω) ^ P)
        ∂oneEndedLaw W b j ≤
      ENNReal.ofReal (G₂ ^ j) * oneEndedLaw W b j (goodSet b E D r₀ J j)ᶜ ^ (1 / 2 : ℝ) := by
  have hm := (measurableSet_goodSet (b := b) (E := E) (D := D) r₀ J j).compl
  have hf : Measurable (fun ω => ENNReal.ofReal (clockU (oneEndedY b E q D j ω) ^ P)) :=
    ENNReal.measurable_ofReal.comp ((measurable_clockU_chain b E q D j).pow_const P)
  rw [← lintegral_indicator hm]
  have heq : (goodSet b E D r₀ J j)ᶜ.indicator
      (fun ω => ENNReal.ofReal (clockU (oneEndedY b E q D j ω) ^ P)) =
      (fun ω => ENNReal.ofReal (clockU (oneEndedY b E q D j ω) ^ P)) *
        (goodSet b E D r₀ J j)ᶜ.indicator 1 := by
    funext ω
    by_cases h : ω ∈ (goodSet b E D r₀ J j)ᶜ
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  rw [heq]
  refine (ENNReal.lintegral_mul_le_Lp_mul_Lq _ Real.HolderConjugate.two_two hf.aemeasurable
    ((measurable_one.indicator hm).aemeasurable)).trans ?_
  have hsq : ∀ ω, ENNReal.ofReal (clockU (oneEndedY b E q D j ω) ^ P) ^ (2 : ℝ) =
      ENNReal.ofReal (clockU (oneEndedY b E q D j ω) ^ (2 * P)) := by
    intro ω
    rw [ENNReal.ofReal_rpow_of_nonneg (pow_nonneg (clockU_chain_nonneg hq0 j ω) P)
      (by norm_num), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← pow_mul,
      mul_comm]
  have hind : ∀ ω, ((goodSet b E D r₀ J j)ᶜ.indicator (1 : (Fin j → OneEndedLayer W) → ℝ≥0∞) ω) ^
      (2 : ℝ) = (goodSet b E D r₀ J j)ᶜ.indicator 1 ω := by
    intro ω
    by_cases h : ω ∈ (goodSet b E D r₀ J j)ᶜ
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  simp only [hsq, hind]
  rw [lintegral_indicator_one hm]
  gcongr
  refine (ENNReal.rpow_le_rpow h2 (by norm_num)).trans ?_
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : 1 ≤ G₂ ^ j := one_le_pow₀ hG₂
  calc (G₂ ^ j) ^ (1 / 2 : ℝ) ≤ (G₂ ^ j) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
    _ = G₂ ^ j := Real.rpow_one _

/-- `(1 + C/W)^n ≤ e^{C T'}` for `n ≤ TW`, `T' = max T 0`. -/
theorem growth_le {C T : ℝ} (hC : 0 ≤ C) {Wr : ℝ} (hW : 0 < Wr) {n : ℕ} (hn : (n : ℝ) ≤ T * Wr) :
    (1 + C / Wr) ^ n ≤ Real.exp (C * max T 0) := by
  have h1 : (1 + C / Wr) ^ n ≤ Real.exp (C / Wr) ^ n :=
    pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (C / Wr)]) n
  rw [← Real.exp_nat_mul] at h1
  refine h1.trans (Real.exp_le_exp.mpr ?_)
  have h2 : (n : ℝ) / Wr ≤ max T 0 := by
    rw [div_le_iff₀ hW]; exact hn.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hW.le)
  have : (n : ℝ) * (C / Wr) = C * ((n : ℝ) / Wr) := by ring
  rw [this]
  exact mul_le_mul_of_nonneg_left h2 hC

end Final

/-- **Clock moments of the open-inputs lemma** along the one-ended path, split into the part before
the exit from the scalar domain and the exceptional part. -/
theorem clock_moment_raw (hCS : ClockStepBound) {b E : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2)
    (hE0 : -2 < E) (hE1 : E < 2) {q : ℝ → ℝ} (hq : IsClockWeight q) (T : ℝ) {P : ℕ} (hP : 2 ≤ P) :
    ∃ r₁ : ℝ, 0 < r₁ ∧ ∀ r₀ : ℝ, 0 < r₀ → r₀ ≤ r₁ → ∀ J : ℕ, ∃ (A G : ℝ) (W₀ : ℕ), 0 ≤ A ∧ 1 ≤ G ∧
      ∀ W : ℕ, W₀ ≤ W → ∀ D : Matrix (Fin W) (Fin W) ℂ, D.IsHermitian → ∀ j : ℕ, (j : ℝ) ≤ T * W →
        ∫⁻ ω, ENNReal.ofReal (clockU (oneEndedY b E q D j ω) ^ P) ∂oneEndedLaw W b j ≤
          ENNReal.ofReal ((A * ((j : ℝ) + 1)) ^ P) +
            ENNReal.ofReal (G ^ j) * oneEndedLaw W b j (goodSet b E D r₀ J j)ᶜ ^ (1 / 2 : ℝ) := by
  obtain ⟨-, hq0, Kq₀, hqK₀⟩ := hq
  have hqK : ∀ x, q x ≤ max Kq₀ 0 := fun x => (hqK₀ x).trans (le_max_left _ _)
  have hKq : 0 ≤ max Kq₀ 0 := le_max_right _ _
  obtain ⟨⟨C₁, W₁, hcr1⟩, ⟨r₁, K, Cw, W₃, hr₁, hK, hwt⟩⟩ :=
    hCS b hb0 hb1 E hE0 hE1 (max Kq₀ 0) hKq P hP
  obtain ⟨⟨C₂, W₂, hcr2⟩, -⟩ := hCS b hb0 hb1 E hE0 hE1 (max Kq₀ 0) hKq (2 * P) (by omega)
  refine ⟨r₁, hr₁, fun r₀ hr₀ hr₀₁ J => ?_⟩
  have hE : |E| ≤ 2 := abs_le.mpr ⟨hE0.le, hE1.le⟩
  have hzpos : 0 < (boundaryZ b E).im := by
    rw [BlockBand.Layers.boundaryZ_im hE]
    have := BlockBand.Layers.matchedA_im_neg (abs_lt.mpr ⟨hE0, hE1⟩)
    have : 0 < 1 - b := by linarith
    nlinarith
  set G₁ := 2 * max C₁ 1 with hG₁
  set G₂ := 2 * max C₂ 1 with hG₂
  have hG₁1 : 1 ≤ G₁ := by have := le_max_right C₁ 1; linarith
  have hG₂1 : 1 ≤ G₂ := by have := le_max_right C₂ 1; linarith
  set Cw' := max Cw 0 with hCw'
  have hCw'0 : 0 ≤ Cw' := le_max_right _ _
  have hPr : (0 : ℝ) < P := by exact_mod_cast (by omega : 0 < P)
  set C' := 3 * Cw' / P with hC'
  have hC'0 : 0 ≤ C' := by positivity
  have hPC : 3 * Cw' ≤ P * C' := by rw [hC']; field_simp; exact le_rfl
  set B₀ := 1 / (boundaryZ b E).im + 1 with hB₀
  have hB₀0 : 0 ≤ B₀ := by positivity
  set A₀ := max 1 ((1 + K * B₀) * G₁ ^ J) with hA₀
  have hA₀1 : 1 ≤ A₀ := le_max_left _ _
  set A₁ := Real.exp (Cw' * max T 0) * (A₀ + C') with hA₁
  refine ⟨max A₁ (G₁ ^ J), G₂, max (max W₁ W₂) (max W₃ 1), by positivity, hG₂1, ?_⟩
  intro W hW D hD j hj
  have hW1 : W₁ ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hW)
  have hW2 : W₂ ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hW)
  have hW3 : W₃ ≤ W := (le_max_left _ _).trans ((le_max_right _ _).trans hW)
  have hW0 : 0 < W := (le_max_right _ _).trans ((le_max_right _ _).trans hW)
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW0
  have hcrude1 := crude_iter (q := q) (D := D) (b := b) (E := E) hq0 hqK
    (fun X hX Y hY w hw0 hw1 => hcr1 W hW0 hW1 X hX Y hY w hw0 hw1) hD
  have hcrude2 := crude_iter (q := q) (D := D) (b := b) (E := E) hq0 hqK
    (fun X hX Y hY w hw0 hw1 => hcr2 W hW0 hW2 X hX Y hY w hw0 hw1) hD
  have hA1 : 1 ≤ max A₁ (G₁ ^ J) := (one_le_pow₀ hG₁1).trans (le_max_right _ _)
  have hAj : 1 ≤ max A₁ (G₁ ^ J) * ((j : ℝ) + 1) := by
    have : (1 : ℝ) ≤ (j : ℝ) + 1 := by have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j); linarith
    nlinarith
  rcases lt_or_ge j J with hjJ | hjJ
  · -- before the entrance: the crude bound
    refine le_add_right ((hcrude1 j).trans (ENNReal.ofReal_le_ofReal ?_))
    calc G₁ ^ j ≤ G₁ ^ J := pow_le_pow_right₀ hG₁1 hjJ.le
      _ ≤ max A₁ (G₁ ^ J) := le_max_right _ _
      _ ≤ max A₁ (G₁ ^ J) * ((j : ℝ) + 1) := by nlinarith
      _ ≤ (max A₁ (G₁ ^ J) * ((j : ℝ) + 1)) ^ P := le_self_pow₀ hAj (by omega)
  · obtain ⟨n, rfl⟩ : ∃ n, j = J + n := ⟨j - J, by omega⟩
    have hm := measurableSet_goodSet (b := b) (E := E) (D := D) r₀ J (J + n)
    rw [← lintegral_add_compl _ hm]
    refine add_le_add ?_ (exceptional_part hq0 hG₂1 (hcrude2 (J + n)))
    -- the part before the exit
    have hwt' : ∀ X : Matrix (Fin W) (Fin W) ℂ, X.IsHermitian → jetDistance0 b E X ≤ r₀ →
        ∀ Y : Matrix (Fin W) (Fin W) ℂ, Y.PosSemidef → ∀ w : ℝ, 0 ≤ w → w ≤ max Kq₀ 0 →
          ∫⁻ ω, ENNReal.ofReal ((1 + K * jetDistance0 b E (freshSchur E X ω)) *
              nextClockU b E w X Y ω ^ P) ∂freshLaw W b ≤
            ENNReal.ofReal ((1 + Cw' / W) * (1 + K * jetDistance0 b E X) * clockU Y ^ P +
              Cw' * (clockU Y ^ (P - 1) + 1)) := by
      intro X hX hδ Y hY w hw0 hw1
      refine (hwt W hW0 hW3 X hX (hδ.trans hr₀₁) Y hY w hw0 hw1).trans
        (ENNReal.ofReal_le_ofReal ?_)
      have hu := clockU_nonneg' hY
      have h1 : 0 ≤ (1 + K * jetDistance0 b E X) * clockU Y ^ P := by
        have h0 : 0 ≤ K * jetDistance0 b E X := mul_nonneg hK (norm_nonneg _)
        have : 0 ≤ 1 + K * jetDistance0 b E X := by linarith
        positivity
      have h2 : 0 ≤ clockU Y ^ (P - 1) + 1 := by positivity
      have h3 : Cw / W ≤ Cw' / W := div_le_div_of_nonneg_right (le_max_left _ _) hWr.le
      have h4 : (1 + Cw / W) * ((1 + K * jetDistance0 b E X) * clockU Y ^ P) ≤
          (1 + Cw' / W) * ((1 + K * jetDistance0 b E X) * clockU Y ^ P) :=
        mul_le_mul_of_nonneg_right (by linarith) h1
      have h5 : Cw * (clockU Y ^ (P - 1) + 1) ≤ Cw' * (clockU Y ^ (P - 1) + 1) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) h2
      nlinarith
    have h0 : ∫⁻ ω, weightFun b E q D r₀ J K P J ω ∂oneEndedLaw W b J ≤
        ENNReal.ofReal (A₀ ^ P) := by
      have hpt : ∀ᵐ ω ∂oneEndedLaw W b J, weightFun b E q D r₀ J K P J ω ≤
          ENNReal.ofReal (1 + K * B₀) * ENNReal.ofReal (clockU (oneEndedY b E q D J ω) ^ P) := by
        filter_upwards [ZeroEntranceProb.ae_X_isHermitian b E hD J] with ω hω
        unfold weightFun
        by_cases hg : ω ∈ goodSet b E D r₀ J J
        · rw [Set.indicator_of_mem hg, ← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_
            (pow_nonneg (clockU_chain_nonneg hq0 J ω) P))
          have := jetDistance0_le hW0 hω hzpos hE (b := b)
          have : K * chainD0 b E D J ω ≤ K * B₀ := mul_le_mul_of_nonneg_left this hK
          linarith
        · rw [Set.indicator_of_notMem hg]; exact zero_le
      refine (lintegral_mono_ae hpt).trans ?_
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine (mul_le_mul_of_nonneg_left (hcrude1 J) zero_le).trans ?_
      rw [← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ((le_max_right (1 : ℝ) ((1 + K * B₀) * G₁ ^ J)).trans ?_)
      exact le_self_pow₀ hA₀1 (by omega)
    have hit := weighted_iter hq0 hqK hK hCw'0 hW0 (by omega) hwt' hD J hA₀1 hC'0 hPC h0 n
    rw [← lintegral_indicator hm]
    refine le_trans (lintegral_mono fun ω => ?_) (hit.trans (ENNReal.ofReal_le_ofReal ?_))
    · unfold weightFun
      by_cases hg : ω ∈ goodSet b E D r₀ J (J + n)
      · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg]
        refine ENNReal.ofReal_le_ofReal ?_
        have hu := pow_nonneg (clockU_chain_nonneg (b := b) (E := E) (D := D) hq0 (J + n) ω) P
        have : 0 ≤ K * chainD0 b E D (J + n) ω := mul_nonneg hK (norm_nonneg _)
        nlinarith
      · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg]
    · refine pow_le_pow_left₀ (by positivity) ?_ P
      have hn : (n : ℝ) ≤ T * W := by
        have : (n : ℝ) ≤ ((J + n : ℕ) : ℝ) := by exact_mod_cast (by omega : n ≤ J + n)
        linarith
      have hg := growth_le hCw'0 hWr hn
      have hj1 : (A₀ + n * C') ≤ (A₀ + C') * (((J + n : ℕ) : ℝ) + 1) := by
        have h1 : (n : ℝ) ≤ ((J + n : ℕ) : ℝ) + 1 := by push_cast; linarith
        have h2 : (1 : ℝ) ≤ ((J + n : ℕ) : ℝ) + 1 := by
          have := (Nat.cast_nonneg (J + n) : (0 : ℝ) ≤ _); linarith
        nlinarith
      calc (1 + Cw' / W) ^ n * (A₀ + n * C')
          ≤ Real.exp (Cw' * max T 0) * ((A₀ + C') * (((J + n : ℕ) : ℝ) + 1)) :=
            mul_le_mul hg hj1 (by positivity) (by positivity)
        _ = A₁ * (((J + n : ℕ) : ℝ) + 1) := by rw [hA₁]; ring
        _ ≤ max A₁ (G₁ ^ J) * (((J + n : ℕ) : ℝ) + 1) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

end OpenInputsProof

end BlockBand.Endpoints.Clock
