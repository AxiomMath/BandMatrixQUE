module

public import BlockBand.Endpoints.Clock.ClockMixingStep

/-!
# The clock-mixing lemma: the one-step `L^p` recursion along the one-ended path

Here `Z_j = Tr(Q_j f(X_j))` (`openClockZ`) and `√S_j = ‖Q_j^{1/2} f(X_j) Q_j^{1/2}‖_HS`
(`openClockSqrtS`). For one fresh layer at a deterministic Hermitian past, the hypotheses of
`stepZ` and `stepS` are those provided by `PassiveSourceMixingContract` (`oneStepMean` at zero
passive mass, with error `C(δ₀ + δ₁ + W⁻²)`, and `oneStepFluctuation`) and by
`GaussianAbsorptionContract` (`‖‖𝒢‖‖_{2p} ≤ C`); they are stated as explicit hypotheses on the
one-layer law. The conclusions, for the full `L^p` norms on the first `j+1` layers, are:

* `stepZ`: `‖Z_{j+1}‖_p ≤ |θ|‖Z_j‖_p + ‖h_j‖_p + ‖f‖_∞ K_q C²/W`,
* `stepS`: `‖√S_{j+1}‖_p ≤ |θ|‖√S_j‖_p + ‖h_j‖_p + ‖f‖_∞ K_q C²/√W + ‖f‖_∞ ‖γ_{j+1}‖_p/√W`,

with `h_j = (C_m(δ_{0,j} + δ_{1,j} + W⁻²) + C_f W^{-1/2}) γ_j` (the mean error and the centered
fluctuation), `‖f‖_∞ = (Im z)⁻¹ + |c₀|`, `q ≤ K_q`. The injection
`B = q((j+1)/W) C_{j+1}/W²` is handled by `|Tr(Bf)| ≤ ‖f‖ Tr B`, `Tr C ≤ W‖𝒢‖²` and, for
`√S`, by `hsSandwich_add_le_injection` and `√(2ab) ≤ a√W + b/√W`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
  BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal NNReal ComplexConjugate Matrix Matrix.Norms.L2Operator ComplexOrder

/-- `Z_j = Tr(Q_j^q f(X_j))`. -/
def openClockZ (b E : ℝ) (q : ℝ → ℝ) {W : ℕ} (D : Matrix (Fin W) (Fin W) ℂ) (j : ℕ)
    (ω : Fin j → OneEndedLayer W) : ℂ :=
  (oneEndedQ b E q D j ω * passiveF b E (oneEndedX E D j ω)).trace

/-- `√S_j = ‖Q^{1/2} f(X_j) Q^{1/2}‖_HS = (Tr(Q f Q f*))^{1/2}`. -/
def openClockSqrtS (b E : ℝ) (q : ℝ → ℝ) {W : ℕ} (D : Matrix (Fin W) (Fin W) ℂ) (j : ℕ)
    (ω : Fin j → OneEndedLayer W) : ℝ :=
  hsSandwich (oneEndedQ b E q D j ω) (passiveF b E (oneEndedX E D j ω))

namespace ClockMixingProb

open ClockMixingAlg

theorem meas_openClockZ (b E : ℝ) (q : ℝ → ℝ) {W : ℕ} (D : Matrix (Fin W) (Fin W) ℂ) (j : ℕ) :
    Measurable (openClockZ b E q D j) :=
  meas_trace (meas_mul (meas_Q b E q D j) ((meas_passiveF b E).comp (meas_X E D j)))

theorem meas_openClockSqrtS (b E : ℝ) (q : ℝ → ℝ) {W : ℕ} (D : Matrix (Fin W) (Fin W) ℂ)
    (j : ℕ) : Measurable (openClockSqrtS b E q D j) :=
  meas_hsSandwich (meas_Q b E q D j) ((meas_passiveF b E).comp (meas_X E D j))

/-- `√(2ab) ≤ at + b/t` for `a, b ≥ 0`, `t > 0`. -/
theorem sqrt_two_mul_le {a c t : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (ht : 0 < t) :
    Real.sqrt (2 * a * c) ≤ a * t + c / t := by
  have h0 : 0 ≤ a * t + c / t := by positivity
  rw [Real.sqrt_le_left h0]
  have : (a * t + c / t) ^ 2 - 2 * a * c = (a * t - c / t) ^ 2 + 2 * a * c := by
    field_simp; ring
  nlinarith [sq_nonneg (a * t - c / t), mul_nonneg ha hc]

variable {W : ℕ} {b E : ℝ} {q : ℝ → ℝ} {D : Matrix (Fin W) (Fin W) ℂ}

/-- The past-measurable error weight `h_j = (C_m(δ₀ + δ₁ + W⁻²) + c) γ_j`. -/
def errWeight (b E : ℝ) (q : ℝ → ℝ) (D : Matrix (Fin W) (Fin W) ℂ) (s : ℂ) (Cm c : ℝ) (j : ℕ)
    (x : Fin j → OneEndedLayer W) : ℝ :=
  (Cm * (jetDistance0 b E (oneEndedX E D j x) + jetDistance1 b E s (oneEndedX E D j x) +
    (W : ℝ)⁻¹ ^ 2) + c) * oneEndedGamma b E q D j x

/-- The pointwise algebra of one step, at a sample whose blocks are all Hermitian. -/
theorem step_pointwise (hD : D.IsHermitian) (hq0 : ∀ x, 0 ≤ q x) {Kq : ℝ} (hqK : ∀ x, q x ≤ Kq)
    (hW : 1 ≤ (W : ℝ)) (hz : 0 < (boundaryZ b E).im) (θ : ℂ) (j : ℕ)
    (ω : Fin (j + 1) → OneEndedLayer W) (hω : ∀ k a, ((ω k).1 a).IsHermitian) :
    let x := Fin.init ω
    let ξ := ω (Fin.last j)
    let X := oneEndedX E D j x
    let Kf := (boundaryZ b E).im⁻¹ + ‖cZero b E‖
    ‖openClockZ b E q D (j + 1) ω‖ ≤ ‖θ‖ * ‖openClockZ b E q D j x‖ +
        ‖(oneEndedQ b E q D j x * (freshTransportedF b E X ξ - θ • passiveF b E X)).trace‖ +
        Kf * Kq / W * ‖freshLayer b E X ξ‖ ^ 2 ∧
      openClockSqrtS b E q D (j + 1) ω ≤ ‖θ‖ * openClockSqrtS b E q D j x +
        hsSandwich (oneEndedQ b E q D j x) (freshTransportedF b E X ξ - θ • passiveF b E X) +
        Kf * Kq / Real.sqrt W * ‖freshLayer b E X ξ‖ ^ 2 +
        Kf / Real.sqrt W * oneEndedGamma b E q D (j + 1) ω := by
  intro x ξ X Kf
  have hx : ∀ k a, ((x k).1 a).IsHermitian := fun k a => hω _ a
  have hX : X.IsHermitian := X_isHermitian E hD j x hx
  have hXp : (freshSchur E X ξ).IsHermitian := freshSchur_isHermitian E hX ξ (hω (Fin.last j))
  have hQ : (oneEndedQ b E q D j x).PosSemidef := Q_posSemidef b E hq0 D j x
  set Q := oneEndedQ b E q D j x
  set L := freshL b E X ξ
  set f := passiveF b E X
  set fp := passiveF b E (freshSchur E X ξ)
  set Tp := freshTransportedF b E X ξ
  set c' : ℝ := q (((j + 1 : ℕ) : ℝ) / W) / (W : ℝ) ^ 2
  set B : Matrix (Fin W) (Fin W) ℂ := (c' : ℂ) • freshC b E X ξ
  have hW0 : (0 : ℝ) < W := by linarith
  have hKq : 0 ≤ Kq := (hq0 0).trans (hqK 0)
  have hc' : 0 ≤ c' := div_nonneg (hq0 _) (by positivity)
  have hB : B.PosSemidef := (freshC_posSemidef b E X ξ).smul (Complex.zero_le_real.mpr hc')
  have hA : (Lᴴ * Q * L).PosSemidef := hQ.conjTranspose_mul_mul_same L
  have hQp : oneEndedQ b E q D (j + 1) ω = Lᴴ * Q * L + B := Q_succ b E q D j ω
  have hXs : oneEndedX E D (j + 1) ω = freshSchur E X ξ := rfl
  have hTp : Tp = L * fp * Lᴴ := rfl
  have hfp : ‖fp‖ ≤ Kf := norm_passiveF_le b E hz hXp
  have hKf : 0 ≤ Kf := by positivity
  -- `Tr B ≤ (K_q / W) ‖𝒢‖²`
  have hTrB : B.trace.re ≤ Kq / W * ‖freshLayer b E X ξ‖ ^ 2 := by
    have h1 : B.trace.re = c' * (freshC b E X ξ).trace.re := by
      simp only [B, trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
    have h2 := trace_freshC_le b E X ξ
    have h3 : c' ≤ Kq / (W : ℝ) ^ 2 := by
      simp only [c']; gcongr; exact hqK _
    have hC0 : 0 ≤ (freshC b E X ξ).trace.re := trace_re_nonneg (freshC_posSemidef b E X ξ)
    rw [h1]
    calc c' * (freshC b E X ξ).trace.re ≤ Kq / (W : ℝ) ^ 2 * (W * ‖freshLayer b E X ξ‖ ^ 2) :=
          mul_le_mul h3 h2 hC0 (by positivity)
      _ = Kq / W * ‖freshLayer b E X ξ‖ ^ 2 := by field_simp
  have hTrB0 : 0 ≤ B.trace.re := trace_re_nonneg hB
  -- the mean/fluctuation split `T₊ = θ f + (T₊ - θ f)`
  have hsplit : Tp = θ • f + (Tp - θ • f) := by abel
  refine ⟨?_, ?_⟩
  · -- the trace
    have hZ : openClockZ b E q D (j + 1) ω =
        θ * (Q * f).trace + (Q * (Tp - θ • f)).trace + (B * fp).trace := by
      unfold openClockZ
      rw [hQp, hXs, Matrix.add_mul, trace_add, trace_transport, ← hTp]
      conv_lhs => rw [hsplit]
      rw [Matrix.mul_add, trace_add, Matrix.mul_smul, trace_smul, smul_eq_mul]
    rw [hZ]
    have hBf : ‖(B * fp).trace‖ ≤ Kf * Kq / W * ‖freshLayer b E X ξ‖ ^ 2 := by
      refine (norm_trace_mul_le hB fp).trans ?_
      calc ‖fp‖ * B.trace.re ≤ Kf * (Kq / W * ‖freshLayer b E X ξ‖ ^ 2) :=
            mul_le_mul hfp hTrB hTrB0 hKf
        _ = Kf * Kq / W * ‖freshLayer b E X ξ‖ ^ 2 := by ring
    calc ‖θ * (Q * f).trace + (Q * (Tp - θ • f)).trace + (B * fp).trace‖
        ≤ ‖θ * (Q * f).trace‖ + ‖(Q * (Tp - θ • f)).trace‖ + ‖(B * fp).trace‖ :=
          (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
      _ ≤ _ := by
          rw [norm_mul]
          exact add_le_add le_rfl hBf
  · -- the Hilbert–Schmidt part
    have hS : openClockSqrtS b E q D (j + 1) ω = hsSandwich (Lᴴ * Q * L + B) fp := by
      unfold openClockSqrtS; rw [hQp, hXs]
    rw [hS]
    have hinj := hsSandwich_add_le_injection hA hB fp
    rw [hsSandwich_transport, ← hTp] at hinj
    have hTp' : hsSandwich Q Tp ≤ ‖θ‖ * hsSandwich Q f + hsSandwich Q (Tp - θ • f) := by
      conv_lhs => rw [hsplit]
      refine (hsSandwich_add_le hQ _ _).trans ?_
      rw [hsSandwich_smul hQ.1]
    have hγ : (Lᴴ * Q * L + B).trace.re = oneEndedGamma b E q D (j + 1) ω := by
      unfold oneEndedGamma; rw [hQp]
    rw [hγ] at hinj
    have hγ0 : 0 ≤ oneEndedGamma b E q D (j + 1) ω := by
      rw [← hγ]; exact trace_re_nonneg (hA.add hB)
    have hsq := sqrt_two_mul_le hTrB0 hγ0 (Real.sqrt_pos.mpr hW0)
    have hsW : 0 < Real.sqrt W := Real.sqrt_pos.mpr hW0
    have hinj2 : ‖fp‖ * Real.sqrt (2 * B.trace.re * oneEndedGamma b E q D (j + 1) ω) ≤
        Kf * Kq / Real.sqrt W * ‖freshLayer b E X ξ‖ ^ 2 +
          Kf / Real.sqrt W * oneEndedGamma b E q D (j + 1) ω := by
      have h1 : B.trace.re * Real.sqrt W ≤ Kq / Real.sqrt W * ‖freshLayer b E X ξ‖ ^ 2 := by
        calc B.trace.re * Real.sqrt W ≤ Kq / W * ‖freshLayer b E X ξ‖ ^ 2 * Real.sqrt W :=
              mul_le_mul_of_nonneg_right hTrB hsW.le
          _ = Kq * ‖freshLayer b E X ξ‖ ^ 2 * (Real.sqrt W / W) := by ring
          _ = Kq * ‖freshLayer b E X ξ‖ ^ 2 * (1 / Real.sqrt W) := by rw [Real.sqrt_div_self']
          _ = Kq / Real.sqrt W * ‖freshLayer b E X ξ‖ ^ 2 := by ring
      calc ‖fp‖ * Real.sqrt (2 * B.trace.re * oneEndedGamma b E q D (j + 1) ω)
          ≤ Kf * (B.trace.re * Real.sqrt W +
              oneEndedGamma b E q D (j + 1) ω / Real.sqrt W) :=
            mul_le_mul hfp hsq (Real.sqrt_nonneg _) hKf
        _ ≤ Kf * (Kq / Real.sqrt W * ‖freshLayer b E X ξ‖ ^ 2 +
              oneEndedGamma b E q D (j + 1) ω / Real.sqrt W) := by gcongr
        _ = _ := by ring
    calc hsSandwich (Lᴴ * Q * L + B) fp
        ≤ hsSandwich Q Tp + ‖fp‖ * Real.sqrt (2 * B.trace.re * oneEndedGamma b E q D (j + 1) ω) :=
          hinj
      _ ≤ (‖θ‖ * hsSandwich Q f + hsSandwich Q (Tp - θ • f)) +
            (Kf * Kq / Real.sqrt W * ‖freshLayer b E X ξ‖ ^ 2 +
              Kf / Real.sqrt W * oneEndedGamma b E q D (j + 1) ω) := add_le_add hTp' hinj2
      _ = _ := by unfold openClockSqrtS; ring

section LpStep

/-- The one-layer hypotheses extracted from `PassiveSourceMixingContract` (`oneStepMean` at zero
passive mass, `oneStepFluctuation`, `GaussianAbsorptionContract`), at a fixed width `W`.
-/
structure StepHyp (W : ℕ) (b E : ℝ) (θ s : ℂ) (Cm Cf Cg p : ℝ) : Prop where
  mean : ∀ X : Matrix (Fin W) (Fin W) ℂ, X.IsHermitian →
    ‖matrixExpect (freshLaw W b) (freshTransportedF b E X) - θ • passiveF b E X‖ ≤
      Cm * (jetDistance0 b E X + jetDistance1 b E s X + (W : ℝ)⁻¹ ^ 2)
  fluct : ∀ X : Matrix (Fin W) (Fin W) ℂ, X.IsHermitian → ∀ u v : Fin W → ℂ,
    eLpNorm (fun ξ => bilinear u (freshTransportedF b E X ξ -
        matrixExpect (freshLaw W b) (freshTransportedF b E X)) v) (ENNReal.ofReal (max p 2))
      (freshLaw W b) ≤ ENNReal.ofReal (Cf / Real.sqrt W * vecNorm u * vecNorm v)
  absorb : ∀ X : Matrix (Fin W) (Fin W) ℂ, X.IsHermitian →
    eLpNorm (fun ξ => ‖freshLayer b E X ξ‖) (ENNReal.ofReal (2 * p)) (freshLaw W b) ≤
      ENNReal.ofReal Cg

/-- The conditional error bounds at a Hermitian past, for the trace. -/
theorem cond_errZ (hD : D.IsHermitian) (hq0 : ∀ x, 0 ≤ q x) (hW : 1 ≤ (W : ℝ)) (θ : ℂ) {s : ℂ}
    {Cm Cf Cg p : ℝ} (hCf : 0 ≤ Cf) (hp : 1 ≤ p) (H : StepHyp W b E θ s Cm Cf Cg p) (j : ℕ) :
    ∀ᵐ x ∂oneEndedLaw W b j,
      eLpNorm (fun ξ => (oneEndedQ b E q D j x * (freshTransportedF b E (oneEndedX E D j x) ξ -
          θ • passiveF b E (oneEndedX E D j x))).trace) (ENNReal.ofReal p) (freshLaw W b) ≤
        ENNReal.ofReal (errWeight b E q D s Cm (Cf / Real.sqrt W) j x) := by
  refine (ae_blocks_isHermitian b j).mono fun x hx => ?_
  have hX := X_isHermitian E hD j x hx
  have hQ := Q_posSemidef b E hq0 D j x
  have hc : 0 ≤ Cf / Real.sqrt W := by positivity
  have hfl' : ∀ u v : Fin W → ℂ, eLpNorm (fun ξ => bilinear u (freshTransportedF b E
      (oneEndedX E D j x) ξ - matrixExpect (freshLaw W b)
        (freshTransportedF b E (oneEndedX E D j x))) v) (ENNReal.ofReal p) (freshLaw W b) ≤
      ENNReal.ofReal (Cf / Real.sqrt W * vecNorm u * vecNorm v) := fun u v =>
    (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal (le_max_left p 2))).trans
      (H.fluct _ hX u v)
  refine (condTrace_le hQ (passiveF b E (oneEndedX E D j x)) θ hp hc hfl').trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  unfold errWeight
  exact mul_le_mul_of_nonneg_right (add_le_add_left (H.mean _ hX) _) (trace_re_nonneg hQ)

/-- The conditional error bounds at a Hermitian past, for the Hilbert–Schmidt norm. -/
theorem cond_errS (hD : D.IsHermitian) (hq0 : ∀ x, 0 ≤ q x) (hW : 1 ≤ (W : ℝ)) (θ : ℂ) {s : ℂ}
    {Cm Cf Cg p : ℝ} (hCf : 0 ≤ Cf) (hp : 1 ≤ p) (H : StepHyp W b E θ s Cm Cf Cg p) (j : ℕ) :
    ∀ᵐ x ∂oneEndedLaw W b j,
      eLpNorm (fun ξ => hsSandwich (oneEndedQ b E q D j x)
          (freshTransportedF b E (oneEndedX E D j x) ξ - θ • passiveF b E (oneEndedX E D j x)))
          (ENNReal.ofReal p) (freshLaw W b) ≤
        ENNReal.ofReal (errWeight b E q D s Cm (Cf / Real.sqrt W) j x) := by
  refine (ae_blocks_isHermitian b j).mono fun x hx => ?_
  have hX := X_isHermitian E hD j x hx
  have hQ := Q_posSemidef b E hq0 D j x
  have hc : 0 ≤ Cf / Real.sqrt W := by positivity
  have hT : Measurable (fun ξ => freshTransportedF b E (oneEndedX E D j x) ξ) := by
    have h := (meas_freshTransportedF (W := W) b E).comp
      (measurable_prodMk_left (x := oneEndedX E D j x))
    simpa only [Function.comp_def] using h
  refine (condHS_le hQ (passiveF b E (oneEndedX E D j x)) θ hT hp (le_max_left p 2)
    (le_max_right p 2) hc (H.fluct _ hX)).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  unfold errWeight
  exact mul_le_mul_of_nonneg_right (add_le_add_left (H.mean _ hX) _) (trace_re_nonneg hQ)

/-- The conditional injection bound `‖‖𝒢‖²‖_p ≤ C²`. -/
theorem cond_errB (hD : D.IsHermitian) (θ : ℂ) {s : ℂ} {Cm Cf Cg p : ℝ} (hCg : 0 ≤ Cg)
    (hp : 1 ≤ p) (H : StepHyp W b E θ s Cm Cf Cg p) (j : ℕ) :
    ∀ᵐ x ∂oneEndedLaw W b j,
      eLpNorm (fun ξ => ‖freshLayer b E (oneEndedX E D j x) ξ‖ ^ 2) (ENNReal.ofReal p)
        (freshLaw W b) ≤ ENNReal.ofReal (Cg ^ 2) := by
  refine (ae_blocks_isHermitian b j).mono fun x hx => ?_
  exact condSq_le (by linarith) hCg (H.absorb _ (X_isHermitian E hD j x hx))

/-- **One step for the trace**. -/
theorem stepZ (hD : D.IsHermitian) (hq0 : ∀ x, 0 ≤ q x) {Kq : ℝ} (hqK : ∀ x, q x ≤ Kq)
    (hW : 1 ≤ (W : ℝ)) (hz : 0 < (boundaryZ b E).im) (θ : ℂ) {s : ℂ} {Cm Cf Cg p : ℝ}
    (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg) (hp : 1 ≤ p) (H : StepHyp W b E θ s Cm Cf Cg p) (j : ℕ) :
    eLpNorm (openClockZ b E q D (j + 1)) (ENNReal.ofReal p) (oneEndedLaw W b (j + 1)) ≤
      ENNReal.ofReal ‖θ‖ * eLpNorm (openClockZ b E q D j) (ENNReal.ofReal p) (oneEndedLaw W b j) +
        eLpNorm (errWeight b E q D s Cm (Cf / Real.sqrt W) j) (ENNReal.ofReal p)
          (oneEndedLaw W b j) +
        ENNReal.ofReal (((boundaryZ b E).im⁻¹ + ‖cZero b E‖) * Kq / W * Cg ^ 2) := by
  set K := ((boundaryZ b E).im⁻¹ + ‖cZero b E‖) * Kq / W
  have hKq : 0 ≤ Kq := (hq0 0).trans (hqK 0)
  have hK : 0 ≤ K := by positivity
  have hp0 : 0 < p := by linarith
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have hpair : Measurable (fun z : (Fin j → OneEndedLayer W) × OneEndedLayer W =>
      (oneEndedX E D j z.1, z.2)) := ((meas_X E D j).comp measurable_fst).prodMk measurable_snd
  set GZ : (Fin j → OneEndedLayer W) × OneEndedLayer W → ℂ := fun z =>
    (oneEndedQ b E q D j z.1 * (freshTransportedF b E (oneEndedX E D j z.1) z.2 -
      θ • passiveF b E (oneEndedX E D j z.1))).trace with hGZ
  set GB : (Fin j → OneEndedLayer W) × OneEndedLayer W → ℝ := fun z =>
    ‖freshLayer b E (oneEndedX E D j z.1) z.2‖ ^ 2 with hGB
  have hGZm : Measurable GZ :=
    meas_trace (meas_mul ((meas_Q b E q D j).comp measurable_fst)
      (((meas_freshTransportedF b E).comp hpair).sub
        (meas_smul θ ((meas_passiveF b E).comp ((meas_X E D j).comp measurable_fst)))))
  have hGBm : Measurable GB :=
    (continuous_norm.measurable.comp ((meas_freshLayer b E).comp hpair)).pow_const 2
  have hφ : Measurable (fun ω : Fin (j + 1) → OneEndedLayer W => (Fin.init ω, ω (Fin.last j))) :=
    (meas_init j).prodMk (meas_last j)
  have hpt : ∀ᵐ ω ∂oneEndedLaw W b (j + 1), ‖openClockZ b E q D (j + 1) ω‖ ≤
      ‖θ‖ * ‖openClockZ b E q D j (Fin.init ω)‖ + ‖GZ (Fin.init ω, ω (Fin.last j))‖ +
        K * GB (Fin.init ω, ω (Fin.last j)) :=
    (ae_blocks_isHermitian b (j + 1)).mono fun ω hω =>
      (step_pointwise hD hq0 hqK hW hz θ j ω hω).1
  have h1 := eLpNorm_mono_ae_real (p := ENNReal.ofReal p) (meas_openClockZ b E q D (j + 1)).aestronglyMeasurable hpt
  refine h1.trans ?_
  set F1 : (Fin (j + 1) → OneEndedLayer W) → ℝ :=
    fun ω => ‖θ‖ * ‖openClockZ b E q D j (Fin.init ω)‖ with hF1
  set F2 : (Fin (j + 1) → OneEndedLayer W) → ℝ :=
    fun ω => ‖GZ (Fin.init ω, ω (Fin.last j))‖ with hF2
  set F3 : (Fin (j + 1) → OneEndedLayer W) → ℝ :=
    fun ω => K * GB (Fin.init ω, ω (Fin.last j)) with hF3
  have hsum : (fun ω => ‖θ‖ * ‖openClockZ b E q D j (Fin.init ω)‖ +
      ‖GZ (Fin.init ω, ω (Fin.last j))‖ + K * GB (Fin.init ω, ω (Fin.last j))) =
      F1 + F2 + F3 := rfl
  rw [hsum]
  have e1 := eLpNorm_add_le (μ := oneEndedLaw W b (j + 1)) (f := F1 + F2) (g := F3) hp1
  have e2 := eLpNorm_add_le (μ := oneEndedLaw W b (j + 1)) (f := F1) (g := F2) hp1
  refine e1.trans (add_le_add (e2.trans (add_le_add ?_ ?_)) ?_)
  · rw [hF1, eLpNorm_real_mul_le, abs_of_nonneg (norm_nonneg _)]
    gcongr
    have e := eLpNorm_init_eq (freshLaw W b) j (meas_openClockZ b E q D j).norm.aestronglyMeasurable
      (ENNReal.ofReal p)
    have e' := eLpNorm_norm (μ := oneEndedLaw W b j) (p := ENNReal.ofReal p) _
      (meas_openClockZ b E q D j).aestronglyMeasurable
    exact (le_of_eq e).trans (le_of_eq e')
  · have e := eLpNorm_norm (μ := oneEndedLaw W b (j + 1)) (p := ENNReal.ofReal p)
      (fun ω => GZ (Fin.init ω, ω (Fin.last j))) (hGZm.comp hφ).aestronglyMeasurable
    exact (le_of_eq e).trans (eLpNorm_initLast_le (freshLaw W b) j hGZm.aestronglyMeasurable hp0
      (cond_errZ hD hq0 hW θ hCf hp H j))
  · rw [hF3, eLpNorm_real_mul_le, abs_of_nonneg hK, ENNReal.ofReal_mul hK]
    gcongr
    refine (eLpNorm_initLast_le (freshLaw W b) j hGBm.aestronglyMeasurable hp0
      (h := fun _ => Cg ^ 2) (cond_errB hD θ hCg hp H j)).trans ?_
    rw [eLpNorm_const_prob _ (by simpa using hp0), Real.enorm_eq_ofReal_abs,
      abs_of_nonneg (sq_nonneg _)]

/-- **One step for the Hilbert–Schmidt norm**. -/
theorem stepS (hD : D.IsHermitian) (hq0 : ∀ x, 0 ≤ q x) {Kq : ℝ} (hqK : ∀ x, q x ≤ Kq)
    (hW : 1 ≤ (W : ℝ)) (hz : 0 < (boundaryZ b E).im) (θ : ℂ) {s : ℂ} {Cm Cf Cg p : ℝ}
    (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg) (hp : 1 ≤ p) (H : StepHyp W b E θ s Cm Cf Cg p) (j : ℕ) :
    eLpNorm (openClockSqrtS b E q D (j + 1)) (ENNReal.ofReal p) (oneEndedLaw W b (j + 1)) ≤
      ENNReal.ofReal ‖θ‖ *
          eLpNorm (openClockSqrtS b E q D j) (ENNReal.ofReal p) (oneEndedLaw W b j) +
        eLpNorm (errWeight b E q D s Cm (Cf / Real.sqrt W) j) (ENNReal.ofReal p)
          (oneEndedLaw W b j) +
        ENNReal.ofReal (((boundaryZ b E).im⁻¹ + ‖cZero b E‖) * Kq / Real.sqrt W * Cg ^ 2) +
        ENNReal.ofReal (((boundaryZ b E).im⁻¹ + ‖cZero b E‖) / Real.sqrt W) *
          eLpNorm (oneEndedGamma b E q D (j + 1)) (ENNReal.ofReal p) (oneEndedLaw W b (j + 1)) := by
  set K := ((boundaryZ b E).im⁻¹ + ‖cZero b E‖) * Kq / Real.sqrt W
  set K' := ((boundaryZ b E).im⁻¹ + ‖cZero b E‖) / Real.sqrt W
  have hKq : 0 ≤ Kq := (hq0 0).trans (hqK 0)
  have hK : 0 ≤ K := by positivity
  have hK' : 0 ≤ K' := by positivity
  have hp0 : 0 < p := by linarith
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have hpair : Measurable (fun z : (Fin j → OneEndedLayer W) × OneEndedLayer W =>
      (oneEndedX E D j z.1, z.2)) := ((meas_X E D j).comp measurable_fst).prodMk measurable_snd
  set GS : (Fin j → OneEndedLayer W) × OneEndedLayer W → ℝ := fun z =>
    hsSandwich (oneEndedQ b E q D j z.1) (freshTransportedF b E (oneEndedX E D j z.1) z.2 -
      θ • passiveF b E (oneEndedX E D j z.1)) with hGS
  set GB : (Fin j → OneEndedLayer W) × OneEndedLayer W → ℝ := fun z =>
    ‖freshLayer b E (oneEndedX E D j z.1) z.2‖ ^ 2 with hGB
  have hGSm : Measurable GS :=
    meas_hsSandwich ((meas_Q b E q D j).comp measurable_fst)
      (((meas_freshTransportedF b E).comp hpair).sub
        (meas_smul θ ((meas_passiveF b E).comp ((meas_X E D j).comp measurable_fst))))
  have hGBm : Measurable GB :=
    (continuous_norm.measurable.comp ((meas_freshLayer b E).comp hpair)).pow_const 2
  have hφ : Measurable (fun ω : Fin (j + 1) → OneEndedLayer W => (Fin.init ω, ω (Fin.last j))) :=
    (meas_init j).prodMk (meas_last j)
  have hpt : ∀ᵐ ω ∂oneEndedLaw W b (j + 1), ‖openClockSqrtS b E q D (j + 1) ω‖ ≤
      ‖θ‖ * openClockSqrtS b E q D j (Fin.init ω) + GS (Fin.init ω, ω (Fin.last j)) +
        K * GB (Fin.init ω, ω (Fin.last j)) + K' * oneEndedGamma b E q D (j + 1) ω :=
    (ae_blocks_isHermitian b (j + 1)).mono fun ω hω => by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (show 0 ≤ openClockSqrtS b E q D (j + 1) ω from hsSandwich_nonneg _ _)]
      exact (step_pointwise hD hq0 hqK hW hz θ j ω hω).2
  have h1 := eLpNorm_mono_ae_real (p := ENNReal.ofReal p)
    (meas_openClockSqrtS b E q D (j + 1)).aestronglyMeasurable hpt
  refine h1.trans ?_
  set F1 : (Fin (j + 1) → OneEndedLayer W) → ℝ :=
    fun ω => ‖θ‖ * openClockSqrtS b E q D j (Fin.init ω) with hF1
  set F2 : (Fin (j + 1) → OneEndedLayer W) → ℝ :=
    fun ω => GS (Fin.init ω, ω (Fin.last j)) with hF2
  set F3 : (Fin (j + 1) → OneEndedLayer W) → ℝ :=
    fun ω => K * GB (Fin.init ω, ω (Fin.last j)) with hF3
  set F4 : (Fin (j + 1) → OneEndedLayer W) → ℝ :=
    fun ω => K' * oneEndedGamma b E q D (j + 1) ω with hF4
  have hsum : (fun ω => ‖θ‖ * openClockSqrtS b E q D j (Fin.init ω) +
      GS (Fin.init ω, ω (Fin.last j)) + K * GB (Fin.init ω, ω (Fin.last j)) +
      K' * oneEndedGamma b E q D (j + 1) ω) = F1 + F2 + F3 + F4 := rfl
  rw [hsum]
  have e1 := eLpNorm_add_le (μ := oneEndedLaw W b (j + 1)) (f := F1 + F2 + F3) (g := F4) hp1
  have e2 := eLpNorm_add_le (μ := oneEndedLaw W b (j + 1)) (f := F1 + F2) (g := F3) hp1
  have e3 := eLpNorm_add_le (μ := oneEndedLaw W b (j + 1)) (f := F1) (g := F2) hp1
  refine e1.trans (add_le_add (e2.trans (add_le_add (e3.trans (add_le_add ?_ ?_)) ?_)) ?_)
  · rw [hF1, eLpNorm_real_mul_le, abs_of_nonneg (norm_nonneg _)]
    gcongr
    exact (eLpNorm_init_eq (freshLaw W b) j
      (meas_openClockSqrtS b E q D j).aestronglyMeasurable _).le
  · exact eLpNorm_initLast_le (freshLaw W b) j hGSm.aestronglyMeasurable hp0
      (cond_errS hD hq0 hW θ hCf hp H j)
  · rw [hF3, eLpNorm_real_mul_le, abs_of_nonneg hK, ENNReal.ofReal_mul hK]
    gcongr
    refine (eLpNorm_initLast_le (freshLaw W b) j hGBm.aestronglyMeasurable hp0
      (h := fun _ => Cg ^ 2) (cond_errB hD θ hCg hp H j)).trans ?_
    rw [eLpNorm_const_prob _ (by simpa using hp0), Real.enorm_eq_ofReal_abs,
      abs_of_nonneg (sq_nonneg _)]
  · rw [hF4, eLpNorm_real_mul_le, abs_of_nonneg hK']

end LpStep

end ClockMixingProb

end BlockBand.Endpoints.Clock
