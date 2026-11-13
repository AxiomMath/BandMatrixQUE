module

public import BlockBand.Endpoints.Clock.OpenInputsProofEntrance
public import BlockBand.Endpoints.Clock.OpenInputsProofClock
public import BlockBand.Endpoints.Clock.OpenInputsProofClockStep
public import BlockBand.Endpoints.Clock.OpenInputsProofEmbed

/-!
# The open-inputs lemma: one-ended first jet and unstopped clocks

`openInputsMoments_of` proves `OpenInputsMoments` from the contracts
* `GaussianAbsorptionContract` (the Gaussian absorption lemma),
* `TraceMatrixContract` (the trace-matrix lemma), and
* `WeightedLayerContract` (the weighted-layer lemma, fields `clockMean`, `clockNoise`,
  `unrestricted`, read for one block),
through the cavity-mean lemma (`cavityMean_of`) and the zero-entrance lemma
(`zeroEntrance_of_contracts`).

## Structure of the proof (the steps of the paper's proof)
* Steps 2–4, deterministic one-step contraction of the scalar and of the first jet:
  `OpenInputsProofStep` (`step_bound`).
* Steps 2, 5 along the chain (conditional `L^p` noise, scalar-domain events, measurability):
  `OpenInputsProofChain`; the `L^p` recursion before the exit and the exit recursion:
  `OpenInputsProofJet`.
* Step 1 (entrance) and the asymptotics (`e^{-cW log W}` exit probability at order `P = aW`,
  `q^{(log W)²}` smaller than every power of `W`): `OpenInputsProofEntrance`.
* Step 6, conditional clock moments: `OpenInputsProofEmbed` (the weighted-layer lemma for one
  block), `OpenInputsProofClockStep` (`ClockStepBound`); Step 7, iteration and the unstopped
  bound: `OpenInputsProofClock`.

## Differences from the paper's proof (none in the statement)
* The first jet is carried in the combined quantity `Φ = δ₀ + λδ₁` with one contraction
  factor `θ = (1+q)/2`, instead of two separate geometric recursions (Steps 2 and 5).
* The exit probability is estimated at the moment order `P = aW` directly (Markov), giving
  `(K/√W)^{aW}`, which is of the form `e^{-c_*W log W}`.
* In Step 7 the Hölder step `E 1_G u^{P-1} ≤ M^{1-1/P}` is replaced by Young's inequality
  `u^{P-1} ≤ u^P/A + A^{P-1}` at the current majorant `A` (same conclusion).
* The real moment order `p ≥ 1` is reached from `max p 2` (scalar and jet) and from the integer
  `⌈p⌉ + 2` (clocks) by monotonicity of `L^p` norms on a probability space.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
  BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal NNReal Matrix.Norms.L2Operator

namespace OpenInputsProof

open CavityMeanProb ZeroEntranceProb

variable {W : ℕ} {b E : ℝ}

/-- **The exit probability** up to `TW`: `P(G_jᶜ) ≤ (1 + T'W)(K √P/W)^P`. -/
theorem beta_bound {r₀ q Cst C₀ a₀ : ℝ} (hF : OneStepFacts b E r₀ q Cst C₀ a₀) (hW : 0 < W)
    {D : Matrix (Fin W) (Fin W) ℂ} (hD : D.IsHermitian) (J : ℕ) {ρ P Ke Kt T' : ℝ}
    (hρ0 : 0 < ρ) (hρ : ρ + C₀ / (W : ℝ) ^ 2 ≤ (1 - q) * r₀) (hP2 : 2 ≤ P) (hPa : P ≤ a₀ * W)
    (hent : oneEndedLaw W b J {ω | r₀ < chainD0 b E D J ω} ≤
      ENNReal.ofReal ((Ke * Real.sqrt P / W) ^ P))
    (hKe0 : 0 ≤ Ke) (hKe : Ke ≤ Kt) (hKC : C₀ / ρ ≤ Kt) (j : ℕ)
    (hj : (j : ℝ) ≤ T' * W) :
    oneEndedLaw W b j (goodSet b E D r₀ J j)ᶜ ≤
      ENNReal.ofReal ((1 + T' * W) * (Kt * Real.sqrt P / W) ^ P) := by
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hC₀ : 0 ≤ C₀ := hF.2.2.2.2.1
  have hP0 : 0 ≤ P := by linarith
  have hKt0 : 0 ≤ Kt := hKe0.trans hKe
  have hbase : 0 ≤ (Kt * Real.sqrt P / W) ^ P := by positivity
  by_cases hjJ : j < J
  · rw [goodSet_eq_univ j hjJ, Set.compl_univ, measure_empty]; exact zero_le
  push Not at hjJ
  obtain ⟨n, rfl⟩ : ∃ n, j = J + n := ⟨j - J, by omega⟩
  have h1 := bad_bound hF hW hD J hρ0 hρ hP2 hPa n
  have h2 : oneEndedLaw W b J (goodSet b E D r₀ J J)ᶜ ≤
      ENNReal.ofReal ((Kt * Real.sqrt P / W) ^ P) := by
    refine (measure_mono goodSet_compl_subset).trans (hent.trans (ENNReal.ofReal_le_ofReal ?_))
    exact Real.rpow_le_rpow (by positivity) (by gcongr) hP0
  have h3 : ENNReal.ofReal ((C₀ * Real.sqrt P / W / ρ) ^ P) ≤
      ENNReal.ofReal ((Kt * Real.sqrt P / W) ^ P) := by
    refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (by positivity) ?_ hP0)
    have : C₀ * Real.sqrt P / W / ρ = C₀ / ρ * (Real.sqrt P / W) := by ring
    rw [this, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right hKC (by positivity)
  refine h1.trans ((add_le_add h2 (mul_le_mul_of_nonneg_left h3 zero_le)).trans ?_)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnT : (n : ℝ) ≤ T' * W := by
    have : ((J + n : ℕ) : ℝ) = J + n := by push_cast; ring
    rw [this] at hj
    have : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    linarith
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hn, ← ENNReal.ofReal_add hbase
    (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have : (1 + (n : ℝ)) * (Kt * Real.sqrt P / W) ^ P ≤ (1 + T' * W) * (Kt * Real.sqrt P / W) ^ P :=
    mul_le_mul_of_nonneg_right (by linarith) hbase
  linarith

/-- `γ_j = W⁻¹ u_j` with `u_j = W⁻¹ Re Tr Y_j`. -/
theorem gamma_eq (b E : ℝ) (q : ℝ → ℝ) (D : Matrix (Fin W) (Fin W) ℂ) (j : ℕ)
    (ω : Fin j → OneEndedLayer W) :
    oneEndedGamma b E q D j ω = (W : ℝ)⁻¹ * clockU (oneEndedY b E q D j ω) := by
  simp only [oneEndedGamma, oneEndedQ, Matrix.trace_smul, smul_eq_mul, clockU]
  rw [show (((W : ℝ) ^ 2)⁻¹ : ℂ) = ((((W : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) by push_cast; rfl,
    Complex.re_ofReal_mul]
  ring

/-- From the `P`-th clock moment to the `L^P` norm of `γ_j = W⁻¹ u_j`. -/
theorem eLpNorm_gamma_le (hW : 0 < W) {q : ℝ → ℝ} (hq0 : ∀ x, 0 ≤ q x)
    (D : Matrix (Fin W) (Fin W) ℂ) (j P : ℕ) (hP : 1 ≤ P) {c : ℝ} (hc : 0 ≤ c)
    (h : ∫⁻ ω, ENNReal.ofReal (clockU (oneEndedY b E q D j ω) ^ P) ∂oneEndedLaw W b j ≤
      ENNReal.ofReal (c ^ P)) :
    eLpNorm (oneEndedGamma b E q D j) (ENNReal.ofReal (P : ℝ)) (oneEndedLaw W b j) ≤
      ENNReal.ofReal (c / W) := by
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have hu : ∀ ω, 0 ≤ clockU (oneEndedY b E q D j ω) := fun ω =>
    mul_nonneg (by positivity) (ClockMixingAlg.trace_re_nonneg
      (ClockMixingProb.Y_posSemidef b E hq0 D j ω))
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hP0.ne') ENNReal.ofReal_ne_top
    (ClockMixingProb.meas_gamma b E q D j).aestronglyMeasurable, ENNReal.toReal_ofReal hP0.le]
  have hpt : ∀ ω, ‖oneEndedGamma b E q D j ω‖ₑ ^ (P : ℝ) =
      ENNReal.ofReal ((W : ℝ)⁻¹ ^ P) * ENNReal.ofReal (clockU (oneEndedY b E q D j ω) ^ P) := by
    intro ω
    rw [gamma_eq, Real.enorm_eq_ofReal_abs, abs_of_nonneg (mul_nonneg (by positivity) (hu ω)),
      ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (by positivity) (hu ω)) hP0.le,
      Real.rpow_natCast, mul_pow, ENNReal.ofReal_mul (by positivity)]
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc (ENNReal.ofReal ((W : ℝ)⁻¹ ^ P) *
        ∫⁻ ω, ENNReal.ofReal (clockU (oneEndedY b E q D j ω) ^ P) ∂oneEndedLaw W b j) ^ (1 / (P : ℝ))
      ≤ (ENNReal.ofReal ((W : ℝ)⁻¹ ^ P) * ENNReal.ofReal (c ^ P)) ^ (1 / (P : ℝ)) := by gcongr
    _ = ENNReal.ofReal (c / W) := by
      rw [← ENNReal.ofReal_mul (by positivity), ← mul_pow,
        ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), mul_one_div_cancel hP0.ne',
        Real.rpow_one]
      ring

/-- `(x + 1)^P ≥ x^P + 1` for `x ≥ 0`. -/
theorem pow_add_one_ge {x : ℝ} (hx : 0 ≤ x) (P : ℕ) (hP : 1 ≤ P) :
    x ^ P + 1 ≤ (x + 1) ^ P := by
  induction P with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · have ih' := ih h
      have h1 : 1 ≤ (x + 1) ^ n := one_le_pow₀ (by linarith)
      calc x ^ (n + 1) + 1 = x * x ^ n + 1 := by ring
        _ ≤ (x + 1) * (x + 1) ^ n := by nlinarith [pow_nonneg hx n]
        _ = (x + 1) ^ (n + 1) := by ring

/-- **The scalar and first-jet bound at a fixed `W`** (assembled). -/
theorem jet_final {r₀ qq Cst C₀ a₀ : ℝ} (hF : OneStepFacts b E r₀ qq Cst C₀ a₀) (hW0 : 0 < W)
    (hW1 : (1 : ℝ) ≤ W) {D : Matrix (Fin W) (Fin W) ℂ} (hD : D.IsHermitian)
    (hzpos : 0 < (boundaryZ b E).im) (hE : |E| ≤ 2) {s : ℂ} (hs : IsStationaryJet b E s)
    (J n : ℕ) {p p' τ : ℝ} (hpp' : p ≤ p') (hp'2 : 2 ≤ p') (hp'a : p' ≤ a₀ * W) (hτ0 : 0 ≤ τ)
    (hθn : (W : ℝ) * ((1 + qq) / 2) ^ n ≤ 1)
    (hβ : oneEndedLaw W b (J + n) (goodSet b E D r₀ J (J + n))ᶜ ≤ ENNReal.ofReal τ)
    (hτp : (1 / (boundaryZ b E).im + 1 + (1 - qq) / (2 * (Cst + 1)) *
        (1 / (boundaryZ b E).im ^ 2 + dStar b)) * τ ^ (1 / p') ≤ 1 / W) :
    eLpNorm (fun ω => jetDistance0 b E (oneEndedX E D (J + n) ω)) (ENNReal.ofReal p)
        (oneEndedLaw W b (J + n)) +
      eLpNorm (fun ω => jetDistance1 b E s (oneEndedX E D (J + n) ω)) (ENNReal.ofReal p)
        (oneEndedLaw W b (J + n)) ≤
      ENNReal.ofReal ((1 + 1 / ((1 - qq) / (2 * (Cst + 1)))) *
        ((1 / (boundaryZ b E).im + 1 + (1 - qq) / (2 * (Cst + 1)) *
            (1 / (boundaryZ b E).im ^ 2 + dStar b)) +
          (1 + (1 - qq) / (2 * (Cst + 1))) * C₀ * (1 + Real.sqrt p') / (1 - (1 + qq) / 2) + 1) /
          W) := by
  have hF' := hF
  obtain ⟨-, hqq0, hqq1, hCst, hC₀, -, -⟩ := hF'
  have hWr : (0 : ℝ) < W := by linarith
  set lam := (1 - qq) / (2 * (Cst + 1)) with hlam
  have hlam0 : 0 < lam := div_pos (by linarith) (by positivity)
  have hdS : 0 ≤ dStar b := (norm_nonneg s).trans hs.2
  set B := 1 / (boundaryZ b E).im + 1 + lam * (1 / (boundaryZ b E).im ^ 2 + dStar b) with hB
  have hB0 : 0 ≤ B := by positivity
  have h1 := jet_le_phi (s := s) hD hzpos hlam0 (J + n) (ENNReal.ofReal p')
  have h2 := phi_split (r₀ := r₀) hW0 hD hzpos hE hs hlam0.le J (J + n) (by linarith : 1 ≤ p')
  have h3 := phi_good_bound hF hW0 hD hzpos hE hs J hp'2 hp'a n
  have hmono : eLpNorm (fun ω => jetDistance0 b E (oneEndedX E D (J + n) ω)) (ENNReal.ofReal p)
        (oneEndedLaw W b (J + n)) +
      eLpNorm (fun ω => jetDistance1 b E s (oneEndedX E D (J + n) ω)) (ENNReal.ofReal p)
        (oneEndedLaw W b (J + n)) ≤
      eLpNorm (chainD0 b E D (J + n)) (ENNReal.ofReal p') (oneEndedLaw W b (J + n)) +
        eLpNorm (chainD1 b E s D (J + n)) (ENNReal.ofReal p') (oneEndedLaw W b (J + n)) :=
    add_le_add (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hpp'))
      (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hpp'))
  refine hmono.trans (h1.trans ?_)
  have hgap : 0 < 1 - (1 + qq) / 2 := by linarith
  have hFle : (1 + lam) * C₀ / (W : ℝ) ^ 2 + (1 + lam) * (C₀ * Real.sqrt p' / W) ≤
      (1 + lam) * C₀ * (1 + Real.sqrt p') / W := by
    have hW2 : (1 + lam) * C₀ / (W : ℝ) ^ 2 ≤ (1 + lam) * C₀ / W := by
      apply div_le_div_of_nonneg_left (by positivity) hWr
      nlinarith
    have : (1 + lam) * C₀ * (1 + Real.sqrt p') / W =
        (1 + lam) * C₀ / W + (1 + lam) * (C₀ * Real.sqrt p' / W) := by ring
    linarith
  have hθB : ((1 + qq) / 2) ^ n * B ≤ B / W := by
    rw [le_div_iff₀ hWr]
    have := mul_le_mul_of_nonneg_right hθn hB0
    linarith
  have hfin : ((1 + qq) / 2) ^ n * B +
      ((1 + lam) * C₀ / (W : ℝ) ^ 2 + (1 + lam) * (C₀ * Real.sqrt p' / W)) /
        (1 - (1 + qq) / 2) + B * τ ^ (1 / p') ≤
      (B + (1 + lam) * C₀ * (1 + Real.sqrt p') / (1 - (1 + qq) / 2) + 1) / W := by
    have e1 : ((1 + lam) * C₀ / (W : ℝ) ^ 2 + (1 + lam) * (C₀ * Real.sqrt p' / W)) /
        (1 - (1 + qq) / 2) ≤ (1 + lam) * C₀ * (1 + Real.sqrt p') / W / (1 - (1 + qq) / 2) :=
      div_le_div_of_nonneg_right hFle hgap.le
    have e2 : (B + (1 + lam) * C₀ * (1 + Real.sqrt p') / (1 - (1 + qq) / 2) + 1) / W =
        B / W + (1 + lam) * C₀ * (1 + Real.sqrt p') / W / (1 - (1 + qq) / 2) + 1 / W := by
      field_simp
    rw [e2]; linarith
  calc ENNReal.ofReal (1 + 1 / lam) *
        eLpNorm (chainPhi b E s D lam (J + n)) (ENNReal.ofReal p') (oneEndedLaw W b (J + n))
      ≤ ENNReal.ofReal (1 + 1 / lam) *
          (ENNReal.ofReal (((1 + qq) / 2) ^ n * B +
              ((1 + lam) * C₀ / (W : ℝ) ^ 2 + (1 + lam) * (C₀ * Real.sqrt p' / W)) /
                (1 - (1 + qq) / 2)) +
            ENNReal.ofReal B * ENNReal.ofReal τ ^ (1 / p')) := by
        gcongr
        refine h2.trans (add_le_add h3 ?_)
        gcongr
    _ = ENNReal.ofReal ((1 + 1 / lam) * (((1 + qq) / 2) ^ n * B +
              ((1 + lam) * C₀ / (W : ℝ) ^ 2 + (1 + lam) * (C₀ * Real.sqrt p' / W)) /
                (1 - (1 + qq) / 2) + B * τ ^ (1 / p'))) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hτ0 (by positivity), ← ENNReal.ofReal_mul hB0,
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc (1 + 1 / lam) * (((1 + qq) / 2) ^ n * B +
              ((1 + lam) * C₀ / (W : ℝ) ^ 2 + (1 + lam) * (C₀ * Real.sqrt p' / W)) /
                (1 - (1 + qq) / 2) + B * τ ^ (1 / p'))
            ≤ (1 + 1 / lam) * ((B + (1 + lam) * C₀ * (1 + Real.sqrt p') /
                (1 - (1 + qq) / 2) + 1) / W) :=
              mul_le_mul_of_nonneg_left hfin (by positivity)
          _ = _ := by ring

/-- The exit term of the jet bound: `(BW)^{p'} τ ≤ 1 ⇒ B τ^{1/p'} ≤ 1/W`. -/
theorem tail_root_le {B τ p' : ℝ} {W : ℕ} (hB : 0 < B) (hW : (0 : ℝ) < W) (hτ0 : 0 ≤ τ)
    (hp' : 0 < p') (ht : (B * W) ^ p' * τ ≤ 1) : B * τ ^ (1 / p') ≤ 1 / W := by
  have hBW : 0 < B * W := by positivity
  have hprod : ((B * W) ^ p' * τ) ^ (1 / p') ≤ 1 :=
    Real.rpow_le_one (by positivity) ht (by positivity)
  rw [Real.mul_rpow (by positivity) hτ0, ← Real.rpow_mul hBW.le,
    mul_one_div_cancel hp'.ne', Real.rpow_one] at hprod
  rw [le_div_iff₀ hW]
  calc B * τ ^ (1 / p') * W = B * W * τ ^ (1 / p') := by ring
    _ ≤ 1 := hprod

/-- **The unstopped clock bound at a fixed `W`** (assembled). -/
theorem clock_final (hW0 : 0 < W) {q : ℝ → ℝ} (hq0 : ∀ x, 0 ≤ q x)
    {D : Matrix (Fin W) (Fin W) ℂ} (j : ℕ) {P : ℕ} (hP : 1 ≤ P) {p A G τ : ℝ} (hpP : p ≤ P)
    (hA : 0 ≤ A) (hτ0 : 0 ≤ τ) {Bad : Set (Fin j → OneEndedLayer W)}
    (hc : ∫⁻ ω, ENNReal.ofReal (clockU (oneEndedY b E q D j ω) ^ P) ∂oneEndedLaw W b j ≤
      ENNReal.ofReal ((A * ((j : ℝ) + 1)) ^ P) +
        ENNReal.ofReal (G ^ j) * oneEndedLaw W b j Bad ^ (1 / 2 : ℝ))
    (hβ : oneEndedLaw W b j Bad ≤ ENNReal.ofReal τ) (hG0 : 0 ≤ G)
    (hGτ : G ^ j * Real.sqrt τ ≤ 1) :
    eLpNorm (oneEndedGamma b E q D j) (ENNReal.ofReal p) (oneEndedLaw W b j) ≤
      ENNReal.ofReal ((A + 1) * ((j : ℝ) + 1) / W) := by
  have hmom : ∫⁻ ω, ENNReal.ofReal (clockU (oneEndedY b E q D j ω) ^ P) ∂oneEndedLaw W b j ≤
      ENNReal.ofReal (((A + 1) * ((j : ℝ) + 1)) ^ P) := by
    refine hc.trans ?_
    have e1 : ENNReal.ofReal (G ^ j) * oneEndedLaw W b j Bad ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal 1 := by
      calc ENNReal.ofReal (G ^ j) * oneEndedLaw W b j Bad ^ (1 / 2 : ℝ)
          ≤ ENNReal.ofReal (G ^ j) * ENNReal.ofReal τ ^ (1 / 2 : ℝ) := by gcongr
        _ = ENNReal.ofReal (G ^ j * Real.sqrt τ) := by
            rw [ENNReal.ofReal_rpow_of_nonneg hτ0 (by norm_num), ← Real.sqrt_eq_rpow,
              ← ENNReal.ofReal_mul (by positivity)]
        _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal hGτ
    refine (add_le_add le_rfl e1).trans ?_
    rw [← ENNReal.ofReal_add (by positivity) zero_le_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have hx : 0 ≤ A * ((j : ℝ) + 1) := by positivity
    have h1 := pow_add_one_ge hx P hP
    have h2 : A * ((j : ℝ) + 1) + 1 ≤ (A + 1) * ((j : ℝ) + 1) := by
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      nlinarith
    exact h1.trans (pow_le_pow_left₀ (by positivity) h2 P)
  have hγ := eLpNorm_gamma_le (b := b) (E := E) hW0 hq0 D j P hP (by positivity) hmom
  exact (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hpP)).trans hγ

/-- `G^j √τ ≤ 1` from `L^W τ ≤ 1`, `L = G^{2⌈T'⌉}`, `j ≤ ⌈T'⌉ W`. -/
theorem clock_tail_le {G τ : ℝ} (hG : 1 ≤ G) (hτ0 : 0 ≤ τ) {j m W : ℕ} (hj : j ≤ m * W)
    (ht : (G ^ (2 * m)) ^ W * τ ≤ 1) : G ^ j * Real.sqrt τ ≤ 1 := by
  have hG2 : (G ^ j) ^ 2 ≤ (G ^ (2 * m)) ^ W := by
    rw [← pow_mul, ← pow_mul]
    exact pow_le_pow_right₀ hG (by nlinarith)
  have hprod : (G ^ j) ^ 2 * τ ≤ 1 :=
    (mul_le_mul_of_nonneg_right hG2 hτ0).trans ht
  have hGj : 0 ≤ G ^ j := by positivity
  rw [← Real.sqrt_sq hGj, ← Real.sqrt_mul (by positivity)]
  exact Real.sqrt_le_one.mpr hprod

/-- `K √(aW)/W ≤ (K√a + 1)/√W`. -/
theorem base_comp {K a : ℝ} {W : ℕ} (ha : 0 < a) (hW : (0 : ℝ) < W) :
    K * Real.sqrt (a * W) / W ≤ (K * Real.sqrt a + 1) / Real.sqrt W := by
  have hsW : 0 < Real.sqrt W := Real.sqrt_pos.mpr hW
  rw [Real.sqrt_mul ha.le, div_le_div_iff₀ hW hsW]
  have hs : Real.sqrt W * Real.sqrt W = W := Real.mul_self_sqrt hW.le
  have : K * (Real.sqrt a * Real.sqrt W) * Real.sqrt W = K * Real.sqrt a * W := by
    rw [mul_assoc, mul_assoc, hs]; ring
  rw [this]
  nlinarith

/-- The large-`W` facts used by the assembly. -/
theorem large_W_facts {a a₀ ae p' C₀ ρ : ℝ} (ha : 0 < a) (ha₀ : 0 < a₀) (hρ0 : 0 < ρ)
    (haa₀ : a ≤ a₀) (haae : a ≤ ae) (hC₀ : 0 ≤ C₀) {W : ℕ}
    (hW : ⌈2 / a⌉₊ + ⌈p' / a₀⌉₊ + ⌈C₀ / ρ⌉₊ + 1 ≤ W) :
    (1 : ℝ) ≤ W ∧ 2 ≤ a * W ∧ a * W ≤ a₀ * W ∧ a * W ≤ ae * W ∧ p' ≤ a₀ * W ∧
      C₀ / (W : ℝ) ^ 2 ≤ ρ := by
  have hWm : ((⌈2 / a⌉₊ + ⌈p' / a₀⌉₊ + ⌈C₀ / ρ⌉₊ + 1 : ℕ) : ℝ) ≤ W := by exact_mod_cast hW
  push_cast at hWm
  have hc1 := Nat.le_ceil (2 / a)
  have hc2 := Nat.le_ceil (p' / a₀)
  have hc3 := Nat.le_ceil (C₀ / ρ)
  have hn1 : (0 : ℝ) ≤ ⌈2 / a⌉₊ := Nat.cast_nonneg _
  have hn2 : (0 : ℝ) ≤ ⌈p' / a₀⌉₊ := Nat.cast_nonneg _
  have hn3 : (0 : ℝ) ≤ ⌈C₀ / ρ⌉₊ := Nat.cast_nonneg _
  have hW1 : (1 : ℝ) ≤ W := by linarith
  have hWr : (0 : ℝ) < W := by linarith
  refine ⟨hW1, ?_, mul_le_mul_of_nonneg_right haa₀ hWr.le, mul_le_mul_of_nonneg_right haae hWr.le,
    ?_, ?_⟩
  · have : 2 / a ≤ W := by linarith
    rwa [div_le_iff₀ ha, mul_comm] at this
  · have : p' / a₀ ≤ W := by linarith
    rwa [div_le_iff₀ ha₀, mul_comm] at this
  · have h1 : C₀ / ρ ≤ W := by linarith
    have h2 : C₀ ≤ ρ * W := by rwa [div_le_iff₀ hρ0, mul_comm] at h1
    rw [div_le_iff₀ (by positivity)]
    nlinarith

/-- **The input moments of the open-inputs lemma** (`OpenInputsMoments`), proved from
`GaussianAbsorptionContract`, `TraceMatrixContract` and `WeightedLayerContract`.
-/
theorem openInputsMoments_of (hGA : GaussianAbsorptionContract) (hTM : TraceMatrixContract)
    (hWL : WeightedLayerContract) : OpenInputsMoments := by
  intro b hb0 hb1 E hE0 hE1 T q hq p hp
  have hE : |E| ≤ 2 := abs_le.mpr ⟨hE0.le, hE1.le⟩
  have hzpos : 0 < (boundaryZ b E).im := by
    rw [BlockBand.Layers.boundaryZ_im hE]
    have := BlockBand.Layers.matchedA_im_neg (abs_lt.mpr ⟨hE0, hE1⟩)
    have : 0 < 1 - b := by linarith
    nlinarith
  have hq0 : ∀ x, 0 ≤ q x := hq.2.1
  have hp'2 : 2 ≤ max p 2 := le_max_right _ _
  have hpp' : p ≤ max p 2 := le_max_left _ _
  have hP2 : 2 ≤ ⌈p⌉₊ + 2 := by omega
  have hpP : p ≤ ((⌈p⌉₊ + 2 : ℕ) : ℝ) := by
    have := Nat.le_ceil p
    push_cast; linarith
  obtain ⟨rs, qq, Cst, C₀, a₀, hF⟩ := oneStepFacts_of (cavityMean_of hGA hTM) hb0 hb1 hE0 hE1
  obtain ⟨r₁, hr₁, hclock⟩ := clock_moment_raw
    (clockStep_of (onePortWeighted_of hWL hGA) hGA hTM) hb0 hb1 hE0 hE1 hq T hP2
  have hr₀ : 0 < min rs r₁ := lt_min hF.1 hr₁
  have hF0 := hF.mono hr₀ (min_le_left _ _)
  obtain ⟨J, ε, ae, Ke, We, hε, hae, hKe0, hent⟩ :=
    entrance_bound (zeroEntrance_of_contracts hGA hTM) hb0 hb1 hE0 hE1 hr₀
  obtain ⟨A, G, Wc, hA, hG, hclk⟩ := hclock (min rs r₁) hr₀ (min_le_right _ _) J
  have hF1 := hF0
  obtain ⟨-, hqq0, hqq1, hCst, hC₀, ha₀, -⟩ := hF1
  have hθ0 : 0 < (1 + qq) / 2 := by linarith
  have hθ1 : (1 + qq) / 2 < 1 := by linarith
  have hlam0 : 0 < (1 - qq) / (2 * (Cst + 1)) := div_pos (by linarith) (by positivity)
  have hρ0 : 0 < (1 - qq) * min rs r₁ / 2 := by
    have : 0 < 1 - qq := by linarith
    positivity
  have ha : 0 < min a₀ ae := lt_min ha₀ hae
  have hKt0 : 0 ≤ max Ke (C₀ / ((1 - qq) * min rs r₁ / 2)) := hKe0.trans (le_max_left _ _)
  have hκ0 : 0 < max Ke (C₀ / ((1 - qq) * min rs r₁ / 2)) * Real.sqrt (min a₀ ae) + 1 := by
    positivity
  have hT'0 : 0 ≤ max T 0 := le_max_right _ _
  have hdS : 0 ≤ dStar b := by unfold dStar; have : 0 < 1 - b := by linarith
                               positivity
  have hB0 : 0 < 1 / (boundaryZ b E).im + 1 + (1 - qq) / (2 * (Cst + 1)) *
      (1 / (boundaryZ b E).im ^ 2 + dStar b) := by positivity
  obtain ⟨Wg, hWg⟩ := geom_small hθ0 hθ1 J
  obtain ⟨Wt1, hWt1⟩ := tail_small hB0 (by linarith : (0 : ℝ) ≤ max p 2) le_rfl hT'0 hκ0 ha
  obtain ⟨Wt2, hWt2⟩ := tail_small (B := 1) (m := 0) (L := G ^ (2 * ⌈max T 0⌉₊)) one_pos le_rfl
    (one_le_pow₀ hG) hT'0 hκ0 ha
  have hgap : 0 < 1 - (1 + qq) / 2 := by linarith
  refine ⟨ε, max ((1 + 1 / ((1 - qq) / (2 * (Cst + 1)))) *
      ((1 / (boundaryZ b E).im + 1 + (1 - qq) / (2 * (Cst + 1)) *
          (1 / (boundaryZ b E).im ^ 2 + dStar b)) +
        (1 + (1 - qq) / (2 * (Cst + 1))) * C₀ * (1 + Real.sqrt (max p 2)) /
          (1 - (1 + qq) / 2) + 1)) (A + 1),
    max (max (max We Wc) (max Wg (max Wt1 Wt2)))
      (⌈2 / min a₀ ae⌉₊ + ⌈max p 2 / a₀⌉₊ + ⌈C₀ / ((1 - qq) * min rs r₁ / 2)⌉₊ + 1), hε, ?_⟩
  intro W hW D hD hDε
  have hWe : We ≤ W := le_trans (le_max_left _ _) (le_trans (le_max_left _ _)
    (le_trans (le_max_left _ _) hW))
  have hWc : Wc ≤ W := le_trans (le_max_right _ _) (le_trans (le_max_left _ _)
    (le_trans (le_max_left _ _) hW))
  have hWg' : Wg ≤ W := le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
    (le_trans (le_max_left _ _) hW))
  have hWt1' : Wt1 ≤ W := le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hW)))
  have hWt2' : Wt2 ≤ W := le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hW)))
  obtain ⟨hW1, hP2W, hPa₀, hPae, hp'a, hCW⟩ := large_W_facts ha ha₀ hρ0 (min_le_left _ _)
    (min_le_right _ _) hC₀ (le_trans (le_max_right _ _) hW)
  have hWr : (0 : ℝ) < W := by linarith
  have hW0 : 0 < W := by exact_mod_cast hWr
  have hρW : (1 - qq) * min rs r₁ / 2 + C₀ / (W : ℝ) ^ 2 ≤ (1 - qq) * min rs r₁ := by
    linarith
  have hentW := hent W hWe D hD hDε (min a₀ ae * W) hP2W hPae
  have hτ0 : 0 ≤ (1 + max T 0 * W) *
      ((max Ke (C₀ / ((1 - qq) * min rs r₁ / 2)) * Real.sqrt (min a₀ ae) + 1) / Real.sqrt W) ^
        (min a₀ ae * W) := by positivity
  have hβ : ∀ j : ℕ, (j : ℝ) ≤ T * W →
      oneEndedLaw W b j (goodSet b E D (min rs r₁) J j)ᶜ ≤ ENNReal.ofReal ((1 + max T 0 * W) *
        ((max Ke (C₀ / ((1 - qq) * min rs r₁ / 2)) * Real.sqrt (min a₀ ae) + 1) / Real.sqrt W) ^
          (min a₀ ae * W)) := by
    intro j hj
    have hj' : (j : ℝ) ≤ max T 0 * W :=
      hj.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hWr.le)
    refine (beta_bound hF0 hW0 hD J hρ0 hρW hP2W hPa₀ hentW hKe0
      (le_max_left _ _) (le_max_right _ _) j hj').trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity)
      (base_comp ha hWr) (by positivity)) (by positivity)
  refine ⟨fun s hs j hj0 hjT => ?_, fun j hjT => ?_⟩
  · obtain ⟨hJj0, hgeom⟩ := hWg W hWg'
    obtain ⟨n, rfl⟩ : ∃ n, j = J + n := ⟨j - J, by omega⟩
    have ht := hWt1 W hWt1'
    rw [one_pow, mul_one, mul_assoc] at ht
    refine (jet_final hF0 hW0 hW1 hD hzpos hE hs J n hpp' hp'2 hp'a hτ0 (hgeom n hj0)
      (hβ (J + n) hjT) (tail_root_le hB0 hWr hτ0 (by linarith) ht)).trans
      (ENNReal.ofReal_le_ofReal ?_)
    exact div_le_div_of_nonneg_right (le_max_left _ _) hWr.le
  · have hjN : j ≤ ⌈max T 0⌉₊ * W := by
      have h1 : (j : ℝ) ≤ max T 0 * W :=
        hjT.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hWr.le)
      have h2 : max T 0 * W ≤ (⌈max T 0⌉₊ : ℝ) * W :=
        mul_le_mul_of_nonneg_right (Nat.le_ceil _) hWr.le
      exact_mod_cast h1.trans h2
    have ht := hWt2 W hWt2'
    rw [Real.rpow_zero, one_mul, mul_assoc] at ht
    have hGτ := clock_tail_le hG hτ0 hjN ht
    refine (clock_final hW0 hq0 j (by omega) hpP hA hτ0 (hclk W hWc D hD j hjT) (hβ j hjT)
      (by linarith) hGτ).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

end OpenInputsProof

end BlockBand.Endpoints.Clock
