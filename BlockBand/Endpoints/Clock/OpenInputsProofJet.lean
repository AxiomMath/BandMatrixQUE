module

public import BlockBand.Endpoints.Clock.OpenInputsProofChain

/-!
# The open-inputs lemma: `L^p` recursion before the exit, and the exit set

We iterate the one-step bounds for the scalar and the first jet along the one-ended chain.

With `Φ_j = δ₀(X_j) + λ δ₁(X_j)` (`λ = (1-q)/(2(C+1))`, so that one step contracts `Φ` by
`θ = (1+q)/2 < 1` on the scalar domain), and the "no exit" events `G_j = goodSet` (`δ₀(X_i) ≤ r₀`
for `J ≤ i ≤ j`):
* `phi_recursion`: `‖1_{G_{j+1}} Φ_{j+1}‖_p ≤ θ ‖1_{G_j} Φ_j‖_p + c W⁻² + c √p/W` for
  `j ≥ J`, `2 ≤ p ≤ a₀W` (Minkowski's inequality and the geometric sum);
* `phi_good_bound`: hence `‖1_{G_{J+n}} Φ_{J+n}‖_p ≤ θⁿ B + F/(1-θ)`, with the deterministic
  bound `Φ ≤ B` (`phi_le_ae`: the trace is deterministically bounded by `(Im z)⁻¹`);
* `bad_bound`: the exit probability recursion `P(G_{J+n}ᶜ) ≤ P(G_Jᶜ) + n·max_i P(N₀ ≥ ρ)`
  (to leave the scalar domain for the first time, a step needs a fresh error of fixed size), with
  the fresh tail by Markov at order `P` (`tail_bound`);
* `phi_split`: `‖Φ_j‖_p ≤ θ^{j-J} B + F/(1-θ) + B P(G_jᶜ)^{1/p}`.
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

/-- The conclusion of `one_step`, at the scalar radius `r₀`. -/
def OneStepFacts (b E r₀ q Cst C₀ a₀ : ℝ) : Prop :=
  0 < r₀ ∧ 0 ≤ q ∧ q < 1 ∧ 0 ≤ Cst ∧ 0 ≤ C₀ ∧ 0 < a₀ ∧
    ∀ W : ℕ, 0 < W → ∀ X : Matrix (Fin W) (Fin W) ℂ, X.IsHermitian →
      (∀ p : ℝ, 2 ≤ p → p ≤ a₀ * W →
        eLpNorm (freshNoise0 b E X) (ENNReal.ofReal p) (freshLaw W b) ≤
            ENNReal.ofReal (C₀ * Real.sqrt p / W) ∧
          eLpNorm (freshNoise1 b E X) (ENNReal.ofReal p) (freshLaw W b) ≤
            ENNReal.ofReal (C₀ * Real.sqrt p / W)) ∧
      (jetDistance0 b E X ≤ r₀ → ∀ y : OneEndedLayer W,
        jetDistance0 b E (freshSchur E X y) ≤
            q * jetDistance0 b E X + C₀ / (W : ℝ) ^ 2 + freshNoise0 b E X y ∧
          ∀ s : ℂ, IsStationaryJet b E s →
            jetDistance1 b E s (freshSchur E X y) ≤
              q * jetDistance1 b E s X + Cst * jetDistance0 b E X + C₀ / (W : ℝ) ^ 2 +
                freshNoise1 b E X y)

theorem oneStepFacts_of (hQ : CavityMeanStatement) {b E : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2)
    (hE0 : -2 < E) (hE1 : E < 2) :
    ∃ r₀ q Cst C₀ a₀ : ℝ, OneStepFacts b E r₀ q Cst C₀ a₀ :=
  one_step hQ hb0 hb1 hE0 hE1

theorem OneStepFacts.mono {b E r₀ q Cst C₀ a₀ r : ℝ} (h : OneStepFacts b E r₀ q Cst C₀ a₀)
    (hr : 0 < r) (hrr : r ≤ r₀) : OneStepFacts b E r q Cst C₀ a₀ := by
  obtain ⟨-, hq0, hq1, hC, hC₀, ha₀, hs⟩ := h
  refine ⟨hr, hq0, hq1, hC, hC₀, ha₀, fun W hW X hX => ⟨(hs W hW X hX).1, fun hδ y => ?_⟩⟩
  exact (hs W hW X hX).2 (hδ.trans hrr) y

variable {W : ℕ} {b E : ℝ}

/-!
## Deterministic bounds
-/

theorem jetDistance0_le (hW : 0 < W) {X : Matrix (Fin W) (Fin W) ℂ} (hX : X.IsHermitian)
    (hz : 0 < (boundaryZ b E).im) (hE : |E| ≤ 2) :
    jetDistance0 b E X ≤ 1 / (boundaryZ b E).im + 1 := by
  rw [jetDistance0_eq]
  refine (norm_sub_le _ _).trans ?_
  rw [BlockBand.Layers.norm_matchedA hE]
  linarith [norm_normalizedResolventTrace_le hW hX hz]

theorem jetDistance1_le (hW : 0 < W) {X : Matrix (Fin W) (Fin W) ℂ} (hX : X.IsHermitian)
    (hz : 0 < (boundaryZ b E).im) {s : ℂ} (hs : IsStationaryJet b E s) :
    jetDistance1 b E s X ≤ 1 / (boundaryZ b E).im ^ 2 + dStar b := by
  rw [jetDistance1_eq, (hasDerivAt_normalizedResolventTrace hX hz).deriv]
  refine (norm_sub_le _ _).trans (add_le_add ?_ hs.2)
  rw [norm_neg]
  exact (norm_kerK_self_le (isCavityWeights_uniform hW) _).trans
    (CavityMean.cavitySq_le _ (isCavityWeights_uniform hW) hz)

/-!
## The `L^p` recursion before the exit
-/

section Rec

variable {s : ℂ} {D : Matrix (Fin W) (Fin W) ℂ}

/-- The pathwise one-step bound for `1_{G} Φ`. -/
theorem phi_step_ae {r₀ q Cst C₀ a₀ : ℝ} (hF : OneStepFacts b E r₀ q Cst C₀ a₀) (hW : 0 < W)
    (hD : D.IsHermitian) (hs : IsStationaryJet b E s) {J j : ℕ} (hJ : J ≤ j) :
    ∀ᵐ ω ∂oneEndedLaw W b (j + 1),
      ‖(goodSet b E D r₀ J (j + 1)).indicator
          (chainPhi b E s D ((1 - q) / (2 * (Cst + 1))) (j + 1)) ω‖ ≤
        (1 + q) / 2 * ‖(goodSet b E D r₀ J j).indicator
            (chainPhi b E s D ((1 - q) / (2 * (Cst + 1))) j) (Fin.init ω)‖ +
          (1 + (1 - q) / (2 * (Cst + 1))) * C₀ / (W : ℝ) ^ 2 +
          chainNoise b E D ((1 - q) / (2 * (Cst + 1))) j (Fin.init ω, ω (Fin.last j)) := by
  obtain ⟨-, hq0, hq1, hCst, hC₀, -, hstep⟩ := hF
  set lam := (1 - q) / (2 * (Cst + 1)) with hlam
  have hlam0 : 0 ≤ lam := by rw [hlam]; have : 0 < 2 * (Cst + 1) := by positivity
                             exact div_nonneg (by linarith) this.le
  have hlamC : lam * Cst ≤ (1 - q) / 2 := by
    rw [hlam, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h1 : ∀ᵐ ω ∂oneEndedLaw W b (j + 1), (oneEndedX E D j (Fin.init ω)).IsHermitian :=
    (measurePreserving_init (freshLaw W b) j).quasiMeasurePreserving.ae
      (ae_X_isHermitian b E hD j)
  filter_upwards [h1] with ω hX
  have hn0 : 0 ≤ freshNoise0 b E (oneEndedX E D j (Fin.init ω)) (ω (Fin.last j)) :=
    norm_nonneg _
  have hn1 : 0 ≤ freshNoise1 b E (oneEndedX E D j (Fin.init ω)) (ω (Fin.last j)) :=
    norm_nonneg _
  have hc0 : 0 ≤ (1 + lam) * C₀ / (W : ℝ) ^ 2 := by positivity
  have hnoise : 0 ≤ chainNoise b E D lam j (Fin.init ω, ω (Fin.last j)) := by
    unfold chainNoise; positivity
  by_cases hω : ω ∈ goodSet b E D r₀ J (j + 1)
  · have hx := init_mem_goodSet hω
    have hδ := chainD0_le_of_mem_goodSet hx hJ
    rw [Set.indicator_of_mem hω, Set.indicator_of_mem hx]
    obtain ⟨hsc, hjet⟩ := (hstep W hW _ hX).2 hδ (ω (Fin.last j))
    have hj1 := hjet s hs
    have hd0 : 0 ≤ chainD0 b E D j (Fin.init ω) := norm_nonneg _
    have hd1 : 0 ≤ chainD1 b E s D j (Fin.init ω) := norm_nonneg _
    have hP : 0 ≤ chainPhi b E s D lam (j + 1) ω :=
      add_nonneg (norm_nonneg _) (mul_nonneg hlam0 (norm_nonneg _))
    have hP' : 0 ≤ chainPhi b E s D lam j (Fin.init ω) := by unfold chainPhi; positivity
    rw [Real.norm_of_nonneg hP, Real.norm_of_nonneg hP']
    have e1 : chainPhi b E s D lam (j + 1) ω =
        jetDistance0 b E (freshSchur E (oneEndedX E D j (Fin.init ω)) (ω (Fin.last j))) +
          lam * jetDistance1 b E s
            (freshSchur E (oneEndedX E D j (Fin.init ω)) (ω (Fin.last j))) := rfl
    have e2 : chainPhi b E s D lam j (Fin.init ω) =
        chainD0 b E D j (Fin.init ω) + lam * chainD1 b E s D j (Fin.init ω) := rfl
    have e3 : chainNoise b E D lam j (Fin.init ω, ω (Fin.last j)) =
        freshNoise0 b E (oneEndedX E D j (Fin.init ω)) (ω (Fin.last j)) +
          lam * freshNoise1 b E (oneEndedX E D j (Fin.init ω)) (ω (Fin.last j)) := rfl
    rw [e1, e2, e3]
    have hlj : lam * jetDistance1 b E s
          (freshSchur E (oneEndedX E D j (Fin.init ω)) (ω (Fin.last j))) ≤
        lam * (q * chainD1 b E s D j (Fin.init ω) + Cst * chainD0 b E D j (Fin.init ω) +
          C₀ / (W : ℝ) ^ 2 + freshNoise1 b E (oneEndedX E D j (Fin.init ω)) (ω (Fin.last j))) :=
      mul_le_mul_of_nonneg_left hj1 hlam0
    have hq' : lam * q * chainD1 b E s D j (Fin.init ω) ≤
        (1 + q) / 2 * (lam * chainD1 b E s D j (Fin.init ω)) := by
      have : lam * chainD1 b E s D j (Fin.init ω) * q ≤
          lam * chainD1 b E s D j (Fin.init ω) * ((1 + q) / 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith
    have hC' : lam * Cst * chainD0 b E D j (Fin.init ω) ≤
        (1 - q) / 2 * chainD0 b E D j (Fin.init ω) := mul_le_mul_of_nonneg_right hlamC hd0
    have hsc' : jetDistance0 b E (freshSchur E (oneEndedX E D j (Fin.init ω)) (ω (Fin.last j))) ≤
        q * chainD0 b E D j (Fin.init ω) + C₀ / (W : ℝ) ^ 2 +
          freshNoise0 b E (oneEndedX E D j (Fin.init ω)) (ω (Fin.last j)) := hsc
    have ec : (1 + lam) * C₀ / (W : ℝ) ^ 2 = C₀ / (W : ℝ) ^ 2 + lam * (C₀ / (W : ℝ) ^ 2) := by
      ring
    nlinarith
  · rw [Set.indicator_of_notMem hω, norm_zero]
    have : 0 ≤ (1 + q) / 2 * ‖(goodSet b E D r₀ J j).indicator
        (chainPhi b E s D lam j) (Fin.init ω)‖ := by
      have : 0 ≤ (1 + q) / 2 := by linarith
      positivity
    linarith

/-- The conditional bound for the combined noise. -/
theorem chainNoise_cond {r₀ q Cst C₀ a₀ : ℝ} (hF : OneStepFacts b E r₀ q Cst C₀ a₀) (hW : 0 < W)
    (hD : D.IsHermitian) {lam : ℝ} (hlam : 0 ≤ lam) (j : ℕ)
    {p : ℝ} (hp2 : 2 ≤ p) (hpa : p ≤ a₀ * W) :
    ∀ᵐ x ∂oneEndedLaw W b j, eLpNorm (fun y => chainNoise b E D lam j (x, y))
      (ENNReal.ofReal p) (freshLaw W b) ≤ ENNReal.ofReal ((1 + lam) * (C₀ * Real.sqrt p / W)) := by
  obtain ⟨-, -, -, -, hC₀, -, hstep⟩ := hF
  filter_upwards [ae_X_isHermitian b E hD j] with x hx
  obtain ⟨h0, h1⟩ := (hstep W hW _ hx).1 p hp2 hpa
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr (by linarith)
  have heq : (fun y => chainNoise b E D lam j (x, y)) =
      (fun y => freshNoise0 b E (oneEndedX E D j x) y) +
        (fun y => lam * freshNoise1 b E (oneEndedX E D j x) y) := rfl
  rw [heq]
  refine (eLpNorm_add_le hp1).trans ?_
  rw [eLpNorm_real_mul, abs_of_nonneg hlam]
  have hb : 0 ≤ C₀ * Real.sqrt p / W := by positivity
  calc eLpNorm (fun y => freshNoise0 b E (oneEndedX E D j x) y) (ENNReal.ofReal p) (freshLaw W b) +
        ENNReal.ofReal lam * eLpNorm (freshNoise1 b E (oneEndedX E D j x)) (ENNReal.ofReal p)
          (freshLaw W b)
      ≤ ENNReal.ofReal (C₀ * Real.sqrt p / W) +
          ENNReal.ofReal lam * ENNReal.ofReal (C₀ * Real.sqrt p / W) := by gcongr
    _ = ENNReal.ofReal ((1 + lam) * (C₀ * Real.sqrt p / W)) := by
        rw [← ENNReal.ofReal_mul hlam, ← ENNReal.ofReal_add hb (by positivity)]
        congr 1; ring

/-- **The `L^p` recursion before the exit**. -/
theorem phi_recursion {r₀ q Cst C₀ a₀ : ℝ} (hF : OneStepFacts b E r₀ q Cst C₀ a₀) (hW : 0 < W)
    (hD : D.IsHermitian) (hz : 0 < (boundaryZ b E).im) (hs : IsStationaryJet b E s) {J j : ℕ}
    (hJ : J ≤ j) {p : ℝ} (hp2 : 2 ≤ p) (hpa : p ≤ a₀ * W) :
    eLpNorm ((goodSet b E D r₀ J (j + 1)).indicator
        (chainPhi b E s D ((1 - q) / (2 * (Cst + 1))) (j + 1))) (ENNReal.ofReal p)
        (oneEndedLaw W b (j + 1)) ≤
      ENNReal.ofReal ((1 + q) / 2) * eLpNorm ((goodSet b E D r₀ J j).indicator
          (chainPhi b E s D ((1 - q) / (2 * (Cst + 1))) j)) (ENNReal.ofReal p)
          (oneEndedLaw W b j) +
        ENNReal.ofReal ((1 + (1 - q) / (2 * (Cst + 1))) * C₀ / (W : ℝ) ^ 2) +
        ENNReal.ofReal ((1 + (1 - q) / (2 * (Cst + 1))) * (C₀ * Real.sqrt p / W)) := by
  have hF' := hF
  obtain ⟨-, hq0, hq1, hCst, hC₀, -, -⟩ := hF'
  have hlam0 : 0 ≤ (1 - q) / (2 * (Cst + 1)) := div_nonneg (by linarith) (by positivity)
  refine eLpNorm_step_le (freshLaw W b) (j := j)
    ((aesm_chainPhi hD hz _ (j + 1)).indicator (measurableSet_goodSet r₀ J (j + 1)))
    ((aesm_chainPhi hD hz _ j).indicator (measurableSet_goodSet r₀ J j))
    (aesm_chainNoise hD hz _ j) (by linarith) (by positivity) (by positivity) (by linarith)
    (phi_step_ae hF hW hD hs hJ) (chainNoise_cond hF hW hD hlam0 j hp2 hpa)

end Rec

/-!
## The exit set
-/

section Exit

variable {s : ℂ} {D : Matrix (Fin W) (Fin W) ℂ}

/-- **Fresh tail** by Markov at order `P`. -/
theorem tail_bound {r₀ q Cst C₀ a₀ : ℝ} (hF : OneStepFacts b E r₀ q Cst C₀ a₀) (hW : 0 < W)
    (hD : D.IsHermitian) (j : ℕ) {ρ P : ℝ} (hρ : 0 < ρ) (hP2 : 2 ≤ P) (hPa : P ≤ a₀ * W) :
    oneEndedLaw W b (j + 1) {ω | ρ ≤ chainNoise0 b E D j (Fin.init ω, ω (Fin.last j))} ≤
      ENNReal.ofReal ((C₀ * Real.sqrt P / W / ρ) ^ P) := by
  obtain ⟨-, -, -, -, hC₀, -, hstep⟩ := hF
  have hB0 : 0 ≤ C₀ * Real.sqrt P / W := by positivity
  refine measure_ge_le_of_eLpNorm hρ (by linarith) hB0 ?_
  refine (eLpNorm_initLast_le (freshLaw W b) j (measurable_chainNoise0 j).aestronglyMeasurable
    (by linarith) (h := fun _ => C₀ * Real.sqrt P / W) ?_).trans ?_
  · filter_upwards [ae_X_isHermitian b E hD j] with x hx
    exact ((hstep W hW _ hx).1 P hP2 hPa).1
  · rw [ZeroEntranceProb.eLpNorm_const_prob _ (by linarith), abs_of_nonneg hB0]

/-- The exit inclusion: leaving the scalar domain at step `j+1` needs a fresh error `≥ ρ`. -/
theorem exit_ae {r₀ q Cst C₀ a₀ : ℝ} (hF : OneStepFacts b E r₀ q Cst C₀ a₀) (hW : 0 < W)
    (hD : D.IsHermitian) {J j : ℕ} (hJ : J ≤ j) {ρ : ℝ}
    (hρ : ρ + C₀ / (W : ℝ) ^ 2 ≤ (1 - q) * r₀) :
    ∀ᵐ ω ∂oneEndedLaw W b (j + 1), ω ∈ (goodSet b E D r₀ J (j + 1))ᶜ →
      Fin.init ω ∈ (goodSet b E D r₀ J j)ᶜ ∨
        ρ ≤ chainNoise0 b E D j (Fin.init ω, ω (Fin.last j)) := by
  obtain ⟨-, hq0, -, -, -, -, hstep⟩ := hF
  have h1 : ∀ᵐ ω ∂oneEndedLaw W b (j + 1), (oneEndedX E D j (Fin.init ω)).IsHermitian :=
    (measurePreserving_init (freshLaw W b) j).quasiMeasurePreserving.ae
      (ae_X_isHermitian b E hD j)
  filter_upwards [h1] with ω hX hω
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hg, hn⟩ := hcon
  have hg' : Fin.init ω ∈ goodSet b E D r₀ J j := not_not.mp hg
  have hn' : chainNoise0 b E D j (Fin.init ω, ω (Fin.last j)) < ρ := not_le.mp hn
  have hδ := chainD0_le_of_mem_goodSet hg' hJ
  obtain ⟨hsc, -⟩ := (hstep W hW _ hX).2 hδ (ω (Fin.last j))
  apply hω
  refine ⟨hg', fun _ => ?_⟩
  have e : chainD0 b E D (j + 1) ω =
      jetDistance0 b E (freshSchur E (oneEndedX E D j (Fin.init ω)) (ω (Fin.last j))) := rfl
  have e2 : chainNoise0 b E D j (Fin.init ω, ω (Fin.last j)) =
      freshNoise0 b E (oneEndedX E D j (Fin.init ω)) (ω (Fin.last j)) := rfl
  rw [e]
  rw [e2] at hn'
  have hq : q * chainD0 b E D j (Fin.init ω) ≤ q * r₀ := mul_le_mul_of_nonneg_left hδ hq0
  have hsc' : jetDistance0 b E (freshSchur E (oneEndedX E D j (Fin.init ω)) (ω (Fin.last j))) ≤
      q * chainD0 b E D j (Fin.init ω) + C₀ / (W : ℝ) ^ 2 +
        freshNoise0 b E (oneEndedX E D j (Fin.init ω)) (ω (Fin.last j)) := hsc
  linarith

/-- **The exit probability recursion**: `P(G_{J+n}ᶜ) ≤ P(G_Jᶜ) + n M`. -/
theorem bad_bound {r₀ q Cst C₀ a₀ : ℝ} (hF : OneStepFacts b E r₀ q Cst C₀ a₀) (hW : 0 < W)
    (hD : D.IsHermitian) (J : ℕ) {ρ P : ℝ} (hρ0 : 0 < ρ)
    (hρ : ρ + C₀ / (W : ℝ) ^ 2 ≤ (1 - q) * r₀) (hP2 : 2 ≤ P) (hPa : P ≤ a₀ * W) :
    ∀ n : ℕ, oneEndedLaw W b (J + n) (goodSet b E D r₀ J (J + n))ᶜ ≤
      oneEndedLaw W b J (goodSet b E D r₀ J J)ᶜ +
        n * ENNReal.ofReal ((C₀ * Real.sqrt P / W / ρ) ^ P) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have h := measure_step_le (freshLaw W b) (j := J + n)
      (A := (goodSet b E D r₀ J (J + n + 1))ᶜ) (A' := (goodSet b E D r₀ J (J + n))ᶜ)
      (measurableSet_goodSet r₀ J (J + n)).compl (exit_ae hF hW hD (by omega) hρ)
    have ht := tail_bound hF hW hD (J + n) hρ0 hP2 hPa
    calc oneEndedLaw W b (J + (n + 1)) (goodSet b E D r₀ J (J + (n + 1)))ᶜ
        ≤ oneEndedLaw W b (J + n) (goodSet b E D r₀ J (J + n))ᶜ +
            ENNReal.ofReal ((C₀ * Real.sqrt P / W / ρ) ^ P) := h.trans (add_le_add le_rfl ht)
      _ ≤ _ := by
          rw [Nat.cast_succ, add_mul, one_mul, ← add_assoc]
          exact add_le_add ih le_rfl

end Exit

/-- Geometric decay for an `ℝ≥0∞`-valued recursion. -/
theorem geom_decay {a : ℕ → ℝ≥0∞} {θ A F : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hA : 0 ≤ A)
    (hF : 0 ≤ F) (h0 : a 0 ≤ ENNReal.ofReal A)
    (hs : ∀ n, a (n + 1) ≤ ENNReal.ofReal θ * a n + ENNReal.ofReal F) :
    ∀ n, a n ≤ ENNReal.ofReal (θ ^ n * A + F / (1 - θ)) := by
  have h1θ : 0 < 1 - θ := by linarith
  intro n
  induction n with
  | zero =>
    refine h0.trans (ENNReal.ofReal_le_ofReal ?_)
    have : 0 ≤ F / (1 - θ) := by positivity
    simp only [pow_zero, one_mul]; linarith
  | succ n ih =>
    have hB : 0 ≤ θ ^ n * A + F / (1 - θ) := by positivity
    calc a (n + 1) ≤ ENNReal.ofReal θ * a n + ENNReal.ofReal F := hs n
      _ ≤ ENNReal.ofReal θ * ENNReal.ofReal (θ ^ n * A + F / (1 - θ)) + ENNReal.ofReal F := by
          gcongr
      _ = ENNReal.ofReal (θ * (θ ^ n * A + F / (1 - θ)) + F) := by
          rw [← ENNReal.ofReal_mul hθ0, ← ENNReal.ofReal_add (mul_nonneg hθ0 hB) hF]
      _ = ENNReal.ofReal (θ ^ (n + 1) * A + F / (1 - θ)) := by
          congr 1; field_simp; ring

/-!
## Assembly of the scalar and first-jet bounds
-/

section Assembly

variable {s : ℂ} {D : Matrix (Fin W) (Fin W) ℂ}

/-- The deterministic bound `Φ ≤ B`. -/
theorem phi_le_ae (hW : 0 < W) (hD : D.IsHermitian) (hz : 0 < (boundaryZ b E).im)
    (hE : |E| ≤ 2) (hs : IsStationaryJet b E s) {lam : ℝ} (hlam : 0 ≤ lam) (j : ℕ) :
    ∀ᵐ ω ∂oneEndedLaw W b j, ‖chainPhi b E s D lam j ω‖ ≤
      1 / (boundaryZ b E).im + 1 + lam * (1 / (boundaryZ b E).im ^ 2 + dStar b) := by
  filter_upwards [ae_X_isHermitian b E hD j] with ω hω
  have h0 := jetDistance0_le hW hω hz hE (b := b)
  have h1 := jetDistance1_le hW hω hz hs
  have hP : 0 ≤ chainPhi b E s D lam j ω :=
    add_nonneg (norm_nonneg _) (mul_nonneg hlam (norm_nonneg _))
  rw [Real.norm_of_nonneg hP]
  have := mul_le_mul_of_nonneg_left h1 hlam
  unfold chainPhi chainD0 chainD1
  linarith

/-- `‖1_{G_{J+n}} Φ_{J+n}‖_p ≤ θⁿB + F/(1-θ)`. -/
theorem phi_good_bound {r₀ q Cst C₀ a₀ : ℝ} (hF : OneStepFacts b E r₀ q Cst C₀ a₀)
    (hW : 0 < W) (hD : D.IsHermitian) (hz : 0 < (boundaryZ b E).im) (hE : |E| ≤ 2)
    (hs : IsStationaryJet b E s) (J : ℕ) {p : ℝ} (hp2 : 2 ≤ p) (hpa : p ≤ a₀ * W) (n : ℕ) :
    eLpNorm ((goodSet b E D r₀ J (J + n)).indicator
        (chainPhi b E s D ((1 - q) / (2 * (Cst + 1))) (J + n))) (ENNReal.ofReal p)
        (oneEndedLaw W b (J + n)) ≤
      ENNReal.ofReal (((1 + q) / 2) ^ n *
          (1 / (boundaryZ b E).im + 1 + (1 - q) / (2 * (Cst + 1)) *
            (1 / (boundaryZ b E).im ^ 2 + dStar b)) +
        ((1 + (1 - q) / (2 * (Cst + 1))) * C₀ / (W : ℝ) ^ 2 +
          (1 + (1 - q) / (2 * (Cst + 1))) * (C₀ * Real.sqrt p / W)) / (1 - (1 + q) / 2)) := by
  have hF' := hF
  obtain ⟨-, hq0, hq1, hCst, hC₀, -, -⟩ := hF'
  have hlam0 : 0 ≤ (1 - q) / (2 * (Cst + 1)) := div_nonneg (by linarith) (by positivity)
  have hd : 0 ≤ dStar b := (norm_nonneg s).trans hs.2
  have hB : 0 ≤ 1 / (boundaryZ b E).im + 1 + (1 - q) / (2 * (Cst + 1)) *
      (1 / (boundaryZ b E).im ^ 2 + dStar b) := by positivity
  refine geom_decay (a := fun n => eLpNorm ((goodSet b E D r₀ J (J + n)).indicator
      (chainPhi b E s D ((1 - q) / (2 * (Cst + 1))) (J + n))) (ENNReal.ofReal p)
      (oneEndedLaw W b (J + n))) (by linarith) (by linarith) hB (by positivity) ?_ ?_ n
  · refine (eLpNorm_mono_ae ((aesm_chainPhi hD hz _ (J + 0)).indicator
      (measurableSet_goodSet r₀ J (J + 0))) (g := fun _ => 1 / (boundaryZ b E).im + 1 +
        (1 - q) / (2 * (Cst + 1)) * (1 / (boundaryZ b E).im ^ 2 + dStar b)) ?_).trans ?_
    · filter_upwards [phi_le_ae hW hD hz hE hs hlam0 (J + 0)] with ω hω
      rw [Real.norm_of_nonneg hB]
      by_cases h : ω ∈ goodSet b E D r₀ J (J + 0)
      · rw [Set.indicator_of_mem h]; exact hω
      · rw [Set.indicator_of_notMem h, norm_zero]; exact hB
    · rw [ZeroEntranceProb.eLpNorm_const_prob _ (by linarith), abs_of_nonneg hB]
  · intro n
    have h := phi_recursion hF hW hD hz hs (J := J) (j := J + n) (by omega) hp2 hpa
    refine h.trans (le_of_eq ?_)
    rw [add_assoc, ← ENNReal.ofReal_add (by positivity) (by positivity)]

/-- `‖Φ_j‖_p ≤ (bound on the good set) + B P(G_jᶜ)^{1/p}`. -/
theorem phi_split {r₀ : ℝ} (hW : 0 < W) (hD : D.IsHermitian) (hz : 0 < (boundaryZ b E).im)
    (hE : |E| ≤ 2) (hs : IsStationaryJet b E s) {lam : ℝ} (hlam : 0 ≤ lam) (J j : ℕ) {p : ℝ}
    (hp : 1 ≤ p) :
    eLpNorm (chainPhi b E s D lam j) (ENNReal.ofReal p) (oneEndedLaw W b j) ≤
      eLpNorm ((goodSet b E D r₀ J j).indicator (chainPhi b E s D lam j)) (ENNReal.ofReal p)
          (oneEndedLaw W b j) +
        ENNReal.ofReal (1 / (boundaryZ b E).im + 1 + lam * (1 / (boundaryZ b E).im ^ 2 + dStar b)) *
          oneEndedLaw W b j (goodSet b E D r₀ J j)ᶜ ^ (1 / p) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hp
  have hd : 0 ≤ dStar b := (norm_nonneg s).trans hs.2
  set B := 1 / (boundaryZ b E).im + 1 + lam * (1 / (boundaryZ b E).im ^ 2 + dStar b) with hBdef
  have hB : 0 ≤ B := by rw [hBdef]; positivity
  have hm := measurableSet_goodSet (b := b) (E := E) (D := D) r₀ J j
  rw [← Set.indicator_self_add_compl (goodSet b E D r₀ J j) (chainPhi b E s D lam j)]
  refine (eLpNorm_add_le hp1).trans (add_le_add ?_ ?_)
  · rw [Set.indicator_self_add_compl]
  · refine (eLpNorm_mono_ae ((aesm_chainPhi hD hz lam j).indicator hm.compl)
      (g := (goodSet b E D r₀ J j)ᶜ.indicator fun _ => B) ?_).trans ?_
    · filter_upwards [phi_le_ae hW hD hz hE hs hlam j] with ω hω
      by_cases h : ω ∈ (goodSet b E D r₀ J j)ᶜ
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, Real.norm_of_nonneg hB]
        exact hω
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
    · rw [eLpNorm_indicator_const hm.compl.nullMeasurableSet (by simpa using (by linarith : (0:ℝ) < p))
        ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (by linarith), Real.enorm_eq_ofReal_abs,
        abs_of_nonneg hB]

/-- `‖δ₀‖_p + ‖δ₁‖_p ≤ (1 + λ⁻¹) ‖Φ‖_p`. -/
theorem jet_le_phi (hD : D.IsHermitian) (hz : 0 < (boundaryZ b E).im) {lam : ℝ}
    (hlam : 0 < lam) (j : ℕ) (p : ℝ≥0∞) :
    eLpNorm (chainD0 b E D j) p (oneEndedLaw W b j) +
        eLpNorm (chainD1 b E s D j) p (oneEndedLaw W b j) ≤
      ENNReal.ofReal (1 + 1 / lam) * eLpNorm (chainPhi b E s D lam j) p (oneEndedLaw W b j) := by
  have h0 : eLpNorm (chainD0 b E D j) p (oneEndedLaw W b j) ≤
      eLpNorm (chainPhi b E s D lam j) p (oneEndedLaw W b j) := by
    refine eLpNorm_mono (measurable_chainD0 j).aestronglyMeasurable fun ω => ?_
    have h1 : 0 ≤ chainD1 b E s D j ω := norm_nonneg _
    have h2 : 0 ≤ chainD0 b E D j ω := norm_nonneg _
    rw [Real.norm_of_nonneg h2, Real.norm_of_nonneg (by unfold chainPhi; positivity)]
    unfold chainPhi; nlinarith
  have h1 : eLpNorm (chainD1 b E s D j) p (oneEndedLaw W b j) ≤
      ENNReal.ofReal (1 / lam) * eLpNorm (chainPhi b E s D lam j) p (oneEndedLaw W b j) := by
    rw [← abs_of_pos (by positivity : 0 < 1 / lam), ← eLpNorm_real_mul]
    refine eLpNorm_mono (aesm_chainD1 hD hz j) fun ω => ?_
    have h1 : 0 ≤ chainD1 b E s D j ω := norm_nonneg _
    have h2 : 0 ≤ chainD0 b E D j ω := norm_nonneg _
    rw [Real.norm_of_nonneg h1, Real.norm_of_nonneg (by unfold chainPhi; positivity)]
    unfold chainPhi
    rw [mul_add, ← mul_assoc, one_div_mul_cancel hlam.ne', one_mul]
    have : 0 ≤ 1 / lam * chainD0 b E D j ω := by positivity
    linarith
  calc _ ≤ eLpNorm (chainPhi b E s D lam j) p (oneEndedLaw W b j) +
        ENNReal.ofReal (1 / lam) * eLpNorm (chainPhi b E s D lam j) p (oneEndedLaw W b j) :=
        add_le_add h0 h1
    _ = _ := by
        rw [ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one, add_mul, one_mul]

end Assembly

end OpenInputsProof

end BlockBand.Endpoints.Clock
