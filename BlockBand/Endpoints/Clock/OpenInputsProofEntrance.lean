module

public import BlockBand.Endpoints.Clock.OpenInputsProofJet

/-!
# The open-inputs lemma: the entrance and the asymptotic bookkeeping

We prove the entrance bound of the open-inputs lemma and the elementary asymptotic estimates used
in its assembly.

* `entrance_bound`: from the zero-entrance lemma (`ZeroEntranceStatement`): a fixed
  `J` whose zero-boundary mean is within `r/4` of `a` (seed `C e^{-c_* J}`), the sensitivity
  `C_J ε ≤ r/4` to the initial matrix (`‖D‖ ≤ ε`), the mean error `C_J/W ≤ r/4`, and the
  concentration `C_J √P/W` at order `P ≤ a_J W` with Markov give
  `P(δ₀(X_J) > r) ≤ (K √P / W)^P`, uniformly in Hermitian `D` with `‖D‖ ≤ ε`.
* `tail_small`: `(BW)^m L^W (1 + cW) (κ/√W)^{aW} ≤ 1` for large `W` (the exit probability at
  order `P = aW` is `e^{-c W log W}` small, and beats the crude clock growth
  `C^{TW}`, and every power of `W`).
* `geom_small`: `W θ^n ≤ 1` for `n ≥ ⌈(log W)²⌉ - J` and large `W` ("`q^{(log W)²}` is
  smaller than every power of `W`").
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

/-- **The entrance bound.** -/
theorem entrance_bound (hZ : ZeroEntranceStatement) {b E : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2)
    (hE0 : -2 < E) (hE1 : E < 2) {r : ℝ} (hr : 0 < r) :
    ∃ (J : ℕ) (ε a K : ℝ) (W₀ : ℕ), 0 < ε ∧ 0 < a ∧ 0 ≤ K ∧
      ∀ W : ℕ, W₀ ≤ W → ∀ D : Matrix (Fin W) (Fin W) ℂ, D.IsHermitian → ‖D‖ ≤ ε →
        ∀ P : ℝ, 2 ≤ P → P ≤ a * W →
          oneEndedLaw W b J {ω | r < chainD0 b E D J ω} ≤
            ENNReal.ofReal ((K * Real.sqrt P / W) ^ P) := by
  obtain ⟨μ, -, hseed, hfix⟩ := hZ
  obtain ⟨hκ, hpar⟩ := kappaOf_facts hb0 hb1 hE0 hE1
  obtain ⟨Cs, cs, hCs, hcs, hseed'⟩ := hseed (kappaOf b E) hκ
  -- a fixed `J` with a small seed
  have hlim : Tendsto (fun J : ℕ => Cs * Real.exp (-cs * J)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun J : ℕ => -cs * (J : ℝ)) atTop atBot :=
      tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (neg_lt_zero.mpr hcs)
    have h2 := (Real.tendsto_exp_atBot.comp h1).const_mul Cs
    simpa [Function.comp_def] using h2
  obtain ⟨J, hJ⟩ := (hlim.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < r / 4))).exists
  obtain ⟨a, C, W₀, ha, hC, hfixJ⟩ := hfix (kappaOf b E) hκ J
  refine ⟨J, r / (4 * C), a, 4 * C / r, max W₀ (⌈4 * C / r⌉₊ + 1), by positivity, ha,
    by positivity, ?_⟩
  intro W hW D hD hDε P hP2 hPa
  have hW0 : W₀ ≤ W := (le_max_left _ _).trans hW
  have hW1 : ⌈4 * C / r⌉₊ + 1 ≤ W := (le_max_right _ _).trans hW
  have hWr : (0 : ℝ) < W := by
    have : (1 : ℝ) ≤ W := by exact_mod_cast (Nat.succ_le_of_lt (Nat.lt_of_lt_of_le
      (Nat.succ_pos _) hW1))
    linarith
  have hCW : C / W ≤ r / 4 := by
    have h1 : 4 * C / r < W := by
      have := Nat.le_ceil (4 * C / r)
      have h2 : ((⌈4 * C / r⌉₊ + 1 : ℕ) : ℝ) ≤ W := by exact_mod_cast hW1
      push_cast at h2; linarith
    rw [div_lt_iff₀ hr] at h1
    rw [div_le_iff₀ hWr]; linarith
  obtain ⟨hmean, -, hconc, hpert⟩ := hfixJ W hW0 b E hpar
  obtain ⟨h1, -⟩ := hconc D hD P hP2 hPa
  obtain ⟨h2, -⟩ := hpert (r / (4 * C)) D hD hDε
  have h3 := hseed' b E J hpar
  have hCε : C * (r / (4 * C)) = r / 4 := by field_simp
  set Z := ∫ ω', zeTrace E D J (boundaryZ b E) ω' ∂oneEndedLaw W b J with hZdef
  have hsub : {ω | r < chainD0 b E D J ω} ⊆
      {ω | r / 4 ≤ ‖zeTrace E D J (boundaryZ b E) ω - Z‖} := by
    intro ω hω
    have hω' : r < chainD0 b E D J ω := hω
    show r / 4 ≤ ‖zeTrace E D J (boundaryZ b E) ω - Z‖
    have e : chainD0 b E D J ω = ‖zeTrace E D J (boundaryZ b E) ω - matchedA E‖ := rfl
    rw [e] at hω'
    set h := zeTrace E D J (boundaryZ b E) ω
    set Z0 := ∫ ω', zeTrace E (0 : Matrix (Fin W) (Fin W) ℂ) J (boundaryZ b E) ω'
      ∂oneEndedLaw W b J
    set G := stieltjesG (μ b E J) (boundaryZ b E)
    have t1 := norm_sub_le_norm_sub_add_norm_sub h Z (matchedA E)
    have t2 := norm_sub_le_norm_sub_add_norm_sub Z Z0 (matchedA E)
    have t3 := norm_sub_le_norm_sub_add_norm_sub Z0 G (matchedA E)
    have hs : Cs * Real.exp (-cs * J) < r / 4 := hJ
    linarith
  refine (measure_mono hsub).trans ?_
  have hB0 : 0 ≤ C * Real.sqrt P / W := by positivity
  have hm : AEStronglyMeasurable (fun ω => zeTrace E D J (boundaryZ b E) ω - Z)
      (oneEndedLaw W b J) :=
    ((measurable_zeTrace E D J (boundaryZ b E)).sub measurable_const).aestronglyMeasurable
  have hN : eLpNorm (fun ω => ‖zeTrace E D J (boundaryZ b E) ω - Z‖) (ENNReal.ofReal P)
      (oneEndedLaw W b J) ≤ ENNReal.ofReal (C * Real.sqrt P / W) := by
    rw [eLpNorm_norm _ hm]; exact h1
  refine (measure_ge_le_of_eLpNorm (by positivity) (by linarith) hB0 hN).trans
    (le_of_eq (congrArg ENNReal.ofReal ?_))
  congr 1
  field_simp

/-!
## Asymptotics
-/

/-- The exceptional sets are negligible: `(BW)^m L^W (1 + cW) (κ/√W)^{aW} ≤ 1` for large `W`. -/
theorem tail_small {B m L c κ a : ℝ} (hB : 0 < B) (hm : 0 ≤ m) (hL : 1 ≤ L) (hc : 0 ≤ c)
    (hκ : 0 < κ) (ha : 0 < a) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      (B * W) ^ m * L ^ W * (1 + c * W) * (κ / Real.sqrt W) ^ (a * W) ≤ 1 := by
  set Λ := 2 / a * (m * B + Real.log L + c + a * Real.log κ) + 1 with hΛ
  refine ⟨⌈Real.exp Λ⌉₊ + 1, fun W hW => ?_⟩
  have hW1 : Real.exp Λ < W := by
    have h1 := Nat.le_ceil (Real.exp Λ)
    have h2 : ((⌈Real.exp Λ⌉₊ + 1 : ℕ) : ℝ) ≤ W := by exact_mod_cast hW
    push_cast at h2; linarith
  have hWpos : (0 : ℝ) < W := (Real.exp_pos _).trans hW1
  have hlogW : Λ < Real.log W := by
    rw [← Real.exp_lt_exp, Real.exp_log hWpos]; exact hW1
  have hsq : 0 < Real.sqrt W := Real.sqrt_pos.mpr hWpos
  have hL0 : 0 < L := by linarith
  have hpos1 : 0 < (B * W) ^ m := Real.rpow_pos_of_pos (by positivity) _
  have hpos2 : 0 < L ^ W := pow_pos hL0 _
  have hpos3 : 0 < 1 + c * W := by positivity
  have hpos4 : 0 < (κ / Real.sqrt W) ^ (a * W) := Real.rpow_pos_of_pos (by positivity) _
  rw [← Real.exp_log (by positivity : (0 : ℝ) < (B * W) ^ m * L ^ W * (1 + c * W) *
    (κ / Real.sqrt W) ^ (a * W)), Real.exp_le_one_iff]
  rw [Real.log_mul (by positivity) hpos4.ne', Real.log_mul (by positivity) hpos3.ne',
    Real.log_mul hpos1.ne' hpos2.ne', Real.log_rpow (by positivity), Real.log_pow,
    Real.log_rpow (by positivity), Real.log_div hκ.ne' hsq.ne', Real.log_sqrt hWpos.le]
  have e1 : Real.log (B * W) ≤ B * W := (Real.log_le_sub_one_of_pos (by positivity)).trans
    (by linarith)
  have e2 : Real.log (1 + c * W) ≤ c * W := (Real.log_le_sub_one_of_pos hpos3).trans
    (by linarith)
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL
  -- `a W (log κ - log W / 2) ≤ -W (m B + log L + c)`
  have e3 : a * W * (Real.log κ - Real.log W / 2) ≤ -(W * (m * B + Real.log L + c)) := by
    have : a * (Real.log κ - Real.log W / 2) ≤ -(m * B + Real.log L + c) := by
      have h4 : 2 / a * (m * B + Real.log L + c + a * Real.log κ) < Real.log W := by
        linarith
      rw [div_mul_eq_mul_div, div_lt_iff₀ ha] at h4
      nlinarith
    nlinarith
  have e4 : m * Real.log (B * W) ≤ m * (B * W) := mul_le_mul_of_nonneg_left e1 hm
  have e5 : (W : ℝ) * Real.log L = W * Real.log L := rfl
  nlinarith

/-- `W θⁿ ≤ 1` once `n ≥ ⌈(log W)²⌉ - J` and `W` is large. -/
theorem geom_small {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (J : ℕ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → J + 1 ≤ openEntranceTime W ∧
      ∀ n : ℕ, openEntranceTime W ≤ J + n → (W : ℝ) * θ ^ n ≤ 1 := by
  set ℓ := Real.log (1 / θ) with hℓ
  have hℓ0 : 0 < ℓ := Real.log_pos (by rw [lt_div_iff₀ hθ0]; linarith)
  set Λ := max 1 ((J : ℝ) + 1 + 1 / ℓ) with hΛ
  refine ⟨⌈Real.exp Λ⌉₊ + 1, fun W hW => ?_⟩
  have hW1 : Real.exp Λ < W := by
    have h1 := Nat.le_ceil (Real.exp Λ)
    have h2 : ((⌈Real.exp Λ⌉₊ + 1 : ℕ) : ℝ) ≤ W := by exact_mod_cast hW
    push_cast at h2; linarith
  have hWpos : (0 : ℝ) < W := (Real.exp_pos _).trans hW1
  have hlogW : Λ < Real.log W := by
    rw [← Real.exp_lt_exp, Real.exp_log hWpos]; exact hW1
  have hl1 : 1 ≤ Real.log W := (le_max_left _ _).trans hlogW.le
  have hl2 : (J : ℝ) + 1 + 1 / ℓ ≤ Real.log W := (le_max_right _ _).trans hlogW.le
  have hsq : ((J : ℝ) + 1 + 1 / ℓ) * Real.log W ≤ Real.log W ^ 2 := by
    rw [sq]; exact mul_le_mul_of_nonneg_right hl2 (by linarith)
  have hℓ' : 0 ≤ 1 / ℓ := by positivity
  have hent : Real.log W ^ 2 ≤ openEntranceTime W := by
    unfold openEntranceTime; exact Nat.le_ceil _
  refine ⟨?_, fun n hn => ?_⟩
  · have : ((J : ℝ) + 1) ≤ openEntranceTime W := by nlinarith
    exact_mod_cast this
  · have hn' : (openEntranceTime W : ℝ) ≤ J + n := by exact_mod_cast hn
    have hnl : Real.log W / ℓ ≤ n := by
      have : Real.log W * (1 / ℓ) ≤ n := by nlinarith
      rwa [mul_one_div] at this
    rw [← Real.exp_log (by positivity : (0 : ℝ) < W * θ ^ n), Real.exp_le_one_iff]
    rw [Real.log_mul hWpos.ne' (pow_pos hθ0 n).ne', Real.log_pow]
    have hlθ : Real.log θ = -ℓ := by rw [hℓ, Real.log_div one_ne_zero hθ0.ne', Real.log_one]; ring
    rw [hlθ]
    rw [div_le_iff₀ hℓ0] at hnl
    nlinarith

end OpenInputsProof

end BlockBand.Endpoints.Clock
