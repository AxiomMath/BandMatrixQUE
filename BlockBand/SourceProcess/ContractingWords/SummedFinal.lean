module

public import BlockBand.SourceProcess.ContractingWords.SummedStepPath

/-!
# The summed step at one step: the error in `stepErr` form

`first_step_bound`, `second_step_bound`: the first and second increment formulas at one step of
the growth path, with all error terms collected into the form `stepErr`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory MvPolynomial
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal

variable {W nT nI : ℕ}

/-- `Σ_w C(∂_wΦ) sq(2N(∂_wΦ))`. -/
def kOne (Cf : TracePoly nT nI → ℝ) (Nf : TracePoly nT nI → ℕ) (sq : ℕ → ℝ)
    (Φ : TracePoly nT nI) : ℝ :=
  ∑ w ∈ Φ.vars, Cf (pderiv w Φ) * sq (2 * Nf (pderiv w Φ))

/-- `Σ_{(w,v)} C(∂_v∂_wΦ) sq(2N(∂_v∂_wΦ))`. -/
def kTwo (Cf : TracePoly nT nI → ℝ) (Nf : TracePoly nT nI → ℕ) (sq : ℕ → ℝ)
    (Φ : TracePoly nT nI) : ℝ :=
  ∑ p ∈ Φ.vars ×ˢ Φ.vars, Cf (pderiv p.2 (pderiv p.1 Φ)) * sq (2 * Nf (pderiv p.2 (pderiv p.1 Φ)))

/-- `C(Φ)|S|²·|S| sq(2N(Φ))`. -/
def kThree (Cf : TracePoly nT nI → ℝ) (Nf : TracePoly nT nI → ℕ) (sq : ℕ → ℝ)
    (Φ : TracePoly nT nI) : ℝ :=
  Cf Φ * (Φ.vars.card : ℝ) ^ 2 * (Φ.vars.card * sq (2 * Nf Φ))

/-- `Σ_{(w,v)} C(∂_wΦ)C(∂_vΦ) sq(2(N(∂_wΦ) + N(∂_vΦ)))`. -/
def kFour (Cf : TracePoly nT nI → ℝ) (Nf : TracePoly nT nI → ℕ) (sq : ℕ → ℝ)
    (Φ : TracePoly nT nI) : ℝ :=
  ∑ p ∈ Φ.vars ×ˢ Φ.vars, Cf (pderiv p.1 Φ) * Cf (pderiv p.2 Φ) *
    sq (2 * (Nf (pderiv p.1 Φ) + Nf (pderiv p.2 Φ)))

/-- `3C(Φ)²(1+|S|)³|S|²·|S| sq(2(2N(Φ)+3))`. -/
def kFive (Cf : TracePoly nT nI → ℝ) (Nf : TracePoly nT nI → ℕ) (sq : ℕ → ℝ)
    (Φ : TracePoly nT nI) : ℝ :=
  3 * Cf Φ ^ 2 * (1 + Φ.vars.card) ^ 3 * (Φ.vars.card : ℝ) ^ 2 *
    (Φ.vars.card * sq (2 * (2 * Nf Φ + 3)))

theorem real_comb3 {K1 K2 K3 e1 e2 c s0 s3 : ℝ} (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) (hK3 : 0 ≤ K3)
    (h1 : e1 ≤ s0) (h2 : e2 ≤ s0) (h3 : c ≤ s3) :
    K1 * e1 + K2 * e2 + K3 * c ≤ (K1 + K2) * s0 + K3 * s3 := by
  have := mul_le_mul_of_nonneg_left h1 hK1
  have := mul_le_mul_of_nonneg_left h2 hK2
  have := mul_le_mul_of_nonneg_left h3 hK3
  nlinarith

theorem ennreal_comb3 {A1 A2 A3 B1 B2 : ℝ≥0∞} {K1 K2 e1 e2 R : ℝ} (hK1 : 0 ≤ K1)
    (hK2 : 0 ≤ K2) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2) (hR : 0 ≤ R)
    (h1 : A1 ≤ ENNReal.ofReal K1) (h2 : A2 ≤ ENNReal.ofReal K2) (h3 : A3 ≤ ENNReal.ofReal R)
    (hB1 : B1 = ENNReal.ofReal e1) (hB2 : B2 = ENNReal.ofReal e2) :
    A1 * B1 + A2 * B2 + A3 ≤ ENNReal.ofReal (K1 * e1 + K2 * e2 + R) := by
  rw [hB1, hB2, ENNReal.ofReal_add (by positivity) hR, ENNReal.ofReal_add (by positivity)
    (by positivity), ENNReal.ofReal_mul hK1, ENNReal.ofReal_mul hK2]
  gcongr

theorem ennreal_comb2 {A1 A3 B1 : ℝ≥0∞} {K1 e1 R : ℝ} (hK1 : 0 ≤ K1) (he1 : 0 ≤ e1)
    (hR : 0 ≤ R) (h1 : A1 ≤ ENNReal.ofReal K1) (h3 : A3 ≤ ENNReal.ofReal R)
    (hB1 : B1 = ENNReal.ofReal e1) :
    A1 * B1 + A3 ≤ ENNReal.ofReal (K1 * e1 + R) := by
  rw [hB1, ENNReal.ofReal_add (by positivity) hR, ENNReal.ofReal_mul hK1]
  gcongr

theorem real_comb2 {K1 K3 e1 c s0 s3 : ℝ} (hK1 : 0 ≤ K1) (hK3 : 0 ≤ K3) (h1 : e1 ≤ s0)
    (h3 : c ≤ s3) : K1 * e1 + K3 * c ≤ K1 * s0 + K3 * s3 := by
  have := mul_le_mul_of_nonneg_left h1 hK1
  have := mul_le_mul_of_nonneg_left h3 hK3
  linarith

/-- **The first increment formula at one step, in `stepErr` form.** -/
theorem first_step_bound (b E : ℝ) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (K ε : ℝ) (j : ℕ)
    (Φ : TracePoly nT nI) {Cf : TracePoly nT nI → ℝ} {Nf : TracePoly nT nI → ℕ}
    (hCf : ∀ Ψ, 0 ≤ Cf Ψ) (hTf : ∀ Ψ, TayBound Φ.vars Ψ (Cf Ψ) (Nf Ψ)) {Nb : ℕ}
    (hmom : ∀ n ≤ Nb, ∫⁻ ω, ENNReal.ofReal (domM b E k q j Φ.vars ω) ^ n
      ∂growthPathLaw W b ≠ ⊤)
    (hN1 : ∀ w ∈ Φ.vars, 2 * Nf (pderiv w Φ) + 2 ≤ Nb)
    (hN2 : ∀ w ∈ Φ.vars, ∀ v ∈ Φ.vars, 2 * Nf (pderiv v (pderiv w Φ)) + 2 ≤ Nb)
    (hN3 : 2 * Nf Φ + 3 ≤ Nb) {sq : ℕ → ℝ} (hsq : ∀ n, 0 ≤ sq n)
    (hT : ∀ n, 2 * n ≤ Nb → momT (growthPathLaw W b) (domM b E k q j Φ.vars) n ≤
      ENNReal.ofReal (sq (2 * n)))
    {C1 ρ1 C2 ρ2 C3 Cm ρ : ℝ} (hW1 : 1 ≤ W) (hC1 : 0 ≤ C1) (hρ1 : 0 ≤ ρ1) (hC2 : 0 ≤ C2)
    (hρ2 : 0 ≤ ρ2) (hC3 : 0 ≤ C3) (hm1 : C1 ≤ Cm) (hm2 : C2 ≤ Cm) (hr1 : ρ1 ≤ ρ) (hr2 : ρ2 ≤ ρ)
    (h1 : ∀ w ∈ Φ.vars, eLpNorm ((alive b E k q K ε W j).indicator fun ω =>
      (growthPathLaw W b)[(alive b E k q K ε W j).indicator (wordInc b E k q W j w) |
        growthSigma W j] ω -
      (W : ℂ)⁻¹ * polyValue b E k q W j ω (wordDrift (transportD0 b E) w +
        MvPolynomial.C (wordInjection b q (stepTime W j) w))) 2 (growthPathLaw W b) ≤
        ENNReal.ofReal (stepErr C1 ρ1 ε W k j))
    (h2 : ∀ p ∈ Φ.vars ×ˢ Φ.vars, eLpNorm ((alive b E k q K ε W j).indicator fun ω =>
      (growthPathLaw W b)[(alive b E k q K ε W j).indicator
        (fun ω => wordInc b E k q W j p.1 ω * wordInc b E k q W j p.2 ω) | growthSigma W j] ω -
      (W : ℂ)⁻¹ * polyValue b E k q W j ω (wordCov (transportD0 b E) p.1 p.2))
        2 (growthPathLaw W b) ≤ ENNReal.ofReal (stepErr C2 ρ2 ε W k j))
    (h3 : ∀ w ∈ Φ.vars, eLpNorm ((alive b E k q K ε W j).indicator (wordInc b E k q W j w)) 6
      (growthPathLaw W b) ≤ ENNReal.ofReal (C3 / Real.sqrt W)) :
    ∫⁻ ω, ‖(alive b E k q K ε W j).indicator (fun ω =>
        (growthPathLaw W b)[(alive b E k q K ε W j).indicator (fun ω =>
          polyValue b E k q W (j + 1) ω Φ - polyValue b E k q W j ω Φ) | growthSigma W j] ω -
        (W : ℂ)⁻¹ * polyValue b E k q W j ω (wordGenerator b E q (stepTime W j) Φ)) ω‖ₑ
        ∂growthPathLaw W b ≤ ENNReal.ofReal (stepErr ((kOne Cf Nf sq Φ + kTwo Cf Nf sq Φ) * Cm +
          kThree Cf Nf sq Φ * C3 ^ 3) ρ ε W k j) := by
  refine (first_path b E k q K ε j Φ hCf hTf hmom (fun w hw => by have := hN1 w hw; omega)
    (fun w hw v hv => by have := hN2 w hw v hv; omega) (by omega) h1 h2 h3).trans ?_
  have hK1 : 0 ≤ kOne Cf Nf sq Φ := Finset.sum_nonneg fun w _ => mul_nonneg (hCf _) (hsq _)
  have hK2 : 0 ≤ kTwo Cf Nf sq Φ := Finset.sum_nonneg fun p _ => mul_nonneg (hCf _) (hsq _)
  have hK3 : 0 ≤ kThree Cf Nf sq Φ := by
    unfold kThree; have := hCf Φ; have := hsq (2 * Nf Φ); positivity
  have t1 := sum_ofReal_mul_le Φ.vars (fun w => Cf (pderiv w Φ))
    (fun w => sq (2 * Nf (pderiv w Φ))) _ (fun _ => hCf _) (fun _ => hsq _)
    fun w hw => hT _ (by have := hN1 w hw; omega)
  have t2 := sum_ofReal_mul_le (Φ.vars ×ˢ Φ.vars) (fun p => Cf (pderiv p.2 (pderiv p.1 Φ)))
    (fun p => sq (2 * Nf (pderiv p.2 (pderiv p.1 Φ)))) _ (fun _ => hCf _) (fun _ => hsq _)
    fun p hp => hT _ (by
      have := hN2 p.1 (Finset.mem_product.mp hp).1 p.2 (Finset.mem_product.mp hp).2; omega)
  have t3 := rem_term_le (c := Cf Φ * (Φ.vars.card : ℝ) ^ 2) (n := Φ.vars.card) (W := W)
    (mul_nonneg (hCf Φ) (by positivity))
    (hsq (2 * Nf Φ)) hC3 (hT (Nf Φ) (by omega))
  have hs1 := stepErr_nonneg (ε := ε) (W := W) (k := k) (j := j) hC1 hρ1
  have hs2 := stepErr_nonneg (ε := ε) (W := W) (k := k) (j := j) hC2 hρ2
  refine (ennreal_comb3 hK1 hK2 hs1 hs2 (by have := hCf Φ; have := hsq (2 * Nf Φ); positivity)
    t1 t2 t3 rfl rfl).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have e1 : stepErr C1 ρ1 ε W k j ≤ stepErr Cm ρ ε W k j := stepErr_mono hm1 hC1 hρ1 hr1
  have e2 : stepErr C2 ρ2 ε W k j ≤ stepErr Cm ρ ε W k j := stepErr_mono hm2 hC2 hρ2 hr2
  have e3 : (C3 / Real.sqrt W) ^ 3 ≤ stepErr (C3 ^ 3) ρ ε W k j :=
    cube_le_stepErr hW1 hC3 (hρ1.trans hr1)
  rw [← stepErr_add, ← stepErr_smul, ← stepErr_smul]
  exact real_comb3 hK1 hK2 hK3 e1 e2 e3

/-- **The second increment formula at one step, in `stepErr` form.** -/
theorem second_step_bound (b E : ℝ) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (K ε : ℝ) (j : ℕ)
    (Φ : TracePoly nT nI) {Cf : TracePoly nT nI → ℝ} {Nf : TracePoly nT nI → ℕ}
    (hCf : ∀ Ψ, 0 ≤ Cf Ψ) (hTf : ∀ Ψ, TayBound Φ.vars Ψ (Cf Ψ) (Nf Ψ)) {Nb : ℕ}
    (hmom : ∀ n ≤ Nb, ∫⁻ ω, ENNReal.ofReal (domM b E k q j Φ.vars ω) ^ n
      ∂growthPathLaw W b ≠ ⊤)
    (hN1 : ∀ w ∈ Φ.vars, ∀ v ∈ Φ.vars, 2 * (Nf (pderiv w Φ) + Nf (pderiv v Φ)) + 2 ≤ Nb)
    (hN3 : 2 * (2 * Nf Φ + 3) + 3 ≤ Nb) {sq : ℕ → ℝ} (hsq : ∀ n, 0 ≤ sq n)
    (hT : ∀ n, 2 * n ≤ Nb → momT (growthPathLaw W b) (domM b E k q j Φ.vars) n ≤
      ENNReal.ofReal (sq (2 * n)))
    {C2 ρ2 C3 Cm ρ : ℝ} (hW1 : 1 ≤ W) (hC2 : 0 ≤ C2) (hρ2 : 0 ≤ ρ2) (hC3 : 0 ≤ C3)
    (hm2 : C2 ≤ Cm) (hr2 : ρ2 ≤ ρ)
    (h2 : ∀ p ∈ Φ.vars ×ˢ Φ.vars, eLpNorm ((alive b E k q K ε W j).indicator fun ω =>
      (growthPathLaw W b)[(alive b E k q K ε W j).indicator
        (fun ω => wordInc b E k q W j p.1 ω * wordInc b E k q W j p.2 ω) | growthSigma W j] ω -
      (W : ℂ)⁻¹ * polyValue b E k q W j ω (wordCov (transportD0 b E) p.1 p.2))
        2 (growthPathLaw W b) ≤ ENNReal.ofReal (stepErr C2 ρ2 ε W k j))
    (h3 : ∀ w ∈ Φ.vars, eLpNorm ((alive b E k q K ε W j).indicator (wordInc b E k q W j w)) 6
      (growthPathLaw W b) ≤ ENNReal.ofReal (C3 / Real.sqrt W)) :
    ∫⁻ ω, ‖(alive b E k q K ε W j).indicator (fun ω =>
        (growthPathLaw W b)[(alive b E k q K ε W j).indicator (fun ω =>
          (polyValue b E k q W (j + 1) ω Φ - polyValue b E k q W j ω Φ) ^ 2) |
            growthSigma W j] ω -
        (W : ℂ)⁻¹ * polyValue b E k q W j ω (wordCarre b E Φ)) ω‖ₑ ∂growthPathLaw W b ≤
      ENNReal.ofReal (stepErr (kFour Cf Nf sq Φ * Cm + kFive Cf Nf sq Φ * C3 ^ 3) ρ ε W k j) := by
  refine (second_path b E k q K ε j Φ hCf hTf hmom (fun w hw v hv => by
    have := hN1 w hw v hv; omega) (by omega) h2 h3).trans ?_
  have hK4 : 0 ≤ kFour Cf Nf sq Φ := Finset.sum_nonneg fun p _ =>
    mul_nonneg (mul_nonneg (hCf _) (hCf _)) (hsq _)
  have hK5 : 0 ≤ kFive Cf Nf sq Φ := by
    unfold kFive; have := hsq (2 * (2 * Nf Φ + 3)); positivity
  have t4 := sum_ofReal_mul_le (Φ.vars ×ˢ Φ.vars)
    (fun p => Cf (pderiv p.1 Φ) * Cf (pderiv p.2 Φ))
    (fun p => sq (2 * (Nf (pderiv p.1 Φ) + Nf (pderiv p.2 Φ)))) _
    (fun _ => mul_nonneg (hCf _) (hCf _)) (fun _ => hsq _) fun p hp => hT _ (by
      have := hN1 p.1 (Finset.mem_product.mp hp).1 p.2 (Finset.mem_product.mp hp).2; omega)
  have t5 := rem_term_le
    (c := 3 * Cf Φ ^ 2 * (1 + Φ.vars.card) ^ 3 * (Φ.vars.card : ℝ) ^ 2) (n := Φ.vars.card)
    (W := W) (by have := hCf Φ; positivity)
    (hsq (2 * (2 * Nf Φ + 3))) hC3 (hT (2 * Nf Φ + 3) (by omega))
  have hs2 := stepErr_nonneg (ε := ε) (W := W) (k := k) (j := j) hC2 hρ2
  refine (ennreal_comb2 hK4 hs2
    (by have := hCf Φ; have := hsq (2 * (2 * Nf Φ + 3)); positivity) t4 t5 rfl).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have e2 : stepErr C2 ρ2 ε W k j ≤ stepErr Cm ρ ε W k j := stepErr_mono hm2 hC2 hρ2 hr2
  have e3 : (C3 / Real.sqrt W) ^ 3 ≤ stepErr (C3 ^ 3) ρ ε W k j :=
    cube_le_stepErr hW1 hC3 (hρ2.trans hr2)
  rw [← stepErr_add, ← stepErr_smul, ← stepErr_smul]
  exact real_comb2 hK4 hK5 e2 e3

end BlockBand.SourceProcess.ContractingWords
