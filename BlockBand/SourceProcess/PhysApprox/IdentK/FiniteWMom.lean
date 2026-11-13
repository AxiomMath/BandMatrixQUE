module

public import BlockBand.SourceProcess.PhysApprox.IdentK.FiniteWSum

/-!
# Second and fourth moments of a step; birth steps

Closed law `μ = closedLaw b W np`, Borel alive set `A'_j`, `n_s ≤ j`. `Q_W(R)` is bounded through
the brackets (`C_R` the bracket bound on Gram states of trace at most `R`), `L_W(R)` is the
Lindeberg sum, and births are handled by the Lipschitz bound and the birth errors.

* `sig`: the conjugate partner of a basic increment (`β_{σ i} = conj β_i` without a birth).
* **`lint_sq_le`**: `∫⁻ 1_{A'_j} ‖β_i‖² ≤ C_R / W + pinE2 j i (σ i)` (no birth).
* **`lint_four_le`**: `∫⁻ 1_{A'_j} ‖β‖₁⁴ ≤ |BI|³ Σ_i ∫⁻ 1_{A_j} ‖dX_{c(i)}‖⁴` (no birth).
* **`lint_birth_le`**: `∫⁻ 1_{A'_j} |dStep_j| ≤ 3C Σ_i genBirthStep j (c i) + C_Λ / W` (any step).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram.IdentK.FW

open MeasureTheory Finset Filter Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.CapLimit
open scoped ComplexConjugate ENNReal Topology

variable {W np K : ℕ}

/-- The conjugate partner of a basic increment. -/
def sig : BI K np → BI K np
  | Sum.inl e => Sum.inl (eStar e)
  | Sum.inr (Sum.inl a) => Sum.inr (Sum.inr a)
  | Sum.inr (Sum.inr a) => Sum.inr (Sum.inl a)

theorem norm_inv_natCast_le (W : ℕ) : ‖(W : ℂ)⁻¹‖ ≤ 1 / W := by
  rw [norm_inv, Complex.norm_natCast, one_div]

section Mom

variable {b E s h : ℝ} {τ m : Fin np → ℝ} {R : ℝ} {W : ℕ}
  {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}

theorem betaS_mul_sig {j : ℕ} (hj : ¬ IsBirthStep τ W j) (y : ProbedPath W np × ℝ)
    (i : BI K np) :
    betaS b E s h τ m W Vs j y i * betaS b E s h τ m W Vs j y (sig i) =
      ((‖betaS b E s h τ m W Vs j y i‖ ^ 2 : ℝ) : ℂ) := by
  rw [ofReal_norm_sq_eq]
  congr 1
  rcases i with e | a | a
  · simp only [sig, betaS_inl b E s h τ m W Vs hj, conj_b3dX_inl]
  · simp only [sig, betaS_K b E s h τ m W Vs hj, betaS_Kc b E s h τ m W Vs hj]
  · simp only [sig, betaS_K b E s h τ m W Vs hj, betaS_Kc b E s h τ m W Vs hj,
      Complex.conj_conj]

theorem norm_betaS_eq {j : ℕ} (hj : ¬ IsBirthStep τ W j) (y : ProbedPath W np × ℝ)
    (i : BI K np) :
    ‖betaS b E s h τ m W Vs j y i‖ = ‖b3dX b E s h τ m W j Vs (cOf i) y‖ := by
  rcases i with e | a | a
  · simp only [betaS_inl b E s h τ m W Vs hj, cOf]
  · simp only [betaS_K b E s h τ m W Vs hj, cOf]
  · simp only [betaS_Kc b E s h τ m W Vs hj, cOf, Complex.norm_conj]

theorem norm_betaS_birth (j : ℕ) (y : ProbedPath W np × ℝ) (i : BI K np) :
    ‖betaS b E s h τ m W Vs j y i‖ = ‖b3dX b E s h τ m W j Vs (cOf i) y -
      cEntry (cOf i) (b3BirthAt b τ m W j) (b3KBirthAt E τ m W j)‖ := by
  rcases i with e | a | a
  · simp only [betaS_inl_birth, cOf]
  · simp only [betaS_K_birth, cOf]
  · simp only [betaS_Kc_birth, cOf, Complex.norm_conj]

/-- **Second moments from the brackets** (no birth). -/
theorem lint_sq_le (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2)
    (hV : Measurable[growthSigma W (closeLen s W)] Vs) {j : ℕ} (hjs : closeLen s W ≤ j)
    (hj : ¬ IsBirthStep τ W j)
    (hL2 : ∀ c, MemLp ((b3Alive b E s h τ m R W j Vs).indicator (b3dX b E s h τ m W j Vs c)) 2
      (closedLaw b W np))
    {CR : ℝ} (hCR0 : 0 ≤ CR) (hCR : ∀ H : GSt K np, (∀ e, ‖gramEntry e H‖ ≤ R) →
      (∀ i, ‖dvec b E H i‖ ≤ CR) ∧ ∀ i i', ‖Bmat b E H i i'‖ ≤ CR) (i : BI K np) :
    ∫⁻ y, (b3AliveM b E s h τ m R W j Vs).indicator
        (fun y => ENNReal.ofReal (‖betaS b E s h τ m W Vs j y i‖ ^ 2)) y ∂closedLaw b W np ≤
      ENNReal.ofReal (CR / W) + pinE2 b E s h τ m R W Vs j i (sig i) := by
  set μ := closedLaw b W np
  set A' := b3AliveM b E s h τ m R W j Vs
  have hV' : Measurable Vs := hV.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  have hm := gen_sigma_le W j np
  have hA : MeasurableSet[b3Sigma W j np] A' :=
    Modul.measurableSet_b3AliveM_past s h τ m R hjs le_rfl hV
  have hAm : MeasurableSet A' := hm _ hA
  have hAA := b3Alive_ae_eq hb hE1 hE2 s h τ m R W j Vs (np := np)
  have hβ2 : ∀ i, MemLp (A'.indicator fun y => betaS b E s h τ m W Vs j y i) 2 μ := by
    intro i
    refine ((hL2 (cOf i)).ae_eq (indicator_ae_eq_of_ae_eq_set hAA)).congr_norm
      ((measurable_betaS hV' i).indicator hAm).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ A' <;> simp [A', hy, norm_betaS_eq hj]
  set X : ProbedPath W np × ℝ → ℂ := fun y =>
    betaS b E s h τ m W Vs j y i * betaS b E s h τ m W Vs j y (sig i)
  have hX : Integrable (A'.indicator X) μ := by
    rw [indicator_mul']; exact (hβ2 i).integrable_mul (hβ2 (sig i))
  have hXr : A'.indicator X = fun y =>
      ((A'.indicator (fun y => ‖betaS b E s h τ m W Vs j y i‖ ^ 2) y : ℝ) : ℂ) := by
    funext y; by_cases hy : y ∈ A' <;> simp [X, hy, betaS_mul_sig hj]
  have hreal : Integrable (A'.indicator (fun y => ‖betaS b E s h τ m W Vs j y i‖ ^ 2)) μ := by
    have := hX.norm
    refine this.congr (Eventually.of_forall fun y => ?_)
    simp only [hXr, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (Set.indicator_nonneg (fun _ _ => sq_nonneg _) _)
  have e1 : ∫⁻ y, A'.indicator (fun y => ENNReal.ofReal (‖betaS b E s h τ m W Vs j y i‖ ^ 2)) y ∂μ
      = ‖∫ y, A'.indicator X y ∂μ‖ₑ := by
    rw [hXr, integral_complex_ofReal, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg fun y => Set.indicator_nonneg (fun _ _ => sq_nonneg _) _),
      ofReal_integral_eq_lintegral_ofReal hreal
        (Eventually.of_forall fun y => Set.indicator_nonneg (fun _ _ => sq_nonneg _) _)]
    refine lintegral_congr fun y => ?_
    by_cases hy : y ∈ A' <;> simp [hy]
  set P : ProbedPath W np × ℝ → ℂ := fun y =>
    (W : ℂ)⁻¹ * Bmat b E (b3ClosedGramAt b E s h τ m W j Vs y) i (sig i)
  have hPb : ∀ y, ‖A'.indicator P y‖ ≤ CR / W := fun y => by
    by_cases hy : y ∈ A'
    · rw [Set.indicator_of_mem hy, norm_mul]
      have := (hCR _ (gram_bound_of_alive hjs hy)).2 i (sig i)
      calc ‖(W : ℂ)⁻¹‖ * _ ≤ (1 / W) * CR :=
            mul_le_mul (norm_inv_natCast_le W) this (norm_nonneg _) (by positivity)
        _ = CR / W := by ring
    · rw [Set.indicator_of_notMem hy, norm_zero]; positivity
  have hP : Integrable (A'.indicator P) μ :=
    Integrable.of_bound ((((measurable_comp_gram hV' (continuous_Bmat b E i (sig i))).const_mul
      _).indicator hAm).aestronglyMeasurable) _ (Eventually.of_forall hPb)
  have h1 := enorm_integral_sub_le_cond (μ := μ) hm hA hX hP stronglyMeasurable_const
    (g := fun _ => (1 : ℂ)) (Cg := 1) (fun _ => by simp)
  simp only [one_mul, ENNReal.ofReal_one] at h1
  have h2 : ‖∫ y, A'.indicator P y ∂μ‖ₑ ≤ ENNReal.ofReal (CR / W) := by
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    calc ∫⁻ y, ‖A'.indicator P y‖ₑ ∂μ ≤ ∫⁻ _, ENNReal.ofReal (CR / W) ∂μ :=
          lintegral_mono fun y => by rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hPb y)
      _ = ENNReal.ofReal (CR / W) := by simp
  have h3 : ∫⁻ y, ‖A'.indicator (fun y => μ[A'.indicator X | b3Sigma W j np] y - P y) y‖ₑ ∂μ =
      pinE2 b E s h τ m R W Vs j i (sig i) := e2S_eq s h τ m R W Vs hb hE1 hE2 hj i (sig i)
  rw [e1]
  calc ‖∫ y, A'.indicator X y ∂μ‖ₑ ≤ ‖∫ y, A'.indicator X y ∂μ - ∫ y, A'.indicator P y ∂μ‖ₑ +
        ‖∫ y, A'.indicator P y ∂μ‖ₑ := by
        have := enorm_add_le (∫ y, A'.indicator X y ∂μ - ∫ y, A'.indicator P y ∂μ)
          (∫ y, A'.indicator P y ∂μ)
        rwa [sub_add_cancel] at this
    _ ≤ pinE2 b E s h τ m R W Vs j i (sig i) + ENNReal.ofReal (CR / W) :=
        add_le_add (h1.trans_eq h3) h2
    _ = _ := add_comm _ _

theorem pow_four_sum_le {I : Type*} [Fintype I] (x : I → ℝ) (hx : ∀ i, 0 ≤ x i) :
    (∑ i, x i) ^ 4 ≤ (Fintype.card I : ℝ) ^ 3 * ∑ i, x i ^ 4 := by
  rcases Nat.eq_zero_or_pos (Fintype.card I) with h0 | h0
  · have : IsEmpty I := Fintype.card_eq_zero_iff.1 h0
    simp
  · have h := pow_sum_div_card_le_sum_pow (s := (univ : Finset I)) (fun i _ => hx i) 3
    have hc : (0 : ℝ) < (Fintype.card I : ℝ) ^ 3 := by positivity
    rw [card_univ, div_le_iff₀ hc] at h
    have h' : (∑ i, x i) ^ 4 ≤ (∑ i, x i ^ 4) * (Fintype.card I : ℝ) ^ 3 := by simpa using h
    linarith [mul_comm (∑ i, x i ^ 4) ((Fintype.card I : ℝ) ^ 3)]

/-- **Fourth moments from Lindeberg** (no birth). -/
theorem lint_four_le (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) (hV : Measurable Vs) {j : ℕ}
    (hj : ¬ IsBirthStep τ W j) :
    ∫⁻ y, (b3AliveM b E s h τ m R W j Vs).indicator
        (fun y => ENNReal.ofReal (nrm (betaS b E s h τ m W Vs j y) ^ 4)) y ∂closedLaw b W np ≤
      ENNReal.ofReal ((Fintype.card (BI K np) : ℝ) ^ 3) * ∑ i : BI K np,
        ∫⁻ y, (b3Alive b E s h τ m R W j Vs).indicator
          (fun y => ‖b3dX b E s h τ m W j Vs (cOf i) y‖ₑ ^ 4) y ∂closedLaw b W np := by
  set A' := b3AliveM b E s h τ m R W j Vs
  have hAA := b3Alive_ae_eq hb hE1 hE2 s h τ m R W j Vs (np := np)
  have hAm : MeasurableSet A' := measurableSet_b3AliveM b E s h τ m R W j hV
  have hf : ∀ i : BI K np, Measurable fun y => ‖b3dX b E s h τ m W j Vs (cOf i) y‖ₑ ^ 4 :=
    fun i => (genMem_measurable_b3dX b E s h τ m W j hV (cOf i)).enorm.pow_const 4
  have hpt : ∀ y, A'.indicator (fun y => ENNReal.ofReal (nrm (betaS b E s h τ m W Vs j y) ^ 4)) y
      ≤ ENNReal.ofReal ((Fintype.card (BI K np) : ℝ) ^ 3) * ∑ i : BI K np,
        A'.indicator (fun y => ‖b3dX b E s h τ m W j Vs (cOf i) y‖ₑ ^ 4) y := fun y => by
    by_cases hy : y ∈ A'
    · simp only [Set.indicator_of_mem hy]
      have h1 := pow_four_sum_le (fun i => ‖betaS b E s h τ m W Vs j y i‖) (fun _ => norm_nonneg _)
      refine (ENNReal.ofReal_le_ofReal h1).trans (le_of_eq ?_)
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg
        (fun _ _ => by positivity)]
      congr 1
      refine sum_congr rfl fun i _ => ?_
      rw [norm_betaS_eq hj, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    · simp [Set.indicator_of_notMem hy]
  calc _ ≤ ∫⁻ y, ENNReal.ofReal ((Fintype.card (BI K np) : ℝ) ^ 3) * ∑ i : BI K np,
        A'.indicator (fun y => ‖b3dX b E s h τ m W j Vs (cOf i) y‖ₑ ^ 4) y ∂closedLaw b W np :=
        lintegral_mono hpt
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_finsetSum _ fun i _ => (hf i).indicator hAm]
      congr 1
      exact sum_congr rfl fun i _ => lintegral_congr_ae (indicator_ae_eq_of_ae_eq_set hAA.symm)

/-- The Lipschitz bound of a step from the uniform Taylor bound. -/
theorem norm_fn_step_le {χ ξ : ℝ → ℝ} {κ : KTest K np} {D C : ℝ} (hC : TayB χ ξ κ D C)
    {z : ZK K np} {dY : GSt K np} {dK : KSt np} (hz : Adm D z) (hz' : Adm D (zstep z dY dK))
    (hd : DiagReal dY) :
    ‖κ.fn χ ξ (zstep z dY dK) - κ.fn χ ξ z‖ ≤ 3 * C * nrm (bvec dY dK) := by
  obtain ⟨hC0, hCb, hCr⟩ := hC
  set N := nrm (bvec dY dK)
  have hN0 : 0 ≤ N := nrm_nonneg _
  have hL := norm_lin_le (hCb z hz).2.1 (bvec dY dK)
  have hQ := norm_quad_le (hCb z hz).2.2 (bvec dY dK)
  have hr := hCr z dY dK hz hz' hd
  by_cases hN : N ≤ 1
  · have h1 : N ^ 2 ≤ N := by nlinarith
    have h2 : N ^ 3 ≤ N := by nlinarith
    calc _ = ‖(κ.fn χ ξ (zstep z dY dK) - κ.fn χ ξ z - lin (jF χ ξ κ z).l (bvec dY dK) -
          quad (jF χ ξ κ z).q (bvec dY dK)) + lin (jF χ ξ κ z).l (bvec dY dK) +
            quad (jF χ ξ κ z).q (bvec dY dK)‖ := by congr 1; ring
      _ ≤ C * N ^ 3 + C * N + C * N ^ 2 :=
          (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hr hL)) hQ)
      _ ≤ 3 * C * N := by nlinarith
  · push Not at hN
    calc _ ≤ ‖κ.fn χ ξ (zstep z dY dK)‖ + ‖κ.fn χ ξ z‖ := norm_sub_le _ _
      _ ≤ C + C := add_le_add (hCb _ hz').1 (hCb _ hz).1
      _ ≤ 3 * C * N := by nlinarith

/-- **A birth step** (and any step): the stopped step is controlled by the birth errors. -/
theorem lint_birth_le (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) (hV : Measurable Vs) {j : ℕ}
    (hjs : closeLen s W ≤ j) {χ ξ : ℝ → ℝ} {κ : KTest K np} {C CΛ : ℝ}
    (hC : TayB χ ξ κ (((Fintype.card (SrcCol K (Fin np)) : ℝ) + 1) * cJump b m) C)
    (hCΛ0 : 0 ≤ CΛ)
    (hCΛ : ∀ (J : GSt K np) (z : ZK K np), (∀ e, ‖gramEntry e J‖ ≤ cJump b m) →
      Adm (((Fintype.card (SrcCol K (Fin np)) : ℝ) + 1) * cJump b m) z →
      ‖κ.lam χ ξ b E (J, z)‖ ≤ CΛ) :
    ∫⁻ y, (b3AliveM b E s h τ m R W j Vs).indicator
        (fun y => ‖dStep b E s h τ m W Vs χ ξ κ j y‖ₑ) y ∂closedLaw b W np ≤
      ENNReal.ofReal (3 * C) * ∑ i : BI K np, genBirthStep b E s h τ m R W j Vs (cOf i) +
        ENNReal.ofReal (CΛ / W) := by
  set A' := b3AliveM b E s h τ m R W j Vs
  have hAA := b3Alive_ae_eq hb hE1 hE2 s h τ m R W j Vs (np := np)
  have hAm : MeasurableSet A' := measurableSet_b3AliveM b E s h τ m R W j hV
  have hC0 : 0 ≤ C := hC.1
  have hf : ∀ i : BI K np, Measurable fun y => ‖betaS b E s h τ m W Vs j y i‖ₑ :=
    fun i => (measurable_betaS hV i).enorm
  have hpt : ∀ y, A'.indicator (fun y => ‖dStep b E s h τ m W Vs χ ξ κ j y‖ₑ) y ≤
      ENNReal.ofReal (3 * C) * ∑ i : BI K np,
        A'.indicator (fun y => ‖betaS b E s h τ m W Vs j y i‖ₑ) y + ENNReal.ofReal (CΛ / W) :=
    fun y => by
    by_cases hy : y ∈ A'
    · simp only [Set.indicator_of_mem hy]
      have h1 := norm_fn_step_le hC (adm_zeta b E s h τ m W Vs j y)
        (by rw [← zeta_succ b E s h τ m W Vs hjs]; exact adm_zeta b E s h τ m W Vs (j + 1) y)
        (diagReal_dYs b E s h τ m W Vs j y)
      rw [← zeta_succ b E s h τ m W Vs hjs] at h1
      have h2 : ‖(W : ℂ)⁻¹ * κ.lam χ ξ b E (b3JumpAt b s τ m W j,
          zeta b E s h τ m W Vs j y)‖ ≤ CΛ / W := by
        rw [norm_mul]
        calc _ ≤ (1 / W) * CΛ := mul_le_mul (norm_inv_natCast_le W)
              (hCΛ _ _ (norm_gramEntry_b3JumpAt_le b s τ m W j) (adm_zeta b E s h τ m W Vs j y))
              (norm_nonneg _) (by positivity)
          _ = CΛ / W := by ring
      have h3 : ‖dStep b E s h τ m W Vs χ ξ κ j y‖ ≤
          3 * C * nrm (betaS b E s h τ m W Vs j y) + CΛ / W :=
        (norm_sub_le _ _).trans (add_le_add h1 h2)
      rw [← ofReal_norm]
      refine (ENNReal.ofReal_le_ofReal h3).trans (le_of_eq ?_)
      rw [ENNReal.ofReal_add (by have := nrm_nonneg (betaS b E s h τ m W Vs j y); positivity)
        (by positivity), ENNReal.ofReal_mul (by positivity), nrm, ENNReal.ofReal_sum_of_nonneg
          (fun _ _ => norm_nonneg _)]
      simp only [ofReal_norm]
    · simp [Set.indicator_of_notMem hy]
  calc _ ≤ ∫⁻ y, (ENNReal.ofReal (3 * C) * ∑ i : BI K np,
        A'.indicator (fun y => ‖betaS b E s h τ m W Vs j y i‖ₑ) y + ENNReal.ofReal (CΛ / W))
          ∂closedLaw b W np := lintegral_mono hpt
    _ = ENNReal.ofReal (3 * C) * ∑ i : BI K np, ∫⁻ y,
          A'.indicator (fun y => ‖betaS b E s h τ m W Vs j y i‖ₑ) y ∂closedLaw b W np +
        ENNReal.ofReal (CΛ / W) := by
      rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_finsetSum _ fun i _ => (hf i).indicator hAm, lintegral_const]
      simp
    _ = _ := by
      congr 2
      refine sum_congr rfl fun i _ => ?_
      unfold genBirthStep
      refine lintegral_congr_ae ((indicator_ae_eq_of_ae_eq_set (f := fun y =>
        ‖betaS b E s h τ m W Vs j y i‖ₑ) hAA.symm).mono fun y hy => ?_)
      rw [hy]
      by_cases hy' : y ∈ b3Alive b E s h τ m R W j Vs
      · simp only [Set.indicator_of_mem hy']
        rw [← ofReal_norm, ← ofReal_norm, norm_betaS_birth]
      · simp [Set.indicator_of_notMem hy']

end Mom

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram.IdentK.FW
