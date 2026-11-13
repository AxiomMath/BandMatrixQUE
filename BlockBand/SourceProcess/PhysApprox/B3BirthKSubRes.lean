module

public import BlockBand.SourceProcess.PhysApprox.B3BirthKSubFar

/-!
# The resolvent phase means at birth from path-only statements

This file removes the probe Gaussians from `BirthKResIn` and `BirthKResOut`. Measure:
`probedPathLaw W np b` for the estimates, `growthPathLaw W b` for the path-only statements; phase
`phaseLaw`; cap event `physCapEventC b E s h K W`; same domain and quantifiers as the estimates.

* `lintegral_sq_lintegral_l2_le` (Minkowski in the phase, via Tonelli and Cauchy–Schwarz in the
  probe): for every measurable `θ ↦ L_θ` and `g ~ CN(0, I_W)`,
  `E_g (E_θ‖L_θ g‖)² ≤ (E_θ ‖L_θ‖_HS)²`, `‖L‖_HS² = Re Tr(LᴴL)`.
* `lintegral_cap_phase_le`: hence, for a probe column `c` born before length `n`,
  `E_x[1_cap (E_θ‖(M_θV_n)_c‖)²] ≤ E_ω[1_cap (m_c/W)(E_θ (Re Tr(M_θᴴM_θ Y_{n;k_c}))^{1/2})²]`.
* **`birthKResIn_of_path`, `birthKResOut_of_path`**: `BirthKResIn ⇐ BirthKResInPath` and
  `BirthKResOut ⇐ BirthKResOutPath`, where the path-only estimates bound
  `E_ω[1_cap (m_c/W)(E_θ ‖M_θ𝒰ᴴι_{p_c}‖_HS)²]` with `M_θ = R(θ)ᴴA` (`resInMat`), resp.
  `M_θ = R(θ)Π𝕊` (`resOutMat`), at the birth lengths, for every born probe `c`
  (`⌊Wτ_c⌋ ≤ j`; unborn columns are zero).

The path-only estimates are **equivalent to the original estimates up to a universal constant** (not
formalized): for Gaussian `g`, `E‖Lg‖ ≥ c₀‖L‖_HS` (Khintchine–Kahane), so
`E_g (E_θ‖L_θg‖)² ≥ (E_θE_g‖L_θg‖)² ≥ c₀²(E_θ‖L_θ‖_HS)²`. So nothing is strengthened beyond a
constant, and the phase mean stays an `L¹` mean (no `L²`-in-phase strengthening, which would
replace `log(1/t)` by `1/t` per omitted mode).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.BirthKSub

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosingLeak BlockBand.SourceProcess.ComplexSourceLaw
open BlockBand.SourceProcess.ClosingAux BlockBand.SourceProcess.FullSourceStops
open BlockBand.Transmission.Bridge
open scoped NNReal ENNReal ComplexConjugate ComplexOrder

variable {W np : ℕ}

/-!
## Minkowski in the phase
-/

theorem re_trace_conjTranspose_mul_self_nonneg {ρ κ : Type*} [Fintype ρ] [Fintype κ]
    [DecidableEq κ] (L : Matrix ρ κ ℂ) : 0 ≤ (Lᴴ * L).trace.re :=
  (Complex.nonneg_iff.1 (posSemidef_conjTranspose_mul_self L).trace_nonneg).1

/-- `(E_g ‖Lg‖²)^{1/2} = ‖L‖_HS`. -/
theorem lintegral_l2_rpow_two (L : Matrix (Fin 2 × Fin W) (Fin W) ℂ) :
    (∫⁻ v, ENNReal.ofReal (l2 (L *ᵥ v)) ^ (2 : ℝ) ∂circularVectorLaw (Fin W)) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (Real.sqrt (Lᴴ * L).trace.re) := by
  have e : ∀ v, ENNReal.ofReal (l2 (L *ᵥ v)) ^ (2 : ℝ) = ENNReal.ofReal (l2 (L *ᵥ v) ^ 2) := by
    intro v
    rw [ENNReal.ofReal_rpow_of_nonneg (l2_nonneg _) zero_le_two, Real.rpow_two]
  simp_rw [e]
  rw [lintegral_l2_sq_mulVec, ENNReal.ofReal_rpow_of_nonneg
    (re_trace_conjTranspose_mul_self_nonneg L) (by norm_num), ← Real.sqrt_eq_rpow]

theorem measurable_ofReal_l2_mulVec' {α κ : Type*} [MeasurableSpace α] [Fintype κ]
    {L : α → Matrix (Fin 2 × Fin W) κ ℂ} {v : α → κ → ℂ} (hL : Measurable L) (hv : Measurable v) :
    Measurable fun a => ENNReal.ofReal (l2 (L a *ᵥ v a)) := by
  refine (continuous_l2.measurable.comp (measurable_pi_iff.2 fun y => ?_)).ennreal_ofReal
  simp only [mulVec, dotProduct]
  exact Finset.measurable_sum _ fun a _ => hL.eval_matrix.mul ((measurable_pi_apply a).comp hv)

theorem measurable_ofReal_l2_mulVec (A : Matrix (Fin 2 × Fin W) (Fin W) ℂ) :
    Measurable fun v : Fin W → ℂ => ENNReal.ofReal (l2 (A *ᵥ v)) :=
  (continuous_l2.comp (continuous_const.matrix_mulVec continuous_id)).measurable.ennreal_ofReal

/-- Cauchy–Schwarz in the probe: `E‖Ag‖‖Bg‖ ≤ ‖A‖_HS ‖B‖_HS`. -/
theorem lintegral_l2_mul_l2_le (A B : Matrix (Fin 2 × Fin W) (Fin W) ℂ) :
    ∫⁻ v, ENNReal.ofReal (l2 (A *ᵥ v)) * ENNReal.ofReal (l2 (B *ᵥ v)) ∂circularVectorLaw (Fin W) ≤
      ENNReal.ofReal (Real.sqrt (Aᴴ * A).trace.re) *
        ENNReal.ofReal (Real.sqrt (Bᴴ * B).trace.re) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (circularVectorLaw (Fin W))
    Real.HolderConjugate.two_two (measurable_ofReal_l2_mulVec A).aemeasurable
    (measurable_ofReal_l2_mulVec B).aemeasurable
  rw [lintegral_l2_rpow_two, lintegral_l2_rpow_two] at h
  exact h

theorem measurable_sqrt_hs {α : Type*} [MeasurableSpace α]
    {L : α → Matrix (Fin 2 × Fin W) (Fin W) ℂ} (hL : Measurable L) :
    Measurable fun θ => ENNReal.ofReal (Real.sqrt ((L θ)ᴴ * L θ).trace.re) := by
  have hLL := measurable_matrix_mul' (measurable_matrix_conjTranspose' hL) hL
  refine (Real.continuous_sqrt.measurable.comp (Complex.measurable_re.comp ?_)).ennreal_ofReal
  unfold Matrix.trace Matrix.diag
  exact Finset.measurable_sum _ fun z _ => hLL.eval_matrix

/-- `(E_θ f_θ)² = E_{θ,θ'} f_θ f_θ'`. -/
theorem sq_lintegral_eq_prod {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ θ, f θ ∂phaseLaw) ^ 2 = ∫⁻ q, f q.1 * f q.2 ∂(phaseLaw.prod phaseLaw) := by
  rw [sq, lintegral_prod_mul hf.aemeasurable hf.aemeasurable]

theorem lintegral_sq_swap {L : ℝ → Matrix (Fin 2 × Fin W) (Fin W) ℂ} (hL : Measurable L) :
    ∫⁻ v, ∫⁻ q, ENNReal.ofReal (l2 (L q.1 *ᵥ v)) * ENNReal.ofReal (l2 (L q.2 *ᵥ v))
        ∂(phaseLaw.prod phaseLaw) ∂circularVectorLaw (Fin W) =
      ∫⁻ q, ∫⁻ v, ENNReal.ofReal (l2 (L q.1 *ᵥ v)) * ENNReal.ofReal (l2 (L q.2 *ᵥ v))
        ∂circularVectorLaw (Fin W) ∂(phaseLaw.prod phaseLaw) := by
  have hG : Measurable fun z : (Fin W → ℂ) × (ℝ × ℝ) =>
      ENNReal.ofReal (l2 (L z.2.1 *ᵥ z.1)) * ENNReal.ofReal (l2 (L z.2.2 *ᵥ z.1)) :=
    Measurable.mul (measurable_ofReal_l2_mulVec' (hL.comp (measurable_fst.comp measurable_snd))
      measurable_fst)
      (measurable_ofReal_l2_mulVec' (hL.comp (measurable_snd.comp measurable_snd)) measurable_fst)
  exact lintegral_lintegral_swap hG.aemeasurable

/-- **Minkowski in the phase**: `E_g (E_θ‖L_θ g‖)² ≤ (E_θ ‖L_θ‖_HS)²`. -/
theorem lintegral_sq_lintegral_l2_le {L : ℝ → Matrix (Fin 2 × Fin W) (Fin W) ℂ}
    (hL : Measurable L) :
    ∫⁻ v, (∫⁻ θ, ENNReal.ofReal (l2 (L θ *ᵥ v)) ∂phaseLaw) ^ 2 ∂circularVectorLaw (Fin W) ≤
      (∫⁻ θ, ENNReal.ofReal (Real.sqrt ((L θ)ᴴ * L θ).trace.re) ∂phaseLaw) ^ 2 := by
  have hsq : ∀ v : Fin W → ℂ, (∫⁻ θ, ENNReal.ofReal (l2 (L θ *ᵥ v)) ∂phaseLaw) ^ 2 =
      ∫⁻ q, ENNReal.ofReal (l2 (L q.1 *ᵥ v)) * ENNReal.ofReal (l2 (L q.2 *ᵥ v))
        ∂(phaseLaw.prod phaseLaw) := fun v =>
    sq_lintegral_eq_prod (f := fun θ => ENNReal.ofReal (l2 (L θ *ᵥ v)))
      (measurable_ofReal_l2_mulVec' hL measurable_const)
  rw [lintegral_congr hsq, lintegral_sq_swap hL,
    sq_lintegral_eq_prod (measurable_sqrt_hs hL)]
  exact lintegral_mono fun q => lintegral_l2_mul_l2_le (L q.1) (L q.2)

/-!
## Removing the probe
-/

/-- A column of a not-yet-born probe is zero. -/
theorem col_mul_probeFrame_eq_zero (b E : ℝ) (τ m : Fin np → ℝ) (c : Fin np) {n : ℕ}
    (hc : ¬ ⌊(W : ℝ) * τ c⌋₊ < n) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (x : ProbedPath W np) : (X * probeFrame b E W n τ m x)ᵀ c = 0 := by
  have h0 : (probeColumns W n τ m x.2)ᵀ c = 0 := probeColumn_eq_zero n τ m x.2 c hc
  rw [col_mul, probeFrame, col_mul, h0, mulVec_zero, mulVec_zero]

/-- **The probe average of the squared phase mean**, on a path event `Cap`. -/
theorem lintegral_cap_phase_le (b E : ℝ) (τ m : Fin np → ℝ) (c : Fin np) (hm : 0 ≤ m c)
    {n : ℕ} (hc : ⌊(W : ℝ) * τ c⌋₊ < n) (Cap : Set (GrowthPath W))
    {M : GrowthPath W → ℝ → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hM : ∀ ω, Measurable (M ω)) :
    ∫⁻ x, {x : ProbedPath W np | x.1 ∈ Cap}.indicator (fun x =>
        (∫⁻ θ, ENNReal.ofReal (l2 ((M x.1 θ * probeFrame b E W n τ m x)ᵀ c)) ∂phaseLaw) ^ 2) x
      ∂probedPathLaw W np b ≤
    ∫⁻ ω, Cap.indicator (fun ω => ENNReal.ofReal (m c / W) *
        (∫⁻ θ, ENNReal.ofReal (Real.sqrt (((M ω θ)ᴴ * M ω θ *
          tagResponse b E W n ⌊(W : ℝ) * τ c⌋₊ ω).trace.re)) ∂phaseLaw) ^ 2) ω
      ∂growthPathLaw W b := by
  set p : Fin n := ⟨n - 1 - ⌊(W : ℝ) * τ c⌋₊, by omega⟩
  set κ : ℝ := m c / W
  have hκ : 0 ≤ κ := div_nonneg hm (Nat.cast_nonneg W)
  rw [probedPathLaw]
  refine (lintegral_prod_le _).trans (lintegral_mono fun ω => ?_)
  by_cases hω : ω ∈ Cap
  · have hmem : ∀ g : Fin np → Fin W → ℂ, ((ω, g) : ProbedPath W np) ∈
        {x : ProbedPath W np | x.1 ∈ Cap} := fun g => hω
    simp only [Set.indicator_of_mem (hmem _), Set.indicator_of_mem hω]
    set L : ℝ → Matrix (Fin 2 × Fin W) (Fin W) ℂ := fun θ => colMap b E W n (M ω θ) p ω
    have hL : Measurable L := measurable_colMap b E p (hM ω) measurable_const
    set G : (Fin W → ℂ) → ℝ≥0∞ := fun v =>
      (∫⁻ θ, ENNReal.ofReal (l2 (L θ *ᵥ v)) ∂phaseLaw) ^ 2 with hGdef
    have hGm : Measurable G :=
      ((measurable_ofReal_l2_mulVec' (hL.comp measurable_fst) measurable_snd).lintegral_prod_left'
        ).pow_const 2
    have hpt : ∀ g : Fin np → Fin W → ℂ,
        (∫⁻ θ, ENNReal.ofReal (l2 ((M ω θ * probeFrame b E W n τ m (ω, g))ᵀ c)) ∂phaseLaw) ^ 2
          = ENNReal.ofReal κ * G (g c) := by
      intro g
      have e : ∀ θ, ENNReal.ofReal (l2 ((M ω θ * probeFrame b E W n τ m (ω, g))ᵀ c)) =
          ENNReal.ofReal (Real.sqrt κ) * ENNReal.ofReal (l2 (L θ *ᵥ g c)) := by
        intro θ
        rw [l2_col_mul_probeFrame b E τ m c hc, ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
      simp_rw [e]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, mul_pow, ← ENNReal.ofReal_pow
        (Real.sqrt_nonneg _), Real.sq_sqrt hκ]
    simp_rw [hpt]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      (measurePreserving_eval (fun _ : Fin np => circularVectorLaw (Fin W)) c).lintegral_comp
        hGm]
    refine mul_le_mul_right ((lintegral_sq_lintegral_l2_le hL).trans (le_of_eq ?_)) _
    congr 2
    funext θ
    simp only [L, p]
    rw [trace_colMap b E hc]
  · have hnm : ∀ g : Fin np → Fin W → ℂ, ((ω, g) : ProbedPath W np) ∉
        {x : ProbedPath W np | x.1 ∈ Cap} := fun g => hω
    simp only [Set.indicator_of_notMem (hnm _), Set.indicator_of_notMem hω, lintegral_zero,
      le_refl]

/-!
## The two resolvent matrices and the path-only estimates
-/

theorem measurable_birthKRes (b E s h : ℝ) (W n : ℕ) (ω : GrowthPath W) :
    Measurable (birthKRes b E s h W n ω) :=
  measurable_matrix_inv.comp (measurable_matrix_sub measurable_const
    (measurable_matrix_cmul measurable_phase measurable_const))

/-- `M_θ = R(θ)ᴴA` (the `BirthKResIn` matrix). -/
def resInMat (b E s h : ℝ) (W n : ℕ) (ω : GrowthPath W) (θ : ℝ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  (birthKRes b E s h W n ω θ)ᴴ * farEmbed (omittedProj b E h W (closeLen s W) ω)

/-- `M_θ = R(θ)Π𝕊` (the `BirthKResOut` matrix). -/
def resOutMat (b E s h : ℝ) (W n : ℕ) (ω : GrowthPath W) (θ : ℝ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  birthKRes b E s h W n ω θ *
    (farEmbed (closingPairing b E h W (closeLen s W) ω) * scatteringMatrix b E W n ω)

theorem measurable_resInMat (b E s h : ℝ) (W n : ℕ) (ω : GrowthPath W) :
    Measurable (resInMat b E s h W n ω) :=
  measurable_matrix_mul' (measurable_matrix_conjTranspose' (measurable_birthKRes b E s h W n ω))
    measurable_const

theorem measurable_resOutMat (b E s h : ℝ) (W n : ℕ) (ω : GrowthPath W) :
    Measurable (resOutMat b E s h W n ω) :=
  measurable_matrix_mul' (measurable_birthKRes b E s h W n ω) measurable_const

theorem resIn_eq (b E s h : ℝ) (τ m : Fin np → ℝ) (n : ℕ) (x : ProbedPath W np) (θ : ℝ) :
    (birthKRes b E s h W n x.1 θ)ᴴ * birthKIn b E s h τ m W n x =
      resInMat b E s h W n x.1 θ * probeFrame b E W n τ m x := by
  rw [birthKIn, resInMat, Matrix.mul_assoc]

theorem resOut_eq (b E s h : ℝ) (τ m : Fin np → ℝ) (n : ℕ) (x : ProbedPath W np) (θ : ℝ) :
    birthKRes b E s h W n x.1 θ * birthKOut b E s h τ m W n x =
      resOutMat b E s h W n x.1 θ * probeFrame b E W n τ m x := by
  simp only [birthKOut, resOutMat, Matrix.mul_assoc]

/-- **`BirthKResInPath`**: on the cap event, the path second
moment of the phase mean of `W^{-1/2}‖R(θ)ᴴA𝒰ᴴι_{p_c}‖_HS` (weight `m_c`) is bounded at birth
steps, for every probe `c` born by then. Equivalent to `BirthKResIn` up to a universal constant
(see the module docstring). -/
def BirthKResInPath : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ), ComplexSourceLawDomain b E τ m T → 0 < s →
    (∀ j, s < τ j) → 0 < h → h < 1 → ∃ C : ℝ, ∀ᶠ W in atTop,
      ∀ j, closeLen s W ≤ j → j < ⌊(W : ℝ) * T⌋₊ → IsBirthStep τ W j → ∀ c : Fin np,
        ⌊(W : ℝ) * τ c⌋₊ ≤ j →
        ∫⁻ ω, (physCapEventC b E s h K W).indicator (fun ω => ENNReal.ofReal (m c / W) *
            (∫⁻ θ, ENNReal.ofReal (Real.sqrt (((resInMat b E s h W (j + 1) ω θ)ᴴ *
              resInMat b E s h W (j + 1) ω θ *
              tagResponse b E W (j + 1) ⌊(W : ℝ) * τ c⌋₊ ω).trace.re)) ∂phaseLaw) ^ 2) ω
          ∂growthPathLaw W b ≤ ENNReal.ofReal C

/-- **`BirthKResOutPath`**: as `BirthKResInPath` with
`R(θ)Π𝕊` in place of `R(θ)ᴴA`. Equivalent to `BirthKResOut` up to a universal constant. -/
def BirthKResOutPath : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ), ComplexSourceLawDomain b E τ m T → 0 < s →
    (∀ j, s < τ j) → 0 < h → h < 1 → ∃ C : ℝ, ∀ᶠ W in atTop,
      ∀ j, closeLen s W ≤ j → j < ⌊(W : ℝ) * T⌋₊ → IsBirthStep τ W j → ∀ c : Fin np,
        ⌊(W : ℝ) * τ c⌋₊ ≤ j →
        ∫⁻ ω, (physCapEventC b E s h K W).indicator (fun ω => ENNReal.ofReal (m c / W) *
            (∫⁻ θ, ENNReal.ofReal (Real.sqrt (((resOutMat b E s h W (j + 1) ω θ)ᴴ *
              resOutMat b E s h W (j + 1) ω θ *
              tagResponse b E W (j + 1) ⌊(W : ℝ) * τ c⌋₊ ω).trace.re)) ∂phaseLaw) ^ 2) ω
          ∂growthPathLaw W b ≤ ENNReal.ofReal C

/-- An unborn column contributes nothing. -/
theorem lintegral_cap_phase_unborn (b E : ℝ) (τ m : Fin np → ℝ) (c : Fin np) {n : ℕ}
    (hc : ¬ ⌊(W : ℝ) * τ c⌋₊ < n) (Cap : Set (GrowthPath W))
    (M : GrowthPath W → ℝ → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    ∫⁻ x, {x : ProbedPath W np | x.1 ∈ Cap}.indicator (fun x =>
        (∫⁻ θ, ENNReal.ofReal (l2 ((M x.1 θ * probeFrame b E W n τ m x)ᵀ c)) ∂phaseLaw) ^ 2) x
      ∂probedPathLaw W np b = 0 := by
  have h0 : ∀ x : ProbedPath W np, ∀ θ,
      l2 ((M x.1 θ * probeFrame b E W n τ m x)ᵀ c) = 0 := by
    intro x θ
    rw [col_mul_probeFrame_eq_zero b E τ m c hc, l2]
    simp
  simp only [h0]
  simp

/-- **`BirthKResIn` from the path-only estimate.** -/
theorem birthKResIn_of_path (hP : BirthKResInPath) : BirthKResIn := by
  intro b E np τ m T s h K hD hs hsτ hh0 hh1
  obtain ⟨C, hC⟩ := hP b E np τ m T s h K hD hs hsτ hh0 hh1
  obtain ⟨-, -, -, -, -, -, hm, -⟩ := hD
  refine ⟨C, ?_⟩
  filter_upwards [hC] with W hW
  intro j hj1 hj2 hb c
  simp_rw [resIn_eq]
  by_cases hcj : ⌊(W : ℝ) * τ c⌋₊ ≤ j
  · exact (lintegral_cap_phase_le b E τ m c (hm c) (by omega) _
      (measurable_resInMat b E s h W (j + 1))).trans (hW j hj1 hj2 hb c hcj)
  · rw [lintegral_cap_phase_unborn b E τ m c (by omega)]
    exact zero_le

/-- **`BirthKResOut` from the path-only estimate.** -/
theorem birthKResOut_of_path (hP : BirthKResOutPath) : BirthKResOut := by
  intro b E np τ m T s h K hD hs hsτ hh0 hh1
  obtain ⟨C, hC⟩ := hP b E np τ m T s h K hD hs hsτ hh0 hh1
  obtain ⟨-, -, -, -, -, -, hm, -⟩ := hD
  refine ⟨C, ?_⟩
  filter_upwards [hC] with W hW
  intro j hj1 hj2 hb c
  simp_rw [resOut_eq]
  by_cases hcj : ⌊(W : ℝ) * τ c⌋₊ ≤ j
  · exact (lintegral_cap_phase_le b E τ m c (hm c) (by omega) _
      (measurable_resOutMat b E s h W (j + 1))).trans (hW j hj1 hj2 hb c hcj)
  · rw [lintegral_cap_phase_unborn b E τ m c (by omega)]
    exact zero_le

end BlockBand.SourceProcess.PhysApprox.B3.BirthKSub
