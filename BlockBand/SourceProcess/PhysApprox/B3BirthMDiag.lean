module

public import BlockBand.SourceProcess.PhysApprox.B3BirthMFar
public import BlockBand.SourceProcess.TagBirth.Main
public import BlockBand.SourceProcess.PhysApprox.ClosingGramInt
public import BlockBand.SourceProcess.RawTag.JointLaw
public import BlockBand.SourceProcess.ClosedSumProof.Adapted
public import BlockBand.SourceProcess.ClosingLeak.Bound
public import BlockBand.SourceProcess.PhysApprox.B3BirthClose

/-!
# The closed Gram diagonal of a newborn tag

Notation at the birth length `n = j + 1` of the tag `i` (`⌊Wτ_i⌋ = j`): `V` the unclosed newborn
column, `v = C_n(z)ᴴV` the closed one (`b3ClosedFrameAt_col`), `Y = Y_{n;j}`.

* `gram_err_le` (pointwise): `|N_σ(v) − t| ≤ (1+ε)|‖V‖² − t| + εt + (1 + ε⁻¹)‖v − V‖² + ‖(1−P)V‖²`,
  `N_0 = ‖·‖²`, `N_1 = ‖P·‖²`;
* `lintegral_newborn_sq_sub_le`: `E|‖V‖² − m t| ≤ m E[W⁻¹(Tr Y²)^{1/2} + |W⁻¹Tr Y − t|]`
  (Gaussian concentration over the newborn probe, `Birth.lintegral_quad_sub_le`);
* `lintegral_newborn_far_eq`: `E‖(1−P)V‖² = m E[W⁻¹ Re Tr((1−P)Y)]`;
* `lintegral_closed_leak_le`: `E‖v − V‖² ≤ 2E‖(1−P)V‖²` (phase average, `lintegral_phase_l2_sq_le`);
* **`complexBirthGramDiag_holds`**: `MatchedTracesContract → GaussianAbsorptionContract →
  ComplexBirthGramDiag`, with `TagBirth.tagBirthValue_holds` (trace and square) and
  `newbornFarMass_holds`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

namespace BirthM

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosingLeak
open BlockBand.SourceProcess.ClosingAux BlockBand.SourceProcess.ClosedLimit
open BlockBand.SourceProcess.ClosedPath BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.Transmission.Bridge
open scoped NNReal ENNReal ComplexConjugate ComplexOrder

variable {W : ℕ}

/-!
## The pointwise error bound
-/

theorem sq_sub_sq_le {x a ℓ : ℝ} (hx : 0 ≤ x) (ha : 0 ≤ a) (h : |x - a| ≤ ℓ) :
    |x ^ 2 - a ^ 2| ≤ ℓ * (2 * a + ℓ) := by
  have h1 := abs_le.mp h
  have hℓ : 0 ≤ ℓ := (abs_nonneg _).trans h
  rw [show x ^ 2 - a ^ 2 = (x - a) * (x + a) by ring, abs_mul,
    abs_of_nonneg (show 0 ≤ x + a by linarith)]
  exact mul_le_mul h (by linarith) (by linarith) hℓ

/-- **The pointwise error of a closed newborn diagonal.** -/
theorem gram_err_le (V v : Fin 2 × Fin W → ℂ) {t ε : ℝ} (hε : 0 < ε) (σ : Fin 2) :
    |(if σ = 0 then l2 v ^ 2 else l2 (nearPortProj W *ᵥ v) ^ 2) - t| ≤
      (1 + ε) * |l2 V ^ 2 - t| + ε * t + (1 + ε⁻¹) * l2 (v - V) ^ 2 +
        l2 ((1 - nearPortProj W) *ᵥ V) ^ 2 := by
  set a := l2 V
  set ℓ := l2 (v - V)
  set f := l2 ((1 - nearPortProj W) *ᵥ V) ^ 2
  have ha : 0 ≤ a := l2_nonneg _
  have hℓ : 0 ≤ ℓ := l2_nonneg _
  have hf : 0 ≤ f := sq_nonneg _
  -- `2aℓ ≤ εa² + ℓ²/ε` and `a² ≤ |a² − t| + t`
  have hamgm : 2 * a * ℓ ≤ ε * a ^ 2 + ε⁻¹ * ℓ ^ 2 := by
    have h := sq_nonneg (ε * a - ℓ)
    have hε' : ε * ε⁻¹ = 1 := mul_inv_cancel₀ hε.ne'
    have : ε⁻¹ * (ε * a - ℓ) ^ 2 = ε * a ^ 2 - 2 * a * ℓ + ε⁻¹ * ℓ ^ 2 := by
      field_simp; ring
    nlinarith [mul_nonneg (inv_nonneg.mpr hε.le) h]
  have hat : a ^ 2 ≤ |a ^ 2 - t| + t := by linarith [le_abs_self (a ^ 2 - t)]
  have hkey : ∀ x : ℝ, 0 ≤ x → |x - a| ≤ ℓ → |x ^ 2 - t| ≤ (1 + ε) * |a ^ 2 - t| + ε * t +
      (1 + ε⁻¹) * ℓ ^ 2 + f := by
    intro x hx hxa
    have h1 := sq_sub_sq_le hx ha hxa
    have h2 : |x ^ 2 - t| ≤ |x ^ 2 - a ^ 2| + |a ^ 2 - t| := by
      rw [show x ^ 2 - t = (x ^ 2 - a ^ 2) + (a ^ 2 - t) by ring]; exact abs_add_le _ _
    nlinarith
  split_ifs with hσ
  · exact hkey _ (l2_nonneg _) (by
      have := abs_l2_sub_le v V; exact this)
  · -- the near norm: `‖Pv‖` is within `ℓ` of `‖PV‖`, and `‖PV‖² = a² − f`
    set q := l2 (nearPortProj W *ᵥ V)
    have hq : 0 ≤ q := l2_nonneg _
    have hsplit : a ^ 2 = q ^ 2 + f := l2_sq_split V
    have hpq : |l2 (nearPortProj W *ᵥ v) - q| ≤ ℓ := by
      refine (abs_l2_sub_le _ _).trans ?_
      rw [← mulVec_sub]
      exact l2_near_le _
    have hqa : q ≤ a := l2_near_le V
    have h1 := sq_sub_sq_le (l2_nonneg _) hq hpq
    have h2 : |l2 (nearPortProj W *ᵥ v) ^ 2 - t| ≤
        |l2 (nearPortProj W *ᵥ v) ^ 2 - q ^ 2| + f + |a ^ 2 - t| := by
      rw [show l2 (nearPortProj W *ᵥ v) ^ 2 - t =
        (l2 (nearPortProj W *ᵥ v) ^ 2 - q ^ 2) + (-f) + (a ^ 2 - t) by rw [hsplit]; ring]
      refine (abs_add_le _ _).trans ?_
      have h3 := abs_add_le (l2 (nearPortProj W *ᵥ v) ^ 2 - q ^ 2) (-f)
      rw [abs_neg, abs_of_nonneg hf] at h3
      linarith
    nlinarith

/-!
## Integration over the newborn probe
-/

theorem lintegral_probed_eval {np : ℕ} (b : ℝ) (i : Fin np)
    {F : GrowthPath W × (Fin W → ℂ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F (x.1, x.2 i) ∂probedPathLaw W np b =
      ∫⁻ ω, ∫⁻ g, F (ω, g) ∂circularVectorLaw (Fin W) ∂growthPathLaw W b := by
  rw [probedPathLaw, lintegral_prod (fun x : ProbedPath W np => F (x.1, x.2 i))
    (hF.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))).aemeasurable]
  refine lintegral_congr fun ω => ?_
  exact (measurePreserving_eval (fun _ : Fin np => circularVectorLaw (Fin W)) i).lintegral_comp
    (hF.comp measurable_prodMk_left)

theorem measurable_newR (b E : ℝ) (n : ℕ) (p : Fin n) :
    Measurable (newR b E W n p) :=
  measurable_matrix_mul' (measurable_matrix_conjTranspose'
    (ClosedSumProof.measurable_boundaryToInterior b E n)) measurable_const

theorem measurable_newR_mulVec (b E : ℝ) (n : ℕ) (p : Fin n)
    (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Measurable fun z : GrowthPath W × (Fin W → ℂ) => (M * newR b E W n p z.1) *ᵥ z.2 :=
  RawTag.measurable_mulVec' (measurable_matrix_mul' measurable_const
    ((measurable_newR b E n p).comp measurable_fst)) measurable_snd

theorem sqrt_div_sq_norm {μ : ℝ} (hμ : 0 ≤ μ) (W : ℕ) :
    ‖(((Real.sqrt (μ / W)) : ℝ) : ℂ)‖ ^ 2 = μ / W := by
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (div_nonneg hμ (Nat.cast_nonneg W))]

/-- `‖QV‖² = (m/W)‖QRg‖²` for the unclosed newborn column. -/
theorem l2_sq_probeFrame_col (b E : ℝ) {np n : ℕ} (τ m : Fin np → ℝ) (i : Fin np)
    (hm : 0 ≤ m i) (hi : ⌊(W : ℝ) * τ i⌋₊ < n) (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (x : ProbedPath W np) :
    l2 (M *ᵥ fun w => probeFrame b E W n τ m x w i) ^ 2 =
      m i / W * l2 ((M * newR b E W n ⟨n - 1 - ⌊(W : ℝ) * τ i⌋₊, by omega⟩ x.1) *ᵥ x.2 i) ^ 2 := by
  rw [probeFrame_col b E τ m i hi x, mulVec_smul, l2_smul_sq, sqrt_div_sq_norm hm, mulVec_mulVec]

theorem trace_far_newR (b E : ℝ) {n k : ℕ} (hk : k < n) (ω : GrowthPath W) :
    (((1 - nearPortProj W) * newR b E W n ⟨n - 1 - k, by omega⟩ ω)ᴴ *
      ((1 - nearPortProj W) * newR b E W n ⟨n - 1 - k, by omega⟩ ω)).trace =
        ((1 - nearProjection W) * tagResponse b E W n k ω).trace := by
  set R := newR b E W n ⟨n - 1 - k, by omega⟩ ω
  set F := 1 - nearPortProj W
  have hF : Fᴴ * F = F := by
    simp only [F]
    rw [one_sub_nearPortProj_eq_farEmbed, farEmbed_conjTranspose, conjTranspose_one, farEmbed_mul,
      Matrix.mul_one]
  rw [conjTranspose_mul]
  calc (Rᴴ * Fᴴ * (F * R)).trace = (Rᴴ * (Fᴴ * F * R)).trace := by simp only [Matrix.mul_assoc]
    _ = (Fᴴ * F * R * Rᴴ).trace := by rw [Matrix.trace_mul_comm]
    _ = _ := by rw [hF, Matrix.mul_assoc, newR_mul_conj b E hk]; rfl

theorem measurable_probeFrame_col (b E : ℝ) {np n : ℕ} (τ m : Fin np → ℝ) (i : Fin np) :
    Measurable fun x : ProbedPath W np => fun w => probeFrame b E W n τ m x w i :=
  measurable_pi_iff.2 fun _ => (measurable_probeFrame b E W n τ m).eval_matrix

/-- **Gaussian concentration of the newborn squared norm** over its probe:
`E|‖V‖² − m t| ≤ m E[W⁻¹(Re Tr Y²)^{1/2} + |W⁻¹Tr Y − t|]`, `Y = Y_{n;k}`, `k = ⌊Wτ_i⌋ < n`. -/
theorem lintegral_newborn_sq_sub_le (b E : ℝ) {np n : ℕ} (τ m : Fin np → ℝ) (i : Fin np)
    (hm : 0 ≤ m i) (hi : ⌊(W : ℝ) * τ i⌋₊ < n) (t : ℝ) :
    ∫⁻ x, ENNReal.ofReal |l2 (fun w => probeFrame b E W n τ m x w i) ^ 2 - m i * t|
        ∂probedPathLaw W np b ≤
      ENNReal.ofReal (m i) * ∫⁻ ω, (ENNReal.ofReal ((W : ℝ)⁻¹ * Real.sqrt
          (tagResponse b E W n ⌊(W : ℝ) * τ i⌋₊ ω *
            tagResponse b E W n ⌊(W : ℝ) * τ i⌋₊ ω).trace.re) +
        ‖(W : ℂ)⁻¹ * (tagResponse b E W n ⌊(W : ℝ) * τ i⌋₊ ω).trace - (t : ℂ)‖ₑ)
        ∂growthPathLaw W b := by
  set k := ⌊(W : ℝ) * τ i⌋₊
  set p : Fin n := ⟨n - 1 - k, by omega⟩
  set Y := fun ω => tagResponse b E W n k ω
  set F : GrowthPath W × (Fin W → ℂ) → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (m i / W) * ENNReal.ofReal |l2 (((1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) *
      newR b E W n p z.1) *ᵥ z.2) ^ 2 -
      ((newR b E W n p z.1)ᴴ * newR b E W n p z.1).trace.re| +
    ENNReal.ofReal (m i) * ‖(W : ℂ)⁻¹ * (Y z.1).trace - (t : ℂ)‖ₑ with hFdef
  have hmR := measurable_newR (W := W) b E n p
  have hTr : Measurable fun ω : GrowthPath W => ((newR b E W n p ω)ᴴ * newR b E W n p ω).trace.re :=
    Complex.measurable_re.comp ((continuous_id.matrix_trace).measurable.comp
      (measurable_matrix_mul' (measurable_matrix_conjTranspose' hmR) hmR))
  have hF : Measurable F := by
    refine (measurable_const.mul (((continuous_l2.measurable.comp
      (measurable_newR_mulVec b E n p 1)).pow_const 2).sub
        (hTr.comp measurable_fst)).abs.ennreal_ofReal).add ?_
    have hY : Measurable fun z : GrowthPath W × (Fin W → ℂ) =>
        ‖(W : ℂ)⁻¹ * (Y z.1).trace - (t : ℂ)‖ₑ :=
      ((measurable_const.mul ((continuous_id.matrix_trace).measurable.comp
        ((FullSourceStops.measurable_tagResponse b E n k).comp measurable_fst))).sub_const
          _).enorm
    exact hY.const_mul _
  have hpt : ∀ x : ProbedPath W np, ENNReal.ofReal |l2 (fun w => probeFrame b E W n τ m x w i) ^ 2 -
      m i * t| ≤ F (x.1, x.2 i) := by
    intro x
    have e := l2_sq_probeFrame_col b E τ m i hm hi 1 x
    rw [one_mulVec] at e
    rw [e]
    have htr : ((newR b E W n p x.1)ᴴ * newR b E W n p x.1).trace = (Y x.1).trace :=
      trace_conj_mul_newR b E hi x.1
    have hre : |(W : ℝ)⁻¹ * ((newR b E W n p x.1)ᴴ * newR b E W n p x.1).trace.re - t| ≤
        ‖(W : ℂ)⁻¹ * (Y x.1).trace - (t : ℂ)‖ := by
      refine le_trans (le_of_eq ?_) (Complex.abs_re_le_norm _)
      rw [htr, Complex.sub_re, ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
        Complex.re_ofReal_mul, Complex.ofReal_re]
    set q := l2 (((1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) * newR b E W n p x.1) *ᵥ
      x.2 i) ^ 2
    set c := ((newR b E W n p x.1)ᴴ * newR b E W n p x.1).trace.re
    have hW : (0 : ℝ) ≤ m i / W := div_nonneg hm (Nat.cast_nonneg W)
    have hsplit : |m i / W * q - m i * t| ≤ m i / W * |q - c| + m i * |(W : ℝ)⁻¹ * c - t| := by
      rw [show m i / W * q - m i * t = m i / W * (q - c) + m i * ((W : ℝ)⁻¹ * c - t) by
        rw [div_eq_mul_inv]; ring]
      refine (abs_add_le _ _).trans (le_of_eq ?_)
      rw [abs_mul, abs_mul, abs_of_nonneg hW, abs_of_nonneg hm]
    simp only [hFdef]
    rw [← ENNReal.ofReal_mul hW, ← ofReal_norm, ← ENNReal.ofReal_mul hm,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal (hsplit.trans ?_)
    gcongr
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_probed_eval b i hF, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun ω => ?_
  simp only [hFdef]
  rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hG := lintegral_abs_l2_sq_sub_le (W := W) (newR b E W n p ω)
  have hsq := trace_sq_of_mul_conj (newR_mul_conj b E hi ω)
  simp only [Matrix.one_mul]
  rw [mul_add]
  refine add_le_add ?_ le_rfl
  calc ENNReal.ofReal (m i / W) * ∫⁻ g, ENNReal.ofReal |l2 (newR b E W n p ω *ᵥ g) ^ 2 -
        ((newR b E W n p ω)ᴴ * newR b E W n p ω).trace.re| ∂circularVectorLaw (Fin W)
      ≤ ENNReal.ofReal (m i / W) * ENNReal.ofReal (Real.sqrt ((newR b E W n p ω)ᴴ *
          newR b E W n p ω * ((newR b E W n p ω)ᴴ * newR b E W n p ω)ᴴ).trace.re) := by gcongr
    _ = _ := by
        rw [hsq, ← ENNReal.ofReal_mul (div_nonneg hm (Nat.cast_nonneg W)),
          ← ENNReal.ofReal_mul hm]
        congr 1
        rw [div_eq_mul_inv, mul_assoc]

/-- **The newborn far mass in the probe mean**: `E‖(1−P)V‖² = m E[W⁻¹ Re Tr((1−P)Y)]`. -/
theorem lintegral_newborn_far_eq (b E : ℝ) {np n : ℕ} (τ m : Fin np → ℝ) (i : Fin np)
    (hm : 0 ≤ m i) (hi : ⌊(W : ℝ) * τ i⌋₊ < n) :
    ∫⁻ x, ENNReal.ofReal (l2 ((1 - nearPortProj W) *ᵥ fun w => probeFrame b E W n τ m x w i) ^ 2)
        ∂probedPathLaw W np b =
      ENNReal.ofReal (m i) * ∫⁻ ω, ENNReal.ofReal ((W : ℝ)⁻¹ *
        ((1 - nearProjection W) * tagResponse b E W n ⌊(W : ℝ) * τ i⌋₊ ω).trace.re)
        ∂growthPathLaw W b := by
  set k := ⌊(W : ℝ) * τ i⌋₊
  set p : Fin n := ⟨n - 1 - k, by omega⟩
  set F : GrowthPath W × (Fin W → ℂ) → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (m i / W) *
      ENNReal.ofReal (l2 (((1 - nearPortProj W) * newR b E W n p z.1) *ᵥ z.2) ^ 2) with hFdef
  have hF : Measurable F := measurable_const.mul ((continuous_l2.measurable.comp
    (measurable_newR_mulVec b E n p _)).pow_const 2).ennreal_ofReal
  have hpt : ∀ x : ProbedPath W np,
      ENNReal.ofReal (l2 ((1 - nearPortProj W) *ᵥ fun w => probeFrame b E W n τ m x w i) ^ 2) =
        F (x.1, x.2 i) := by
    intro x
    rw [l2_sq_probeFrame_col b E τ m i hm hi _ x, ENNReal.ofReal_mul (div_nonneg hm
      (Nat.cast_nonneg W))]
  simp_rw [hpt]
  rw [lintegral_probed_eval b i hF, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun ω => ?_
  simp only [hFdef]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_l2_sq_mulVec,
    trace_far_newR b E hi ω, ← ENNReal.ofReal_mul (div_nonneg hm (Nat.cast_nonneg W)),
    ← ENNReal.ofReal_mul hm]
  congr 1
  rw [div_eq_mul_inv, mul_assoc]

/-- **The closing leak of the newborn column** in mean: `E‖C_nᴴV − V‖² ≤ 2E‖(1−P)V‖²`. -/
theorem lintegral_closed_leak_le {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E)
    (hE2 : E < 2) (hW : 1 ≤ W) (s h : ℝ) (hh0 : 0 < h) (hh1 : h < 1) {np n : ℕ} (hn : 1 ≤ n)
    (τ m : Fin np → ℝ) (i : Fin np) :
    ∫⁻ y, ENNReal.ofReal (l2 ((physClosingMapAt b E s h W n y.1.1 (phase y.2))ᴴ *ᵥ
        (fun w => probeFrame b E W n τ m y.1 w i) - fun w => probeFrame b E W n τ m y.1 w i) ^ 2)
      ∂closedLaw b W np ≤
    ENNReal.ofReal 2 * ∫⁻ x, ENNReal.ofReal
      (l2 ((1 - nearPortProj W) *ᵥ fun w => probeFrame b E W n τ m x w i) ^ 2)
      ∂probedPathLaw W np b := by
  have hV := measurable_probeFrame_col (W := W) b E (n := n) τ m i
  have hC : Measurable fun y : ProbedPath W np × ℝ =>
      physClosingMapAt b E s h W n y.1.1 (phase y.2) :=
    measurable_physClosingMapAt_comp b E s h n (measurable_fst.comp measurable_fst)
      (measurable_phase.comp measurable_snd)
  have hm : Measurable fun y : ProbedPath W np × ℝ =>
      ENNReal.ofReal (l2 ((physClosingMapAt b E s h W n y.1.1 (phase y.2))ᴴ *ᵥ
        (fun w => probeFrame b E W n τ m y.1 w i) - fun w => probeFrame b E W n τ m y.1 w i) ^ 2) :=
    ((continuous_l2.measurable.comp ((RawTag.measurable_mulVec'
      (measurable_matrix_conjTranspose' hC) (hV.comp measurable_fst)).sub
        (hV.comp measurable_fst))).pow_const 2).ennreal_ofReal
  rw [lintegral_prod _ hm.aemeasurable, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hae := ae_phaseAvg_closingDefectAt hb0 hb hE1 hE2 hW s h hh0 hh1
  have hae' : ∀ᵐ x ∂probedPathLaw W np b, ∀ n, 1 ≤ n →
      (∀ θ, IsUnit (1 - phase θ • closingN (scatteringMatrix b E W n x.1)
        (farEmbed (omittedProj b E h W (closeLen s W) x.1))
        (farEmbed (closingPairing b E h W (closeLen s W) x.1))).det) ∧
      phaseAvg (fun θ => (physClosingMapAt b E s h W n x.1 (phase θ) - 1) *
          (physClosingMapAt b E s h W n x.1 (phase θ) - 1)ᴴ) =
        (2 : ℂ) • farEmbed (omittedProj b E h W (closeLen s W) x.1) :=
    Measure.QuasiMeasurePreserving.ae (Measure.quasiMeasurePreserving_fst (μ := growthPathLaw W b)
      (ν := Measure.pi fun _ : Fin np => circularVectorLaw (Fin W))) hae
  refine lintegral_mono_ae (hae'.mono fun x hx => ?_)
  obtain ⟨hU, hD⟩ := hx n hn
  have key := lintegral_phase_l2_sq_le hD hU (fun w => probeFrame b E W n τ m x w i)
  refine le_trans (le_of_eq ?_) (key.trans (le_of_eq (ENNReal.ofReal_mul (by norm_num))))
  rfl

/-!
## The path inputs
-/

/-- `E[W⁻¹(Re Tr Y²)^{1/2}] ≤ (C/W)^{1/2}` from the square moment `E|Tr(Y/W)²| ≤ C/W`. -/
theorem lintegral_sqrt_trace_sq_le (b E : ℝ) {n k : ℕ} (hk : k < n) {C : ℝ}
    (hC : ∫⁻ ω, ‖(((W : ℂ)⁻¹ • tagResponse b E W n k ω) ^ 2).trace‖ₑ ∂growthPathLaw W b ≤
      ENNReal.ofReal (C / W)) :
    ∫⁻ ω, ENNReal.ofReal ((W : ℝ)⁻¹ * Real.sqrt
        (tagResponse b E W n k ω * tagResponse b E W n k ω).trace.re) ∂growthPathLaw W b ≤
      ENNReal.ofReal (Real.sqrt (max C 0 / W)) := by
  set f : GrowthPath W → ℝ := fun ω =>
    ((W : ℝ)⁻¹) ^ 2 * (tagResponse b E W n k ω * tagResponse b E W n k ω).trace.re with hfdef
  have hY := FullSourceStops.measurable_tagResponse (W := W) b E n k
  have hf : Measurable f := measurable_const.mul (Complex.measurable_re.comp
    ((continuous_id.matrix_trace).measurable.comp (measurable_matrix_mul' hY hY)))
  have hYY : ∀ ω, 0 ≤ (tagResponse b E W n k ω * tagResponse b E W n k ω).trace.re := by
    intro ω
    rw [← trace_sq_of_mul_conj (newR_mul_conj b E hk ω)]
    exact (Complex.nonneg_iff.mp (Matrix.posSemidef_self_mul_conjTranspose _).trace_nonneg).1
  have hf0 : ∀ ω, 0 ≤ f ω := fun ω => mul_nonneg (sq_nonneg _) (hYY ω)
  have hpt : ∀ ω, (W : ℝ)⁻¹ * Real.sqrt (tagResponse b E W n k ω *
      tagResponse b E W n k ω).trace.re = Real.sqrt (f ω) := by
    intro ω
    rw [hfdef, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_nonneg.mpr (Nat.cast_nonneg W))]
  simp_rw [hpt]
  refine (lintegral_sqrt_le hf hf0).trans ?_
  have h1 : ∫⁻ ω, ENNReal.ofReal (f ω) ∂growthPathLaw W b ≤ ENNReal.ofReal (max C 0 / W) := by
    refine le_trans (lintegral_mono fun ω => ?_) (hC.trans (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg W))))
    rw [← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ((le_of_eq ?_).trans (Complex.re_le_norm _))
    rw [smul_pow, trace_smul, smul_eq_mul, sq (tagResponse b E W n k ω),
      show ((W : ℂ)⁻¹) ^ 2 = ((((W : ℝ)⁻¹) ^ 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.re_ofReal_mul]
  calc (∫⁻ ω, ENNReal.ofReal (f ω) ∂growthPathLaw W b) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal (max C 0 / W)) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow h1 (by norm_num)
    _ = _ := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), Real.sqrt_eq_rpow]

/-!
## `ComplexBirthGramDiag`
-/

theorem enorm_indicator_le {α : Type*} (A : Set α) (f : α → ℂ) (y : α) :
    ‖A.indicator f y‖ₑ ≤ ‖f y‖ₑ := by
  by_cases hy : y ∈ A
  · rw [Set.indicator_of_mem hy]
  · rw [Set.indicator_of_notMem hy, enorm_zero]; exact zero_le

/-- The pointwise bound of the closed newborn diagonal error, in `ℝ≥0∞`. -/
theorem enorm_gram_err_le (b E s h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (i : Fin np)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (n : ℕ) (σ : Fin 2)
    (A : Set (ProbedPath W np × ℝ)) {t ε : ℝ} (hε : 0 < ε) (y : ProbedPath W np × ℝ) :
    ‖A.indicator (fun y => gramEntry (σ, Sum.inr i, Sum.inr i)
        (b3ClosedGramAt b E s h τ m W n Vs y) - (t : ℂ)) y‖ₑ ≤
      ENNReal.ofReal (1 + ε) *
          ENNReal.ofReal |l2 (fun w => probeFrame b E W n τ m y.1 w i) ^ 2 - t| +
        ENNReal.ofReal (ε * t) +
        ENNReal.ofReal (1 + ε⁻¹) * ENNReal.ofReal (l2 ((physClosingMapAt b E s h W n y.1.1
          (phase y.2))ᴴ *ᵥ (fun w => probeFrame b E W n τ m y.1 w i) -
            fun w => probeFrame b E W n τ m y.1 w i) ^ 2) +
        ENNReal.ofReal
          (l2 ((1 - nearPortProj W) *ᵥ fun w => probeFrame b E W n τ m y.1 w i) ^ 2) := by
  refine (enorm_indicator_le A _ y).trans ?_
  have hg := gramEntry_closed_diag (n := n) b E s h τ m i Vs y σ
  dsimp only at hg
  rw [hg, b3ClosedFrameAt_col]
  set V := fun w => probeFrame b E W n τ m y.1 w i
  set v := (physClosingMapAt b E s h W n y.1.1 (phase y.2))ᴴ *ᵥ V
  have herr := gram_err_le V v (t := t) hε σ
  rw [← Complex.ofReal_sub, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
  refine (ENNReal.ofReal_le_ofReal herr).trans ?_
  refine (ENNReal.ofReal_add_le).trans (add_le_add ((ENNReal.ofReal_add_le).trans (add_le_add
    ((ENNReal.ofReal_add_le).trans (add_le_add ?_ le_rfl)) ?_)) le_rfl)
  · rw [ENNReal.ofReal_mul (by positivity)]
  · rw [ENNReal.ofReal_mul (by positivity)]

theorem lintegral_four_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {f g k : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) (a c e : ℝ≥0∞) :
    ∫⁻ y, (a * f y + c + e * g y + k y) ∂μ =
      a * ∫⁻ y, f y ∂μ + c + e * ∫⁻ y, g y ∂μ + ∫⁻ y, k y ∂μ := by
  rw [lintegral_add_left (f := fun y => a * f y + c + e * g y)
      (((hf.const_mul a).add measurable_const).add (hg.const_mul e)),
    lintegral_add_left (f := fun y => a * f y + c) ((hf.const_mul a).add measurable_const),
    lintegral_add_left (f := fun y => a * f y) (hf.const_mul a), lintegral_const_mul a hf,
    lintegral_const, measure_univ, mul_one, lintegral_const_mul e hg]

end BirthM

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosingLeak
open BlockBand.SourceProcess.ClosingAux BlockBand.SourceProcess.ClosedLimit
open BlockBand.SourceProcess.ClosedPath BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.Transmission.Bridge
open scoped NNReal ENNReal ComplexConjugate ComplexOrder

open BirthM

variable {W : ℕ}

/-- **`ComplexBirthGramDiag` holds**, from `MatchedTracesContract` and
`GaussianAbsorptionContract` (`gaussianLpGradient_holds` is used inside).
-/
theorem complexBirthGramDiag_holds (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) : ComplexBirthGramDiag := by
  intro b E np τ m T s h K Vs hD R θ hθ i σ
  obtain ⟨⟨hb0, hb, hE1, hE2, -, -, hm0, hτT⟩, hs, hsτ, hh0, hh1, -⟩ := hD
  have hm := hm0 i
  have hTB := TagBirth.tagBirthValue_holds hMT hGA
    BlockBand.GaussianCalculus.gaussianLpGradient_holds
  set t := dStar b * m i with htdef
  have hd : 0 ≤ dStar b := by
    unfold dStar; have : 0 < 1 - b := by linarith
    positivity
  have ht : 0 ≤ t := mul_nonneg hd hm
  set ε := θ / (2 * (t + 1)) with hεdef
  have hε : 0 < ε := by positivity
  set M := (m i + 1) * (2 * (1 + ε) + 2 * (1 + ε⁻¹) + 1) with hMdef
  have hM : 0 < M := by positivity
  set θ₁ := θ / (2 * M) with hθ₁def
  have hθ₁ : 0 < θ₁ := by positivity
  have hsT : s / 2 < T := by linarith [hsτ i, hτT i]
  obtain ⟨Wt, hWt⟩ := hTB.trace b hb0 hb E hE1 hE2 (s / 2) T 1 (by positivity) hsT le_rfl θ₁ hθ₁
  obtain ⟨C, Ws, hWs⟩ := hTB.square b hb0 hb E hE1 hE2 (s / 2) T (by positivity) hsT
  set C' := max C 0
  filter_upwards [newbornFarMass_holds hMT hGA b hb0 hb E hE1 hE2 s T hs θ₁ hθ₁,
    eventually_ge_atTop (max (max Wt Ws) (max (⌈2 / s⌉₊ + 1) (⌈C' / θ₁ ^ 2⌉₊ + 1)))]
    with W hFar hW j hj1 hj2 hij
  subst hij
  set k := ⌊(W : ℝ) * τ i⌋₊ with hkdef
  have hWt' : Wt ≤ W := le_trans (by simp) hW
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
  -- the path inputs
  have hTr := hWt W hWt' k hkε hkT
  have hYm : Measurable fun ω : GrowthPath W =>
      (W : ℂ)⁻¹ * (tagResponse b E W (k + 1) k ω).trace - (dStar b : ℂ) :=
    (measurable_const.mul ((continuous_id.matrix_trace).measurable.comp
      (FullSourceStops.measurable_tagResponse b E (k + 1) k))).sub_const _
  rw [ENNReal.ofReal_one, eLpNorm_one_eq_lintegral_enorm hYm.aestronglyMeasurable] at hTr
  have hSq := lintegral_sqrt_trace_sq_le b E hlt (hWs W hWs' k hkε hkT)
  have hsq : Real.sqrt (C' / W) ≤ θ₁ := by
    have hc : C' / θ₁ ^ 2 ≤ W := by
      have := Nat.le_ceil (C' / θ₁ ^ 2)
      have h2 : ((⌈C' / θ₁ ^ 2⌉₊ : ℕ) : ℝ) ≤ W := by
        exact_mod_cast (by omega : ⌈C' / θ₁ ^ 2⌉₊ ≤ W)
      linarith
    have : C' / W ≤ θ₁ ^ 2 := by
      rw [div_le_iff₀ hWr]; rw [div_le_iff₀ (by positivity)] at hc; linarith
    calc Real.sqrt (C' / W) ≤ Real.sqrt (θ₁ ^ 2) := Real.sqrt_le_sqrt this
      _ = θ₁ := Real.sqrt_sq hθ₁.le
  have hF := hFar k hj1 hj2
  -- the four terms
  have hVm : Measurable fun x : ProbedPath W np => fun w => probeFrame b E W (k + 1) τ m x w i :=
    measurable_probeFrame_col b E τ m i
  have hf1 : Measurable fun x : ProbedPath W np =>
      ENNReal.ofReal |l2 (fun w => probeFrame b E W (k + 1) τ m x w i) ^ 2 - t| :=
    (((continuous_l2.measurable.comp hVm).pow_const 2).sub_const _).abs.ennreal_ofReal
  have hf4 : Measurable fun x : ProbedPath W np => ENNReal.ofReal
      (l2 ((1 - nearPortProj W) *ᵥ fun w => probeFrame b E W (k + 1) τ m x w i) ^ 2) :=
    ((continuous_l2.measurable.comp (RawTag.measurable_mulVec' measurable_const hVm)).pow_const
      2).ennreal_ofReal
  have hC : Measurable fun y : ProbedPath W np × ℝ =>
      physClosingMapAt b E s h W (k + 1) y.1.1 (phase y.2) :=
    measurable_physClosingMapAt_comp b E s h (k + 1) (measurable_fst.comp measurable_fst)
      (measurable_phase.comp measurable_snd)
  have hf3 : Measurable fun y : ProbedPath W np × ℝ => ENNReal.ofReal
      (l2 ((physClosingMapAt b E s h W (k + 1) y.1.1 (phase y.2))ᴴ *ᵥ
        (fun w => probeFrame b E W (k + 1) τ m y.1 w i) -
          fun w => probeFrame b E W (k + 1) τ m y.1 w i) ^ 2) :=
    ((continuous_l2.measurable.comp ((RawTag.measurable_mulVec'
      (measurable_matrix_conjTranspose' hC) (hVm.comp measurable_fst)).sub
        (hVm.comp measurable_fst))).pow_const 2).ennreal_ofReal
  have I1 : ∫⁻ y, ENNReal.ofReal |l2 (fun w => probeFrame b E W (k + 1) τ m y.1 w i) ^ 2 - t|
      ∂closedLaw b W np ≤ ENNReal.ofReal (m i * (θ₁ + θ₁)) := by
    rw [Birth.lintegral_closedLaw_fst hf1]
    have e := lintegral_newborn_sq_sub_le (W := W) (n := k + 1) b E τ m i hm hlt (dStar b)
    rw [show m i * dStar b = t by rw [htdef, mul_comm], ← hkdef] at e
    refine e.trans ?_
    rw [ENNReal.ofReal_mul hm]
    refine mul_le_mul_right ?_ _
    refine (le_of_eq (lintegral_add_left ?_ _)).trans ?_
    · exact (measurable_const.mul (Real.continuous_sqrt.measurable.comp
        (Complex.measurable_re.comp ((continuous_id.matrix_trace).measurable.comp
          (measurable_matrix_mul' (FullSourceStops.measurable_tagResponse b E (k + 1) k)
            (FullSourceStops.measurable_tagResponse b E (k + 1) k)))))).ennreal_ofReal
    rw [ENNReal.ofReal_add hθ₁.le hθ₁.le]
    exact add_le_add (hSq.trans (ENNReal.ofReal_le_ofReal hsq)) hTr
  have I4 : ∫⁻ y, ENNReal.ofReal
      (l2 ((1 - nearPortProj W) *ᵥ fun w => probeFrame b E W (k + 1) τ m y.1 w i) ^ 2)
      ∂closedLaw b W np ≤ ENNReal.ofReal (m i * θ₁) := by
    rw [Birth.lintegral_closedLaw_fst hf4, lintegral_newborn_far_eq b E τ m i hm hlt,
      ENNReal.ofReal_mul hm]
    exact mul_le_mul_right hF _
  have I3 : ∫⁻ y, ENNReal.ofReal (l2 ((physClosingMapAt b E s h W (k + 1) y.1.1 (phase y.2))ᴴ *ᵥ
        (fun w => probeFrame b E W (k + 1) τ m y.1 w i) -
          fun w => probeFrame b E W (k + 1) τ m y.1 w i) ^ 2) ∂closedLaw b W np ≤
      ENNReal.ofReal (2 * (m i * θ₁)) := by
    refine (lintegral_closed_leak_le hb0 hb hE1 hE2 hW1 s h hh0 hh1 (by omega) τ m i).trans ?_
    rw [ENNReal.ofReal_mul (by norm_num)]
    refine mul_le_mul_right ?_ _
    rw [← Birth.lintegral_closedLaw_fst hf4]
    exact I4
  -- assembly
  refine (lintegral_mono fun y => enorm_gram_err_le b E s h τ m i (Vs W) (k + 1) σ
    (b3Alive b E s h τ m R W k (Vs W)) (t := t) hε y).trans ?_
  refine (le_of_eq (lintegral_four_eq (hf1.comp measurable_fst) hf3 _ _ _)).trans ?_
  refine (add_le_add (add_le_add (add_le_add (mul_le_mul_right I1 _) le_rfl)
    (mul_le_mul_right I3 _)) I4).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : ε * t ≤ θ / 2 := by
    rw [hεdef, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h2 : m i * θ₁ * (2 * (1 + ε) + 2 * (1 + ε⁻¹) + 1) ≤ θ / 2 := by
    have e : m i * θ₁ * (2 * (1 + ε) + 2 * (1 + ε⁻¹) + 1) = θ / 2 * (m i / (m i + 1)) := by
      rw [hθ₁def, hMdef]; field_simp
    rw [e]
    exact mul_le_of_le_one_right (by positivity) ((div_le_one (by positivity)).mpr
      (by linarith))
  nlinarith

end BlockBand.SourceProcess.PhysApprox.B3
