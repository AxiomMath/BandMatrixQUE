module

public import BlockBand.SourceProcess.PhysApprox.B3BirthClose
public import BlockBand.SourceProcess.PhysApprox.B3BirthGauss
public import BlockBand.SourceProcess.ComplexSourceLaw.Marginal

/-!
# Gaussian concentration of the fresh `𝒦` diagonal

At length `n`, the tag `i` born at `k = ⌊Wτ_i⌋ < n` sits on the block at position `p = n−1−k`,
and its unclosed fresh diagonal is a circular quadratic form of its own probe `g_i`:
`𝒦_ii = (m_i/W) Q_{B}(g_i)` with `B = G₁₁[(p,·),(p,·)]` (`birthBlock`; `kc_diag_eq_quad`). With
`Birth.lintegral_quad_sub_le` and Tonelli over the probe:

* **`lintegral_kc_diag_sub_le`**: `E|𝒦_ii − (m_i/W) Tr B| ≤ m_i E[W⁻¹ (Re Tr BBᴴ)^{1/2}]`;
* **`complexBirthKFresh_of_trace`**: `ComplexBirthKFresh` follows from the path-only estimate
  `ComplexBirthKFreshTrace` (the normalized trace `W⁻¹ Tr B` of the newest block at its birth
  length tends to `a`, and its normalized Hilbert–Schmidt norm `W⁻¹‖B‖_HS` tends to `0`, both in
  `L¹`, uniformly over the birth steps in `[n_s, ⌊WT⌋)`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ClosedPath
open scoped NNReal ENNReal ComplexConjugate

/-- The diagonal block of `G₁₁` at the block position `p` of the path of length `n`. -/
def birthBlock (b E : ℝ) (W n : ℕ) (p : Fin n) (ω : GrowthPath W) : Matrix (Fin W) (Fin W) ℂ :=
  Matrix.of fun a a' => (fullInverse b E W n ω).toBlocks₁₁ (p, a) (p, a')

namespace Birth

variable {W n : ℕ}

/-- A tag form of one tag vector with itself is a circular quadratic form of its probe. -/
theorem tagForm_tagVector_self (G : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ) (k : Fin n)
    {μ : ℝ} (hμ : 0 ≤ μ) (g : Fin W → ℂ) :
    tagForm G (tagVector W n k μ g) (tagVector W n k μ g) =
      ((μ / W : ℝ) : ℂ) * Counting.complexQuadraticForm (Matrix.of fun a a' => G (k, a) (k, a'))
        g := by
  have hc : ((Real.sqrt (μ / W) : ℝ) : ℂ) * ((Real.sqrt (μ / W) : ℝ) : ℂ) = ((μ / W : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (div_nonneg hμ (Nat.cast_nonneg W))]
  simp only [tagForm, tagVector, dotProduct, mulVec, Fintype.sum_prod_type, Pi.star_apply]
  rw [Finset.sum_eq_single k (fun x _ hx => by simp [hx]) (by simp)]
  simp only [Counting.complexQuadraticForm, Finset.mul_sum, Matrix.of_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single k (fun x _ hx => by simp [hx]) (by simp)]
  refine Finset.sum_congr rfl fun a' _ => ?_
  simp only [↓reduceIte, star_mul', Complex.star_def, Complex.conj_ofReal]
  linear_combination (G (k, a) (k, a') * (conj (g a) * g a')) * hc

/-- **The fresh `𝒦` diagonal is a circular quadratic form**: `𝒦_ii = (m_i/W) Q_B(g_i)`. -/
theorem kc_diag_eq_quad (b E : ℝ) {np : ℕ} (τ m : Fin np → ℝ) (i : Fin np) (hm : 0 ≤ m i)
    (hi : ⌊(W : ℝ) * τ i⌋₊ < n) (x : ProbedPath W np) :
    complexSourceK b E W n τ m x i i = ((m i / W : ℝ) : ℂ) *
      Counting.complexQuadraticForm
        (birthBlock b E W n ⟨n - 1 - ⌊(W : ℝ) * τ i⌋₊, by omega⟩ x.1) (x.2 i) := by
  rw [complexSourceK_apply, probeColumn_eq_tagVector n τ m _ i hi, tagForm_tagVector_self _ _ hm]
  rfl

theorem measurable_birthBlock (b E : ℝ) (p : Fin n) :
    Measurable (birthBlock b E W n p) :=
  Measurable.of_eval_matrix _ fun a a' => by
    simp only [birthBlock, Matrix.of_apply]
    exact (measurable_interior b E n).eval_matrix

theorem measurable_quad_birthBlock (b E : ℝ) (p : Fin n) :
    Measurable fun z : GrowthPath W × (Fin W → ℂ) =>
      Counting.complexQuadraticForm (birthBlock b E W n p z.1) z.2 := by
  unfold Counting.complexQuadraticForm
  refine Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun a' _ => ?_
  exact (((measurable_birthBlock b E p).eval_matrix).comp measurable_fst).mul
    ((Complex.continuous_conj.measurable.comp ((measurable_pi_apply a).comp measurable_snd)).mul
      ((measurable_pi_apply a').comp measurable_snd))

theorem measurable_trace_birthBlock (b E : ℝ) (p : Fin n) :
    Measurable fun ω : GrowthPath W => (birthBlock b E W n p ω).trace := by
  unfold Matrix.trace Matrix.diag
  exact Finset.measurable_sum _ fun a _ => (measurable_birthBlock b E p).eval_matrix

/-- **Gaussian concentration of the fresh `𝒦` diagonal over its probe**:
`E|𝒦_ii − (m_i/W) Tr B| ≤ m_i E[W⁻¹ (Re Tr BBᴴ)^{1/2}]`. -/
theorem lintegral_kc_diag_sub_le (b E : ℝ) {np : ℕ} (τ m : Fin np → ℝ) (i : Fin np)
    (hm : 0 ≤ m i) (hi : ⌊(W : ℝ) * τ i⌋₊ < n) :
    ∫⁻ x, ‖complexSourceK b E W n τ m x i i -
        ((m i / W : ℝ) : ℂ) * (birthBlock b E W n ⟨n - 1 - ⌊(W : ℝ) * τ i⌋₊, by omega⟩ x.1).trace‖ₑ
      ∂probedPathLaw W np b ≤
    ENNReal.ofReal (m i) * ∫⁻ ω, ENNReal.ofReal ((W : ℝ)⁻¹ *
      Real.sqrt ((birthBlock b E W n ⟨n - 1 - ⌊(W : ℝ) * τ i⌋₊, by omega⟩ ω) *
        (birthBlock b E W n ⟨n - 1 - ⌊(W : ℝ) * τ i⌋₊, by omega⟩ ω)ᴴ).trace.re)
      ∂growthPathLaw W b := by
  set p : Fin n := ⟨n - 1 - ⌊(W : ℝ) * τ i⌋₊, by omega⟩
  set F : GrowthPath W × (Fin W → ℂ) → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (m i / W) * ‖Counting.complexQuadraticForm (birthBlock b E W n p z.1) z.2 -
      (birthBlock b E W n p z.1).trace‖ₑ with hFdef
  have hF : Measurable F :=
    measurable_const.mul ((measurable_quad_birthBlock b E p).sub
      ((measurable_trace_birthBlock b E p).comp measurable_fst)).enorm
  have hpt : ∀ x : ProbedPath W np, ‖complexSourceK b E W n τ m x i i -
      ((m i / W : ℝ) : ℂ) * (birthBlock b E W n p x.1).trace‖ₑ = F (x.1, x.2 i) := by
    intro x
    rw [kc_diag_eq_quad b E τ m i hm hi x, ← mul_sub, enorm_mul]
    simp only [hFdef]
    congr 1
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  simp_rw [hpt]
  rw [probedPathLaw, lintegral_prod (fun x : ProbedPath W np => F (x.1, x.2 i))
    (hF.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))).aemeasurable,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun ω => ?_
  have hg : Measurable fun g : Fin W → ℂ => F (ω, g) := hF.comp measurable_prodMk_left
  have e := (measurePreserving_eval (fun _ : Fin np => circularVectorLaw (Fin W)) i).lintegral_comp
    hg
  refine (le_of_eq e).trans ?_
  simp only [hFdef]
  rw [lintegral_const_mul _ (((measurable_quad _).sub_const _).enorm)]
  calc ENNReal.ofReal (m i / W) * ∫⁻ g, ‖Counting.complexQuadraticForm (birthBlock b E W n p ω) g -
        (birthBlock b E W n p ω).trace‖ₑ ∂circularVectorLaw (Fin W)
      ≤ ENNReal.ofReal (m i / W) * ENNReal.ofReal (Real.sqrt ((birthBlock b E W n p ω) *
          (birthBlock b E W n p ω)ᴴ).trace.re) := by
        gcongr
        exact lintegral_quad_sub_le _
    _ = _ := by
        rw [div_eq_mul_inv, ENNReal.ofReal_mul hm, mul_assoc,
          ← ENNReal.ofReal_mul (inv_nonneg.mpr (Nat.cast_nonneg W))]

/-- A function of the path integrates over the probed law as over the path law. -/
theorem lintegral_probedPathLaw_fst {np : ℕ} {b : ℝ} {f : GrowthPath W → ℝ≥0∞}
    (hf : Measurable f) : ∫⁻ x, f x.1 ∂probedPathLaw W np b = ∫⁻ ω, f ω ∂growthPathLaw W b := by
  rw [probedPathLaw, lintegral_prod (fun x : ProbedPath W np => f x.1)
    (hf.comp measurable_fst).aemeasurable]
  simp

/-- `m_i·u ≤ θ/2` for `u ≤ θ/(2(m_i+1))`. -/
theorem mul_le_half {μ θ u : ℝ} (hμ : 0 ≤ μ) (hθ : 0 < θ) (hu : u ≤ θ / (2 * (μ + 1))) :
    μ * u ≤ θ / 2 := by
  calc μ * u ≤ μ * (θ / (2 * (μ + 1))) := mul_le_mul_of_nonneg_left hu hμ
    _ = θ / 2 * (μ / (μ + 1)) := by
        have h1 : μ + 1 ≠ 0 := by positivity
        field_simp
    _ ≤ θ / 2 * 1 := mul_le_mul_of_nonneg_left ((div_le_one (by positivity)).mpr (by linarith))
        (by positivity)
    _ = θ / 2 := mul_one _

end Birth

/-!
## The path-only estimate and the reduction
-/

/-- **Path-only estimate (the fresh normalized trace and Hilbert–Schmidt norm)**: at its birth
length `j + 1` (`n_s ≤ j < ⌊WT⌋`), the newest block `B = G₁₁[(0,·),(0,·)] = R + RΔR`
(`RawTag.RawBirth`) has `W⁻¹ Tr B → a` and `W⁻¹ (Re Tr BBᴴ)^{1/2} → 0` in `L¹(growthPathLaw)`,
uniformly in `j`. -/
def ComplexBirthKFreshTrace : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s : ℝ), ComplexSourceLawDomain b E τ m T → 0 < s →
    (∀ j, s < τ j) → ∀ θ : ℝ, 0 < θ → ∀ᶠ W : ℕ in atTop,
      ∀ j, closeLen s W ≤ j → j < ⌊(W : ℝ) * T⌋₊ →
        ∫⁻ ω, ‖(W : ℂ)⁻¹ * (birthBlock b E W (j + 1) 0 ω).trace - matchedA E‖ₑ
            ∂growthPathLaw W b ≤ ENNReal.ofReal θ ∧
        ∫⁻ ω, ENNReal.ofReal ((W : ℝ)⁻¹ * Real.sqrt ((birthBlock b E W (j + 1) 0 ω) *
            (birthBlock b E W (j + 1) 0 ω)ᴴ).trace.re) ∂growthPathLaw W b ≤ ENNReal.ofReal θ

/-- **The unclosed fresh `𝒦` diagonal from the path-only estimate.** -/
theorem complexBirthKFresh_of_trace (hT : ComplexBirthKFreshTrace) : ComplexBirthKFresh := by
  intro b E np τ m T s hD hs hsτ θ hθ i
  have hm : 0 ≤ m i := hD.2.2.2.2.2.2.1 i
  have hθ' : 0 < θ / (2 * (m i + 1)) := div_pos hθ (by positivity)
  filter_upwards [hT b E np τ m T s hD hs hsτ _ hθ'] with W hW
  intro j hj1 hj2 hi
  obtain ⟨h1, h2⟩ := hW j hj1 hj2
  have hlt : ⌊(W : ℝ) * τ i⌋₊ < j + 1 := by omega
  have hp : (⟨j + 1 - 1 - ⌊(W : ℝ) * τ i⌋₊, by omega⟩ : Fin (j + 1)) = 0 := by
    ext; simp only [Fin.val_zero]; omega
  have hA := Birth.lintegral_kc_diag_sub_le (W := W) (n := j + 1) b E τ m i hm hlt
  rw [hp] at hA
  set B := birthBlock b E W (j + 1) 0
  have hmB : Measurable fun x : ProbedPath W np => ‖complexSourceK b E W (j + 1) τ m x i i -
      ((m i / W : ℝ) : ℂ) * (B x.1).trace‖ₑ :=
    ((measurable_complexSourceK b E W (j + 1) τ m).eval_matrix.sub
      (measurable_const.mul ((Birth.measurable_trace_birthBlock b E 0).comp measurable_fst))).enorm
  have hmT : Measurable fun ω : GrowthPath W => ‖(W : ℂ)⁻¹ * (B ω).trace - matchedA E‖ₑ :=
    ((measurable_const.mul (Birth.measurable_trace_birthBlock b E 0)).sub_const _).enorm
  have hsecond : ∫⁻ x, ‖((m i / W : ℝ) : ℂ) * (B x.1).trace - matchedA E * (m i : ℂ)‖ₑ
      ∂probedPathLaw W np b =
        ENNReal.ofReal (m i) * ∫⁻ ω, ‖(W : ℂ)⁻¹ * (B ω).trace - matchedA E‖ₑ
          ∂growthPathLaw W b := by
    have hpt : ∀ x : ProbedPath W np,
        ‖((m i / W : ℝ) : ℂ) * (B x.1).trace - matchedA E * (m i : ℂ)‖ₑ =
          ENNReal.ofReal (m i) * ‖(W : ℂ)⁻¹ * (B x.1).trace - matchedA E‖ₑ := by
      intro x
      rw [show ((m i / W : ℝ) : ℂ) * (B x.1).trace - matchedA E * (m i : ℂ) =
          (m i : ℂ) * ((W : ℂ)⁻¹ * (B x.1).trace - matchedA E) by push_cast; ring, enorm_mul,
        ← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hm]
    simp_rw [hpt]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    exact Birth.lintegral_probedPathLaw_fst hmT
  calc ∫⁻ x, ‖complexSourceK b E W (j + 1) τ m x i i - matchedA E * (m i : ℂ)‖ₑ
        ∂probedPathLaw W np b
      ≤ ∫⁻ x, (‖complexSourceK b E W (j + 1) τ m x i i - ((m i / W : ℝ) : ℂ) * (B x.1).trace‖ₑ +
          ‖((m i / W : ℝ) : ℂ) * (B x.1).trace - matchedA E * (m i : ℂ)‖ₑ)
          ∂probedPathLaw W np b := by
        refine lintegral_mono fun x => ?_
        rw [show complexSourceK b E W (j + 1) τ m x i i - matchedA E * (m i : ℂ) =
          (complexSourceK b E W (j + 1) τ m x i i - ((m i / W : ℝ) : ℂ) * (B x.1).trace) +
            (((m i / W : ℝ) : ℂ) * (B x.1).trace - matchedA E * (m i : ℂ)) by ring]
        exact enorm_add_le _ _
    _ = ∫⁻ x, ‖complexSourceK b E W (j + 1) τ m x i i - ((m i / W : ℝ) : ℂ) * (B x.1).trace‖ₑ
          ∂probedPathLaw W np b +
        ∫⁻ x, ‖((m i / W : ℝ) : ℂ) * (B x.1).trace - matchedA E * (m i : ℂ)‖ₑ
          ∂probedPathLaw W np b := lintegral_add_left hmB _
    _ ≤ ENNReal.ofReal (m i) * ENNReal.ofReal (θ / (2 * (m i + 1))) +
        ENNReal.ofReal (m i) * ENNReal.ofReal (θ / (2 * (m i + 1))) := by
        rw [hsecond]
        exact add_le_add (hA.trans (by gcongr)) (by gcongr)
    _ ≤ ENNReal.ofReal (θ / 2) + ENNReal.ofReal (θ / 2) := by
        rw [← ENNReal.ofReal_mul hm]
        gcongr <;> exact Birth.mul_le_half hm hθ le_rfl
    _ = ENNReal.ofReal θ := Birth.ofReal_half_add_half hθ

end BlockBand.SourceProcess.PhysApprox.B3
