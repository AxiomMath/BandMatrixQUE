module

public import BlockBand.Critical.Herglotz.SineIntensity

/-!
# Intensity of the decorated sine process for tests unbounded in the mark

The setting of the canonical Cauchy series uses `E Σ_j f(x_j, g_j) = ∫∫ f(x, g) dγ(g) dx` for
tests such as `f(x, g) = χ(x) |g|²`, which are compactly supported in the location `x` but
unbounded in the Gaussian mark `g`.

Law: `Ξ` is a decorated sine process (`IsDecoratedSineProcess`, marks
`γ = circularVectorLaw (Fin r)`). Domain: `ℝ × ℂ^r`, mark norm the sup norm of `Fin r → ℂ`
(only used for the cutoff, the result is norm-free). Proof: monotone truncation in the mark,
`f_M(x, g) = f(x, g) ψ_M(g)` with `ψ_M ↑ 1` continuous, `ψ_M = 0` for `‖g‖ ≥ M + 1`, and the
`C_c` intensity `lintegral_coordinate_of_decoratedSine`; both sides pass to the limit `M → ∞`
by monotone convergence. All statements are in `ℝ≥0∞` (`lintegral`), so no integrability is
assumed.

* `markCutoff`, `markTruncation` — the cutoffs.
* `lintegral_ofReal_eq_iSup_markCutoff` — monotone convergence for one measure.
* `lintegral_lintegral_ofReal_of_decoratedSine` — **intensity** for continuous nonnegative tests
  vanishing off `S × ℂ^r`, `S ⊆ ℝ` compact: measurability of `ω ↦ ∫⁻ f dΞ(ω)` and
  `E ∫⁻ f dΞ = ∫⁻ x, ∫⁻ g, f(x, g) dγ dx`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace BlockBand.Critical.Herglotz

open BlockBand.Internal.Contracts.CriticalEntire
open BlockBand.Internal.Contracts.CoareaPalm (circularVectorLaw)

variable {r : ℕ}

/-- Mark cutoff `ψ_M(g) = max(0, min(1, M + 1 - ‖g‖))` on `ℂ^r` (sup norm): continuous,
`0 ≤ ψ_M ≤ 1`, `ψ_M = 1` on `‖g‖ ≤ M`, `ψ_M = 0` on `‖g‖ ≥ M + 1`, nondecreasing in `M`. -/
def markCutoff (M : ℕ) (g : Fin r → ℂ) : ℝ := max 0 (min 1 ((M : ℝ) + 1 - ‖g‖))

theorem markCutoff_nonneg (M : ℕ) (g : Fin r → ℂ) : 0 ≤ markCutoff M g := le_max_left _ _

theorem markCutoff_le_one (M : ℕ) (g : Fin r → ℂ) : markCutoff M g ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem continuous_markCutoff (M : ℕ) : Continuous (markCutoff (r := r) M) := by
  unfold markCutoff
  exact continuous_const.max (continuous_const.min (continuous_const.sub continuous_norm))

theorem markCutoff_mono {M M' : ℕ} (h : M ≤ M') (g : Fin r → ℂ) :
    markCutoff M g ≤ markCutoff M' g := by
  unfold markCutoff
  have : (M : ℝ) ≤ M' := by exact_mod_cast h
  exact max_le_max le_rfl (min_le_min le_rfl (by linarith))

theorem markCutoff_eq_one {M : ℕ} {g : Fin r → ℂ} (h : ‖g‖ ≤ M) : markCutoff M g = 1 := by
  unfold markCutoff
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]

theorem markCutoff_eq_zero {M : ℕ} {g : Fin r → ℂ} (h : (M : ℝ) + 1 ≤ ‖g‖) :
    markCutoff M g = 0 := by
  unfold markCutoff
  rw [max_eq_left]
  exact min_le_of_right_le (by linarith)

theorem eventually_markCutoff_eq_one (g : Fin r → ℂ) :
    ∀ᶠ M : ℕ in atTop, markCutoff M g = 1 :=
  (eventually_ge_atTop ⌈‖g‖⌉₊).mono fun M hM =>
    markCutoff_eq_one ((Nat.le_ceil _).trans (by exact_mod_cast hM))

/-- The truncated test `f_M(x, g) = f(x, g) ψ_M(g) ∈ C_c(ℝ × ℂ^r)`, for `f` continuous and
vanishing off `S × ℂ^r` with `S ⊆ ℝ` compact. -/
def markTruncation (f : ℝ × (Fin r → ℂ) → ℝ) (hf : Continuous f) {S : Set ℝ} (hS : IsCompact S)
    (hfS : ∀ x g, x ∉ S → f (x, g) = 0) (M : ℕ) :
    CompactlySupportedContinuousMap (ℝ × (Fin r → ℂ)) ℝ where
  toFun p := f p * markCutoff M p.2
  continuous_toFun := hf.mul ((continuous_markCutoff M).comp continuous_snd)
  hasCompactSupport' := by
    refine HasCompactSupport.intro
      (hS.prod (isCompact_closedBall (0 : Fin r → ℂ) ((M : ℝ) + 1))) ?_
    rintro ⟨x, g⟩ hp
    rw [Set.mem_prod, not_and_or] at hp
    rcases hp with hx | hg
    · simp [hfS x g hx]
    · rw [Metric.mem_closedBall, dist_zero_right, not_le] at hg
      simp [markCutoff_eq_zero hg.le]

theorem markTruncation_apply (f : ℝ × (Fin r → ℂ) → ℝ) (hf : Continuous f) {S : Set ℝ}
    (hS : IsCompact S) (hfS : ∀ x g, x ∉ S → f (x, g) = 0) (M : ℕ) (p : ℝ × (Fin r → ℂ)) :
    markTruncation f hf hS hfS M p = f p * markCutoff M p.2 := rfl

/-- **Monotone convergence in the mark.** For every measure `μ` on `ℝ × ℂ^r` and every
continuous `f ≥ 0`: `∫⁻ ofReal f dμ = ⨆_M ∫⁻ ofReal (f ψ_M) dμ`. -/
theorem lintegral_ofReal_eq_iSup_markCutoff {f : ℝ × (Fin r → ℂ) → ℝ} (hf : Continuous f)
    (hf0 : ∀ z, 0 ≤ f z) (μ : Measure (ℝ × (Fin r → ℂ))) :
    ∫⁻ p, ENNReal.ofReal (f p) ∂μ =
      ⨆ M : ℕ, ∫⁻ p, ENNReal.ofReal (f p * markCutoff M p.2) ∂μ := by
  have hm (M : ℕ) : Measurable fun p : ℝ × (Fin r → ℂ) =>
      ENNReal.ofReal (f p * markCutoff M p.2) :=
    ENNReal.measurable_ofReal.comp
      (hf.mul ((continuous_markCutoff M).comp continuous_snd)).measurable
  rw [← lintegral_iSup hm (fun M M' h p => ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (markCutoff_mono h _) (hf0 p)))]
  refine lintegral_congr fun p => le_antisymm ?_ (iSup_le fun M => ENNReal.ofReal_le_ofReal ?_)
  · obtain ⟨M, hM⟩ := (eventually_markCutoff_eq_one p.2).exists
    exact le_iSup_of_le M (by rw [hM, mul_one])
  · have := markCutoff_le_one M p.2
    nlinarith [hf0 p, markCutoff_nonneg M p.2]

/-- **Pathwise monotone convergence in the mark** for a locally finite point measure `ξ` on
`ℝ × ℂ^r`: `∫⁻ ofReal f dξ = ⨆_M ofReal (∫ f_M dξ)` with `f_M = markTruncation f … M`, and
`M ↦ ofReal (∫ f_M dξ)` is monotone. -/
theorem lintegral_ofReal_eq_iSup_markTruncation {f : ℝ × (Fin r → ℂ) → ℝ} (hf : Continuous f)
    (hf0 : ∀ z, 0 ≤ f z) {S : Set ℝ} (hS : IsCompact S) (hfS : ∀ x g, x ∉ S → f (x, g) = 0)
    (ξ : VaguePointMeasure (ℝ × (Fin r → ℂ))) :
    (∫⁻ p, ENNReal.ofReal (f p) ∂ξ.measure =
      ⨆ M : ℕ, ENNReal.ofReal (∫ p, markTruncation f hf hS hfS M p ∂ξ.measure)) ∧
    Monotone fun M : ℕ => ENNReal.ofReal (∫ p, markTruncation f hf hS hfS M p ∂ξ.measure) := by
  have hint (M : ℕ) : Integrable (fun p => markTruncation f hf hS hfS M p) ξ.measure :=
    (markTruncation f hf hS hfS M).continuous.integrable_of_hasCompactSupport
      (markTruncation f hf hS hfS M).hasCompactSupport
  have h0 (M : ℕ) (p : ℝ × (Fin r → ℂ)) : 0 ≤ markTruncation f hf hS hfS M p :=
    mul_nonneg (hf0 p) (markCutoff_nonneg M p.2)
  refine ⟨?_, fun M M' hMM' => ENNReal.ofReal_le_ofReal (integral_mono (hint M) (hint M')
    fun p => mul_le_mul_of_nonneg_left (markCutoff_mono hMM' _) (hf0 p))⟩
  rw [lintegral_ofReal_eq_iSup_markCutoff hf hf0]
  refine iSup_congr fun M => ?_
  exact (ofReal_integral_eq_lintegral_ofReal (hint M) (Eventually.of_forall (h0 M))).symm

/-- `ofReal (∫ x, ∫ g, F(x, g) dγ dx) = ∫⁻ x, ∫⁻ g, ofReal F(x, g) dγ dx` for nonnegative
`F ∈ C_c(ℝ × ℂ^r)` (Lebesgue measure in `x`, `γ = circularVectorLaw (Fin r)` in `g`). -/
theorem ofReal_integral_integral_eq_lintegral
    (F : CompactlySupportedContinuousMap (ℝ × (Fin r → ℂ)) ℝ) (hF : ∀ z, 0 ≤ F z) :
    ENNReal.ofReal (∫ x, ∫ g, F (x, g) ∂circularVectorLaw (Fin r)) =
      ∫⁻ x, ∫⁻ g, ENNReal.ofReal (F (x, g)) ∂circularVectorLaw (Fin r) := by
  have hi : Integrable (fun p => F p) ((volume : Measure ℝ).prod (circularVectorLaw (Fin r))) :=
    F.continuous.integrable_of_hasCompactSupport F.hasCompactSupport
  rw [← integral_prod _ hi, ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hF),
    lintegral_prod (fun z => ENNReal.ofReal (F z))
      (ENNReal.measurable_ofReal.comp F.continuous.measurable).aemeasurable]

/-- **Intensity of the decorated sine process, tests unbounded in the mark.** Law: `Ξ` is a
decorated sine process on `(Ω, P)` (`IsDecoratedSineProcess`; marks
`γ = circularVectorLaw (Fin r)`). For every continuous `f ≥ 0` on `ℝ × ℂ^r` vanishing for
`x ∉ S`, `S ⊆ ℝ` compact (no bound or decay in the mark `g`): `ω ↦ ∫⁻ ofReal f dΞ(ω)` is
measurable and `∫⁻ ω, ∫⁻ ofReal f dΞ(ω) dP = ∫⁻ x, ∫⁻ g, ofReal f(x, g) dγ(g) dx` (Lebesgue in
`x`), in `ℝ≥0∞`. Uses only the `C_c` intensity `lintegral_coordinate_of_decoratedSine` and
monotone convergence in the mark cutoff `M → ∞`. -/
theorem lintegral_lintegral_ofReal_of_decoratedSine {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Ξ : Ω → VaguePointMeasure (ℝ × (Fin r → ℂ))}
    (h : IsDecoratedSineProcess r P Ξ) {f : ℝ × (Fin r → ℂ) → ℝ} (hf : Continuous f)
    (hf0 : ∀ z, 0 ≤ f z) {S : Set ℝ} (hS : IsCompact S) (hfS : ∀ x g, x ∉ S → f (x, g) = 0) :
    Measurable (fun ω => ∫⁻ p, ENNReal.ofReal (f p) ∂(Ξ ω).measure) ∧
      ∫⁻ ω, ∫⁻ p, ENNReal.ofReal (f p) ∂(Ξ ω).measure ∂P =
        ∫⁻ x, ∫⁻ g, ENNReal.ofReal (f (x, g)) ∂circularVectorLaw (Fin r) := by
  set fM := markTruncation f hf hS hfS with hfM
  have hfM0 (M : ℕ) (p : ℝ × (Fin r → ℂ)) : 0 ≤ fM M p :=
    mul_nonneg (hf0 p) (markCutoff_nonneg M p.2)
  have hint (M : ℕ) (μ : Measure (ℝ × (Fin r → ℂ))) [IsFiniteMeasureOnCompacts μ] :
      Integrable (fun p => fM M p) μ :=
    (fM M).continuous.integrable_of_hasCompactSupport (fM M).hasCompactSupport
  have hpath (ω : Ω) (M : ℕ) : ∫⁻ p, ENNReal.ofReal (f p * markCutoff M p.2) ∂(Ξ ω).measure =
      ENNReal.ofReal (∫ p, fM M p ∂(Ξ ω).measure) :=
    (ofReal_integral_eq_lintegral_ofReal (hint M _) (Eventually.of_forall (hfM0 M))).symm
  have hcoord (M : ℕ) : Measurable (fun ω => ∫ p, fM M p ∂(Ξ ω).measure) :=
    (BlockBand.Model.Construction.continuous_vaguePointMeasure_coordinate (fM M)).measurable.comp
      h.measurable
  have hrep (ω : Ω) : ∫⁻ p, ENNReal.ofReal (f p) ∂(Ξ ω).measure =
      ⨆ M : ℕ, ENNReal.ofReal (∫ p, fM M p ∂(Ξ ω).measure) := by
    rw [lintegral_ofReal_eq_iSup_markCutoff hf hf0]
    simp_rw [hpath]
  have hmono : Monotone fun (M : ℕ) (ω : Ω) => ENNReal.ofReal (∫ p, fM M p ∂(Ξ ω).measure) := by
    intro M M' hMM' ω
    exact ENNReal.ofReal_le_ofReal (integral_mono (hint M _) (hint M' _) fun p =>
      mul_le_mul_of_nonneg_left (markCutoff_mono hMM' _) (hf0 p))
  have hcm (M : ℕ) : Measurable fun ω => ENNReal.ofReal (∫ p, fM M p ∂(Ξ ω).measure) :=
    ENNReal.measurable_ofReal.comp (hcoord M)
  have hmeas : Measurable (fun ω => ∫⁻ p, ENNReal.ofReal (f p) ∂(Ξ ω).measure) := by
    simp_rw [hrep]
    exact Measurable.iSup hcm
  refine ⟨hmeas, ?_⟩
  simp_rw [hrep]
  rw [lintegral_iSup hcm hmono]
  simp_rw [lintegral_coordinate_of_decoratedSine h (fM _) (hfM0 _),
    ofReal_integral_integral_eq_lintegral (fM _) (hfM0 _), hfM, markTruncation_apply]
  -- monotone convergence in `g`, then in `x`
  have hg (x : ℝ) : ∫⁻ g, ENNReal.ofReal (f (x, g)) ∂circularVectorLaw (Fin r) =
      ⨆ M : ℕ, ∫⁻ g, ENNReal.ofReal (f (x, g) * markCutoff M g) ∂circularVectorLaw (Fin r) := by
    have hm (M : ℕ) : Measurable fun g : Fin r → ℂ =>
        ENNReal.ofReal (f (x, g) * markCutoff M g) :=
      ENNReal.measurable_ofReal.comp
        ((hf.comp (Continuous.prodMk_right x)).mul (continuous_markCutoff M)).measurable
    rw [← lintegral_iSup hm
      (fun M M' hMM' g => ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (markCutoff_mono hMM' _) (hf0 _)))]
    refine lintegral_congr fun g => le_antisymm ?_
      (iSup_le fun M => ENNReal.ofReal_le_ofReal ?_)
    · obtain ⟨M, hM⟩ := (eventually_markCutoff_eq_one g).exists
      exact le_iSup_of_le M (by rw [hM, mul_one])
    · have := markCutoff_le_one M g
      nlinarith [hf0 (x, g), markCutoff_nonneg M g]
  simp_rw [hg]
  have hjm (M : ℕ) : Measurable fun p : ℝ × (Fin r → ℂ) =>
      ENNReal.ofReal (f p * markCutoff M p.2) :=
    ENNReal.measurable_ofReal.comp
      (hf.mul ((continuous_markCutoff M).comp continuous_snd)).measurable
  rw [lintegral_iSup (fun M => (hjm M).lintegral_prod_right')]
  intro M M' hMM' x
  exact lintegral_mono fun g => ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left (markCutoff_mono hMM' _) (hf0 _))

end BlockBand.Critical.Herglotz
