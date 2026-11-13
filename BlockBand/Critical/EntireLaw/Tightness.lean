module

public import BlockBand.Critical.EntireLaw.Montel
public import BlockBand.Critical.EntireLaw.RingProbe
public import BlockBand.Critical.EntireLaw.Statements

/-!
# The entire law: tightness of `D_W` from one-probe tightness

* `isTightMeasureSet_finiteEntireLaw_of_probe`: for any family of finite realizations (any
  index type and parameters), any `E` and nonnegative `q`, if the one-probe variables
  `X_a = ζ_a^* R ζ_a` (`fullRingProbeLaw` with `J = 1`, profile `Q_a` of the full family
  `1, q_1, …, q_k`) are tight uniformly in the family, the laws of `D_W` on
  `EntireFunction (k+1)` are tight;
* `entireTightness_of_probeTightness`: `EntireTightness`, from that one-probe tightness along
  every critical sequence and every choice of realizations.

Chain: one-probe tightness ⇒ tightness of `Tr A_a` and `‖A_0‖_HS`
(`ProbeTightness`, characteristic-function form of the converse probe-tightness bound) ⇒ uniform
bounds in probability of `sup_{‖z‖ ≤ r} |D_W(z)|` (`norm_finiteEntireDeterminant_le`)
⇒ tightness (`isTightMeasureSet_of_forall_exists_bound`).

One-probe tightness itself requires the closing steps. By the lemmas above, it is equivalent to
tightness of `W⁻² Tr(R Q_a)` and `W⁻² ‖R‖_HS`, i.e. to control of the resolvent at the
eigenvalue-spacing scale. Tightness of `Re W⁻² Tr(R Q_a)` needs principal-value cancellation,
whereas the crude bound through `Tr |R|` is of order `N log N`. This control comes from the
closed-source limit and collar source removal: `tendsto_finiteMoment_value` gives the
pointwise convergence of `E exp(∓ i t X_a)`, `t ≥ 0`, and Mathlib's
`isTightMeasureSet_of_tendsto_charFun` (Lévy) then gives tightness once the limit is continuous at
`t = 0`. That continuity needs (i) the scaling `κ_{tQ} = (t•)_# κ_Q` of the global probe law (finite
identity `𝒦_W(tQ) = t 𝒦_W(Q)` and uniqueness of the critical limit), so that
`𝒯^{(tQ)} = t 𝒯^{(Q)}`, and (ii) `Im 𝒯_00 = 0` a.s. (`𝖢_1(0)` real a.s.) for dominated convergence.
Both are proved in `ProbeScaling`, and `ClosingTightness` assembles the argument
(`probeTightness_of_closing`, `entireTightness_of_closing`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.EntireLaw

open MeasureTheory Filter Topology Matrix Set Metric
open BlockBand.Critical.Entire
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.CriticalEntire
open scoped ENNReal NNReal

/-- **Tightness of `D_W` from one-probe tightness**. For any family of finite
realizations (any index type, any parameters), any real `E` and nonnegative profiles `q`: if for
every profile `a` of the full family `1, q_1, …, q_k` the one-probe variables
`X_a = ζ_a^* R ζ_a` (one standard circular probe of covariance `Q_a/W²`, `fullRingProbeLaw` with
`J = 1`) are tight uniformly in the family, then the laws of `D_W` on `EntireFunction (k+1)`
are tight. -/
theorem isTightMeasureSet_finiteEntireLaw_of_probe {ιJ : Type*} {p : ιJ → Parameters}
    (R : ∀ j, FiniteRealization (p j)) (E : ℝ) {k : ℕ} {q : Fin k → C(Torus, ℝ)}
    (hq : IsProfileFamily q)
    (hX : ∀ a : Fin (k + 1), ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ j,
      (fullRingProbeLaw (R j).model 1).real
        {x | M < ‖ringSourceMatrix (p j) E (fun _ : Fin 1 => fullProfile q a) x.1 x.2 0 0‖} ≤ ε) :
    IsTightMeasureSet (Set.range fun j =>
      (finiteEntireLaw (R j) E (fullProfile q) : Measure (EntireFunction (k + 1)))) := by
  set Q := fullProfile q
  have hQ : ∀ a t, 0 ≤ Q a t := fullProfile_nonneg hq
  apply isTightMeasureSet_of_forall_exists_bound
  intro r δ hδ
  obtain ⟨η, -, hηpos, hηδ⟩ := ENNReal.lt_iff_exists_real_btwn.mp hδ
  have hη : 0 < η := ENNReal.ofReal_pos.mp hηpos
  set η₁ : ℝ := η / ((k + 1 : ℕ) + 1)
  have hη₁ : 0 < η₁ := by positivity
  choose M hM using fun a => hX a (η₁ / 512) (by positivity)
  set M' : Fin (k + 1) → ℝ := fun a => max (M a) 0
  have hM'0 : ∀ a, 0 ≤ M' a := fun a => le_max_right _ _
  have hM' : ∀ a j, ((R j).model.law.toMeasure.prod (circularVectorLaw (p j).Site)).real
      {x | M' a < ‖probeForm (oneProbeMatrix (p j) E Q a x.1) x.2‖} ≤ η₁ / 512 := by
    intro a j
    have h := hM a j
    rw [measureReal_ringSource_eq] at h
    refine (measureReal_mono fun x (hx : M' a < _) => ?_).trans h
    exact lt_of_le_of_lt (le_max_left _ _) hx
  set Lv : Fin (k + 1) → ℝ := fun a => probeLevelL η₁ (M' a)
  set K0 : ℝ := probeLevelK η₁ (M' 0)
  set C : ℝ := Real.exp (∑ a, r * Lv a + 2⁻¹ * (∑ a, r * ‖Q a‖) ^ 2 * K0 ^ 2)
  refine ⟨C, ?_⟩
  rintro μ ⟨j, rfl⟩
  set law : Measure (p j).SiteMatrix := (R j).model.law.toMeasure
  have hherm : ∀ᵐ H ∂law, H.IsHermitian := (R j).model.isPhysical.1
  have hAm : ∀ a, Measurable (oneProbeMatrix (p j) E Q a) := fun a =>
    measurable_oneProbeMatrix E Q a
  have hAh : ∀ a, ∀ᵐ H ∂law, (oneProbeMatrix (p j) E Q a H).IsHermitian := fun a =>
    hherm.mono fun H hH => isHermitian_oneProbeMatrix E Q a hH
  have htr : ∀ a, law.real {H | Lv a < |(oneProbeMatrix (p j) E Q a H).trace.re|} ≤ η₁ :=
    fun a => probe_trace_tail law (hAm a) (hAh a) hη₁ (hM'0 a) (hM' a j)
  have hhs : law.real {H | K0 ^ 2 < hsSq (oneProbeMatrix (p j) E Q 0 H)} ≤ η₁ :=
    probe_hsSq_tail law (hAm 0) (hAh 0) hη₁ (hM'0 0) ((hM' 0 j).trans (by linarith))
  have hnull : law.real {H : (p j).SiteMatrix | ¬ H.IsHermitian} = 0 := by
    have h0 : law {H : (p j).SiteMatrix | ¬ H.IsHermitian} = 0 := ae_iff.mp hherm
    simp [Measure.real, h0]
  set bad := {F : EntireFunction (k + 1) | ∃ z ∈ closedBall (0 : Fin (k + 1) → ℂ) r, C < ‖F z‖}
  have hbad : IsOpen bad := by
    have : bad = ⋃ z ∈ closedBall (0 : Fin (k + 1) → ℂ) r,
        {F : EntireFunction (k + 1) | C < ‖F z‖} := by
      ext F; simp [bad]
    rw [this]
    exact isOpen_biUnion fun z _ =>
      isOpen_lt continuous_const (EntireFunction.continuous_eval_const z).norm
  have hD := BlockBand.Critical.JointRecovery.measurable_finiteEntireDeterminant (p := p j) E Q
  set U := (⋃ a, {H : (p j).SiteMatrix | Lv a < |(oneProbeMatrix (p j) E Q a H).trace.re|}) ∪
    {H | K0 ^ 2 < hsSq (oneProbeMatrix (p j) E Q 0 H)} ∪ {H | ¬ H.IsHermitian}
  have hsub : finiteEntireDeterminant (p j) E Q ⁻¹' bad ⊆ U := by
    intro H hH
    by_contra hcon
    simp only [U, mem_union, mem_iUnion, mem_ofPred_eq, not_or, not_exists, not_lt,
      not_not] at hcon
    obtain ⟨⟨htrH, hhsH⟩, hHerm⟩ := hcon
    obtain ⟨z, hz, hlt⟩ := hH
    have hzr : ∀ a, ‖z a‖ ≤ r := fun a =>
      (norm_le_pi_norm z a).trans (mem_closedBall_zero_iff.mp hz)
    have hT : ∀ a, ‖profileTrace (p j) E Q H a‖ ≤ Lv a := by
      intro a
      rw [profileTrace_eq_trace E hQ H a,
        trace_eq_ofReal_re (isHermitian_oneProbeMatrix E Q a hHerm), Complex.norm_real,
        Real.norm_eq_abs]
      exact htrH a
    have hS : scaledResolventHS (p j) E H ≤ K0 ^ 2 := by
      rw [scaledResolventHS_eq_hsSq E q H]; exact hhsH
    have hsum1 : ∑ a, ‖z a‖ * ‖profileTrace (p j) E Q H a‖ ≤ ∑ a, r * Lv a :=
      Finset.sum_le_sum fun a _ => mul_le_mul (hzr a) (hT a) (norm_nonneg _)
        ((norm_nonneg _).trans (hzr a))
    have hsum2 : ∑ a, ‖z a‖ * ‖Q a‖ ≤ ∑ a, r * ‖Q a‖ :=
      Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_right (hzr a) (norm_nonneg _)
    have hsum2' : (∑ a, ‖z a‖ * ‖Q a‖) ^ 2 ≤ (∑ a, r * ‖Q a‖) ^ 2 :=
      pow_le_pow_left₀ (Finset.sum_nonneg fun a _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
        hsum2 2
    have hHS0 : 0 ≤ scaledResolventHS (p j) E H :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hexp : ‖finiteEntireDeterminant (p j) E Q H z‖ ≤ C := by
      refine (norm_finiteEntireDeterminant_le E Q H z).trans (Real.exp_le_exp.mpr ?_)
      have : 2⁻¹ * (∑ a, ‖z a‖ * ‖Q a‖) ^ 2 * scaledResolventHS (p j) E H ≤
          2⁻¹ * (∑ a, r * ‖Q a‖) ^ 2 * K0 ^ 2 := by
        have h1 := mul_le_mul hsum2' hS hHS0 (sq_nonneg _)
        nlinarith
      linarith
    exact absurd hlt (not_lt.mpr hexp)
  have hU : law.real U ≤ η := by
    have h1 := measureReal_union_le (μ := law)
      ((⋃ a, {H : (p j).SiteMatrix | Lv a < |(oneProbeMatrix (p j) E Q a H).trace.re|}) ∪
        {H | K0 ^ 2 < hsSq (oneProbeMatrix (p j) E Q 0 H)}) {H | ¬ H.IsHermitian}
    have h2 := measureReal_union_le (μ := law)
      (⋃ a, {H : (p j).SiteMatrix | Lv a < |(oneProbeMatrix (p j) E Q a H).trace.re|})
      {H | K0 ^ 2 < hsSq (oneProbeMatrix (p j) E Q 0 H)}
    have h3 := measureReal_iUnion_fintype_le (μ := law)
      fun a => {H : (p j).SiteMatrix | Lv a < |(oneProbeMatrix (p j) E Q a H).trace.re|}
    have h4 : ∑ a, law.real {H : (p j).SiteMatrix |
        Lv a < |(oneProbeMatrix (p j) E Q a H).trace.re|} ≤ ∑ _a : Fin (k + 1), η₁ :=
      Finset.sum_le_sum fun a _ => htr a
    have h5 : ∑ _a : Fin (k + 1), η₁ = ((k + 1 : ℕ) : ℝ) * η₁ := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    have h6 : ((k + 1 : ℕ) : ℝ) * η₁ + η₁ = η := by
      simp only [η₁]
      field_simp
    simp only [U]
    linarith
  show (finiteEntireLaw (R j) E Q : Measure (EntireFunction (k + 1))) bad ≤ δ
  unfold finiteEntireLaw
  rw [ProbabilityMeasure.toMeasure_map, Measure.map_apply hD hbad.measurableSet]
  calc law (finiteEntireDeterminant (p j) E Q ⁻¹' bad) ≤ law U := measure_mono hsub
    _ = ENNReal.ofReal (law.real U) := (ofReal_measureReal).symm
    _ ≤ ENNReal.ofReal η := ENNReal.ofReal_le_ofReal hU
    _ ≤ δ := hηδ.le

/-- **`EntireTightness` from one-probe tightness along critical sequences** (tightness of the
one-probe variable `X` implies tightness of both `Tr A` and `‖A‖_HS`; then the determinant bound
and Montel). The hypothesis is one-probe tightness, for every profile of the full family, along
every critical sequence and every choice of realizations. -/
theorem entireTightness_of_probeTightness
    (hX : ∀ (b E : ℝ) (hb : 0 < b) (hb' : b < 1 / 2), -2 < E ∧ E < 2 →
      ∀ (τ : PositiveRatio) (k : ℕ) (q : Fin k → C(Torus, ℝ)), IsProfileFamily q →
      ∀ (s : CriticalSequence τ.1) (R : ∀ j, FiniteRealization (s.parameters b hb hb' j)),
      ∀ a : Fin (k + 1), ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ j,
        (fullRingProbeLaw (R j).model 1).real
          {x | M < ‖ringSourceMatrix (s.parameters b hb hb' j) E
            (fun _ : Fin 1 => fullProfile q a) x.1 x.2 0 0‖} ≤ ε) :
    EntireTightness := by
  intro b E hb hb' hE τ k q hq s R
  exact isTightMeasureSet_finiteEntireLaw_of_probe R E hq (hX b E hb hb' hE τ k q hq s R)

end BlockBand.Critical.EntireLaw
