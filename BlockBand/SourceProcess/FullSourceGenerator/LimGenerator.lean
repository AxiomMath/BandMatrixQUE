module

public import BlockBand.SourceProcess.FullSourceGenerator.LimDrift
public import BlockBand.SourceProcess.FullSourceGenerator.LimTests
public import BlockBand.SourceProcess.FullSourceGenerator.LimBracket

/-!
# `GeneratorClause`: the bracket conjunct and the assembly

* **`GenLim.bracket_martingale`**: for every joint critical limit and ordinary `Φ`,
  `M(s,t)² - ∫_s^tΓ(Φ)(Z_u)du` has martingale increments on `[t₀,∞)`. Proof (limit side, no new
  finite-`W` input): `drift_martingale` for `Φ` and for `Φ²` (`𝒜(Φ²) = 2Φ𝒜Φ + Γ(Φ)`,
  `wordGenerator_pow`), the unbounded tests `φ·Φ(Z_s)` and `φ·𝒜Φ(Z_u)` (`slot_test_zero`), the
  versions `ver` of `Φ, 𝒜Φ, Γ(Φ)` with limit moments from `point_lemma`, and
  `bracket_abstract`.
* **`generatorClause_of hES hFS hMT hGA hLp hSR : GeneratorClause`** and
  **`fullSourceGenerator_holds_of_early … : FullSourceGeneratorContract`** (with
  `fullSourceGenerator_of_early`). Hypotheses: `EarlySummed` (open; supplied by
  `ContractingWords.earlySummed_holds`), `FullSourceStopsContract`, and
  `MatchedTracesContract`, `GaussianAbsorptionContract`, `GaussianLpGradient`,
  `ScalarRecursionContract`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceGenerator.GenLim

open MeasureTheory Filter Topology MvPolynomial
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.FullSourceStops
open scoped ENNReal

variable {nT nI : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- **The second conjunct of `GeneratorClause`, for every ordinary `Φ`.** -/
theorem bracket_martingale (hES : EarlySummed) (hFS : FullSourceStopsContract)
    (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {E : ℝ}
    (hE1 : -2 < E) (hE2 : E < 2) {t₀ : ℝ} (ht₀ : 0 < t₀) {q : Fin nI → ℝ → ℝ}
    (hq : ∀ a, ∃ s : ℝ, IsSourceTest s t₀ (q a)) (k : ℕ → Fin nT → ℕ)
    (hk : ∀ᶠ W in atTop, ∀ a, ((k W a + 1 : ℕ) : ℝ) ≤ W * t₀) {P : Measure Ω}
    {Z : TraceWord nT nI → ℝ → Ω → ℂ} (h : IsWordLimit b E k q t₀ P Z) {Φ : TracePoly nT nI}
    (hΦ : IsOrdinaryPoly Φ) :
    IsMartingaleIncrements P (fun w : {w : TraceWord nT nI // IsOrdinaryWord w} => Z w.1)
      (Set.Ici t₀) fun s t ω => (eval (fun w => Z w t ω) Φ - eval (fun w => Z w s ω) Φ -
        ∫ u in s..t, eval (fun w => Z w u ω) (wordGenerator b E q u Φ)) ^ 2 -
          ∫ u in s..t, eval (fun w => Z w u ω) (wordCarre b E Φ) := by
  have := h.prob
  have hM1 := drift_martingale hES hFS hMT hGA hLp hSR hb0 hb hE1 hE2 ht₀ hq k hk h hΦ
  have hM2 := drift_martingale hES hFS hMT hGA hLp hSR hb0 hb hE1 hE2 ht₀ hq k hk h
    (isOrdinaryPoly_pow hΦ 2)
  obtain ⟨σ, hσm, hfdd⟩ := h.fdd
  have hqI : IsIntervalTests q := fun a => let ⟨s', hs'⟩ := hq a; ⟨s', t₀, hs'⟩
  have hq0 : ∀ a x, t₀ < x → q a x = 0 := fun a x hx => by
    obtain ⟨s', hs'⟩ := hq a
    exact hs'.2.1 x fun h => by linarith [h.2]
  set A := wordGenerator b E q (t₀ + 1) Φ
  set Γ := wordCarre b E Φ
  have hA : IsOrdinaryPoly A := isOrdinaryPoly_of_mem (wordGenerator_mem hΦ b E q _)
  have hΓ : IsOrdinaryPoly Γ := isOrdinaryPoly_of_mem (wordCarre_mem hΦ b E)
  have hgen : ∀ u, t₀ < u → wordGenerator b E q u Φ = A := fun u hu =>
    wordGenerator_congr_time b E q (fun a => by rw [hq0 a u hu, hq0 a _ (by linarith)]) Φ
  have hgen2 : ∀ u, t₀ < u → ∀ x : TraceWord nT nI → ℂ, eval x (wordGenerator b E q u (Φ ^ 2)) =
      2 * eval x Φ * eval x A + eval x Γ := fun u hu x => by
    rw [wordGenerator_pow, hgen u hu]
    simp only [map_add, map_mul, map_pow, eval_C]
    norm_num
    rfl
  set S := contSet P Z t₀
  have hS : ∀ᵐ ω ∂P, ω ∈ S := ae_contSet h.continuous
  obtain ⟨X, hXd⟩ : ∃ X : ℝ → Ω → ℂ, X = ver P Z t₀ Φ := ⟨_, rfl⟩
  obtain ⟨Av, hAd⟩ : ∃ X : ℝ → Ω → ℂ, X = ver P Z t₀ A := ⟨_, rfl⟩
  obtain ⟨Gv, hGd⟩ : ∃ X : ℝ → Ω → ℂ, X = ver P Z t₀ Γ := ⟨_, rfl⟩
  have hX : ∀ u, t₀ ≤ u → ∀ ω ∈ S, X u ω = eval (fun w => Z w u ω) Φ :=
    fun u hu ω hω => by rw [hXd]; exact ver_eq hΦ hu hω
  have hAv : ∀ u, t₀ ≤ u → ∀ ω ∈ S, Av u ω = eval (fun w => Z w u ω) A :=
    fun u hu ω hω => by rw [hAd]; exact ver_eq hA hu hω
  have hGv : ∀ u, t₀ ≤ u → ∀ ω ∈ S, Gv u ω = eval (fun w => Z w u ω) Γ :=
    fun u hu ω hω => by rw [hGd]; exact ver_eq hΓ hu hω
  -- the increments are the version increments on `S`
  have hMZ : ∀ u t, t₀ ≤ u → u ≤ t → ∀ ω ∈ S, eval (fun w => Z w t ω) Φ -
      eval (fun w => Z w u ω) Φ - ∫ v in u..t, eval (fun w => Z w v ω) (wordGenerator b E q v Φ) =
        incr X Av u t ω := fun u t hu hut ω hω => by
    simp only [incr]
    rw [hX t (hu.trans hut) ω hω, hX u hu ω hω]
    congr 1
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun v hv => ?_)
    rw [Set.uIoc_of_le hut] at hv
    rw [hgen v (by linarith [hv.1]), hAv v (by linarith [hv.1]) ω hω]
  intro s t hs ht hst
  have hs' : t₀ ≤ s := hs
  have hΓZ : ∀ ω ∈ S, ∫ u in s..t, eval (fun w => Z w u ω) Γ = ∫ u in s..t, Gv u ω :=
    fun ω hω => intervalIntegral.integral_congr_ae (Eventually.of_forall fun v hv => by
      rw [Set.uIoc_of_le hst] at hv
      rw [hGv v (by linarith [hv.1]) ω hω])
  -- moments on `[s, t]`
  have hmom : ∀ Ψ : TracePoly nT nI, IsOrdinaryPoly Ψ → ∃ C : ℝ, 0 ≤ C ∧ ∀ v ∈ Set.Icc s t,
      ∫⁻ ω, ‖ver P Z t₀ Ψ v ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal C ∧
        ∫⁻ ω, ‖ver P Z t₀ Ψ v ω‖ₑ ∂P ≤ ENNReal.ofReal C := fun Ψ hΨ => by
    obtain ⟨C, hC0, -, -, hlim, -⟩ := point_lemma hMT hGA hLp hSR hb0 hb hE1 hE2 ht₀ hqI
      h.measurable hσm.tendsto_atTop hfdd hΨ (T := t + 1) (by linarith [ht.out])
    refine ⟨1 * (1 + C), by positivity, fun v hv => ?_⟩
    have hv0 : t₀ ≤ v := hs'.trans hv.1
    have hl := hlim v ⟨hv0, by linarith [hv.2]⟩
    have e : ∀ g : ℂ → ℝ≥0∞, ∫⁻ ω, g (ver P Z t₀ Ψ v ω) ∂P =
        ∫⁻ ω, g (eval (fun w => Z w v ω) Ψ) ∂P := fun g =>
      lintegral_congr_ae (hS.mono fun ω hω => by beta_reduce; rw [ver_eq hΨ hv0 hω])
    rw [e (fun z => ‖z‖ₑ ^ 2), e (fun z => ‖z‖ₑ)]
    exact ⟨lintegral_le_mul_one_add zero_le_one hC0 (fun ω => by
        rw [ENNReal.ofReal_one, one_mul]; exact ennreal_sq_le_one_add_pow4 _) hl,
      lintegral_le_mul_one_add zero_le_one hC0 (fun ω => by
        rw [ENNReal.ofReal_one, one_mul]; exact ennreal_le_one_add_pow4 _) hl⟩
  obtain ⟨C₁, hC₁, hm₁⟩ := hmom Φ hΦ
  obtain ⟨C₂, hC₂, hm₂⟩ := hmom A hA
  obtain ⟨C₃, hC₃, hm₃⟩ := hmom Γ hΓ
  set C := C₁ + C₂ + C₃
  have hC : 0 ≤ C := by positivity
  have le1 : ENNReal.ofReal C₁ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal (by linarith)
  have le2 : ENNReal.ofReal C₂ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal (by linarith)
  have le3 : ENNReal.ofReal C₃ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal (by linarith)
  have hX2 : ∀ v ∈ Set.Icc s t, ∫⁻ ω, ‖X v ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal C :=
    fun v hv => by rw [hXd]; exact (hm₁ v hv).1.trans le1
  have hA2 : ∀ v ∈ Set.Icc s t, ∫⁻ ω, ‖Av v ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal C :=
    fun v hv => by rw [hAd]; exact (hm₂ v hv).1.trans le2
  have hG1 : ∀ v ∈ Set.Icc s t, ∫⁻ ω, ‖Gv v ω‖ₑ ∂P ≤ ENNReal.ofReal C :=
    fun v hv => by rw [hGd]; exact (hm₃ v hv).2.trans le3
  have hXm : Measurable (Function.uncurry X) := by
    rw [hXd]; exact measurable_uncurry_ver h.measurable Φ
  have hAm : Measurable (Function.uncurry Av) := by
    rw [hAd]; exact measurable_uncurry_ver h.measurable A
  have hGm : Measurable (Function.uncurry Gv) := by
    rw [hGd]; exact measurable_uncurry_ver h.measurable Γ
  have hXc : ∀ ω, Continuous fun u => X u ω := by rw [hXd]; exact continuous_ver Φ
  have hAc : ∀ ω, Continuous fun u => Av u ω := by rw [hAd]; exact continuous_ver A
  have hGc : ∀ ω, Continuous fun u => Gv u ω := by rw [hGd]; exact continuous_ver Γ
  -- `L²` of the increments `M(u,t)`, `u ∈ [s,t]`
  have hMZ2 : ∀ u, s ≤ u → u ≤ t → MemLp (fun ω => eval (fun w => Z w t ω) Φ -
      eval (fun w => Z w u ω) Φ - ∫ v in u..t, eval (fun w => Z w v ω)
        (wordGenerator b E q v Φ)) 2 P := fun u hu hut =>
    ((memLp_incr hXm hAc hAm hut (fun v hv => hX2 v ⟨hu.trans hv.1, hv.2⟩)
      (fun v hv => hA2 v ⟨hu.trans hv.1, hv.2⟩)).2).ae_eq
        (hS.mono fun ω hω => (hMZ u t (hs'.trans hu) hut ω hω).symm)
  have hev2 : ∀ (Ψ : TracePoly nT nI) (Y : ℝ → Ω → ℂ) (C' : ℝ),
      Measurable (Function.uncurry Y) →
      (∀ u, t₀ ≤ u → ∀ ω ∈ S, Y u ω = eval (fun w => Z w u ω) Ψ) → ∀ u, s ≤ u → u ≤ t →
      (∀ v ∈ Set.Icc s t, ∫⁻ ω, ‖Y v ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal C') →
      MemLp (fun ω => eval (fun w => Z w u ω) Ψ) 2 P := fun Ψ Y C' hYm hY u hu hut hb2 =>
    (memLp_two_of_lintegral (measurable_slice hYm u).aestronglyMeasurable
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hb2 u ⟨hu, hut⟩))).ae_eq
        (hS.mono fun ω hω => hY u (hs'.trans hu) ω hω)
  -- the tested statement for every cylinder test
  have key : ∀ (m : ℕ) (i : Fin m → {w : TraceWord nT nI // IsOrdinaryWord w}) (us : Fin m → ℝ),
      (∀ l, us l ∈ Set.Ici t₀ ∧ us l ≤ s) → ∀ φ : BoundedContinuousFunction (Fin m → ℂ) ℝ,
      Integrable (fun ω => incr X Av s t ω ^ 2 - ∫ u in s..t, Gv u ω) P ∧
        ∫ ω, ((φ (fun l => Z (i l).1 (us l) ω) : ℝ) : ℂ) *
          (incr X Av s t ω ^ 2 - ∫ u in s..t, Gv u ω) ∂P = 0 := by
    intro m i us hus φ
    set ws : Fin m → TraceWord nT nI := fun l => (i l).1
    have hws : ∀ l, IsOrdinaryWord (ws l) ∧ t₀ ≤ us l := fun l => ⟨(i l).2, (hus l).1⟩
    set f : Ω → ℂ := fun ω => ((φ (fun l => Z (ws l) (us l) ω) : ℝ) : ℂ)
    have hfm : Measurable f := Complex.measurable_ofReal.comp (φ.continuous.measurable.comp
      (measurable_pi_iff.mpr fun l => h.measurable _ (hws l).1 _ (hws l).2))
    have hfb : ∀ ω, ‖f ω‖ ≤ ‖φ‖ := fun ω => by
      simp only [f, Complex.norm_real]; exact φ.norm_coe_le_norm _
    refine bracket_abstract hfm (norm_nonneg _) hfb hXc hAc hGc hXm hAm hGm hst hC hX2 hA2 hG1
      ?_ ?_ ?_
    · have h0 := (hM2 s t hs ht hst).2 m i us hus φ
      refine (integral_congr_ae (hS.mono fun ω hω => ?_)).trans h0
      simp only [Complex.real_smul, map_pow]
      rw [hX t (hs'.trans hst) ω hω, hX s hs' ω hω]
      congr 2
      refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun v hv => ?_)
      rw [Set.uIoc_of_le hst] at hv
      have hv0 : t₀ ≤ v := by linarith [hv.1]
      rw [hgen2 v (by linarith [hv.1]), hX v hv0 ω hω, hAv v hv0 ω hω, hGv v hv0 ω hω]
    · have h0 := slot_test_zero h.measurable hM1 hs' hst (hMZ2 s le_rfl hst) hΦ
        (hev2 Φ X C hXm hX s le_rfl hst hX2) hws (fun l => (hus l).2) φ
      refine (integral_congr_ae (hS.mono fun ω hω => ?_)).trans h0
      rw [hMZ s t hs' hst ω hω, hX s hs' ω hω]
    · intro u hu
      have hu0 : t₀ ≤ u := hs'.trans hu.1.le
      have h0 := slot_test_zero h.measurable hM1 hu0 hu.2 (hMZ2 u hu.1.le hu.2) hA
        (hev2 A Av C hAm hAv u hu.1.le hu.2 hA2) hws (fun l => (hus l).2.trans hu.1.le) φ
      refine (integral_congr_ae (hS.mono fun ω hω => ?_)).trans h0
      rw [hMZ u t hu0 hu.2 ω hω, hAv u hu0 ω hω]
  have hae : ∀ᵐ ω ∂P, (eval (fun w => Z w t ω) Φ - eval (fun w => Z w s ω) Φ -
      ∫ u in s..t, eval (fun w => Z w u ω) (wordGenerator b E q u Φ)) ^ 2 -
        ∫ u in s..t, eval (fun w => Z w u ω) (wordCarre b E Φ) =
      incr X Av s t ω ^ 2 - ∫ u in s..t, Gv u ω := hS.mono fun ω hω => by
    rw [hMZ s t hs' hst ω hω, hΓZ ω hω]
  refine ⟨(key 0 Fin.elim0 Fin.elim0 (fun l => l.elim0)
      (BoundedContinuousFunction.const _ 1)).1.congr (hae.mono fun ω h => h.symm),
    fun m i us hus φ => ?_⟩
  refine (integral_congr_ae (hae.mono fun ω hω => ?_)).trans (key m i us hus φ).2
  simp only [Complex.real_smul]
  rw [hω]

end BlockBand.SourceProcess.FullSourceGenerator.GenLim

namespace BlockBand.SourceProcess.FullSourceGenerator

open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.Layers

/-- **`GeneratorClause`** (the `generator` field) from `EarlySummed` (open),
`FullSourceStopsContract` and the four input hypotheses. -/
theorem generatorClause_of (hES : EarlySummed) (hFS : FullSourceStopsContract)
    (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) : GeneratorClause := by
  intro b hb0 hb E hE1 hE2 t₀ ht₀ nT nI q hq k hk Ω _ P Z h Φ hΦ
  exact ⟨GenLim.drift_martingale hES hFS hMT hGA hLp hSR hb0 hb hE1 hE2 ht₀ hq k hk h hΦ,
    GenLim.bracket_martingale hES hFS hMT hGA hLp hSR hb0 hb hE1 hE2 ht₀ hq k hk h hΦ⟩

/-- **`FullSourceGeneratorContract`** from `EarlySummed`, `FullSourceStopsContract`
and the four input hypotheses (`tight`: `tightClause_of`; `moments`:
`fullSourceMoments_holds`). -/
theorem fullSourceGenerator_holds_of_early (hES : EarlySummed) (hFS : FullSourceStopsContract)
    (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) : FullSourceGeneratorContract :=
  fullSourceGenerator_of_early hES hFS hMT hGA hLp hSR
    (generatorClause_of hES hFS hMT hGA hLp hSR)

end BlockBand.SourceProcess.FullSourceGenerator
