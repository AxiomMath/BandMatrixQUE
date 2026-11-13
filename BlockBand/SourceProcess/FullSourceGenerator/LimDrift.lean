module

public import BlockBand.SourceProcess.FullSourceGenerator.LimPoint

/-!
# The first conjunct of `GeneratorClause`: the drift martingale of every limit

**`drift_martingale hES hFS hMT hGA hLp hSR … h hΦ`**: for the data of
`GeneratorClause`, every joint critical limit `h : IsWordLimit b E k q t₀ P Z` and every ordinary
`Φ`, `M(s,t) = Φ(Z_t) - Φ(Z_s) - ∫_s^t 𝒜_uΦ(Z_u) du` has martingale increments on `[t₀,∞)`
(natural filtration of the ordinary words). Hypotheses: `EarlySummed` (open), `FullSourceStopsContract`
and the four input hypotheses `MatchedTracesContract`, `GaussianAbsorptionContract`,
`GaussianLpGradient`, `ScalarRecursionContract`.

Proof: `tendsto_tested_cyl` along the fdd subsequence `σ`; split
`E[ξ(Φ_t - Φ_s - Σ W⁻¹𝒜Φ_j)]` (fourth moments on the window); `E_n[ξΦ_{⌊σ_n v⌋}]` and the cells
`E_n[ξ𝒜Φ_{⌊σ_n v⌋}]` converge by `point_lemma`; the Riemann sum by `riemann_tendsto_C`;
`fubini_slices_C` with the version `ver P Z t₀ (𝒜Φ)` identifies `∫_s^t E[f𝒜Φ(Z_u)] du` with
`E[f∫_s^t𝒜Φ(Z_u)du]`. After `t₀` the generator is time-free (`wordGenerator_congr_time`), so
`𝒜_u = 𝒜_{t₀+1}` on `(s,t]`.
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

theorem ennreal_le_one_add_pow4 (x : ℝ≥0∞) : x ≤ 1 + x ^ 4 := by
  rcases le_total x 1 with h | h
  · exact h.trans le_self_add
  · calc x = x ^ 1 := (pow_one x).symm
      _ ≤ x ^ 4 := pow_le_pow_right₀ h (by norm_num)
      _ ≤ 1 + x ^ 4 := le_add_self

theorem enorm_mul_le_one_add {ψ p : ℂ} {B : ℝ} (hψ : ‖ψ‖ ≤ B) :
    ‖ψ * p‖ₑ ≤ ENNReal.ofReal B * (1 + ‖p‖ₑ ^ 4) := by
  rw [enorm_mul]
  gcongr
  · rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal hψ
  · exact ennreal_le_one_add_pow4 _

theorem norm_integral_le_of_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {g : α → ℂ} {B : ℝ} (hB : 0 ≤ B) (h : ∫⁻ x, ‖g x‖ₑ ∂μ ≤ ENNReal.ofReal B) :
    ‖∫ x, g x ∂μ‖ ≤ B := by
  have := (enorm_integral_le_lintegral_enorm g).trans h
  rwa [← ofReal_norm, ENNReal.ofReal_le_ofReal_iff hB] at this

theorem integrable_of_lintegral_four {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {f : α → ℂ} (hf : AEStronglyMeasurable f μ) {C : ℝ}
    (h : ∫⁻ x, ‖f x‖ₑ ^ 4 ∂μ ≤ ENNReal.ofReal C) : Integrable f μ :=
  (memLp_two_of_lintegral_four hf h).integrable one_le_two

/-- **The first conjunct of `GeneratorClause`, for every ordinary `Φ`.** -/
theorem drift_martingale (hES : EarlySummed) (hFS : FullSourceStopsContract)
    (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {E : ℝ}
    (hE1 : -2 < E) (hE2 : E < 2) {t₀ : ℝ} (ht₀ : 0 < t₀) {q : Fin nI → ℝ → ℝ}
    (hq : ∀ a, ∃ s : ℝ, IsSourceTest s t₀ (q a)) (k : ℕ → Fin nT → ℕ)
    (hk : ∀ᶠ W in atTop, ∀ a, ((k W a + 1 : ℕ) : ℝ) ≤ W * t₀) {P : Measure Ω}
    {Z : TraceWord nT nI → ℝ → Ω → ℂ} (h : IsWordLimit b E k q t₀ P Z) {Φ : TracePoly nT nI}
    (hΦ : IsOrdinaryPoly Φ) :
    IsMartingaleIncrements P (fun w : {w : TraceWord nT nI // IsOrdinaryWord w} => Z w.1)
      (Set.Ici t₀) fun s t ω => eval (fun w => Z w t ω) Φ - eval (fun w => Z w s ω) Φ -
        ∫ u in s..t, eval (fun w => Z w u ω) (wordGenerator b E q u Φ) := by
  have := h.prob
  obtain ⟨σ, hσm, hfdd⟩ := h.fdd
  have hσ := hσm.tendsto_atTop
  have hqI : IsIntervalTests q := fun a => let ⟨s', hs'⟩ := hq a; ⟨s', t₀, hs'⟩
  have hq0 : ∀ a x, t₀ < x → q a x = 0 := fun a x hx => by
    obtain ⟨s', hs'⟩ := hq a
    exact hs'.2.1 x fun h => by linarith [h.2]
  set A := wordGenerator b E q (t₀ + 1) Φ with hAdef
  have hA : IsOrdinaryPoly A := isOrdinaryPoly_of_mem (wordGenerator_mem hΦ b E q _)
  have hgen : ∀ u, t₀ < u → wordGenerator b E q u Φ = A := fun u hu =>
    wordGenerator_congr_time b E q (fun a => by rw [hq0 a u hu, hq0 a _ (by linarith)]) Φ
  intro s t hs ht hst
  have hs' : t₀ ≤ s := hs
  have ht' : t₀ ≤ t := ht
  set S := contSet P Z t₀
  have hS : ∀ᵐ ω ∂P, ω ∈ S := ae_contSet h.continuous
  set F := ver P Z t₀ A
  have hFm : Measurable (Function.uncurry F) := measurable_uncurry_ver h.measurable A
  have hFeq : ∀ u, t₀ ≤ u → ∀ ω ∈ S, F u ω = eval (fun w => Z w u ω) A :=
    fun u hu ω hω => ver_eq hA hu hω
  have hIeq : ∀ ω ∈ S, ∫ u in s..t, eval (fun w => Z w u ω) (wordGenerator b E q u Φ) =
      ∫ u in s..t, F u ω := fun ω hω =>
    intervalIntegral.integral_congr_ae (Eventually.of_forall fun u hu => by
      rw [Set.uIoc_of_le hst] at hu
      rw [hgen u (by linarith [hu.1]), hFeq u (by linarith [hu.1]) ω hω])
  obtain ⟨CΦ, -, hΦwin, -, hΦlim, hΦt⟩ := point_lemma hMT hGA hLp hSR hb0 hb hE1 hE2 ht₀ hqI
    h.measurable hσ hfdd hΦ (T := t + 1) (by linarith)
  obtain ⟨CA, hCA0, hAwin, hflo, hAlim, hAt⟩ := point_lemma hMT hGA hLp hSR hb0 hb hE1 hE2 ht₀
    hqI h.measurable hσ hfdd hA (T := t + 1) (by linarith)
  have hX : ∀ v, t₀ ≤ v → v ≤ t + 1 → Integrable (fun ω => eval (fun w => Z w v ω) Φ) P :=
    fun v hv1 hv2 => integrable_of_lintegral_four
      (measurable_evalZ h.measurable hΦ hv1).aestronglyMeasurable (hΦlim v ⟨hv1, hv2⟩)
  -- slices of the version
  have hslice : ∀ (ψ : Ω → ℂ) (B : ℝ), 0 ≤ B → (∀ ω, ‖ψ ω‖ ≤ B) → ∀ u ∈ Set.Ioc s t,
      ∫⁻ ω, ‖ψ ω * F u ω‖ₑ ∂P ≤ ENNReal.ofReal (B * (1 + CA)) := by
    intro ψ B hB hψ u hu
    have hu0 : t₀ ≤ u := by linarith [hu.1]
    rw [lintegral_congr_ae (hS.mono fun ω hω => by rw [hFeq u hu0 ω hω])]
    exact lintegral_le_mul_one_add hB hCA0 (fun ω => enorm_mul_le_one_add (hψ ω))
      (hAlim u ⟨hu0, by linarith [hu.2]⟩)
  have hF1 := fubini_slices_C hFm (ψ := fun _ => (1 : ℂ)) measurable_const hst
    (hslice _ 1 zero_le_one fun _ => by simp)
  have hIint : Integrable (fun ω => ∫ u in s..t, eval (fun w => Z w u ω)
      (wordGenerator b E q u Φ)) P :=
    (hF1.1.congr (Eventually.of_forall fun ω => one_mul _)).congr
      (hS.mono fun ω hω => (hIeq ω hω).symm)
  refine ⟨((hX t ht' (by linarith)).sub (hX s hs' (by linarith))).sub hIint,
    fun m i us hus φ => ?_⟩
  set ws : Fin m → TraceWord nT nI := fun l => (i l).1
  have hws : ∀ l, IsOrdinaryWord (ws l) ∧ t₀ ≤ us l := fun l => ⟨(i l).2, (hus l).1⟩
  set f : Ω → ℂ := fun ω => ((φ (fun l => Z (ws l) (us l) ω) : ℝ) : ℂ)
  have hfm : Measurable f := Complex.measurable_ofReal.comp (φ.continuous.measurable.comp
    (measurable_pi_iff.mpr fun l => h.measurable _ (hws l).1 _ (hws l).2))
  have hfb : ∀ ω, ‖f ω‖ ≤ ‖φ‖ := fun ω => by
    simp only [f, Complex.norm_real]; exact φ.norm_coe_le_norm _
  have hF := fubini_slices_C hFm hfm hst (hslice f ‖φ‖ (norm_nonneg _) hfb)
  set g : ℝ → ℂ := fun u => ∫ ω, f ω * eval (fun w => Z w u ω) A ∂P
  have hgF : Set.EqOn (fun u => ∫ ω, f ω * F u ω ∂P) g (Set.uIoc s t) := fun u hu => by
    rw [Set.uIoc_of_le hst] at hu
    exact integral_congr_ae (hS.mono fun ω hω => by
      beta_reduce; rw [hFeq u (by linarith [hu.1]) ω hω])
  -- the finite-`W` side
  set ξ : ℕ → (W : ℕ) → GrowthPath W → ℂ := fun n W ω =>
    ((φ (fun l => wordValue b E (k (σ n)) q W ⌊(W : ℝ) * us l⌋₊ ω (ws l)) : ℝ) : ℂ)
  set a : ℝ → ℕ → ℂ := fun v n => ∫ ω, ξ n (σ n) ω *
    polyValue b E (k (σ n)) q (σ n) ⌊(σ n : ℝ) * v⌋₊ ω Φ ∂growthPathLaw (σ n) b
  set c : ℕ → ℕ → ℂ := fun n j => ∫ ω, ξ n (σ n) ω *
    polyValue b E (k (σ n)) q (σ n) j ω A ∂growthPathLaw (σ n) b
  have hfin := (tendsto_tested_cyl hES hFS hMT hGA hLp hSR hb0 hb hE1 hE2 ht₀ hq k hk hΦ hs' hst
    ws us (fun l => (hus l).2) φ).comp hσ
  have hξm : ∀ n, AEStronglyMeasurable (ξ n (σ n)) (growthPathLaw (σ n) b) := fun n =>
    (Complex.measurable_ofReal.comp (φ.continuous.measurable.comp (measurable_pi_iff.mpr
      fun l => (measurable_wordValue_past b E (k (σ n)) q le_rfl _).mono
        (growthSigma_le' _ _) le_rfl))).aestronglyMeasurable
  have hξb : ∀ n ω, ‖ξ n (σ n) ω‖ ≤ ‖φ‖ := fun n ω => by
    simp only [ξ, Complex.norm_real]; exact φ.norm_coe_le_norm _
  have hpint : ∀ (Ψ : TracePoly nT nI) (C : ℝ) (n j : ℕ),
      ∫⁻ ω, ‖polyValue b E (k (σ n)) q (σ n) j ω Ψ‖ₑ ^ 4 ∂growthPathLaw (σ n) b ≤
        ENNReal.ofReal C →
      Integrable (fun ω => ξ n (σ n) ω * polyValue b E (k (σ n)) q (σ n) j ω Ψ)
        (growthPathLaw (σ n) b) := fun Ψ C n j hC =>
    (integrable_of_lintegral_four ((measurable_polyValue_past b E (k (σ n)) q le_rfl Ψ).mono
      (growthSigma_le' _ _) le_rfl).aestronglyMeasurable hC).bdd_mul (hξm n)
        (Eventually.of_forall (hξb n))
  have hsplit : ∀ᶠ n in atTop, ∫ ω, ξ n (σ n) ω *
      (polyValue b E (k (σ n)) q (σ n) ⌊(σ n : ℝ) * t⌋₊ ω Φ -
        polyValue b E (k (σ n)) q (σ n) ⌊(σ n : ℝ) * s⌋₊ ω Φ -
          ∑ j ∈ Finset.Ico ⌊(σ n : ℝ) * s⌋₊ ⌊(σ n : ℝ) * t⌋₊,
            (σ n : ℂ)⁻¹ * polyValue b E (k (σ n)) q (σ n) j ω A) ∂growthPathLaw (σ n) b =
      a t n - a s n - ∑ j ∈ Finset.Ico ⌊(σ n : ℝ) * s⌋₊ ⌊(σ n : ℝ) * t⌋₊, c n j / (σ n : ℂ) := by
    filter_upwards [hΦwin, hAwin, hflo] with n hn1 hn2 hn3
    have ht1 := hn3 t ⟨ht', by linarith⟩
    have hs1 := hn3 s ⟨hs', by linarith⟩
    have hjw : ∀ j ∈ Finset.Ico ⌊(σ n : ℝ) * s⌋₊ ⌊(σ n : ℝ) * t⌋₊,
        t₀ / 2 * (σ n : ℝ) ≤ j ∧ (j : ℝ) ≤ (t + 1) * σ n := fun j hj => by
      obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj
      refine ⟨hs1.1.trans (by exact_mod_cast hj1), le_trans ?_ ht1.2⟩
      exact_mod_cast hj2.le
    have hiA : ∀ j ∈ Finset.Ico ⌊(σ n : ℝ) * s⌋₊ ⌊(σ n : ℝ) * t⌋₊, Integrable (fun ω =>
        (σ n : ℂ)⁻¹ * (ξ n (σ n) ω * polyValue b E (k (σ n)) q (σ n) j ω A))
          (growthPathLaw (σ n) b) := fun j hj =>
      (hpint A CA n j (hn2 j (hjw j hj).1 (hjw j hj).2)).const_mul _
    have e : ∀ ω, ξ n (σ n) ω * (polyValue b E (k (σ n)) q (σ n) ⌊(σ n : ℝ) * t⌋₊ ω Φ -
        polyValue b E (k (σ n)) q (σ n) ⌊(σ n : ℝ) * s⌋₊ ω Φ -
          ∑ j ∈ Finset.Ico ⌊(σ n : ℝ) * s⌋₊ ⌊(σ n : ℝ) * t⌋₊,
            (σ n : ℂ)⁻¹ * polyValue b E (k (σ n)) q (σ n) j ω A) =
        ξ n (σ n) ω * polyValue b E (k (σ n)) q (σ n) ⌊(σ n : ℝ) * t⌋₊ ω Φ -
          ξ n (σ n) ω * polyValue b E (k (σ n)) q (σ n) ⌊(σ n : ℝ) * s⌋₊ ω Φ -
          ∑ j ∈ Finset.Ico ⌊(σ n : ℝ) * s⌋₊ ⌊(σ n : ℝ) * t⌋₊,
            (σ n : ℂ)⁻¹ * (ξ n (σ n) ω * polyValue b E (k (σ n)) q (σ n) j ω A) := fun ω => by
      rw [mul_sub, mul_sub, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [integral_congr_ae (Eventually.of_forall e),
      integral_sub (f := fun ω => ξ n (σ n) ω * polyValue b E (k (σ n)) q (σ n) ⌊(σ n : ℝ) * t⌋₊ ω Φ -
          ξ n (σ n) ω * polyValue b E (k (σ n)) q (σ n) ⌊(σ n : ℝ) * s⌋₊ ω Φ)
        ((hpint Φ CΦ n _ (hn1 _ ht1.1 ht1.2)).sub (hpint Φ CΦ n _ (hn1 _ hs1.1 hs1.2)))
        (integrable_finsetSum _ hiA),
      integral_sub (hpint Φ CΦ n _ (hn1 _ ht1.1 ht1.2)) (hpint Φ CΦ n _ (hn1 _ hs1.1 hs1.2)),
      integral_finsetSum _ hiA]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by rw [integral_const_mul, inv_mul_eq_div]
  -- the three limits
  have hat := hΦt t ⟨ht', by linarith⟩ m ws us hws φ
  have has := hΦt s ⟨hs', by linarith⟩ m ws us hws φ
  have hbd : ∀ᶠ n in atTop, ∀ v ∈ Set.Icc s t, ‖c n ⌊((σ n : ℕ) : ℝ) * v⌋₊‖ ≤ ‖φ‖ * (1 + CA) := by
    filter_upwards [hAwin, hflo] with n hn hn' v hv
    have hv' := hn' v ⟨hs'.trans hv.1, by linarith [hv.2]⟩
    refine norm_integral_le_of_lintegral (by positivity) ?_
    exact lintegral_le_mul_one_add (norm_nonneg _) hCA0
      (fun ω => enorm_mul_le_one_add (hξb n ω)) (hn _ hv'.1 hv'.2)
  have hR := riemann_tendsto_C hσ (c := c) (g := g) (by linarith) hst (hF.2.2.2.congr hgF) hbd
    fun v hv => hAt v ⟨hs'.trans hv.1, by linarith [hv.2]⟩ m ws us hws φ
  have hzero : (∫ ω, f ω * eval (fun w => Z w t ω) Φ ∂P) -
      (∫ ω, f ω * eval (fun w => Z w s ω) Φ ∂P) - ∫ u in s..t, g u = 0 :=
    tendsto_nhds_unique ((hat.sub has).sub hR) (hfin.congr' (hsplit.mono fun n hn => Eq.trans rfl hn))
  -- Fubini on the limit and conclusion
  have hfub : ∫ ω, f ω * (∫ u in s..t, F u ω) ∂P = ∫ u in s..t, g u := by
    rw [hF.2.2.1]; exact intervalIntegral.integral_congr_ae (Eventually.of_forall fun u hu => hgF hu)
  have hfX : ∀ v, t₀ ≤ v → v ≤ t + 1 → Integrable (fun ω => f ω * eval (fun w => Z w v ω) Φ) P :=
    fun v hv1 hv2 => (hX v hv1 hv2).bdd_mul hfm.aestronglyMeasurable
      (Eventually.of_forall hfb)
  show ∫ ω, φ (fun l => Z (ws l) (us l) ω) • (eval (fun w => Z w t ω) Φ -
    eval (fun w => Z w s ω) Φ - ∫ u in s..t, eval (fun w => Z w u ω)
      (wordGenerator b E q u Φ)) ∂P = 0
  have e2 : (fun ω => φ (fun l => Z (ws l) (us l) ω) • (eval (fun w => Z w t ω) Φ -
      eval (fun w => Z w s ω) Φ - ∫ u in s..t, eval (fun w => Z w u ω)
        (wordGenerator b E q u Φ))) =ᵐ[P] fun ω => f ω * eval (fun w => Z w t ω) Φ -
          f ω * eval (fun w => Z w s ω) Φ - f ω * ∫ u in s..t, F u ω :=
    hS.mono fun ω hω => by
      simp only [Complex.real_smul, f]; rw [hIeq ω hω]; ring
  rw [integral_congr_ae e2, integral_sub (f := fun ω => f ω * eval (fun w => Z w t ω) Φ -
      f ω * eval (fun w => Z w s ω) Φ) ((hfX t ht' (by linarith)).sub
      (hfX s hs' (by linarith))) hF.1,
    integral_sub (hfX t ht' (by linarith)) (hfX s hs' (by linarith)), hfub]
  exact hzero

end BlockBand.SourceProcess.FullSourceGenerator.GenLim
