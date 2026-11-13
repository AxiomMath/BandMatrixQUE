module

public import BlockBand.SourceProcess.FullSourceGenerator.LimVersion

/-!
# Tested values at one time along the fdd subsequence

`point_lemma`: the tested values of a polynomial at one time have uniform fourth moments at
finite `W`, satisfy a Fatou bound in the limit, and converge along the subsequence of
finite-dimensional distributions.
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

theorem enorm_bcf_mul_sq_le {m : ℕ} (φ : BoundedContinuousFunction (Fin m → ℂ) ℝ)
    (x : Fin m → ℂ) (p : ℂ) :
    ‖((φ x : ℝ) : ℂ) * p‖ₑ ^ 2 ≤ ENNReal.ofReal (‖φ‖ ^ 2) * (1 + ‖p‖ₑ ^ 4) := by
  rw [enorm_mul, mul_pow]
  gcongr
  · rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) ?_ 2)
    simpa [Complex.norm_real] using φ.norm_coe_le_norm x
  · exact ennreal_sq_le_one_add_pow4 _

theorem lintegral_le_mul_one_add {α : Type*} [MeasurableSpace α] {ν : Measure α}
    [IsProbabilityMeasure ν] {a C : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C) {f g : α → ℝ≥0∞}
    (hfg : ∀ x, g x ≤ ENNReal.ofReal a * (1 + f x)) (hf : ∫⁻ x, f x ∂ν ≤ ENNReal.ofReal C) :
    ∫⁻ x, g x ∂ν ≤ ENNReal.ofReal (a * (1 + C)) := by
  calc ∫⁻ x, g x ∂ν ≤ ∫⁻ x, ENNReal.ofReal a * (1 + f x) ∂ν := lintegral_mono hfg
    _ = ENNReal.ofReal a * (1 + ∫⁻ x, f x ∂ν) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left measurable_const,
          lintegral_const, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal a * (1 + ENNReal.ofReal C) := by gcongr
    _ = ENNReal.ofReal (a * (1 + C)) := by
        rw [ENNReal.ofReal_mul ha, ENNReal.ofReal_add zero_le_one hC, ENNReal.ofReal_one]

variable {P : Measure Ω} {Z : TraceWord nT nI → ℝ → Ω → ℂ} {t₀ : ℝ}

/-- **Weak convergence of a continuous slot functional** (fdd + uniform `L²` bound). -/
theorem slot_conv {b E : ℝ} {k : ℕ → Fin nT → ℕ} {q : Fin nI → ℝ → ℝ} {σ : ℕ → ℕ}
    [IsProbabilityMeasure P] (hm : ∀ w, IsOrdinaryWord w → ∀ t, t₀ ≤ t → Measurable (Z w t))
    (hfdd : ∀ (m : ℕ) (ws : Fin m → TraceWord nT nI) (ts : Fin m → ℝ),
      (∀ l, IsOrdinaryWord (ws l) ∧ t₀ ≤ ts l) → ∀ Ψ : BoundedContinuousFunction (Fin m → ℂ) ℝ,
        Tendsto (fun n => ∫ ω, Ψ (fun l =>
          wordValue b E (k (σ n)) q (σ n) ⌊(σ n : ℝ) * ts l⌋₊ ω (ws l)) ∂growthPathLaw (σ n) b)
        atTop (𝓝 (∫ ω, Ψ (fun l => Z (ws l) (ts l) ω) ∂P)))
    {Ψ : TracePoly nT nI} (hΨ : IsOrdinaryPoly Ψ) {u : ℝ} (hu : t₀ ≤ u) {m : ℕ}
    {ws : Fin m → TraceWord nT nI} {us : Fin m → ℝ} (hws : ∀ l, IsOrdinaryWord (ws l) ∧ t₀ ≤ us l)
    {G : (Fin m ⊕ Ψ.vars → ℂ) → ℂ} (hG : Continuous G) {C : ℝ}
    (hC : ∀ᶠ n in atTop, ∫⁻ ω, ‖G (fun i => wordValue b E (k (σ n)) q (σ n)
      ⌊(σ n : ℝ) * slotT us Ψ u i⌋₊ ω (slotW ws Ψ i))‖ₑ ^ 2 ∂growthPathLaw (σ n) b ≤
        ENNReal.ofReal C) :
    ∫⁻ ω, ‖G (fun i => Z (slotW ws Ψ i) (slotT us Ψ u i) ω)‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal C ∧
      Tendsto (fun n => ∫ ω, G (fun i => wordValue b E (k (σ n)) q (σ n)
        ⌊(σ n : ℝ) * slotT us Ψ u i⌋₊ ω (slotW ws Ψ i)) ∂growthPathLaw (σ n) b) atTop
        (𝓝 (∫ ω, G (fun i => Z (slotW ws Ψ i) (slotT us Ψ u i) ω) ∂P)) := by
  have hs := slot_ord hws hΨ hu
  refine tendsto_integral_of_sq_bound_C (fun n => measurable_pi_iff.mpr fun i =>
      (measurable_wordValue_past b E (k (σ n)) q le_rfl _).mono (growthSigma_le' _ _) le_rfl)
    (measurable_pi_iff.mpr fun i => hm _ (hs i).1 _ (hs i).2)
    (fdd_fintype hfdd _ _ hs) hG hC

/-- **The tested values of a polynomial at one time**: uniform fourth moments at finite `W`
(on the window and at the floors of `[t₀, T]`), the Fatou bound on the limit, and the
convergence of `E[φ(test) Ψ(Z_u)]` along the fdd subsequence. -/
theorem point_lemma (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract) {b : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) (ht₀ : 0 < t₀)
    {q : Fin nI → ℝ → ℝ} (hq : IsIntervalTests q) {k : ℕ → Fin nT → ℕ}
    [IsProbabilityMeasure P] (hm : ∀ w, IsOrdinaryWord w → ∀ t, t₀ ≤ t → Measurable (Z w t))
    {σ : ℕ → ℕ} (hσ : Tendsto σ atTop atTop)
    (hfdd : ∀ (m : ℕ) (ws : Fin m → TraceWord nT nI) (ts : Fin m → ℝ),
      (∀ l, IsOrdinaryWord (ws l) ∧ t₀ ≤ ts l) → ∀ Ψ : BoundedContinuousFunction (Fin m → ℂ) ℝ,
        Tendsto (fun n => ∫ ω, Ψ (fun l =>
          wordValue b E (k (σ n)) q (σ n) ⌊(σ n : ℝ) * ts l⌋₊ ω (ws l)) ∂growthPathLaw (σ n) b)
        atTop (𝓝 (∫ ω, Ψ (fun l => Z (ws l) (ts l) ω) ∂P)))
    {Ψ : TracePoly nT nI} (hΨ : IsOrdinaryPoly Ψ) {T : ℝ} (hT : t₀ < T) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ᶠ n in atTop, ∀ j : ℕ, t₀ / 2 * (σ n : ℝ) ≤ j → (j : ℝ) ≤ T * σ n →
        ∫⁻ ω, ‖polyValue b E (k (σ n)) q (σ n) j ω Ψ‖ₑ ^ 4 ∂growthPathLaw (σ n) b ≤
          ENNReal.ofReal C) ∧
      (∀ᶠ n in atTop, ∀ u ∈ Set.Icc t₀ T, t₀ / 2 * (σ n : ℝ) ≤ ⌊(σ n : ℝ) * u⌋₊ ∧
        (⌊(σ n : ℝ) * u⌋₊ : ℝ) ≤ T * σ n) ∧
      (∀ u ∈ Set.Icc t₀ T, ∫⁻ ω, ‖eval (fun w => Z w u ω) Ψ‖ₑ ^ 4 ∂P ≤ ENNReal.ofReal C) ∧
      ∀ u ∈ Set.Icc t₀ T, ∀ (m : ℕ) (ws : Fin m → TraceWord nT nI) (us : Fin m → ℝ),
        (∀ l, IsOrdinaryWord (ws l) ∧ t₀ ≤ us l) → ∀ φ : BoundedContinuousFunction (Fin m → ℂ) ℝ,
        Tendsto (fun n => ∫ ω, ((φ (fun l => wordValue b E (k (σ n)) q (σ n)
            ⌊(σ n : ℝ) * us l⌋₊ ω (ws l)) : ℝ) : ℂ) *
            polyValue b E (k (σ n)) q (σ n) ⌊(σ n : ℝ) * u⌋₊ ω Ψ ∂growthPathLaw (σ n) b)
          atTop (𝓝 (∫ ω, ((φ (fun l => Z (ws l) (us l) ω) : ℝ) : ℂ) *
            eval (fun w => Z w u ω) Ψ ∂P)) := by
  obtain ⟨C, W₀, hC0, hC⟩ := lintegral_polyValue_pow_le hMT hGA hLp hSR hb0 hb hE1 hE2 hq
    (ε := t₀ / 2) (T := T) (by positivity) (by linarith) (mem_ordPoly_of_isOrdinaryPoly hΨ) 4
  have hA : ∀ᶠ n in atTop, ∀ j : ℕ, t₀ / 2 * (σ n : ℝ) ≤ j → (j : ℝ) ≤ T * σ n →
      ∫⁻ ω, ‖polyValue b E (k (σ n)) q (σ n) j ω Ψ‖ₑ ^ 4 ∂growthPathLaw (σ n) b ≤
        ENNReal.ofReal C :=
    (hσ.eventually_ge_atTop W₀).mono fun n hn j hj1 hj2 => hC _ hn _ j hj1 hj2
  have hB : ∀ᶠ n in atTop, ∀ u ∈ Set.Icc t₀ T, t₀ / 2 * (σ n : ℝ) ≤ ⌊(σ n : ℝ) * u⌋₊ ∧
      (⌊(σ n : ℝ) * u⌋₊ : ℝ) ≤ T * σ n := by
    filter_upwards [hσ.eventually_ge_atTop ⌈2 / t₀⌉₊] with n hn u hu
    have hW2 : 2 ≤ (σ n : ℝ) * t₀ := by
      have := Nat.ceil_le.mp hn
      rwa [div_le_iff₀ ht₀] at this
    have hWr : (0 : ℝ) ≤ σ n := Nat.cast_nonneg _
    have h1 := Nat.lt_floor_add_one ((σ n : ℝ) * u)
    have h2 : (σ n : ℝ) * t₀ ≤ σ n * u := mul_le_mul_of_nonneg_left hu.1 hWr
    have h3 : (σ n : ℝ) * u ≤ T * σ n := by nlinarith [hu.2]
    exact ⟨by nlinarith, (Nat.floor_le (by nlinarith [hu.1])).trans h3⟩
  have hAB : ∀ᶠ n in atTop, ∀ u ∈ Set.Icc t₀ T,
      ∫⁻ ω, ‖polyValue b E (k (σ n)) q (σ n) ⌊(σ n : ℝ) * u⌋₊ ω Ψ‖ₑ ^ 4
        ∂growthPathLaw (σ n) b ≤ ENNReal.ofReal C := by
    filter_upwards [hA, hB] with n hn hn' u hu
    exact hn _ (hn' u hu).1 (hn' u hu).2
  refine ⟨C, hC0, hA, hB, fun u hu => ?_, fun u hu m ws us hws φ => ?_⟩
  · -- the Fatou bound: `G = (1 · Ψ)²`
    set φ₁ : BoundedContinuousFunction (Fin 0 → ℂ) ℝ := BoundedContinuousFunction.const _ 1
    have key : ∀ V : TraceWord nT nI → ℝ → ℂ,
        ‖slotG φ₁ Ψ (fun i => V (slotW Fin.elim0 Ψ i) (slotT Fin.elim0 Ψ u i)) ^ 2‖ₑ ^ 2 =
          ‖eval (fun w => V w u) Ψ‖ₑ ^ 4 := fun V => by
      rw [slotG_apply]
      simp [φ₁, enorm_pow, ← pow_mul]
    have h := (slot_conv hm hfdd hΨ hu.1 (ws := Fin.elim0) (us := Fin.elim0)
      (fun l => l.elim0) ((continuous_slotG φ₁ Ψ).pow 2) (C := C) (hAB.mono fun n hn => by
        refine le_of_eq_of_le (lintegral_congr fun ω => ?_) (hn u hu)
        exact key (fun w τ => wordValue b E (k (σ n)) q (σ n) ⌊(σ n : ℝ) * τ⌋₊ ω w))).1
    exact le_of_eq_of_le (lintegral_congr fun ω => (key (fun w τ => Z w τ ω)).symm) h
  · have key : ∀ V : TraceWord nT nI → ℝ → ℂ,
        slotG φ Ψ (fun i => V (slotW ws Ψ i) (slotT us Ψ u i)) =
          ((φ (fun l => V (ws l) (us l)) : ℝ) : ℂ) * eval (fun w => V w u) Ψ :=
      fun V => slotG_apply φ Ψ ws us u V
    have h := (slot_conv hm hfdd hΨ hu.1 hws (continuous_slotG φ Ψ)
      (C := ‖φ‖ ^ 2 * (1 + C)) (hAB.mono fun n hn => by
        refine lintegral_le_mul_one_add (by positivity) hC0 (fun ω => ?_) (hn u hu)
        rw [key (fun w τ => wordValue b E (k (σ n)) q (σ n) ⌊(σ n : ℝ) * τ⌋₊ ω w)]
        exact enorm_bcf_mul_sq_le φ _ _)).2
    have hlim : ∫ ω, slotG φ Ψ (fun i => Z (slotW ws Ψ i) (slotT us Ψ u i) ω) ∂P =
        ∫ ω, ((φ (fun l => Z (ws l) (us l) ω) : ℝ) : ℂ) * eval (fun w => Z w u ω) Ψ ∂P :=
      integral_congr_ae (Eventually.of_forall fun ω => key (fun w τ => Z w τ ω))
    rw [hlim] at h
    refine h.congr fun n => integral_congr_ae (Eventually.of_forall fun ω => ?_)
    exact key (fun w τ => wordValue b E (k (σ n)) q (σ n) ⌊(σ n : ℝ) * τ⌋₊ ω w)

end BlockBand.SourceProcess.FullSourceGenerator.GenLim
