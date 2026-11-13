module

public import BlockBand.Endpoints.Response.NearSchattenLimit
public import BlockBand.Endpoints.Response.NearSchattenUpper

/-!
# Exponential decay of critical limsups

This file proves the `limsupDecay` clause of `NearSchattenDecayContract` (`ns_limsupDecay`).
The hypotheses are `ClockFractionalEntranceContract` (`later`), `FullSourceGeneratorContract` (only
`moments`, for the higher trace bound `E (Tr A)² ≤ C₂`), `NsRegularizedLimitGenerator` (through
`limitDecay`) and `NsCriticalClockLimitsExist`.

* The constant `C = max(C₁, 0) e^{κ}` comes from the finite fractional entrance at one unit of
  travel (`later` on `[1, 1]`; chosen before the source and the preceding middle length).
* If the limsup at travel time `s ≥ 1` exceeded `C e^{-κ s}`, a subsequence would stay above a
  level `c' > C e^{-κ s}`; a further subsequence has a critical limit with clock measures
  (`NsCriticalClockLimitsExist`); along it the upper passage (`ns_limsup_fracTrace_le`, small
  eigenvalues cut by the small-channel bound with the smaller power `p/2`, large ones by
  `E (Tr A)²`) gives `c' ≤ E H_p(μ_{t₀+s})`, `limitDecay` gives
  `≤ e^{-κ(s-1)} E H_p(μ_{t₀+1})`, and the lower passage of the entrance bound gives
  `≤ e^{-κ(s-1)} C₁ ≤ C e^{-κ s}`, a contradiction. The width `W` is never interchanged with an
  unbounded time.
* A source whose injection ends at time `0` vanishes at every width `W ≥ 1`
  (`ns_clockFracMoment_eq_zero_of_origin`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Matrix Filter Topology Set
open scoped ENNReal
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Endpoints

/-- A unit source with `t₁ + R = 0` is supported at `0`, so its clock vanishes at every width
`W ≥ 1` and every length: `E H_p = 0` (`p > 0`). -/
theorem ns_clockFracMoment_eq_zero_of_origin {b E p : ℝ} (hp : 0 < p) {t₁ R : ℝ} {q : ℝ → ℝ}
    (hq : IsUnitSource t₁ R q) (h0 : t₁ + R = 0) {W : ℕ} (hW : 1 ≤ W) (s : ℝ) :
    clockFracMoment b E p W t₁ R s q = 0 := by
  have ht₁ : t₁ = 0 := by linarith [hq.1, hq.2.1]
  have hR : R = 0 := by linarith [hq.1, hq.2.1]
  have hsupp := hq.2.2.2.1.2.1
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hQ : ∀ j ω, intervalSource b E W j q ω = 0 := by
    intro j ω
    unfold intervalSource
    refine Finset.sum_eq_zero fun k _ => ?_
    have hx : ((k + 1 : ℕ) : ℝ) / W ∉ Icc t₁ (t₁ + R) := by
      rw [ht₁, hR, add_zero, Icc_self, mem_singleton_iff]
      exact (div_pos (by positivity) hW0).ne'
    rw [hsupp _ hx, zero_div, Complex.ofReal_zero, zero_smul]
  have hA : ∀ j ω, nearClock b E W j q ω = 0 := by
    intro j ω
    unfold nearClock
    rw [hQ]
    ext x y
    simp [portBlock]
  have hfr : fracTrace p (0 : Matrix (Fin W) (Fin W) ℂ) = 0 := by
    have h := fracTrace_smul (isHermitian_zero (n := Fin W) (α := ℂ)) (le_refl (0 : ℝ)) p
    rw [Complex.ofReal_zero, zero_smul, Real.zero_rpow hp.ne', zero_mul] at h
    exact h
  unfold clockFracMoment
  simp_rw [hA, hfr, ENNReal.ofReal_zero, lintegral_zero]

/-- **The `limsupDecay` clause** of the `NearSchattenDecayContract`:
for every `0 < p < 1` there is `C`, chosen before the source, the preceding middle length and
the travel time, with `limsup_W E H_p(s) ≤ C e^{-Dp(1-p)s/2}` at every travel time `s ≥ 1`.
-/
theorem ns_limsupDecay (hEnt : ClockFractionalEntranceContract)
    (hRG : NsRegularizedLimitGenerator) (hGen : FullSourceGeneratorContract)
    (hEx : NsCriticalClockLimitsExist) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ p : ℝ, 0 < p → p < 1 →
      ∃ C : ℝ, ∀ (t₁ R : ℝ) (q : ℝ → ℝ), IsUnitSource t₁ R q → ∀ s : ℝ, 1 ≤ s →
        limsup (fun W : ℕ => clockFracMoment b E p W t₁ R s q) atTop ≤
          ENNReal.ofReal (C * Real.exp (-(transportD0 b E * p * (1 - p) * s / 2))) := by
  intro b hb hb' E hE hE' p hp hp1
  set κ := transportD0 b E * p * (1 - p) / 2 with hκ
  obtain ⟨C₁, hC₁⟩ := hEnt.later b hb hb' E hE hE' p hp hp1 1 1 one_pos le_rfl
  refine ⟨max C₁ 0 * Real.exp κ, fun t₁ R q hq s hs => ?_⟩
  have ht₀ : 0 ≤ t₁ + R := by linarith [hq.1, hq.2.1]
  rcases ht₀.eq_or_lt with h0 | hpos
  · have hev : (fun W : ℕ => clockFracMoment b E p W t₁ R s q) =ᶠ[atTop] fun _ => 0 :=
      eventually_atTop.2 ⟨1, fun W hW => ns_clockFracMoment_eq_zero_of_origin hp hq h0.symm hW s⟩
    rw [limsup_congr hev, limsup_const]
    exact zero_le
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨c', hc'1, hc'2⟩ := exists_between hlt
  have hfreq : ∃ᶠ W in atTop, c' < clockFracMoment b E p W t₁ R s q :=
    frequently_lt_of_lt_limsup (by isBoundedDefault) hc'2
  obtain ⟨ψ, hψ, hψc⟩ := extraction_of_frequently_atTop hfreq
  obtain ⟨φ, hφ, Ω, _, P, Z, μ, hWL, hfdd, hμ⟩ := hEx b hb hb' E hE hE' t₁ R q hq hpos ψ hψ
  have hP := hWL.prob
  have hqnn := ns_isUnitSource_nonneg hq
  have hq1 : ∀ x, q x ≤ 1 := hq.2.2.2.2
  have hmeas : ∀ u, t₁ + R ≤ u → ∀ k, 1 ≤ k → Measurable (Z (clockWord k) u) := fun u hu k hk =>
    hWL.measurable _ (ns_isOrdinaryWord_clockWord hk) u hu
  have hmono := hψ.comp hφ
  -- the upper passage at travel time `s`
  set p₀ := p / 2 with hp₀
  have hp₀0 : 0 < p₀ := by positivity
  have hp₀p : p₀ < p := by linarith
  obtain ⟨C₀, hC₀⟩ := hEnt.later b hb hb' E hE hE' p₀ hp₀0 (by linarith) s s (by linarith) le_rfl
  obtain ⟨W₀, hW₀⟩ := hC₀ t₁ R q hq
  obtain ⟨C₂, W₂, hC₂⟩ := ns_trace_sq_bound hGen.moments hb hb' hE hE' (u := t₁ + R + s)
    (by linarith)
  have hus : t₁ + R ≤ t₁ + R + s := by linarith
  have hupper := ns_limsup_fracTrace_le hqnn hus (hmeas _ hus) hmono hfdd (hμ _ hus) hp₀0 hp₀p hp1
    (C₀ := C₀) (C₂ := C₂)
    (eventually_atTop.2 ⟨W₀, fun W hW => by
      have h := hW₀ W hW s ⟨le_rfl, le_rfl⟩
      unfold clockFracMoment travelLength at h
      exact h⟩)
    (eventually_atTop.2 ⟨W₂, fun W hW => hC₂ W hW q hqnn hq1⟩)
  -- the lower bound `c' ≤ limsup` along the subsequence
  have hlow : c' ≤ limsup (fun n => ∫⁻ ω, ENNReal.ofReal
      (fracTrace p (nearClock b E ((ψ ∘ φ) n) ⌊((ψ ∘ φ) n : ℝ) * (t₁ + R + s)⌋₊ q ω))
        ∂growthPathLaw ((ψ ∘ φ) n) b) atTop :=
    le_limsup_of_frequently_le (Frequently.of_forall fun n => by
      have h := (hψc (φ n)).le
      unfold clockFracMoment travelLength at h
      exact h) (by isBoundedDefault)
  -- `limitDecay` from travel time `1` to `s`
  have hdec := ns_limitDecay hEnt hRG b hb hb' E hE hE' p hp hp1 t₁ R q hq Ω _ P Z hWL μ hμ 1
    (s - 1) one_pos (by linarith)
  have hts : t₁ + R + 1 + (s - 1) = t₁ + R + s := by ring
  rw [hts] at hdec
  -- the entrance bound at travel time `1`, passed to the limit
  obtain ⟨W₁, hW₁⟩ := hC₁ t₁ R q hq
  have h1 : t₁ + R ≤ t₁ + R + 1 := by linarith
  have hent := ns_lintegral_limitFracTrace_le hqnn h1 (hmeas _ h1) hmono hfdd (hμ _ h1) hp hp1
    (C := ENNReal.ofReal C₁) (eventually_atTop.2 ⟨W₁, fun W hW => by
      have h := hW₁ W hW 1 ⟨le_rfl, le_rfl⟩
      unfold clockFracMoment travelLength at h
      exact h⟩)
  -- the chain of inequalities
  have hexp : Real.exp (-(transportD0 b E * p * (1 - p) * (s - 1) / 2)) =
      Real.exp κ * Real.exp (-(transportD0 b E * p * (1 - p) * s / 2)) := by
    rw [← Real.exp_add, hκ]; ring_nf
  have hfinal : c' ≤ ENNReal.ofReal (max C₁ 0 * Real.exp κ *
      Real.exp (-(transportD0 b E * p * (1 - p) * s / 2))) := by
    calc c' ≤ _ := hlow
      _ ≤ ∫⁻ ω, limitFracTrace p (μ (t₁ + R + s) ω) ∂P := hupper
      _ ≤ ENNReal.ofReal (Real.exp (-(transportD0 b E * p * (1 - p) * (s - 1) / 2))) *
            ∫⁻ ω, limitFracTrace p (μ (t₁ + R + 1) ω) ∂P := hdec
      _ ≤ ENNReal.ofReal (Real.exp (-(transportD0 b E * p * (1 - p) * (s - 1) / 2))) *
            ENNReal.ofReal (max C₁ 0) := by
          gcongr
          exact hent.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
      _ = _ := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, hexp]
          ring_nf
  exact absurd (hc'1.trans_le hfinal) (lt_irrefl _)

end BlockBand.Endpoints
