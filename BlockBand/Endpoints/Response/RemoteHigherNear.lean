module

public import BlockBand.Endpoints.Response.RemoteHigherNearLater
public import BlockBand.Endpoints.Response.RemoteHigherNearPassage
public import BlockBand.Endpoints.Response.NearSchattenLimsup
public import BlockBand.Endpoints.Response.RemoteHigher

/-!
# Decay of higher moments of a near clock

* `rhn_nearHigherLimsupDecay`: `RhNearHigherLimsupDecay` from the higher entrance bound
  `RhnHigherLater` and the limiting decay `RhHigherLimitDecay`, by contradiction along a critical
  limit (as in `ns_limsupDecay`).
* `rhn_nearHigherLimsupDecay_of_recursion`: the same from the finite-`W` weighted recursion
  `RhnHigherWeightedRecursion` (through `rhn_higherLater_of_recursion`).
* `remoteHigher_of_recursion`: `RemoteHigherStatement` from the recursion and
  `RhHigherLimitDecay`.
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
`W ≥ 1` and every length, and so does `E (Tr A^p)^r` (`p, r > 0`). -/
theorem rhn_lintegral_rpow_eq_zero_of_origin {b E p r : ℝ} (hp : 0 < p) (hr : 0 < r)
    {t₁ R : ℝ} {q : ℝ → ℝ} (hq : IsUnitSource t₁ R q) (h0 : t₁ + R = 0) {W : ℕ} (hW : 1 ≤ W)
    (j : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (fracTrace p (nearClock b E W j q ω)) ^ r ∂growthPathLaw W b = 0 := by
  have ht₁ : t₁ = 0 := by linarith [hq.1, hq.2.1]
  have hR : R = 0 := by linarith [hq.1, hq.2.1]
  have hsupp := hq.2.2.2.1.2.1
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hQ : ∀ ω, intervalSource b E W j q ω = 0 := by
    intro ω
    unfold intervalSource
    refine Finset.sum_eq_zero fun k _ => ?_
    have hx : ((k + 1 : ℕ) : ℝ) / W ∉ Icc t₁ (t₁ + R) := by
      rw [ht₁, hR, add_zero, Icc_self, mem_singleton_iff]
      exact (div_pos (by positivity) hW0).ne'
    rw [hsupp _ hx, zero_div, Complex.ofReal_zero, zero_smul]
  have hA : ∀ ω, nearClock b E W j q ω = 0 := by
    intro ω
    unfold nearClock
    rw [hQ]
    ext x y
    simp [portBlock]
  have hfr : fracTrace p (0 : Matrix (Fin W) (Fin W) ℂ) = 0 := by
    have h := fracTrace_smul (isHermitian_zero (n := Fin W) (α := ℂ)) (le_refl (0 : ℝ)) p
    rw [Complex.ofReal_zero, zero_smul, Real.zero_rpow hp.ne', zero_mul] at h
    exact h
  simp_rw [hA, hfr, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos hr, lintegral_zero]

/-- **`RhNearHigherLimsupDecay`** (exponentially decreasing travel bounds) from the finite-`W`
higher bounds `RhnHigherLater`, the limiting decay `RhHigherLimitDecay`,
`FullSourceGeneratorContract` (only `moments`) and the existence of critical limits
`NsCriticalClockLimitsExist`. Rate `c = D₀ r p (1 - rp)/2`.
-/
theorem rhn_nearHigherLimsupDecay (hLater : RhnHigherLater) (hL : RhHigherLimitDecay)
    (hGen : FullSourceGeneratorContract) (hEx : NsCriticalClockLimitsExist) :
    RhNearHigherLimsupDecay := by
  intro b hb hb' E hE hE' p r hp hp1 hr hpr
  have hr0 : 0 < r := by linarith
  set κ := transportD0 b E * r * p * (1 - r * p) / 2 with hκ
  have hκ0 : 0 < κ := by
    have := ns_transportD0_pos hb hE hE'
    have : 0 < 1 - r * p := by linarith [mul_comm p r]
    positivity
  obtain ⟨C₁, hC₁⟩ := hLater b hb hb' E hE hE' p r hp hp1 hr hpr 1 1 one_pos le_rfl
  set K₃ : ℝ := (3 : ℝ) ^ r * (2 : ℝ) ^ (r - 1) with hK₃
  have hK₃0 : 0 ≤ K₃ := by positivity
  refine ⟨K₃ * max C₁ 0 * Real.exp κ, κ, hκ0, fun t₁ R q hq s hs => ?_⟩
  have ht₀ : 0 ≤ t₁ + R := by linarith [hq.1, hq.2.1]
  rcases ht₀.eq_or_lt with h0 | hpos
  · have hev : (fun W : ℕ => ∫⁻ ω, ENNReal.ofReal
        (fracTrace p (nearClock b E W (travelLength W t₁ R s) q ω)) ^ r ∂growthPathLaw W b)
        =ᶠ[atTop] fun _ => 0 :=
      eventually_atTop.2 ⟨1, fun W hW =>
        rhn_lintegral_rpow_eq_zero_of_origin hp hr0 hq h0.symm hW _⟩
    rw [limsup_congr hev, limsup_const]
    exact zero_le
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨c', hc'1, hc'2⟩ := exists_between hlt
  have hfreq : ∃ᶠ W in atTop, c' < ∫⁻ ω, ENNReal.ofReal
      (fracTrace p (nearClock b E W (travelLength W t₁ R s) q ω)) ^ r ∂growthPathLaw W b :=
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
  have hp₀r : p₀ * r < 1 := by
    have : p₀ * r = p * r / 2 := by rw [hp₀]; ring
    rw [this]; linarith
  obtain ⟨C₀, hC₀⟩ := hLater b hb hb' E hE hE' p₀ r hp₀0 (by linarith) hr hp₀r s s (by linarith)
    le_rfl
  obtain ⟨W₀, hW₀⟩ := hC₀ t₁ R q hq
  obtain ⟨C₂, W₂, hC₂⟩ := rhn_trace_sq_rpow_bound hGen.moments hb hb' hE hE'
    (u := t₁ + R + s) (by linarith) (r := r) (by linarith)
  have hus : t₁ + R ≤ t₁ + R + s := by linarith
  have hupper := rhn_limsup_fracTrace_rpow_le hqnn hus (hmeas _ hus) hmono hfdd (hμ _ hus) hp₀0
    hp₀p hp1 hr (C₀ := C₀) (C₂ := C₂)
    (eventually_atTop.2 ⟨W₀, fun W hW => by
      have h := hW₀ W hW s ⟨le_rfl, le_rfl⟩
      unfold travelLength at h
      exact h⟩)
    (eventually_atTop.2 ⟨W₂, fun W hW => hC₂ W hW q hqnn hq1⟩)
  -- the lower bound `c' ≤ limsup` along the subsequence
  have hlow : c' ≤ limsup (fun n => ∫⁻ ω, ENNReal.ofReal
      (fracTrace p (nearClock b E ((ψ ∘ φ) n) ⌊((ψ ∘ φ) n : ℝ) * (t₁ + R + s)⌋₊ q ω)) ^ r
        ∂growthPathLaw ((ψ ∘ φ) n) b) atTop :=
    le_limsup_of_frequently_le (Frequently.of_forall fun n => by
      have h := (hψc (φ n)).le
      unfold travelLength at h
      exact h) (by isBoundedDefault)
  -- the limiting decay from travel time `1` to `s`
  have hdec := hL b hb hb' E hE hE' p r hp hp1 hr hpr t₁ R q hq Ω _ P Z hWL μ hμ 1 (s - 1)
    one_pos (by linarith)
  have hts : t₁ + R + 1 + (s - 1) = t₁ + R + s := by ring
  rw [hts] at hdec
  -- the finite-width bound at travel time `1`, passed to the limit
  obtain ⟨W₁, hW₁⟩ := hC₁ t₁ R q hq
  have h1 : t₁ + R ≤ t₁ + R + 1 := by linarith
  have hent := rhn_lintegral_limitFracTrace_rpow_le hqnn h1 (hmeas _ h1) hmono hfdd (hμ _ h1) hp
    hp1 hr0 (C := ENNReal.ofReal C₁) (eventually_atTop.2 ⟨W₁, fun W hW => by
      have h := hW₁ W hW 1 ⟨le_rfl, le_rfl⟩
      unfold travelLength at h
      exact h⟩)
  -- the chain of inequalities
  have hexp : Real.exp (-(transportD0 b E * r * p * (1 - r * p) * (s - 1) / 2)) =
      Real.exp κ * Real.exp (-(κ * s)) := by
    rw [← Real.exp_add, hκ]; ring_nf
  have h3 : (3 : ℝ≥0∞) ^ r * 2 ^ (r - 1) = ENNReal.ofReal K₃ := by
    rw [hK₃, ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_rpow_of_nonneg (by norm_num) hr0.le,
      ← ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by linarith)]
    norm_num
  have hfinal : c' ≤ ENNReal.ofReal (K₃ * max C₁ 0 * Real.exp κ * Real.exp (-(κ * s))) := by
    calc c' ≤ _ := hlow
      _ ≤ 3 ^ r * (2 ^ (r - 1) * ∫⁻ ω, limitFracTrace p (μ (t₁ + R + s) ω) ^ r ∂P) := hupper
      _ ≤ 3 ^ r * (2 ^ (r - 1) * (ENNReal.ofReal
            (Real.exp (-(transportD0 b E * r * p * (1 - r * p) * (s - 1) / 2))) *
            ENNReal.ofReal (max C₁ 0))) := by
          gcongr
          refine hdec.trans ?_
          gcongr
          exact hent.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
      _ = ENNReal.ofReal K₃ * (ENNReal.ofReal
            (Real.exp (-(transportD0 b E * r * p * (1 - r * p) * (s - 1) / 2))) *
            ENNReal.ofReal (max C₁ 0)) := by rw [← h3]; ring
      _ = _ := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul hK₃0, hexp]
          ring_nf
  exact absurd (hc'1.trans_le hfinal) (lt_irrefl _)

/-- **`RhNearHigherLimsupDecay` from the finite-`W` higher recursion**, the hypotheses
`RhHigherLimitDecay` and `NsCriticalClockLimitsExist`, and `FullSourceGeneratorContract`.
-/
theorem rhn_nearHigherLimsupDecay_of_recursion (hRec : RhnHigherWeightedRecursion)
    (hL : RhHigherLimitDecay) (hGen : FullSourceGeneratorContract)
    (hEx : NsCriticalClockLimitsExist) : RhNearHigherLimsupDecay :=
  rhn_nearHigherLimsupDecay (rhn_higherLater_of_recursion hRec) hL hGen hEx

/-- **The remote higher-order theorem** (`RemoteHigherStatement`) from the finite-`W` higher
recursion `RhnHigherWeightedRecursion`, the hypotheses `RhHigherLimitDecay` and
`NsCriticalClockLimitsExist`, and `FullSourceGeneratorContract`; composes
`rhn_nearHigherLimsupDecay_of_recursion` with `remoteHigher_holds`.
-/
theorem remoteHigher_of_recursion (hRec : RhnHigherWeightedRecursion) (hL : RhHigherLimitDecay)
    (hGen : FullSourceGeneratorContract) (hEx : NsCriticalClockLimitsExist) :
    RemoteHigherStatement :=
  remoteHigher_holds (rhn_nearHigherLimsupDecay_of_recursion hRec hL hGen hEx) hL

end BlockBand.Endpoints
