module

public import BlockBand.Native.CEH.LocalLaw.Holds

/-!
# CEH ETH: the single-resolvent tube along the characteristic flow

## Main results

* `flowTube_holds` (hypothesis-free): for all `ε, ζ, D > 0` there is `N₀` such that for
  `N ≥ N₀`, every such probability space, `s > 0`, `F`, `z`, `Mz` with `N^ε ≤ N η ρ`,
  `Q {∃ t ∈ [0, s], N^ζ/(N η_t) < ‖⟨R_t⟩ - m‖ ∨ c/2 < ‖⟨R_t⟩ - m‖} ≤ N^{-D}`.
  The tube exponent `ζ > 0` is arbitrary (independent of `ε`).
* `flowTube_holds_flowResolvent`: the same, written with `flowResolvent F G z m s σ ω` for
  `σ : ℝ≥0`, `σ ≤ s`, with the extra consequence `|Im ⟨R_σ⟩| ≤ 3c/2` in the good event
  (`abs_im_le_of_norm_sub_le`; hence `≤ 2c`).

**Measure.** `Q` (any probability measure carrying `G`); `Q` is applied to arbitrary sets (outer
measure). **Norms.** `‖·‖` on `ℂ`. **Uniformity.** `N₀` depends only on `ε, ζ, D`; the bound is
uniform in the probability space, `s`, `F`, `z`, `Mz`. The hypotheses `0 < s` and `0 < D` of
`flowTube_holds` are part of the requested packaging and are not used.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.ETH

open MeasureTheory Set
open BlockBand.External.CEH BlockBand.Native.CEH.Phase1 BlockBand.Native.CEH.Flow
open BlockBand.Native.CEH.Zig BlockBand.Native.CEH.LocalLaw
open BlockBand.Internal.Contracts.Transmission BlockBand.Internal.Contracts.Inputs
open scoped NNReal ENNReal

variable {Ω : Type} {N : ℕ}

/-!
## Deterministic corollaries
-/

/-- `‖X - m‖ ≤ |Im m|/2 ⟹ |Im X| ≤ 3|Im m|/2`. -/
theorem abs_im_le_of_norm_sub_le {X m : ℂ} (h : ‖X - m‖ ≤ |m.im| / 2) :
    |X.im| ≤ 3 / 2 * |m.im| := by
  have := abs_im_le_add_norm_sub X m
  linarith

/-- `‖X - m‖ ≤ |Im m|/2 ⟹ |Im X| ≤ 2|Im m|`. -/
theorem abs_im_le_two_mul_of_norm_sub_le {X m : ℂ} (h : ‖X - m‖ ≤ |m.im| / 2) :
    |X.im| ≤ 2 * |m.im| := by
  have := abs_im_le_of_norm_sub_le h
  linarith [abs_nonneg m.im]

/-- The sample path at a time `σ : ℝ≥0` is the flow resolvent at `σ`. -/
theorem pathR_coe_eq_flowResolvent (F : Matrix (Fin N) (Fin N) ℂ)
    (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (z m : ℂ) (s : ℝ≥0) (ω : Ω) (σ : ℝ≥0) :
    pathR F G z m s ω (σ : ℝ) = flowResolvent F G z m s σ ω := by
  simp only [pathR, Real.toNNReal_coe]

/-!
## Fixed data
-/

section Fixed

variable [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ}

/-- **Single-resolvent flow tube for fixed data.** Simultaneously for all `t ∈ [0, s]`,
`‖⟨R_t⟩ - m‖ ≤ 2K(1 + log(η_0/η_t))/(N η_t)` and `‖⟨R_t⟩ - m‖ ≤ c/2`, except on an event of
probability `≤ (2N + 4) · 2 exp(-K²/64)`. -/
theorem flowTube_core (hG : IsHermitianBrownian Q 𝓖 N G) (hN : 0 < N) {F : SourceHermitian N}
    {s : ℝ≥0} {z : ℂ} {Mz : Matrix (Fin N) (Fin N) ℂ} (hMDE : IsManuscriptMDE (s : ℝ) F z Mz)
    (hz : z.im ≠ 0) {ρ θ K : ℝ} (hK : 0 < K) (hρ : 0 < ρ)
    (hρc : ρ ≤ |(normalizedTrace Mz).im|)
    (hL : zigHeight |z.im| |(normalizedTrace Mz).im| s 0 ≤ 2 ^ N * |z.im|)
    (hsmall₁ : 4 * K * (1 + Real.log (zigHeight |z.im| |(normalizedTrace Mz).im| s 0 / |z.im|)) <
      θ)
    (hsmall₂ : 2 * θ ≤ N * |(normalizedTrace Mz).im| * |z.im|)
    (hsmall₃ : θ ^ 2 * ρ ≤ K ^ 2 * |(normalizedTrace Mz).im| ^ 2 * (N * |z.im|))
    (hsmall₄ : θ ^ 2 ≤ N * |z.im| * ρ) :
    Q {ω | ∃ t ∈ Icc 0 (s : ℝ),
        ¬ (‖normalizedTrace (pathR F.1 G z (normalizedTrace Mz) s ω t) - normalizedTrace Mz‖ ≤
            2 * K * (1 + Real.log (zigHeight |z.im| |(normalizedTrace Mz).im| s 0 /
              zigHeight |z.im| |(normalizedTrace Mz).im| s t)) /
              (N * zigHeight |z.im| |(normalizedTrace Mz).im| s t) ∧
          ‖normalizedTrace (pathR F.1 G z (normalizedTrace Mz) s ω t) - normalizedTrace Mz‖ ≤
            |(normalizedTrace Mz).im| / 2)} ≤
      ENNReal.ofReal (((2 * N + 4 : ℕ) : ℝ) * (2 * Real.exp (-(K ^ 2 / 64)))) := by
  have hs0 : (0 : ℝ) ≤ s := s.2
  set m := normalizedTrace Mz with hmdef
  set η := |z.im| with hηdef
  set c := |m.im| with hcdef
  have hη : 0 < η := abs_pos.2 hz
  have hc : 0 < c := abs_im_trace_pos hN hMDE
  have hη0 : 0 < zigHeight η c s 0 := zigHeight_pos hη hc.le hs0
  have hcount : ((Fintype.card Empty + 1) * ((N + 1) * 2) + 2 : ℕ) = 2 * N + 4 := by
    simp only [Fintype.card_eq_zero, zero_add]
    ring
  have hqav : ∀ k : ℕ, 0 < K / (4 * N * (zigHeight η c s 0 / 2 ^ k)) ∧
      0 < 2 / ((N : ℝ) ^ 2 * (zigHeight η c s 0 / 2 ^ k) ^ 2) ∧
      K ^ 2 / 64 ≤ (K / (4 * N * (zigHeight η c s 0 / 2 ^ k))) ^ 2 /
        (2 * (2 / ((N : ℝ) ^ 2 * (zigHeight η c s 0 / 2 ^ k) ^ 2))) := by
    intro k
    have hh : 0 < zigHeight η c s 0 / 2 ^ k := by positivity
    refine ⟨by positivity, by positivity, le_of_eq ?_⟩
    field_simp
    ring
  rw [← hcount]
  refine measure_le_of_martGood hG hN hMDE hz (Empty.elim : Empty → Fin N → ℂ)
    (fun k => K / (4 * N * (zigHeight η c s 0 / 2 ^ k)))
    (fun k => 2 / ((N : ℝ) ^ 2 * (zigHeight η c s 0 / 2 ^ k) ^ 2))
    (fun _ _ => 1) (fun _ _ => 1) (avgK N)
    (K / (4 * N * (zigHeight η c s 0 / 2 ^ 0)))
    (2 / ((N : ℝ) ^ 2 * (zigHeight η c s 0 / 2 ^ 0) ^ 2)) (K ^ 2 / 64) hqav
    (fun i => i.elim) (hqav 0) _ ?_
  intro ω hω hav _ _
  have hP := flowPath_pathR hG hN hMDE hz ω
  have hmon := hP.monitored (Empty.elim : Empty → Fin N → ℂ) hN hρ hρc hK.le
    (fun i => i.elim) hL hsmall₁ hsmall₂ hsmall₃ hsmall₄ hav (fun i => i.elim)
  obtain ⟨t, ht, hnot⟩ := hω
  exact hnot ⟨(hmon t ht).1, (hmon t ht).2.1⟩

end Fixed

/-!
## Asymptotic form
-/

/-- **Single-resolvent flow tube** (CEH (6.2) along the whole flow), hypothesis-free.

For `ε, ζ, D > 0` there is `N₀` such that for `N ≥ N₀`, every filtered probability space with a
Hermitian Brownian motion `G`, `s > 0`, Hermitian `F`, nonreal `z` and MDE solution `Mz` at
`(s, F, z)` with `N^ε ≤ N |Im z| ρ` (`ρ = sourceDensity Mz`): with `m = ⟨Mz⟩`, `c = |Im m|`,
`η_t = zigHeight |Im z| c s t`, the event that for some `t ∈ [0, s]`
`‖⟨R_t⟩ - m‖ > N^ζ / (N η_t)` or `‖⟨R_t⟩ - m‖ > c/2` has probability `≤ N^{-D}`.
`ζ > 0` is arbitrary. The hypotheses `0 < s`, `0 < D` are not used. -/
theorem flowTube_holds : ∀ ε ζ D : ℝ, 0 < ε → 0 < ζ → 0 < D → ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {Ω : Type} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
      (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
      (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ), IsHermitianBrownian Q 𝓖 N G →
    ∀ (s : ℝ≥0), 0 < (s : ℝ) → ∀ (F : SourceHermitian N) (z : ℂ)
      (Mz : Matrix (Fin N) (Fin N) ℂ), IsManuscriptMDE (s : ℝ) F z Mz → z.im ≠ 0 →
      (N : ℝ) ^ ε ≤ N * |z.im| * sourceDensity Mz →
    Q {ω | ∃ t ∈ Icc 0 (s : ℝ),
        (N : ℝ) ^ ζ / (N * zigHeight |z.im| |(normalizedTrace Mz).im| s t) <
          ‖normalizedTrace (pathR F.1 G z (normalizedTrace Mz) s ω t) - normalizedTrace Mz‖ ∨
        |(normalizedTrace Mz).im| / 2 <
          ‖normalizedTrace (pathR F.1 G z (normalizedTrace Mz) s ω t) - normalizedTrace Mz‖} ≤
      ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
  intro ε ζ D hε hζ _hD
  set ξ := min ε ζ / 10 with hξdef
  have hξ : 0 < ξ := by positivity
  have hξε : ξ ≤ ε / 10 := by rw [hξdef]; gcongr; exact min_le_left _ _
  have hξζ : ξ ≤ ζ / 10 := by rw [hξdef]; gcongr; exact min_le_right _ _
  have hev := ((eventually_nat_add_mul_log_lt hξ (6 + 4 * Real.log 2) 4).and
    (eventually_nat_add_mul_log_lt (by positivity : (0 : ℝ) < 2 * ξ) (64 * Real.log 32)
      (64 * (2 + D)))).and (Filter.eventually_ge_atTop 1)
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 hev
  refine ⟨N₁, ?_⟩
  intro N hN Ω _ Q _ 𝓖 G hG s _hs F z Mz hMDE hz hdom
  obtain ⟨⟨hE1, hE2⟩, hN1⟩ := hN₁ N hN
  have hNpos : 0 < N := hN1
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hNpos
  have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  set m := normalizedTrace Mz with hmdef
  set η := |z.im| with hηdef
  set c := |m.im| with hcdef
  set ρ := sourceDensity Mz with hρdef
  have hη : 0 < η := abs_pos.2 hz
  have hc : 0 < c := abs_im_trace_pos hNpos hMDE
  have hcπ : c = Real.pi * ρ := abs_im_normalizedTrace_eq_pi_mul_sourceDensity Mz
  have hρ : 0 < ρ := by
    rw [hcπ] at hc
    exact pos_of_mul_pos_right hc Real.pi_pos.le
  have hNε1 : (1 : ℝ) ≤ (N : ℝ) ^ ε := Real.one_le_rpow hNr1 hε.le
  have hNηρ : 1 ≤ (N : ℝ) * η * ρ := hNε1.trans hdom
  -- parameters `K = N^ξ`, `θ = K²`
  set K := (N : ℝ) ^ ξ with hKdef
  have hK : 0 < K := Real.rpow_pos_of_pos hNr ξ
  have hK2 : K ^ 2 = (N : ℝ) ^ (2 * ξ) := by
    rw [hKdef, ← Real.rpow_two, ← Real.rpow_mul hNr.le, mul_comm]
  have hK4 : (K ^ 2) ^ 2 = (N : ℝ) ^ (4 * ξ) := by
    rw [hK2, ← Real.rpow_two, ← Real.rpow_mul hNr.le]
    congr 1
    ring
  have hK2ε : K ^ 2 ≤ (N : ℝ) ^ ε := hK2 ▸ Real.rpow_le_rpow_of_exponent_le hNr1 (by linarith)
  have hK4ε : (K ^ 2) ^ 2 ≤ (N : ℝ) ^ ε :=
    hK4 ▸ Real.rpow_le_rpow_of_exponent_le hNr1 (by linarith)
  have hK2ζ : K ^ 2 ≤ (N : ℝ) ^ ζ := hK2 ▸ Real.rpow_le_rpow_of_exponent_le hNr1 (by linarith)
  -- the height ratio `η_0 / η ≤ 1 + N ≤ 2^N`
  have hts : (0 : ℝ) ≤ s := s.2
  have hdens := density_sq_mul_le hMDE hz hts hNpos
  have hcs : c * s ≤ N * η := by
    have h1 : 1 ≤ (N : ℝ) * η * c := by
      have e : (N : ℝ) * η * c = Real.pi * (N * η * ρ) := by rw [hcπ]; ring
      rw [e]
      exact hNηρ.trans (le_mul_of_one_le_left (by positivity) (by linarith [Real.pi_gt_three]))
    calc c * s = c * s * 1 := (mul_one _).symm
      _ ≤ c * s * (N * η * c) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (c ^ 2 * s) * (N * η) := by ring
      _ ≤ 1 * (N * η) := mul_le_mul_of_nonneg_right hdens (by positivity)
      _ = N * η := one_mul _
  have hη0 : zigHeight η c s 0 ≤ (1 + N) * η := by
    have e : (1 + (N : ℝ)) * η = η + N * η := by ring
    rw [zigHeight, sub_zero, e]
    linarith
  have hpow : (1 + (N : ℝ)) ≤ 2 ^ N := by
    have : N + 1 ≤ 2 ^ N := Nat.lt_two_pow_self
    exact_mod_cast (by omega : 1 + N ≤ 2 ^ N)
  have hL : zigHeight η c s 0 ≤ 2 ^ N * η :=
    hη0.trans (mul_le_mul_of_nonneg_right hpow hη.le)
  have hη0pos : 0 < zigHeight η c s 0 := zigHeight_pos hη hc.le hts
  have hLg : Real.log (zigHeight η c s 0 / η) ≤ Real.log 2 + Real.log N := by
    rw [← Real.log_mul (by norm_num) hNr.ne']
    refine Real.log_le_log (div_pos hη0pos hη) ?_
    rw [div_le_iff₀ hη]
    exact hη0.trans (mul_le_mul_of_nonneg_right (by linarith) hη.le)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hNr1
  have hKbig : 6 + 4 * Real.log (zigHeight η c s 0 / η) < K := by linarith
  -- smallness conditions of `FlowPath.monitored`, with `ρ = sourceDensity Mz`
  have hsmall₁ : 4 * K * (1 + Real.log (zigHeight η c s 0 / η)) < K ^ 2 := by
    have h4 : 4 * (1 + Real.log (zigHeight η c s 0 / η)) < K := by
      have := Real.log_nonneg ((one_le_div hη).2 (le_zigHeight hc.le hts))
      linarith
    calc 4 * K * (1 + Real.log (zigHeight η c s 0 / η))
        = K * (4 * (1 + Real.log (zigHeight η c s 0 / η))) := by ring
      _ < K * K := mul_lt_mul_of_pos_left h4 hK
      _ = K ^ 2 := (sq K).symm
  have hNcη : (N : ℝ) * c * η = Real.pi * (N * η * ρ) := by rw [hcπ]; ring
  have hKρ : K ^ 2 ≤ N * η * ρ := hK2ε.trans hdom
  have hsmall₂ : 2 * K ^ 2 ≤ N * c * η := by
    rw [hNcη]
    calc 2 * K ^ 2 ≤ 2 * (N * η * ρ) := by linarith
      _ ≤ Real.pi * (N * η * ρ) :=
        mul_le_mul_of_nonneg_right (by linarith [Real.pi_gt_three]) (by positivity)
  have hsmall₃ : (K ^ 2) ^ 2 * ρ ≤ K ^ 2 * c ^ 2 * (N * η) := by
    have hpi : (1 : ℝ) ≤ Real.pi ^ 2 := by
      have := Real.pi_gt_three
      nlinarith
    have h1 : K ^ 2 ≤ Real.pi ^ 2 * (N * η * ρ) :=
      hKρ.trans (le_mul_of_one_le_left (by positivity) hpi)
    have h2 : K ^ 2 * c ^ 2 * (N * η) = K ^ 2 * (Real.pi ^ 2 * (N * η * ρ)) * ρ := by
      rw [hcπ]; ring
    rw [h2, sq (K ^ 2)]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (sq_nonneg K)) hρ.le
  have hsmall₄ : (K ^ 2) ^ 2 ≤ N * η * ρ := hK4ε.trans hdom
  have hρc : ρ ≤ c := by
    rw [hcπ]; exact le_mul_of_one_le_left hρ.le (by linarith [Real.pi_gt_three])
  -- the tube width: `2K(1 + log(η_0/η_t)) ≤ K² ≤ N^ζ`
  have hwidth : ∀ t ∈ Icc 0 (s : ℝ),
      2 * K * (1 + Real.log (zigHeight η c s 0 / zigHeight η c s t)) ≤ (N : ℝ) ^ ζ := by
    intro t ht
    have hηt : 0 < zigHeight η c s t := zigHeight_pos hη hc.le ht.2
    have hle : Real.log (zigHeight η c s 0 / zigHeight η c s t) ≤
        Real.log (zigHeight η c s 0 / η) :=
      Real.log_le_log (div_pos hη0pos hηt)
        (div_le_div_of_nonneg_left hη0pos.le hη (le_zigHeight hc.le ht.2))
    have h6 : 2 * (1 + Real.log (zigHeight η c s 0 / zigHeight η c s t)) ≤ K := by linarith
    calc 2 * K * (1 + Real.log (zigHeight η c s 0 / zigHeight η c s t))
        = K * (2 * (1 + Real.log (zigHeight η c s 0 / zigHeight η c s t))) := by ring
      _ ≤ K * K := mul_le_mul_of_nonneg_left h6 hK.le
      _ = K ^ 2 := (sq K).symm
      _ ≤ _ := hK2ζ
  -- the final numerical bound
  have hprob : ENNReal.ofReal (((2 * N + 4 : ℕ) : ℝ) * (2 * Real.exp (-(K ^ 2 / 64)))) ≤
      ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
    refine ENNReal.ofReal_le_ofReal ?_
    have hn' : (((2 * N + 4 : ℕ) : ℝ)) ≤ 16 * (N : ℝ) ^ 2 := by
      push_cast
      nlinarith
    have h := prob_small hN1 (X := K ^ 2) (D := D) (by rw [hK2]; exact hE2)
    calc (((2 * N + 4 : ℕ) : ℝ)) * (2 * Real.exp (-(K ^ 2 / 64)))
        ≤ 16 * (N : ℝ) ^ 2 * (2 * Real.exp (-(K ^ 2 / 64))) := by gcongr
      _ = 32 * (N : ℝ) ^ 2 * Real.exp (-(K ^ 2 / 64)) := by ring
      _ ≤ _ := h
  refine le_trans (measure_mono ?_) ((flowTube_core hG hNpos hMDE hz hK hρ hρc hL
    hsmall₁ hsmall₂ hsmall₃ hsmall₄).trans hprob)
  intro ω hω
  obtain ⟨t, ht, hbad⟩ := hω
  refine ⟨t, ht, fun ⟨h1, h2⟩ => ?_⟩
  have hηt : 0 < zigHeight η c s t := zigHeight_pos hη hc.le ht.2
  have h1' : ‖normalizedTrace (pathR F.1 G z m s ω t) - m‖ ≤
      (N : ℝ) ^ ζ / (N * zigHeight η c s t) :=
    h1.trans (div_le_div_of_nonneg_right (hwidth t ht) (by positivity))
  rcases hbad with hb | hb <;> linarith

/-- **Single-resolvent flow tube, flow-resolvent form.** As `flowTube_holds`, written with
`R_σ = flowResolvent F G z m s σ ω` for `σ : ℝ≥0`, `σ ≤ s`,
with the corollary `|Im ⟨R_σ⟩| ≤ 3c/2` (`c = |Im m| = π ρ`) included in the good event. -/
theorem flowTube_holds_flowResolvent : ∀ ε ζ D : ℝ, 0 < ε → 0 < ζ → 0 < D → ∃ N₀ : ℕ,
    ∀ N ≥ N₀,
    ∀ {Ω : Type} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
      (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
      (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ), IsHermitianBrownian Q 𝓖 N G →
    ∀ (s : ℝ≥0), 0 < (s : ℝ) → ∀ (F : SourceHermitian N) (z : ℂ)
      (Mz : Matrix (Fin N) (Fin N) ℂ), IsManuscriptMDE (s : ℝ) F z Mz → z.im ≠ 0 →
      (N : ℝ) ^ ε ≤ N * |z.im| * sourceDensity Mz →
    Q {ω | ∃ σ : ℝ≥0, σ ≤ s ∧
        ¬ (‖normalizedTrace (flowResolvent F.1 G z (normalizedTrace Mz) s σ ω) -
              normalizedTrace Mz‖ ≤
            (N : ℝ) ^ ζ / (N * zigHeight |z.im| |(normalizedTrace Mz).im| s σ) ∧
          ‖normalizedTrace (flowResolvent F.1 G z (normalizedTrace Mz) s σ ω) -
              normalizedTrace Mz‖ ≤ |(normalizedTrace Mz).im| / 2 ∧
          |(normalizedTrace (flowResolvent F.1 G z (normalizedTrace Mz) s σ ω)).im| ≤
            3 / 2 * |(normalizedTrace Mz).im|)} ≤
      ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
  intro ε ζ D hε hζ hD
  obtain ⟨N₀, hN₀⟩ := flowTube_holds ε ζ D hε hζ hD
  refine ⟨N₀, ?_⟩
  intro N hN Ω _ Q _ 𝓖 G hG s hs F z Mz hMDE hz hdom
  refine le_trans (measure_mono ?_) (hN₀ N hN Q 𝓖 G hG s hs F z Mz hMDE hz hdom)
  intro ω hω
  obtain ⟨σ, hσ, hbad⟩ := hω
  refine ⟨(σ : ℝ), ⟨σ.2, NNReal.coe_le_coe.2 hσ⟩, ?_⟩
  rw [pathR_coe_eq_flowResolvent]
  by_contra hgood
  push Not at hgood
  exact hbad ⟨hgood.1, hgood.2, abs_im_le_of_norm_sub_le hgood.2⟩

end BlockBand.Native.CEH.ETH
