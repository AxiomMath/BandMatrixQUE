module

public import BlockBand.Native.CEH.LocalLaw.Tail
public import BlockBand.Native.CEH.LocalLaw.Controls

/-!
# CEH local law, assembly: the failure probability for fixed data

Setting: `(Ω, 𝓖, Q)` a filtered probability space, `G` a Hermitian Brownian motion, `N > 0`,
`s : ℝ≥0`, Hermitian `F`, `M` solving the MDE of the paper at `(s, F, z)`, `Im z ≠ 0`;
`m = ⟨M⟩`, `η = |Im z|`, `c = |Im m|`, `ρ = sourceDensity M`, `η_0 = η + c s`, flow resolvent
`R_s = (F + G_s - z)⁻¹ = pathR ω s`.

* `measure_le_of_martGood`: a union bound. If every `ω ∈ S` violates one of the `MartGood`
  conditions (averaged and diagonal quadratic forms on the height grid `η_0 / 2^k`, `k ≤ N`, and a
  target), then `Q S ≤ #events · 2 exp(-q)`, where `q ≤ a²/(2b)` for every event.
* `iso_core`, `avg_core`: for fixed data and parameters `K > 0`, `θ`, loss `Λ` satisfying the
  smallness conditions of `zig_bootstrap` and `2K + 4K(1 + log(η_0/η)) ≤ Λ`,
  `Q {Λ · isotropicControl < ‖x* (R_s - M) y‖} ≤ (6(N+1) + 2) · 2 exp(-K²/64)` and
  `Q {Λ · averagedControl < ‖⟨(R_s - M) B⟩‖} ≤ (2(N+1)² + 2) · 2 exp(-K²/64)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.LocalLaw

open Matrix MeasureTheory ProbabilityTheory Set
open BlockBand.External.CEH BlockBand.Native.CEH.Phase1 BlockBand.Native.CEH.Flow
open BlockBand.Native.CEH.Zig BlockBand.Internal.Contracts.Transmission
open BlockBand.Internal.Contracts.Inputs
open scoped NNReal ENNReal

variable {Ω : Type} {N : ℕ}

/-- `K` or `-i K`. -/
def evK (K : Matrix (Fin N) (Fin N) ℂ) (p : Bool) : Matrix (Fin N) (Fin N) ℂ :=
  if p then K else (-Complex.I) • K

/-- The tail-event family: monitored `(none | some i, k, Re/Im)` and target `Re/Im`. -/
def eventFamily {ι : Type} (F : Matrix (Fin N) (Fin N) ℂ) (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ)
    (z m : ℂ) (s : ℝ≥0) (u : ι → Fin N → ℂ) (aav bav : ℕ → ℝ) (av bv : ι → ℕ → ℝ)
    (Kt : Matrix (Fin N) (Fin N) ℂ) (aT bT : ℝ) :
    (Option ι × Fin (N + 1) × Bool) ⊕ Bool → Set Ω
  | Sum.inl (none, k, p) => tailEvent F G z m s (evK (avgK N) p) (aav k) (bav k)
  | Sum.inl (some i, k, p) =>
      if u i = 0 then ∅ else tailEvent F G z m s (evK (isoK (u i) (u i)) p) (av i k) (bv i k)
  | Sum.inr p => tailEvent F G z m s (evK Kt p) aT bT

section Union

variable [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ}

/-- **Union bound over the tail events.** -/
theorem measure_le_of_martGood (hG : IsHermitianBrownian Q 𝓖 N G) (hN : 0 < N)
    {F : SourceHermitian N} {s : ℝ≥0} {z : ℂ} {Mz : Matrix (Fin N) (Fin N) ℂ}
    (hMDE : IsManuscriptMDE (s : ℝ) F z Mz) (hz : z.im ≠ 0) {ι : Type} [Fintype ι]
    (u : ι → Fin N → ℂ) (aav bav : ℕ → ℝ) (av bv : ι → ℕ → ℝ) (Kt : Matrix (Fin N) (Fin N) ℂ)
    (aT bT q : ℝ)
    (hqav : ∀ k, 0 < aav k ∧ 0 < bav k ∧ q ≤ aav k ^ 2 / (2 * bav k))
    (hqv : ∀ i, u i ≠ 0 → ∀ k, 0 < av i k ∧ 0 < bv i k ∧ q ≤ av i k ^ 2 / (2 * bv i k))
    (hqt : 0 < aT ∧ 0 < bT ∧ q ≤ aT ^ 2 / (2 * bT)) (S : Set Ω)
    (hS : ∀ ω ∈ S,
      (∀ k ≤ N, MartGood (avgK N) Mz (normalizedTrace Mz)
        (pathR F.1 G z (normalizedTrace Mz) s ω) s (aav k) (bav k)) →
      (∀ i, u i ≠ 0 → ∀ k ≤ N, MartGood (isoK (u i) (u i)) Mz (normalizedTrace Mz)
        (pathR F.1 G z (normalizedTrace Mz) s ω) s (av i k) (bv i k)) →
      MartGood Kt Mz (normalizedTrace Mz) (pathR F.1 G z (normalizedTrace Mz) s ω) s aT bT →
      False) :
    Q S ≤ ENNReal.ofReal
      (((Fintype.card ι + 1) * ((N + 1) * 2) + 2 : ℕ) * (2 * Real.exp (-q))) := by
  set m := normalizedTrace Mz with hmdef
  have hm : 0 ≤ z.im * m.im := mde_im_mul_im_nonneg hMDE
  set E := eventFamily (Ω := Ω) F.1 G z m s u aav bav av bv Kt aT bT with hEdef
  have tail : ∀ (K : Matrix (Fin N) (Fin N) ℂ) (a b : ℝ), 0 < a → 0 < b →
      q ≤ a ^ 2 / (2 * b) →
      Q (tailEvent F.1 G z m s K a b) ≤ ENNReal.ofReal (2 * Real.exp (-q)) := by
    intro K a b ha hb hq
    refine (measure_tailEvent_le hG F.2 hz hm s K ha hb).trans (ENNReal.ofReal_le_ofReal ?_)
    gcongr
    rw [neg_div]
    linarith
  have hE : ∀ j, Q (E j) ≤ ENNReal.ofReal (2 * Real.exp (-q)) := by
    rintro (⟨_ | i, k, p⟩ | p)
    · obtain ⟨h1, h2, h3⟩ := hqav k
      exact tail _ _ _ h1 h2 h3
    · simp only [hEdef, eventFamily]
      split_ifs with hi
      · simp
      · obtain ⟨h1, h2, h3⟩ := hqv i hi k
        exact tail _ _ _ h1 h2 h3
    · exact tail _ _ _ hqt.1 hqt.2.1 hqt.2.2
  have hsub : S ⊆ ⋃ j, E j := by
    intro ω hω
    by_contra hnot
    simp only [mem_iUnion, not_exists] at hnot
    have hP := flowPath_pathR hG hN hMDE hz ω
    have hint := hP.intervalIntegrable_obsD
    refine hS ω hω (fun k hk => ?_) (fun i hi k hk => ?_) ?_
    · have h1 := hnot (Sum.inl (none, ⟨k, by omega⟩, true))
      have h2 := hnot (Sum.inl (none, ⟨k, by omega⟩, false))
      simp only [hEdef, eventFamily, evK, ite_true, Bool.false_eq_true, ite_false] at h1 h2
      exact martGood_of_not_mem hP.init hint h1 h2
    · have h1 := hnot (Sum.inl (some i, ⟨k, by omega⟩, true))
      have h2 := hnot (Sum.inl (some i, ⟨k, by omega⟩, false))
      simp only [hEdef, eventFamily, evK, ite_true, Bool.false_eq_true, ite_false, hi] at h1 h2
      exact martGood_of_not_mem hP.init hint h1 h2
    · have h1 := hnot (Sum.inr true)
      have h2 := hnot (Sum.inr false)
      simp only [hEdef, eventFamily, evK, ite_true, Bool.false_eq_true, ite_false] at h1 h2
      exact martGood_of_not_mem hP.init hint h1 h2
  calc Q S ≤ Q (⋃ j, E j) := measure_mono hsub
    _ ≤ ∑ j, Q (E j) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _j : (Option ι × Fin (N + 1) × Bool) ⊕ Bool, ENNReal.ofReal (2 * Real.exp (-q)) :=
        Finset.sum_le_sum fun j _ => hE j
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 3
        simp [Fintype.card_sum, Fintype.card_prod, Fintype.card_option]

theorem abs_im_trace_pos (hN : 0 < N) {s : ℝ} {F : SourceHermitian N} {z : ℂ}
    {Mz : Matrix (Fin N) (Fin N) ℂ} (hMDE : IsManuscriptMDE s F z Mz) :
    0 < |(normalizedTrace Mz).im| := abs_pos.2 fun h0 => by
  have := mde_im_mul_im_pos hN hMDE
  rw [h0, mul_zero] at this
  exact lt_irrefl _ this

/-- **Isotropic failure probability for fixed data.** -/
theorem iso_core (hG : IsHermitianBrownian Q 𝓖 N G) (hN : 0 < N) {F : SourceHermitian N}
    {s : ℝ≥0} {z : ℂ} {Mz : Matrix (Fin N) (Fin N) ℂ} (hMDE : IsManuscriptMDE (s : ℝ) F z Mz)
    (hz : z.im ≠ 0) {x y : Fin N → ℂ} (hx : x ≠ 0) (hy : y ≠ 0) {K θ Λ : ℝ} (hK : 0 < K)
    (hρ : 0 < sourceDensity Mz) (hρc : sourceDensity Mz ≤ |(normalizedTrace Mz).im|)
    (hcρ : |(normalizedTrace Mz).im| ≤ 8 * sourceDensity Mz)
    (hL : zigHeight |z.im| |(normalizedTrace Mz).im| s 0 ≤ 2 ^ N * |z.im|)
    (hsmall₁ : 4 * K * (1 + Real.log (zigHeight |z.im| |(normalizedTrace Mz).im| s 0 / |z.im|)) <
      θ)
    (hsmall₂ : 2 * θ ≤ N * |(normalizedTrace Mz).im| * |z.im|)
    (hsmall₃ : θ ^ 2 * sourceDensity Mz ≤ K ^ 2 * |(normalizedTrace Mz).im| ^ 2 * (N * |z.im|))
    (hsmall₄ : θ ^ 2 ≤ N * |z.im| * sourceDensity Mz)
    (hfin : 2 * K + 4 * K *
      (1 + Real.log (zigHeight |z.im| |(normalizedTrace Mz).im| s 0 / |z.im|)) ≤ Λ)
    (hNηρ : 1 ≤ N * |z.im| * sourceDensity Mz) :
    Q {ω | Λ * isotropicControl Mz z x y <
        ‖sourceMatrixElement (pathR F.1 G z (normalizedTrace Mz) s ω s) x y -
          sourceMatrixElement Mz x y‖} ≤
      ENNReal.ofReal (((Fintype.card (Fin 2) + 1) * ((N + 1) * 2) + 2 : ℕ) *
        (2 * Real.exp (-(K ^ 2 / 64)))) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hs0 : (0 : ℝ) ≤ s := s.2
  set m := normalizedTrace Mz with hmdef
  set η := |z.im| with hηdef
  set c := |m.im| with hcdef
  set ρ := sourceDensity Mz with hρdef
  have hη : 0 < η := abs_pos.2 hz
  have hc : 0 < c := abs_im_trace_pos hN hMDE
  have hη0 : 0 < zigHeight η c s 0 := zigHeight_pos hη hc.le hs0
  set u : Fin 2 → Fin N → ℂ := ![x, y] with hudef
  set wx := |(sourceMatrixElement Mz x x).im| with hwxdef
  set wy := |(sourceMatrixElement Mz y y).im| with hwydef
  have hwx : 0 < wx := mde_weight_pos hMDE hz hs0 hx
  have hwy : 0 < wy := mde_weight_pos hMDE hz hs0 hy
  set κ := Real.sqrt (ρ / (N * η)) * Real.sqrt (wx * wy) / c with hκdef
  have hκ : 0 < κ := by
    have : 0 < Real.sqrt (ρ / (N * η)) := Real.sqrt_pos.2 (by positivity)
    have : 0 < Real.sqrt (wx * wy) := Real.sqrt_pos.2 (by positivity)
    positivity
  refine measure_le_of_martGood hG hN hMDE hz u
    (fun k => K / (4 * N * (zigHeight η c s 0 / 2 ^ k)))
    (fun k => 2 / ((N : ℝ) ^ 2 * (zigHeight η c s 0 / 2 ^ k) ^ 2))
    (fun i k => K * |(sourceMatrixElement Mz (u i) (u i)).im| /
      (2 * Real.sqrt (2 * N * (zigHeight η c s 0 / 2 ^ k) * ρ)))
    (fun i k => 4 * |(sourceMatrixElement Mz (u i) (u i)).im| ^ 2 /
      (N * ρ * (zigHeight η c s 0 / 2 ^ k)))
    (isoK x y) (K * κ) (4 * wx * wy / (N * c * η)) (K ^ 2 / 64) ?_ ?_ ?_ _ ?_
  · intro k
    have hh : 0 < zigHeight η c s 0 / 2 ^ k := by positivity
    refine ⟨by positivity, by positivity, le_of_eq ?_⟩
    field_simp
    ring
  · intro i hi k
    have hw := mde_weight_pos hMDE hz hs0 hi
    have hh : 0 < zigHeight η c s 0 / 2 ^ k := by positivity
    refine ⟨by positivity, by positivity, le_of_eq ?_⟩
    rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    field_simp
    ring
  · refine ⟨by positivity, by positivity, ?_⟩
    have e : (K * κ) ^ 2 / (2 * (4 * wx * wy / (N * c * η))) = K ^ 2 * ρ / (8 * c) := by
      rw [hκdef, mul_pow, div_pow, mul_pow, Real.sq_sqrt (by positivity),
        Real.sq_sqrt (by positivity)]
      field_simp
      ring
    rw [e, div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith [sq_nonneg K]
  · intro ω hω hav hv ht
    have hP := flowPath_pathR hG hN hMDE hz ω
    have hmon := hP.monitored u hN hρ hρc hK.le (fun i hi => mde_weight_pos hMDE hz hs0 hi) hL
      hsmall₁ hsmall₂ hsmall₃ hsmall₄ hav hv
    have htgt := hP.target_iso x y hN hK.le (fun t ht => ⟨(hmon t ht).1,
      by simpa [hudef] using (hmon t ht).2.2 0, by simpa [hudef] using (hmon t ht).2.2 1⟩) ht
    have hctrl : isotropicControl Mz z x y = κ := isotropicControl_eq hMDE hz hs0 hN hx hy
    set Lg := Real.log (zigHeight η c s 0 / η) with hLg
    have hLg0 : 0 ≤ Lg := Real.log_nonneg ((one_le_div hη).2 (le_zigHeight hc.le hs0))
    have hb : Real.sqrt (wx * wy) / (N * c * η) ≤ κ := by
      have h1 : 1 / (N * η) ≤ Real.sqrt (ρ / (N * η)) := by
        rw [Real.le_sqrt (by positivity) (by positivity), div_pow, one_pow,
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      have h2 : 0 ≤ Real.sqrt (wx * wy) := Real.sqrt_nonneg _
      calc Real.sqrt (wx * wy) / (N * c * η) = 1 / (N * η) * Real.sqrt (wx * wy) / c := by
            field_simp
        _ ≤ Real.sqrt (ρ / (N * η)) * Real.sqrt (wx * wy) / c := by gcongr
    have hfinal : ‖sourceMatrixElement (pathR F.1 G z m s ω s) x y -
        sourceMatrixElement Mz x y‖ ≤ Λ * κ := by
      refine htgt.trans ?_
      calc 2 * (K * κ) + 2 * K * (2 * Real.sqrt (wx * wy)) * (1 + Lg) / (N * c * η)
          = 2 * K * κ + 4 * K * (1 + Lg) * (Real.sqrt (wx * wy) / (N * c * η)) := by ring
        _ ≤ 2 * K * κ + 4 * K * (1 + Lg) * κ := by gcongr
        _ = (2 * K + 4 * K * (1 + Lg)) * κ := by ring
        _ ≤ Λ * κ := by gcongr
    simp only [mem_ofPred_eq] at hω
    rw [hctrl] at hω
    linarith

/-- `√(c W) / (N c η) = √(W / c) / (N η)`. -/
theorem sqrt_mul_div_eq {c W N η : ℝ} (hc : 0 < c) :
    Real.sqrt (c * W) / (N * c * η) = Real.sqrt (W / c) / (N * η) := by
  have e : Real.sqrt (c * W) = c * Real.sqrt (W / c) := by
    rw [← Real.sqrt_sq hc.le, ← Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]
    congr 1
    field_simp
  rw [e]
  rcases eq_or_ne N 0 with hN | hN
  · simp [hN]
  rcases eq_or_ne η 0 with hη | hη
  · simp [hη]
  field_simp

/-- **Averaged failure probability for fixed data.** -/
theorem avg_core (hG : IsHermitianBrownian Q 𝓖 N G) (hN : 0 < N) {F : SourceHermitian N}
    {s : ℝ≥0} {z : ℂ} {Mz : Matrix (Fin N) (Fin N) ℂ} (hMDE : IsManuscriptMDE (s : ℝ) F z Mz)
    (hz : z.im ≠ 0) {B : Matrix (Fin N) (Fin N) ℂ} (hB : B ≠ 0) {K θ Λ : ℝ} (hK : 0 < K)
    (hρ : 0 < sourceDensity Mz) (hρc : sourceDensity Mz ≤ |(normalizedTrace Mz).im|)
    (hL : zigHeight |z.im| |(normalizedTrace Mz).im| s 0 ≤ 2 ^ N * |z.im|)
    (hsmall₁ : 4 * K * (1 + Real.log (zigHeight |z.im| |(normalizedTrace Mz).im| s 0 / |z.im|)) <
      θ)
    (hsmall₂ : 2 * θ ≤ N * |(normalizedTrace Mz).im| * |z.im|)
    (hsmall₃ : θ ^ 2 * sourceDensity Mz ≤ K ^ 2 * |(normalizedTrace Mz).im| ^ 2 * (N * |z.im|))
    (hsmall₄ : θ ^ 2 ≤ N * |z.im| * sourceDensity Mz)
    (hfin : 2 * K + 4 * K *
      (1 + Real.log (zigHeight |z.im| |(normalizedTrace Mz).im| s 0 / |z.im|)) ≤ Λ) :
    Q {ω | Λ * averagedControl Mz B z <
        ‖normalizedTrace ((pathR F.1 G z (normalizedTrace Mz) s ω s - Mz) * B)‖} ≤
      ENNReal.ofReal (((Fintype.card (Fin N) + 1) * ((N + 1) * 2) + 2 : ℕ) *
        (2 * Real.exp (-(K ^ 2 / 64)))) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hs0 : (0 : ℝ) ≤ s := s.2
  set m := normalizedTrace Mz with hmdef
  set η := |z.im| with hηdef
  set c := |m.im| with hcdef
  set ρ := sourceDensity Mz with hρdef
  have hη : 0 < η := abs_pos.2 hz
  have hc : 0 < c := abs_im_trace_pos hN hMDE
  have hη0 : 0 < zigHeight η c s 0 := zigHeight_pos hη hc.le hs0
  set W := (N : ℝ)⁻¹ * ∑ j, |(sourceMatrixElement Mz (col B j) (col B j)).im| with hWdef
  have hW : 0 < W := mde_weight_sum_pos hMDE hz hs0 hN hB
  set κ := Real.sqrt (W / c) / (N * η) with hκdef
  have hκ : 0 < κ := by
    have : 0 < Real.sqrt (W / c) := Real.sqrt_pos.2 (by positivity)
    positivity
  refine measure_le_of_martGood hG hN hMDE hz (col B)
    (fun k => K / (4 * N * (zigHeight η c s 0 / 2 ^ k)))
    (fun k => 2 / ((N : ℝ) ^ 2 * (zigHeight η c s 0 / 2 ^ k) ^ 2))
    (fun i k => K * |(sourceMatrixElement Mz (col B i) (col B i)).im| /
      (2 * Real.sqrt (2 * N * (zigHeight η c s 0 / 2 ^ k) * ρ)))
    (fun i k => 4 * |(sourceMatrixElement Mz (col B i) (col B i)).im| ^ 2 /
      (N * ρ * (zigHeight η c s 0 / 2 ^ k)))
    (obsB B) (K * κ) (2 * W / ((N : ℝ) ^ 2 * c * η ^ 2)) (K ^ 2 / 64) ?_ ?_ ?_ _ ?_
  · intro k
    have hh : 0 < zigHeight η c s 0 / 2 ^ k := by positivity
    refine ⟨by positivity, by positivity, le_of_eq ?_⟩
    field_simp
    ring
  · intro i hi k
    have hw := mde_weight_pos hMDE hz hs0 hi
    have hh : 0 < zigHeight η c s 0 / 2 ^ k := by positivity
    refine ⟨by positivity, by positivity, le_of_eq ?_⟩
    rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    field_simp
    ring
  · refine ⟨by positivity, by positivity, ?_⟩
    have e : (K * κ) ^ 2 / (2 * (2 * W / ((N : ℝ) ^ 2 * c * η ^ 2))) = K ^ 2 / 4 := by
      rw [hκdef, mul_pow, div_pow, Real.sq_sqrt (by positivity)]
      field_simp
      ring
    rw [e]
    have := sq_nonneg K
    linarith
  · intro ω hω hav hv ht
    have hP := flowPath_pathR hG hN hMDE hz ω
    have hmon := hP.monitored (col B) hN hρ hρc hK.le
      (fun i hi => mde_weight_pos hMDE hz hs0 hi) hL hsmall₁ hsmall₂ hsmall₃ hsmall₄ hav hv
    have htgt := hP.target_avg B hN hK.le hmon ht
    have hctrl : averagedControl Mz B z = κ := averagedControl_eq hMDE hz hs0 hN hB
    set Lg := Real.log (zigHeight η c s 0 / η) with hLg
    have hLg0 : 0 ≤ Lg := Real.log_nonneg ((one_le_div hη).2 (le_zigHeight hc.le hs0))
    have hb : Real.sqrt (c * W) / (N * c * η) = κ := sqrt_mul_div_eq hc
    have hfinal : ‖normalizedTrace ((pathR F.1 G z m s ω s - Mz) * B)‖ ≤ Λ * κ := by
      refine htgt.trans ?_
      calc 2 * (K * κ) + 2 * K * (2 * Real.sqrt (c * W)) * (1 + Lg) / (N * c * η)
          = 2 * K * κ + 4 * K * (1 + Lg) * (Real.sqrt (c * W) / (N * c * η)) := by ring
        _ = (2 * K + 4 * K * (1 + Lg)) * κ := by rw [hb]; ring
        _ ≤ Λ * κ := by gcongr
    simp only [mem_ofPred_eq] at hω
    rw [hctrl] at hω
    linarith

end Union

end BlockBand.Native.CEH.LocalLaw
