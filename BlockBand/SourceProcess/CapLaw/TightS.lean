module

public import BlockBand.SourceProcess.CapLaw.Pins

/-!
# `ClosedTightS`: the closed modulus from time `s` on

`closedTight_of` with `s ≤ t₁ ≤ T`. The proof is that of `closedTight_of` except for the window
bounds: it uses `t₁ > s` only through `n_s ≤ ⌊Wt₁⌋` and `0 ≤ t₁`, and `closed_modulus_W`
accepts `j₁ = n_s`. This gives the modulus of `G − J` on `[s, T]`, i.e.
right-continuity of the limit at the entrance time.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CapLaw

open MeasureTheory Matrix Finset Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.SourceProcessLaw
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedIdent
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.ClosedSumProof
open scoped ENNReal

/-- **`ClosedTightS` from the summed errors, the fourth moments and the stop tail.** -/
theorem closedTightS_of (hS : ClosedSummed) (hF : ClosedFourth) (hT : ClosedStopTail) :
    ClosedTightS := by
  intro b hb0 hb E hE1 hE2 s T hs hsT p q hq h hh0 hh1 K M hM Vs hVs e t₁ ht₁ ht₁T
  have hq' : ∀ i x, 0 ≤ q i x := fun i x => (hq i).1 x
  have hb1 : b < 1 := by linarith
  have hP : ∀ W : ℕ, IsProbabilityMeasure (lawW b T q M W) := fun W => by
    have := isProbabilityMeasure_sampledPathLaw (b := b) (W := W) (M := M) hq' ⌊(W : ℝ) * T⌋₊
    unfold lawW; infer_instance
  have hfl : ∀ W : ℕ, closeLen s W ≤ ⌊(W : ℝ) * t₁⌋₊ ∧ ⌊(W : ℝ) * t₁⌋₊ ≤ ⌊(W : ℝ) * T⌋₊ :=
    fun W => ⟨Nat.floor_mono (mul_le_mul_of_nonneg_left ht₁ (Nat.cast_nonneg _)),
      Nat.floor_mono (mul_le_mul_of_nonneg_left ht₁T (Nat.cast_nonneg _))⟩
  have hs0 : 0 ≤ t₁ := hs.le.trans ht₁
  have hT0 : 0 < T := hs.trans hsT
  refine ⟨fun θ hθ => ?_, fun η θ hη hθ => ?_⟩
  · obtain ⟨R, hR⟩ := hT b hb0 hb E hE1 hE2 s T hs hsT p q hq h hh0 hh1 K M hM Vs hVs θ hθ
    obtain ⟨W₀, hW₀⟩ := eventually_atTop.mp hR
    exact ⟨max R 0, W₀, fun W hW =>
      (measure_mono (tight_incl (R := R) e (hfl W).1 (hfl W).2)).trans (hW₀ W hW)⟩
  obtain ⟨R, hR⟩ := hT b hb0 hb E hE1 hE2 s T hs hsT p q hq h hh0 hh1 K M hM Vs hVs (θ / 4)
    (by positivity)
  set Cb := driftC b E K p M R
  set Cc := covC b E K p M R
  have hCb0 : 0 ≤ Cb := driftC_nonneg b E K p M R
  set lam := η / 16
  have hlam : 0 < lam := by positivity
  set δ := min (1 / 2) (min (η / (16 * (Cb + 1))) (θ * lam ^ 4 / (1024 * (Cc ^ 2 + 1) * (T + 1))))
  have hδ : 0 < δ := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hδ2 : δ ≤ 1 / 2 := min_le_left _ _
  have hδb : δ ≤ η / (16 * (Cb + 1)) := (min_le_right _ _).trans (min_le_left _ _)
  have hδc : δ ≤ θ * lam ^ 4 / (1024 * (Cc ^ 2 + 1) * (T + 1)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  set A := (64 + 8 * lam ^ 2) / lam ^ 4 + 1 / lam + 1 / lam
  have hA0 : 0 ≤ A := by positivity
  set ε₀ := min 1 (θ / (8 * (A + 1)))
  have hε₀ : 0 < ε₀ := lt_min one_pos (by positivity)
  have hε₁ : ε₀ ≤ 1 := min_le_left _ _
  have hε₀A : ε₀ * A ≤ θ / 8 := by
    have h1 : ε₀ ≤ θ / (8 * (A + 1)) := min_le_right _ _
    have h2 : θ / (8 * (A + 1)) * A ≤ θ / 8 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    exact (mul_le_mul_of_nonneg_right h1 hA0).trans h2
  have hSW := (ENNReal.tendsto_nhds_zero.mp (hS b hb0 hb E hE1 hE2 s T hs hsT p q hq h hh0 hh1 K M
    hM R Vs hVs e (swapE e))) _ (ENNReal.ofReal_pos.mpr hε₀)
  have hFW := (ENNReal.tendsto_nhds_zero.mp (hF b hb0 hb E hE1 hE2 s T hs hsT p q hq h hh0 hh1 K M
    hM R Vs hVs e)) _ (ENNReal.ofReal_pos.mpr hε₀)
  have hWδ : ∀ᶠ W : ℕ in atTop, (1 : ℝ) ≤ W * δ := by
    filter_upwards [eventually_ge_atTop ⌈1 / δ⌉₊] with W hW
    have : (1 / δ : ℝ) ≤ W := (Nat.le_ceil _).trans (by exact_mod_cast hW)
    rwa [div_le_iff₀ hδ] at this
  obtain ⟨W₀, hW₀⟩ := eventually_atTop.mp (hVs.and (hR.and (hSW.and (hFW.and hWδ))))
  refine ⟨δ, hδ, W₀, fun W hW => ?_⟩
  obtain ⟨hV, hRW, hSW', hFW', hWδ'⟩ := hW₀ W hW
  have := hP W
  have hW0 : (0 : ℝ) < W := by
    by_contra hc
    have h0 : (W : ℝ) = 0 := le_antisymm (not_lt.mp hc) (Nat.cast_nonneg _)
    rw [h0, zero_mul] at hWδ'
    linarith
  set j₁ := ⌊(W : ℝ) * t₁⌋₊
  set L := ⌊(W : ℝ) * T⌋₊ - j₁
  set ℓ := ⌊(W : ℝ) * δ⌋₊ + 1
  set N := L / ℓ + 1
  have hℓ : 0 < ℓ := Nat.succ_pos _
  have hdm := Nat.div_add_mod L ℓ
  have hml := Nat.mod_lt L hℓ
  have hNL : L ≤ N * ℓ := by
    have e : N * ℓ = ℓ * (L / ℓ) + ℓ := by simp only [N]; ring
    omega
  have hNL2 : N * ℓ ≤ L + ℓ := by
    have e : N * ℓ = ℓ * (L / ℓ) + ℓ := by simp only [N]; ring
    omega
  have hjL : j₁ + L = ⌊(W : ℝ) * T⌋₊ := by have := (hfl W).2; omega
  have hℓR : (ℓ : ℝ) ≤ W * δ + 1 := by
    simp only [ℓ, Nat.cast_add, Nat.cast_one]
    linarith [Nat.floor_le (mul_nonneg hW0.le hδ.le)]
  have hthr : 3 * lam + ℓ * ((W : ℝ)⁻¹ * Cb) + lam + lam ≤ η / 2 := by
    have h1 : (ℓ : ℝ) * (W : ℝ)⁻¹ ≤ 2 * δ := by
      rw [← div_eq_mul_inv, div_le_iff₀ hW0]; linarith
    have h2 : 2 * δ * Cb ≤ η / 8 := by
      have := (le_div_iff₀ (by positivity : (0 : ℝ) < 16 * (Cb + 1))).mp hδb
      nlinarith
    have h3 : (ℓ : ℝ) * ((W : ℝ)⁻¹ * Cb) ≤ 2 * δ * Cb := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right h1 hCb0
    simp only [lam]; linarith
  have hincl := modulus_incl (R := R) (N := N) e hs0 hδ.le (hfl W).2 hNL hthr
    (b := b) (E := E) (s := s) (T := T) (h := h) (q := q) (Vs := Vs W) (K := K) (M := M)
  refine (measure_mono hincl).trans ((measure_union_le _ _).trans
    ((add_le_add hRW (measure_union_le _ _)).trans ?_))
  have hpart : ∀ u : ℂ, ‖u‖ = 1 → (lawW b T q M W) (closedAlive b E s T h q R W ⌊(W : ℝ) * T⌋₊
      (Vs W) ∩ modEv b E s T h q W (Vs W) e u j₁ L N ℓ
        (3 * lam + ℓ * ((W : ℝ)⁻¹ * Cb) + lam + lam)) ≤ ENNReal.ofReal (3 * θ / 8) := by
    intro u hu
    refine le_of_eq_of_le (measure_congr ((closedAlive_ae_eq hb1 hE1 hE2 s T h hq'
      ⌊(W : ℝ) * T⌋₊ R ⌊(W : ℝ) * T⌋₊ (Vs W)).inter (EventuallyEq.refl _
        (modEv b E s T h q W (Vs W) e u j₁ L N ℓ (3 * lam + ℓ * ((W : ℝ)⁻¹ * Cb) + lam + lam)))))
      ?_
    have hmod := closed_modulus_W e hb1 hE1 hE2 hq' hV.1 (hfl W).1 (le_of_eq hjL) N ℓ hℓ hNL
      hε₀.le hε₁ hSW' hFW' hu hlam hlam hlam
    rw [hjL] at hmod
    refine hmod.trans (ENNReal.ofReal_le_ofReal ?_)
    have hNLR : ((N : ℝ) * ℓ) ≤ W * T + (W * δ + 1) := by
      have h1 : ((N * ℓ : ℕ) : ℝ) ≤ (L : ℝ) + ℓ := by exact_mod_cast hNL2
      have h2 : (L : ℝ) ≤ W * T := (Nat.cast_le.mpr (Nat.sub_le _ _)).trans
        (Nat.floor_le (mul_nonneg hW0.le hT0.le))
      push_cast at h1; linarith
    have hc := coeff_bound (Cc := Cc) hW0 hWδ' hT0 hNLR hδ2 (by positivity) hℓR
    have hb1' : 16 * ((W : ℝ)⁻¹ * Cc) ^ 2 * ((N : ℝ) * ℓ) * ℓ / lam ^ 4 ≤ θ / 32 := by
      have hl4 : 0 < lam ^ 4 := by positivity
      rw [div_le_iff₀ hl4]
      have h1 : 16 * ((W : ℝ)⁻¹ * Cc) ^ 2 * ((N : ℝ) * ℓ) * ℓ ≤ 32 * Cc ^ 2 * (T + 1) * δ := by
        nlinarith
      have h2 : 32 * Cc ^ 2 * (T + 1) * δ ≤ θ / 32 * lam ^ 4 := by
        have := (le_div_iff₀ (by positivity : (0 : ℝ) < 1024 * (Cc ^ 2 + 1) * (T + 1))).mp hδc
        have hC : Cc ^ 2 ≤ Cc ^ 2 + 1 := by linarith
        have hδ0 := hδ.le
        nlinarith [mul_le_mul_of_nonneg_right hC (mul_nonneg (by linarith : (0 : ℝ) ≤ T + 1) hδ0)]
      linarith
    have : ε₀ * ((64 + 8 * lam ^ 2) / lam ^ 4 + 1 / lam + 1 / lam) ≤ θ / 8 := hε₀A
    linarith
  refine (add_le_add le_rfl (add_le_add (hpart 1 (by simp)) (hpart (-Complex.I) (by simp)))).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- The same with `ClosedLindeberg`. -/
theorem closedTightS_of_lindeberg (hS : ClosedSummed) (hL : ClosedReduce.ClosedLindeberg)
    (hT : ClosedStopTail) : ClosedTightS :=
  closedTightS_of hS ((closedFourth_iff_lindeberg).2 hL) hT

end BlockBand.SourceProcess.CapLaw
