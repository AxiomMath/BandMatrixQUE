module

public import BlockBand.SourceProcess.ClosedSumProof.ClosedModW

/-!
# Event inclusions for `ClosedTight`

* `norm_gramEntry_closed`: every closed Gram coordinate is at most `Re Tr M`.
* `tight_incl`: on the cap event, a large coordinate at `⌊Wt₁⌋` forces the stop event.
* **`modulus_incl`**: on the cap event, a modulus event of `G_e - J_e` on `[t₁, T]` (time
  resolution `δ`) lies in the stop event or in the modulus event of `Re` or of `Im = Re(-i ·)` of
  the window coordinate `procX` (window `[⌊Wt₁⌋, ⌊WT⌋]`, block length `ℓ = ⌊Wδ⌋ + 1`), with any
  threshold `≤ η/2`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedSumProof

open MeasureTheory Matrix Finset
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.SourceProcessLaw
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedIdent
open BlockBand.SourceProcess.ClosedSum

variable {W p K M : ℕ} {b E s T h : ℝ} {q : Fin p → ℝ → ℝ} {R : ℝ}
  {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
  (e : Fin 2 × SrcCol K (Fin p × Fin M) × SrcCol K (Fin p × Fin M))

theorem norm_gramEntry_closed (j : ℕ) (y : SampledPath W p M × ℝ) :
    ‖gramEntry e (closedGramAt b E s T h q W j Vs y)‖ ≤
      ((closedGramAt b E s T h q W j Vs y).1.trace).re :=
  norm_gramEntry_le (closedFrameAt b E s T h q W j Vs y) (fun z => if z.1 = 0 then 1 else 0)
    (norm_nearPortProj_entry_le W) e

theorem tight_incl {j : ℕ} (hj1 : closeLen s W ≤ j) (hj2 : j ≤ ⌊(W : ℝ) * T⌋₊) :
    {y : SampledPath W p M × ℝ | y.1.1 ∈ physCapEvent b E s h K W ∧
      max R 0 < ‖gramEntry e (closedGramAt b E s T h q W j Vs y)‖} ⊆
      closedStopEvent b E s T h q R W Vs := by
  rintro y ⟨hcap, hgt⟩
  refine ⟨hcap, j, hj1, hj2, ?_⟩
  by_contra hlt
  have := norm_gramEntry_closed (b := b) (E := E) (s := s) (T := T) (h := h) (q := q) (Vs := Vs)
    e j y
  linarith [le_max_left R 0, not_le.mp hlt]

theorem floor_add_le' {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) : ⌊a + c⌋₊ ≤ ⌊a⌋₊ + ⌊c⌋₊ + 1 := by
  have h1 := Nat.floor_le (add_nonneg ha hc)
  have h2 := Nat.lt_floor_add_one a
  have h3 := Nat.lt_floor_add_one c
  have : (⌊a + c⌋₊ : ℝ) < ⌊a⌋₊ + ⌊c⌋₊ + 2 := by linarith
  have : ⌊a + c⌋₊ < ⌊a⌋₊ + ⌊c⌋₊ + 2 := by exact_mod_cast this
  omega

theorem floor_close {W : ℕ} {t t' δ : ℝ} (ht' : 0 ≤ t') (hδ : 0 ≤ δ) (htt : t ≤ t' + δ) :
    ⌊(W : ℝ) * t⌋₊ ≤ ⌊(W : ℝ) * t'⌋₊ + (⌊(W : ℝ) * δ⌋₊ + 1) := by
  have hW := Nat.cast_nonneg (α := ℝ) W
  have := Nat.floor_mono (show (W : ℝ) * t ≤ W * t' + W * δ by nlinarith)
  have := floor_add_le' (mul_nonneg hW ht') (mul_nonneg hW hδ)
  omega

theorem exists_window (f : ℕ → ℝ) {j₁ L N ℓ a a' : ℕ} (ha : j₁ ≤ a ∧ a ≤ j₁ + L)
    (ha' : j₁ ≤ a' ∧ a' ≤ j₁ + L) (h1 : a ≤ a' + ℓ) (h2 : a' ≤ a + ℓ) (hNL : L ≤ N * ℓ)
    {thr : ℝ} (hgt : thr < |f (a - j₁) - f (a' - j₁)|) :
    ∃ x y, x ≤ y ∧ y ≤ N * ℓ ∧ y ≤ x + ℓ ∧ thr < |f y - f x| := by
  rcases le_total a a' with hle | hle
  · exact ⟨a - j₁, a' - j₁, by omega, by omega, by omega, by rwa [abs_sub_comm]⟩
  · exact ⟨a' - j₁, a - j₁, by omega, by omega, by omega, hgt⟩

/-- The modulus event of the window coordinate `procX`. -/
def modEv (b E s T h : ℝ) (q : Fin p → ℝ → ℝ) (W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (e : Fin 2 × SrcCol K (Fin p × Fin M) × SrcCol K (Fin p × Fin M)) (u : ℂ)
    (j₁ L N ℓ : ℕ) (thr : ℝ) : Set (SampledPath W p M × ℝ) :=
  {y | ∃ x y', x ≤ y' ∧ y' ≤ N * ℓ ∧ y' ≤ x + ℓ ∧
    thr < |procX b E s T h q W Vs e u j₁ L y' y - procX b E s T h q W Vs e u j₁ L x y|}

theorem procX_at (u : ℂ) {j₁ L j : ℕ} (h1 : j₁ ≤ j) (h2 : j ≤ j₁ + L)
    (y : SampledPath W p M × ℝ) :
    procX b E s T h q W Vs e u j₁ L (j - j₁) y = reMul u (zc b E s T h q W Vs e j y -
      gramEntry e (closedJump b s T q W j y)) := by
  unfold procX
  rw [min_eq_left (by omega : j - j₁ ≤ L), Nat.add_sub_cancel' h1]

/-- **The modulus inclusion.** -/
theorem modulus_incl {t₁ δ η thr : ℝ} (ht₁ : 0 ≤ t₁) (hδ : 0 ≤ δ) {N : ℕ}
    (hj : ⌊(W : ℝ) * t₁⌋₊ ≤ ⌊(W : ℝ) * T⌋₊)
    (hNL : ⌊(W : ℝ) * T⌋₊ - ⌊(W : ℝ) * t₁⌋₊ ≤ N * (⌊(W : ℝ) * δ⌋₊ + 1)) (hthr : thr ≤ η / 2) :
    {y : SampledPath W p M × ℝ | y.1.1 ∈ physCapEvent b E s h K W ∧
        ∃ t ∈ Set.Icc t₁ T, ∃ t' ∈ Set.Icc t₁ T, |t - t'| ≤ δ ∧ η < ‖gramEntry e
          (closedGramAt b E s T h q W ⌊(W : ℝ) * t⌋₊ Vs y - closedJump b s T q W ⌊(W : ℝ) * t⌋₊ y -
            (closedGramAt b E s T h q W ⌊(W : ℝ) * t'⌋₊ Vs y -
              closedJump b s T q W ⌊(W : ℝ) * t'⌋₊ y))‖} ⊆
      closedStopEvent b E s T h q R W Vs ∪
        ((closedAlive b E s T h q R W ⌊(W : ℝ) * T⌋₊ Vs ∩ modEv b E s T h q W Vs e 1
            ⌊(W : ℝ) * t₁⌋₊ (⌊(W : ℝ) * T⌋₊ - ⌊(W : ℝ) * t₁⌋₊) N (⌊(W : ℝ) * δ⌋₊ + 1) thr) ∪
          (closedAlive b E s T h q R W ⌊(W : ℝ) * T⌋₊ Vs ∩ modEv b E s T h q W Vs e (-Complex.I)
            ⌊(W : ℝ) * t₁⌋₊ (⌊(W : ℝ) * T⌋₊ - ⌊(W : ℝ) * t₁⌋₊) N (⌊(W : ℝ) * δ⌋₊ + 1) thr)) := by
  rintro y ⟨hcap, t, ht, t', ht', htt, hη⟩
  by_cases hst : y ∈ closedStopEvent b E s T h q R W Vs
  · exact Or.inl hst
  right
  set j₁ := ⌊(W : ℝ) * t₁⌋₊
  set L := ⌊(W : ℝ) * T⌋₊ - j₁
  have hal : y ∈ closedAlive b E s T h q R W ⌊(W : ℝ) * T⌋₊ Vs :=
    ⟨hcap, fun i hi1 hi2 => not_le.mp fun hR => hst ⟨hcap, i, hi1, hi2, hR⟩⟩
  have hW := Nat.cast_nonneg (α := ℝ) W
  have hrange : ∀ τ ∈ Set.Icc t₁ T, j₁ ≤ ⌊(W : ℝ) * τ⌋₊ ∧ ⌊(W : ℝ) * τ⌋₊ ≤ j₁ + L := fun τ hτ =>
    ⟨Nat.floor_mono (mul_le_mul_of_nonneg_left hτ.1 hW), by
      have := Nat.floor_mono (mul_le_mul_of_nonneg_left hτ.2 hW); omega⟩
  have h1 := floor_close (W := W) (t := t) (t' := t') (ht₁.trans ht'.1) hδ
    (by linarith [le_abs_self (t - t')])
  have h2 := floor_close (W := W) (t := t') (t' := t) (ht₁.trans ht.1) hδ
    (by linarith [neg_abs_le (t - t')])
  set zz : ℕ → ℂ := fun j => zc b E s T h q W Vs e j y - gramEntry e (closedJump b s T q W j y)
  have hw : gramEntry e (closedGramAt b E s T h q W ⌊(W : ℝ) * t⌋₊ Vs y -
      closedJump b s T q W ⌊(W : ℝ) * t⌋₊ y - (closedGramAt b E s T h q W ⌊(W : ℝ) * t'⌋₊ Vs y -
        closedJump b s T q W ⌊(W : ℝ) * t'⌋₊ y)) = zz ⌊(W : ℝ) * t⌋₊ - zz ⌊(W : ℝ) * t'⌋₊ := by
    simp only [zz, zc, gramEntry_sub]
  rw [hw] at hη
  have hsplit := Complex.norm_le_abs_re_add_abs_im (zz ⌊(W : ℝ) * t⌋₊ - zz ⌊(W : ℝ) * t'⌋₊)
  have hX : ∀ u : ℂ, reMul u (zz ⌊(W : ℝ) * t⌋₊ - zz ⌊(W : ℝ) * t'⌋₊) =
      procX b E s T h q W Vs e u j₁ L (⌊(W : ℝ) * t⌋₊ - j₁) y -
        procX b E s T h q W Vs e u j₁ L (⌊(W : ℝ) * t'⌋₊ - j₁) y := fun u => by
    rw [procX_at e u (hrange t ht).1 (hrange t ht).2, procX_at e u (hrange t' ht').1
      (hrange t' ht').2, map_sub]
  by_cases hre : η / 2 < |(zz ⌊(W : ℝ) * t⌋₊ - zz ⌊(W : ℝ) * t'⌋₊).re|
  · refine Or.inl ⟨hal, exists_window (fun k => procX b E s T h q W Vs e 1 j₁ L k y)
      (hrange t ht) (hrange t' ht') h1 h2 hNL ?_⟩
    have e1 : (zz ⌊(W : ℝ) * t⌋₊ - zz ⌊(W : ℝ) * t'⌋₊).re =
        reMul 1 (zz ⌊(W : ℝ) * t⌋₊ - zz ⌊(W : ℝ) * t'⌋₊) := by rw [reMul_apply, one_mul]
    rw [e1, hX] at hre
    linarith
  · refine Or.inr ⟨hal, exists_window (fun k => procX b E s T h q W Vs e (-Complex.I) j₁ L k y)
      (hrange t ht) (hrange t' ht') h1 h2 hNL ?_⟩
    have e1 : (zz ⌊(W : ℝ) * t⌋₊ - zz ⌊(W : ℝ) * t'⌋₊).im =
        reMul (-Complex.I) (zz ⌊(W : ℝ) * t⌋₊ - zz ⌊(W : ℝ) * t'⌋₊) := by
      rw [reMul_apply]; simp
    have him : η / 2 < |(zz ⌊(W : ℝ) * t⌋₊ - zz ⌊(W : ℝ) * t'⌋₊).im| := by
      rw [Complex.sub_re] at hre hsplit; rw [Complex.sub_im] at hsplit ⊢
      linarith
    rw [e1, hX] at him
    linarith

end BlockBand.SourceProcess.ClosedSumProof
