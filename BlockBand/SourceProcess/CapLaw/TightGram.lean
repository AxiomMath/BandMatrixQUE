module

public import BlockBand.SourceProcess.CapLaw.Coords

/-!
# Tightness and modulus of the conditioned Gram coordinates

From `ClosedTightS` (`t₁ = s`) under `condLaw`, when `P_W(A_W) ≥ c > 0`:
* `gram_modulus`: the conditioned modulus of a Gram coordinate on `[s, T']`.
* `gram_tight`: one-time tightness at every `t ≥ s`, by chaining (`chain_bound`) from the
  tightness at `n_s`, where `J = 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CapLaw

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.SourceProcessLaw
open BlockBand.SourceProcess.ClosedPath BlockBand.SourceProcess.ClosedIdent
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.ClosedSumProof
open scoped ENNReal

variable {W p K M : ℕ}

/-- Chaining: a `δ`-modulus `η` on `[s, T]` gives `‖f u − f s‖ ≤ n η` for `u ≤ s + nδ`. -/
theorem chain_bound {f : ℝ → ℂ} {s T δ η : ℝ} (hδ : 0 < δ)
    (hf : ∀ u ∈ Icc s T, ∀ u' ∈ Icc s T, |u - u'| ≤ δ → ‖f u - f u'‖ ≤ η) (n : ℕ) :
    ∀ u ∈ Icc s T, u ≤ s + n * δ → ‖f u - f s‖ ≤ n * η := by
  induction n with
  | zero =>
    intro u hu hus
    have : u = s := le_antisymm (by simpa using hus) hu.1
    simp [this]
  | succ n ih =>
    intro u hu hus
    have hη : 0 ≤ η := (norm_nonneg _).trans (hf u hu u hu (by simp [hδ.le]))
    by_cases hle : u ≤ s + n * δ
    · exact (ih u hu hle).trans (by push_cast; nlinarith)
    · have hη' : η ≤ ((n + 1 : ℕ) : ℝ) * η := by push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) n]
      push_cast at hus hle
      by_cases hsd : s ≤ u - δ
      · have hu' : u - δ ∈ Icc s T := ⟨hsd, by linarith [hu.2]⟩
        have h1 := hf u hu (u - δ) hu' (by rw [sub_sub_cancel, abs_of_pos hδ])
        have h2 := ih (u - δ) hu' (by linarith)
        calc ‖f u - f s‖ ≤ ‖f u - f (u - δ)‖ + ‖f (u - δ) - f s‖ :=
              norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ η + n * η := add_le_add h1 h2
          _ = ((n + 1 : ℕ) : ℝ) * η := by push_cast; ring
      · have hs : s ∈ Icc s T := ⟨le_rfl, hu.1.trans hu.2⟩
        exact (hf u hu s hs (by rw [abs_of_nonneg (by linarith [hu.1])]; linarith)).trans hη'

theorem capCoord_gram_min {b E s T h : ℝ} {q : Fin p → ℝ → ℝ}
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} (e : GIdx K p M) (t : ℝ) :
    capCoord b E s T h q W Vs (Sum.inl e) t =
      fun y => gramEntry e (closedGramAt b E s T h q W ⌊(W : ℝ) * min t T⌋₊ Vs y -
        closedJump b s T q W ⌊(W : ℝ) * min t T⌋₊ y) := rfl

theorem capCoord_gram_s {b E s T h : ℝ} (hsT : s < T) {q : Fin p → ℝ → ℝ}
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} (e : GIdx K p M)
    (y : SampledPath W p M × ℝ) :
    capCoord b E s T h q W Vs (Sum.inl e) s y =
      gramEntry e (closedGramAt b E s T h q W ⌊(W : ℝ) * s⌋₊ Vs y) := by
  simp [capCoord_gram_min, min_eq_left hsT.le, closedJump]

variable {b E s T h : ℝ} {q : Fin p → ℝ → ℝ}
  {Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}

/-- The modulus event of a Gram coordinate on `[s, T']` lies in that of `ClosedTightS` on `[s, T]`. -/
theorem modulus_subset (hsT : s < T) (e : GIdx K p M) {T' δ η : ℝ} :
    {y : SampledPath W p M × ℝ | y.1.1 ∈ physCapEvent b E s h K W ∧
      y ∈ {y | ∃ t ∈ Icc s T', ∃ t' ∈ Icc s T', |t - t'| ≤ δ ∧
        η < ‖capCoord b E s T h q W (Vs W) (Sum.inl e) t y -
          capCoord b E s T h q W (Vs W) (Sum.inl e) t' y‖}} ⊆
      {y | y.1.1 ∈ physCapEvent b E s h K W ∧ ∃ t ∈ Icc s T, ∃ t' ∈ Icc s T,
        |t - t'| ≤ δ ∧ η < ‖gramEntry e
          (closedGramAt b E s T h q W ⌊(W : ℝ) * t⌋₊ (Vs W) y -
            closedJump b s T q W ⌊(W : ℝ) * t⌋₊ y -
            (closedGramAt b E s T h q W ⌊(W : ℝ) * t'⌋₊ (Vs W) y -
              closedJump b s T q W ⌊(W : ℝ) * t'⌋₊ y))‖} := by
  rintro y ⟨hcap, t, ht, t', ht', htt, hη⟩
  refine ⟨hcap, min t T, ⟨?_, min_le_right _ _⟩, min t' T, ⟨?_, min_le_right _ _⟩, ?_, ?_⟩
  · exact le_min ht.1 hsT.le
  · exact le_min ht'.1 hsT.le
  · exact (abs_min_sub_min_le_max _ _ _ _).trans (by simp [htt])
  · rwa [gramEntry_sub]

section Seq

variable (hTS : ClosedTightS) (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
  (hs : 0 < s) (hsT : s < T) (hq : ∀ i, IsSourceTest s T (q i)) (hh0 : 0 < h) (hh1 : h < 1)
  (hM : 0 < M) (hVs : ∀ᶠ W in atTop, IsTimeSFrame b E s h K W (Vs W)) {Wn : ℕ → ℕ}
  (hWn : Tendsto Wn atTop atTop) {c : ℝ} (hc : 0 < c)
  (hcap : ∀ n, ENNReal.ofReal c ≤ lawW b T q M (Wn n) (capY b E s h K (Wn n) p M))

include hTS hb0 hb hE1 hE2 hs hsT hq hh0 hh1 hM hVs hWn hc hcap

/-- **The conditioned modulus of a Gram coordinate on `[s, T']`.** -/
theorem gram_modulus (e : GIdx K p M) (T' η θ : ℝ) (hη : 0 < η) (hθ : 0 < θ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      condLaw b E s T h q K M (Wn n) {y | ∃ t ∈ Icc s T', ∃ t' ∈ Icc s T', |t - t'| ≤ δ ∧
        η < ‖capCoord b E s T h q (Wn n) (Vs (Wn n)) (Sum.inl e) t y -
          capCoord b E s T h q (Wn n) (Vs (Wn n)) (Sum.inl e) t' y‖} ≤ ENNReal.ofReal θ := by
  have hq' : ∀ i x, 0 ≤ q i x := fun i => (hq i).1
  obtain ⟨-, hmod⟩ := hTS b hb0 hb E hE1 hE2 s T hs hsT p q hq h hh0 hh1 K M hM Vs hVs e s le_rfl
    hsT.le
  obtain ⟨δ, hδ, W₀, hW₀⟩ := hmod η (c * θ) hη (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hWn.eventually (eventually_ge_atTop W₀))
  exact ⟨δ, hδ, N, fun n hn => condLaw_le (by linarith) hE1 hE2 hq' hc (hcap n)
    ((measure_mono (modulus_subset hsT e)).trans (hW₀ _ (hN n hn)))⟩

/-- **One-time tightness of a Gram coordinate at `t ≥ s`.** -/
theorem gram_tight (e : GIdx K p M) {t : ℝ} (ht : s ≤ t) (θ : ℝ) (hθ : 0 < θ) :
    ∃ (C : ℝ) (N : ℕ), ∀ n, N ≤ n →
      condLaw b E s T h q K M (Wn n)
        {y | C < ‖capCoord b E s T h q (Wn n) (Vs (Wn n)) (Sum.inl e) t y‖} ≤
          ENNReal.ofReal θ := by
  have hq' : ∀ i x, 0 ≤ q i x := fun i => (hq i).1
  obtain ⟨htight, hmod⟩ := hTS b hb0 hb E hE1 hE2 s T hs hsT p q hq h hh0 hh1 K M hM Vs hVs e s
    le_rfl hsT.le
  obtain ⟨C₀, W₁, hW₁⟩ := htight (c * θ / 2) (by positivity)
  obtain ⟨δ, hδ, W₂, hW₂⟩ := hmod 1 (c * θ / 2) one_pos (by positivity)
  set m : ℕ := ⌈(T - s) / δ⌉₊
  have hm : T ≤ s + m * δ := by
    have := mul_le_mul_of_nonneg_right (Nat.le_ceil ((T - s) / δ)) hδ.le
    rw [div_mul_cancel₀ _ hδ.ne'] at this
    linarith
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hWn.eventually (eventually_ge_atTop (max W₁ W₂)))
  refine ⟨C₀ + m, N, fun n hn => condLaw_le (by linarith) hE1 hE2 hq' hc (hcap n) ?_⟩
  set W := Wn n
  have hsub : {y : SampledPath W p M × ℝ | y.1.1 ∈ physCapEvent b E s h K W ∧
      y ∈ {y | C₀ + m < ‖capCoord b E s T h q W (Vs W) (Sum.inl e) t y‖}} ⊆
      {y | y.1.1 ∈ physCapEvent b E s h K W ∧
        C₀ < ‖gramEntry e (closedGramAt b E s T h q W ⌊(W : ℝ) * s⌋₊ (Vs W) y)‖} ∪
      {y | y.1.1 ∈ physCapEvent b E s h K W ∧ ∃ t ∈ Icc s T, ∃ t' ∈ Icc s T,
        |t - t'| ≤ δ ∧ 1 < ‖gramEntry e
          (closedGramAt b E s T h q W ⌊(W : ℝ) * t⌋₊ (Vs W) y -
            closedJump b s T q W ⌊(W : ℝ) * t⌋₊ y -
            (closedGramAt b E s T h q W ⌊(W : ℝ) * t'⌋₊ (Vs W) y -
              closedJump b s T q W ⌊(W : ℝ) * t'⌋₊ y))‖} := by
    rintro y ⟨hcap, hy⟩
    by_contra hno
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_and, not_exists, not_lt] at hno
    obtain ⟨h1, h2⟩ := hno
    set f : ℝ → ℂ := fun u => gramEntry e (closedGramAt b E s T h q W ⌊(W : ℝ) * u⌋₊ (Vs W) y -
      closedJump b s T q W ⌊(W : ℝ) * u⌋₊ y) with hf
    have hmodf : ∀ u ∈ Icc s T, ∀ u' ∈ Icc s T, |u - u'| ≤ δ → ‖f u - f u'‖ ≤ 1 :=
      fun u hu u' hu' huu => by
        have := h2 hcap u hu u' hu' huu
        simpa only [hf, gramEntry_sub] using this
    have hu : min t T ∈ Icc s T := ⟨le_min ht hsT.le, min_le_right _ _⟩
    have hch := chain_bound hδ hmodf m (min t T) hu ((min_le_right _ _).trans hm)
    have hfs : f s = gramEntry e (closedGramAt b E s T h q W ⌊(W : ℝ) * s⌋₊ (Vs W) y) := by
      simp [hf, closedJump]
    have hXt : capCoord b E s T h q W (Vs W) (Sum.inl e) t y = f (min t T) := rfl
    have hy' : C₀ + m < ‖f (min t T)‖ := by rw [← hXt]; exact hy
    have h3 : ‖f (min t T)‖ ≤ ‖f s‖ + ‖f (min t T) - f s‖ := norm_le_insert' _ _
    have h4 : ‖f s‖ ≤ C₀ := by rw [hfs]; exact h1 hcap
    linarith
  have hW₁' := hW₁ W ((le_max_left _ _).trans (hN n hn))
  have hW₂' := hW₂ W ((le_max_right _ _).trans (hN n hn))
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ((add_le_add hW₁' hW₂').trans ?_))
  rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves]

end Seq

end BlockBand.SourceProcess.CapLaw
