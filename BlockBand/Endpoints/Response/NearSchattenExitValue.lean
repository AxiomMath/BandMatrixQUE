module

public import BlockBand.Endpoints.Response.NearSchattenExitTools

/-!
# The exit and end values of the stopped clock

Part of the proof of the near-Schatten decay theorem.

**Proved here** (fixed width `W`, no probabilistic input).
* `nsx_value_pointwise`: for every path,
  `Tr f_ε(A_{j₂}) + 1{σ>j₁}(Φ_π(A_{j₂∧σ}))⁻ ≤ 1{σ>j₁}(Φ_π(A_{j₂∧σ}))⁺ + δ(K+1)
    + pε^{p-1} 1{σ≤j₂} sup Tr Q + (Σ_r|a_r|) 1_J (1 + (sup Tr Q)^{N+1})`,
  `J` the event of a one-step jump of `Tr(QP)` larger than `1` on `[j₁, j₂)`. On `{σ > j₂}`:
  `|π - f_ε| ≤ δx` on the spectrum in `[0, K]`; on `{j₁ < σ ≤ j₂}` off `J`: the exit value
  `Tr A_σ ≤ Tr A_{σ-1} + 1 ≤ K + 1`, so `Φ_π(A_σ) ≥ -δ(K+1)`; on `J`: the polynomial growth bound;
  on `{σ ≤ j₂}`: `Tr f_ε(A) ≤ pε^{p-1} Tr A`.
* `nsx_value_le`: its integrated form.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Matrix Filter Topology Set Finset
open scoped ENNReal ComplexOrder
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Endpoints

variable {W : ℕ}

/-!
## Spectral bounds at one length
-/

theorem nsx_nuclearNorm_nonneg {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) :
    0 ≤ nuclearNorm M := by
  unfold nuclearNorm
  exact Multiset.sum_nonneg fun x hx => by
    obtain ⟨z, -, rfl⟩ := Multiset.mem_map.1 hx
    exact norm_nonneg z

/-- Before the stop, at lengths `j ≥ εW`, `Tr A_j ≤ K` (no unitarity needed). -/
theorem nsx_trA_le_of_alive {b E : ℝ} {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) {K ε : ℝ} {j : ℕ}
    {ω : GrowthPath W} (h : ω ∈ alive b E (noTags W) (fun _ : Fin 1 => q) K ε W j)
    (hj : ε * W ≤ j) : (nearClock b E W j q ω).trace.re ≤ K := by
  have hL := nsf_traceLoad_le_of_alive h hj
  rw [nsf_traceLoad_eq] at hL
  have := (trace_nearClock_le b E W j q hq ω).2
  have := nsx_nuclearNorm_nonneg (pathCurrent b E W j ω)
  linarith

/-- `|Φ_π(A_j) - Tr f_ε(A_j)| ≤ δ Tr A_j` when `Tr A_j ≤ K + 1`. -/
theorem nsx_clock_sub_le {b E p ε : ℝ} {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) {K δ : ℝ} {a : ℕ → ℝ}
    {N : ℕ} (h0 : ∀ x ∈ Icc 0 (K + 1), |nsfPolyFun a N x - nsfRegFun p ε x| ≤ δ * x) {j : ℕ}
    (ω : GrowthPath W) (hA : (nearClock b E W j q ω).trace.re ≤ K + 1) :
    |(polyValue b E (noTags W) (fun _ => q) W j ω (nsfClockPoly a N)).re -
        nsClockSum (nsRegKernel p ε) (nearClock b E W j q ω)| ≤
      δ * (nearClock b E W j q ω).trace.re := by
  have hpsd := ns_nearClock_posSemidef b E W j q hq ω
  rw [nsf_polyValue_clockPoly_path b E hq W j ω (noTags W) a N, Complex.ofReal_re,
    nsf_clockSum_regKernel hpsd]
  have hsum : ∑ i, hpsd.1.eigenvalues i = (nearClock b E W j q ω).trace.re := by
    rw [hpsd.1.trace_eq_sum_eigenvalues, Complex.re_sum]; simp
  have hlam : ∀ i, hpsd.1.eigenvalues i ∈ Icc 0 (K + 1) := fun i =>
    ⟨hpsd.eigenvalues_nonneg i, (nsf_eigenvalue_le_trace hpsd i).trans hA⟩
  have h := nsf_sum_regFun_sub_le h0 hlam
  rwa [hsum] at h

/-- `0 ≤ Tr f_ε(A) ≤ pε^{p-1} Tr A`. -/
theorem nsx_regTrace_le {b E p ε : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 < ε) {q : ℝ → ℝ}
    (hq : ∀ x, 0 ≤ q x) (j : ℕ) (ω : GrowthPath W) :
    0 ≤ nsClockSum (nsRegKernel p ε) (nearClock b E W j q ω) ∧
      nsClockSum (nsRegKernel p ε) (nearClock b E W j q ω) ≤
        p * ε ^ (p - 1) * (nearClock b E W j q ω).trace.re := by
  have hpsd := ns_nearClock_posSemidef b E W j q hq ω
  refine ⟨ns_clockSum_nonneg (fun x _ => ns_regKernel_nonneg hp0 hε x) hpsd, ?_⟩
  rw [ns_clockSum_eq _ hpsd.1]
  have hsum : ∑ i, hpsd.1.eigenvalues i = (nearClock b E W j q ω).trace.re := by
    rw [hpsd.1.trace_eq_sum_eigenvalues, Complex.re_sum]; simp
  rw [← hsum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [mul_comm (p * ε ^ (p - 1))]
  exact mul_le_mul_of_nonneg_left (nsg_regKernel_le hp0 hp1 hε _) (hpsd.eigenvalues_nonneg i)

/-- `|Φ_π(A_j)| ≤ (Σ_r|a_r|)(1 + (Tr Q_j)^{N+1})`. -/
theorem nsx_abs_clock_le {b E : ℝ} {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) (a : ℕ → ℝ) (N : ℕ) (j : ℕ)
    (ω : GrowthPath W) :
    |(polyValue b E (noTags W) (fun _ => q) W j ω (nsfClockPoly a N)).re| ≤
      (∑ r ∈ range N, |a r|) * (1 + (intervalSource b E W j q ω).trace.re ^ (N + 1)) := by
  have hpsd := ns_nearClock_posSemidef b E W j q hq ω
  rw [nsf_polyValue_clockPoly_path b E hq W j ω (noTags W) a N, Complex.ofReal_re]
  have hsum : ∑ i, hpsd.1.eigenvalues i = (nearClock b E W j q ω).trace.re := by
    rw [hpsd.1.trace_eq_sum_eigenvalues, Complex.re_sum]; simp
  exact nss_abs_sum_polyFun_le a N (fun i => hpsd.eigenvalues_nonneg i)
    (hsum.trans_le (trace_nearClock_le b E W j q hq ω).2)

/-- `Tr Q_j ≤ sup Tr Q` on the window. -/
theorem nsx_trQ_le_supQ (b E : ℝ) {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) {ε T : ℝ} {j : ℕ}
    (hj1 : ε * W ≤ j) (hj2 : (j : ℝ) ≤ T * W) (ω : GrowthPath W) :
    ENNReal.ofReal (intervalSource b E W j q ω).trace.re ≤ nsxSupQ b E q ε T W ω := by
  have e : ENNReal.ofReal (intervalSource b E W j q ω).trace.re =
      ‖sourceTrace b E (noTags W) (fun _ : Fin 1 => q) W j ω (Sum.inr 0)‖ₑ := by
    rw [nsx_sourceTrace_eq, Real.enorm_eq_ofReal_abs,
      abs_of_nonneg (trace_intervalSource_re_nonneg b E W j q hq ω)]
  rw [e]
  exact le_iSup₂ (f := fun (i : ℕ) (_ : ε * W ≤ i ∧ (i : ℝ) ≤ T * W) =>
    ‖sourceTrace b E (noTags W) (fun _ : Fin 1 => q) W i ω (Sum.inr 0)‖ₑ) j ⟨hj1, hj2⟩

/-- The growth bound in `ℝ≥0∞`: `(Φ_π(A_j))^± ≤ (Σ|a_r|)(1 + (sup Tr Q)^{N+1})`. -/
theorem nsx_ofReal_abs_clock_le {b E : ℝ} {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) (a : ℕ → ℝ)
    (N : ℕ) {ε T : ℝ} {j : ℕ} (hj1 : ε * W ≤ j) (hj2 : (j : ℝ) ≤ T * W) (ω : GrowthPath W) :
    ENNReal.ofReal |(polyValue b E (noTags W) (fun _ => q) W j ω (nsfClockPoly a N)).re| ≤
      ENNReal.ofReal (∑ r ∈ range N, |a r|) * (1 + nsxSupQ b E q ε T W ω ^ (N + 1)) := by
  have hA0 : 0 ≤ ∑ r ∈ range N, |a r| := Finset.sum_nonneg fun r _ => abs_nonneg _
  have hQ0 := trace_intervalSource_re_nonneg b E W j q hq ω
  refine (ENNReal.ofReal_le_ofReal (nsx_abs_clock_le hq a N j ω)).trans ?_
  rw [ENNReal.ofReal_mul hA0, ENNReal.ofReal_add zero_le_one (by positivity),
    ENNReal.ofReal_one, ENNReal.ofReal_pow hQ0]
  gcongr
  exact nsx_trQ_le_supQ b E hq hj1 hj2 ω

/-!
## The stopped index
-/

theorem nsx_stopIdx_of_alive {j₂ : ℕ} {σ : ℕ∞} (h : (j₂ : ℕ∞) < σ) : nssStopIdx j₂ σ = j₂ := by
  unfold nssStopIdx
  rw [min_eq_left h.le, ENat.toNat_natCast]

theorem nsx_exit_index {j₁ j₂ : ℕ} {σ : ℕ∞} (h1 : (j₁ : ℕ∞) < σ) (h2 : ¬ (j₂ : ℕ∞) < σ) :
    ∃ s : ℕ, σ = s ∧ j₁ < s ∧ s ≤ j₂ ∧ nssStopIdx j₂ σ = s := by
  have h2' : σ ≤ j₂ := not_lt.1 h2
  obtain ⟨s, rfl⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (ENat.natCast_ne_top j₂) h2')
  refine ⟨s, rfl, by exact_mod_cast h1, by exact_mod_cast h2', ?_⟩
  unfold nssStopIdx
  rw [min_eq_right h2', ENat.toNat_natCast]

/-- `ofReal x + ofReal(-y) ≤ ofReal y + ofReal w` from `x - w ≤ y`, `x ≥ 0`. -/
theorem nsx_ofReal_add_neg_le {x y w : ℝ} (hx : 0 ≤ x) (h : x - w ≤ y) :
    ENNReal.ofReal x + ENNReal.ofReal (-y) ≤ ENNReal.ofReal y + ENNReal.ofReal w := by
  rcases le_or_gt 0 y with hy | hy
  · rw [ENNReal.ofReal_of_nonpos (show -y ≤ 0 by linarith), add_zero]
    exact (ENNReal.ofReal_le_ofReal (by linarith)).trans ENNReal.ofReal_add_le
  · rw [ENNReal.ofReal_of_nonpos (show y ≤ 0 from hy.le), zero_add,
      ← ENNReal.ofReal_add hx (by linarith)]
    exact ENNReal.ofReal_le_ofReal (by linarith)

/-!
## The pointwise value comparison
-/

section Value

variable {b E p ε : ℝ} {q : ℝ → ℝ} {K u₁ u₂ δ : ℝ} {a : ℕ → ℝ} {N : ℕ}

/-- The exit value off the jump event: `(Φ_π(A_σ))⁻ ≤ δ(K+1)` on `{j₁ < σ ≤ j₂}`. -/
theorem nsx_exit_neg_le (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 < ε) (hq : ∀ x, 0 ≤ q x)
    (hδ : 0 ≤ δ)
    (h0 : ∀ x ∈ Icc 0 (K + 1), |nsfPolyFun a N x - nsfRegFun p ε x| ≤ δ * x)
    (hjW : u₁ / 2 * W ≤ ⌊(W : ℝ) * u₁⌋₊) {ω : GrowthPath W}
    (hJ : ω ∉ nsxJump b E q u₁ u₂ W) {s : ℕ}
    (hσ : traceStop b E (noTags W) (fun _ : Fin 1 => q) K (u₁ / 2) W ω = s)
    (hs1 : ⌊(W : ℝ) * u₁⌋₊ < s) (hs2 : s ≤ ⌊(W : ℝ) * u₂⌋₊) :
    ENNReal.ofReal (-(polyValue b E (noTags W) (fun _ => q) W s ω (nsfClockPoly a N)).re) ≤
      ENNReal.ofReal (δ * (K + 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by omega⟩
  have hal : ω ∈ alive b E (noTags W) (fun _ : Fin 1 => q) K (u₁ / 2) W m := by
    show (m : ℕ∞) < traceStop b E (noTags W) (fun _ : Fin 1 => q) K (u₁ / 2) W ω
    rw [hσ]; exact_mod_cast Nat.lt_succ_self m
  have hm1 : ⌊(W : ℝ) * u₁⌋₊ ≤ m := by omega
  have hmW : u₁ / 2 * W ≤ m := hjW.trans (by exact_mod_cast hm1)
  have hAm := nsx_trA_le_of_alive hq hal hmW
  have hstep := nsx_trA_step_le b E q u₁ u₂ hJ hm1 (by omega)
  have hA0 := (trace_nearClock_le b E W (m + 1) q hq ω).1
  have hAs : (nearClock b E W (m + 1) q ω).trace.re ≤ K + 1 := by linarith
  have hc := (abs_le.1 (nsx_clock_sub_le hq h0 ω hAs)).1
  have hf := (nsx_regTrace_le (b := b) (E := E) hp0 hp1 hε hq (m + 1) ω).1
  refine ENNReal.ofReal_le_ofReal ?_
  nlinarith

/-- The window `εW ≤ j ≤ TW` for `j₁ ≤ j ≤ j₂`. -/
theorem nsx_window {u₁ u₂ : ℝ} (hjW : u₁ / 2 * W ≤ ⌊(W : ℝ) * u₁⌋₊)
    (hj₂T : (⌊(W : ℝ) * u₂⌋₊ : ℝ) ≤ (u₂ + 1) * W) {j : ℕ} (hj1 : ⌊(W : ℝ) * u₁⌋₊ ≤ j)
    (hj2 : j ≤ ⌊(W : ℝ) * u₂⌋₊) : u₁ / 2 * W ≤ j ∧ (j : ℝ) ≤ (u₂ + 1) * W :=
  ⟨hjW.trans (by exact_mod_cast hj1), (Nat.cast_le.2 hj2).trans hj₂T⟩

/-- **The pointwise value comparison** at the stop. -/
theorem nsx_value_pointwise (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 < ε) (hq : ∀ x, 0 ≤ q x)
    (hδ : 0 ≤ δ) (h0 : ∀ x ∈ Icc 0 (K + 1), |nsfPolyFun a N x - nsfRegFun p ε x| ≤ δ * x)
    (hjW : u₁ / 2 * W ≤ ⌊(W : ℝ) * u₁⌋₊) (h12 : ⌊(W : ℝ) * u₁⌋₊ ≤ ⌊(W : ℝ) * u₂⌋₊)
    (hj₂T : (⌊(W : ℝ) * u₂⌋₊ : ℝ) ≤ (u₂ + 1) * W) (ω : GrowthPath W) :
    ENNReal.ofReal (nsClockSum (nsRegKernel p ε) (nearClock b E W ⌊(W : ℝ) * u₂⌋₊ q ω)) +
        (nsfAlive b E q K u₁ W ⌊(W : ℝ) * u₁⌋₊).indicator (fun ω => ENNReal.ofReal
          (-nssStoppedClock b E q K u₁ a N W ⌊(W : ℝ) * u₂⌋₊ ω)) ω ≤
      (nsfAlive b E q K u₁ W ⌊(W : ℝ) * u₁⌋₊).indicator (fun ω => ENNReal.ofReal
          (nssStoppedClock b E q K u₁ a N W ⌊(W : ℝ) * u₂⌋₊ ω)) ω +
        (ENNReal.ofReal (δ * (K + 1)) + ENNReal.ofReal (p * ε ^ (p - 1)) *
            (nsfAlive b E q K u₁ W ⌊(W : ℝ) * u₂⌋₊)ᶜ.indicator
              (fun ω => nsxSupQ b E q (u₁ / 2) (u₂ + 1) W ω ^ 1) ω +
          ENNReal.ofReal (∑ r ∈ range N, |a r|) *
            ((nsxJump b E q u₁ u₂ W).indicator 1 ω + (nsxJump b E q u₁ u₂ W).indicator
              (fun ω => nsxSupQ b E q (u₁ / 2) (u₂ + 1) W ω ^ (N + 1)) ω)) := by
  set j₁ := ⌊(W : ℝ) * u₁⌋₊ with hj₁
  set j₂ := ⌊(W : ℝ) * u₂⌋₊ with hj₂
  set S := nsxSupQ b E q (u₁ / 2) (u₂ + 1) W with hS
  set J := nsxJump b E q u₁ u₂ W with hJdef
  set Aπ := ∑ r ∈ range N, |a r| with hAπ
  set σ := traceStop b E (noTags W) (fun _ : Fin 1 => q) K (u₁ / 2) W ω with hσ
  have hΦ : nssStoppedClock b E q K u₁ a N W j₂ ω =
      (polyValue b E (noTags W) (fun _ => q) W (nssStopIdx j₂ σ) ω (nsfClockPoly a N)).re := rfl
  have hw₂ := nsx_window hjW hj₂T h12 le_rfl
  have hc0 : 0 ≤ p * ε ^ (p - 1) := mul_nonneg hp0 (Real.rpow_nonneg hε.le _)
  obtain ⟨hf0, hfle⟩ := nsx_regTrace_le (b := b) (E := E) hp0 hp1 hε hq j₂ ω
  by_cases h2 : ω ∈ nsfAlive b E q K u₁ W j₂
  · have h2' : (j₂ : ℕ∞) < σ := h2
    have h1 : ω ∈ nsfAlive b E q K u₁ W j₁ :=
      show (j₁ : ℕ∞) < σ from lt_of_le_of_lt (by exact_mod_cast h12) h2'
    rw [Set.indicator_of_mem h1, Set.indicator_of_mem h1, hΦ, nsx_stopIdx_of_alive h2']
    have hA := nsx_trA_le_of_alive hq h2 hw₂.1
    have hA0 := (trace_nearClock_le b E W j₂ q hq ω).1
    have hc := (abs_le.1 (nsx_clock_sub_le hq h0 ω (by linarith))).1
    have key := nsx_ofReal_add_neg_le (w := δ * (K + 1)) hf0 (by nlinarith)
    refine key.trans ?_
    gcongr
    exact le_add_right (le_add_right le_rfl)
  · rw [Set.indicator_of_mem (show ω ∈ (nsfAlive b E q K u₁ W j₂)ᶜ from h2), pow_one]
    have hTf : ENNReal.ofReal (nsClockSum (nsRegKernel p ε) (nearClock b E W j₂ q ω)) ≤
        ENNReal.ofReal (p * ε ^ (p - 1)) * S ω := by
      refine (ENNReal.ofReal_le_ofReal hfle).trans ?_
      rw [ENNReal.ofReal_mul hc0]
      gcongr
      exact nsx_trA_le_supQ b E hq hw₂.1 hw₂.2 ω
    have hX : (nsfAlive b E q K u₁ W j₁).indicator (fun ω => ENNReal.ofReal
          (-nssStoppedClock b E q K u₁ a N W j₂ ω)) ω ≤
        ENNReal.ofReal (δ * (K + 1)) + ENNReal.ofReal Aπ *
          (J.indicator 1 ω + J.indicator (fun ω => S ω ^ (N + 1)) ω) := by
      by_cases h1 : ω ∈ nsfAlive b E q K u₁ W j₁
      · obtain ⟨s, hs, hs1, hs2, hidx⟩ := nsx_exit_index (show (j₁ : ℕ∞) < σ from h1) h2
        rw [Set.indicator_of_mem h1, hΦ, hidx]
        by_cases hJ : ω ∈ J
        · rw [Set.indicator_of_mem hJ, Set.indicator_of_mem hJ, Pi.one_apply]
          have hw := nsx_window hjW hj₂T hs1.le hs2
          refine le_add_left ((ENNReal.ofReal_le_ofReal (neg_le_abs _)).trans ?_)
          exact nsx_ofReal_abs_clock_le hq a N hw.1 hw.2 ω
        · exact le_add_right (nsx_exit_neg_le hp0 hp1 hε hq hδ h0 hjW hJ hs hs1 hs2)
      · rw [Set.indicator_of_notMem h1]; exact zero_le
    calc _ ≤ ENNReal.ofReal (p * ε ^ (p - 1)) * S ω + (ENNReal.ofReal (δ * (K + 1)) +
          ENNReal.ofReal Aπ * (J.indicator 1 ω + J.indicator (fun ω => S ω ^ (N + 1)) ω)) :=
          add_le_add hTf hX
      _ = ENNReal.ofReal (δ * (K + 1)) + ENNReal.ofReal (p * ε ^ (p - 1)) * S ω +
          ENNReal.ofReal Aπ * (J.indicator 1 ω + J.indicator (fun ω => S ω ^ (N + 1)) ω) := by
          ring
      _ ≤ _ := le_add_self

/-- **The integrated value comparison** at a fixed width:
`E Tr f_ε(A_{j₂}) + E[1{σ>j₁}(Φ_π)⁻] ≤ E[1{σ>j₁}(Φ_π)⁺] + δ(K+1) + pε^{p-1} E[1{σ≤j₂} sup Tr Q]
  + (Σ|a_r|)(P(J) + E[1_J (sup Tr Q)^{N+1}])`. -/
theorem nsx_value_le (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 < ε) (hq : ∀ x, 0 ≤ q x)
    (hδ : 0 ≤ δ) (h0 : ∀ x ∈ Icc 0 (K + 1), |nsfPolyFun a N x - nsfRegFun p ε x| ≤ δ * x)
    (hjW : u₁ / 2 * W ≤ ⌊(W : ℝ) * u₁⌋₊) (h12 : ⌊(W : ℝ) * u₁⌋₊ ≤ ⌊(W : ℝ) * u₂⌋₊)
    (hj₂T : (⌊(W : ℝ) * u₂⌋₊ : ℝ) ≤ (u₂ + 1) * W) :
    ∫⁻ ω, ENNReal.ofReal (nsClockSum (nsRegKernel p ε)
          (nearClock b E W ⌊(W : ℝ) * u₂⌋₊ q ω)) ∂growthPathLaw W b +
        ∫⁻ ω, (nsfAlive b E q K u₁ W ⌊(W : ℝ) * u₁⌋₊).indicator (fun ω => ENNReal.ofReal
          (-nssStoppedClock b E q K u₁ a N W ⌊(W : ℝ) * u₂⌋₊ ω)) ω ∂growthPathLaw W b ≤
      ∫⁻ ω, (nsfAlive b E q K u₁ W ⌊(W : ℝ) * u₁⌋₊).indicator (fun ω => ENNReal.ofReal
          (nssStoppedClock b E q K u₁ a N W ⌊(W : ℝ) * u₂⌋₊ ω)) ω ∂growthPathLaw W b +
        (ENNReal.ofReal (δ * (K + 1)) + ENNReal.ofReal (p * ε ^ (p - 1)) *
            ∫⁻ ω, (nsfAlive b E q K u₁ W ⌊(W : ℝ) * u₂⌋₊)ᶜ.indicator
              (fun ω => nsxSupQ b E q (u₁ / 2) (u₂ + 1) W ω ^ 1) ω ∂growthPathLaw W b +
          ENNReal.ofReal (∑ r ∈ range N, |a r|) *
            (growthPathLaw W b (nsxJump b E q u₁ u₂ W) +
              ∫⁻ ω, (nsxJump b E q u₁ u₂ W).indicator
                (fun ω => nsxSupQ b E q (u₁ / 2) (u₂ + 1) W ω ^ (N + 1)) ω
                ∂growthPathLaw W b)) := by
  have hP := passDeriv_isProbabilityMeasure_growthPathLaw W b
  have hSm := nsx_measurable_supQ b E q (u₁ / 2) (u₂ + 1) W
  have hJm := nsx_measurableSet_jump b E q u₁ u₂ W
  have hDm := (nss_measurableSet_alive b E (noTags W) q K (u₁ / 2) W ⌊(W : ℝ) * u₂⌋₊).compl
  have hf : Measurable ((nsfAlive b E q K u₁ W ⌊(W : ℝ) * u₂⌋₊)ᶜ.indicator
      (fun ω => nsxSupQ b E q (u₁ / 2) (u₂ + 1) W ω ^ 1)) := (hSm.pow_const 1).indicator hDm
  have hg : Measurable ((nsxJump b E q u₁ u₂ W).indicator (1 : GrowthPath W → ℝ≥0∞)) :=
    measurable_one.indicator hJm
  have hh : Measurable ((nsxJump b E q u₁ u₂ W).indicator
      (fun ω => nsxSupQ b E q (u₁ / 2) (u₂ + 1) W ω ^ (N + 1))) :=
    (hSm.pow_const _).indicator hJm
  refine (le_lintegral_add _ _).trans ?_
  refine (lintegral_mono fun ω => nsx_value_pointwise hp0 hp1 hε hq hδ h0 hjW h12 hj₂T ω).trans
    (le_of_eq ?_)
  set c₁ := ENNReal.ofReal (δ * (K + 1))
  set c₂ := ENNReal.ofReal (p * ε ^ (p - 1))
  set c₃ := ENNReal.ofReal (∑ r ∈ range N, |a r|)
  set f := (nsfAlive b E q K u₁ W ⌊(W : ℝ) * u₂⌋₊)ᶜ.indicator
    (fun ω => nsxSupQ b E q (u₁ / 2) (u₂ + 1) W ω ^ 1)
  set g := (nsxJump b E q u₁ u₂ W).indicator (1 : GrowthPath W → ℝ≥0∞)
  set h := (nsxJump b E q u₁ u₂ W).indicator
    (fun ω => nsxSupQ b E q (u₁ / 2) (u₂ + 1) W ω ^ (N + 1))
  have hgh : Measurable (fun ω => g ω + h ω) := hg.add hh
  have h12m : Measurable (fun ω => c₁ + c₂ * f ω) := measurable_const.add (hf.const_mul _)
  have hrest : Measurable (fun ω => c₁ + c₂ * f ω + c₃ * (g ω + h ω)) :=
    h12m.add (hgh.const_mul _)
  rw [lintegral_add_right _ hrest]
  congr 1
  rw [lintegral_add_left h12m, lintegral_add_left measurable_const, lintegral_const,
    measure_univ, mul_one, lintegral_const_mul _ hf, lintegral_const_mul _ hgh,
    lintegral_add_left hg, lintegral_indicator_one hJm]

end Value

end BlockBand.Endpoints
