module

public import BlockBand.Endpoints.Response.RemoteHigherExitTools

/-!
# The exit and end values of the stopped higher composite

Part of the proof of the remote higher-moment theorem; the `r`-analogue of
`NearSchattenExitValue`.

**Proved here** (fixed width `W`, no probabilistic input; values of `π` on `[0, K+1]` and of `G`
on `rhfRange p ε K` only).
* `rhx_ranges`: when `Tr A_j ≤ K + 1`, `|Tr π(A_j) - H_ε(A_j)| ≤ δ Tr A_j` and both lie in
  `rhfRange p ε K` (`δ ≤ 1`, `δ(K+1) ≤ ε^p/2`).
* `rhx_value_pointwise`: for every path,
  `(H_ε(A_{j₂})+ε^p)^r + 1{σ>j₁}(G(Φ_π)(A_{j₂∧σ}))⁻ ≤ 1{σ>j₁}(G(Φ_π)(A_{j₂∧σ}))⁺ + δ(BK+1)
    + c_end 1{σ≤j₂}(1 + (sup Tr Q)^{k+1}) + C_{π,G} 1_J (1 + (sup Tr Q)^{(N+1)(d+1)})`,
  `J` the event of a one-step jump of `Tr(QP)` larger than `1` on `[j₁, j₂)`. On `{σ > j₂}`:
  `G(Tr π) ≥ h(H_ε) - δ(BK+1)` (`h` is `B`-Lipschitz on the range); on `{j₁ < σ ≤ j₂}` off `J`:
  `Tr A_σ ≤ K + 1`, so `Tr π(A_σ) ∈ rhfRange` and `G(Tr π(A_σ)) ≥ h - δ ≥ -δ`; on `J`: the
  polynomial growth bound `rhf_abs_eval_le`; on `{σ ≤ j₂}`: `(H_ε+ε^p)^r ≤ c_end(1 + (Tr A)^{k+1})`
  (`r ≤ k + 1`).
* `rhx_value_le`: its integrated form.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Matrix Filter Topology Set Finset Polynomial
open scoped ENNReal ComplexOrder
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Endpoints

variable {W : ℕ}

/-!
## Constants
-/

/-- `c_end = L^r 2^{k+1}`, the end-value constant. -/
def rhxCEnd (p r ε : ℝ) (k : ℕ) : ℝ := rhxL p ε ^ r * 2 ^ (k + 1)

theorem rhx_CEnd_nonneg {p r ε : ℝ} (hp0 : 0 ≤ p) (hε : 0 < ε) (k : ℕ) : 0 ≤ rhxCEnd p r ε k := by
  have hL := rhx_one_le_L hp0 hε
  have := Real.rpow_nonneg (show (0 : ℝ) ≤ rhxL p ε by linarith) r
  unfold rhxCEnd; positivity

/-- `C_{π,G} = (Σ_i |g_i|)(2Σ_r|a_r| + 1)^d`, the growth constant of `G(Φ_π)`. -/
def rhxCG (a : ℕ → ℝ) (N : ℕ) (G : ℝ[X]) : ℝ :=
  (∑ i ∈ range (G.natDegree + 1), |G.coeff i|) * (2 * ∑ r ∈ range N, |a r| + 1) ^ G.natDegree

theorem rhx_CG_nonneg (a : ℕ → ℝ) (N : ℕ) (G : ℝ[X]) : 0 ≤ rhxCG a N G := by
  have h1 : 0 ≤ ∑ i ∈ range (G.natDegree + 1), |G.coeff i| :=
    Finset.sum_nonneg fun i _ => abs_nonneg _
  have h2 : 0 ≤ ∑ r ∈ range N, |a r| := Finset.sum_nonneg fun r _ => abs_nonneg _
  unfold rhxCG; positivity

/-- The growth exponent `(N+1)(d+1) - 1`. -/
def rhxExp (N d : ℕ) : ℕ := N * (d + 1) + d

theorem rhx_exp_succ (N d : ℕ) : (N + 1) * (d + 1) = rhxExp N d + 1 := by
  unfold rhxExp; ring

/-!
## Ranges and values at one length
-/

/-- When `Tr A_j ≤ K + 1`: `|Tr π(A_j) - H_ε(A_j)| ≤ δ Tr A_j`, and both lie in `rhfRange`. -/
theorem rhx_ranges {b E p ε : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 < ε) {q : ℝ → ℝ}
    (hq : ∀ x, 0 ≤ q x) {K δ : ℝ} {a : ℕ → ℝ} {N : ℕ}
    (h0 : ∀ x ∈ Icc 0 (K + 1), |nsfPolyFun a N x - nsfRegFun p ε x| ≤ δ * x) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) (hδK : δ * (K + 1) ≤ ε ^ p / 2) {j : ℕ} (ω : GrowthPath W)
    (hA : (nearClock b E W j q ω).trace.re ≤ K + 1) :
    |rhfClockVal b E q a N W j ω - nsClockSum (nsRegKernel p ε) (nearClock b E W j q ω)| ≤
        δ * (nearClock b E W j q ω).trace.re ∧
      rhfClockVal b E q a N W j ω ∈ rhfRange p ε K ∧
      nsClockSum (nsRegKernel p ε) (nearClock b E W j q ω) ∈ rhfRange p ε K := by
  have hc : |rhfClockVal b E q a N W j ω - nsClockSum (nsRegKernel p ε) (nearClock b E W j q ω)|
      ≤ δ * (nearClock b E W j q ω).trace.re := nsx_clock_sub_le hq h0 ω hA
  obtain ⟨hH0, hHle⟩ := nsx_regTrace_le (b := b) (E := E) hp0 hp1 hε hq j ω
  have hA0 := (trace_nearClock_le b E W j q hq ω).1
  have hεp := Real.rpow_pos_of_pos hε p
  have hM1 : 0 ≤ p * ε ^ (p - 1) := mul_nonneg hp0 (Real.rpow_nonneg hε.le _)
  have e1 : δ * (nearClock b E W j q ω).trace.re ≤ δ * (K + 1) := mul_le_mul_of_nonneg_left hA hδ0
  have e2 : δ * (nearClock b E W j q ω).trace.re ≤ 1 * (nearClock b E W j q ω).trace.re :=
    mul_le_mul_of_nonneg_right hδ1 hA0
  have e3 : p * ε ^ (p - 1) * (nearClock b E W j q ω).trace.re ≤ p * ε ^ (p - 1) * (K + 1) :=
    mul_le_mul_of_nonneg_left hA hM1
  obtain ⟨hc1, hc2⟩ := abs_le.1 hc
  refine ⟨hc, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

theorem rhx_H_nonneg {p r ε K y : ℝ} (hε : 0 < ε) (hy : y ∈ rhfRange p ε K) :
    0 ≤ rhfH (ε ^ p) r y := Real.rpow_nonneg (rhf_range_pos hε hy).le r

/-- The stopped value is `G(Tr π(A_{j₂∧σ}))`. -/
theorem rhx_stoppedValue_eq (b E : ℝ) {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) (K u₁ : ℝ) (a : ℕ → ℝ)
    (N : ℕ) (G : ℝ[X]) (W j₂ : ℕ) (ω : GrowthPath W) :
    rhfStoppedValue b E q K u₁ a N G W j₂ ω = G.eval (rhfClockVal b E q a N W
      (nssStopIdx j₂ (traceStop b E (noTags W) (fun _ : Fin 1 => q) K (u₁ / 2) W ω)) ω) := by
  unfold rhfStoppedValue
  rw [rhf_polyValue_composite b E hq, Complex.ofReal_re]

section Value

variable {b E p r ε : ℝ} {q : ℝ → ℝ} {K u₁ u₂ δ : ℝ} {a : ℕ → ℝ} {N : ℕ} {G : ℝ[X]}

/-- The exit value off the jump event: `(G(Tr π(A_σ)))⁻ ≤ δ(BK+1)` on `{j₁ < σ ≤ j₂}`. -/
theorem rhx_exit_neg_le (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 < ε) (hq : ∀ x, 0 ≤ q x)
    (hK : 0 ≤ K) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hδK : δ * (K + 1) ≤ ε ^ p / 2)
    (h0 : ∀ x ∈ Icc 0 (K + 1), |nsfPolyFun a N x - nsfRegFun p ε x| ≤ δ * x)
    (hG0 : ∀ y ∈ rhfRange p ε K, |G.eval y - rhfH (ε ^ p) r y| ≤ δ)
    (hjW : u₁ / 2 * W ≤ ⌊(W : ℝ) * u₁⌋₊) {ω : GrowthPath W}
    (hJ : ω ∉ nsxJump b E q u₁ u₂ W) {s : ℕ}
    (hσ : traceStop b E (noTags W) (fun _ : Fin 1 => q) K (u₁ / 2) W ω = s)
    (hs1 : ⌊(W : ℝ) * u₁⌋₊ < s) (hs2 : s ≤ ⌊(W : ℝ) * u₂⌋₊) :
    ENNReal.ofReal (-G.eval (rhfClockVal b E q a N W s ω)) ≤
      ENNReal.ofReal (δ * (rhfB p r ε K * K + 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by omega⟩
  have hal : ω ∈ alive b E (noTags W) (fun _ : Fin 1 => q) K (u₁ / 2) W m := by
    show (m : ℕ∞) < traceStop b E (noTags W) (fun _ : Fin 1 => q) K (u₁ / 2) W ω
    rw [hσ]; exact_mod_cast Nat.lt_succ_self m
  have hm1 : ⌊(W : ℝ) * u₁⌋₊ ≤ m := by omega
  have hmW : u₁ / 2 * W ≤ m := hjW.trans (by exact_mod_cast hm1)
  have hAm := nsx_trA_le_of_alive hq hal hmW
  have hstep := nsx_trA_step_le b E q u₁ u₂ hJ hm1 (by omega)
  have hAs : (nearClock b E W (m + 1) q ω).trace.re ≤ K + 1 := by linarith
  obtain ⟨-, hΨR, -⟩ := rhx_ranges hp0 hp1 hε hq h0 hδ0 hδ1 hδK ω hAs
  have hG := (abs_le.1 (hG0 _ hΨR)).1
  have hh := rhx_H_nonneg (r := r) hε hΨR
  have hB := rhf_B_nonneg (p := p) (r := r) (K := K) hε
  have : 0 ≤ δ * (rhfB p r ε K * K) := mul_nonneg hδ0 (mul_nonneg hB hK)
  refine ENNReal.ofReal_le_ofReal ?_
  nlinarith

/-- The exit value on the jump event: `|G(Tr π(A_s))| ≤ C_{π,G}(1 + (sup Tr Q)^{(N+1)(d+1)})`. -/
theorem rhx_ofReal_abs_eval_le (hq : ∀ x, 0 ≤ q x) {s : ℕ}
    (hw1 : u₁ / 2 * W ≤ s) (hw2 : (s : ℝ) ≤ (u₂ + 1) * W) (ω : GrowthPath W) :
    ENNReal.ofReal |G.eval (rhfClockVal b E q a N W s ω)| ≤
      ENNReal.ofReal (rhxCG a N G) *
        (1 + nsxSupQ b E q (u₁ / 2) (u₂ + 1) W ω ^ (rhxExp N G.natDegree + 1)) := by
  have hSa : 0 ≤ ∑ r ∈ range N, |a r| := Finset.sum_nonneg fun r _ => abs_nonneg _
  have hT0 := trace_intervalSource_re_nonneg b E W s q hq ω
  have hy : |rhfClockVal b E q a N W s ω| ≤
      (∑ r ∈ range N, |a r|) * (1 + (intervalSource b E W s q ω).trace.re ^ (N + 1)) :=
    nsx_abs_clock_le hq a N s ω
  have h' := rhf_abs_eval_le G N hSa hT0 hy
  rw [rhx_exp_succ] at h'
  have h : |G.eval (rhfClockVal b E q a N W s ω)| ≤ rhxCG a N G *
      (1 + (intervalSource b E W s q ω).trace.re ^ (rhxExp N G.natDegree + 1)) := h'
  refine (ENNReal.ofReal_le_ofReal h).trans ?_
  rw [ENNReal.ofReal_mul (rhx_CG_nonneg a N G), ENNReal.ofReal_add zero_le_one (by positivity),
    ENNReal.ofReal_one, ENNReal.ofReal_pow hT0]
  gcongr
  exact nsx_trQ_le_supQ b E hq hw1 hw2 ω

/-- **The pointwise value comparison** at the stop. -/
theorem rhx_value_pointwise (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 < ε) (hr0 : 0 ≤ r) {k : ℕ}
    (hrk : r ≤ k + 1) (hq : ∀ x, 0 ≤ q x) (hK : 0 ≤ K) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hδK : δ * (K + 1) ≤ ε ^ p / 2)
    (h0 : ∀ x ∈ Icc 0 (K + 1), |nsfPolyFun a N x - nsfRegFun p ε x| ≤ δ * x)
    (hG0 : ∀ y ∈ rhfRange p ε K, |G.eval y - rhfH (ε ^ p) r y| ≤ δ)
    (hjW : u₁ / 2 * W ≤ ⌊(W : ℝ) * u₁⌋₊) (h12 : ⌊(W : ℝ) * u₁⌋₊ ≤ ⌊(W : ℝ) * u₂⌋₊)
    (hj₂T : (⌊(W : ℝ) * u₂⌋₊ : ℝ) ≤ (u₂ + 1) * W) (ω : GrowthPath W) :
    ENNReal.ofReal ((nsClockSum (nsRegKernel p ε) (nearClock b E W ⌊(W : ℝ) * u₂⌋₊ q ω) +
          ε ^ p) ^ r) +
        (nsfAlive b E q K u₁ W ⌊(W : ℝ) * u₁⌋₊).indicator (fun ω => ENNReal.ofReal
          (-rhfStoppedValue b E q K u₁ a N G W ⌊(W : ℝ) * u₂⌋₊ ω)) ω ≤
      (nsfAlive b E q K u₁ W ⌊(W : ℝ) * u₁⌋₊).indicator (fun ω => ENNReal.ofReal
          (rhfStoppedValue b E q K u₁ a N G W ⌊(W : ℝ) * u₂⌋₊ ω)) ω +
        (ENNReal.ofReal (δ * (rhfB p r ε K * K + 1)) + ENNReal.ofReal (rhxCEnd p r ε k) *
            ((nsfAlive b E q K u₁ W ⌊(W : ℝ) * u₂⌋₊)ᶜ.indicator 1 ω +
              (nsfAlive b E q K u₁ W ⌊(W : ℝ) * u₂⌋₊)ᶜ.indicator
                (fun ω => nsxSupQ b E q (u₁ / 2) (u₂ + 1) W ω ^ (k + 1)) ω) +
          ENNReal.ofReal (rhxCG a N G) *
            ((nsxJump b E q u₁ u₂ W).indicator 1 ω + (nsxJump b E q u₁ u₂ W).indicator
              (fun ω => nsxSupQ b E q (u₁ / 2) (u₂ + 1) W ω ^ (rhxExp N G.natDegree + 1)) ω)) := by
  set j₁ := ⌊(W : ℝ) * u₁⌋₊ with hj₁
  set j₂ := ⌊(W : ℝ) * u₂⌋₊ with hj₂
  set S := nsxSupQ b E q (u₁ / 2) (u₂ + 1) W with hS
  set J := nsxJump b E q u₁ u₂ W with hJdef
  set Cπ := rhxCG a N G with hCπ
  set σ := traceStop b E (noTags W) (fun _ : Fin 1 => q) K (u₁ / 2) W ω with hσ
  set M := rhxExp N G.natDegree + 1 with hM
  have hΦ : rhfStoppedValue b E q K u₁ a N G W j₂ ω =
      G.eval (rhfClockVal b E q a N W (nssStopIdx j₂ σ) ω) := rhx_stoppedValue_eq b E hq K u₁ a N G W j₂ ω
  have hw₂ := nsx_window hjW hj₂T h12 le_rfl
  have hc0 := rhx_CEnd_nonneg (r := r) hp0 hε k
  obtain ⟨hH0, hHle⟩ := nsx_regTrace_le (b := b) (E := E) hp0 hp1 hε hq j₂ ω
  have hA0 := (trace_nearClock_le b E W j₂ q hq ω).1
  by_cases h2 : ω ∈ nsfAlive b E q K u₁ W j₂
  · have h2' : (j₂ : ℕ∞) < σ := h2
    have h1 : ω ∈ nsfAlive b E q K u₁ W j₁ :=
      show (j₁ : ℕ∞) < σ from lt_of_le_of_lt (by exact_mod_cast h12) h2'
    rw [Set.indicator_of_mem h1, Set.indicator_of_mem h1, hΦ, nsx_stopIdx_of_alive h2']
    have hA := nsx_trA_le_of_alive hq h2 hw₂.1
    obtain ⟨hdK, hΨR, hHR⟩ := rhx_ranges hp0 hp1 hε hq h0 hδ0 hδ1 hδK (j := j₂) ω
      (by linarith)
    have hGv := (abs_le.1 (hG0 _ hΨR)).1
    have hLip := (abs_le.1 (rhf_abs_H_sub_le (r := r) hε hΨR hHR)).1
    have hB := rhf_B_nonneg (p := p) (r := r) (K := K) hε
    have e1 : rhfB p r ε K * |rhfClockVal b E q a N W j₂ ω -
        nsClockSum (nsRegKernel p ε) (nearClock b E W j₂ q ω)| ≤ rhfB p r ε K * (δ * K) :=
      mul_le_mul_of_nonneg_left (hdK.trans (mul_le_mul_of_nonneg_left hA hδ0)) hB
    have hh0 : 0 ≤ rhfH (ε ^ p) r (nsClockSum (nsRegKernel p ε) (nearClock b E W j₂ q ω)) :=
      rhx_H_nonneg hε hHR
    unfold rhfH at hGv hLip hh0
    have key := nsx_ofReal_add_neg_le (w := δ * (rhfB p r ε K * K + 1))
      (y := G.eval (rhfClockVal b E q a N W j₂ ω)) hh0 (by nlinarith)
    refine key.trans ?_
    gcongr
    exact le_add_right (le_add_right le_rfl)
  · rw [Set.indicator_of_mem (show ω ∈ (nsfAlive b E q K u₁ W j₂)ᶜ from h2),
      Set.indicator_of_mem (show ω ∈ (nsfAlive b E q K u₁ W j₂)ᶜ from h2), Pi.one_apply]
    have hTf : ENNReal.ofReal ((nsClockSum (nsRegKernel p ε) (nearClock b E W j₂ q ω) + ε ^ p) ^ r)
        ≤ ENNReal.ofReal (rhxCEnd p r ε k) * (1 + S ω ^ (k + 1)) := by
      have h := rhx_shift_rpow_le hp0 hε hH0 hHle hA0 hr0 (m := k + 1) (by push_cast; linarith)
      refine (ENNReal.ofReal_le_ofReal h).trans ?_
      rw [show rhxL p ε ^ r * 2 ^ (k + 1) = rhxCEnd p r ε k from rfl,
        ENNReal.ofReal_mul hc0, ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one,
        ENNReal.ofReal_pow hA0]
      gcongr
      exact nsx_trA_le_supQ b E hq hw₂.1 hw₂.2 ω
    have hX : (nsfAlive b E q K u₁ W j₁).indicator (fun ω => ENNReal.ofReal
          (-rhfStoppedValue b E q K u₁ a N G W j₂ ω)) ω ≤
        ENNReal.ofReal (δ * (rhfB p r ε K * K + 1)) + ENNReal.ofReal Cπ *
          (J.indicator 1 ω + J.indicator (fun ω => S ω ^ M) ω) := by
      by_cases h1 : ω ∈ nsfAlive b E q K u₁ W j₁
      · obtain ⟨s, hs, hs1, hs2, hidx⟩ := nsx_exit_index (show (j₁ : ℕ∞) < σ from h1) h2
        rw [Set.indicator_of_mem h1, hΦ, hidx]
        by_cases hJ : ω ∈ J
        · rw [Set.indicator_of_mem hJ, Set.indicator_of_mem hJ, Pi.one_apply]
          have hw := nsx_window hjW hj₂T hs1.le hs2
          refine le_add_left ((ENNReal.ofReal_le_ofReal (neg_le_abs _)).trans ?_)
          exact rhx_ofReal_abs_eval_le hq hw.1 hw.2 ω
        · exact le_add_right (rhx_exit_neg_le hp0 hp1 hε hq hK hδ0 hδ1 hδK h0 hG0 hjW hJ hs hs1 hs2)
      · rw [Set.indicator_of_notMem h1]; exact zero_le
    calc _ ≤ ENNReal.ofReal (rhxCEnd p r ε k) * (1 + S ω ^ (k + 1)) +
          (ENNReal.ofReal (δ * (rhfB p r ε K * K + 1)) +
            ENNReal.ofReal Cπ * (J.indicator 1 ω + J.indicator (fun ω => S ω ^ M) ω)) :=
          add_le_add hTf hX
      _ = ENNReal.ofReal (δ * (rhfB p r ε K * K + 1)) +
          ENNReal.ofReal (rhxCEnd p r ε k) * (1 + S ω ^ (k + 1)) +
          ENNReal.ofReal Cπ * (J.indicator 1 ω + J.indicator (fun ω => S ω ^ M) ω) := by
          ring
      _ ≤ _ := le_add_self

/-- **The integrated value comparison** at a fixed width:
`E(H_ε(A_{j₂})+ε^p)^r + E[1{σ>j₁}(G(Φ_π))⁻] ≤ E[1{σ>j₁}(G(Φ_π))⁺] + δ(BK+1)
  + c_end(P(σ≤j₂) + E[1{σ≤j₂}(sup Tr Q)^{k+1}]) + C_{π,G}(P(J) + E[1_J (sup Tr Q)^{(N+1)(d+1)}])`. -/
theorem rhx_value_le (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 < ε) (hr0 : 0 ≤ r) {k : ℕ}
    (hrk : r ≤ k + 1) (hq : ∀ x, 0 ≤ q x) (hK : 0 ≤ K) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hδK : δ * (K + 1) ≤ ε ^ p / 2)
    (h0 : ∀ x ∈ Icc 0 (K + 1), |nsfPolyFun a N x - nsfRegFun p ε x| ≤ δ * x)
    (hG0 : ∀ y ∈ rhfRange p ε K, |G.eval y - rhfH (ε ^ p) r y| ≤ δ)
    (hjW : u₁ / 2 * W ≤ ⌊(W : ℝ) * u₁⌋₊) (h12 : ⌊(W : ℝ) * u₁⌋₊ ≤ ⌊(W : ℝ) * u₂⌋₊)
    (hj₂T : (⌊(W : ℝ) * u₂⌋₊ : ℝ) ≤ (u₂ + 1) * W) :
    ∫⁻ ω, ENNReal.ofReal ((nsClockSum (nsRegKernel p ε)
          (nearClock b E W ⌊(W : ℝ) * u₂⌋₊ q ω) + ε ^ p) ^ r) ∂growthPathLaw W b +
        ∫⁻ ω, (nsfAlive b E q K u₁ W ⌊(W : ℝ) * u₁⌋₊).indicator (fun ω => ENNReal.ofReal
          (-rhfStoppedValue b E q K u₁ a N G W ⌊(W : ℝ) * u₂⌋₊ ω)) ω ∂growthPathLaw W b ≤
      ∫⁻ ω, (nsfAlive b E q K u₁ W ⌊(W : ℝ) * u₁⌋₊).indicator (fun ω => ENNReal.ofReal
          (rhfStoppedValue b E q K u₁ a N G W ⌊(W : ℝ) * u₂⌋₊ ω)) ω ∂growthPathLaw W b +
        (ENNReal.ofReal (δ * (rhfB p r ε K * K + 1)) + ENNReal.ofReal (rhxCEnd p r ε k) *
            (growthPathLaw W b (nsfAlive b E q K u₁ W ⌊(W : ℝ) * u₂⌋₊)ᶜ +
              ∫⁻ ω, (nsfAlive b E q K u₁ W ⌊(W : ℝ) * u₂⌋₊)ᶜ.indicator
                (fun ω => nsxSupQ b E q (u₁ / 2) (u₂ + 1) W ω ^ (k + 1)) ω ∂growthPathLaw W b) +
          ENNReal.ofReal (rhxCG a N G) *
            (growthPathLaw W b (nsxJump b E q u₁ u₂ W) +
              ∫⁻ ω, (nsxJump b E q u₁ u₂ W).indicator
                (fun ω => nsxSupQ b E q (u₁ / 2) (u₂ + 1) W ω ^ (rhxExp N G.natDegree + 1)) ω
                ∂growthPathLaw W b)) := by
  have hP := passDeriv_isProbabilityMeasure_growthPathLaw W b
  have hSm := nsx_measurable_supQ b E q (u₁ / 2) (u₂ + 1) W
  have hJm := nsx_measurableSet_jump b E q u₁ u₂ W
  have hDm := (nss_measurableSet_alive b E (noTags W) q K (u₁ / 2) W ⌊(W : ℝ) * u₂⌋₊).compl
  set D := (nsfAlive b E q K u₁ W ⌊(W : ℝ) * u₂⌋₊)ᶜ with hDdef
  set J := nsxJump b E q u₁ u₂ W with hJdef
  have hd1 : Measurable (D.indicator (1 : GrowthPath W → ℝ≥0∞)) := measurable_one.indicator hDm
  have hf : Measurable (D.indicator
      (fun ω => nsxSupQ b E q (u₁ / 2) (u₂ + 1) W ω ^ (k + 1))) := (hSm.pow_const _).indicator hDm
  have hg : Measurable (J.indicator (1 : GrowthPath W → ℝ≥0∞)) := measurable_one.indicator hJm
  have hh : Measurable (J.indicator
      (fun ω => nsxSupQ b E q (u₁ / 2) (u₂ + 1) W ω ^ (rhxExp N G.natDegree + 1))) :=
    (hSm.pow_const _).indicator hJm
  refine (le_lintegral_add _ _).trans ?_
  refine (lintegral_mono fun ω => rhx_value_pointwise hp0 hp1 hε hr0 hrk hq hK hδ0 hδ1 hδK h0 hG0
    hjW h12 hj₂T ω).trans (le_of_eq ?_)
  set c₁ := ENNReal.ofReal (δ * (rhfB p r ε K * K + 1))
  set c₂ := ENNReal.ofReal (rhxCEnd p r ε k)
  set c₃ := ENNReal.ofReal (rhxCG a N G)
  set d1 := D.indicator (1 : GrowthPath W → ℝ≥0∞)
  set f := D.indicator (fun ω => nsxSupQ b E q (u₁ / 2) (u₂ + 1) W ω ^ (k + 1))
  set g := J.indicator (1 : GrowthPath W → ℝ≥0∞)
  set h := J.indicator (fun ω => nsxSupQ b E q (u₁ / 2) (u₂ + 1) W ω ^ (rhxExp N G.natDegree + 1))
  have hdf : Measurable (fun ω => d1 ω + f ω) := hd1.add hf
  have hgh : Measurable (fun ω => g ω + h ω) := hg.add hh
  have h12m : Measurable (fun ω => c₁ + c₂ * (d1 ω + f ω)) := measurable_const.add (hdf.const_mul _)
  have hrest : Measurable (fun ω => c₁ + c₂ * (d1 ω + f ω) + c₃ * (g ω + h ω)) :=
    h12m.add (hgh.const_mul _)
  rw [lintegral_add_right _ hrest]
  congr 1
  rw [lintegral_add_left h12m, lintegral_add_left measurable_const, lintegral_const,
    measure_univ, mul_one, lintegral_const_mul _ hdf, lintegral_const_mul _ hgh,
    lintegral_add_left hd1, lintegral_indicator_one hDm, lintegral_add_left hg,
    lintegral_indicator_one hJm]

end Value

end BlockBand.Endpoints
