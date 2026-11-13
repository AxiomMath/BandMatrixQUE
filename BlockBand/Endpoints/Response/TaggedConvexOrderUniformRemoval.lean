module

public import BlockBand.Endpoints.Response.TaggedConvexOrderUniformBase
public import BlockBand.Endpoints.Response.TaggedConvexOrderStoppedRemoval

/-!
# Energy-uniform tagged convex order: stop removal and the moving transport constant

Step 3 of the proof of the tagged convex-order theorem: the estimate is first used before a
trace stop, and the stop is then removed by the full-source stops lemma. Energy-uniform reading:
the moving transport constant `D₀(e_j) → D₀(E)` costs `o(1)`.

**Law, domain, uniformity.** As in `TaggedConvexOrderUniformBase`: fixed `0 < b < 1/2`, base bulk
`E`, `s > 0`, a tagged sequence with moving energies `e_j → E`, eventually in `bulkInterval κ`.
Path law `growthPathLaw W b`, probe `circularVectorLaw`.

**The two remainders.** The witness `tcw_deficit` and the stopped remainder `tcw_rem` use the
transport constant at the path energy, `D₀(e_j)`; the one-step error `tcs_monoErr` inside
`TcwRemainderAlong` uses the base `D₀(E)` (the limit object). Hence:
* `TcuOwnRemainderAlong`: the remainder clause with `tcs_monoErr` at `D₀(e_j)` (an auxiliary
  definition; it is proved, not assumed).
* `tcu_ownRemainderAlong`: `TcuOwnRemainderAlong` from `FullSourceMomentsEnergyUniformContract`,
  `FullSourceStopsEnergyUniformContract` (`supMoments`, `tail`, both at the margin `κ`; the `tail`
  supremum over `E ∈ bulkInterval κ` is evaluated at `e_j`), `ConditionalBlockGUECount` and the
  stopped input `TcwStoppedRemainderAlong` (moving-energy version of
  `tcwRemainderCoreFixed_of_stopped'`; the prefactor `D₀(e_j)` is bounded by `D₀(E) + 1`
  eventually).
* `tcu_remainderAlong_of_own`: `TcwRemainderAlong` from `TcuOwnRemainderAlong` and the moments:
  `tcs_monoErr(D₀(E)) - tcs_monoErr(D₀(e)) = W⁻¹(λ_m(e) - λ_m(E)) E Z_l^m` summed over at most
  `(τ+1)W` steps is at most `(τ+1)|D₀(e_j) - D₀(E)| |m(m-1)|/2 (1 + C_m) → 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Filter Topology Polynomial Finset Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Inputs BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionUniform BlockBand.Internal.Contracts.TransmissionUniform2
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ENNReal NNReal

/-- **The remainder clause at the path's own transport constant** (auxiliary): as
`TcwRemainderAlong`, with `tcs_monoErr` at `D₀(e_j)` instead of the base `D₀(E)`. -/
def TcuOwnRemainderAlong (b : ℝ) {s τ E : ℝ} (σ : TcoTagSequence s τ E) : Prop :=
  ∀ (M : ℕ) (δ : ℝ), 0 < δ → ∀ᶠ j in atTop, ∀ m ≤ M, ∀ l', σ.k j + 1 ≤ l' → l' ≤ σ.n j →
    |∑ l ∈ Ico (σ.k j + 1) l',
      (tcs_monoErr b (σ.energy j) (transportD0 b (σ.energy j)) (σ.W j) l (σ.k j) m -
        tcw_deficit b (σ.energy j) (σ.W j) l (σ.k j) m)| ≤ δ

/-- `D₀(e_j) → D₀(E)` along a tagged sequence (`D₀(e) = 2/(b(4 - e²))` is continuous on the open
bulk). -/
theorem tcu_transportD0_tendsto {b : ℝ} (hb : 0 < b) {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2)
    {s τ : ℝ} (σ : TcoTagSequence s τ E) :
    Tendsto (fun j => transportD0 b (σ.energy j)) atTop (𝓝 (transportD0 b E)) := by
  have hne : b * (4 - E ^ 2) ≠ 0 := by
    have : 0 < 4 - E ^ 2 := by nlinarith
    positivity
  have hc : ContinuousAt (fun e : ℝ => 2 / (b * (4 - e ^ 2))) E :=
    ContinuousAt.div continuousAt_const (by fun_prop) hne
  exact hc.tendsto.comp σ.energy_tendsto

/-- The one-step error is affine in the transport constant:
`ε_l(m; D₀) - ε_l(m; D₀') = W⁻¹(λ_m(D₀') - λ_m(D₀)) E Z_l^m`. -/
theorem tcu_monoErr_sub (b e D0 D0' : ℝ) (W l k m : ℕ) :
    tcs_monoErr b e D0 W l k m - tcs_monoErr b e D0' W l k m =
      (W : ℝ)⁻¹ * ((tcc_lam D0' m - tcc_lam D0 m) * ∫ x, x ^ m ∂tcc_law b e W l k) := by
  unfold tcs_monoErr
  ring

/-- **Stop removal along moving energies**: `TcuOwnRemainderAlong` from
`FullSourceMomentsEnergyUniformContract`, `FullSourceStopsEnergyUniformContract` (`supMoments`,
`tail`), `ConditionalBlockGUECount` and the stopped input `TcwStoppedRemainderAlong`. -/
theorem tcu_ownRemainderAlong (hMom : FullSourceMomentsEnergyUniformContract)
    (hStops : FullSourceStopsEnergyUniformContract) (hCount : ConditionalBlockGUECount)
    {b : ℝ} (hb : 0 < b) (hb' : b < 1 / 2) {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) {s τ : ℝ}
    (hs : 0 < s) (σ : TcoTagSequence s τ E) (hSt : TcwStoppedRemainderAlong b σ) :
    TcuOwnRemainderAlong b σ := by
  intro M δ hδ
  obtain ⟨κb, hκb, hbulk⟩ := tcu_eventually_bulk σ hE1 hE2
  have hsτ := tco_tagSequence_s_le σ
  have hε : 0 < s / 2 := by linarith
  have hεT : s / 2 < τ + 1 := by linarith
  have hq : IsIntervalTests tcw_noInterval := fun a => a.elim0
  suffices H : ∀ m ∈ range (M + 1), ∀ᶠ j in atTop, ∀ l', σ.k j + 1 ≤ l' → l' ≤ σ.n j →
      |∑ l ∈ Ico (σ.k j + 1) l',
        (tcs_monoErr b (σ.energy j) (transportD0 b (σ.energy j)) (σ.W j) l (σ.k j) m -
          tcw_deficit b (σ.energy j) (σ.W j) l (σ.k j) m)| ≤ δ by
    filter_upwards [(eventually_all_finset _).2 H] with j hj m hm l' h1 h2
    exact hj m (by simp; omega) l' h1 h2
  intro m hmM
  have hmM' : m ≤ M := by simp at hmM; omega
  obtain ⟨c, hc0, hc⟩ := tcw_F_bound m
  have hD0 := transportD0_pos hb hE1 hE2
  set κ : ℝ := (transportD0 b E + 1) / 2 * |(m : ℝ) * ((m : ℝ) - 1)|
  have hκ : 0 ≤ κ := by positivity
  set K₁ : ℝ := 4 + (τ + 1) * κ
  have hK₁ : 0 < K₁ := by
    have : 0 ≤ (τ + 1) * κ := mul_nonneg (by linarith) hκ
    linarith
  obtain ⟨Cs, W₀s, hCs⟩ := hStops.supMoments b hb hb' κb hκb 1 0 tcw_noInterval hq (s / 2)
    (τ + 1) ((2 * m + 1 : ℕ) : ℝ) hε hεT (by positivity)
  obtain ⟨Ct, hCt⟩ := hStops.tail b hb hb' κb hκb 1 0 tcw_noInterval hq (s / 2) (τ + 1) hε hεT
  set Is : ℝ := 1 + max Cs 0
  have hIs : 0 < Is := by have := le_max_right Cs 0; simp only [Is]; linarith
  set L : ℝ := 4 * K₁ * (c ^ 2 * Is) / δ + 1
  have hL : 0 < L := by positivity
  set Kc : ℝ := 4 * K₁ * L * (|Ct| + 1) / δ + 1
  have hKc : 0 < Kc := by positivity
  set β : ℝ := (|Ct| + 1) / Kc
  have hβ : 0 ≤ β := by positivity
  have htail : ∀ᶠ W : ℕ in atTop, (⨆ (E' : ℝ) (_ : E' ∈ bulkInterval κb) (k' : Fin 1 → ℕ),
      growthPathLaw W b {ω | ∃ j : ℕ, s / 2 * W ≤ j ∧ (j : ℝ) ≤ (τ + 1) * W ∧
        Kc < traceLoad b E' k' tcw_noInterval W j ω}) < ENNReal.ofReal β := by
    refine eventually_lt_of_limsup_lt ((hCt Kc hKc).trans_lt ?_)
    rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    exact div_lt_div_of_pos_right ((le_abs_self Ct).trans_lt (lt_add_one _)) hKc
  choose Cf hCf using tcu_momentsAlong hMom hb hb' hE1 hE2 σ
  have hmomE : ∀ᶠ j in atTop, ∀ p ∈ range (m + 3), ∀ l, σ.k j < l → l ≤ σ.n j →
      ∫⁻ x, ENNReal.ofReal (x ^ (2 * p)) ∂tcc_law b (σ.energy j) (σ.W j) l (σ.k j) ≤
        ENNReal.ofReal (Cf p) :=
    (eventually_all_finset _).2 fun p _ => hCf p
  have htag : ∀ᶠ j in atTop, s / 2 * (σ.W j : ℝ) ≤ σ.k j := by
    filter_upwards [σ.tag_tendsto.eventually (lt_mem_nhds (show s / 2 < s by linarith))] with j hj
    have hW : (0 : ℝ) < σ.W j := by exact_mod_cast σ.W_pos j
    rw [lt_div_iff₀ hW] at hj
    exact hj.le
  have hD0near : ∀ᶠ j in atTop, transportD0 b (σ.energy j) ≤ transportD0 b E + 1 :=
    (tcu_transportD0_tendsto hb hE1 hE2 σ).eventually
      (ge_mem_nhds (show transportD0 b E < transportD0 b E + 1 by linarith))
  filter_upwards [hSt M (δ / 2) Kc (half_pos hδ) hKc, hmomE,
    tcc_eventually_len σ W₀s, htag, σ.width_tendsto.eventually htail, hbulk, hD0near]
    with j hStj hmj hlen hkj htj he hDj
  intro l' h1 h2
  obtain ⟨he1, he2⟩ := tcu_bulk_bounds hκb he
  set e := σ.energy j with he_def
  have hWpos := σ.W_pos j
  have hint : ∀ l, σ.k j + 1 ≤ l → l ≤ σ.n j → ∀ p ≤ m + 2, Integrable
      (fun x => lmf_tagResponseClock b e (σ.W j) l (σ.k j) x ^ p) (probedClockLaw (σ.W j) b) :=
    fun l hl1 hl2 p hp => tcw_integrable_tagClock_pow (hmj p (by simp; omega) l (by omega) hl2)
  -- the remainder as a path expectation, split at the stop
  have hsplit : ∀ l ∈ Ico (σ.k j + 1) l',
      tcs_monoErr b e (transportD0 b e) (σ.W j) l (σ.k j) m -
          tcw_deficit b e (σ.W j) l (σ.k j) m =
        ∫ ω, (tcw_alive b e (σ.W j) (σ.k j) Kc (s / 2) l).indicator
            (tcw_rem b e (σ.W j) l (σ.k j) m) ω ∂growthPathLaw (σ.W j) b +
          ∫ ω, (tcw_alive b e (σ.W j) (σ.k j) Kc (s / 2) l)ᶜ.indicator
            (tcw_rem b e (σ.W j) l (σ.k j) m) ω ∂growthPathLaw (σ.W j) b := by
    intro l hl
    obtain ⟨hl1, hl2⟩ := mem_Ico.1 hl
    rw [tcw_remainder_eq hCount hb' he1 he2 hWpos l (σ.k j) m
      (hint (l + 1) (by omega) (by omega) m (by omega)) (hint l (by omega) (by omega) m (by omega))
      (hint l (by omega) (by omega) (m - 2 + 2) (by omega))]
    have hr : Integrable (tcw_rem b e (σ.W j) l (σ.k j) m) (growthPathLaw (σ.W j) b) :=
      ((tcw_integrable_F (hint (l + 1) (by omega) (by omega) m (by omega))).sub
        (tcw_integrable_F (hint l (by omega) (by omega) m (by omega)))).sub
        ((tcw_integrable_H hCount hb' he1 he2 hWpos l (σ.k j) m
          (hint l (by omega) (by omega) (m - 2 + 2) (by omega))).const_mul _)
    have hA := tcx_measurableSet_alive b e (σ.W j) (σ.k j) Kc (s / 2) l
    rw [← integral_add (hr.indicator hA) (hr.indicator hA.compl)]
    exact integral_congr_ae (Eventually.of_forall fun ω =>
      (Set.indicator_self_add_compl_apply _ _ ω).symm)
  rw [sum_congr rfl hsplit, sum_add_distrib]
  have hstop := hStj m hmM' l' h1 h2
  have hbad : growthPathLaw (σ.W j) b {ω | ∃ j' : ℕ, s / 2 * (σ.W j : ℝ) ≤ j' ∧
      (j' : ℝ) ≤ (τ + 1) * σ.W j ∧
        Kc < traceLoad b e (tcw_tagFamily (σ.k j)) tcw_noInterval (σ.W j) j' ω} ≤
      ENNReal.ofReal β :=
    (le_iSup₂_of_le (f := fun (E' : ℝ) (_ : E' ∈ bulkInterval κb) => ⨆ k' : Fin 1 → ℕ,
        growthPathLaw (σ.W j) b {ω | ∃ j' : ℕ, s / 2 * (σ.W j : ℝ) ≤ j' ∧
          (j' : ℝ) ≤ (τ + 1) * σ.W j ∧ Kc < traceLoad b E' k' tcw_noInterval (σ.W j) j' ω})
      e he (le_iSup (fun k' : Fin 1 → ℕ => growthPathLaw (σ.W j) b {ω | ∃ j' : ℕ,
        s / 2 * (σ.W j : ℝ) ≤ j' ∧ (j' : ℝ) ≤ (τ + 1) * σ.W j ∧
          Kc < traceLoad b e k' tcw_noInterval (σ.W j) j' ω}) (tcw_tagFamily (σ.k j)))).trans
      htj.le
  have hoff := tcx_offStop_total (K := Kc) (ε := s / 2) (T := τ + 1) hCount hb hb' he1 he2
    hWpos (k := σ.k j) (m := m) h1 (by push_cast; linarith) ((by exact_mod_cast h2 :
      (l' : ℝ) ≤ σ.n j).trans hlen.2) hc0 (fun l ω => hc b e (σ.W j) l (σ.k j) ω)
    (fun l hl1 hl2 => ⟨hint l hl1 (hl2.trans h2) m (by omega),
      hint l hl1 (hl2.trans h2) (m - 2 + 2) (by omega)⟩)
    (hCs (σ.W j) hlen.1 e he (tcw_tagFamily (σ.k j)) (Sum.inl 0)) hβ hbad hL
  -- the prefactor at the moving energy is at most `K₁`
  have hpre : 4 + (τ + 1) * (transportD0 b e / 2 * |(m : ℝ) * ((m : ℝ) - 1)|) ≤ K₁ := by
    have h3 : transportD0 b e / 2 * |(m : ℝ) * ((m : ℝ) - 1)| ≤ κ :=
      mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    have : (τ + 1) * (transportD0 b e / 2 * |(m : ℝ) * ((m : ℝ) - 1)|) ≤ (τ + 1) * κ :=
      mul_le_mul_of_nonneg_left h3 (by linarith)
    simp only [K₁]
    linarith
  have hoff' : |∑ l ∈ Ico (σ.k j + 1) l', ∫ ω, (tcw_alive b e (σ.W j) (σ.k j) Kc (s / 2) l)ᶜ.indicator
      (tcw_rem b e (σ.W j) l (σ.k j) m) ω ∂growthPathLaw (σ.W j) b| ≤
      K₁ * (L * β + c ^ 2 * Is / L) :=
    hoff.trans (mul_le_mul_of_nonneg_right hpre (by positivity))
  -- the two smallness conditions
  have hq1 : K₁ * (c ^ 2 * Is / L) ≤ δ / 4 := by
    rw [show K₁ * (c ^ 2 * Is / L) = K₁ * (c ^ 2 * Is) / L by ring, div_le_iff₀ hL]
    have : δ / 4 * L = K₁ * (c ^ 2 * Is) + δ / 4 := by
      simp only [L]; field_simp; try ring
    have : 0 ≤ K₁ * (c ^ 2 * Is) := by positivity
    nlinarith
  have hq2 : K₁ * (L * β) ≤ δ / 4 := by
    simp only [β]
    rw [show K₁ * (L * ((|Ct| + 1) / Kc)) = K₁ * L * (|Ct| + 1) / Kc by ring, div_le_iff₀ hKc]
    have : δ / 4 * Kc = K₁ * L * (|Ct| + 1) + δ / 4 := by
      simp only [Kc]; field_simp; try ring
    have : 0 ≤ K₁ * L * (|Ct| + 1) := by positivity
    nlinarith
  calc _ ≤ |∑ l ∈ Ico (σ.k j + 1) l', ∫ ω, (tcw_alive b e (σ.W j) (σ.k j) Kc (s / 2) l).indicator
          (tcw_rem b e (σ.W j) l (σ.k j) m) ω ∂growthPathLaw (σ.W j) b| +
        |∑ l ∈ Ico (σ.k j + 1) l', ∫ ω, (tcw_alive b e (σ.W j) (σ.k j) Kc (s / 2) l)ᶜ.indicator
          (tcw_rem b e (σ.W j) l (σ.k j) m) ω ∂growthPathLaw (σ.W j) b| := abs_add_le _ _
    _ ≤ δ / 2 + K₁ * (L * β + c ^ 2 * Is / L) := add_le_add hstop hoff'
    _ ≤ δ := by nlinarith

/-- **The moving transport constant costs `o(1)`**: `TcwRemainderAlong` (one-step error at the
base `D₀(E)`) from `TcuOwnRemainderAlong` (at `D₀(e_j)`) and the moments along `σ`. -/
theorem tcu_remainderAlong_of_own {b : ℝ} (hb : 0 < b) {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2)
    {s τ : ℝ} (σ : TcoTagSequence s τ E) (hM : TccMomentsAlong b σ)
    (hOwn : TcuOwnRemainderAlong b σ) : TcwRemainderAlong b σ := by
  intro M δ hδ
  choose Cf hCf using hM
  suffices H : ∀ m ∈ range (M + 1), ∀ᶠ j in atTop, ∀ l', σ.k j + 1 ≤ l' → l' ≤ σ.n j →
      |∑ l ∈ Ico (σ.k j + 1) l',
        (tcs_monoErr b (σ.energy j) (transportD0 b E) (σ.W j) l (σ.k j) m -
          tcw_deficit b (σ.energy j) (σ.W j) l (σ.k j) m)| ≤ δ by
    filter_upwards [(eventually_all_finset _).2 H] with j hj m hm l' h1 h2
    exact hj m (by simp; omega) l' h1 h2
  intro m hmM
  have hmM' : m ≤ M := by simp at hmM; omega
  set Bm : ℝ := 1 + max (Cf m) 0
  have hBm : 0 ≤ Bm := by have := le_max_right (Cf m) 0; simp only [Bm]; linarith
  set cm : ℝ := |(m : ℝ) * ((m : ℝ) - 1) / 2|
  have hsmall : ∀ᶠ j in atTop,
      (τ + 1) * (|transportD0 b (σ.energy j) - transportD0 b E| * cm * Bm) ≤ δ / 2 := by
    have t0 : Tendsto (fun j => |transportD0 b (σ.energy j) - transportD0 b E|) atTop (𝓝 0) := by
      have := (tendsto_sub_nhds_zero_iff.2 (tcu_transportD0_tendsto hb hE1 hE2 σ)).abs
      rwa [abs_zero] at this
    have t1 := (t0.mul_const (cm * Bm)).const_mul (τ + 1)
    rw [zero_mul, mul_zero] at t1
    filter_upwards [t1.eventually (ge_mem_nhds (half_pos hδ))] with j hj
    simpa only [mul_assoc] using hj
  filter_upwards [hOwn M (δ / 2) (half_pos hδ), hCf m, tcc_eventually_len σ 0, hsmall]
    with j hO hmj hlen hsm
  intro l' h1 h2
  set e := σ.energy j
  set W := σ.W j
  set k := σ.k j
  have hW0 : (0 : ℝ) < W := by exact_mod_cast σ.W_pos j
  set Xb : ℝ := |transportD0 b e - transportD0 b E| * cm * Bm
  have hX : 0 ≤ Xb := by positivity
  have hterm : ∀ l ∈ Ico (k + 1) l',
      |tcs_monoErr b e (transportD0 b E) W l k m - tcs_monoErr b e (transportD0 b e) W l k m| ≤
        (W : ℝ)⁻¹ * Xb := by
    intro l hl
    obtain ⟨hl1, hl2⟩ := mem_Ico.1 hl
    have := tcc_law_prob b e W l k
    have hmo := tcc_abs_moment_le m (hmj l (by omega) (by omega))
    have hlam : tcc_lam (transportD0 b e) m - tcc_lam (transportD0 b E) m =
        (transportD0 b e - transportD0 b E) * ((m : ℝ) * ((m : ℝ) - 1) / 2) := by
      unfold tcc_lam; ring
    rw [tcu_monoErr_sub, hlam, abs_mul, abs_of_nonneg (inv_nonneg.2 hW0.le), abs_mul, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hW0.le)
    simp only [Xb]
    exact mul_le_mul_of_nonneg_left hmo (by positivity)
  have hcard : ((Ico (k + 1) l').card : ℝ) * (W : ℝ)⁻¹ ≤ τ + 1 := by
    rw [Nat.card_Ico, ← div_eq_mul_inv, div_le_iff₀ hW0]
    calc ((l' - (k + 1) : ℕ) : ℝ) ≤ σ.n j := by exact_mod_cast (Nat.sub_le l' (k + 1)).trans h2
      _ ≤ (τ + 1) * W := hlen.2
  have hmis : |∑ l ∈ Ico (k + 1) l',
      (tcs_monoErr b e (transportD0 b E) W l k m - tcs_monoErr b e (transportD0 b e) W l k m)| ≤
        δ / 2 := by
    refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hterm).trans ?_)
    rw [sum_const, nsmul_eq_mul, ← mul_assoc]
    exact (mul_le_mul_of_nonneg_right hcard hX).trans hsm
  have hO' := hO m hmM' l' h1 h2
  have hsum : ∑ l ∈ Ico (k + 1) l',
      (tcs_monoErr b e (transportD0 b E) W l k m - tcw_deficit b e W l k m) =
      ∑ l ∈ Ico (k + 1) l', (tcs_monoErr b e (transportD0 b e) W l k m -
        tcw_deficit b e W l k m) +
      ∑ l ∈ Ico (k + 1) l',
        (tcs_monoErr b e (transportD0 b E) W l k m - tcs_monoErr b e (transportD0 b e) W l k m) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun l _ => by ring
  rw [hsum]
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ δ / 2 + δ / 2 := add_le_add hO' hmis
    _ = δ := by ring

end BlockBand.Endpoints
