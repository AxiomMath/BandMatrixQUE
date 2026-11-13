module

public import BlockBand.Endpoints.Response.TaggedConvexOrderMoments
public import BlockBand.Endpoints.Response.TaggedConvexOrderGBM
public import Mathlib.Topology.MetricSpace.Sequences

/-!
# The averaged clause of the tagged convex order

Law: `probedClockLaw W b` (the near-end-grown path with an independent `h ~ CN(0, I_{2W})`);
`Z_{n;k} = lmf_tagResponseClock`, `M_W = rescaledClock`, `d = d_*`. The hypotheses are
`FullSourceMomentsEnergyUniformContract` and the comparison along tagged sequences `hcomp`.

`tco_flat_of_along`: fixed `0 < b < 1/2`, bulk `E`, `T₀ > 0`, `p ≥ 1`; then one constant
`C = C_{p,T₀}` (the constant `K` of the geometric Brownian bound `E(dG_t - d)^{2p} ≤ Kt^p` on
`[0, T₀]`, depending on `p, T₀, b, E` only); for every `τ ∈ (0, T₀]` and every `ClockSequence τ E`
(`W_j → ∞`, `n_j/W_j → τ`, moving energies `e_j → E`) along which every tagged subsequence (tags
`k_j ≥ εW_j` after extraction, energies taken from the sequence) satisfies the convex comparison
`TcoConvexComparisonAlong`: `limsup_j n⁻¹Σ_{k<n} E|Z_{n;k} - d|^{2p} ≤ Cτ^p` and
`limsup_j E|M_W - d|^{2p} ≤ Cτ^p` (lower integrals in `ℝ≥0∞`).

Proof: for `k ≥ εW` the bound `C(τ - s)^p ≤ Cτ^p` is uniform (a contradicting sequence has, after
extraction, a convergent tag time `s ∈ [ε, τ]`, by Bolzano–Weierstrass); the tags with `k < εW`
are a fraction `≤ (εW+1)/n → ε/τ` of all tags, each with `E|Z - d|^{2p} ≤ C_A` by the full tag
clock moments (`tco_tag_centered_bound`); then `ε ↓ 0`; Jensen gives the `M_W` clause.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Filter Topology Polynomial
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionUniform
open scoped ENNReal NNReal

/-!
## Elementary facts
-/

theorem tco_bulk_margin {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) :
    ∃ κ : ℝ, 0 < κ ∧ bulkInterval κ ∈ 𝓝 E := by
  refine ⟨(2 - |E|) / 2, by linarith [abs_lt.2 ⟨hE1, hE2⟩], ?_⟩
  unfold bulkInterval
  have h := abs_lt.2 ⟨hE1, hE2⟩
  refine Icc_mem_nhds ?_ ?_ <;> cases abs_cases E <;> linarith

theorem tco_transportD0_nonneg {b E : ℝ} (hb : 0 < b) (hE1 : -2 < E) (hE2 : E < 2) :
    0 ≤ transportD0 b E := by
  unfold transportD0
  have : 0 < 4 - E ^ 2 := by nlinarith
  positivity

theorem tco_dStar_nonneg {b : ℝ} (hb' : b < 1 / 2) : 0 ≤ dStar b := by
  unfold dStar
  have : 0 < 1 - b := by linarith
  positivity

theorem tco_convex_centered (d : ℝ) (p : ℕ) :
    ConvexOn ℝ (Set.Ici 0) (fun x => ((X - C d) ^ (2 * p) : ℝ[X]).eval x) := by
  have h := ((Even.convexOn_pow (𝕜 := ℝ) (even_two_mul p)).translate_right (-d)).subset
    (Set.subset_univ _) (convex_Ici (0 : ℝ))
  convert h using 1
  funext x
  simp only [eval_pow, eval_sub, eval_X, eval_C, Function.comp_apply]
  ring

/-- The good event along a clock sequence: large width, energy in the compact bulk interval,
length at most `(T₀ + 1)W`, and a nonempty path. -/
theorem tco_eventually_good {τ E T₀ κ : ℝ} (s : ClockSequence τ E) (hτ : 0 < τ) (hτT : τ ≤ T₀)
    (hκE : bulkInterval κ ∈ 𝓝 E) (W₀ : ℕ) :
    ∀ᶠ j in atTop, W₀ ≤ s.W j ∧ s.energy j ∈ bulkInterval κ ∧
      (s.n j : ℝ) ≤ (T₀ + 1) * s.W j ∧ 0 < s.n j := by
  have h1 := s.width_tendsto.eventually_ge_atTop W₀
  have h2 := s.energy_tendsto hκE
  have h3 := s.ratio_tendsto (Iio_mem_nhds (show τ < T₀ + 1 by linarith))
  have h4 := s.ratio_tendsto (Ioi_mem_nhds (show (0 : ℝ) < τ from hτ))
  filter_upwards [h1, h2, h3, h4] with j hj1 hj2 hj3 hj4
  have hW : (0 : ℝ) < s.W j := by exact_mod_cast s.W_pos j
  refine ⟨hj1, hj2, ?_, ?_⟩
  · have : (s.n j : ℝ) / s.W j < T₀ + 1 := hj3
    rw [div_lt_iff₀ hW] at this
    exact this.le
  · have : (0 : ℝ) < (s.n j : ℝ) / s.W j := hj4
    have : (0 : ℝ) < s.n j := by
      by_contra hc
      have : (s.n j : ℝ) = 0 := le_antisymm (not_lt.1 hc) (Nat.cast_nonneg _)
      simp_all
    exact_mod_cast this

/-- The tagged average of the centered moments. -/
abbrev tco_tagMoment (b : ℝ) {τ E : ℝ} (s : ClockSequence τ E) (p j k : ℕ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal
      (|lmf_tagResponseClock b (s.energy j) (s.W j) (s.n j) k x - dStar b| ^ (2 * p))
    ∂probedClockLaw (s.W j) b

/-- The hypothesis of the reduction: the convex comparison along every tagged sequence whose
energies are taken from those of `s`. -/
def TcoComparisonFrom (b : ℝ) {τ E : ℝ} (s : ClockSequence τ E) : Prop :=
  ∀ (s₀ : ℝ) (σ : TcoTagSequence s₀ τ E), 0 < s₀ → (∀ i, σ.energy i ∈ Set.range s.energy) →
    TcoConvexComparisonAlong b σ

/-!
## The tags with `k ≥ εW`
-/

/-- Uniform bound for the tags `k ≥ εW`. -/
theorem tco_large_tags (hMom : FullSourceMomentsEnergyUniformContract) {b : ℝ} (hb : 0 < b)
    (hb' : b < 1 / 2) {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) {T₀ τ : ℝ} (hτ : 0 < τ)
    (hτT : τ ≤ T₀) {p : ℕ} (hp : 0 < p) (s : ClockSequence τ E) (hcomp : TcoComparisonFrom b s)
    {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ t : ℝ, 0 ≤ t → t ≤ T₀ →
      tco_gbmExpect (transportD0 b E) (dStar b) t ((X - C (dStar b)) ^ (2 * p)) ≤ K * t ^ p)
    {ε : ℝ} (hε : 0 < ε) :
    limsup (fun j => ((Finset.range (s.n j)).filter (fun k : ℕ => ε * s.W j ≤ k)).sup
      (tco_tagMoment b s p j)) atTop ≤ ENNReal.ofReal (K * τ ^ p) := by
  obtain ⟨κ, hκ, hκE⟩ := tco_bulk_margin hE1 hE2
  obtain ⟨CA, W₀, hCA0, hCA⟩ := tco_tag_centered_bound hMom hb hb' hκ (T₀ + 1) hp
  have hev := tco_eventually_good s hτ hτT hκE W₀
  set L : ℕ → ℝ≥0∞ := fun j => ((Finset.range (s.n j)).filter (fun k : ℕ => ε * s.W j ≤ k)).sup
    (tco_tagMoment b s p j)
  by_contra hlt'
  have hlt := lt_of_not_ge hlt'
  obtain ⟨c', hc1, hc2⟩ := exists_between hlt
  have hfreq := (frequently_lt_of_lt_limsup (by isBoundedDefault) hc2).and_eventually hev
  obtain ⟨ψ, hψ, hψP⟩ := Filter.extraction_of_frequently_atTop hfreq
  have hk : ∀ i, ∃ k ∈ (Finset.range (s.n (ψ i))).filter (fun k : ℕ => ε * s.W (ψ i) ≤ k),
      c' < tco_tagMoment b s p (ψ i) k := fun i => Finset.lt_sup_iff.1 (hψP i).1
  choose kk hkk hkc using hk
  have hkk' : ∀ i, kk i < s.n (ψ i) ∧ ε * s.W (ψ i) ≤ kk i := fun i => by
    have := hkk i
    rw [Finset.mem_filter, Finset.mem_range] at this
    exact this
  set x : ℕ → ℝ := fun i => (kk i : ℝ) / s.W (ψ i)
  obtain ⟨M, hM⟩ := s.ratio_tendsto.bddAbove_range
  have hWpos : ∀ j, (0 : ℝ) < s.W j := fun j => by exact_mod_cast s.W_pos j
  have hxle : ∀ i, x i ≤ (s.n (ψ i) : ℝ) / s.W (ψ i) := fun i =>
    div_le_div_of_nonneg_right (by exact_mod_cast (hkk' i).1.le) (hWpos _).le
  have hxge : ∀ i, ε ≤ x i := fun i => by
    rw [le_div_iff₀ (hWpos _)]; exact (hkk' i).2
  have hxmem : ∀ i, x i ∈ Set.Icc (0 : ℝ) M := fun i =>
    ⟨hε.le.trans (hxge i), (hxle i).trans (hM ⟨ψ i, rfl⟩)⟩
  obtain ⟨s₀, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded (Metric.isBounded_Icc 0 M) hxmem
  have hψφ : StrictMono (ψ ∘ φ) := hψ.comp hφ
  have hs₀ε : ε ≤ s₀ := ge_of_tendsto hlim (Eventually.of_forall fun i => hxge (φ i))
  have hs₀τ : s₀ ≤ τ := le_of_tendsto_of_tendsto hlim
    (s.ratio_tendsto.comp hψφ.tendsto_atTop) (Eventually.of_forall fun i => hxle (φ i))
  let σ : TcoTagSequence s₀ τ E :=
    { W := fun i => s.W (ψ (φ i))
      n := fun i => s.n (ψ (φ i))
      k := fun i => kk (φ i)
      energy := fun i => s.energy (ψ (φ i))
      W_pos := fun i => s.W_pos _
      width_tendsto := s.width_tendsto.comp hψφ.tendsto_atTop
      tag_lt := fun i => (hkk' (φ i)).1
      tag_tendsto := hlim
      ratio_tendsto := s.ratio_tendsto.comp hψφ.tendsto_atTop
      energy_tendsto := s.energy_tendsto.comp hψφ.tendsto_atTop }
  have hσ := hcomp s₀ σ (by linarith) (fun i => ⟨_, rfl⟩)
  obtain ⟨r, -, hr1, hr2⟩ := ENNReal.lt_iff_exists_real_btwn.1 hc1
  have hKr : K * τ ^ p < r := by
    by_contra hc
    exact absurd hr1 (not_lt.2 (ENNReal.ofReal_le_ofReal (not_lt.1 hc)))
  have hgbm : tco_gbmExpect (transportD0 b E) (dStar b) (τ - s₀) ((X - C (dStar b)) ^ (2 * p)) ≤
      K * τ ^ p := by
    refine (hK (τ - s₀) (by linarith) (by linarith)).trans ?_
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) p) hK0
  have hδ := hσ ((X - C (dStar b)) ^ (2 * p)) (tco_convex_centered (dStar b) p) (r - K * τ ^ p)
    (by linarith)
  obtain ⟨i, hi⟩ := hδ.exists
  -- the `i`-th tag of the extracted sequence
  set j := ψ (φ i)
  have hgood := (hψP (φ i)).2
  have hb_le := hCA (s.W j) hgood.1 (s.energy j) hgood.2.1 (s.n j) hgood.2.2.1 (kk (φ i))
    (hkk' (φ i)).1
  set f : GrowthPath (s.W j) × (Fin 2 × Fin (s.W j) → ℂ) → ℝ := fun x =>
    (lmf_tagResponseClock b (s.energy j) (s.W j) (s.n j) (kk (φ i)) x - dStar b) ^ (2 * p)
  have hf0 : ∀ x, 0 ≤ f x := fun x => by
    simp only [f]; rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _
  have hfabs : ∀ x, |lmf_tagResponseClock b (s.energy j) (s.W j) (s.n j) (kk (φ i)) x -
      dStar b| ^ (2 * p) = f x := fun x => (even_two_mul p).pow_abs _
  have hfm : Measurable f :=
    ((tco_measurable_tagClock b _ _ _ _).sub_const _).pow_const _
  have hfint : Integrable f (probedClockLaw (s.W j) b) := by
    refine ⟨hfm.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    simp_rw [Real.enorm_of_nonneg (hf0 _), ← hfabs]
    exact hb_le.trans_lt ENNReal.ofReal_lt_top
  have heq : tco_tagMoment b s p j (kk (φ i)) =
      ENNReal.ofReal (∫ x, f x ∂probedClockLaw (s.W j) b) := by
    rw [ofReal_integral_eq_lintegral_ofReal hfint (ae_of_all _ hf0)]
    simp only [tco_tagMoment, hfabs]
  have hi' : ∫ x, f x ∂probedClockLaw (s.W j) b ≤ r := by
    have : ∫ x, ((X - C (dStar b)) ^ (2 * p) : ℝ[X]).eval (tco_tagZ b σ i x)
        ∂probedClockLaw (σ.W i) b = ∫ x, f x ∂probedClockLaw (s.W j) b := by
      simp only [eval_pow, eval_sub, eval_X, eval_C, f, tco_tagZ, σ, j]
    rw [← this]; linarith
  have hlt' : tco_tagMoment b s p j (kk (φ i)) < c' := by
    rw [heq]; exact (ENNReal.ofReal_le_ofReal hi').trans_lt hr2
  exact absurd (hkc (φ i)) (not_lt.2 hlt'.le)

/-!
## The averaged clause
-/

/-- The averaged bound and the `M_W` bound from the convex comparison. -/
theorem tco_flat_of_along (hMom : FullSourceMomentsEnergyUniformContract) {b : ℝ} (hb : 0 < b)
    (hb' : b < 1 / 2) {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) (T₀ : ℝ) {p : ℕ} (hp : 0 < p) :
    ∃ C : ℝ, ∀ τ : ℝ, 0 < τ → τ ≤ T₀ → ∀ s : ClockSequence τ E, TcoComparisonFrom b s →
      limsup (fun j => ((s.n j : ℝ≥0∞))⁻¹ * ∑ k ∈ Finset.range (s.n j),
          ∫⁻ x, ENNReal.ofReal
              (|lmf_tagResponseClock b (s.energy j) (s.W j) (s.n j) k x - dStar b| ^ (2 * p))
            ∂probedClockLaw (s.W j) b) atTop ≤ ENNReal.ofReal (C * τ ^ p) ∧
      limsup (fun j => ∫⁻ x, ENNReal.ofReal (|rescaledClock b s j x - dStar b| ^ (2 * p))
          ∂probedClockLaw (s.W j) b) atTop ≤ ENNReal.ofReal (C * τ ^ p) := by
  obtain ⟨K, hK0, hK⟩ := tco_gbmExpect_centered_le (transportD0 b E) (dStar b) T₀
    (tco_transportD0_nonneg hb hE1 hE2) p
  refine ⟨K, fun τ hτ hτT s hcomp => ?_⟩
  obtain ⟨κ, hκ, hκE⟩ := tco_bulk_margin hE1 hE2
  obtain ⟨CA, W₀, hCA0, hCA⟩ := tco_tag_centered_bound hMom hb hb' hκ (T₀ + 1) hp
  have hev := tco_eventually_good s hτ hτT hκE W₀
  set avg : ℕ → ℝ≥0∞ := fun j => ((s.n j : ℝ≥0∞))⁻¹ * ∑ k ∈ Finset.range (s.n j),
    tco_tagMoment b s p j k
  have hWpos : ∀ j, (0 : ℝ) < s.W j := fun j => by exact_mod_cast s.W_pos j
  -- for every `ε > 0`: `limsup avg ≤ ofReal(εC_A/τ) + ofReal(Kτ^p)`
  have hε_bound : ∀ ε : ℝ, 0 < ε → limsup avg atTop ≤
      ENNReal.ofReal (ε / τ * (CA + 1)) + ENNReal.ofReal (K * τ ^ p) := by
    intro ε hε
    set L : ℕ → ℝ≥0∞ := fun j => ((Finset.range (s.n j)).filter
      (fun k : ℕ => ε * s.W j ≤ k)).sup (tco_tagMoment b s p j)
    set u : ℕ → ℝ≥0∞ := fun j =>
      ENNReal.ofReal ((ε * s.W j + 1) / s.n j * CA)
    have hpt : ∀ᶠ j in atTop, avg j ≤ u j + L j := by
      filter_upwards [hev] with j hj
      obtain ⟨hj1, hj2, hj3, hj4⟩ := hj
      set n := s.n j
      set big := (Finset.range n).filter (fun k : ℕ => ε * s.W j ≤ k)
      set small := (Finset.range n).filter (fun k : ℕ => ¬ (ε * s.W j ≤ k))
      have hsplit : ∑ k ∈ Finset.range n, tco_tagMoment b s p j k =
          ∑ k ∈ big, tco_tagMoment b s p j k + ∑ k ∈ small, tco_tagMoment b s p j k :=
        (Finset.sum_filter_add_sum_filter_not _ _ _).symm
      have hbig : ∑ k ∈ big, tco_tagMoment b s p j k ≤ (n : ℝ≥0∞) * L j := by
        calc ∑ k ∈ big, tco_tagMoment b s p j k ≤ ∑ _k ∈ big, L j :=
              Finset.sum_le_sum fun k hk => Finset.le_sup hk
          _ = (big.card : ℝ≥0∞) * L j := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (n : ℝ≥0∞) * L j := by
              gcongr
              exact_mod_cast (Finset.card_filter_le _ _).trans (Finset.card_range n).le
      have hcard : (small.card : ℝ) ≤ ε * s.W j + 1 := by
        have hsub : small ⊆ Finset.range ⌈ε * s.W j⌉₊ := by
          intro k hk
          rw [Finset.mem_filter] at hk
          rw [Finset.mem_range]
          exact Nat.lt_ceil.2 (lt_of_not_ge hk.2)
        have := Finset.card_le_card hsub
        rw [Finset.card_range] at this
        calc (small.card : ℝ) ≤ ⌈ε * s.W j⌉₊ := by exact_mod_cast this
          _ ≤ ε * s.W j + 1 := (Nat.ceil_lt_add_one (by positivity)).le
      have hsmall : ∑ k ∈ small, tco_tagMoment b s p j k ≤
          (small.card : ℝ≥0∞) * ENNReal.ofReal CA := by
        calc ∑ k ∈ small, tco_tagMoment b s p j k ≤ ∑ _k ∈ small, ENNReal.ofReal CA :=
              Finset.sum_le_sum fun k hk => by
                rw [Finset.mem_filter, Finset.mem_range] at hk
                exact hCA (s.W j) hj1 (s.energy j) hj2 n hj3 k hk.1
          _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
      have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast hj4.ne'
      have hnR : (0 : ℝ) < n := by exact_mod_cast hj4
      simp only [avg]
      rw [hsplit, mul_add, add_comm (u j)]
      gcongr ?_ + ?_
      · calc ((n : ℝ≥0∞))⁻¹ * ∑ k ∈ big, tco_tagMoment b s p j k
            ≤ ((n : ℝ≥0∞))⁻¹ * ((n : ℝ≥0∞) * L j) := by gcongr
          _ = L j := by
              rw [← mul_assoc, ENNReal.inv_mul_cancel hn0 (ENNReal.natCast_ne_top n), one_mul]
      · calc ((n : ℝ≥0∞))⁻¹ * ∑ k ∈ small, tco_tagMoment b s p j k
            ≤ ((n : ℝ≥0∞))⁻¹ * ((small.card : ℝ≥0∞) * ENNReal.ofReal CA) := by gcongr
          _ = ENNReal.ofReal ((n : ℝ)⁻¹ * small.card * CA) := by
              rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
                ENNReal.ofReal_inv_of_pos hnR, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
                mul_assoc]
          _ ≤ u j := by
              refine ENNReal.ofReal_le_ofReal ?_
              rw [div_eq_inv_mul]
              have : (n : ℝ)⁻¹ * small.card ≤ (n : ℝ)⁻¹ * (ε * s.W j + 1) :=
                mul_le_mul_of_nonneg_left hcard (by positivity)
              nlinarith
    -- the limit of `u`
    have hn_top : Tendsto (fun j => (s.n j : ℝ)) atTop atTop := by
      have hW : Tendsto (fun j => (s.W j : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.comp s.width_tendsto
      have := s.ratio_tendsto.pos_mul_atTop hτ hW
      refine this.congr fun j => ?_
      rw [div_mul_cancel₀ _ (hWpos j).ne']
    have hu_lim : Tendsto (fun j => (ε * s.W j + 1) / s.n j * CA) atTop (𝓝 (ε / τ * CA)) := by
      have e : ∀ j, (ε * s.W j + 1) / s.n j * CA =
          (ε * ((s.n j : ℝ) / s.W j)⁻¹ + ((s.n j : ℝ))⁻¹) * CA := by
        intro j; rw [inv_div, add_div, mul_div_assoc, one_div]
      simp_rw [e]
      have h1 : Tendsto (fun j => ε * ((s.n j : ℝ) / s.W j)⁻¹ + ((s.n j : ℝ))⁻¹) atTop
          (𝓝 (ε * τ⁻¹ + 0)) :=
        ((s.ratio_tendsto.inv₀ hτ.ne').const_mul ε).add (tendsto_inv_atTop_zero.comp hn_top)
      rw [add_zero, ← div_eq_mul_inv] at h1
      exact h1.mul_const CA
    have hu_ev : ∀ᶠ j in atTop, u j ≤ ENNReal.ofReal (ε / τ * (CA + 1)) := by
      have hlt : ε / τ * CA < ε / τ * (CA + 1) := by
        have : 0 < ε / τ := by positivity
        nlinarith
      filter_upwards [hu_lim (Iio_mem_nhds hlt)] with j hj
      exact ENNReal.ofReal_le_ofReal (le_of_lt hj)
    have hpt' : ∀ᶠ j in atTop, avg j ≤ ENNReal.ofReal (ε / τ * (CA + 1)) + L j := by
      filter_upwards [hpt, hu_ev] with j h1 h2
      exact h1.trans (add_le_add_left h2 _)
    calc limsup avg atTop ≤ limsup (fun j => ENNReal.ofReal (ε / τ * (CA + 1)) + L j) atTop :=
          limsup_le_limsup hpt'
      _ = ENNReal.ofReal (ε / τ * (CA + 1)) + limsup L atTop :=
          limsup_const_add atTop L _ (by isBoundedDefault) (by isBoundedDefault)
      _ ≤ ENNReal.ofReal (ε / τ * (CA + 1)) + ENNReal.ofReal (K * τ ^ p) := by
          gcongr
          exact tco_large_tags hMom hb hb' hE1 hE2 hτ hτT hp s hcomp hK0 hK hε
  have havg : limsup avg atTop ≤ ENNReal.ofReal (K * τ ^ p) := by
    refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
    have hδR : (0 : ℝ) < δ := hδ
    set ε : ℝ := δ * τ / (CA + 1)
    have hε : 0 < ε := by positivity
    refine (hε_bound ε hε).trans ?_
    rw [add_comm]
    gcongr
    rw [← ENNReal.ofReal_coe_nnreal]
    refine ENNReal.ofReal_le_ofReal ?_
    have : ε / τ * (CA + 1) = δ := by
      simp only [ε]; field_simp
    rw [this]
  refine ⟨havg, ?_⟩
  refine le_trans (limsup_le_limsup ?_) havg
  filter_upwards [hev] with j hj
  exact tco_rescaledClock_jensen b s j hj.2.2.2 p

end BlockBand.Endpoints
