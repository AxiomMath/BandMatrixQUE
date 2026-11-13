module

public import BlockBand.Endpoints.Response.NearSchattenFiniteStop
public import BlockBand.Endpoints.Response.NearSchattenFinitePoly
public import BlockBand.Endpoints.Response.NearSchattenGenerator
public import BlockBand.Endpoints.Response.NearSchattenDecay
public import BlockBand.Endpoints.Response.NearSchattenProkhorov

/-!
# The finite-width trace generator from the word generator on the trace stop

This file reduces the finite-width trace generator inequality to the stopped word-energy
inequality `NsfStoppedWordEnergy` (`nsgFiniteTraceGenerator_of_stoppedWordEnergy`), and deduces
`NearSchattenDecayContract` from it (`nearSchattenDecay_of_stoppedWordEnergy`).
`NsfStoppedWordEnergy` is the integrated energy inequality for polynomial approximations `π` of
`f_ε` on a trace stop: on the stop survival event the dissipation is that of the word generator at
the clock polynomial `Φ_π`, off it that of `f_ε` itself.

* `nsf_neg_genExpr_le_poly`: on the stop, the generator expression of `f_ε` is controlled by that
  of a polynomial approximation.
* `nsf_lintegral_floor_le_sum` (Riemann form): `∫_{[u₁,u₂]} h(⌊Wu⌋) du ≤ Σ_{j₁≤j≤j₂} W⁻¹h(j)`
  (`h ≥ 0`, `j_i = ⌊Wu_i⌋`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Matrix Filter Topology Set Finset
open scoped ENNReal ComplexOrder
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Endpoints

/-!
## The bridge on the stop
-/

/-- Before the trace stop, at `j ≥ ε'W`, after the injection, with `𝕊` unitary and `π` a
`δ`-approximant of `f_ε` in `C²` on `[0,K+1]`:
`-𝒢_ε ≤ -Re polyValue(𝒜_tΦ_π) + (D/2)δ(K²/2 + K²)`. -/
theorem nsf_neg_genExpr_le_poly {b E p ε : ℝ} (hb : 0 < b) (hE : -2 < E) (hE' : E < 2)
    {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) {K ε' δ : ℝ} {a : ℕ → ℝ} {N : ℕ}
    (h1 : ∀ x ∈ Icc 0 (K + 1), |nsfPolyD1 a N x - nsgDeriv p ε x| ≤ δ)
    (h2 : ∀ x ∈ Icc 0 (K + 1), ∀ y ∈ Icc 0 (K + 1),
      |nsfDivDiff (nsfPolyD1 a N) (nsfPolyD2 a N) x y - nsgDivDiff p ε x y| ≤ δ)
    {W j : ℕ} {ω : GrowthPath W} (κ : Fin 0 → ℕ)
    (halive : ω ∈ alive b E κ (fun _ : Fin 1 => q) K ε' W j) (hj : ε' * W ≤ j)
    (hS : (scatteringMatrix b E W j ω)ᴴ * scatteringMatrix b E W j ω = 1) {t : ℝ}
    (hqt : q t = 0) :
    -nsgGenExpr b E p ε q W j ω ≤
      -(polyValue b E κ (fun _ => q) W j ω
          (wordGenerator b E (fun _ => q) t (nsfClockPoly a N))).re +
        transportD0 b E / 2 * δ * (K / 2 * K + K ^ 2) := by
  have hpsd := ns_nearClock_posSemidef b E W j q hq ω
  obtain ⟨hV, -⟩ := nsf_eigenframe hpsd.1
  obtain ⟨-, hg, -, hA⟩ := nsf_alive_bounds κ hq halive hj hS
  rw [nsf_polyValue_wordGenerator_path b E hq W j ω κ a N hqt, Complex.ofReal_re,
    nsf_nsgGenExpr_eq]
  unfold nsfGenExpr
  rw [dite_eq_left hpsd.1, dite_eq_left hpsd.1]
  set lam := hpsd.1.eigenvalues
  have hsum : ∑ i, lam i = (nearClock b E W j q ω).trace.re := by
    rw [hpsd.1.trace_eq_sum_eigenvalues, Complex.re_sum]; simp [lam]
  have hlam : ∀ i, lam i ∈ Icc 0 (K + 1) := fun i =>
    ⟨hpsd.eigenvalues_nonneg i, (nsf_eigenvalue_le_trace hpsd i).trans (by linarith)⟩
  have hg0 := nsg_conductance_nonneg hS
  have hD := (ns_transportD0_pos hb hE hE').le
  have hδ : 0 ≤ δ := (abs_nonneg _).trans (h1 0 ⟨le_rfl, by linarith [hlam]⟩)
  have hcmp := nsf_specGen_sub_le (L := K + 1) (d₂ := nsfPolyD2 a N) (e₂ := nsgDeriv2 p ε)
    hD hg0 hlam
    (fun i => nsg_frameDiag_nonneg _ _ i) (fun i => nsg_frameDiag_le_one hS hV i) h1
    (fun x hx y hy => h2 x hx y hy)
  have hS0 : 0 ≤ ∑ i, lam i := Finset.sum_nonneg fun i _ => (hlam i).1
  have hbd : transportD0 b E / 2 * δ * (nsgConductance (scatteringMatrix b E W j ω) *
      ∑ i, lam i + (∑ i, lam i) ^ 2) ≤ transportD0 b E / 2 * δ * (K / 2 * K + K ^ 2) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [hsum] at hS0 ⊢
    have hK0 : 0 ≤ K := hS0.trans hA
    gcongr
  have := (abs_le.1 (hcmp.trans hbd)).2
  linarith

/-!
## Riemann form
-/

theorem nsf_floor_eq_of_mem {W : ℕ} (hW : 0 < W) {j : ℕ} {u : ℝ}
    (hu : u ∈ Ico ((j : ℝ) / W) (((j : ℝ) + 1) / W)) : ⌊(W : ℝ) * u⌋₊ = j := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  rw [Nat.floor_eq_iff (mul_nonneg hW'.le ((by positivity : (0 : ℝ) ≤ j / W).trans hu.1))]
  constructor
  · have := hu.1; rw [div_le_iff₀ hW'] at this; linarith
  · have := hu.2; rw [lt_div_iff₀ hW'] at this; linarith

/-- Riemann form of the time integral: `∫_{[u₁,u₂]} h(⌊Wu⌋) du ≤ Σ_{j₁≤j≤j₂} W⁻¹ h(j)`. -/
theorem nsf_lintegral_floor_le_sum {W : ℕ} (hW : 0 < W) {u₁ u₂ : ℝ} (hu₁ : 0 ≤ u₁)
    (h : ℕ → ℝ≥0∞) :
    ∫⁻ u in Icc u₁ u₂, h ⌊(W : ℝ) * u⌋₊ ≤
      ∑ j ∈ Finset.Icc ⌊(W : ℝ) * u₁⌋₊ ⌊(W : ℝ) * u₂⌋₊, (W : ℝ≥0∞)⁻¹ * h j := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  set piece : ℕ → Set ℝ := fun j => Ico ((j : ℝ) / W) (((j : ℝ) + 1) / W)
  have hcover : Icc u₁ u₂ ⊆ ⋃ j ∈ Finset.Icc ⌊(W : ℝ) * u₁⌋₊ ⌊(W : ℝ) * u₂⌋₊, piece j := by
    intro u hu
    have hu0 : 0 ≤ (W : ℝ) * u := mul_nonneg hW'.le (hu₁.trans hu.1)
    refine Set.mem_biUnion (x := ⌊(W : ℝ) * u⌋₊) (Finset.mem_Icc.2
      ⟨Nat.floor_le_floor (mul_le_mul_of_nonneg_left hu.1 hW'.le),
        Nat.floor_le_floor (mul_le_mul_of_nonneg_left hu.2 hW'.le)⟩) ?_
    refine ⟨?_, ?_⟩
    · rw [div_le_iff₀ hW']; linarith [Nat.floor_le hu0]
    · rw [lt_div_iff₀ hW']; linarith [Nat.lt_floor_add_one ((W : ℝ) * u)]
  have hdisj : Set.PairwiseDisjoint (↑(Finset.Icc ⌊(W : ℝ) * u₁⌋₊ ⌊(W : ℝ) * u₂⌋₊)) piece := by
    intro j _ j' _ hjj'
    refine Set.disjoint_left.2 fun u hu hu' => hjj' ?_
    rw [← nsf_floor_eq_of_mem hW hu, ← nsf_floor_eq_of_mem hW hu']
  calc ∫⁻ u in Icc u₁ u₂, h ⌊(W : ℝ) * u⌋₊
      ≤ ∫⁻ u in ⋃ j ∈ Finset.Icc ⌊(W : ℝ) * u₁⌋₊ ⌊(W : ℝ) * u₂⌋₊, piece j,
          h ⌊(W : ℝ) * u⌋₊ := lintegral_mono_set hcover
    _ = ∑ j ∈ Finset.Icc ⌊(W : ℝ) * u₁⌋₊ ⌊(W : ℝ) * u₂⌋₊,
          ∫⁻ u in piece j, h ⌊(W : ℝ) * u⌋₊ :=
        lintegral_biUnion_finset hdisj (fun j _ => measurableSet_Ico) _
    _ = ∑ j ∈ Finset.Icc ⌊(W : ℝ) * u₁⌋₊ ⌊(W : ℝ) * u₂⌋₊, (W : ℝ≥0∞)⁻¹ * h j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [setLIntegral_congr_fun measurableSet_Ico (g := fun _ => h j)
          (fun u hu => by rw [nsf_floor_eq_of_mem hW hu]), setLIntegral_const, Real.volume_Ico,
          mul_comm]
        congr 1
        rw [show ((j : ℝ) + 1) / W - (j : ℝ) / W = (W : ℝ)⁻¹ by field_simp; ring,
          ENNReal.ofReal_inv_of_pos hW', ENNReal.ofReal_natCast]

/-!
## The stopped energy inequality
-/

/-- The trace stop survival event of the clock family (with level `K`). -/
abbrev nsfAlive (b E : ℝ) (q : ℝ → ℝ) (K u₁ : ℝ) (W j : ℕ) : Set (GrowthPath W) :=
  alive b E (noTags W) (fun _ : Fin 1 => q) K (u₁ / 2) W j

/-- The stopped dissipation integrand at length `j`: before the stop, the word generator
of the clock polynomial `Φ_π` at time `(j+1)/W` (`-Re polyValue(𝒜Φ_π)`, truncated at `0`);
after the stop, the regularized spectral generator `-𝒢_ε` (truncated at `0`).
-/
def nsfStoppedDiss (b E p ε : ℝ) (q : ℝ → ℝ) (K u₁ : ℝ) (a : ℕ → ℝ) (N W j : ℕ)
    (ω : GrowthPath W) : ℝ≥0∞ :=
  (nsfAlive b E q K u₁ W j).indicator (fun ω => ENNReal.ofReal
      (-(polyValue b E (noTags W) (fun _ => q) W j ω
        (wordGenerator b E (fun _ => q) (((j + 1 : ℕ) : ℝ) / W) (nsfClockPoly a N))).re)) ω +
    (nsfAlive b E q K u₁ W j)ᶜ.indicator
      (fun ω => ENNReal.ofReal (-nsgGenExpr b E p ε q W j ω)) ω

/-- **The stopped energy inequality with the word generator** (polynomial approximation on a
trace stop; the fixed clock and current moments remove the stops).
Fixed `0 < b < 1/2`, bulk `E`, `0 < p < 1`, a unit source `q`, `ε > 0`, `t₁ + R < u₁ ≤ u₂`, and
`θ > 0`.
There are a stop level `K > 0` and `δ₀ > 0` such that for every `δ ∈ (0, δ₀]` and every
polynomial `π(x) = Σ_r a_r x^{r+1}` that is a `δ`-approximant of `f_ε` in `C²` on `[0, K+1]`
(`|π - f_ε| ≤ δx`, `|π' - f_ε'| ≤ δ`, `|DD π' - DD f_ε'| ≤ δ`), for all large `W`, with
`j_i = ⌊Wu_i⌋` and the stop `σ_K` from `(u₁/2)W`:
`E Tr f_ε(A_{j₂}) + Σ_{j₁ ≤ j ≤ j₂} W⁻¹ E[1{j<σ}(-Re 𝒜Φ_π(j))⁺ + 1{j≥σ}(-𝒢_ε(j))⁺]
 ≤ E Tr f_ε(A_{j₁}) + θ`.

Derivation: `ContractingWordsContract.summed` for the ordinary `Φ_π` (`nsf_isOrdinaryPoly_clockPoly`) on the stop, telescoping with the
tower property and the `growthSigma`-adaptedness of `alive` (the `tcx_stopped_step` pattern),
`|π - f_ε| ≤ δx` before the stop, the exit value by `FullSourceGeneratorContract.tight`
(word `Tr QP`) with `FullSourceStopsContract.supMoments`, stop removal by `tail` and
`supMoments`, and the dissipation mass after the stop by `compensatorUI` (word `Tr QP`, whose
drift is `-(D/2) g Tr A`:
`nsf_polyValue_wordDrift_clockWord` at `r = 0`) and `supMoments`.
The sign `(·)⁺` before the stop costs `(D/2)δ(K²/2 + K²)` per unit time
(`nsf_neg_genExpr_le_poly` and `nsg_genExpr_le`), absorbed by `δ₀`.

Why strictly smaller than `NsgFiniteTraceGenerator`: the spectral generator `𝒢_ε` before the
stop is replaced by the `wordGenerator` of a clock polynomial; the identification of the
two (the `wordDrift` identity, the eigenframe, `g ≤ ½Tr|J| ≤ K/2`, `Tr A ≤ K`), the
existence of the `C²` approximants (Weierstrass) and the generator comparison, and the Riemann
form of the time integral are proved (`nsgFiniteTraceGenerator_of_stoppedWordEnergy`).
What remains is the probabilistic chain above.

It is a hypothesis of `nsgFiniteTraceGenerator_of_stoppedWordEnergy`; it is derived in
`nsfStoppedWordEnergy_of_exitRemoval`.
-/
def NsfStoppedWordEnergy : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ p : ℝ, 0 < p → p < 1 → ∀ (t₁ R : ℝ) (q : ℝ → ℝ), IsUnitSource t₁ R q →
    ∀ ε : ℝ, 0 < ε → ∀ u₁ u₂ : ℝ, t₁ + R < u₁ → u₁ ≤ u₂ → ∀ θ : ℝ, 0 < θ →
    ∃ K : ℝ, 0 < K ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
    ∀ (a : ℕ → ℝ) (N : ℕ),
      (∀ x ∈ Icc 0 (K + 1), |nsfPolyFun a N x - nsfRegFun p ε x| ≤ δ * x ∧
        |nsfPolyD1 a N x - nsgDeriv p ε x| ≤ δ) →
      (∀ x ∈ Icc 0 (K + 1), ∀ y ∈ Icc 0 (K + 1),
        |nsfDivDiff (nsfPolyD1 a N) (nsfPolyD2 a N) x y - nsgDivDiff p ε x y| ≤ δ) →
      ∀ᶠ W : ℕ in atTop,
        ∫⁻ ω, ENNReal.ofReal (nsClockSum (nsRegKernel p ε)
            (nearClock b E W ⌊(W : ℝ) * u₂⌋₊ q ω)) ∂growthPathLaw W b +
          ∑ j ∈ Finset.Icc ⌊(W : ℝ) * u₁⌋₊ ⌊(W : ℝ) * u₂⌋₊, (W : ℝ≥0∞)⁻¹ *
            ∫⁻ ω, nsfStoppedDiss b E p ε q K u₁ a N W j ω ∂growthPathLaw W b ≤
        ∫⁻ ω, ENNReal.ofReal (nsClockSum (nsRegKernel p ε)
            (nearClock b E W ⌊(W : ℝ) * u₁⌋₊ q ω)) ∂growthPathLaw W b + ENNReal.ofReal θ

/-!
## The reduction
-/

/-- The constant-slack sum: `Σ_{j₁≤j≤j₂} W⁻¹ c ≤ (u₂ - u₁ + 2) c` for `W ≥ 1`. -/
theorem nsf_sum_const_le {W : ℕ} (hW : 0 < W) {u₁ u₂ : ℝ} (hu₁ : 0 ≤ u₁) (hu : u₁ ≤ u₂) {c : ℝ}
    (hc : 0 ≤ c) :
    ∑ _j ∈ Finset.Icc ⌊(W : ℝ) * u₁⌋₊ ⌊(W : ℝ) * u₂⌋₊, (W : ℝ≥0∞)⁻¹ * ENNReal.ofReal c ≤
      ENNReal.ofReal ((u₂ - u₁ + 2) * c) := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have e1 : ((W : ℝ≥0∞))⁻¹ = ENNReal.ofReal ((W : ℝ)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos hW', ENNReal.ofReal_natCast]
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, e1, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ hc
  have h0 : 0 ≤ (W : ℝ) * u₁ := mul_nonneg hW'.le hu₁
  have h2 : ((⌊(W : ℝ) * u₂⌋₊ : ℕ) : ℝ) ≤ (W : ℝ) * u₂ := Nat.floor_le (h0.trans
    (mul_le_mul_of_nonneg_left hu hW'.le))
  have h1 : (W : ℝ) * u₁ < (⌊(W : ℝ) * u₁⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hcard : (((⌊(W : ℝ) * u₂⌋₊ + 1 - ⌊(W : ℝ) * u₁⌋₊ : ℕ)) : ℝ) ≤
      (W : ℝ) * u₂ + 2 - (W : ℝ) * u₁ := by
    rcases le_or_gt ⌊(W : ℝ) * u₁⌋₊ (⌊(W : ℝ) * u₂⌋₊ + 1) with h | h
    · rw [Nat.cast_sub h]; push_cast; linarith
    · rw [Nat.sub_eq_zero_of_le h.le]; simp; nlinarith
  rw [mul_comm, ← div_eq_inv_mul, div_le_iff₀ hW']
  nlinarith

/-- `NsgFiniteTraceGenerator` from `NsfStoppedWordEnergy` and `ConditionalBlockGUECount` (a.s.
unitarity of `𝕊`), via the Riemann form (`nsf_lintegral_floor_le_sum`), the bridge on the stop
(`nsf_neg_genExpr_le_poly`), the `C²` approximants `nsf_exists_poly_approx` and
`δ ≤ θ/(2(u₂−u₁+2)(c+1))`, `c = (D/2)(K²/2+K²)`.
-/
theorem nsgFiniteTraceGenerator_of_stoppedWordEnergy (hR : NsfStoppedWordEnergy)
    (hCount : BlockBand.Internal.Contracts.Inputs.ConditionalBlockGUECount) :
    NsgFiniteTraceGenerator := by
  intro b hb hb1 E hE hE' p hp hp1 t₁ R q hq ε hε u₁ u₂ hu₁ hu₂ θ hθ
  have hq0 : ∀ x, 0 ≤ q x := hq.2.2.2.1.1
  have hqoff : ∀ x, t₁ + R < x → q x = 0 := fun x hx =>
    hq.2.2.2.1.2.1 x fun h => by linarith [h.2]
  have hu₁0 : 0 < u₁ := by linarith [hq.1, hq.2.1]
  obtain ⟨K, hK, δ₀, hδ₀, hRK⟩ :=
    hR b hb hb1 E hE hE' p hp hp1 t₁ R q hq ε hε u₁ u₂ hu₁ hu₂ (θ / 2) (by positivity)
  set c := transportD0 b E / 2 * (K / 2 * K + K ^ 2) with hc
  have hD := (ns_transportD0_pos hb hE hE').le
  have hc0 : 0 ≤ c := by positivity
  set δ := min δ₀ (θ / 2 / ((u₂ - u₁ + 2) * (c + 1))) with hδdef
  have hδ : 0 < δ := lt_min hδ₀ (by have : 0 < u₂ - u₁ + 2 := by linarith
                                    positivity)
  have hδle : δ ≤ δ₀ := min_le_left _ _
  have hslack : (u₂ - u₁ + 2) * (c * δ) ≤ θ / 2 := by
    have h2 : δ ≤ θ / 2 / ((u₂ - u₁ + 2) * (c + 1)) := min_le_right _ _
    have hpos : 0 < (u₂ - u₁ + 2) * (c + 1) := by
      have : 0 < u₂ - u₁ + 2 := by linarith
      positivity
    rw [le_div_iff₀ hpos] at h2
    nlinarith [hδ.le]
  obtain ⟨a, N, hA1, hA2⟩ := nsf_exists_poly_approx (p := p) hε (L := K + 1) (by linarith) hδ
  filter_upwards [hRK δ hδ hδle a N hA1 hA2, eventually_gt_atTop 0,
    eventually_ge_atTop ⌈2 / u₁⌉₊] with W hW hW0 hWu
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW0
  have hWu' : 2 / u₁ ≤ W := (Nat.le_ceil _).trans (by exact_mod_cast hWu)
  -- per-length bound
  have hstep : ∀ j ∈ Finset.Icc ⌊(W : ℝ) * u₁⌋₊ ⌊(W : ℝ) * u₂⌋₊,
      ∫⁻ ω, ENNReal.ofReal (-nsgGenExpr b E p ε q W j ω) ∂growthPathLaw W b ≤
        ∫⁻ ω, nsfStoppedDiss b E p ε q K u₁ a N W j ω ∂growthPathLaw W b +
          ENNReal.ofReal (c * δ) := by
    intro j hj
    have hj1 := (Finset.mem_Icc.1 hj).1
    have hjW : u₁ / 2 * W ≤ j := by
      have h1 : (W : ℝ) * u₁ < (⌊(W : ℝ) * u₁⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
      have h2 : (⌊(W : ℝ) * u₁⌋₊ : ℝ) ≤ j := by exact_mod_cast hj1
      have h3 : 2 ≤ u₁ * W := by rw [div_le_iff₀ hu₁0] at hWu'; linarith
      nlinarith
    have hqt : q (((j + 1 : ℕ) : ℝ) / W) = 0 := by
      refine hqoff _ ?_
      have h1 : (W : ℝ) * u₁ < (⌊(W : ℝ) * u₁⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
      have h2 : (⌊(W : ℝ) * u₁⌋₊ : ℝ) ≤ j := by exact_mod_cast hj1
      rw [lt_div_iff₀ hW']
      push_cast
      nlinarith
    have hadd : ∫⁻ ω, (nsfStoppedDiss b E p ε q K u₁ a N W j ω + ENNReal.ofReal (c * δ))
        ∂growthPathLaw W b = ∫⁻ ω, nsfStoppedDiss b E p ε q K u₁ a N W j ω ∂growthPathLaw W b +
          ENNReal.ofReal (c * δ) := by
      have := passDeriv_isProbabilityMeasure_growthPathLaw W b
      rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
    rw [← hadd]
    refine lintegral_mono_ae ?_
    filter_upwards [nsg_ae_scattering_unitary hCount hb1 hE hE' hW0 j] with ω hS
    unfold nsfStoppedDiss
    by_cases hal : ω ∈ nsfAlive b E q K u₁ W j
    · rw [Set.indicator_of_mem hal, Set.indicator_of_notMem (Set.notMem_compl_iff.2 hal),
        add_zero]
      have hbr := nsf_neg_genExpr_le_poly hb hE hE' hq0 (fun x hx => (hA1 x hx).2) hA2
        (noTags W) hal hjW hS hqt
      calc ENNReal.ofReal (-nsgGenExpr b E p ε q W j ω)
          ≤ ENNReal.ofReal (-(polyValue b E (noTags W) (fun _ => q) W j ω
              (wordGenerator b E (fun _ => q) (((j + 1 : ℕ) : ℝ) / W)
                (nsfClockPoly a N))).re + c * δ) :=
            ENNReal.ofReal_le_ofReal (by rw [hc]; linarith)
        _ ≤ _ := ENNReal.ofReal_add_le
    · rw [Set.indicator_of_notMem hal, Set.indicator_of_mem (Set.mem_compl hal), zero_add]
      exact le_self_add
  calc ∫⁻ ω, ENNReal.ofReal (nsClockSum (nsRegKernel p ε)
          (nearClock b E W ⌊(W : ℝ) * u₂⌋₊ q ω)) ∂growthPathLaw W b +
        ∫⁻ u in Icc u₁ u₂, ∫⁻ ω, ENNReal.ofReal
          (-nsgGenExpr b E p ε q W ⌊(W : ℝ) * u⌋₊ ω) ∂growthPathLaw W b
      ≤ ∫⁻ ω, ENNReal.ofReal (nsClockSum (nsRegKernel p ε)
          (nearClock b E W ⌊(W : ℝ) * u₂⌋₊ q ω)) ∂growthPathLaw W b +
        (∑ j ∈ Finset.Icc ⌊(W : ℝ) * u₁⌋₊ ⌊(W : ℝ) * u₂⌋₊, (W : ℝ≥0∞)⁻¹ *
            ∫⁻ ω, nsfStoppedDiss b E p ε q K u₁ a N W j ω ∂growthPathLaw W b +
          ∑ j ∈ Finset.Icc ⌊(W : ℝ) * u₁⌋₊ ⌊(W : ℝ) * u₂⌋₊, (W : ℝ≥0∞)⁻¹ *
            ENNReal.ofReal (c * δ)) := by
        gcongr
        refine (nsf_lintegral_floor_le_sum hW0 hu₁0.le
          (fun j => ∫⁻ ω, ENNReal.ofReal (-nsgGenExpr b E p ε q W j ω) ∂growthPathLaw W b)).trans ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun j hj => ?_
        rw [← mul_add]
        exact mul_le_mul_right (hstep j hj) _
    _ ≤ (∫⁻ ω, ENNReal.ofReal (nsClockSum (nsRegKernel p ε)
          (nearClock b E W ⌊(W : ℝ) * u₁⌋₊ q ω)) ∂growthPathLaw W b + ENNReal.ofReal (θ / 2)) +
        ENNReal.ofReal (θ / 2) := by
        rw [← add_assoc]
        gcongr
        exact (nsf_sum_const_le hW0 hu₁0.le hu₂ (mul_nonneg hc0 hδ.le)).trans
          (ENNReal.ofReal_le_ofReal hslack)
    _ = _ := by
        rw [add_assoc, ← ENNReal.ofReal_add (by positivity) (by positivity), add_halves]

/-!
## The composite
-/

/-- `NearSchattenDecayContract` from `ClockFractionalEntranceContract`,
`FullSourceGeneratorContract`, `ConditionalBlockGUECount` and `NsfStoppedWordEnergy`.
-/
theorem nearSchattenDecay_of_stoppedWordEnergy (hEnt : ClockFractionalEntranceContract)
    (hGen : FullSourceGeneratorContract)
    (hCount : BlockBand.Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hR : NsfStoppedWordEnergy) : NearSchattenDecayContract :=
  nearSchattenDecay_holds hEnt hGen
    (nsg_regularizedLimitGenerator (nsgFiniteTraceGenerator_of_stoppedWordEnergy hR hCount)
      hCount hGen.moments)
    (nsCriticalClockLimitsExist_of_contracts hGen)

end BlockBand.Endpoints
