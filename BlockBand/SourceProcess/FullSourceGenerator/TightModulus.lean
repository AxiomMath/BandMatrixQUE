module

public import BlockBand.SourceProcess.FullSourceGenerator.TightFixed
public import BlockBand.SourceProcess.FullSourceGenerator.Interface
public import BlockBand.SourceProcess.FullSourceStops.LoadMoments

/-!
# The asymptotic modulus of a real trace polynomial

The tightness step with the stop tail, for a real ordinary polynomial `Φ`
(`IsRealPoly`) and the homogeneous families of `tight` (tags born before `t₀`, interval tests
supported in `[s, t₀]`): `modulus_real`, for all `η, θ > 0` there are `δ > 0` and `W₀` with
`P(∃ t, t' ∈ [t₁,T], |t-t'| ≤ δ, |X_{⌊Wt⌋} - X_{⌊Wt'⌋}| > η) ≤ θ` for `W ≥ W₀`.

Order of the choices: the stop level `K` (`FullSourceStopsContract.tail`: `C/K < θ/4`), then the
constants `C_𝒜, C_Γ, C_X` of `ae_polyValue_le_of_alive` and those of `EarlySummed` (for `Φ` and
`Φ^r`, `r ≤ 4`) and of the load moments; then `λ = η/12`, `κ = η/4` and `δ`; then `W₀`
(`modulus_fixed`, all errors `O(W^{-1/2})`).

Hypotheses: `EarlySummed`, `FullSourceStopsContract` (field `tail` only) and the four input
hypotheses of `FullSourceStops.lintegral_wordLoad_pow_le`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceGenerator

open MeasureTheory MvPolynomial Finset Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.FullSourceStops
open scoped ENNReal

variable {nT nI : ℕ}

theorem tendsto_err : Tendsto (fun W : ℕ => 1 / Real.sqrt W + 1 / (W : ℝ)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun W : ℕ => 1 / Real.sqrt W) atTop (𝓝 0) := by
    simp only [one_div]
    exact tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have := h1.add tendsto_one_div_atTop_nhds_zero_nat
  rwa [add_zero] at this

/-- **The asymptotic modulus of a real ordinary trace polynomial.** -/
theorem modulus_real (hES : EarlySummed) (hFS : FullSourceStopsContract)
    (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {E : ℝ}
    (hE1 : -2 < E) (hE2 : E < 2) {t₀ : ℝ} (ht₀ : 0 < t₀) {q : Fin nI → ℝ → ℝ}
    (hq : ∀ a, ∃ s : ℝ, IsSourceTest s t₀ (q a)) {k : ℕ → Fin nT → ℕ}
    (hk : ∀ᶠ W in atTop, ∀ a, ((k W a + 1 : ℕ) : ℝ) ≤ W * t₀) {Φ : TracePoly nT nI}
    (hΦ : IsOrdinaryPoly Φ) (hR : IsRealPoly b E q Φ) {t₁ T : ℝ} (ht₁ : t₀ ≤ t₁) (hT : t₁ < T)
    {η θ : ℝ} (hη : 0 < η) (hθ : 0 < θ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      growthPathLaw W b {ω | ∃ t ∈ Set.Icc t₁ T, ∃ t' ∈ Set.Icc t₁ T, |t - t'| ≤ δ ∧
        η < |realVal b E (k W) q W ⌊(W : ℝ) * t⌋₊ Φ ω -
          realVal b E (k W) q W ⌊(W : ℝ) * t'⌋₊ Φ ω|} ≤ ENNReal.ofReal θ := by
  have hqI : IsIntervalTests q := fun a => let ⟨s, hs⟩ := hq a; ⟨s, t₀, hs⟩
  have hq0 : ∀ a t, t₀ < t → q a t = 0 := fun a t ht => by
    obtain ⟨s, hs⟩ := hq a
    exact hs.2.1 t fun h => absurd h.2 (not_le.mpr ht)
  set ε := t₀ / 2
  have hε : 0 < ε := by positivity
  have hT0 : 0 < T := by linarith
  have hεT : ε < T + 1 := by show t₀ / 2 < T + 1; linarith
  -- the stop level
  obtain ⟨Cs, hCs⟩ := hFS.tail b hb0 hb E hE1 hE2 nT nI q hqI ε (T + 1) hε hεT
  set K := 4 * |Cs| / θ + 1
  have hK : 0 < K := by positivity
  have hCK : Cs / K < θ / 4 := by
    rw [div_lt_iff₀ hK]
    have : θ / 4 * K = |Cs| + θ / 4 := by simp only [K]; field_simp
    linarith [le_abs_self Cs]
  have hstop : ∀ᶠ W : ℕ in atTop, (⨆ k' : Fin nT → ℕ, growthPathLaw W b {ω | ∃ j : ℕ,
      ε * W ≤ j ∧ (j : ℝ) ≤ (T + 1) * W ∧ K < traceLoad b E k' q W j ω}) <
        ENNReal.ofReal (θ / 4) :=
    eventually_lt_of_limsup_lt ((hCs K hK).trans_lt
      (ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨hCK, by positivity⟩))
  -- the constants
  set CA := aliveBound K (wordGenerator b E q (t₀ + 1) Φ)
  set CG := aliveBound K (wordCarre b E Φ)
  set CX := aliveBound K Φ
  have hCA : 0 ≤ CA := aliveBound_nonneg hK.le _
  obtain ⟨Cd, Wd, hSd⟩ := hES b hb0 hb E hE1 hE2 nT nI q hqI Φ hΦ ε (T + 1) K hε hεT
  have hESr := fun r : ℕ => hES b hb0 hb E hE1 hE2 nT nI q hqI (Φ ^ r)
    (isOrdinaryPoly_pow hΦ r) ε (T + 1) K hε hεT
  choose Cr Wr hSr using hESr
  set κI := min (E + 2) (2 - E)
  have hκI : 0 < κI := lt_min (by linarith) (by linarith)
  have hEκ : E ∈ bulkInterval κI :=
    ⟨by linarith [min_le_left (E + 2) (2 - E)], by linarith [min_le_right (E + 2) (2 - E)]⟩
  obtain ⟨CL, WL, hCL, hL⟩ := lintegral_wordLoad_pow_le hMT hGA hLp hSR b hb0 hb κI hκI nT nI q
    hqI ε (T + 1) hε hεT (4 * polyExp Φ + 1) (by omega)
  -- the parameters
  set lam := η / 12
  set κ := η / 4
  have hlam : 0 < lam := by positivity
  have hκ : 0 < κ := by positivity
  set δ := min (1 / 2) (min (η / (4 * (CA + 1))) (θ * lam ^ 4 / (64 * (CG ^ 2 + 1) * (T + 1))))
  have hδ : 0 < δ := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hδ2 : δ ≤ 1 / 2 := min_le_left _ _
  have hδA : δ * CA ≤ η / 4 := by
    have h1 : δ ≤ η / (4 * (CA + 1)) := (min_le_right _ _).trans (min_le_left _ _)
    calc δ * CA ≤ η / (4 * (CA + 1)) * CA := mul_le_mul_of_nonneg_right h1 hCA
      _ ≤ η / 4 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hδG : 16 * CG ^ 2 * (T + 1) * δ / lam ^ 4 ≤ θ / 4 := by
    have h1 : δ ≤ θ * lam ^ 4 / (64 * (CG ^ 2 + 1) * (T + 1)) :=
      (min_le_right _ _).trans (min_le_right _ _)
    rw [div_le_iff₀ (by positivity)]
    have hT1 : 0 < T + 1 := by linarith
    have h3 : 16 * CG ^ 2 * (T + 1) * (θ * lam ^ 4 / (64 * (CG ^ 2 + 1) * (T + 1))) =
        θ * lam ^ 4 / 4 * (CG ^ 2 / (CG ^ 2 + 1)) := by field_simp; ring
    have h4 : CG ^ 2 / (CG ^ 2 + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    calc 16 * CG ^ 2 * (T + 1) * δ
        ≤ 16 * CG ^ 2 * (T + 1) * (θ * lam ^ 4 / (64 * (CG ^ 2 + 1) * (T + 1))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = θ * lam ^ 4 / 4 * (CG ^ 2 / (CG ^ 2 + 1)) := h3
      _ ≤ θ * lam ^ 4 / 4 * 1 := mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = θ / 4 * lam ^ 4 := by ring
  -- the vanishing errors
  set e : ℕ → ℝ := fun W => 1 / Real.sqrt W + 1 / (W : ℝ)
  set c4 : ℕ → ℝ := fun r => (Nat.choose 4 r : ℝ) * CX ^ (4 - r)
  have hmax : ∀ C : ℝ, Tendsto (fun W => max (C * e W) 0) atTop (𝓝 0) := fun C => by
    have h := (tendsto_err.const_mul C).max (tendsto_const_nhds (x := (0 : ℝ)))
    rw [mul_zero, max_self] at h; exact h
  have hrest : Tendsto (fun W : ℕ => (16 * CG ^ 2 * (T + 1) * (1 / (W : ℝ)) +
      16 * max (Cd * e W) 0 ^ 2 + 8 * lam ^ 2 * max (Cd * e W) 0 +
        48 * ∑ r ∈ range 5, c4 r * max (Cr r * e W) 0) / lam ^ 4) atTop (𝓝 0) := by
    have := ((((tendsto_one_div_atTop_nhds_zero_nat.const_mul (16 * CG ^ 2 * (T + 1))).add
      (((hmax Cd).pow 2).const_mul 16)).add ((hmax Cd).const_mul (8 * lam ^ 2))).add
      ((tendsto_finsetSum (range 5) fun r _ => (hmax (Cr r)).const_mul (c4 r)).const_mul
        48)).div_const (lam ^ 4)
    convert this using 2; simp
  have hG : Tendsto (fun W => max (Cd * e W) 0 / κ) atTop (𝓝 0) := by
    have h := (hmax Cd).div_const κ; rwa [zero_div] at h
  have hA : Tendsto (fun W : ℕ => CA * (1 / (W : ℝ))) atTop (𝓝 0) := by
    have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul CA; rwa [mul_zero] at h
  refine ⟨δ, hδ, ?_⟩
  rw [← eventually_atTop]
  filter_upwards [hstop, hk, eventually_ge_atTop Wd, eventually_ge_atTop WL,
    eventually_all_finset (range 5) |>.mpr fun r _ => eventually_ge_atTop (Wr r),
    eventually_ge_atTop (max 2 ⌈2 / t₀⌉₊), (tendsto_order.1 hrest).2 _ (by positivity : 0 < θ / 4),
    (tendsto_order.1 hG).2 _ (by positivity : 0 < θ / 4),
    (tendsto_order.1 hA).2 _ (by positivity : 0 < η / 4)] with W hWs hWk hWd hWL hWr hW2 hWR hWG hWA
  have hW2' : 2 ≤ W := le_trans (le_max_left _ _) hW2
  have hW2r : (2 : ℝ) ≤ W := by exact_mod_cast hW2'
  have hW0 : (0 : ℝ) < W := by linarith
  have hWt : 2 ≤ (W : ℝ) * t₀ := by
    have h := (Nat.le_ceil (2 / t₀)).trans (by exact_mod_cast le_trans (le_max_right _ _) hW2 :
      (⌈2 / t₀⌉₊ : ℝ) ≤ W)
    rw [div_le_iff₀ ht₀] at h; linarith
  set j₁ := ⌊(W : ℝ) * t₁⌋₊
  have hj₁ : (W : ℝ) * t₁ < j₁ + 1 := Nat.lt_floor_add_one _
  have hWt₁ : (W : ℝ) * t₀ ≤ W * t₁ := mul_le_mul_of_nonneg_left ht₁ hW0.le
  have hεj : ε * W ≤ j₁ := by simp only [ε]; nlinarith
  have hka : ∀ a, k W a < j₁ := fun a => Nat.lt_of_succ_le (Nat.le_floor ((hWk a).trans hWt₁))
  have hS := hSd W hWd (k W) j₁ hεj hka
  have hSr' : ∀ r < 5, _ := fun r hr =>
    (hSr r W (Finset.mem_range.mpr hr |> hWr r) (k W) j₁ hεj hka).1
  have hthr : 3 * lam + (δ + 1 / W) * CA + κ ≤ η := by
    have : (δ + 1 / W) * CA = δ * CA + CA * (1 / W) := by ring
    rw [this]; simp only [lam, κ]; linarith
  have key := modulus_fixed hb hE1 hE2 hW2' (k W) q hqI hq0 Φ hΦ hR hK.le ht₀ ht₁ hT hδ hδ2 hlam
    hκ hεj hthr hCL (fun j h1 h2 => hL W hWL E hEκ (k W) j h1 h2) (fun r => Cr r * e W) hS.1 hS.2
    hSr'
  refine key.trans ?_
  have hst : growthPathLaw W b {ω | ∃ j : ℕ, t₀ / 2 * W ≤ j ∧ (j : ℝ) ≤ (T + 1) * W ∧
      K < traceLoad b E (k W) q W j ω} ≤ ENNReal.ofReal (θ / 4) :=
    (le_iSup (fun k' : Fin nT → ℕ => growthPathLaw W b {ω | ∃ j : ℕ, ε * W ≤ j ∧
      (j : ℝ) ≤ (T + 1) * W ∧ K < traceLoad b E k' q W j ω}) (k W)).trans hWs.le
  have hR1 : (16 * CG ^ 2 * (T + 1) * (δ + 1 / W) + 16 * max (Cd * e W) 0 ^ 2 +
      8 * lam ^ 2 * max (Cd * e W) 0 + 48 * ∑ r ∈ range 5, (Nat.choose 4 r : ℝ) * CX ^ (4 - r) *
        max (Cr r * e W) 0) / lam ^ 4 ≤ θ / 2 := by
    have e1 : (16 * CG ^ 2 * (T + 1) * (δ + 1 / W) + 16 * max (Cd * e W) 0 ^ 2 +
        8 * lam ^ 2 * max (Cd * e W) 0 + 48 * ∑ r ∈ range 5, (Nat.choose 4 r : ℝ) *
          CX ^ (4 - r) * max (Cr r * e W) 0) / lam ^ 4 = 16 * CG ^ 2 * (T + 1) * δ / lam ^ 4 +
        (16 * CG ^ 2 * (T + 1) * (1 / (W : ℝ)) + 16 * max (Cd * e W) 0 ^ 2 +
          8 * lam ^ 2 * max (Cd * e W) 0 + 48 * ∑ r ∈ range 5, c4 r * max (Cr r * e W) 0) /
            lam ^ 4 := by
      simp only [c4]; ring
    rw [e1]; linarith [hWR.le]
  calc _ ≤ ENNReal.ofReal (θ / 4) + (ENNReal.ofReal (θ / 2) + ENNReal.ofReal (θ / 4)) :=
        add_le_add hst (add_le_add (ENNReal.ofReal_le_ofReal hR1) (ENNReal.ofReal_le_ofReal hWG.le))
    _ = ENNReal.ofReal θ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

end BlockBand.SourceProcess.FullSourceGenerator
