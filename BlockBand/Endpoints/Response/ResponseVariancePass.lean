module

public import BlockBand.Endpoints.Response.ResponseVariancePath

/-!
# The critical signed derivative along a critical sequence of matched-lead paths

Since `q_m(τ-s) = q_m(s)`, the pass-derivative lemma identifies the limit of the expected signed
derivative with `-8πρ(E)J_{τ,m}(x,y)`.

* `rv_isSignedResponse_unique`: the signed response value is unique (corner: `0`; otherwise every
  boundary-start realization gives it, and one exists).
* `rv_isSignedResponse_half`: for a test with `q(τ - ·) = q`, the response of
  `q + q(τ - ·) = 2q` is twice the response of `q`.
* `rv_signedPass_uniform`: clause 2 of the pass-derivative lemma (`passDerivative_of_contracts`,
  stated for path lengths given as a function of the width) transferred to a critical sequence
  `n_j/W_j → τ` (the width may repeat along the sequence), path lengths `r_j = n_j - 3` and the
  physical microscopic energies `e_j(u) = E + u/(N_jρ(E))`: uniformly in `|u| ≤ U`,
  `E ∂_q(F_L+F_R)(e_j(u)) → -4πρ(E)v`. Proof: a failing subsequence with strictly increasing
  widths defines a length function `j(W)` with `j(W)/W → τ`, and `e_j(u)` is the unfolded energy
  `E + u'/(r_jW_jρ(E))` with `u' = u r_j/n_j ∈ [-U, U]`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
  BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionUniform
  BlockBand.Internal.Contracts.Inputs
open scoped ENNReal NNReal

/-!
### The signed response value
-/

theorem rv_isSignedResponse_unique {D0 τ x y v₁ v₂ : ℝ} {g : ℝ → ℝ}
    (h₁ : IsSignedResponse D0 τ g x y v₁) (h₂ : IsSignedResponse D0 τ g x y v₂) : v₁ = v₂ := by
  rcases h₁ with ⟨hx, hy, hv⟩ | ⟨hc, ⟨Ω, m, 𝓖, P, N, X, Y, hP⟩, hval⟩
  · rcases h₂ with ⟨-, -, hv'⟩ | ⟨hc', -, -⟩
    · rw [hv, hv']
    · exact absurd ⟨hx, hy⟩ hc'
  · rcases h₂ with ⟨hx, hy, -⟩ | ⟨-, -, hval'⟩
    · exact absurd ⟨hx, hy⟩ hc
    · rw [← hval Ω m 𝓖 P N X Y hP, ← hval' Ω m 𝓖 P N X Y hP]

theorem rv_isSignedResponse_half {D0 τ x y v : ℝ} {q : ℝ → ℝ} (hq : ∀ t, q (τ - t) = q t)
    (h : IsSignedResponse D0 τ (fun t => q t + q (τ - t)) x y v) :
    IsSignedResponse D0 τ q x y (v / 2) := by
  have hg : (fun t => q t + q (τ - t)) = fun t => 2 * q t := by
    funext t; rw [hq]; ring
  rw [hg] at h
  rcases h with ⟨hx, hy, hv⟩ | ⟨hc, hex, hval⟩
  · exact Or.inl ⟨hx, hy, by rw [hv]; simp⟩
  · refine Or.inr ⟨hc, hex, fun Ω m 𝓖 P N X Y hP => ?_⟩
    have h2 := hval Ω m 𝓖 P N X Y hP
    have e : ∀ ω, responseIntegrand τ (fun t => 2 * q t) N X Y ω =
        2 * responseIntegrand τ q N X Y ω := by
      intro ω
      simp only [responseIntegrand]
      split_ifs
      · rw [← intervalIntegral.integral_const_mul]
        congr 1; funext s; ring
      · simp
    simp_rw [e] at h2
    rw [integral_const_mul] at h2
    linarith

theorem rvCosineTest_reflect (τ : ℝ) (hτ : τ ≠ 0) (m : ℤ) (t : ℝ) :
    rvCosineTest τ m (τ - t) = rvCosineTest τ m t := by
  rw [rvCosineTest, rvCosineTest]
  have : 2 * Real.pi * m * (τ - t) / τ = m * (2 * Real.pi) - 2 * Real.pi * m * t / τ := by
    field_simp
  rw [this, Real.cos_int_mul_two_pi_sub]

theorem rvCosineTest_continuous (τ : ℝ) (m : ℤ) : Continuous (rvCosineTest τ m) := by
  unfold rvCosineTest; fun_prop

theorem rvCosineTest_abs_le (τ : ℝ) (m : ℤ) (t : ℝ) : |rvCosineTest τ m t| ≤ 1 :=
  Real.abs_cos_le_one _

/-!
### A subsequence with strictly increasing widths
-/

/-- Recursive extraction: `ψ 0 = f 0 0`, `ψ (k+1) = f (ψ k) (W (ψ k))`. -/
def rvExtract (f : ℕ → ℕ → ℕ) (Wd : ℕ → ℕ) : ℕ → ℕ
  | 0 => f 0 0
  | k + 1 => f (rvExtract f Wd k) (Wd (rvExtract f Wd k))

theorem rv_extract {P : ℕ → Prop} {Wd : ℕ → ℕ} (h : ∀ M N : ℕ, ∃ k, M < k ∧ N < Wd k ∧ P k) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ StrictMono (fun k => Wd (ψ k)) ∧ ∀ k, P (ψ k) := by
  choose f hf using h
  refine ⟨rvExtract f Wd, strictMono_nat_of_lt_succ fun k => ?_,
    strictMono_nat_of_lt_succ fun k => ?_, fun k => ?_⟩
  · exact (hf _ _).1
  · exact (hf _ _).2.1
  · cases k with
    | zero => exact (hf 0 0).2.2
    | succ k => exact (hf _ _).2.2

/-!
### The length function along an injective subsequence
-/

open Classical in
/-- The length function: `r_{ψ k}` at the width `W_{ψ k}`, `⌊τW⌋` elsewhere. -/
def rvLengthFn (τ : ℝ) (Wd r : ℕ → ℕ) (ψ : ℕ → ℕ) (Wv : ℕ) : ℕ :=
  if h : ∃ k, Wd (ψ k) = Wv then r (ψ (Classical.choose h)) else ⌊τ * Wv⌋₊

theorem rvLengthFn_at {τ : ℝ} {Wd r : ℕ → ℕ} {ψ : ℕ → ℕ} (hinj : StrictMono (fun k => Wd (ψ k)))
    (k : ℕ) : rvLengthFn τ Wd r ψ (Wd (ψ k)) = r (ψ k) := by
  have h : ∃ k', Wd (ψ k') = Wd (ψ k) := ⟨k, rfl⟩
  rw [rvLengthFn, dite_eq_left h, hinj.injective (Classical.choose_spec h)]

theorem rvLengthFn_tendsto {τ : ℝ} (hτ : 0 < τ) {Wd r : ℕ → ℕ} {ψ : ℕ → ℕ}
    (hinj : StrictMono (fun k => Wd (ψ k)))
    (hlim : Tendsto (fun k => (r (ψ k) : ℝ) / Wd (ψ k)) atTop (𝓝 τ)) :
    Tendsto (fun Wv : ℕ => (rvLengthFn τ Wd r ψ Wv : ℝ) / Wv) atTop (𝓝 τ) := by
  have hfl : Tendsto (fun Wv : ℕ => ((⌊τ * Wv⌋₊ : ℕ) : ℝ) / Wv) atTop (𝓝 τ) :=
    (tendsto_nat_floor_mul_div_atTop hτ.le).comp tendsto_natCast_atTop_atTop
  rw [Metric.tendsto_atTop] at hfl hlim ⊢
  intro ε hε
  obtain ⟨K, hK⟩ := hlim ε hε
  obtain ⟨N₁, hN₁⟩ := hfl ε hε
  refine ⟨max N₁ (Wd (ψ K) + 1), fun Wv hWv => ?_⟩
  by_cases h : ∃ k, Wd (ψ k) = Wv
  · obtain ⟨k, hk⟩ := h
    have hkK : K ≤ k := by
      by_contra hlt
      push Not at hlt
      have := hinj hlt
      simp only at this
      omega
    rw [← hk, rvLengthFn_at hinj]
    exact hK k hkK
  · have : rvLengthFn τ Wd r ψ Wv = ⌊τ * Wv⌋₊ := by rw [rvLengthFn, dite_eq_right h]
    rw [this]
    exact hN₁ Wv (le_of_max_le_left hWv)

/-!
### Uniform convergence along the critical sequence
-/

theorem rv_microEnergy_eq_unfolded (p : Parameters) (E u : ℝ) (hρ : 0 < Parameters.semicircleDensity E) :
    microEnergy p E u =
      unfoldedEnergy E p.W (p.n - 3) (u * ((p.n - 3 : ℕ) : ℝ) / p.n) := by
  have hn : 4 ≤ p.n := p.n_ge_four
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hr : (0 : ℝ) < ((p.n - 3 : ℕ) : ℝ) := by exact_mod_cast (show 0 < p.n - 3 by omega)
  have hn0 : (0 : ℝ) < p.n := by exact_mod_cast (show 0 < p.n by omega)
  rw [microEnergy, unfoldedEnergy, Parameters.N, Nat.cast_mul]
  congr 1
  field_simp

/-- The critical signed derivative along a critical sequence, uniformly on the microscopic window
(clause 2 of the pass-derivative lemma, transferred). -/
theorem rv_signedPass_uniform (hMom : FullSourceMomentsContract)
    (hUnifLaw : TransmissionLawEnergyUniformContract)
    (hUnifMom : FullSourceMomentsEnergyUniformContract) (hBdry : DualBoundaryStartContract)
    (hCount : ConditionalBlockGUECount) {b : ℝ} (hb : 0 < b) (hb' : b < 1 / 2) {E : ℝ}
    (hE1 : -2 < E) (hE2 : E < 2) {τ : ℝ} (hτ : 0 < τ) (s : CriticalSequence τ) {x y : ℝ}
    (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y < 1) {q : ℝ → ℝ} (hqc : Continuous q)
    (hqb : ∃ Q : ℝ, ∀ t, |q t| ≤ Q) {v : ℝ}
    (hv : IsSignedResponse (transportD0 b E) τ (fun t => q t + q (τ - t)) x y v)
    (U ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ u ∈ Icc (-U) U,
      |signedPassDerivative b (microEnergy (s.parameters b hb hb' k) E u) x y (s.W k)
          (s.n k - 3) q + 4 * Real.pi * Parameters.semicircleDensity E * v| ≤ ε := by
  have hρ := semicircleDensity_pos hE1 hE2
  set bad : ℕ → Prop := fun k => ¬ ∀ u ∈ Icc (-U) U,
      |signedPassDerivative b (microEnergy (s.parameters b hb hb' k) E u) x y (s.W k)
          (s.n k - 3) q + 4 * Real.pi * Parameters.semicircleDensity E * v| ≤ ε
  by_contra H
  have hfreq : ∃ᶠ k in atTop, bad k := by
    rw [Filter.not_eventually] at H; exact H
  have hex : ∀ M N : ℕ, ∃ k, M < k ∧ N < s.W k ∧ bad k := by
    intro M N
    have h1 : ∀ᶠ k in atTop, M < k ∧ N < s.W k :=
      (eventually_gt_atTop M).and (s.width_tendsto.eventually_gt_atTop N)
    obtain ⟨k, ⟨hk1, hk2⟩, hk3⟩ := (h1.and_frequently hfreq).exists
    exact ⟨k, hk1, hk2, hk3⟩
  obtain ⟨ψ, hψ, hWψ, hbad⟩ := rv_extract hex
  -- the length function
  set r : ℕ → ℕ := fun k => s.n k - 3
  have hratio : Tendsto (fun k => (r k : ℝ) / s.W k) atTop (𝓝 τ) := by
    have h3 : Tendsto (fun k => (3 : ℝ) / s.W k) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp s.width_tendsto)
    have := s.ratio_tendsto.sub h3
    rw [sub_zero] at this
    refine this.congr fun k => ?_
    have hn := s.n_ge_four k
    have hW : (0 : ℝ) < s.W k := by exact_mod_cast s.W_pos k
    simp only [r]
    rw [Nat.cast_sub (by omega)]
    field_simp
    norm_num
  set jf := rvLengthFn τ s.W r ψ
  have hjf : Tendsto (fun Wv : ℕ => (jf Wv : ℝ) / Wv) atTop (𝓝 τ) :=
    rvLengthFn_tendsto hτ hWψ (hratio.comp hψ.tendsto_atTop)
  obtain ⟨-, hcl2⟩ := passDerivative_of_contracts hMom hUnifLaw hUnifMom hBdry hCount
  obtain ⟨v', hv', huni⟩ := hcl2 b hb hb' E hE1 hE2 τ hτ jf hjf x y hx hy0 hy1 q hqc hqb
  have hvv : v' = v := rv_isSignedResponse_unique hv' hv
  subst hvv
  obtain ⟨W₀, hW₀⟩ := huni U ε hε
  -- a bad index with large width
  obtain ⟨k, hk⟩ : ∃ k, W₀ ≤ s.W (ψ k) := ⟨W₀, hWψ.id_le W₀⟩
  apply hbad k
  intro u hu
  have hu' : u * ((s.n (ψ k) - 3 : ℕ) : ℝ) / s.n (ψ k) ∈ Icc (-U) U := by
    have hn := s.n_ge_four (ψ k)
    have hn0 : (0 : ℝ) < s.n (ψ k) := by exact_mod_cast (show 0 < s.n (ψ k) by omega)
    have hr0 : (0 : ℝ) ≤ ((s.n (ψ k) - 3 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hrn : ((s.n (ψ k) - 3 : ℕ) : ℝ) ≤ s.n (ψ k) := by exact_mod_cast Nat.sub_le _ _
    have hfrac0 : 0 ≤ ((s.n (ψ k) - 3 : ℕ) : ℝ) / s.n (ψ k) := div_nonneg hr0 hn0.le
    have hfrac1 : ((s.n (ψ k) - 3 : ℕ) : ℝ) / s.n (ψ k) ≤ 1 := (div_le_one hn0).2 hrn
    have e : u * ((s.n (ψ k) - 3 : ℕ) : ℝ) / s.n (ψ k) =
        u * (((s.n (ψ k) - 3 : ℕ) : ℝ) / s.n (ψ k)) := by ring
    rw [e]
    obtain ⟨hu1, hu2⟩ := hu
    have hU : 0 ≤ U := by linarith
    constructor <;> nlinarith
  have hmain := hW₀ (s.W (ψ k)) hk _ hu'
  have hjk : jf (s.W (ψ k)) = s.n (ψ k) - 3 := rvLengthFn_at hWψ k
  rw [hjk] at hmain
  rw [rv_microEnergy_eq_unfolded _ E u hρ]
  exact hmain

end BlockBand.Endpoints
