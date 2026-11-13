module

public import BlockBand.Endpoints.Response.RemoteHigherFiniteAlgebra
public import BlockBand.Endpoints.Response.NearSchattenStopped

/-!
# The chain-rule generator against the word generator of `G(Φ_π)` on the trace stop

* `rhf_specBracket_sub_le`, `rhf_abs_specBracket_le`: the bracket comparison
  `|Γ_π - Γ_f| ≤ Dδ(2M₁+1)(Σλ)²` and `|Γ_f| ≤ DM₁²(Σλ)²`.
* `rhf_rhlGenExpr_eq`: `rhlGenExpr = h'(H_ε)·𝒢_ε + ½ h''(H_ε)·Γ_ε` with `h(y) = (y+ε^p)^r`.
* `rhf_path_ranges`: on the stop, `|Tr π(A) - H_ε| ≤ δK` and both lie in `rhfRange p ε K`.
* `rhf_abs_polyGen_sub_rhlGenExpr_le` (the bridge on the stop): before the stop, at
  `j ≥ ε'W`, after the injection, with `𝕊` unitary, `π` a `δ`-approximant of `f_ε` in `C²` on
  `[0, K+1]`, `G` a `δ`-approximant of `h` in `C²` on `rhfRange p ε K`, `δ ≤ 1`,
  `δ(K+1) ≤ ε^p/2`: `|Re polyValue(𝒜_t G(Φ_π)) - rhlGenExpr| ≤ δ·rhfKappa` (chain rule
  `rhf_polyValue_wordGenerator_composite_path`, generator comparison
  `nss_abs_polyGen_sub_genExpr_le`, bracket comparison, Lipschitz bounds of `h'`, `h''`).
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
## The bracket comparison
-/

theorem rhf_sum_sq_le {ι : Type*} [Fintype ι] {lam : ι → ℝ} (h0 : ∀ i, 0 ≤ lam i) :
    ∑ i, lam i ^ 2 ≤ (∑ i, lam i) ^ 2 := nss_sum_pow_le h0 1

/-- `|Γ_π - Γ_f| ≤ D δ (2M₁ + 1) (Σλ)²`. -/
theorem rhf_specBracket_sub_le {ι : Type*} [Fintype ι] {D δ L M₁ : ℝ} (hD : 0 ≤ D)
    {d₁ e₁ : ℝ → ℝ} {lam s : ι → ℝ} (hlam : ∀ i, lam i ∈ Icc 0 L) (hs0 : ∀ i, 0 ≤ s i)
    (hs1 : ∀ i, s i ≤ 1) (h1 : ∀ x ∈ Icc 0 L, |d₁ x - e₁ x| ≤ δ)
    (hM : ∀ x ∈ Icc 0 L, |e₁ x| ≤ M₁) (hM₁ : 0 ≤ M₁) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    |rhfSpecBracket D d₁ lam s - rhfSpecBracket D e₁ lam s| ≤
      D * δ * (2 * M₁ + 1) * (∑ i, lam i) ^ 2 := by
  have hl0 : ∀ i, 0 ≤ lam i := fun i => (hlam i).1
  unfold rhfSpecBracket
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_nonneg hD]
  have hterm : ∀ i, |(lam i * d₁ (lam i)) ^ 2 * s i - (lam i * e₁ (lam i)) ^ 2 * s i| ≤
      δ * (2 * M₁ + 1) * lam i ^ 2 := by
    intro i
    have hd := h1 _ (hlam i)
    have he := hM _ (hlam i)
    rw [← sub_mul, abs_mul, abs_of_nonneg (hs0 i)]
    have e : (lam i * d₁ (lam i)) ^ 2 - (lam i * e₁ (lam i)) ^ 2 =
        lam i ^ 2 * ((d₁ (lam i) - e₁ (lam i)) * (d₁ (lam i) - e₁ (lam i) + 2 * e₁ (lam i))) := by
      ring
    rw [e, abs_mul, abs_of_nonneg (sq_nonneg _), abs_mul]
    have hsum : |d₁ (lam i) - e₁ (lam i) + 2 * e₁ (lam i)| ≤ 2 * M₁ + 1 := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_two]
      linarith
    have hprod : |d₁ (lam i) - e₁ (lam i)| * |d₁ (lam i) - e₁ (lam i) + 2 * e₁ (lam i)| ≤
        δ * (2 * M₁ + 1) := mul_le_mul hd hsum (abs_nonneg _) hδ
    calc lam i ^ 2 * (|d₁ (lam i) - e₁ (lam i)| *
          |d₁ (lam i) - e₁ (lam i) + 2 * e₁ (lam i)|) * s i
        ≤ lam i ^ 2 * (δ * (2 * M₁ + 1)) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hprod (sq_nonneg _)) (hs1 i) (hs0 i)
            (mul_nonneg (sq_nonneg _) ((mul_nonneg (abs_nonneg _) (abs_nonneg _)).trans hprod))
      _ = δ * (2 * M₁ + 1) * lam i ^ 2 := by ring
  have hsum := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
    hterm i)
  rw [← Finset.mul_sum] at hsum
  have h2 := rhf_sum_sq_le hl0
  calc D * |∑ i, ((lam i * d₁ (lam i)) ^ 2 * s i - (lam i * e₁ (lam i)) ^ 2 * s i)|
      ≤ D * (δ * (2 * M₁ + 1) * ∑ i, lam i ^ 2) := mul_le_mul_of_nonneg_left hsum hD
    _ ≤ D * (δ * (2 * M₁ + 1) * (∑ i, lam i) ^ 2) := by gcongr
    _ = _ := by ring

/-- `|Γ_f| ≤ D M₁² (Σλ)²`. -/
theorem rhf_abs_specBracket_le {ι : Type*} [Fintype ι] {D L M₁ : ℝ} (hD : 0 ≤ D)
    {e₁ : ℝ → ℝ} {lam s : ι → ℝ} (hlam : ∀ i, lam i ∈ Icc 0 L) (hs0 : ∀ i, 0 ≤ s i)
    (hs1 : ∀ i, s i ≤ 1) (hM : ∀ x ∈ Icc 0 L, |e₁ x| ≤ M₁) :
    |rhfSpecBracket D e₁ lam s| ≤ D * M₁ ^ 2 * (∑ i, lam i) ^ 2 := by
  have hl0 : ∀ i, 0 ≤ lam i := fun i => (hlam i).1
  unfold rhfSpecBracket
  have hnn : 0 ≤ ∑ i, (lam i * e₁ (lam i)) ^ 2 * s i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (hs0 i)
  rw [abs_of_nonneg (mul_nonneg hD hnn)]
  have hterm : ∀ i, (lam i * e₁ (lam i)) ^ 2 * s i ≤ M₁ ^ 2 * lam i ^ 2 := by
    intro i
    have he := hM _ (hlam i)
    have h2 : e₁ (lam i) ^ 2 ≤ M₁ ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) he 2
    calc (lam i * e₁ (lam i)) ^ 2 * s i ≤ (lam i * e₁ (lam i)) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (hs1 i) (sq_nonneg _)
      _ = lam i ^ 2 * e₁ (lam i) ^ 2 := by ring
      _ ≤ lam i ^ 2 * M₁ ^ 2 := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ = M₁ ^ 2 * lam i ^ 2 := by ring
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hterm i
  rw [← Finset.mul_sum] at hsum
  have h2 := rhf_sum_sq_le hl0
  calc D * ∑ i, (lam i * e₁ (lam i)) ^ 2 * s i ≤ D * (M₁ ^ 2 * ∑ i, lam i ^ 2) :=
        mul_le_mul_of_nonneg_left hsum hD
    _ ≤ D * (M₁ ^ 2 * (∑ i, lam i) ^ 2) := by gcongr
    _ = _ := by ring

/-!
## The chain-rule generator in terms of `h`
-/

/-- `rhlGenExpr = h'(H_ε)·𝒢_ε + ½ h''(H_ε)·Γ_ε`, `h(y) = (y+ε^p)^r`, `H_ε = Tr f_ε(A)`. -/
theorem rhf_rhlGenExpr_eq (b E p r ε : ℝ) (q : ℝ → ℝ) (W j : ℕ) (ω : GrowthPath W) :
    rhlGenExpr b E p r ε q W j ω =
      rhfH1 (ε ^ p) r (nsClockSum (nsRegKernel p ε) (nearClock b E W j q ω)) *
          nsgGenExpr b E p ε q W j ω +
        1 / 2 * rhfH2 (ε ^ p) r (nsClockSum (nsRegKernel p ε) (nearClock b E W j q ω)) *
          rhlBracketExpr b E p ε q W j ω := by
  unfold rhlGenExpr rhlShiftTrace rhfH1 rhfH2
  ring

/-- `0 ≤ H_ε ≤ pε^{p-1} Tr A`. -/
theorem rhf_clockSum_regKernel_bounds {p ε : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 < ε)
    {A : Matrix (Fin W) (Fin W) ℂ} (hA : A.PosSemidef) :
    0 ≤ nsClockSum (nsRegKernel p ε) A ∧
      nsClockSum (nsRegKernel p ε) A ≤ p * ε ^ (p - 1) * A.trace.re := by
  refine ⟨ns_clockSum_nonneg (fun x _ => ns_regKernel_nonneg hp0 hε x) hA, ?_⟩
  rw [ns_clockSum_eq _ hA.1]
  have hsum : ∑ i, hA.1.eigenvalues i = A.trace.re := by
    rw [hA.1.trace_eq_sum_eigenvalues, Complex.re_sum]; simp
  rw [← hsum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [mul_comm (p * ε ^ (p - 1))]
  exact mul_le_mul_of_nonneg_left (nsg_regKernel_le hp0 hp1 hε _) (hA.eigenvalues_nonneg i)

theorem rhf_mem_range_of {p ε K y : ℝ} (hp0 : 0 ≤ p) (hε : 0 < ε)
    (hlo : -(ε ^ p / 2) ≤ y) (hhi : y ≤ p * ε ^ (p - 1) * K + K) : y ∈ rhfRange p ε K := by
  refine ⟨hlo, hhi.trans ?_⟩
  have : 0 ≤ p * ε ^ (p - 1) := mul_nonneg hp0 (Real.rpow_nonneg hε.le _)
  nlinarith

/-!
## The bridge on the stop
-/

/-- `C₁ = (D/2) M_ε (K²/2 + K²)`, the bound of `|𝒢_ε|` on the stop. -/
def rhfC1 (b E p ε K : ℝ) : ℝ := transportD0 b E / 2 * nssGenConst p ε * (K / 2 * K + K ^ 2)

/-- `c₀ = (D/2)(K²/2 + K²)`, the generator comparison constant per unit `δ`. -/
def rhfc0 (b E K : ℝ) : ℝ := transportD0 b E / 2 * (K / 2 * K + K ^ 2)

/-- `C₂ = D (pε^{p-1})² K²`, the bound of `|Γ_ε|` on the stop. -/
def rhfC2 (b E p ε K : ℝ) : ℝ := transportD0 b E * (p * ε ^ (p - 1)) ^ 2 * K ^ 2

/-- `c₂ = D (2pε^{p-1} + 1) K²`, the bracket comparison constant per unit `δ`. -/
def rhfc2 (b E p ε K : ℝ) : ℝ := transportD0 b E * (2 * (p * ε ^ (p - 1)) + 1) * K ^ 2

/-- The comparison constant `κ` of the bridge (`|Re 𝒜G(Φ_π) - rhlGenExpr| ≤ δκ`). -/
def rhfKappa (b E p r ε K : ℝ) : ℝ :=
  (1 + rhfB p r ε K * K) * (rhfC1 b E p ε K + rhfc0 b E K) + rhfB p r ε K * rhfc0 b E K +
    ((1 + rhfB p r ε K * K) * (rhfC2 b E p ε K + rhfc2 b E p ε K) +
      rhfB p r ε K * rhfc2 b E p ε K) / 2

/-- `C₀ = B (C₁ + C₂/2)`, the bound of `|rhlGenExpr|` on the stop. -/
def rhfC0 (b E p r ε K : ℝ) : ℝ := rhfB p r ε K * (rhfC1 b E p ε K + rhfC2 b E p ε K / 2)

theorem rhf_consts_nonneg {b E p r ε K : ℝ} (hb : 0 < b) (hE : -2 < E) (hE' : E < 2)
    (hp0 : 0 ≤ p) (hε : 0 < ε) (hK : 0 ≤ K) :
    0 ≤ rhfC1 b E p ε K ∧ 0 ≤ rhfc0 b E K ∧ 0 ≤ rhfC2 b E p ε K ∧ 0 ≤ rhfc2 b E p ε K ∧
      0 ≤ rhfKappa b E p r ε K ∧ 0 ≤ rhfC0 b E p r ε K := by
  have hD := (ns_transportD0_pos hb hE hE').le
  have hM : 0 ≤ nssGenConst p ε :=
    (mul_nonneg hp0 (Real.rpow_nonneg hε.le _)).trans (le_max_left _ _)
  have hB := rhf_B_nonneg (p := p) (r := r) (K := K) hε
  have hM1 : 0 ≤ p * ε ^ (p - 1) := mul_nonneg hp0 (Real.rpow_nonneg hε.le _)
  have h1 : 0 ≤ rhfC1 b E p ε K := by unfold rhfC1; positivity
  have h2 : 0 ≤ rhfc0 b E K := by unfold rhfc0; positivity
  have h3 : 0 ≤ rhfC2 b E p ε K := by unfold rhfC2; positivity
  have h4 : 0 ≤ rhfc2 b E p ε K := by unfold rhfc2; positivity
  refine ⟨h1, h2, h3, h4, ?_, ?_⟩
  · unfold rhfKappa; positivity
  · unfold rhfC0; positivity

/-- The path quantities on the stop: eigenvalues, `Tr π(A)`, `H_ε` and their ranges. -/
theorem rhf_path_ranges {b E p ε : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 < ε)
    {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) {K ε' δ : ℝ} {a : ℕ → ℝ} {N : ℕ}
    (hπ0 : ∀ x ∈ Icc 0 (K + 1), |nsfPolyFun a N x - nsfRegFun p ε x| ≤ δ * x)
    (hδ1 : δ ≤ 1) (hδK : δ * (K + 1) ≤ ε ^ p / 2) {j : ℕ} {ω : GrowthPath W}
    (halive : ω ∈ alive b E (noTags W) (fun _ : Fin 1 => q) K ε' W j) (hj : ε' * W ≤ j)
    (hS : (scatteringMatrix b E W j ω)ᴴ * scatteringMatrix b E W j ω = 1) :
    0 ≤ K ∧ (nearClock b E W j q ω).trace.re ≤ K ∧
      |rhfClockVal b E q a N W j ω - nsClockSum (nsRegKernel p ε) (nearClock b E W j q ω)| ≤
        δ * K ∧
      rhfClockVal b E q a N W j ω ∈ rhfRange p ε K ∧
      nsClockSum (nsRegKernel p ε) (nearClock b E W j q ω) ∈ rhfRange p ε K ∧
      0 ≤ nsClockSum (nsRegKernel p ε) (nearClock b E W j q ω) := by
  have hpsd := ns_nearClock_posSemidef b E W j q hq ω
  obtain ⟨-, -, -, hA⟩ := nsf_alive_bounds (noTags W) hq halive hj hS
  have hA0 := (trace_nearClock_le b E W j q hq ω).1
  have hK : 0 ≤ K := hA0.trans hA
  have hsum : ∑ i, hpsd.1.eigenvalues i = (nearClock b E W j q ω).trace.re := by
    rw [hpsd.1.trace_eq_sum_eigenvalues, Complex.re_sum]; simp
  have hlam : ∀ i, hpsd.1.eigenvalues i ∈ Icc 0 (K + 1) := fun i =>
    ⟨hpsd.eigenvalues_nonneg i, (nsf_eigenvalue_le_trace hpsd i).trans (by linarith)⟩
  have hΨ : rhfClockVal b E q a N W j ω = ∑ i, nsfPolyFun a N (hpsd.1.eigenvalues i) := by
    unfold rhfClockVal
    rw [nsf_polyValue_clockPoly_path b E hq W j ω (noTags W) a N, Complex.ofReal_re]
  have hH := nsf_clockSum_regKernel (p := p) (ε := ε) hpsd
  have hdiff := nsf_sum_regFun_sub_le hπ0 hlam
  rw [← hΨ, ← hH, hsum] at hdiff
  have hδ0 : 0 ≤ δ := by
    have := hπ0 1 ⟨zero_le_one, by linarith⟩
    nlinarith [abs_nonneg (nsfPolyFun a N 1 - nsfRegFun p ε 1)]
  have hdK : |rhfClockVal b E q a N W j ω - nsClockSum (nsRegKernel p ε) (nearClock b E W j q ω)|
      ≤ δ * K := hdiff.trans (mul_le_mul_of_nonneg_left hA hδ0)
  obtain ⟨hH0, hHle⟩ := rhf_clockSum_regKernel_bounds hp0 hp1 hε hpsd
  have hM1 : 0 ≤ p * ε ^ (p - 1) := mul_nonneg hp0 (Real.rpow_nonneg hε.le _)
  have hHK : nsClockSum (nsRegKernel p ε) (nearClock b E W j q ω) ≤ p * ε ^ (p - 1) * K :=
    hHle.trans (mul_le_mul_of_nonneg_left hA hM1)
  have hεp := Real.rpow_pos_of_pos hε p
  have hδK' : δ * K ≤ ε ^ p / 2 := by nlinarith
  have hδK1 : δ * K ≤ K := by nlinarith
  obtain ⟨hd1, hd2⟩ := abs_le.1 hdK
  refine ⟨hK, hA, hdK, rhf_mem_range_of hp0 hε (by linarith) (by linarith),
    rhf_mem_range_of hp0 hε (by linarith) (by linarith), hH0⟩

/-- The bridge on the stop: `|Re polyValue(𝒜_t G(Φ_π)) - rhlGenExpr| ≤ δκ`. -/
theorem rhf_abs_polyGen_sub_rhlGenExpr_le {b E p r ε : ℝ} (hb : 0 < b) (hE : -2 < E)
    (hE' : E < 2) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 < ε) {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x)
    {K ε' δ : ℝ} {a : ℕ → ℝ} {N : ℕ} {G : ℝ[X]}
    (hπ0 : ∀ x ∈ Icc 0 (K + 1), |nsfPolyFun a N x - nsfRegFun p ε x| ≤ δ * x)
    (hπ1 : ∀ x ∈ Icc 0 (K + 1), |nsfPolyD1 a N x - nsgDeriv p ε x| ≤ δ)
    (hπ2 : ∀ x ∈ Icc 0 (K + 1), ∀ y ∈ Icc 0 (K + 1),
      |nsfDivDiff (nsfPolyD1 a N) (nsfPolyD2 a N) x y - nsgDivDiff p ε x y| ≤ δ)
    (hG1 : ∀ y ∈ rhfRange p ε K, |(derivative G).eval y - rhfH1 (ε ^ p) r y| ≤ δ)
    (hG2 : ∀ y ∈ rhfRange p ε K, |(derivative (derivative G)).eval y - rhfH2 (ε ^ p) r y| ≤ δ)
    (hδ1 : δ ≤ 1) (hδK : δ * (K + 1) ≤ ε ^ p / 2) {j : ℕ} {ω : GrowthPath W}
    (halive : ω ∈ alive b E (noTags W) (fun _ : Fin 1 => q) K ε' W j) (hj : ε' * W ≤ j)
    (hS : (scatteringMatrix b E W j ω)ᴴ * scatteringMatrix b E W j ω = 1) {t : ℝ}
    (hqt : q t = 0) :
    |(polyValue b E (noTags W) (fun _ => q) W j ω
          (wordGenerator b E (fun _ => q) t (rhfComposite a N G))).re -
        rhlGenExpr b E p r ε q W j ω| ≤ δ * rhfKappa b E p r ε K := by
  obtain ⟨hK, hA, hdK, hΨR, hHR, -⟩ :=
    rhf_path_ranges hp0 hp1 hε hq hπ0 hδ1 hδK halive hj hS
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (hπ1 0 ⟨le_rfl, by linarith⟩)
  obtain ⟨hC1, hc0, hC2, hc2, -, -⟩ :=
    rhf_consts_nonneg (r := r) hb hE hE' hp0 hε hK
  have hB := rhf_B_nonneg (p := p) (r := r) (K := K) hε
  have hD := (ns_transportD0_pos hb hE hE').le
  set Ψ := rhfClockVal b E q a N W j ω
  set H := nsClockSum (nsRegKernel p ε) (nearClock b E W j q ω)
  set B := rhfB p r ε K
  -- the trace generator
  have h𝒢 : |nsfGenExpr (nsfPolyD1 a N) (nsfPolyD2 a N) b E q W j ω - nsgGenExpr b E p ε q W j ω|
      ≤ δ * rhfc0 b E K := by
    have h := nss_abs_polyGen_sub_genExpr_le hb hE hE' hq hπ1 hπ2 (noTags W) halive hj hS hqt
    rw [nsf_polyValue_wordGenerator_path b E hq W j ω (noTags W) a N hqt, Complex.ofReal_re]
      at h
    exact h.trans_eq (by unfold rhfc0; ring)
  have h𝒢f : |nsgGenExpr b E p ε q W j ω| ≤ rhfC1 b E p ε K :=
    nss_abs_genExpr_le_alive hb hE hE' hp0 hp1 hε hq (noTags W) halive hj hS
  -- the bracket
  have hpsd := ns_nearClock_posSemidef b E W j q hq ω
  obtain ⟨hV, -⟩ := nsf_eigenframe hpsd.1
  have hsum : ∑ i, hpsd.1.eigenvalues i = (nearClock b E W j q ω).trace.re := by
    rw [hpsd.1.trace_eq_sum_eigenvalues, Complex.re_sum]; simp
  have hlam : ∀ i, hpsd.1.eigenvalues i ∈ Icc 0 (K + 1) := fun i =>
    ⟨hpsd.eigenvalues_nonneg i, (nsf_eigenvalue_le_trace hpsd i).trans (by linarith)⟩
  have hsq : (∑ i, hpsd.1.eigenvalues i) ^ 2 ≤ K ^ 2 := by
    rw [hsum]; exact pow_le_pow_left₀ (trace_nearClock_le b E W j q hq ω).1 hA 2
  have hMf : ∀ x ∈ Icc 0 (K + 1), |nsgDeriv p ε x| ≤ p * ε ^ (p - 1) :=
    fun x hx => nss_abs_deriv_le hp0 hp1 hε hx.1
  have hΓ : |rhfBracketExpr (nsfPolyD1 a N) b E q W j ω - rhlBracketExpr b E p ε q W j ω| ≤
      δ * rhfc2 b E p ε K := by
    rw [rhf_rhlBracketExpr_eq]
    unfold rhfBracketExpr
    rw [dite_eq_left hpsd.1, dite_eq_left hpsd.1]
    refine (rhf_specBracket_sub_le hD hlam (fun i => nsg_frameDiag_nonneg _ _ i)
      (fun i => nsg_frameDiag_le_one hS hV i) hπ1 hMf
      (mul_nonneg hp0 (Real.rpow_nonneg hε.le _)) hδ0 hδ1).trans ?_
    unfold rhfc2
    have : 0 ≤ transportD0 b E * δ * (2 * (p * ε ^ (p - 1)) + 1) := by
      have := mul_nonneg hp0 (Real.rpow_nonneg hε.le (p - 1)); positivity
    calc transportD0 b E * δ * (2 * (p * ε ^ (p - 1)) + 1) * (∑ i, hpsd.1.eigenvalues i) ^ 2
        ≤ transportD0 b E * δ * (2 * (p * ε ^ (p - 1)) + 1) * K ^ 2 :=
          mul_le_mul_of_nonneg_left hsq this
      _ = _ := by ring
  have hΓf : |rhlBracketExpr b E p ε q W j ω| ≤ rhfC2 b E p ε K := by
    rw [rhf_rhlBracketExpr_eq]
    unfold rhfBracketExpr
    rw [dite_eq_left hpsd.1]
    refine (rhf_abs_specBracket_le hD hlam (fun i => nsg_frameDiag_nonneg _ _ i)
      (fun i => nsg_frameDiag_le_one hS hV i) hMf).trans ?_
    unfold rhfC2
    exact mul_le_mul_of_nonneg_left hsq (by positivity)
  -- the two products
  have hu1 : |(derivative G).eval Ψ - rhfH1 (ε ^ p) r H| ≤ δ * (1 + B * K) := by
    have h1 := hG1 Ψ hΨR
    have h2 := rhf_abs_H1_sub_le (r := r) hε hΨR hHR
    have h3 : B * |Ψ - H| ≤ B * (δ * K) := mul_le_mul_of_nonneg_left hdK hB
    calc _ = |((derivative G).eval Ψ - rhfH1 (ε ^ p) r Ψ) +
          (rhfH1 (ε ^ p) r Ψ - rhfH1 (ε ^ p) r H)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ δ + B * (δ * K) := add_le_add h1 (h2.trans h3)
      _ = _ := by ring
  have hu2 : |(derivative (derivative G)).eval Ψ - rhfH2 (ε ^ p) r H| ≤ δ * (1 + B * K) := by
    have h1 := hG2 Ψ hΨR
    have h2 := rhf_abs_H2_sub_le (r := r) hε hΨR hHR
    have h3 : B * |Ψ - H| ≤ B * (δ * K) := mul_le_mul_of_nonneg_left hdK hB
    calc _ = |((derivative (derivative G)).eval Ψ - rhfH2 (ε ^ p) r Ψ) +
          (rhfH2 (ε ^ p) r Ψ - rhfH2 (ε ^ p) r H)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ δ + B * (δ * K) := add_le_add h1 (h2.trans h3)
      _ = _ := by ring
  have hv1 : |nsfGenExpr (nsfPolyD1 a N) (nsfPolyD2 a N) b E q W j ω| ≤
      rhfC1 b E p ε K + rhfc0 b E K := by
    have := abs_sub_abs_le_abs_sub (nsfGenExpr (nsfPolyD1 a N) (nsfPolyD2 a N) b E q W j ω)
      (nsgGenExpr b E p ε q W j ω)
    have : δ * rhfc0 b E K ≤ rhfc0 b E K := mul_le_of_le_one_left hc0 hδ1
    linarith
  have hv2 : |rhfBracketExpr (nsfPolyD1 a N) b E q W j ω| ≤ rhfC2 b E p ε K + rhfc2 b E p ε K := by
    have := abs_sub_abs_le_abs_sub (rhfBracketExpr (nsfPolyD1 a N) b E q W j ω)
      (rhlBracketExpr b E p ε q W j ω)
    have : δ * rhfc2 b E p ε K ≤ rhfc2 b E p ε K := mul_le_of_le_one_left hc2 hδ1
    linarith
  have hT1 := rhf_abs_mul_sub_le hu1 hv1 (rhf_abs_H1_le (r := r) hε hHR) h𝒢
  have hT2 := rhf_abs_mul_sub_le hu2 hv2 (rhf_abs_H2_le (r := r) hε hHR) hΓ
  rw [rhf_polyValue_wordGenerator_composite_path b E hq a N W j ω G hqt, Complex.ofReal_re,
    rhf_rhlGenExpr_eq]
  have e : (derivative G).eval Ψ * nsfGenExpr (nsfPolyD1 a N) (nsfPolyD2 a N) b E q W j ω +
        1 / 2 * (derivative (derivative G)).eval Ψ * rhfBracketExpr (nsfPolyD1 a N) b E q W j ω -
      (rhfH1 (ε ^ p) r H * nsgGenExpr b E p ε q W j ω +
        1 / 2 * rhfH2 (ε ^ p) r H * rhlBracketExpr b E p ε q W j ω) =
      ((derivative G).eval Ψ * nsfGenExpr (nsfPolyD1 a N) (nsfPolyD2 a N) b E q W j ω -
        rhfH1 (ε ^ p) r H * nsgGenExpr b E p ε q W j ω) +
      1 / 2 * ((derivative (derivative G)).eval Ψ * rhfBracketExpr (nsfPolyD1 a N) b E q W j ω -
        rhfH2 (ε ^ p) r H * rhlBracketExpr b E p ε q W j ω) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  unfold rhfKappa
  nlinarith

end BlockBand.Endpoints
