module

public import BlockBand.Endpoints.Response.RemoteHigherLimitDefs
public import BlockBand.Endpoints.Response.RemoteHigherLimitPassage
public import BlockBand.Endpoints.Response.RemoteHigherLimitDecay

/-!
# The regularized higher limit generator from a finite-width generator inequality

This file proves `RhlRegularizedLimitGenerator` from its finite-width form
`RhlFiniteTraceGenerator` (`rhl_regularizedLimitGenerator`).

At the path of length `j` (eigenvalues `λ_i` of the near clock `A`, `S_ii` the diagonal of the
projected block of `P' = 𝕊*P𝕊` in the eigenvector frame, `D = transportD0`), with
`H_ε = Tr f_ε(A)` and `Hδ = H_ε + ε^p`:
* `nsgGenExpr` (defined in another module) is the spectral right side of the Schatten trace
  generator, `𝒢H_ε`;
* `rhlBracketExpr` is the spectral bracket `Γ(H_ε,H_ε) = D Σ_i (λ_i f_ε'(λ_i))² S_ii`
  (`Γ(H_p,H_p) = D₀p² Tr(A^{2p}S)` at `ε = 0`);
* `rhlGenExpr = r Hδ^{r-1} 𝒢H_ε + ½ r(r-1) Hδ^{r-2} Γ(H_ε,H_ε)`, the chain rule for
  `Φ_ε = Hδ^r`.

## Main results

* `rhl_specBracket_le`: `Γ ≤ Dp² Diss_ε Hδ` (`S_ii ≤ 1`, `(λf_ε')² = p² λ²(λ+ε)^{p-2}(λ+ε)^p`,
  `(λ+ε)^p = λ·f_ε(λ)/λ + ε^p ≤ Hδ`).
* `rhl_chainRule_le`: the deterministic generator sign `rhlGenExpr ≤ -κ_r Hδ^{r-1} Diss_ε`,
  `κ_r = D r p(1-rp)/2`, from `𝒢H_ε ≤ -(Dp(1-p)/2)Diss_ε` and the bracket bound
  (`p(1-p) - (r-1)p = p(1-rp)`); `rhl_ae_genExpr_le`: almost surely at every length.
* `rhl_regularizedLimitGenerator`: the passage to critical limits.
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
## The bracket and the chain rule (deterministic)
-/

/-- The spectral bracket `Γ(Tr f_ε, Tr f_ε) = D Σ_i (λ_i f_ε'(λ_i))² S_ii`. -/
def rhlSpecBracket {ι : Type*} [Fintype ι] (D p ε : ℝ) (lam s : ι → ℝ) : ℝ :=
  D * ∑ i, (lam i * nsgDeriv p ε (lam i)) ^ 2 * s i

/-- `λ · f_ε(λ)/λ + ε^p = (λ+ε)^p` for `λ ≥ 0`. -/
theorem rhl_mul_regKernel_add {p ε x : ℝ} (hx : 0 ≤ x) :
    x * nsRegKernel p ε x + ε ^ p = (x + ε) ^ p := by
  rcases hx.eq_or_lt with h | h
  · subst h; simp
  · rw [ns_regKernel_of_pos h, mul_div_cancel₀ _ h.ne']; ring

/-- `(λ f_ε'(λ))² = p² (λ · λ(λ+ε)^{p-2}) (λ f_ε(λ)/λ + ε^p)` for `λ ≥ 0`. -/
theorem rhl_sq_deriv_eq {p ε x : ℝ} (hε : 0 < ε) (hx : 0 ≤ x) :
    (x * nsgDeriv p ε x) ^ 2 =
      p ^ 2 * (x * nsDissKernel p ε x) * (x * nsRegKernel p ε x + ε ^ p) := by
  have hy : 0 < x + ε := by linarith
  rw [rhl_mul_regKernel_add hx, nsgDeriv, nsDissKernel, max_eq_left hx]
  have h1 : ((x + ε) ^ (p - 1)) ^ 2 = (x + ε) ^ (p - 2) * (x + ε) ^ p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy.le, ← Real.rpow_add hy]
    congr 1; push_cast; ring
  calc (x * (p * (x + ε) ^ (p - 1))) ^ 2 = p ^ 2 * x ^ 2 * ((x + ε) ^ (p - 1)) ^ 2 := by ring
    _ = _ := by rw [h1]; ring

/-- The bracket bound `Γ ≤ D p² Diss_ε (H_ε + ε^p)` for `D ≥ 0`, `λ_i ≥ 0`, `S_ii ≤ 1`. -/
theorem rhl_specBracket_le {ι : Type*} [Fintype ι] {D p ε : ℝ} {lam s : ι → ℝ} (hD : 0 ≤ D)
    (hp : 0 ≤ p) (hε : 0 < ε) (hlam : ∀ i, 0 ≤ lam i) (hs1 : ∀ i, s i ≤ 1) :
    rhlSpecBracket D p ε lam s ≤ D * p ^ 2 * (∑ i, lam i * nsDissKernel p ε (lam i)) *
      (∑ i, lam i * nsRegKernel p ε (lam i) + ε ^ p) := by
  unfold rhlSpecBracket
  set H := ∑ i, lam i * nsRegKernel p ε (lam i)
  have hterm : ∀ i, (lam i * nsgDeriv p ε (lam i)) ^ 2 * s i ≤
      p ^ 2 * (lam i * nsDissKernel p ε (lam i)) * (H + ε ^ p) := by
    intro i
    have hd : 0 ≤ lam i * nsDissKernel p ε (lam i) :=
      mul_nonneg (hlam i) (ns_dissKernel_nonneg hε _)
    have hsingle : lam i * nsRegKernel p ε (lam i) ≤ H :=
      Finset.single_le_sum (f := fun j => lam j * nsRegKernel p ε (lam j))
        (fun j _ => mul_nonneg (hlam j) (ns_regKernel_nonneg hp hε _)) (Finset.mem_univ i)
    calc (lam i * nsgDeriv p ε (lam i)) ^ 2 * s i ≤ (lam i * nsgDeriv p ε (lam i)) ^ 2 :=
          mul_le_of_le_one_right (sq_nonneg _) (hs1 i)
      _ = p ^ 2 * (lam i * nsDissKernel p ε (lam i)) * (lam i * nsRegKernel p ε (lam i) + ε ^ p) :=
          rhl_sq_deriv_eq hε (hlam i)
      _ ≤ _ := by gcongr
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hterm i
  rw [← Finset.sum_mul, ← Finset.mul_sum] at hsum
  have := mul_le_mul_of_nonneg_left hsum hD
  linarith

/-- The deterministic generator sign of the chain rule: if `G₁ ≤ -(Dp(1-p)/2) X` (the generator
of `H_ε`, `X = Diss_ε ≥ 0`) and `Γ ≤ D p² X Hδ` (`Hδ > 0`), then
`r Hδ^{r-1} G₁ + ½ r(r-1) Hδ^{r-2} Γ ≤ -(D r p(1-rp)/2) Hδ^{r-1} X` (`r ≥ 1`, `D ≥ 0`). -/
theorem rhl_chainRule_le {D p r Hδ X G₁ Γ : ℝ} (hr : 1 ≤ r) (hH : 0 < Hδ)
    (hG₁ : G₁ ≤ -(D * p * (1 - p) / 2) * X) (hΓ : Γ ≤ D * p ^ 2 * X * Hδ) :
    r * Hδ ^ (r - 1) * G₁ + r * (r - 1) / 2 * Hδ ^ (r - 2) * Γ ≤
      -(D * r * p * (1 - r * p) / 2) * (Hδ ^ (r - 1) * X) := by
  have ha : 0 ≤ r * Hδ ^ (r - 1) := mul_nonneg (by linarith) (Real.rpow_nonneg hH.le _)
  have hb : 0 ≤ r * (r - 1) / 2 * Hδ ^ (r - 2) :=
    mul_nonneg (div_nonneg (mul_nonneg (by linarith) (by linarith)) zero_le_two)
      (Real.rpow_nonneg hH.le _)
  have h1 := mul_le_mul_of_nonneg_left hG₁ ha
  have h2 := mul_le_mul_of_nonneg_left hΓ hb
  have he : Hδ ^ (r - 2) * Hδ = Hδ ^ (r - 1) := by
    rw [← Real.rpow_add_one hH.ne']; congr 1; ring
  have h3 : r * (r - 1) / 2 * Hδ ^ (r - 2) * (D * p ^ 2 * X * Hδ) =
      r * (r - 1) / 2 * D * p ^ 2 * (Hδ ^ (r - 1) * X) := by
    rw [← he]; ring
  rw [h3] at h2
  nlinarith

/-!
## The finite-width chain rule at the path
-/

/-- The shifted regularized trace `Hδ = Tr f_ε(A) + ε^p` of the near clock at length `j`. -/
def rhlShiftTrace (b E p ε : ℝ) (q : ℝ → ℝ) (W j : ℕ) (ω : GrowthPath W) : ℝ :=
  nsClockSum (nsRegKernel p ε) (nearClock b E W j q ω) + ε ^ p

/-- The bracket `Γ(H_ε,H_ε) = D Σ_i (λ_i f_ε'(λ_i))² S_ii` at the path of length `j` (same
frame and data as `nsgGenExpr`). -/
def rhlBracketExpr (b E p ε : ℝ) (q : ℝ → ℝ) (W j : ℕ) (ω : GrowthPath W) : ℝ :=
  if hA : (nearClock b E W j q ω).IsHermitian then
    rhlSpecBracket (transportD0 b E) p ε hA.eigenvalues
      (nsgFrameDiag (scatteringMatrix b E W j ω) (hA.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ))
  else 0

/-- The chain-rule generator of `Φ_ε = (Tr f_ε(A) + ε^p)^r` at the path of length `j`:
`r Hδ^{r-1} 𝒢H_ε + ½ r(r-1) Hδ^{r-2} Γ(H_ε,H_ε)`. -/
def rhlGenExpr (b E p r ε : ℝ) (q : ℝ → ℝ) (W j : ℕ) (ω : GrowthPath W) : ℝ :=
  r * rhlShiftTrace b E p ε q W j ω ^ (r - 1) * nsgGenExpr b E p ε q W j ω +
    r * (r - 1) / 2 * rhlShiftTrace b E p ε q W j ω ^ (r - 2) * rhlBracketExpr b E p ε q W j ω

theorem rhl_shiftTrace_pos {b E p ε : ℝ} (hp : 0 ≤ p) (hε : 0 < ε) {q : ℝ → ℝ}
    (hq : ∀ x, 0 ≤ q x) {W j : ℕ} (ω : GrowthPath W) : 0 < rhlShiftTrace b E p ε q W j ω := by
  unfold rhlShiftTrace
  have := ns_clockSum_nonneg (fun x _ => ns_regKernel_nonneg hp hε x)
    (ns_nearClock_posSemidef b E W j q hq ω)
  have := Real.rpow_pos_of_pos hε p
  linarith

/-- The generator sign at the path: when `𝕊` is unitary,
`rhlGenExpr ≤ -κ_r Hδ^{r-1} Σ_i λ_i²(λ_i+ε)^{p-2}`. -/
theorem rhl_genExpr_le {b E p r ε : ℝ} (hb : 0 < b) (hE : -2 < E) (hE' : E < 2) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (hr : 1 ≤ r) (hε : 0 < ε) {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) {W j : ℕ}
    {ω : GrowthPath W} (hS : (scatteringMatrix b E W j ω)ᴴ * scatteringMatrix b E W j ω = 1) :
    rhlGenExpr b E p r ε q W j ω ≤ -rhlDecayRate b E p r *
      (rhlShiftTrace b E p ε q W j ω ^ (r - 1) *
        nsClockSum (nsDissKernel p ε) (nearClock b E W j q ω)) := by
  have hpsd := ns_nearClock_posSemidef b E W j q hq ω
  have hD := (ns_transportD0_pos hb hE hE').le
  have hG := nsg_genExpr_le hb hE hE' hp0 hp1 hε hq hS
  have hV : ((hpsd.1.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ))ᴴ *
      (hpsd.1.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ) = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Unitary.coe_star_mul_self _
  have hΓ : rhlBracketExpr b E p ε q W j ω ≤ transportD0 b E * p ^ 2 *
      nsClockSum (nsDissKernel p ε) (nearClock b E W j q ω) * rhlShiftTrace b E p ε q W j ω := by
    unfold rhlBracketExpr rhlShiftTrace
    rw [dite_eq_left hpsd.1, ns_clockSum_eq _ hpsd.1, ns_clockSum_eq _ hpsd.1]
    exact rhl_specBracket_le hD hp0 hε (fun i => hpsd.eigenvalues_nonneg i)
      (fun i => nsg_frameDiag_le_one hS hV i)
  have hG' : nsgGenExpr b E p ε q W j ω ≤ -(transportD0 b E * p * (1 - p) / 2) *
      nsClockSum (nsDissKernel p ε) (nearClock b E W j q ω) := by
    refine hG.trans_eq ?_
    unfold nsDecayRate; ring
  have h := rhl_chainRule_le hr (rhl_shiftTrace_pos hp0 hε hq ω) hG' hΓ
  unfold rhlGenExpr rhlDecayRate
  exact h

/-- Almost-sure generator sign at every length (`W > 0`). -/
theorem rhl_ae_genExpr_le (hCount : BlockBand.Internal.Contracts.Inputs.ConditionalBlockGUECount)
    {b E p r ε : ℝ} (hb : 0 < b) (hb1 : b < 1 / 2) (hE : -2 < E) (hE' : E < 2) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (hr : 1 ≤ r) (hε : 0 < ε) {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) {W : ℕ}
    (hW : 0 < W) (j : ℕ) :
    ∀ᵐ ω ∂growthPathLaw W b, rhlGenExpr b E p r ε q W j ω ≤ -rhlDecayRate b E p r *
      (rhlShiftTrace b E p ε q W j ω ^ (r - 1) *
        nsClockSum (nsDissKernel p ε) (nearClock b E W j q ω)) := by
  filter_upwards [nsg_ae_scattering_unitary hCount hb1 hE hE' hW j] with ω hS
  exact rhl_genExpr_le hb hE hE' hp0 hp1 hr hε hq hS

/-!
## The finite-width statement
-/

/-- The finite-width integrated chain-rule generator of `(Tr f_ε(A) + ε^p)^r`, the `r`-analogue
of `NsgFiniteTraceGenerator`. Fixed `0 < b < 1/2`, bulk `E`, `0 < p < 1`, `r ≥ 1`, `pr < 1`, a
unit source, `ε > 0`, times `t₁ + R < u₁ ≤ u₂`; for every `θ > 0`, for all large `W`:
`E Φ_ε(A_{⌊Wu₂⌋}) + ∫_{u₁}^{u₂} E[-𝒢Φ_ε(⌊Wu⌋)] du ≤ E Φ_ε(A_{⌊Wu₁⌋}) + θ`,
`Φ_ε(A) = (Tr f_ε(A) + ε^p)^r` (`Tr f_ε(A) = nsClockSum nsRegKernel`), `𝒢Φ_ε = rhlGenExpr`
(`-𝒢Φ_ε ≥ 0` a.s. by `rhl_ae_genExpr_le`).

It is a finite-width statement and asserts no sign and no dissipation (the generator sign
`-𝒢Φ_ε ≥ κ_r(H_ε+ε^p)^{r-1}Diss_ε` is `rhl_ae_genExpr_le`), nothing about critical limits (the
lower passages at `u₂` and in time and the sharp upper passage at `u₁` are proved in
`rhl_regularizedLimitGenerator`), and nothing about `H_p^r` itself (the entrance, Gronwall and
`ε ↓ 0` are in `rhl_limitDecay`). -/
def RhlFiniteTraceGenerator : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ p r : ℝ, 0 < p → p < 1 → 1 ≤ r → p * r < 1 →
    ∀ (t₁ R : ℝ) (q : ℝ → ℝ), IsUnitSource t₁ R q →
    ∀ ε : ℝ, 0 < ε → ∀ u₁ u₂ : ℝ, t₁ + R < u₁ → u₁ ≤ u₂ → ∀ θ : ℝ, 0 < θ →
      ∀ᶠ W : ℕ in atTop,
        ∫⁻ ω, ENNReal.ofReal ((nsClockSum (nsRegKernel p ε)
            (nearClock b E W ⌊(W : ℝ) * u₂⌋₊ q ω) + ε ^ p) ^ r) ∂growthPathLaw W b +
          ∫⁻ u in Icc u₁ u₂, ∫⁻ ω, ENNReal.ofReal
            (-rhlGenExpr b E p r ε q W ⌊(W : ℝ) * u⌋₊ ω) ∂growthPathLaw W b ≤
        ∫⁻ ω, ENNReal.ofReal ((nsClockSum (nsRegKernel p ε)
            (nearClock b E W ⌊(W : ℝ) * u₁⌋₊ q ω) + ε ^ p) ^ r) ∂growthPathLaw W b +
          ENNReal.ofReal θ

/-!
## The reduction
-/

/-- Limit-side identification `Φ_ε(μ) = ofReal((∫ f_ε(x)/x dμ + ε^p)^r)` for clock measures. -/
theorem rhl_powTrace_eq {Ω : Type*} {Z : ClockWord → ℝ → Ω → ℂ} {u : ℝ} {ω : Ω}
    {μ : Measure ℝ} (h : IsClockMeasure Z u ω μ) {p r ε : ℝ} (hp : 0 ≤ p) (hr : 0 ≤ r)
    (hε : 0 < ε) :
    rhlPowTrace p r ε μ = ENNReal.ofReal ((∫ x, nsRegKernel p ε x ∂μ + ε ^ p) ^ r) := by
  have hI : 0 ≤ ∫ x, nsRegKernel p ε x ∂μ := integral_nonneg (ns_regKernel_nonneg hp hε)
  rw [rhlPowTrace, ns_regTrace_eq h hp hε, ← ENNReal.ofReal_add hI (Real.rpow_nonneg hε.le _),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) hr]

/-- `κ · (H_ε + ε^p)^{r-1} Diss_ε = ofReal(κ (∫f_ε/x dμ + ε^p)^{r-1} ∫ x(x+ε)^{p-2} dμ)`. -/
theorem rhl_dissPowTrace_eq {Ω : Type*} {Z : ClockWord → ℝ → Ω → ℂ} {u : ℝ} {ω : Ω}
    {μ : Measure ℝ} (h : IsClockMeasure Z u ω μ) {p r ε κ : ℝ} (hp : 0 ≤ p) (hr : 1 ≤ r)
    (hε : 0 < ε) (hκ : 0 ≤ κ) :
    ENNReal.ofReal κ * rhlDissPowTrace p r ε μ = ENNReal.ofReal (κ *
      (∫ x, nsRegKernel p ε x ∂μ + ε ^ p) ^ (r - 1) * ∫ x, nsDissKernel p ε x ∂μ) := by
  have hI : 0 ≤ ∫ x, nsRegKernel p ε x ∂μ := integral_nonneg (ns_regKernel_nonneg hp hε)
  have hI' : 0 ≤ ∫ x, nsDissKernel p ε x ∂μ := integral_nonneg (ns_dissKernel_nonneg hε)
  have hb : 0 ≤ ∫ x, nsRegKernel p ε x ∂μ + ε ^ p := by
    have := Real.rpow_nonneg hε.le p; linarith
  rw [rhlDissPowTrace, ns_regTrace_eq h hp hε, ns_dissTrace_eq h hε,
    ← ENNReal.ofReal_add hI (Real.rpow_nonneg hε.le _),
    ENNReal.ofReal_rpow_of_nonneg hb (by linarith), ← ENNReal.ofReal_mul (Real.rpow_nonneg hb _),
    ← ENNReal.ofReal_mul hκ, mul_assoc]

/-- **`RhlRegularizedLimitGenerator` from the isolated finite-width chain-rule generator**.
Inputs: the isolated
`RhlFiniteTraceGenerator`; the `ConditionalBlockGUECount` (a.s. unitarity of `𝕊`, for
the generator sign); the `FullSourceMomentsContract` (`E (Tr A)^{2r}` for the sharp upper
passage at `u₁`).
-/
theorem rhl_regularizedLimitGenerator (hFin : RhlFiniteTraceGenerator)
    (hCount : BlockBand.Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hMom : FullSourceMomentsContract) : RhlRegularizedLimitGenerator := by
  intro b hb hb' E hE hE' p r hp hp1 hr hpr t₁ R q hq Ω _ P Z hZ μ hμ ε hε u₁ u₂ hu₁ hu₁₂
  have := hZ.prob
  obtain ⟨φ, hφ, hfdd⟩ := ns_fdd_of_isWordLimit hZ
  have hq0 : ∀ x, 0 ≤ q x := hq.2.2.2.1.1
  have hq1 : ∀ x, q x ≤ 1 := hq.2.2.2.2
  have hR0 : 0 ≤ t₁ + R := by linarith [hq.1, hq.2.1]
  have hr0 : 0 ≤ r := by linarith
  set δ : ℝ := ε ^ p with hδdef
  have hδ : 0 ≤ δ := Real.rpow_nonneg hε.le _
  set κ := rhlDecayRate b E p r with hκdef
  have hκ : 0 ≤ κ := rhl_decayRate_nonneg hb hE hE' hp hr hpr
  have hmeasu : ∀ u, t₁ + R ≤ u → ∀ k, 1 ≤ k → Measurable (Z (clockWord k) u) :=
    fun u hu k hk => hZ.measurable _ (ns_isOrdinaryWord_clockWord hk) u hu
  -- the two functionals
  set G₁ : ℝ → ℝ → ℝ := fun a _ => (a + δ) ^ r with hG₁
  have hG₁c : Continuous fun z : ℝ × ℝ => G₁ z.1 z.2 :=
    (continuous_fst.add continuous_const).rpow_const fun _ => Or.inr hr0
  have hG₁0 : ∀ a c, 0 ≤ a → 0 ≤ c → 0 ≤ G₁ a c := fun a c ha _ =>
    Real.rpow_nonneg (by linarith) _
  have hG₁m : ∀ a a' c c', 0 ≤ a → a ≤ a' → 0 ≤ c → c ≤ c' → G₁ a c ≤ G₁ a' c' :=
    fun a a' c c' ha haa _ _ => Real.rpow_le_rpow (by linarith) (by linarith) hr0
  set G₂ : ℝ → ℝ → ℝ := fun a c => κ * (a + δ) ^ (r - 1) * c with hG₂
  have hG₂c : Continuous fun z : ℝ × ℝ => G₂ z.1 z.2 :=
    (continuous_const.mul ((continuous_fst.add continuous_const).rpow_const
      fun _ => Or.inr (by linarith))).mul continuous_snd
  have hG₂0 : ∀ a c, 0 ≤ a → 0 ≤ c → 0 ≤ G₂ a c := fun a c ha hc =>
    mul_nonneg (mul_nonneg hκ (Real.rpow_nonneg (by linarith) _)) hc
  have hG₂m : ∀ a a' c c', 0 ≤ a → a ≤ a' → 0 ≤ c → c ≤ c' → G₂ a c ≤ G₂ a' c' := by
    intro a a' c c' ha haa hc hcc
    have h1 : (a + δ) ^ (r - 1) ≤ (a' + δ) ^ (r - 1) :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
    have h2 : 0 ≤ (a + δ) ^ (r - 1) := Real.rpow_nonneg (by linarith) _
    simp only [hG₂]
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hκ) hcc hc
      (mul_nonneg hκ (h2.trans h1))
  set a : ℕ → ℝ≥0∞ := fun n => ∫⁻ ω, ENNReal.ofReal ((nsClockSum (nsRegKernel p ε)
    (nearClock b E (φ n) ⌊(φ n : ℝ) * u₂⌋₊ q ω) + δ) ^ r) ∂growthPathLaw (φ n) b with ha
  set cc : ℕ → ℝ≥0∞ := fun n => ∫⁻ ω, ENNReal.ofReal ((nsClockSum (nsRegKernel p ε)
    (nearClock b E (φ n) ⌊(φ n : ℝ) * u₁⌋₊ q ω) + δ) ^ r) ∂growthPathLaw (φ n) b with hcc
  set G : ℕ → ℕ → ℝ≥0∞ := fun n j => ∫⁻ ω, ENNReal.ofReal
    (G₂ (nsClockSum (nsRegKernel p ε) (nearClock b E (φ n) j q ω))
      (nsClockSum (nsDissKernel p ε) (nearClock b E (φ n) j q ω))) ∂growthPathLaw (φ n) b
    with hG
  set d : ℕ → ℝ≥0∞ := fun n => ∫⁻ u in Icc u₁ u₂, G n ⌊(φ n : ℝ) * u⌋₊ with hd
  -- the finite-width inequality along `φ`, through the generator sign
  have hstep1 : ∀ θ : ℝ, 0 < θ → ∀ᶠ n in atTop, a n + d n ≤ cc n + ENNReal.ofReal θ := by
    intro θ hθ
    have h := hφ.tendsto_atTop.eventually
      (hFin b hb hb' E hE hE' p r hp hp1 hr hpr t₁ R q hq ε hε u₁ u₂ hu₁ hu₁₂ θ hθ)
    filter_upwards [h, hφ.tendsto_atTop.eventually (eventually_gt_atTop 0)] with n hn hWpos
    refine le_trans (add_le_add le_rfl ?_) hn
    refine lintegral_mono fun u => lintegral_mono_ae ?_
    filter_upwards [rhl_ae_genExpr_le hCount hb hb' hE hE' hp.le hp1.le hr hε hq0 hWpos
      ⌊(φ n : ℝ) * u⌋₊] with ω hω
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [hG₂]
    unfold rhlShiftTrace at hω
    linarith
  -- lower passage at `u₂`
  have hA : ∫⁻ ω, rhlPowTrace p r ε (μ u₂ ω) ∂P ≤ liminf a atTop := by
    have h := rhl_lintegral_pair_le_liminf hq0 (show t₁ + R ≤ u₂ by linarith)
      (hmeasu u₂ (by linarith)) hfdd (hμ u₂ (by linarith)) (ns_continuous_regKernel hε)
      (ns_regKernel_nonneg hp.le hε) (ns_continuous_regKernel hε) (ns_regKernel_nonneg hp.le hε)
      hG₁c hG₁0 hG₁m
    refine le_trans (le_of_eq (lintegral_congr_ae ?_)) h
    filter_upwards [hμ u₂ (by linarith)] with ω hω
    exact rhl_powTrace_eq hω hp.le hr0 hε
  -- lower passage in time (Fatou in `u`)
  have hD : ENNReal.ofReal κ * ∫⁻ u in Icc u₁ u₂, ∫⁻ ω, rhlDissPowTrace p r ε (μ u ω) ∂P ≤
      liminf d atTop := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ∫⁻ u in Icc u₁ u₂, ENNReal.ofReal κ * ∫⁻ ω, rhlDissPowTrace p r ε (μ u ω) ∂P
        ≤ ∫⁻ u in Icc u₁ u₂, liminf (fun n => G n ⌊(φ n : ℝ) * u⌋₊) atTop := by
          refine setLIntegral_mono' measurableSet_Icc fun u hu => ?_
          have hu0 : t₁ + R ≤ u := by linarith [hu.1]
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine le_trans (le_of_eq (lintegral_congr_ae ?_))
            (rhl_lintegral_pair_le_liminf hq0 hu0 (hmeasu u hu0) hfdd (hμ u hu0)
              (ns_continuous_regKernel hε) (ns_regKernel_nonneg hp.le hε)
              (ns_continuous_dissKernel hε) (ns_dissKernel_nonneg hε) hG₂c hG₂0 hG₂m)
          filter_upwards [hμ u hu0] with ω hω
          exact rhl_dissPowTrace_eq hω hp.le hr hε hκ
      _ ≤ liminf d atTop :=
          lintegral_liminf_le' fun n => (nsg_measurable_floor_comp (G n) (φ n)).aemeasurable
  -- sharp upper passage at `u₁`
  obtain ⟨C₂, W₀, hC₂⟩ := rhn_trace_sq_rpow_bound hMom hb hb' hE hE' (u := u₁) (by linarith)
    (r := r) (by linarith)
  have hUI : ∀ᶠ W : ℕ in atTop, ∫⁻ ω, ENNReal.ofReal
      ((nearClock b E W ⌊(W : ℝ) * u₁⌋₊ q ω).trace.re ^ 2) ^ r ∂growthPathLaw W b ≤
        ENNReal.ofReal C₂ := eventually_atTop.2 ⟨W₀, fun W hW => hC₂ W hW q hq0 hq1⟩
  have hC : limsup cc atTop ≤ ∫⁻ ω, rhlPowTrace p r ε (μ u₁ ω) ∂P := by
    have h := rhl_limsup_rpow_clockSum_le hq0 (show t₁ + R ≤ u₁ by linarith)
      (hmeasu u₁ (by linarith)) hφ hfdd (hμ u₁ (by linarith)) (ns_continuous_regKernel hε)
      (ns_regKernel_nonneg hp.le hε) (nsg_regKernel_le hp.le hp1.le hε) hδ hr hUI
    refine h.trans (le_of_eq (lintegral_congr_ae ?_))
    filter_upwards [hμ u₁ (by linarith)] with ω hω
    exact (rhl_powTrace_eq hω hp.le hr0 hε).symm
  -- combine
  set Cl := ∫⁻ ω, rhlPowTrace p r ε (μ u₁ ω) ∂P
  refine ENNReal.le_of_forall_pos_le_add fun θ hθ hClt => ?_
  have hθ2 : (0 : ℝ) < θ / 2 := by positivity
  have hlt : limsup cc atTop < Cl + ENNReal.ofReal (θ / 2) :=
    hC.trans_lt (ENNReal.lt_add_right hClt.ne (by simpa using hθ2))
  have hev : ∀ᶠ n in atTop, a n + d n ≤ Cl + ENNReal.ofReal (θ / 2) + ENNReal.ofReal (θ / 2) := by
    filter_upwards [hstep1 (θ / 2) hθ2, eventually_lt_of_limsup_lt hlt] with n h1 h2
    exact h1.trans (add_le_add h2.le le_rfl)
  have hsum := nsg_liminf_add_le hev
  have hθe : ENNReal.ofReal (θ / 2) + ENNReal.ofReal (θ / 2) = (θ : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_add hθ2.le hθ2.le, add_halves, ENNReal.ofReal_coe_nnreal]
  rw [add_assoc, hθe] at hsum
  exact (add_le_add hA hD).trans hsum

end BlockBand.Endpoints
