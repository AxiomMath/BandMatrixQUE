module

public import BlockBand.Endpoints.Response.PassDerivativeLimitPorts

/-!
# The pass-derivative lemma, clause 2: the critical derivative

Statement: the critical derivative is
`lim_W E ∂_q(F_L+F_R) = -4πρ(E) E_{x,y}[1{σ₀ ≤ τ} ∫_0^τ {q(s)+q(τ-s)} R_s ds]`.
Here `(X_s, Y_s)`, `R_s = X_s + Y_s` and `σ₀` are the `p = 1` diffusion of the transmission law,
with absorption at its corner. The convergence is uniform for deterministic energies in the
bounded unfolded window.

## Lean form (`passDerivative_clause2`)

* Law and objects as in clause 1 (`growthPathLaw W b`, `portRatioSum`, `0 < b < 1/2`, bulk `E`,
  lengths `j W` with `j W / W → τ > 0`, `x ≥ 0`, `0 ≤ y < 1`).
* Signed test: `q : ℝ → ℝ` continuous and bounded (`|q| ≤ Q`); the physical source evaluates `q`
  at the block positions `(n-i)/W`, which may exceed `τ` when `n ≠ τW`, so `q` is given on all of
  `ℝ` (a test given on `[0, τ]` enters through any continuous bounded extension, e.g.
  `q ∘ projIcc 0 τ`, and the right side only sees `[0, τ]`). The signed derivative
  `∂_q := ∂_{q₊} - ∂_{q₋}`, `q± = max(±q, 0)`, of the expected right derivatives at zero source
  (`signedPassDerivative`).
* Energies: the unfolded window `E + u/(Nρ(E))`, `N = nW`, `|u| ≤ U` (`unfoldedEnergy`);
  "uniformly" is `∀ U, ∀ ε > 0, ∃ W₀, ∀ W ≥ W₀, ∀ |u| ≤ U`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Set Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
  BlockBand.Internal.Contracts.TransmissionUniform BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Layers
open scoped ENNReal NNReal Matrix.Norms.L2Operator

/-!
### Definitions
-/

/-- The unfolded energy `E + u/(Nρ(E))`, `N = nW` (`n` blocks of width `W`). -/
def unfoldedEnergy (E : ℝ) (W n : ℕ) (u : ℝ) : ℝ :=
  E + u / (((n : ℝ) * W) * Parameters.semicircleDensity E)

/-- The positive part `q₊ = max(q, 0)`. -/
def posPart (q : ℝ → ℝ) : ℝ → ℝ := fun t => max (q t) 0

/-- The negative part `q₋ = max(-q, 0)`. -/
def negPart (q : ℝ → ℝ) : ℝ → ℝ := fun t => max (-q t) 0

/-- The expected signed derivative `E ∂_q(F_L + F_R)` at zero source: the difference of the
expected right derivatives along `q₊` and `q₋`. -/
def signedPassDerivative (b E x y : ℝ) (W n : ℕ) (q : ℝ → ℝ) : ℝ :=
  (∫ ω, derivWithin (fun κ => portRatioSum b E x y W n (posPart q) κ ω) (Ici 0) 0
      ∂growthPathLaw W b) -
    ∫ ω, derivWithin (fun κ => portRatioSum b E x y W n (negPart q) κ ω) (Ici 0) 0
      ∂growthPathLaw W b

/-!
### The expected derivative splits over the ports
-/

theorem integral_derivWithin_eq {b E x y : ℝ} {W n : ℕ} (hb : b ≤ 1) (hE1 : -2 < E)
    (hE2 : E < 2) (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y < 1) {q : ℝ → ℝ} (hq : ∀ t, 0 ≤ q t)
    (hinv : ∀ᵐ ω ∂growthPathLaw W b, IsUnit (fullPathMatrix b E W n ω).det)
    (h0 : Integrable (fun ω => portDeriv b E x y W n q 0 ω) (growthPathLaw W b))
    (h1 : Integrable (fun ω => portDeriv b E x y W n q 1 ω) (growthPathLaw W b)) :
    ∫ ω, derivWithin (fun κ => portRatioSum b E x y W n q κ ω) (Ici 0) 0 ∂growthPathLaw W b =
      (∫ ω, portDeriv b E x y W n q 0 ω ∂growthPathLaw W b) +
        ∫ ω, portDeriv b E x y W n q 1 ω ∂growthPathLaw W b := by
  rw [← integral_add h0 h1]
  refine integral_congr_ae ?_
  filter_upwards [ae_growthPath_isHermitian W b, hinv] with ω hH hM
  obtain ⟨-, h2⟩ := portRatio_pointwise hb hE1 hE2 hx hy0 hy1 hq hH
  rw [(h2 hM).2.1.derivWithin (uniqueDiffWithinAt_Ici 0), portRatioDeriv_eq_add]

/-!
### Along one moving energy
-/

theorem posPart_continuous {q : ℝ → ℝ} (hq : Continuous q) : Continuous (posPart q) :=
  hq.max continuous_const

theorem negPart_continuous {q : ℝ → ℝ} (hq : Continuous q) : Continuous (negPart q) :=
  hq.neg.max continuous_const

theorem posPart_sub_negPart (q : ℝ → ℝ) (t : ℝ) : posPart q t - negPart q t = q t := by
  simp only [posPart, negPart]
  rcases le_total (q t) 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring

/-- The signed critical derivative along one moving energy, off the corner. -/
theorem signed_tendsto (hUnifLaw : TransmissionLawEnergyUniformContract)
    (hUnifMom : FullSourceMomentsEnergyUniformContract) (hBdry : DualBoundaryStartContract)
    (hInvU : PathFractionalInverseEnergyUniform) {b E x y τ Ce : ℝ} (hb0 : 0 < b)
    (hb1 : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y < 1)
    (hxy : ¬(x = 0 ∧ y = 0)) (hτ : 0 < τ) {j : ℕ → ℕ}
    (hj : Tendsto (fun W : ℕ => (j W : ℝ) / W) atTop (𝓝 τ)) {q : ℝ → ℝ} (hqc : Continuous q)
    {Q : ℝ} (hqQ : ∀ t, |q t| ≤ Q) {e : ℕ → ℝ} (he : IsMovingEnergy E Ce e) :
    ∃ v, ResponseData (transportD0 b E) τ (fun s => q s + q (τ - s)) x y v ∧
      Tendsto (fun W : ℕ => signedPassDerivative b (e W) x y W (j W) q) atTop
        (𝓝 (-(4 * Real.pi * Parameters.semicircleDensity E) * v)) := by
  have hp0 : ∀ t, 0 ≤ posPart q t := fun t => le_max_right _ _
  have hn0 : ∀ t, 0 ≤ negPart q t := fun t => le_max_right _ _
  have hpQ : ∀ t, posPart q t ≤ max Q 0 := fun t =>
    max_le_max (le_trans (le_abs_self _) (hqQ t)) le_rfl
  have hnQ : ∀ t, negPart q t ≤ max Q 0 := fun t =>
    max_le_max (le_trans (neg_le_abs _) (hqQ t)) le_rfl
  have hpc := posPart_continuous hqc
  have hnc := negPart_continuous hqc
  obtain ⟨v₁, hv₁, hl₁⟩ := nearPort_tendsto hUnifLaw hUnifMom hBdry hInvU hb0 hb1 hE1 hE2 hx hy0
    hy1 hxy hτ hj hpc hp0 hpQ he
  obtain ⟨v₂, hv₂, hl₂⟩ := farPort_tendsto hUnifLaw hUnifMom hBdry hInvU hb0 hb1 hE1 hE2 hx hy0
    hy1 hxy hτ hj hpc hp0 hpQ he
  obtain ⟨v₃, hv₃, hl₃⟩ := nearPort_tendsto hUnifLaw hUnifMom hBdry hInvU hb0 hb1 hE1 hE2 hx hy0
    hy1 hxy hτ hj hnc hn0 hnQ he
  obtain ⟨v₄, hv₄, hl₄⟩ := farPort_tendsto hUnifLaw hUnifMom hBdry hInvU hb0 hb1 hE1 hE2 hx hy0
    hy1 hxy hτ hj hnc hn0 hnQ he
  have hrev : Continuous fun s : ℝ => τ - s := continuous_const.sub continuous_id
  -- the response data of `q + q(τ - ·)`
  have hA := ResponseData.add hτ.le (hpc.comp hrev) hpc hv₁ hv₂
  have hB := ResponseData.add hτ.le (hnc.comp hrev) hnc hv₃ hv₄
  have hg : Continuous fun s => q s + q (τ - s) := hqc.add (hqc.comp hrev)
  have hgB : Continuous fun s => negPart q (τ - s) + negPart q s := (hnc.comp hrev).add hnc
  have hA' : ResponseData (transportD0 b E) τ
      (fun s => (q s + q (τ - s)) + (negPart q (τ - s) + negPart q s)) x y (v₁ + v₂) :=
    hA.congr (funext fun s => by
      have h1 := posPart_sub_negPart q s
      have h2 := posPart_sub_negPart q (τ - s)
      show posPart q (τ - s) + posPart q s = (q s + q (τ - s)) + (negPart q (τ - s) + negPart q s)
      linarith)
  have hR := ResponseData.sub hτ.le hg hgB hA' hB
  refine ⟨v₁ + v₂ - (v₃ + v₄), hR, ?_⟩
  -- the limit
  have hlim := (hl₁.add hl₂).sub (hl₃.add hl₄)
  rw [show -(4 * Real.pi * Parameters.semicircleDensity E) * v₁ +
      -(4 * Real.pi * Parameters.semicircleDensity E) * v₂ -
      (-(4 * Real.pi * Parameters.semicircleDensity E) * v₃ +
        -(4 * Real.pi * Parameters.semicircleDensity E) * v₄) =
      -(4 * Real.pi * Parameters.semicircleDensity E) * (v₁ + v₂ - (v₃ + v₄)) by ring] at hlim
  refine hlim.congr' ?_
  obtain ⟨C₀, W₀, -, hC₀⟩ := portPass_uniform hUnifMom hInvU hb0 hb1 hE1 hE2 hx hy0 hy1 hτ hj
    hp0 hpQ he 0
  obtain ⟨C₁, W₁, -, hC₁⟩ := portPass_uniform hUnifMom hInvU hb0 hb1 hE1 hE2 hx hy0 hy1 hτ hj
    hp0 hpQ he 1
  obtain ⟨C₂, W₂, -, hC₂⟩ := portPass_uniform hUnifMom hInvU hb0 hb1 hE1 hE2 hx hy0 hy1 hτ hj
    hn0 hnQ he 0
  obtain ⟨C₃, W₃, -, hC₃⟩ := portPass_uniform hUnifMom hInvU hb0 hb1 hE1 hE2 hx hy0 hy1 hτ hj
    hn0 hnQ he 1
  filter_upwards [eventually_ge_atTop (max (max W₀ W₁) (max W₂ W₃))] with W hW
  have a0 := hC₀ W (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW)
  have a1 := hC₁ W (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW)
  have a2 := hC₂ W (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hW)
  have a3 := hC₃ W (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hW)
  have hb' : b ≤ 1 := by linarith
  simp only [signedPassDerivative]
  rw [integral_derivWithin_eq hb' a0.1.1 a0.1.2 hx hy0 hy1 hp0 a0.2.1 a0.2.2.1 a1.2.2.1,
    integral_derivWithin_eq hb' a0.1.1 a0.1.2 hx hy0 hy1 hn0 a0.2.1 a2.2.2.1 a3.2.2.1]

/-!
### The unfolded window is a moving energy
-/

theorem unfolded_isMoving {E τ U : ℝ} (hE1 : -2 < E) (hE2 : E < 2) (hτ : 0 < τ) {j : ℕ → ℕ}
    (hj : Tendsto (fun W : ℕ => (j W : ℝ) / W) atTop (𝓝 τ)) :
    ∃ Ce : ℝ, ∀ u : ℕ → ℝ, (∀ W, |u W| ≤ U) →
      IsMovingEnergy E Ce (fun W => unfoldedEnergy E W (j W) (u W)) := by
  have hρ := semicircleDensity_pos' hE1 hE2
  set ρ := Parameters.semicircleDensity E
  obtain ⟨W₁, hW₁⟩ := eventually_atTop.1 (hj.eventually (lt_mem_nhds (by linarith : τ / 2 < τ)))
  set U' := max U 0
  refine ⟨max (2 * U' / (τ * ρ)) (U' * W₁ / ρ), fun u hu W hW => ?_⟩
  have hU' : 0 ≤ U' := le_max_right _ _
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  unfold IsNearEnergy unfoldedEnergy
  rw [add_sub_cancel_left, abs_div]
  have huU : |u W| ≤ U' := (hu W).trans (le_max_left _ _)
  rcases Nat.eq_zero_or_pos (j W) with hj0 | hj0
  · rw [hj0]; simp only [Nat.cast_zero, zero_mul, abs_zero, div_zero]
    have : 0 ≤ max (2 * U' / (τ * ρ)) (U' * W₁ / ρ) :=
      le_trans (by positivity) (le_max_right _ _)
    positivity
  · have hjr : (1 : ℝ) ≤ j W := by exact_mod_cast hj0
    have hden : 0 < ((j W : ℝ) * W) * ρ := by positivity
    rw [abs_of_pos hden, div_le_div_iff₀ hden (by positivity)]
    by_cases hWW : W₁ ≤ W
    · have hjW := hW₁ W hWW
      rw [lt_div_iff₀ hWr] at hjW
      have h1 : |u W| * (W : ℝ) ^ 2 ≤ U' * W ^ 2 :=
        mul_le_mul_of_nonneg_right huU (by positivity)
      have h2 : U' * (W : ℝ) ^ 2 ≤ 2 * U' / (τ * ρ) * ((j W * W) * ρ) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        have : τ / 2 * W * W ≤ j W * W := mul_le_mul_of_nonneg_right hjW.le hWr.le
        nlinarith [mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ 2 * U' * ρ)]
      calc |u W| * (W : ℝ) ^ 2 ≤ 2 * U' / (τ * ρ) * ((j W * W) * ρ) := h1.trans h2
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hden.le
    · have hWlt : (W : ℝ) ≤ W₁ := by exact_mod_cast (le_of_lt (not_le.1 hWW))
      have h1 : |u W| * (W : ℝ) ^ 2 ≤ U' * W ^ 2 :=
        mul_le_mul_of_nonneg_right huU (by positivity)
      have h2 : U' * (W : ℝ) ^ 2 ≤ U' * W₁ / ρ * ((j W * W) * ρ) := by
        have e : U' * W₁ / ρ * ((j W * W) * ρ) = U' * (W₁ * (j W * W)) := by
          field_simp
        rw [e]
        have hW1 : (0 : ℝ) ≤ W₁ := Nat.cast_nonneg _
        have : (W : ℝ) * W ≤ W₁ * (j W * W) :=
          (mul_le_mul_of_nonneg_right hWlt hWr.le).trans
            (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hWr.le hjr) hW1)
        rw [sq]
        exact mul_le_mul_of_nonneg_left this hU'
      calc |u W| * (W : ℝ) ^ 2 ≤ U' * W₁ / ρ * ((j W * W) * ρ) := h1.trans h2
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hden.le

/-!
### The corner
-/

theorem ratioDet_zero_zero {n : Type*} [Fintype n] [DecidableEq n] (T : Matrix n n ℂ) :
    ratioDet 0 0 T = 1 := by
  simp [ratioDet, ratioDetC]

theorem signedPassDerivative_corner (b E : ℝ) (W n : ℕ) (q : ℝ → ℝ) :
    signedPassDerivative b E 0 0 W n q = 0 := by
  have h : ∀ (r : ℝ → ℝ) (ω : GrowthPath W),
      (fun κ => portRatioSum b E 0 0 W n r κ ω) = fun _ => 2 := by
    intro r ω
    funext κ
    simp only [portRatioSum, ratioDet_zero_zero]
    norm_num
  simp only [signedPassDerivative, h]
  exact sub_self _

/-!
### Clause 2
-/

/-- Clause 2 of the pass-derivative lemma; see the module docstring for the formal reading. -/
theorem passDerivative_clause2 (hUnifLaw : TransmissionLawEnergyUniformContract)
    (hUnifMom : FullSourceMomentsEnergyUniformContract) (hBdry : DualBoundaryStartContract)
    (hInvU : PathFractionalInverseEnergyUniform) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ τ : ℝ, 0 < τ → ∀ j : ℕ → ℕ, Tendsto (fun W : ℕ => (j W : ℝ) / W) atTop (𝓝 τ) →
    ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → y < 1 →
    ∀ q : ℝ → ℝ, Continuous q → (∃ Q : ℝ, ∀ t, |q t| ≤ Q) →
    ∃ v : ℝ, IsSignedResponse (transportD0 b E) τ (fun s => q s + q (τ - s)) x y v ∧
      ∀ U : ℝ, ∀ ε : ℝ, 0 < ε → ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ u ∈ Icc (-U) U,
        |signedPassDerivative b (unfoldedEnergy E W (j W) u) x y W (j W) q +
          4 * Real.pi * Parameters.semicircleDensity E * v| ≤ ε := by
  intro b hb0 hb1 E hE1 hE2 τ hτ j hj x y hx hy0 hy1 q hqc hqb
  obtain ⟨Q, hqQ⟩ := hqb
  by_cases hxy : x = 0 ∧ y = 0
  · -- the corner `(0, 0)`: `F_{0,0} ≡ 1`
    obtain ⟨rfl, rfl⟩ := hxy
    refine ⟨0, Or.inl ⟨rfl, rfl, rfl⟩, fun U ε hε => ⟨0, fun W _ u _ => ?_⟩⟩
    rw [signedPassDerivative_corner, mul_zero, add_zero, abs_zero]
    exact hε.le
  have hD0 := transportD0_pos hb0 hE1 hE2
  have hex := hBdry.exists_ _ hD0 x y (isDualStart_one hx hy0 hy1.le hxy)
  obtain ⟨v, hv, -⟩ := signed_tendsto hUnifLaw hUnifMom hBdry hInvU hb0 hb1 hE1 hE2 hx hy0 hy1
    hxy hτ hj hqc hqQ (isMovingEnergy_const E)
  refine ⟨v, Or.inr ⟨hxy, hex, hv.value⟩, fun U ε hε => ?_⟩
  by_contra hcon
  push Not at hcon
  -- a bad energy sequence
  classical
  set bad : ℕ → Prop := fun W => ∃ u ∈ Icc (-U) U,
    ε < |signedPassDerivative b (unfoldedEnergy E W (j W) u) x y W (j W) q +
      4 * Real.pi * Parameters.semicircleDensity E * v|
  have hfreq : ∃ᶠ W in atTop, bad W := by
    rw [frequently_atTop]
    intro W₀
    obtain ⟨W, hW, u, hu, h⟩ := hcon W₀
    exact ⟨W, hW, u, hu, h⟩
  set uW : ℕ → ℝ := fun W => if h : bad W then h.choose else 0
  have huW : ∀ W, |uW W| ≤ max U 0 := by
    intro W
    simp only [uW]
    split_ifs with h
    · have hm := h.choose_spec.1
      rw [abs_le]
      constructor <;> linarith [hm.1, hm.2, le_max_left U 0]
    · simp
  obtain ⟨Ce, hCe⟩ := unfolded_isMoving (U := max U 0) hE1 hE2 hτ hj
  have he := hCe uW huW
  obtain ⟨v', hv', hlim⟩ := signed_tendsto hUnifLaw hUnifMom hBdry hInvU hb0 hb1 hE1 hE2 hx hy0
    hy1 hxy hτ hj hqc hqQ he
  have hvv : v' = v := ResponseData.unique hex hv' hv
  rw [hvv] at hlim
  have hev : ∀ᶠ W in atTop, |signedPassDerivative b (unfoldedEnergy E W (j W) (uW W)) x y W (j W) q +
      4 * Real.pi * Parameters.semicircleDensity E * v| < ε := by
    have := Metric.tendsto_nhds.1 hlim ε hε
    filter_upwards [this] with W hW
    rw [Real.dist_eq] at hW
    have e : signedPassDerivative b (unfoldedEnergy E W (j W) (uW W)) x y W (j W) q +
        4 * Real.pi * Parameters.semicircleDensity E * v =
        signedPassDerivative b (unfoldedEnergy E W (j W) (uW W)) x y W (j W) q -
          -(4 * Real.pi * Parameters.semicircleDensity E) * v := by ring
    rw [e]; exact hW
  obtain ⟨W, hWb, hWe⟩ := (hfreq.and_eventually hev).exists
  have hspec := hWb.choose_spec.2
  have : uW W = hWb.choose := by simp only [uW, dite_pos' hWb]
  rw [this] at hWe
  linarith

end BlockBand.Endpoints
