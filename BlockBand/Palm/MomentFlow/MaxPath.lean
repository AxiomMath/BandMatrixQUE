module

public import BlockBand.Palm.MomentFlow.MaxShell
public import BlockBand.Palm.MomentFlow.MaxDamp

/-!
# Along one eigenvalue path: averaged identity, damped maximum principle and target comparison

Hypotheses along the path:

* the removal identity (`removal_average_uniform`), at all heights: `|remSum Φ - V Ψ| ≤ eR + ρ`;
* the averaged law at all heights: `|Σ_j K_ij - V| ≤ E₂`;
* the long kernel bound `longKer ≤ E₃`;
* the induction hypothesis `|Ψ(ξ - δ_i) - 1| ≤ E₄ + ρ` (`CM(r-1)`);
* the ramp/count bound `|a_{ξ^{ij}} - a_ξ| ≤ min(1, β(|λ_j - λ_i| + η))`;

**`maxPath`**: at every `σ ∈ [s,b]` and every `ξ₀` with `a_{ξ₀} = 1`,
`|Φ(σ, ξ₀) - 1| ≤ Main + ρ(σ) + G e^{-(rv/η)(σ-s)} + e/(rv/η) + ∫_s^σ C ρ`, with explicit
`e` and `C` (`maxPathErr`, `maxPathCoef`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Set Finset MeasureTheory BlockBand.Internal.Contracts.CoareaPalm

variable {N : ℕ}

/-- Shell factor `16βη(L+1) + 2η/(2^Lη)`. -/
def shellFac (β η : ℝ) (L : ℕ) : ℝ := 16 * β * η * (L + 1) + 2 * η / (2 ^ L * η)

/-- Constant part of the error in the averaged identity. -/
def r3Const (N r : ℕ) (η β Vb E₂ E₄ eR Main : ℝ) (L : ℕ) : ℝ :=
  eR + (E₂ + r * ((N : ℝ) * η)⁻¹) +
    shellFac β η L * ((Vb + 1) * (1 + E₄) + eR + (Vb + E₂ + r * ((N : ℝ) * η)⁻¹)) +
    (Vb + E₂ + r * ((N : ℝ) * η)⁻¹) * Main

/-- Coefficient of `ρ` in the error of the averaged identity. -/
def r3Coef (N r : ℕ) (η β Vb E₂ : ℝ) (L : ℕ) : ℝ :=
  1 + shellFac β η L * (Vb + 2) + (Vb + E₂ + r * ((N : ℝ) * η)⁻¹)

/-- The constant error `e` of the damped principle. -/
def maxPathErr (N r : ℕ) (η β G Vb E₂ E₃ E₄ eR Main : ℝ) (L : ℕ) : ℝ :=
  (r : ℝ) / η * (r3Const N r η β Vb E₂ E₄ eR Main L + Vb * E₄ + G * E₂ +
    r * ((N : ℝ) * η)⁻¹ + ((r : ℝ) + 1) * G * E₃)

/-- The coefficient of `ρ` inside the time integral. -/
def maxPathCoef (N r : ℕ) (η β v Vb E₂ : ℝ) (L : ℕ) : ℝ :=
  ((r : ℝ) * (1 + Vb) / η + (r : ℝ) * v / η) * r3Coef N r η β Vb E₂ L

theorem shellFac_nonneg {β η : ℝ} (hβ : 0 ≤ β) (hη : 0 < η) (L : ℕ) : 0 ≤ shellFac β η L := by
  unfold shellFac; positivity

/-- **Damped maximum principle along one path**, with the averaged identity and the target
comparison. -/
theorem maxPath {r ℓ L : ℕ} (hr : 1 ≤ r) {c : ℝ → Fin N → Fin N → ℝ} {lam : ℝ → Fin N → ℝ}
    {s b η G v Vb E₂ E₃ E₄ eR Main β : ℝ} (hsb : s ≤ b) (hη : 0 < η) (hv : 0 < v)
    (hvVb : v ≤ Vb) (hG1 : 1 ≤ G) (hE₂ : 0 ≤ E₂) (hE₃ : 0 ≤ E₃) (hE₄ : 0 ≤ E₄) (heR : 0 ≤ eR)
    (hMain : 0 ≤ Main) (hβ : 0 ≤ β)
    (hc0 : ∀ u ∈ Ioo s b, ∀ i j, i ≠ j → 0 ≤ c u i j)
    (hcK : ∀ u ∈ Ioo s b, ∀ i j, i ≠ j → labelDist i j < ℓ → kerAt (lam u) η i j ≤ η * c u i j)
    (hcl : ∀ u ∈ Ioo s b, ∀ i j, i ≠ j → ℓ ≤ labelDist i j → c u i j = 0)
    {g Φ Ψ : ℝ → Occ N → ℝ} (hg : IsMomentFlowSolution c r s b g)
    (hg0 : ∀ ξ ∈ sector N r, 0 ≤ g s ξ) (hgG : ∀ ξ ∈ sector N r, g s ξ ≤ G)
    (hΦ0 : ∀ u ∈ Ioo s b, ∀ ξ ∈ sector N r, 0 ≤ Φ u ξ)
    {ρ : ℝ → ℝ} (hρc : ContinuousOn ρ (Icc s b)) (hρ0 : ∀ u ∈ Icc s b, 0 ≤ ρ u)
    (P : Occ N → Prop) (aR : Occ N → ℝ) (haR : ∀ ξ, 0 ≤ aR ξ ∧ aR ξ ≤ 1)
    (V : ℝ → ℝ → Fin N → ℝ)
    (hV : ∀ u ∈ Ioo s b, ∀ ξ ∈ sector N r, P ξ → ∀ i, 0 < ξ i →
      v ≤ V η u i ∧ V η u i ≤ Vb ∧ ∀ k ≤ L, 0 ≤ V (2 ^ k * η) u i ∧ V (2 ^ k * η) u i ≤ Vb)
    (hR2 : ∀ u ∈ Ioo s b, ∀ ξ ∈ sector N r, P ξ → ∀ i, 0 < ξ i →
      |remSum (kerAt (lam u) η) (Φ u) ξ i - V η u i * Ψ u (remove ξ i)| ≤ eR + ρ u ∧
      ∀ k ≤ L, |remSum (kerAt (lam u) (2 ^ k * η)) (Φ u) ξ i -
        V (2 ^ k * η) u i * Ψ u (remove ξ i)| ≤ eR + ρ u)
    (hAv : ∀ u ∈ Ioo s b, ∀ ξ ∈ sector N r, P ξ → ∀ i, 0 < ξ i →
      |∑ j, kerAt (lam u) η i j - V η u i| ≤ E₂ ∧
      ∀ k ≤ L, |∑ j, kerAt (lam u) (2 ^ k * η) i j - V (2 ^ k * η) u i| ≤ E₂)
    (hL : ∀ u ∈ Ioo s b, ∀ ξ ∈ sector N r, P ξ → ∀ i, 0 < ξ i →
      longKer (kerAt (lam u) η) ℓ i ≤ E₃)
    (hIH : ∀ u ∈ Ioo s b, ∀ ξ ∈ sector N r, P ξ → ∀ i, 0 < ξ i →
      |Ψ u (remove ξ i) - 1| ≤ E₄ + ρ u)
    (hlip : ∀ u ∈ Ioo s b, ∀ ξ ∈ sector N r, P ξ → ∀ i, 0 < ξ i → ∀ j,
      |aR (remTarget ξ i j) - aR ξ| ≤ min 1 (β * (|lam u j - lam u i| + η)))
    (hdev : ∀ u ∈ Icc s b, ∀ ζ ∈ sector N r, |g u ζ - avFlat aR (Φ u) ζ| ≤ Main + ρ u)
    (hext : ∀ u ∈ Ioo s b, ∀ ξ ∈ sector N r, ¬ P ξ → |g u ξ - 1| ≤ ρ u) :
    ∀ σ ∈ Icc s b, ∀ ξ₀ ∈ sector N r, aR ξ₀ = 1 →
      |Φ σ ξ₀ - 1| ≤ Main + ρ σ + G * Real.exp (-((r : ℝ) * v / η) * (σ - s)) +
        maxPathErr N r η β G Vb E₂ E₃ E₄ eR Main L / ((r : ℝ) * v / η) +
        ∫ t in s..σ, maxPathCoef N r η β v Vb E₂ L * ρ t := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  set Kmax : ℝ := ((N : ℝ) * η)⁻¹ with hKmax
  have hKm0 : 0 ≤ Kmax := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · simp [hKmax, h0]
    · have : (0 : ℝ) < N := by exact_mod_cast h0
      positivity
  have hSh := shellFac_nonneg hβ hη L
  set c₁ := r3Coef N r η β Vb E₂ L with hc₁
  have hVb0 : 0 ≤ Vb := hv.le.trans hvVb
  have hc₁1 : 1 ≤ c₁ := by
    simp only [hc₁, r3Coef]
    have : 0 ≤ shellFac β η L * (Vb + 2) := mul_nonneg hSh (by linarith)
    have : 0 ≤ (r : ℝ) * ((N : ℝ) * η)⁻¹ := mul_nonneg hr0.le hKm0
    linarith
  set ρ' : ℝ → ℝ := fun u => c₁ * ρ u with hρ'
  have hρ'c : ContinuousOn ρ' (Icc s b) := continuousOn_const.mul hρc
  have hρ'0 : ∀ u ∈ Icc s b, 0 ≤ ρ' u := fun u hu => mul_nonneg (by linarith) (hρ0 u hu)
  have hρρ' : ∀ u ∈ Icc s b, ρ u ≤ ρ' u := fun u hu => by
    simp only [hρ']; nlinarith [hρ0 u hu]
  have hρ'i : IntervalIntegrable ρ' volume s b := hρ'c.intervalIntegrable_of_Icc hsb
  have hρ'l : ∀ u ∈ Ioo s b, LowerSemicontinuousAt ρ' u := fun u hu =>
    (hρ'c.continuousAt (Icc_mem_nhds hu.1 hu.2)).lowerSemicontinuousAt
  set E₁ := r3Const N r η β Vb E₂ E₄ eR Main L with hE₁
  have hE₁0 : 0 ≤ E₁ := by
    simp only [hE₁, r3Const]
    have : 0 ≤ (r : ℝ) * ((N : ℝ) * η)⁻¹ := mul_nonneg hr0.le hKm0
    have : 0 ≤ (Vb + 1) * (1 + E₄) + eR + (Vb + E₂ + r * ((N : ℝ) * η)⁻¹) := by positivity
    have : 0 ≤ (Vb + E₂ + r * ((N : ℝ) * η)⁻¹) * Main := by positivity
    positivity
  -- the averaged identity at every interior time and window configuration
  have hR3 : ∀ u ∈ Ioo s b, ∀ ξ ∈ sector N r, P ξ → ∀ i, 0 < ξ i →
      |remSum (kerAt (lam u) η) (g u) ξ i - V η u i * (aR ξ * Ψ u (remove ξ i) + (1 - aR ξ))| ≤
        E₁ + ρ' u := by
    intro u hu ξ hξ hP i hi
    have hu' := Ioo_subset_Icc_self hu
    obtain ⟨hv1, hv2, hvk⟩ := hV u hu ξ hξ hP i hi
    obtain ⟨hR2a, hR2k⟩ := hR2 u hu ξ hξ hP i hi
    obtain ⟨hAva, hAvk⟩ := hAv u hu ξ hξ hP i hi
    have hIHu := hIH u hu ξ hξ hP i hi
    set Ψi := Ψ u (remove ξ i)
    have hΨ : Ψi ≤ 1 + E₄ + ρ u := by have := (abs_le.1 hIHu).2; linarith
    set BF := Vb * (1 + E₄ + ρ u) + eR + ρ u
    set B1 := Vb + E₂ + r * Kmax
    have hBF : ∀ k ≤ L, remSum (kerAt (lam u) (2 ^ k * η)) (Φ u) ξ i ≤ BF := by
      intro k hk
      have h1 := (abs_le.1 (hR2k k hk)).2
      obtain ⟨hV0, hVb'⟩ := hvk k hk
      have h2 : V (2 ^ k * η) u i * Ψi ≤ Vb * (1 + E₄ + ρ u) := by
        rcases le_or_gt 0 Ψi with hp | hn
        · calc V (2 ^ k * η) u i * Ψi ≤ Vb * Ψi := mul_le_mul_of_nonneg_right hVb' hp
            _ ≤ Vb * (1 + E₄ + ρ u) := mul_le_mul_of_nonneg_left hΨ hVb0
        · have : V (2 ^ k * η) u i * Ψi ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hV0 hn.le
          have : 0 ≤ Vb * (1 + E₄ + ρ u) := mul_nonneg hVb0 (by linarith [hρ0 u hu'])
          linarith
      simp only [BF]; linarith
    have hB1 : ∀ k ≤ L, remSum (kerAt (lam u) (2 ^ k * η)) (fun _ => 1) ξ i ≤ B1 := by
      intro k hk
      have hh : 0 < 2 ^ k * η := by positivity
      have h1 := remSum_one_sub_le hξ (fun i j => kerAt_nonneg (lam u) hh.le i j)
        (fun i j => kerAt_le (lam u) hh i j) hi
      have h2 := (abs_le.1 (hAvk k hk)).2
      have h3 : ((N : ℝ) * (2 ^ k * η))⁻¹ ≤ Kmax := by
        rcases Nat.eq_zero_or_pos N with h0 | h0
        · simp [hKmax, h0]
        · have hN : (0 : ℝ) < N := by exact_mod_cast h0
          apply inv_anti₀ (by positivity)
          have : η ≤ 2 ^ k * η := le_mul_of_one_le_left hη.le (one_le_pow₀ (by norm_num))
          nlinarith
      have h4 := (abs_le.1 h1).2
      have h5 : (r : ℝ) * ((N : ℝ) * (2 ^ k * η))⁻¹ ≤ r * Kmax :=
        mul_le_mul_of_nonneg_left h3 hr0.le
      simp only [B1]
      linarith [(hvk k hk).2]
    have hF0 : ∀ j, 0 ≤ Φ u (remTarget ξ i j) := fun j =>
      hΦ0 u hu _ (remTarget_mem_sector hξ hi j)
    have hgd : ∀ j, |g u (remTarget ξ i j) - avFlat aR (Φ u) (remTarget ξ i j)| ≤ Main + ρ u :=
      fun j => hdev u hu' _ (remTarget_mem_sector hξ hi j)
    have h := r3_bound hξ hi (lam u) (BF := BF) (B1 := B1) hη hβ L aR (Φ u) (g u) (haR ξ) hF0
      (hlip u hu ξ hξ hP i hi) hBF hB1 hR2a hAva hgd
    refine h.trans ?_
    have hρu := hρ0 u hu'
    have hrK : 0 ≤ (r : ℝ) * Kmax := mul_nonneg hr0.le hKm0
    -- collect the terms
    have hsum : BF + B1 = ((Vb + 1) * (1 + E₄) + eR + (Vb + E₂ + r * Kmax)) +
        (Vb + 1) * ρ u - (1 + E₄) := by simp only [BF, B1]; ring
    have hVi : V η u i + E₂ + r * Kmax ≤ Vb + E₂ + r * Kmax := by linarith
    have hX : 0 ≤ Main + ρ u := by linarith
    calc eR + ρ u + (E₂ + r * Kmax) + shellFac β η L * (BF + B1) +
          (V η u i + E₂ + r * Kmax) * (Main + ρ u)
        ≤ eR + ρ u + (E₂ + r * Kmax) +
          shellFac β η L * (((Vb + 1) * (1 + E₄) + eR + (Vb + E₂ + r * Kmax)) + (Vb + 2) * ρ u) +
          (Vb + E₂ + r * Kmax) * (Main + ρ u) := by
          have e1 : BF + B1 ≤ ((Vb + 1) * (1 + E₄) + eR + (Vb + E₂ + r * Kmax)) +
              (Vb + 2) * ρ u := by rw [hsum]; nlinarith
          have := mul_le_mul_of_nonneg_left e1 hSh
          have := mul_le_mul_of_nonneg_right hVi hX
          unfold shellFac at *
          linarith
      _ = E₁ + ρ' u := by
          simp only [hE₁, r3Const, hρ', hc₁, r3Coef, hKmax]
          ring
  have hfd := flattened_damped hr (c := c) (K := fun u => kerAt (lam u) η) hsb hη hv hKm0 hG1
    hE₁0 hE₂ hE₃ hE₄ hc0 (fun u _ i j => kerAt_nonneg (lam u) hη.le i j)
    (fun u _ i j => kerAt_le (lam u) hη i j) hcK hcl hg hg0 hgG hρ'i hρ'l hρ'0 (fun _ ξ => P ξ) aR haR
    (fun u ξ i => V η u i) (fun u ξ i => Ψ u (remove ξ i)) hR3
    (fun u hu ξ hξ hP i hi => (hAv u hu ξ hξ hP i hi).1) hL
    (fun u hu ξ hξ hP i hi => (hIH u hu ξ hξ hP i hi).trans
      (by linarith [hρρ' u (Ioo_subset_Icc_self hu)])) hvVb
    (fun u hu ξ hξ hP i hi => ⟨(hV u hu ξ hξ hP i hi).1, (hV u hu ξ hξ hP i hi).2.1⟩)
    (fun u hu ξ hξ hP => (hext u hu ξ hξ hP).trans (hρρ' u (Ioo_subset_Icc_self hu)))
  intro σ hσ ξ₀ hξ₀ ha1
  have h1 := hfd σ hσ ξ₀ hξ₀
  have h2 := hdev σ hσ ξ₀ hξ₀
  have hav : avFlat aR (Φ σ) ξ₀ = Φ σ ξ₀ := by simp [avFlat, ha1]
  rw [hav] at h2
  have hint : (∫ t in s..σ, ((r : ℝ) * (1 + Vb) / η + (r : ℝ) * v / η) * ρ' t) =
      ∫ t in s..σ, maxPathCoef N r η β v Vb E₂ L * ρ t := by
    congr 1; funext t; simp only [hρ', maxPathCoef, hc₁]; ring
  have herr : ((r : ℝ) / η * (E₁ + Vb * E₄ + G * E₂ + r * Kmax + ((r : ℝ) + 1) * G * E₃)) =
      maxPathErr N r η β G Vb E₂ E₃ E₄ eR Main L := by
    simp only [maxPathErr, hE₁, hKmax]
  rw [hint, herr] at h1
  calc |Φ σ ξ₀ - 1| ≤ |Φ σ ξ₀ - g σ ξ₀| + |g σ ξ₀ - 1| := by
        have := abs_sub_le (Φ σ ξ₀) (g σ ξ₀) 1; linarith
    _ ≤ (Main + ρ σ) + (G * Real.exp (-((r : ℝ) * v / η) * (σ - s)) +
        maxPathErr N r η β G Vb E₂ E₃ E₄ eR Main L / ((r : ℝ) * v / η) +
        ∫ t in s..σ, maxPathCoef N r η β v Vb E₂ L * ρ t) := by
        rw [abs_sub_comm] at h2
        gcongr
    _ = _ := by ring

end BlockBand.Palm.MomentFlow
