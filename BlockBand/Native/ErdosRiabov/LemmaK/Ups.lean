module

public import BlockBand.Native.ErdosRiabov.LemmaK.Clauses
public import BlockBand.Native.ErdosRiabov.Flow.Anchor
public import BlockBand.Native.ErdosRiabov.Flow.Const

/-!
# Control inequalities at VS heights

The properties (U1)–(U11) of the polynomial control `Υ` along the VS heights (the control
lemma). Constants are those of `VSData` `d`: `C₁'' = d.C1pp`, `D'' = d.Dpp`,
`C_wc = d.Cwc = (C₁'')^{3/2}`; the bridges `lemmaKC1_eq_C1pp`, `lemmaKCeiling_eq_C0pp`,
`lemmaKDPrime_eq_Dpp` identify them with the constants of the kernel lemma (all `rfl`).

Setting: `S = shortRingProfile d.b m W`, `m ≥ 4`, `W ≥ 1`, `N = mW`, `Υ_h = polynomialControl N W
d.D h`, `z ∈ 𝒟 = BulkDomain N d.δ₀ d.κ d.C₀`, `η_r = vsHeight z r`, `0 ≤ s ≤ t ≤ 1` (so
`η_t ≤ η_s`, both in `[N^{-1+δ₀}, C₀+1]`). `ups_U2_U8_vs` gives (U2) at `η_t`, (U3) with constant
`1`, the reverse comparison (U1b), (U4), (U5) with `C_wc`, (U6) with `C_wc`, (U7) with `C₁''`
(from the `√`-convolution of (U4) and `ℓ_s ≤ N`), (U8) for `r ∈ {s, t}`, and for `η_t ≤ (W/N)²`,
in particular for `t♭ < t` (`t♭ = anchorTime z N W`): `Υ_t ≥ (C₁'')⁻¹(Nη_t)⁻¹` and
`Υ_t ≥ ((3/2)^D)⁻¹(Nη_t)⁻¹`. The remaining items are
(U1) = `lemmaK_K1`, (U9) = `lemmaK_K4`, (U10) = `lemmaK_K2`, (U11) = `lemmaK_K3`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.LemmaK

open BlockBand.External BlockBand.Internal.Contracts.Inputs BlockBand.Adapters.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel BlockBand.Native.ErdosRiabov.Flow
open scoped BigOperators

/-!
## Bridges to the `VSData` constants
-/

/-- `C₁''`: the local `lemmaKC1` is `VSData.C1pp`. -/
theorem lemmaKC1_eq_C1pp (d : VSData) :
    lemmaKC1 d.b d.b_pos d.b_lt_half d.kappa d.C0 d.D = d.C1pp := rfl

/-- `C₀''`: the local `lemmaKCeiling` is `VSData.C0pp`. -/
theorem lemmaKCeiling_eq_C0pp (d : VSData) : lemmaKCeiling d.C0 = d.C0pp := rfl

/-- `D''`: the local `lemmaKDPrime` is `VSData.Dpp`. -/
theorem lemmaKDPrime_eq_Dpp (d : VSData) : lemmaKDPrime d.C0 d.D = d.Dpp := rfl

/-!
## The derived inequalities for an admissible control
-/

private theorem lemmaK_rpow_three_halves {C : ℝ} (hC : 0 < C) :
    C ^ (3 / 2 : ℝ) = C * Real.sqrt C := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hC, Real.rpow_one,
    Real.sqrt_eq_rpow]

/-- (U5)–(U7) from clause (iv) of an admissible control at heights `h₁ ≤ h₂`. -/
private theorem lemmaK_ups_derived {N W : ℕ} (hN : 0 < N) (hW : 0 < W)
    {q : ErdosRiabov.ModelParameters} {S : Matrix (Fin N) (Fin N) ℝ}
    {Υ : ℝ → Matrix (Fin N) (Fin N) ℝ} (hadm : ErdosRiabov.AdmissibleControl q N W S Υ)
    {h₁ h₂ : ℝ} (c1 : ErdosRiabov.ControlHeight q N h₁) (c2 : ErdosRiabov.ControlHeight q N h₂)
    (h12 : h₁ ≤ h₂) :
    (∀ x y, ∑ a, Υ h₂ x a * Υ h₁ a y ≤ q.C1 ^ (3 / 2 : ℝ) / h₂ * Υ h₁ x y) ∧
    (∀ x₁ x₂ y₁ y₂, ∑ a, Real.sqrt (Υ h₂ x₁ a * Υ h₂ x₂ a * Υ h₁ a y₁ * Υ h₁ a y₂) ≤
      q.C1 ^ (3 / 2 : ℝ) / h₂ * Real.sqrt (Υ h₁ x₁ y₁ * Υ h₁ x₂ y₂)) ∧
    (∀ x y, ∑ a, Real.sqrt (Υ h₂ x a * Υ h₁ a y) ≤
      q.C1 / h₂ * Real.sqrt ((N : ℝ) * h₂) * Real.sqrt (Υ h₁ x y)) := by
  have hh2 : 0 < h₂ := lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast hN) _) c2.1
  have hC : 0 < q.C1 := lt_of_lt_of_le one_pos q.C1_ge_one
  have hU1 : ∀ x y, 0 ≤ Υ h₁ x y := fun x y => (hadm.entrywisePositive h₁ c1 x y).le
  have hU2 : ∀ x y, 0 ≤ Υ h₂ x y := fun x y => (hadm.entrywisePositive h₂ c2 x y).le
  have hl := loc_pos hN hW hh2
  have hL : 0 < ErdosRiabov.localizationLength N W h₂ * h₂ := mul_pos hl hh2
  have h5 : ∀ x y, ∑ a, Υ h₂ x a * Υ h₁ a y ≤ q.C1 ^ (3 / 2 : ℝ) / h₂ * Υ h₁ x y := by
    intro x y
    obtain ⟨hpt, hsq⟩ := hadm.clause4 h₁ h₂ c1 c2 h12 x y
    set C := q.C1 with hCdef
    set L := ErdosRiabov.localizationLength N W h₂ * h₂ with hLdef
    set M := Real.sqrt (C / L * Υ h₁ x y) with hMdef
    have hf : ∀ a, Υ h₂ x a * Υ h₁ a y =
        Real.sqrt (Υ h₂ x a * Υ h₁ a y) * Real.sqrt (Υ h₂ x a * Υ h₁ a y) := fun a =>
      (Real.mul_self_sqrt (mul_nonneg (hU2 x a) (hU1 a y))).symm
    have hfM : ∀ a, Real.sqrt (Υ h₂ x a * Υ h₁ a y) ≤ M := fun a => Real.sqrt_le_sqrt (hpt a)
    have hM0 : 0 ≤ M := Real.sqrt_nonneg _
    have hprod : C / L * Υ h₁ x y * (L * Υ h₁ x y) = C * Υ h₁ x y ^ 2 := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff hL.ne']
      ring
    have hMeq : M * Real.sqrt (L * Υ h₁ x y) = Real.sqrt C * Υ h₁ x y := by
      rw [hMdef, ← Real.sqrt_mul (mul_nonneg (div_nonneg hC.le hL.le) (hU1 x y)), hprod,
        Real.sqrt_mul hC.le, Real.sqrt_sq (hU1 x y)]
    calc ∑ a, Υ h₂ x a * Υ h₁ a y
        = ∑ a, Real.sqrt (Υ h₂ x a * Υ h₁ a y) * Real.sqrt (Υ h₂ x a * Υ h₁ a y) :=
          Finset.sum_congr rfl fun a _ => hf a
      _ ≤ ∑ a, M * Real.sqrt (Υ h₂ x a * Υ h₁ a y) :=
          Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_right (hfM a) (Real.sqrt_nonneg _)
      _ = M * ∑ a, Real.sqrt (Υ h₂ x a * Υ h₁ a y) := (Finset.mul_sum _ _ _).symm
      _ ≤ M * (C / h₂ * Real.sqrt (L * Υ h₁ x y)) := mul_le_mul_of_nonneg_left hsq hM0
      _ = C / h₂ * (M * Real.sqrt (L * Υ h₁ x y)) := by ring
      _ = C / h₂ * (Real.sqrt C * Υ h₁ x y) := by rw [hMeq]
      _ = C ^ (3 / 2 : ℝ) / h₂ * Υ h₁ x y := by rw [lemmaK_rpow_three_halves hC]; ring
  refine ⟨h5, fun x₁ x₂ y₁ y₂ => ?_, fun x y => ?_⟩
  · set K := q.C1 ^ (3 / 2 : ℝ) / h₂ with hKdef
    have hK : 0 ≤ K := div_nonneg (Real.rpow_nonneg hC.le _) hh2.le
    calc ∑ a, Real.sqrt (Υ h₂ x₁ a * Υ h₂ x₂ a * Υ h₁ a y₁ * Υ h₁ a y₂)
        = ∑ a, Real.sqrt (Υ h₂ x₁ a * Υ h₁ a y₁) * Real.sqrt (Υ h₂ x₂ a * Υ h₁ a y₂) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [← Real.sqrt_mul (mul_nonneg (hU2 x₁ a) (hU1 a y₁))]
          congr 1
          ring
      _ ≤ Real.sqrt (∑ a, Υ h₂ x₁ a * Υ h₁ a y₁) * Real.sqrt (∑ a, Υ h₂ x₂ a * Υ h₁ a y₂) :=
          Real.sum_sqrt_mul_sqrt_le _ (fun a => mul_nonneg (hU2 x₁ a) (hU1 a y₁))
            (fun a => mul_nonneg (hU2 x₂ a) (hU1 a y₂))
      _ ≤ Real.sqrt (K * Υ h₁ x₁ y₁) * Real.sqrt (K * Υ h₁ x₂ y₂) :=
          mul_le_mul (Real.sqrt_le_sqrt (h5 x₁ y₁)) (Real.sqrt_le_sqrt (h5 x₂ y₂))
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = K * Real.sqrt (Υ h₁ x₁ y₁ * Υ h₁ x₂ y₂) := by
          rw [← Real.sqrt_mul (mul_nonneg hK (hU1 x₁ y₁)),
            show K * Υ h₁ x₁ y₁ * (K * Υ h₁ x₂ y₂) = K ^ 2 * (Υ h₁ x₁ y₁ * Υ h₁ x₂ y₂) by ring,
            Real.sqrt_mul (sq_nonneg K), Real.sqrt_sq hK]
  · have hsq := (hadm.clause4 h₁ h₂ c1 c2 h12 x y).2
    have hLN : ErdosRiabov.localizationLength N W h₂ * h₂ ≤ (N : ℝ) * h₂ :=
      mul_le_mul_of_nonneg_right (loc_le_N N W h₂) hh2.le
    refine hsq.trans ?_
    calc q.C1 / h₂ * Real.sqrt (ErdosRiabov.localizationLength N W h₂ * h₂ * Υ h₁ x y)
        = q.C1 / h₂ * (Real.sqrt (ErdosRiabov.localizationLength N W h₂ * h₂) *
            Real.sqrt (Υ h₁ x y)) := by rw [Real.sqrt_mul hL.le]
      _ ≤ q.C1 / h₂ * (Real.sqrt ((N : ℝ) * h₂) * Real.sqrt (Υ h₁ x y)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hLN) (Real.sqrt_nonneg _))
            (div_nonneg hC.le hh2.le)
      _ = q.C1 / h₂ * Real.sqrt ((N : ℝ) * h₂) * Real.sqrt (Υ h₁ x y) := by ring

/-!
## The control inequalities at VS heights
-/

/-- For VS data `d` (`Flow.VSData`), `m ≥ 4`, `W ≥ 1`, `N = mW`,
`z ∈ BulkDomain N d.δ₀ d.κ d.C₀` and `0 ≤ s ≤ t ≤ 1`, with `η_r = vsHeight z r`,
`Υ = polynomialControl N W d.D`, `ℓ = localizationLength N W`, `C₁'' = d.C1pp`, `D'' = d.Dpp`,
`C_wc = d.Cwc`, all sites:
(U2) `Υ_t ≤ C₁''/(ℓ_tη_t)`, `Σ_a Υ_t(x,a) ≤ C₁''/η_t`,
`Υ_t ≥ N^{-2D''}`, and for `η_t ≤ (W/N)²`:
`(C₁'')⁻¹(Nη_t)⁻¹ ≤ Υ_t ≤ C₁''(Nη_t)⁻¹`;
(U3) `Υ_s ≤ Υ_t` (constant 1);
(U1b) `Υ_t ≤ (η_s/η_t)^{1+D/2} Υ_s`;
(U4) `Υ_s(x,a)Υ_t(a,y) ≤ C₁''/(ℓ_sη_s) Υ_t(x,y)` and
`Σ_a √(Υ_s(x,a)Υ_t(a,y)) ≤ C₁''/η_s √(ℓ_sη_s Υ_t(x,y))`;
(U5) `Σ_a Υ_s(x,a)Υ_t(a,y) ≤ C_wc/η_s Υ_t(x,y)`;
(U6) `Σ_q √(Υ_s(x₁,q)Υ_s(x₂,q)Υ_t(q,y₁)Υ_t(q,y₂)) ≤ C_wc/η_s √(Υ_t(x₁,y₁)Υ_t(x₂,y₂))`;
(U7) `Σ_q √(Υ_s(x,q)Υ_t(q,y)) ≤ C₁''/η_s √(Nη_s) √(Υ_t(x,y))`;
(U8) clause (v) with `η₁ = η_t ≤ η₂ = η_s`, `ηᵢ = η_r`, `r ∈ {s,t}`;
delocalized lower bounds: if `η_t ≤ (W/N)²`, and in particular if `t♭ < t`
(`t♭ = anchorTime z N W`, strict form), `Υ_t ≥ (C₁'')⁻¹(Nη_t)⁻¹` and
`Υ_t ≥ ((3/2)^D)⁻¹(Nη_t)⁻¹`.
-/
theorem ups_U2_U8_vs (d : VSData) {m W : ℕ} (hm : 4 ≤ m) (hW : 0 < W) {z : ℂ}
    (hz : BulkDomain (m * W) d.delta0 d.kappa d.C0 z) {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t)
    (ht1 : t ≤ 1) :
    -- (U2) at `η_t`
    (∀ x y, polynomialControl (m * W) W d.D (vsHeight z t) x y ≤
      d.C1pp / (ErdosRiabov.localizationLength (m * W) W (vsHeight z t) * vsHeight z t)) ∧
    (∀ x, ∑ a, polynomialControl (m * W) W d.D (vsHeight z t) x a ≤ d.C1pp / vsHeight z t) ∧
    (∀ x y, Real.rpow ((m * W : ℕ) : ℝ) (-2 * d.Dpp) ≤
      polynomialControl (m * W) W d.D (vsHeight z t) x y) ∧
    (vsHeight z t ≤ ((W : ℝ) / ((m * W : ℕ) : ℝ)) ^ 2 → ∀ x y,
      (1 / d.C1pp) * (1 / (((m * W : ℕ) : ℝ) * vsHeight z t)) ≤
        polynomialControl (m * W) W d.D (vsHeight z t) x y ∧
      polynomialControl (m * W) W d.D (vsHeight z t) x y ≤
        d.C1pp * (1 / (((m * W : ℕ) : ℝ) * vsHeight z t))) ∧
    -- (U3) with constant one, and the reverse comparison (U1b)
    (∀ x y, polynomialControl (m * W) W d.D (vsHeight z s) x y ≤
      polynomialControl (m * W) W d.D (vsHeight z t) x y) ∧
    (∀ x y, polynomialControl (m * W) W d.D (vsHeight z t) x y ≤
      (vsHeight z s / vsHeight z t) ^ (1 + d.D / 2) *
        polynomialControl (m * W) W d.D (vsHeight z s) x y) ∧
    -- (U4)
    (∀ x y,
      (∀ a, polynomialControl (m * W) W d.D (vsHeight z s) x a *
          polynomialControl (m * W) W d.D (vsHeight z t) a y ≤
        d.C1pp / (ErdosRiabov.localizationLength (m * W) W (vsHeight z s) * vsHeight z s) *
          polynomialControl (m * W) W d.D (vsHeight z t) x y) ∧
      (∑ a, Real.sqrt (polynomialControl (m * W) W d.D (vsHeight z s) x a *
          polynomialControl (m * W) W d.D (vsHeight z t) a y)) ≤
        d.C1pp / vsHeight z s *
          Real.sqrt (ErdosRiabov.localizationLength (m * W) W (vsHeight z s) * vsHeight z s *
            polynomialControl (m * W) W d.D (vsHeight z t) x y)) ∧
    -- (U5)
    (∀ x y, ∑ a, polynomialControl (m * W) W d.D (vsHeight z s) x a *
        polynomialControl (m * W) W d.D (vsHeight z t) a y ≤
      d.Cwc / vsHeight z s * polynomialControl (m * W) W d.D (vsHeight z t) x y) ∧
    -- (U6)
    (∀ x₁ x₂ y₁ y₂, ∑ a, Real.sqrt (polynomialControl (m * W) W d.D (vsHeight z s) x₁ a *
        polynomialControl (m * W) W d.D (vsHeight z s) x₂ a *
        polynomialControl (m * W) W d.D (vsHeight z t) a y₁ *
        polynomialControl (m * W) W d.D (vsHeight z t) a y₂) ≤
      d.Cwc / vsHeight z s * Real.sqrt (polynomialControl (m * W) W d.D (vsHeight z t) x₁ y₁ *
        polynomialControl (m * W) W d.D (vsHeight z t) x₂ y₂)) ∧
    -- (U7)
    (∀ x y, ∑ a, Real.sqrt (polynomialControl (m * W) W d.D (vsHeight z s) x a *
        polynomialControl (m * W) W d.D (vsHeight z t) a y) ≤
      d.C1pp / vsHeight z s * Real.sqrt (((m * W : ℕ) : ℝ) * vsHeight z s) *
        Real.sqrt (polynomialControl (m * W) W d.D (vsHeight z t) x y)) ∧
    -- (U8)
    (∀ r : ℝ, (r = s ∨ r = t) → ∀ x y,
      (∑ a,
        (min ((ErdosRiabov.cyclicDistance (m * W) a x : ℝ) + W)
            (ErdosRiabov.localizationLength (m * W) W (vsHeight z t)) /
          ErdosRiabov.localizationLength (m * W) W (vsHeight z t)) *
          Real.sqrt (polynomialControl (m * W) W d.D (vsHeight z s) x a *
            polynomialControl (m * W) W d.D (vsHeight z r) a y)) ≤
        d.C1pp / vsHeight z s *
          (ErdosRiabov.localizationLength (m * W) W (vsHeight z s) /
            ErdosRiabov.localizationLength (m * W) W (vsHeight z t)) *
          Real.sqrt
            ((ErdosRiabov.localizationLength (m * W) W (vsHeight z s) * vsHeight z s) /
              (ErdosRiabov.localizationLength (m * W) W (vsHeight z r) * vsHeight z r)) *
          Real.sqrt
            (ErdosRiabov.localizationLength (m * W) W (vsHeight z t) * vsHeight z t *
              polynomialControl (m * W) W d.D (vsHeight z t) x y)) ∧
    -- delocalized lower bounds, and the strict form `t♭ < t`
    (vsHeight z t ≤ ((W : ℝ) / ((m * W : ℕ) : ℝ)) ^ 2 → ∀ x y,
      (1 / d.C1pp) * (1 / (((m * W : ℕ) : ℝ) * vsHeight z t)) ≤
        polynomialControl (m * W) W d.D (vsHeight z t) x y ∧
      ((3 / 2 : ℝ) ^ d.D)⁻¹ * (1 / (((m * W : ℕ) : ℝ) * vsHeight z t)) ≤
        polynomialControl (m * W) W d.D (vsHeight z t) x y) ∧
    (anchorTime z (m * W) W < t → ∀ x y,
      (1 / d.C1pp) * (1 / (((m * W : ℕ) : ℝ) * vsHeight z t)) ≤
        polynomialControl (m * W) W d.D (vsHeight z t) x y ∧
      ((3 / 2 : ℝ) ^ d.D)⁻¹ * (1 / (((m * W : ℕ) : ℝ) * vsHeight z t)) ≤
        polynomialControl (m * W) W d.D (vsHeight z t) x y) := by
  have hN : 0 < m * W := Nat.mul_pos (by omega) hW
  have hD0 : (0 : ℝ) ≤ d.D := by linarith [d.D_ge_six]
  have ht0 : 0 ≤ t := hs0.trans hst
  have hη := hz.im_pos hN
  obtain ⟨hadm, hVS, hctl, -, hcl2, hcl35⟩ :=
    lemmaK_K5 d.b_pos d.b_lt_half d.delta0_pos d.kappa_pos d.C0_ge_one d.D_ge_six hm hW hz
  obtain ⟨hs1, hs2⟩ := hVS s hs0 (hst.trans ht1)
  obtain ⟨ht1', ht2⟩ := hVS t ht0 ht1
  have hts : vsHeight z t ≤ vsHeight z s := by
    unfold vsHeight
    nlinarith [semicircleM_im_pos hη]
  have hηt := vsHeight_pos hη ht1
  have c1 := hctl _ ht1' ht2
  have c2 := hctl _ hs1 hs2
  obtain ⟨h5, h6, h7⟩ := lemmaK_ups_derived hN hW hadm c1 c2 hts
  obtain ⟨hU2a, hU2b, hU2c, hU2d⟩ := hcl2 _ ht1' ht2
  obtain ⟨-, hU4, hU8⟩ := hcl35 _ _ ht1' hts hs2
  have hdeloc : vsHeight z t ≤ ((W : ℝ) / ((m * W : ℕ) : ℝ)) ^ 2 → ∀ x y,
      (1 / d.C1pp) * (1 / (((m * W : ℕ) : ℝ) * vsHeight z t)) ≤
        polynomialControl (m * W) W d.D (vsHeight z t) x y ∧
      ((3 / 2 : ℝ) ^ d.D)⁻¹ * (1 / (((m * W : ℕ) : ℝ) * vsHeight z t)) ≤
        polynomialControl (m * W) W d.D (vsHeight z t) x y := fun hsm x y =>
    ⟨(hU2d hsm x y).1, (polynomialControl_deloc hN hW hD0 hηt hsm x y).1⟩
  refine ⟨hU2a, hU2b, hU2c, hU2d, fun x y => polynomialControl_mono hN hW hD0 hηt hts x y,
    fun x y => polynomialControl_reverse hN hW hD0 hηt hts x y, hU4, h5, h6, h7,
    fun r hr x y => hU8 (vsHeight z r)
      (hr.elim (fun h => Or.inr (by rw [h])) (fun h => Or.inl (by rw [h]))) x y, hdeloc,
    fun hlt => hdeloc (lt_etaFlat_of_anchorTime_lt hη hN hlt ht1).1.le⟩

end BlockBand.Native.ErdosRiabov.LemmaK
