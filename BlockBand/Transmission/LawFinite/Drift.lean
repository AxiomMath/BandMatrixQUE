module

public import BlockBand.Transmission.LawFinite.DriftCore

/-!
# The reciprocal drift, with absorption

Hypothesis `PassiveBoundsStatement` (through `reciprocal_core`).

The fresh absorption is moved into the passive input: `X₊ = B*(A - E - X')⁻¹B` with
`X' = X - iε` (`absorbedInput`), so `reciprocal_core` applies at `X'`. Then
* `passiveMass_le_absorb`: `q(X) ≤ (1 + ε/η)²q(X')` (`R = R'(1 + iεR)`, `Q(X') ⪰ R'*YR'`);
* `δ₀(X') ≤ δ₀(X) + ε/η²` (`PathScalar.jetDistance0_absorb_le`, proved elsewhere);
* `drift_absorb_scalar`: the bound at `X'` implies the bound at `X` with the extra `Cε/q`.

This replaces the paper's argument through `q̃₊ = Tr QLL*` and resolvent differentiation in the
fresh `iε` by an exact identity; only `q ≥ K > 0` is used from the domain `q ≥ K`.

**`reciprocalDrift_holds hA : ReciprocalDrift`.**
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawFinite

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PathScalar
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

section Absorb

variable {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
  {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef)
include hb0 hb h1 h2 hY

/-- `R = R'(1 + iεR)`. -/
theorem resolvent_eq_absorb {ε : ℝ} (hε : 0 ≤ ε) :
    passiveResolvent b E X = passiveResolvent b E (absorbedInput X ε) *
      (1 + (((ε : ℝ) : ℂ) * Complex.I) • passiveResolvent b E X) := by
  have hR := (nearPencil_inverse hb0 hb h1 h2 hY).1
  have hR' := (nearPencil_inverse hb0 hb h1 h2 (passiveY_absorbedInput hY hε)).2
  set R := passiveResolvent b E X
  set R' := passiveResolvent b E (absorbedInput X ε)
  have hK : boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - absorbedInput X ε =
      (boundaryZ b E • 1 - X) + (((ε : ℝ) : ℂ) * Complex.I) • 1 := by
    simp only [absorbedInput]; abel
  calc R = R' * (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - absorbedInput X ε) * R := by
        rw [hR', Matrix.one_mul]
    _ = R' * (1 + (((ε : ℝ) : ℂ) * Complex.I) • R) := by
        rw [hK, Matrix.mul_assoc, Matrix.add_mul, hR, Matrix.smul_mul, Matrix.one_mul]

/-- **`q(X) ≤ (1 + ε/η)²q(X - iε)`.** -/
theorem passiveMass_le_absorb {ε : ℝ} (hε : 0 ≤ ε) :
    passiveMass b E X ≤ (1 + ε / etaZ b E) ^ 2 * passiveMass b E (absorbedInput X ε) := by
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hY' := passiveY_absorbedInput hY hε
  set R := passiveResolvent b E X
  set R' := passiveResolvent b E (absorbedInput X ε)
  set A := 1 + (((ε : ℝ) : ℂ) * Complex.I) • R
  have hRn : ‖R‖ ≤ (etaZ b E)⁻¹ := norm_passiveResolvent_le hb0 hb h1 h2 hY
  have hAn : ‖A‖ ≤ 1 + ε / etaZ b E := by
    refine (norm_add_le _ _).trans (add_le_add PassiveLayer.norm_one_le' ?_)
    refine (norm_smul_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hε,
      div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hRn hε
  set P := R'ᴴ * passiveY X * R'
  have hP : P.PosSemidef := hY.conjTranspose_mul_mul_same _
  have hQ : passiveQ b E X = Aᴴ * P * A := by
    rw [passiveQ]
    conv_lhs => rw [show passiveResolvent b E X = R' * A from
      resolvent_eq_absorb hb0 hb h1 h2 hY hε]
    simp only [P, conjTranspose_mul, Matrix.mul_assoc]
  have hPq : P.trace.re ≤ passiveMass b E (absorbedInput X ε) := by
    have hYe : passiveY (absorbedInput X ε) = passiveY X + (ε : ℂ) • 1 :=
      PathScalar.passiveY_absorb_eq X ε
    rw [passiveMass, passiveQ, hYe, Matrix.mul_add, Matrix.add_mul, trace_add, Complex.add_re]
    have : 0 ≤ (R'ᴴ * ((ε : ℂ) • 1) * R').trace.re := by
      have hpsd : (R'ᴴ * ((ε : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)) * R').PosSemidef :=
        (Matrix.PosSemidef.one.smul (by exact_mod_cast hε)).conjTranspose_mul_mul_same _
      exact (SourceMixing.mm_trace_posSemidef hpsd).1
    linarith
  have hA1 : (Aᴴ * P * A).trace.re ≤ (1 + ε / etaZ b E) ^ 2 * P.trace.re := by
    have e : (Aᴴ * P * A).trace = ((A * Aᴴ) * P).trace := by
      rw [Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]; exact trace_mul_comm _ _
    rw [e]
    refine (Complex.re_le_norm _).trans ((norm_trace_mul_posSemidef_le hP _).trans ?_)
    refine mul_le_mul_of_nonneg_right ?_ (SourceMixing.mm_trace_posSemidef hP).1
    refine (Matrix.l2_opNorm_mul _ _).trans ?_
    rw [Matrix.l2_opNorm_conjTranspose, sq]
    exact mul_le_mul hAn hAn (norm_nonneg _) (by positivity)
  rw [passiveMass, hQ]
  refine hA1.trans (mul_le_mul_of_nonneg_left hPq (sq_nonneg _))

end Absorb

/-- Scalar facts for the transfer from `X'` to `X` (pure). -/
theorem drift_absorb_facts {q q' δ δ' ε η Li Kε W : ℝ} (hq : 0 < q) (hW : 1 ≤ W)
    (hε : 0 ≤ ε) (hεK : ε ≤ Kε / W ^ 2) (hη : 0 < η) (hLi : η⁻¹ ≤ Li)
    (hδ : 0 ≤ δ) (hq' : q ≤ (1 + ε / η) ^ 2 * q') (hδ' : δ' ≤ δ + ε / η ^ 2) :
    1 ≤ (1 + Kε * Li) ^ 2 ∧ q'⁻¹ ≤ q⁻¹ + (2 * Li + Kε * Li ^ 2) * (ε / q) ∧
      δ' / q' ≤ (1 + Kε * Li) ^ 2 * (δ / q + Li ^ 2 * (ε / q)) ∧
      (W * q')⁻¹ ≤ (1 + Kε * Li) ^ 2 * (W * q)⁻¹ := by
  have hW0 : 0 < W := by linarith
  have hKε : 0 ≤ Kε := by
    have h0 : 0 ≤ Kε / W ^ 2 := hε.trans hεK
    have := mul_nonneg h0 (sq_nonneg W)
    rwa [div_mul_cancel₀ _ (by positivity)] at this
  have hLi0 : 0 ≤ Li := (inv_pos.mpr hη).le.trans hLi
  have hεK1 : ε ≤ Kε := hεK.trans (div_le_self hKε (one_le_pow₀ hW))
  set ρ := (1 + ε / η) ^ 2
  have hεη : ε / η ≤ ε * Li := by rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_left hLi hε
  have hεη0 : 0 ≤ ε / η := div_nonneg hε hη.le
  have hρ1 : 1 ≤ ρ := one_le_pow₀ (by linarith only [hεη0])
  have hρM : ρ ≤ (1 + Kε * Li) ^ 2 := by
    refine pow_le_pow_left₀ (by positivity) ?_ 2
    have := mul_le_mul_of_nonneg_right hεK1 hLi0
    linarith only [this, hεη]
  have hρ0 : 0 < ρ := by linarith only [hρ1]
  have hq'0 : 0 < q' := by
    by_contra h; push Not at h
    have : ρ * q' ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hρ0.le h
    linarith only [this, hq', hq]
  have hinv : q'⁻¹ ≤ ρ * q⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hq, ← div_eq_inv_mul, div_le_iff₀ hq'0]
    linarith only [hq']
  have hρm1 : ρ - 1 ≤ ε * (2 * Li + Kε * Li ^ 2) := by
    have e : ρ - 1 = 2 * (ε / η) + (ε / η) ^ 2 := by simp only [ρ]; ring
    have h3 : (ε / η) ^ 2 ≤ (ε * Li) ^ 2 := pow_le_pow_left₀ hεη0 hεη 2
    have h4 : (ε * Li) ^ 2 ≤ ε * (Kε * Li ^ 2) := by
      have := mul_le_mul_of_nonneg_right hεK1 (by positivity : (0 : ℝ) ≤ ε * Li ^ 2)
      have e2 : (ε * Li) ^ 2 = ε * (ε * Li ^ 2) := by ring
      have e3 : ε * (Kε * Li ^ 2) = Kε * (ε * Li ^ 2) := by ring
      rw [e2, e3]; nlinarith only [this]
    have e4 : ε * (2 * Li + Kε * Li ^ 2) = 2 * (ε * Li) + ε * (Kε * Li ^ 2) := by ring
    rw [e, e4]; linarith only [hεη, h3, h4]
  have hq1 : 0 ≤ q⁻¹ := (inv_pos.mpr hq).le
  refine ⟨hρ1.trans hρM, ?_, ?_, ?_⟩
  · have e : ρ * q⁻¹ = q⁻¹ + (ρ - 1) * q⁻¹ := by ring
    have h5 : (ρ - 1) * q⁻¹ ≤ ε * (2 * Li + Kε * Li ^ 2) * q⁻¹ :=
      mul_le_mul_of_nonneg_right hρm1 hq1
    have e2 : ε * (2 * Li + Kε * Li ^ 2) * q⁻¹ = (2 * Li + Kε * Li ^ 2) * (ε / q) := by ring
    linarith only [hinv, e, h5, e2]
  · have h6 : δ' / q' ≤ (δ + ε * Li ^ 2) * q'⁻¹ := by
      rw [div_eq_mul_inv]
      have hεη2 : ε / η ^ 2 ≤ ε * Li ^ 2 := by
        rw [div_eq_mul_inv, ← inv_pow]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_pos.mpr hη).le hLi 2) hε
      by_cases hd : 0 ≤ δ'
      · exact mul_le_mul_of_nonneg_right (hδ'.trans (by linarith only [hεη2]))
          (inv_pos.mpr hq'0).le
      · push Not at hd
        have : δ' * q'⁻¹ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hd.le (inv_pos.mpr hq'0).le
        have : 0 ≤ (δ + ε * Li ^ 2) * q'⁻¹ := by positivity
        linarith
    refine h6.trans ?_
    calc (δ + ε * Li ^ 2) * q'⁻¹ ≤ (δ + ε * Li ^ 2) * (ρ * q⁻¹) :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = ρ * (δ / q + Li ^ 2 * (ε / q)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hρM (by positivity)
  · rw [mul_inv, mul_inv]
    calc W⁻¹ * q'⁻¹ ≤ W⁻¹ * (ρ * q⁻¹) := mul_le_mul_of_nonneg_left hinv (inv_pos.mpr hW0).le
      _ = ρ * (W⁻¹ * q⁻¹) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hρM (by positivity)

/-- Scalar transfer of the drift bound from `X'` to `X` (pure). -/
theorem drift_absorb_scalar {q q' δ δ' ε η Li Kε W C' : ℝ} (hq : 0 < q) (hW : 1 ≤ W)
    (hε : 0 ≤ ε) (hεK : ε ≤ Kε / W ^ 2) (hη : 0 < η) (hLi : η⁻¹ ≤ Li) (hC' : 0 ≤ C')
    (hδ : 0 ≤ δ) (hq' : q ≤ (1 + ε / η) ^ 2 * q') (hδ' : δ' ≤ δ + ε / η ^ 2) :
    q'⁻¹ + C' * (W⁻¹ + δ' / q' + (W * q')⁻¹) ≤
      q⁻¹ + (C' * (1 + Kε * Li) ^ 2 * (1 + Li ^ 2) + 2 * Li + Kε * Li ^ 2) *
        (W⁻¹ + δ / q + (W * q)⁻¹ + ε / q) := by
  obtain ⟨hM1, t1, h7, h8⟩ := drift_absorb_facts hq hW hε hεK hη hLi hδ hq' hδ'
  have hW0 : 0 < W := by linarith
  have hLi0 : 0 ≤ Li := (inv_pos.mpr hη).le.trans hLi
  have hKε : 0 ≤ Kε := by
    have h0 : 0 ≤ Kε / W ^ 2 := hε.trans hεK
    have := mul_nonneg h0 (sq_nonneg W)
    rwa [div_mul_cancel₀ _ (by positivity)] at this
  set M := (1 + Kε * Li) ^ 2
  set K₁ := M * (1 + Li ^ 2)
  have hδq : 0 ≤ δ / q := div_nonneg hδ hq.le
  have hεq : 0 ≤ ε / q := div_nonneg hε hq.le
  have hWi : 0 ≤ W⁻¹ := (inv_pos.mpr hW0).le
  have hWqi : 0 ≤ (W * q)⁻¹ := by positivity
  have hL : 0 ≤ Li ^ 2 := sq_nonneg _
  have hMK : M ≤ K₁ := le_mul_of_one_le_right (by linarith only [hM1]) (by linarith only [hL])
  have hMLK : M * Li ^ 2 ≤ K₁ := by
    have : M * Li ^ 2 ≤ M * (1 + Li ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith only) (by linarith only [hM1])
    exact this
  have hK1 : 1 ≤ K₁ := hM1.trans hMK
  have a : W⁻¹ ≤ K₁ * W⁻¹ := le_mul_of_one_le_left hWi hK1
  have b1 := mul_le_mul_of_nonneg_right hMK hδq
  have b2 := mul_le_mul_of_nonneg_right hMLK hεq
  have eb : M * (δ / q + Li ^ 2 * (ε / q)) = M * (δ / q) + M * Li ^ 2 * (ε / q) := by ring
  have c : M * (W * q)⁻¹ ≤ K₁ * (W * q)⁻¹ := mul_le_mul_of_nonneg_right hMK hWqi
  have h9 : W⁻¹ + δ' / q' + (W * q')⁻¹ ≤
      K₁ * W⁻¹ + K₁ * (δ / q) + K₁ * (W * q)⁻¹ + K₁ * (ε / q) := by
    linarith only [a, b1, b2, eb, c, h7, h8]
  have h10 := mul_le_mul_of_nonneg_left h9 hC'
  have t3 : (2 * Li + Kε * Li ^ 2) * (ε / q) ≤
      (2 * Li + Kε * Li ^ 2) * (W⁻¹ + δ / q + (W * q)⁻¹ + ε / q) :=
    mul_le_mul_of_nonneg_left (by linarith only [hδq, hWi, hWqi]) (by positivity)
  have e : (C' * M * (1 + Li ^ 2) + 2 * Li + Kε * Li ^ 2) * (W⁻¹ + δ / q + (W * q)⁻¹ + ε / q) =
      C' * (K₁ * W⁻¹ + K₁ * (δ / q) + K₁ * (W * q)⁻¹ + K₁ * (ε / q)) +
        (2 * Li + Kε * Li ^ 2) * (W⁻¹ + δ / q + (W * q)⁻¹ + ε / q) := by
    simp only [K₁]; ring
  rw [e]
  linarith only [t1, h10, t3]

/-- **`ReciprocalDrift`**. -/
theorem reciprocalDrift_holds (hA : PassiveBoundsStatement) : ReciprocalDrift := by
  intro b hb0 hb κI Kε hκ hKε
  obtain ⟨d', C', hd', hC', hcore⟩ := reciprocal_core hA hb0 hb hκ
  have hηL : 0 < etaLow b κI := etaLow_pos (by linarith) hκ
  set Li := (etaLow b κI)⁻¹
  refine ⟨d' / 2, C' * (1 + Kε * Li) ^ 2 * (1 + Li ^ 2) + 2 * Li + Kε * Li ^ 2, by positivity,
    fun K A hK hA0 => ?_⟩
  obtain ⟨CA, W₀, hCA, hc⟩ := hcore K A hK hA0
  refine ⟨CA, max W₀ (⌈2 * Kε * Li ^ 2 / d'⌉₊ + 1), fun W hW E hE X hY ε hε hεK hδ hqK => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨hW0, hW1⟩ := hW
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hLi : (etaZ b E)⁻¹ ≤ Li := inv_anti₀ hηL (etaLow_le (by linarith) hκ hE)
  have hLi0 : 0 ≤ Li := (inv_pos.mpr hη).le.trans hLi
  have hW1r : (1 : ℝ) ≤ W := by
    have : (1 : ℝ) ≤ ((⌈2 * Kε * Li ^ 2 / d'⌉₊ + 1 : ℕ) : ℝ) := by
      push_cast; have := Nat.cast_nonneg (α := ℝ) ⌈2 * Kε * Li ^ 2 / d'⌉₊; linarith
    exact this.trans (by exact_mod_cast hW1)
  have hWpos : (0 : ℝ) < W := by linarith
  have hq : 0 < passiveMass b E X := lt_of_lt_of_le hK hqK
  have hY' := passiveY_absorbedInput hY hε
  have hδ' : jetDistance0 b E (absorbedInput X ε) ≤ jetDistance0 b E X + ε / etaZ b E ^ 2 :=
    jetDistance0_absorb_le hb0 hb h1 h2 hY hε
  have hq' := passiveMass_le_absorb hb0 hb h1 h2 hY hε
  -- the domain at `X'`
  have hεdom : ε / etaZ b E ^ 2 ≤ d' / 2 := by
    have a1 : ε / etaZ b E ^ 2 ≤ ε * Li ^ 2 := by
      rw [div_eq_mul_inv, ← inv_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_pos.mpr hη).le hLi 2) hε
    have hWc : 2 * Kε * Li ^ 2 / d' ≤ W := by
      have := Nat.le_ceil (2 * Kε * Li ^ 2 / d')
      have : ((⌈2 * Kε * Li ^ 2 / d'⌉₊ + 1 : ℕ) : ℝ) ≤ W := by exact_mod_cast hW1
      push_cast at this; linarith
    have a2 : ε * Li ^ 2 ≤ Kε / W * Li ^ 2 := by
      refine mul_le_mul_of_nonneg_right (hεK.trans ?_) (sq_nonneg _)
      exact div_le_div_of_nonneg_left hKε hWpos (by nlinarith)
    have a3 : Kε / W * Li ^ 2 ≤ d' / 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hWpos]
      rw [div_le_iff₀ hd'] at hWc
      nlinarith
    linarith
  have hq'pos : 0 < passiveMass b E (absorbedInput X ε) := by
    by_contra h; push Not at h
    have : (1 + ε / etaZ b E) ^ 2 * passiveMass b E (absorbedInput X ε) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) h
    linarith
  have hb1 := hc W hW0 E hE _ hY' (by linarith) hq'pos
  refine hb1.trans ?_
  have := drift_absorb_scalar hq hW1r hε hεK hη hLi hC'
    (norm_nonneg _ : 0 ≤ jetDistance0 b E X) hq' hδ'
  exact add_le_add this le_rfl

end BlockBand.Transmission.LawFinite
