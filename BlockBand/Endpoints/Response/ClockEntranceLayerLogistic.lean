module

public import BlockBand.Endpoints.Response.ClockEntranceLayerDefs

/-!
# The fractional logistic inequality from the Jensen gap and the passive mean

This file proves `ClockLayerLogistic` from `ClockLayerJensenGap` and the passive mean bound
`OnePortPassiveMean` (`clockLayerLogistic_of_jensenGap`).

* `cel_transmission_posSemidef`: `T = 4ηR*YR ⪰ 0` for passive `X`.
* `cel_card_discarded_le`: at most `2g` indices have `T_ii > 1/2` in the `A`-eigenbasis.
* `cel_fracTrace_mul_le`: `0 ⪯ U ⪯ mI`, `m ≥ 1` ⇒ `Tr(UA)^p ≤ m Tr A^p` (the passive mean step).
* `cel_sq_div_ge`: `(H-D)²/γ ≥ H²/(2γ) - 2x²γ` for `0 ≤ D ≤ xγ` (discarded sum + AM–GM).
* `cel_gap_lower`: `c'·H_p²/(2γ^p) ≤ Σ_{ret} λ_iλ_j ∫… + 8c'|g|^{2(1-p)}γ^p`,
  `c' = K^{p-2}/(4(2-p))` (the divided difference `sum_concavity_integral_ge`, the
  discarded power sum `(2g)^{1-p}γ^p`, and AM–GM for the forcing).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Matrix
open scoped ENNReal ComplexOrder
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Endpoints BlockBand.Internal.Contracts.Layers

variable {W : ℕ}

theorem cel_InJetDomain.mono {b E : ℝ} {s : ℂ} {d d' : ℝ} {X : Matrix (Fin W) (Fin W) ℂ}
    (h : cel_InJetDomain b E s d X) (hd : d ≤ d') : cel_InJetDomain b E s d' X :=
  ⟨h.1, h.2.1.trans hd, h.2.2.1.trans hd,
    h.2.2.2.trans (mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg _))⟩

/-- For passive `X` (`Y = -Im X ⪰ 0`), the transmission `T = 4ηR*YR` is positive semidefinite. -/
theorem cel_transmission_posSemidef {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2)
    {X : Matrix (Fin W) (Fin W) ℂ} (hX : (passiveY X).PosSemidef) :
    (passiveTransmission b E X).PosSemidef := by
  have hη : 0 < etaZ b E := pfi_boundaryZ_im_pos hb hE1 hE2
  unfold passiveTransmission passiveQ
  refine (hX.conjTranspose_mul_mul_same _).smul ?_
  exact Complex.zero_le_real.mpr (by positivity)

/-- `g = Tr T ≥ 0` for passive `X`. -/
theorem cel_conductance_nonneg {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2)
    {X : Matrix (Fin W) (Fin W) ℂ} (hX : (passiveY X).PosSemidef) :
    0 ≤ conductanceOf (passiveTransmission b E X) := by
  unfold conductanceOf
  have h := (cel_transmission_posSemidef hb hE1 hE2 hX).trace_nonneg
  exact (Complex.le_def.mp h).1

/-- At most `2g` discarded indices: in the eigenbasis of `A` (columns of
`hA.eigenvectorUnitary`), the number of indices with `T_ii > 1/2` is at most `2 Tr T`. -/
theorem cel_card_discarded_le {T A : Matrix (Fin W) (Fin W) ℂ} (hT : T.PosSemidef)
    (hA : A.IsHermitian) :
    ((Finset.univ.filter fun i => ¬ ((star (hA.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ) *
        T * (hA.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ)) i i).re ≤ 1 / 2).card : ℝ) ≤
      2 * T.trace.re := by
  set U : Matrix (Fin W) (Fin W) ℂ := ↑hA.eigenvectorUnitary
  set M := star U * T * U
  have hM : M.PosSemidef := by
    have := hT.conjTranspose_mul_mul_same U
    simpa only [M, star_eq_conjTranspose] using this
  have htr : M.trace = T.trace := by
    simp only [M]
    rw [trace_mul_cycle, Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2, Matrix.one_mul]
  have hsum : ∑ i, (M i i).re = T.trace.re := by
    rw [← htr, trace, Complex.re_sum]; rfl
  have hnn : ∀ i, 0 ≤ (M i i).re := fun i => by
    have := (Complex.le_def.mp (hM.diag_nonneg (i := i))).1
    simpa using this
  set Sc := Finset.univ.filter fun i => ¬ (M i i).re ≤ 1 / 2
  have h1 : (Sc.card : ℝ) * (1 / 2) ≤ ∑ i ∈ Sc, (M i i).re := by
    have := Finset.card_nsmul_le_sum Sc (fun i => (M i i).re) (1 / 2) fun i hi => by
      have := (Finset.mem_filter.mp hi).2
      linarith [not_le.mp this]
    simpa [nsmul_eq_mul] using this
  have h2 : ∑ i ∈ Sc, (M i i).re ≤ ∑ i, (M i i).re :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ => hnn i
  linarith

section Mean

variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped MatrixOrder in
/-- The passive mean step: `0 ⪯ U ⪯ mI` with `m ≥ 1` and `A ⪰ 0` give
`Tr(UA)^p ≤ m^p Tr A^p ≤ m Tr A^p` for `0 ≤ p ≤ 1` (`Tr(UA)^p = Tr(A^{1/2}UA^{1/2})^p`). -/
theorem cel_fracTrace_mul_le {A U : Matrix n n ℂ} (hA : A.PosSemidef) (hU : U.PosSemidef)
    {m : ℝ} (hm : 1 ≤ m) (hUm : (((m : ℝ) : ℂ) • (1 : Matrix n n ℂ) - U).PosSemidef) {p : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) : fracTrace p (U * A) ≤ m * fracTrace p A := by
  obtain ⟨X, hX, -, hXX⟩ := CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts
    hA.isHermitian (QuasispectrumRestricts.nnreal_of_nonneg hA.nonneg)
  have hXh : Xᴴ = X := hX.star_eq
  have h1 : fracTrace p (U * A) = fracTrace p (X * U * X) := by
    rw [← hXX, ← Matrix.mul_assoc, fracTrace_mul_comm, Matrix.mul_assoc]
  have h2 : fracTrace p (X * (((m : ℝ) : ℂ) • (1 : Matrix n n ℂ)) * X) = m ^ p * fracTrace p A := by
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hXX,
      fracTrace_smul hA.isHermitian (by linarith)]
  have hP : (X * U * X).PosSemidef := by
    simpa only [hXh] using hU.mul_mul_conjTranspose_same X
  have hQ : (X * (((m : ℝ) : ℂ) • (1 : Matrix n n ℂ)) * X).PosSemidef := by
    have := (hUm.add hU).mul_mul_conjTranspose_same X
    simpa only [hXh, sub_add_cancel] using this
  have hsub : (X * (((m : ℝ) : ℂ) • (1 : Matrix n n ℂ)) * X - X * U * X).PosSemidef := by
    have := hUm.mul_mul_conjTranspose_same X
    simpa only [hXh, Matrix.mul_sub, Matrix.sub_mul] using this
  have hmp : m ^ p ≤ m := by
    calc m ^ p ≤ m ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hm hp1
      _ = m := Real.rpow_one m
  rw [h1]
  calc fracTrace p (X * U * X) ≤ fracTrace p (X * (((m : ℝ) : ℂ) • (1 : Matrix n n ℂ)) * X) :=
        fracTrace_mono hP.isHermitian hQ.isHermitian hsub hp
    _ = m ^ p * fracTrace p A := h2
    _ ≤ m * fracTrace p A := mul_le_mul_of_nonneg_right hmp (fracTrace_nonneg p A)

end Mean

/-- Discarded sum and AM–GM: for `0 ≤ D ≤ xγ`, `x ≥ 0`, `γ ≥ 0`,
`H²/γ/2 - 2x²γ ≤ (H - D)²/γ` (both sides `0` when `γ = 0`). -/
theorem cel_sq_div_ge {H D x γ : ℝ} (hD0 : 0 ≤ D) (hγ : 0 ≤ γ) (hDx : D ≤ x * γ) :
    H ^ 2 / γ / 2 - 2 * x ^ 2 * γ ≤ (H - D) ^ 2 / γ := by
  rcases eq_or_lt_of_le hγ with h0 | hγ0
  · rw [← h0]; simp
  have hD2 : D ^ 2 ≤ (x * γ) ^ 2 := pow_le_pow_left₀ hD0 hDx 2
  have key : H ^ 2 / 2 - 2 * (x * γ) ^ 2 ≤ (H - D) ^ 2 := by nlinarith [sq_nonneg (H - 2 * D)]
  have e : H ^ 2 / γ / 2 - 2 * x ^ 2 * γ = (H ^ 2 / 2 - 2 * (x * γ) ^ 2) / γ := by
    field_simp
  rw [e]
  exact div_le_div_of_nonneg_right key hγ

/-- The retained concavity gap controls `H_p²/γ^p`: for `A ⪰ 0`, passive-type `T ⪰ 0`
(`T = passiveTransmission b E X`), `0 < p < 1`, `K > 0` and `c' = K^{p-2}/(4(2-p))`,
`c' H_p²/γ^p/2 ≤ Σ_{i,j ret} λ_iλ_j ∫_0^∞ s^{p-1}ds/((Kλ_i+s)(Kλ_j+s)) + 8c'|g|^{2(1-p)}γ^p`. -/
theorem cel_gap_lower {b E p K : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hK : 0 < K)
    {X A : Matrix (Fin W) (Fin W) ℂ} (hT : (passiveTransmission b E X).PosSemidef)
    (hA : A.PosSemidef) :
    K ^ (p - 2) / (4 * (2 - p)) * (fracTrace p A ^ 2 / A.trace.re ^ p / 2) ≤
      cel_retainedGap b E p K X hA.isHermitian + 8 * (K ^ (p - 2) / (4 * (2 - p))) *
        (|conductanceOf (passiveTransmission b E X)| ^ (2 * (1 - p)) * A.trace.re ^ p) := by
  classical
  set c' := K ^ (p - 2) / (4 * (2 - p)) with hc'def
  have hc' : 0 ≤ c' := by
    have : 0 < 2 - p := by linarith
    positivity
  set ev := hA.isHermitian.eigenvalues
  set S := cel_retained b E X hA.isHermitian
  set Sc := Finset.univ.filter fun i => ¬ ((star (hA.isHermitian.eigenvectorUnitary :
    Matrix (Fin W) (Fin W) ℂ) * passiveTransmission b E X *
      (hA.isHermitian.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ)) i i).re ≤ 1 / 2
  set g := conductanceOf (passiveTransmission b E X)
  set γ := A.trace.re
  have hγ0 : 0 ≤ γ := (Complex.le_def.mp hA.trace_nonneg).1
  have hg0 : 0 ≤ g := (Complex.le_def.mp hT.trace_nonneg).1
  have hev : ∀ i, 0 ≤ ev i := fun i => hA.eigenvalues_nonneg i
  -- `H = Σ_S λ^p + Σ_{Sᶜ} λ^p`
  have hH : fracTrace p A = ∑ i ∈ S, ev i ^ p + ∑ i ∈ Sc, ev i ^ p := by
    rw [fracTrace_eq_sum_eigenvalues_of_posSemidef hA]
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  -- discarded power sum
  have hcard : (Sc.card : ℝ) ≤ 2 * g := cel_card_discarded_le hT hA.isHermitian
  have hD := sum_eigenvalues_rpow_le_of_card_le hA hp0 hp1.le Sc hcard
  have hD' : ∑ i ∈ Sc, ev i ^ p ≤ (2 * g) ^ (1 - p) * γ ^ p := hD.1.trans hD.2
  -- retained concavity gap
  have hgap : c' / γ ^ p * (∑ i ∈ S, ev i ^ p) ^ 2 ≤ cel_retainedGap b E p K X hA.isHermitian :=
    sum_concavity_integral_ge S ev hp0 hp1 hK (fun i _ => hev i)
      (fun i _ => eigenvalues_le_trace hA i)
  -- algebra
  set x := (2 * g) ^ (1 - p)
  have hx0 : 0 ≤ x := Real.rpow_nonneg (by linarith) _
  have hγp : 0 ≤ γ ^ p := Real.rpow_nonneg hγ0 _
  have halg := cel_sq_div_ge (H := fracTrace p A) (Finset.sum_nonneg fun i _ =>
    Real.rpow_nonneg (hev i) p) hγp hD'
  have hx2 : x ^ 2 ≤ 4 * |g| ^ (2 * (1 - p)) := by
    have e1 : x ^ 2 = (2 * g) ^ (2 * (1 - p)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num; ring_nf
    rw [e1, Real.mul_rpow (by norm_num) hg0, abs_of_nonneg hg0]
    have h2 : (2 : ℝ) ^ (2 * (1 - p)) ≤ 4 := by
      calc (2 : ℝ) ^ (2 * (1 - p)) ≤ 2 ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 4 := by norm_num
    exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hg0 _)
  have hHS : fracTrace p A - ∑ i ∈ Sc, ev i ^ p = ∑ i ∈ S, ev i ^ p := by rw [hH]; ring
  rw [hHS] at halg
  have e2 : c' / γ ^ p * (∑ i ∈ S, ev i ^ p) ^ 2 = c' * ((∑ i ∈ S, ev i ^ p) ^ 2 / γ ^ p) := by
    ring
  rw [e2] at hgap
  have h3 : c' * (2 * x ^ 2 * γ ^ p) ≤ 8 * c' * (|g| ^ (2 * (1 - p)) * γ ^ p) := by
    have := mul_le_mul_of_nonneg_right hx2 hγp
    nlinarith
  have h4 := mul_le_mul_of_nonneg_left halg hc'
  nlinarith

/-- **The clock fractional logistic inequality from the Jensen gap and the passive mean.**
Hypotheses: `ClockLayerJensenGap` and `OnePortPassiveMean`. Constants: `C = max(C_a, 8cc')`,
`c_L = cc'/2`, `c' = K^{p-2}/(4(2-p))`.
-/
theorem clockLayerLogistic_of_jensenGap (hJ : ClockLayerJensenGap) (ha : OnePortPassiveMean) :
    ClockLayerLogistic := by
  intro b hb hb' E hE hE' p hp hp' s hs
  obtain ⟨K, c, dJ, WJ, hK, hc, hdJ, hJW⟩ := hJ b hb hb' E hE hE' p hp hp' s hs
  obtain ⟨Ca, da, Wa, hCa, hda, haW⟩ := ha b hb hb' E hE hE' s hs
  set c' := K ^ (p - 2) / (4 * (2 - p)) with hc'def
  have hc' : 0 < c' := by
    have : 0 < 2 - p := by linarith
    have : 0 < K ^ (p - 2) := Real.rpow_pos_of_pos hK _
    positivity
  set Cm := max Ca (8 * c * c')
  refine ⟨Cm, c * c' / 2, min dJ da, max WJ Wa, le_max_of_le_left hCa, by positivity,
    lt_min hdJ hda, fun W hW X hX A hA => ?_⟩
  have hb1 : b < 1 := by linarith
  have hXJ := hX.mono (min_le_left _ _)
  have hXa := hX.mono (min_le_right _ _)
  obtain ⟨hU0, hU1⟩ := haW W (le_of_max_le_right hW) X hXa
  have hJ1 := hJW W (le_of_max_le_left hW) X hXJ A hA
  have hT := cel_transmission_posSemidef hb1 hE hE' hX.1
  set H := fracTrace p A
  set γ := A.trace.re
  set g := conductanceOf (passiveTransmission b E X)
  set δ := jetDistance0 b E X
  set F := |g| ^ (2 * (1 - p)) * γ ^ p
  set Q := H ^ 2 / γ ^ p
  set G := cel_retainedGap b E p K X hA.isHermitian
  have hH0 : 0 ≤ H := fracTrace_nonneg p A
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  have hF0 : 0 ≤ F := mul_nonneg (by positivity)
    (Real.rpow_nonneg (Complex.le_def.mp hA.trace_nonneg).1 _)
  have hQ0 : 0 ≤ Q := div_nonneg (sq_nonneg _)
    (Real.rpow_nonneg (Complex.le_def.mp hA.trace_nonneg).1 _)
  -- the mean step
  have hm1 : 1 ≤ 1 + Ca * δ + Ca / (W : ℝ) ^ 2 := by
    have : 0 ≤ Ca * δ := mul_nonneg hCa hδ0
    have : 0 ≤ Ca / (W : ℝ) ^ 2 := div_nonneg hCa (sq_nonneg _)
    linarith
  have hmean := cel_fracTrace_mul_le hA hU0 hm1 hU1 hp.le hp'.le
  have hmean' : fracTrace p (matrixExpect (freshLaw W b) (freshU b E X) * A) ≤
      (1 + Cm * δ + Cm / (W : ℝ) ^ 2) * H := by
    refine hmean.trans (mul_le_mul_of_nonneg_right ?_ hH0)
    have h1 : Ca * δ ≤ Cm * δ := mul_le_mul_of_nonneg_right (le_max_left _ _) hδ0
    have h2 : Ca / (W : ℝ) ^ 2 ≤ Cm / (W : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
    linarith
  -- the gap step
  have hgap := cel_gap_lower (b := b) (E := E) hp hp' hK hT hA
  have hreal : c * c' / 2 / W * Q ≤ c / W * G + Cm / W * F := by
    have hcW : 0 ≤ c / W := div_nonneg hc.le hW0
    have h1 := mul_le_mul_of_nonneg_left hgap hcW
    have h2 : 8 * c * c' / W * F ≤ Cm / W * F :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (le_max_right _ _) hW0) hF0
    have e1 : c * c' / 2 / W * Q = c / W * (c' * (H ^ 2 / γ ^ p / 2)) := by
      simp only [Q]; ring
    have e2 : c / W * (G + 8 * c' * F) = c / W * G + 8 * c * c' / W * F := by ring
    rw [e1]
    linarith
  have hGnn : 0 ≤ c / W * G + Cm / W * F := (mul_nonneg (by positivity) hQ0).trans hreal
  calc ∫⁻ ν, ENNReal.ofReal (fracTrace p ((freshL b E X ν)ᴴ * A * freshL b E X ν))
          ∂freshLaw W b + ENNReal.ofReal (c * c' / 2 / W) * ENNReal.ofReal Q
      = ∫⁻ ν, ENNReal.ofReal (fracTrace p ((freshL b E X ν)ᴴ * A * freshL b E X ν))
          ∂freshLaw W b + ENNReal.ofReal (c * c' / 2 / W * Q) := by
        rw [ENNReal.ofReal_mul (by positivity)]
    _ ≤ ∫⁻ ν, ENNReal.ofReal (fracTrace p ((freshL b E X ν)ᴴ * A * freshL b E X ν))
          ∂freshLaw W b + (ENNReal.ofReal (c / W * G) + ENNReal.ofReal (Cm / W * F)) := by
        gcongr
        exact (ENNReal.ofReal_le_ofReal hreal).trans ENNReal.ofReal_add_le
    _ = (∫⁻ ν, ENNReal.ofReal (fracTrace p ((freshL b E X ν)ᴴ * A * freshL b E X ν))
          ∂freshLaw W b + ENNReal.ofReal (c / W * G)) + ENNReal.ofReal (Cm / W * F) := by
        rw [add_assoc]
    _ ≤ ENNReal.ofReal ((1 + Cm * δ + Cm / (W : ℝ) ^ 2) * H) + ENNReal.ofReal (Cm / W) *
          ENNReal.ofReal F := by
        rw [← ENNReal.ofReal_mul (div_nonneg (le_max_of_le_left hCa) hW0)]
        gcongr
        exact hJ1.trans (ENNReal.ofReal_le_ofReal hmean')

end BlockBand.Endpoints
