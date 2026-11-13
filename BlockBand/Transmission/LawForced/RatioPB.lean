module

public import BlockBand.Transmission.LawForced.RatioP

/-!
# The `κ ≡ 0` one-layer drift: `ratio_layer_P`

* `wmErr_gW_le`: `wmErr` at `G = gW hT Λ` is `≤ (4(Λ̂+lamLip) + 2Λ̂ + c_qΛ̂)P³v³`;
* `pv_mono`: `P^a v^b ≤ P^c v^d` for `a ≤ c`, `d ≤ b`;
* **`ratio_layer_P`**.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawForced

open Matrix Finset MeasureTheory
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers
open BlockBand.Transmission.LawDuality BlockBand.Transmission.Generator
open BlockBand.Transmission.SourceMixing BlockBand.Transmission.PassiveCovariance
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {p W : ℕ}

theorem pv_mono {P v : ℝ} (hP : 1 ≤ P) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) {a b c d : ℕ} (hac : a ≤ c)
    (hdb : d ≤ b) : P ^ a * v ^ b ≤ P ^ c * v ^ d :=
  mul_le_mul (pow_le_pow_right₀ hP hac) (pow_le_pow_of_le_one hv0 hv1 hdb) (by positivity)
    (by positivity)

theorem wmErr_gW_le {z : DualCoord p} (hz : IsRatioRange z.1 z.2) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) (hW : 1 ≤ W) {X : Matrix (Fin W) (Fin W) ℂ}
    (hX : (passiveY X).PosSemidef) (hT : (passiveTransmission b E X).PosSemidef) (s : ℂ)
    {cq : ℝ} (hcq : 0 ≤ cq) (hq : passiveMass b E X ≤ cq * (passiveTransmission b E X).trace.re) :
    wmErr b E X (gW hT fun k => dualLam z (ts_lam hT k)) ≤
      (4 * (lamHat z + lamLip z) + 2 * lamHat z + cq * lamHat z) *
        (ratioP b E s X ^ 3 * (Real.sqrt W)⁻¹ ^ 3) := by
  obtain ⟨hP1, hgP, -, he, -, hqW, hτ, -⟩ := ratio_atoms hb0 hb h1 h2 hW hX s hcq hq
  have ht1 := ts_lam_le_one hT (one_sub_passiveTransmission_posSemidef b E X)
  obtain ⟨hG0, hGl⟩ := re_trace_gW_le hz hT ht1
  have hGf := norm_trace_gW_f_le hz hT ht1 (passiveF b E X)
  set P := ratioP b E s X
  set v := (Real.sqrt W)⁻¹
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hsW : 1 ≤ Real.sqrt W := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt hWr
  have hv0 : 0 ≤ v := inv_nonneg.2 (by linarith)
  have hv1 : v ≤ 1 := inv_le_one_of_one_le₀ hsW
  have hWi : (W : ℝ)⁻¹ = v ^ 2 := by
    rw [inv_pow, Real.sq_sqrt (by linarith)]
  have hP0 : 0 ≤ P := by linarith
  have hΛ := lamHat_nonneg hz
  have hLz := lamLip_nonneg hz
  set G := gW hT fun k => dualLam z (ts_lam hT k)
  set e := jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2
  have he0 : 0 ≤ e := add_nonneg (norm_nonneg _) (by positivity)
  have hg0 : 0 ≤ (passiveTransmission b E X).trace.re := (mm_trace_posSemidef hT).1
  have hGP : G.trace.re ≤ lamHat z * P := hGl.trans (mul_le_mul_of_nonneg_left hgP hΛ)
  have hτ0 : 0 ≤ layerTau b E X := by unfold layerTau hsSandwich; positivity
  have hGf' : ‖(G * passiveF b E X).trace‖ ≤ (lamHat z + lamLip z) * (4 * P * v) :=
    hGf.trans (mul_le_mul_of_nonneg_left hτ (by positivity))
  have hq0 : 0 ≤ passiveMass b E X / W := div_nonneg (passiveMass_nonneg b E hX) (by positivity)
  have t1 : e * ‖(G * passiveF b E X).trace‖ ≤ 4 * (lamHat z + lamLip z) * (P ^ 2 * v ^ 3) := by
    calc e * ‖(G * passiveF b E X).trace‖ ≤ (P * v ^ 2) * ((lamHat z + lamLip z) * (4 * P * v)) :=
          mul_le_mul he hGf' (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have t2 : e ^ 2 * G.trace.re ≤ lamHat z * (P ^ 3 * v ^ 4) := by
    calc e ^ 2 * G.trace.re ≤ (P * v ^ 2) ^ 2 * (lamHat z * P) :=
          mul_le_mul (pow_le_pow_left₀ he0 he 2) hGP hG0 (by positivity)
      _ = _ := by ring
  have t3 : e * passiveMass b E X * G.trace.re / W ≤ cq * lamHat z * (P ^ 3 * v ^ 4) := by
    have e3 : e * passiveMass b E X * G.trace.re / W = e * (passiveMass b E X / W) * G.trace.re :=
      by ring
    rw [e3]
    calc e * (passiveMass b E X / W) * G.trace.re ≤ (P * v ^ 2) * (cq * P * v ^ 2) *
          (lamHat z * P) :=
          mul_le_mul (mul_le_mul he hqW hq0 (by positivity)) hGP hG0 (by positivity)
      _ = _ := by ring
  have t4 : (W : ℝ)⁻¹ ^ 2 * G.trace.re ≤ lamHat z * (P ^ 1 * v ^ 4) := by
    rw [hWi]
    calc (v ^ 2) ^ 2 * G.trace.re ≤ (v ^ 2) ^ 2 * (lamHat z * P) :=
          mul_le_mul_of_nonneg_left hGP (by positivity)
      _ = _ := by ring
  have m1 := mul_le_mul_of_nonneg_left (pv_mono hP1 hv0 hv1 (a := 2) (b := 3) (c := 3) (d := 3)
    (by norm_num) le_rfl) (show 0 ≤ 4 * (lamHat z + lamLip z) by positivity)
  have m2 := mul_le_mul_of_nonneg_left (pv_mono hP1 hv0 hv1 (a := 3) (b := 4) (c := 3) (d := 3)
    le_rfl (by norm_num)) hΛ
  have m3 := mul_le_mul_of_nonneg_left (pv_mono hP1 hv0 hv1 (a := 3) (b := 4) (c := 3) (d := 3)
    le_rfl (by norm_num)) (mul_nonneg hcq hΛ)
  have m4 := mul_le_mul_of_nonneg_left (pv_mono hP1 hv0 hv1 (a := 1) (b := 4) (c := 3) (d := 3)
    (by norm_num) (by norm_num)) hΛ
  unfold wmErr
  linarith

theorem ratio_sigma_le {z : DualCoord p} (hz : IsRatioRange z.1 z.2)
    {T : Matrix (Fin W) (Fin W) ℂ} (hT : T.PosSemidef) (ht1 : ∀ i, ts_lam hT i ≤ 1)
    (Ub : Matrix (Fin W) (Fin W) ℂ) {a Cb P v Ua Lw κy κU κL : ℝ} (ha : 0 ≤ a) (hCb : 0 ≤ Cb)
    (hκy : 0 ≤ κy) (hκU : 0 ≤ κU) (hκL : 0 ≤ κL)
    (hP : 1 ≤ P) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hg : T.trace.re ≤ P)
    (hsg : Real.sqrt T.trace.re ≤ P) (hy : a * T.trace.re ≤ κy * P * v ^ 2)
    (hUa : ‖Ub - (((1 + a * T.trace.re)⁻¹ : ℝ) : ℂ) • 1‖ ≤ Ua) (hU : Ua ≤ κU * P * v ^ 2)
    (hLw : ‖((gW hT fun k => dualLam z (ts_lam hT k)) * Ub).trace -
          (((1 + a * T.trace.re)⁻¹ : ℝ) : ℂ) * (gW hT fun k => dualLam z (ts_lam hT k)).trace‖ ≤
        Lw) (hL : Lw ≤ κL * P ^ 3 * v ^ 3) :
    Cb * v * (lamHat z * T.trace.re) + Cb * v * T.trace.re +
        (|linB z (ts_lam hT) (sand hT Ub - dmat (ts_lam hT))| + hsSandwich T (Ub - 1)) ≤
      (Cb * (lamHat z + 1) + κL + κy * lamHat z + κU + κy) * P ^ 3 * v := by
  have hΛ := lamHat_nonneg hz
  have hg0 : 0 ≤ T.trace.re := by
    rw [← ts_sum_lam hT]; exact Finset.sum_nonneg fun k _ => ts_lam_nonneg hT k
  have hy0 : 0 ≤ a * T.trace.re := mul_nonneg ha hg0
  obtain ⟨c0, c1, -⟩ := meanC_scalar hy0
  have hP0 : 0 ≤ P := by linarith
  have l2 := (linB_bracket_le hz hT ht1 Ub ha).2
  have hn := norm_sub_one_le c0 hUa
  have hs : hsSandwich T (Ub - 1) ≤ ‖Ub - 1‖ * Real.sqrt T.trace.re := by
    have h := frobSq_sand_le hT ht1 (Ub - 1)
    rw [frobSq_sand] at h
    have h0 : 0 ≤ hsSandwich T (Ub - 1) := Real.sqrt_nonneg _
    calc hsSandwich T (Ub - 1) = Real.sqrt (hsSandwich T (Ub - 1) ^ 2) := (Real.sqrt_sq h0).symm
      _ ≤ Real.sqrt (‖Ub - 1‖ ^ 2 * T.trace.re) := Real.sqrt_le_sqrt h
      _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  have hUa0 : 0 ≤ Ua := (norm_nonneg _).trans hUa
  have hLw0 : 0 ≤ Lw := (norm_nonneg _).trans hLw
  have hsg0 := Real.sqrt_nonneg T.trace.re
  have a1 : Cb * v * (lamHat z * T.trace.re) ≤ Cb * lamHat z * (P ^ 1 * v ^ 1) := by
    calc Cb * v * (lamHat z * T.trace.re) ≤ Cb * v * (lamHat z * P) := by gcongr
      _ = _ := by ring
  have a2 : Cb * v * T.trace.re ≤ Cb * (P ^ 1 * v ^ 1) := by
    calc Cb * v * T.trace.re ≤ Cb * v * P := by gcongr
      _ = _ := by ring
  have a3 : a * T.trace.re * (lamHat z * T.trace.re) ≤ κy * lamHat z * (P ^ 2 * v ^ 2) := by
    calc a * T.trace.re * (lamHat z * T.trace.re) ≤ (κy * P * v ^ 2) * (lamHat z * P) :=
          mul_le_mul hy (mul_le_mul_of_nonneg_left hg hΛ) (by positivity) (hy0.trans hy)
      _ = _ := by ring
  have a4 : ‖Ub - 1‖ * Real.sqrt T.trace.re ≤ (κU + κy) * (P ^ 2 * v ^ 2) := by
    have hb : ‖Ub - 1‖ ≤ (κU + κy) * P * v ^ 2 := by linarith
    calc ‖Ub - 1‖ * Real.sqrt T.trace.re ≤ ((κU + κy) * P * v ^ 2) * P :=
          mul_le_mul hb hsg hsg0 ((norm_nonneg _).trans hb)
      _ = _ := by ring
  have m1 := mul_le_mul_of_nonneg_left (pv_mono hP hv0 hv1 (a := 1) (b := 1) (c := 3) (d := 1)
    (by norm_num) le_rfl) (mul_nonneg hCb hΛ)
  have m2 := mul_le_mul_of_nonneg_left (pv_mono hP hv0 hv1 (a := 1) (b := 1) (c := 3) (d := 1)
    (by norm_num) le_rfl) hCb
  have m3 := mul_le_mul_of_nonneg_left (pv_mono hP hv0 hv1 (a := 2) (b := 2) (c := 3) (d := 1)
    (by norm_num) (by norm_num)) (mul_nonneg hκy hΛ)
  have m4 := mul_le_mul_of_nonneg_left (pv_mono hP hv0 hv1 (a := 2) (b := 2) (c := 3) (d := 1)
    (by norm_num) (by norm_num)) (add_nonneg hκU hκy)
  have m5 := mul_le_mul_of_nonneg_left (pv_mono hP hv0 hv1 (a := 3) (b := 3) (c := 3) (d := 1)
    le_rfl (by norm_num)) hκL
  have hL' : Lw ≤ κL * (P ^ 3 * v ^ 3) := by linarith
  simp only [pow_one] at m1 m2 a1 a2 m3 m4 m5 ⊢
  nlinarith

/-- The constants of `ratio_layer_P`. -/
def ratioKP (z : DualCoord p) (Cb Cσ Cε Cu CD cq : ℝ) : ℝ :=
  ratioK (441 * (1 + quadK z + cubK z) ^ 3) (quadK z) (lamHat z)
    (Cb * (lamHat z + 1) + Cu * (4 * (lamHat z + lamLip z) + 2 * lamHat z + cq * lamHat z) +
      CD / 2 * lamHat z + Cu * (1 + cq) + CD / 2)
    (CD / 2) (Cu * (1 + cq)) (Cu * (4 * (lamHat z + lamLip z) + 2 * lamHat z + cq * lamHat z))
    (Cε * (3 + cq)) (2 * Cσ)

/-- **The `κ ≡ 0` one-layer drift against `P²⁷W^{-3/2}`** (deterministic passive `X`). -/
theorem ratio_layer_P {z : DualCoord p} (hz : z ∈ dualChamber p) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hW : 1 ≤ W) (h1 : -2 < E) (h2 : E < 2) {X : Matrix (Fin W) (Fin W) ℂ}
    (hX : (passiveY X).PosSemidef)
    (hUi : ∀ i j, Integrable (fun ω => freshU b E X ω i j) (freshLaw W b))
    (hU2 : Integrable (fun ω => ‖freshU b E X ω‖ ^ 2) (freshLaw W b)) {Cb : ℝ} (hCb : 0 ≤ Cb)
    (hB : ∀ k : ℕ, (k = 3 ∨ k = 9) → ∀ u v : Fin W → ℂ, eLpNorm (fun ω => bilinear u
        (freshU b E X ω - matrixExpect (freshLaw W b) (freshU b E X)) v)
        (ENNReal.ofReal (k : ℝ)) (freshLaw W b) ≤
      ENNReal.ofReal (Cb / Real.sqrt W * vecNorm u * vecNorm v))
    (s σm : ℂ) {Cσ : ℝ} (hσm : ‖σm‖ ≤ Cσ) {Cε : ℝ} (hCε : 0 ≤ Cε)
    (hcov : ∀ v₁ v₂ v₃ v₄ : Fin W → ℂ, ‖bilinearCovariance (freshLaw W b) (freshU b E X)
        v₁ v₂ v₃ v₄ - ((((transportD0 b E / (2 * W) : ℝ)) : ℂ) *
          (crossedTensor v₁ v₂ v₃ v₄ 1 (1 - passiveTransmission b E X) +
            crossedTensor v₁ v₂ v₃ v₄ (1 - passiveTransmission b E X) 1) +
          σm / W * crossedTensor v₁ v₂ v₃ v₄ (passiveF b E X) (passiveF b E X) +
          conj σm / W * crossedTensor v₁ v₂ v₃ v₄ (passiveF b E X)ᴴ (passiveF b E X)ᴴ)‖ ≤
        Cε * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * (jetDistance0 b E X + jetDistance1 b E s X +
          passiveMass b E X / W)) * fourNorm v₁ v₂ v₃ v₄)
    {Cu : ℝ} (hCu : 0 ≤ Cu) (hUa : ‖matrixExpect (freshLaw W b) (freshU b E X) -
      ((meanC b E X : ℝ) : ℂ) • 1‖ ≤
        Cu * (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2 + passiveMass b E X / W))
    (hwm : ∀ G : Matrix (Fin W) (Fin W) ℂ, G.PosSemidef →
      ‖(G * matrixExpect (freshLaw W b) (freshU b E X)).trace -
        ((meanC b E X : ℝ) : ℂ) * G.trace‖ ≤ Cu * wmErr b E X G)
    {CD cq : ℝ} (hDC : transportD0 b E ≤ CD) (hcq : 0 ≤ cq)
    (hq : passiveMass b E X ≤ cq * (passiveTransmission b E X).trace.re) (u : ℝ) :
    |∫ ω, transmissionRatio z.1 z.2 (traceMeasure (passiveTransmission b E (freshSchur E X ω)))
        ∂freshLaw W b - transmissionRatio z.1 z.2 (traceMeasure (passiveTransmission b E X)) -
        ratioDrift (transportD0 b E) E (fun _ => 0) u z
          (traceMeasure (passiveTransmission b E X)) / W| ≤
      ratioKP z Cb Cσ Cε Cu CD cq * (ratioP b E s X ^ 27 * (Real.sqrt W)⁻¹ ^ 3) := by
  have hzr : IsRatioRange z.1 z.2 := IsRatioParameter.isRatioRange hz
  have hT := passiveTransmission_posSemidef (b := b) (by linarith) h1 h2 hX
  have ht1 := ts_lam_le_one hT (one_sub_passiveTransmission_posSemidef b E X)
  obtain ⟨hP1, hgP, hsg, he, hd1, hqW, hτ, hhs⟩ := ratio_atoms hb0 hb h1 h2 hW hX s hcq hq
  set P := ratioP b E s X
  set g := (passiveTransmission b E X).trace.re
  have hg0 : 0 ≤ g := (mm_trace_posSemidef hT).1
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hsW : 1 ≤ Real.sqrt W := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt hWr
  set v := (Real.sqrt W)⁻¹
  have hv0 : 0 ≤ v := inv_nonneg.2 (by linarith)
  have hv1 : v ≤ 1 := inv_le_one_of_one_le₀ hsW
  have hWi : (W : ℝ)⁻¹ = v ^ 2 := by rw [inv_pow, Real.sq_sqrt (by linarith)]
  have hP0 : 0 ≤ P := by linarith
  have hΛ := lamHat_nonneg hzr
  have hLz := lamLip_nonneg hzr
  have hσ0 : 0 ≤ Cσ := (norm_nonneg _).trans hσm
  have hD0 : 0 ≤ transportD0 b E := by
    have : 0 < 4 - E ^ 2 := by nlinarith
    unfold transportD0; positivity
  have hCD : 0 ≤ CD := hD0.trans hDC
  set a := transportD0 b E / (2 * W)
  have ha : 0 ≤ a := by positivity
  have hc : meanC b E X = (1 + a * g)⁻¹ := by
    rw [meanC_eq hb0 hb h1 h2]
    show (1 + transportD0 b E * g / (2 * W))⁻¹ = (1 + a * g)⁻¹
    simp only [a]; ring
  -- the atoms
  have hy : a * g ≤ CD / 2 * P * v ^ 2 := by
    have e : a * g = transportD0 b E * g * (W : ℝ)⁻¹ / 2 := by simp only [a]; ring
    rw [e, hWi]
    have := mul_le_mul hDC hgP hg0 hCD
    have := mul_le_mul_of_nonneg_right this (sq_nonneg v)
    linarith
  set Ua := Cu * (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2 + passiveMass b E X / W)
  have hU : Ua ≤ Cu * (1 + cq) * P * v ^ 2 := by
    have := mul_le_mul_of_nonneg_left (add_le_add he hqW) hCu
    simp only [Ua]; linarith
  have hU0 : 0 ≤ Ua := (norm_nonneg _).trans hUa
  set G := gW hT fun k => dualLam z (ts_lam hT k)
  have hG := gW_dualLam_posSemidef hzr hT ht1
  set Lw := Cu * wmErr b E X G
  have hLw' := hwm G hG
  have hL : Lw ≤ Cu * (4 * (lamHat z + lamLip z) + 2 * lamHat z + cq * lamHat z) * P ^ 3 *
      v ^ 3 := by
    have := mul_le_mul_of_nonneg_left (wmErr_gW_le hzr hb0 hb h1 h2 hW hX hT s hcq hq) hCu
    simp only [Lw]; linarith
  have hL0 : 0 ≤ Lw := (norm_nonneg _).trans hLw'
  set ε := Cε * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * (jetDistance0 b E X + jetDistance1 b E s X +
    passiveMass b E X / W))
  have hε : ε ≤ Cε * (3 + cq) * P * v ^ 4 := by
    have hd0 : jetDistance0 b E X ≤ P * v ^ 2 := by
      have : 0 ≤ (W : ℝ)⁻¹ ^ 2 := by positivity
      linarith
    have hin : (W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * (jetDistance0 b E X + jetDistance1 b E s X +
        passiveMass b E X / W) ≤ (3 + cq) * P * v ^ 4 := by
      rw [hWi]
      have h4 : v ^ 2 * (jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W) ≤
          v ^ 2 * (P * v ^ 2 + P * v ^ 2 + cq * P * v ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg v)
      have h5 : (v ^ 2) ^ 2 ≤ P * v ^ 4 := by
        have := mul_le_mul_of_nonneg_right hP1 (show 0 ≤ v ^ 4 by positivity)
        have e : (v ^ 2) ^ 2 = v ^ 4 := by ring
        linarith
      linarith
    have := mul_le_mul_of_nonneg_left hin hCε
    simp only [ε]; linarith
  set S := ‖σm / W‖ + ‖conj σm / W‖
  have hS : S ≤ 2 * Cσ * v ^ 2 := by
    simp only [S]
    rw [norm_div, norm_div, Complex.norm_conj, Complex.norm_natCast, div_eq_mul_inv, hWi]
    have := mul_le_mul_of_nonneg_right hσm (sq_nonneg v)
    linarith
  -- moments of `M`
  have hUm := measurable_freshU b E X
  have hBk := fun k (hk : k = 3 ∨ k = 9) =>
    ratioMf_moment hzr hT ht1 hUm k (by rcases hk with h | h <;> omega)
      (by positivity : 0 ≤ Cb / Real.sqrt W) (hB k hk)
  obtain ⟨i3, m3⟩ := hBk 3 (Or.inl rfl)
  obtain ⟨i9, m9⟩ := hBk 9 (Or.inr rfl)
  set σ := Cb / Real.sqrt W * (lamHat z * g) + Cb / Real.sqrt W * g +
    (|linB z (ts_lam hT) (sand hT (matrixExpect (freshLaw W b) (freshU b E X)) - dmat (ts_lam hT))| +
      hsSandwich (passiveTransmission b E X) (matrixExpect (freshLaw W b) (freshU b E X) - 1))
  have hσ0 : 0 ≤ σ := by
    have : 0 ≤ hsSandwich (passiveTransmission b E X)
        (matrixExpect (freshLaw W b) (freshU b E X) - 1) := Real.sqrt_nonneg _
    positivity
  rw [hc] at hUa hLw'
  have hσ : σ ≤ (Cb * (lamHat z + 1) +
      Cu * (4 * (lamHat z + lamLip z) + 2 * lamHat z + cq * lamHat z) + CD / 2 * lamHat z +
      Cu * (1 + cq) + CD / 2) * P ^ 3 * v := by
    have e : Cb / Real.sqrt W = Cb * v := div_eq_mul_inv _ _
    simp only [σ, e]
    exact ratio_sigma_le hzr hT ht1 _ ha hCb (by positivity) (by positivity) (by positivity)
      hP1 hv0 hv1 hgP hsg hy hUa hU hLw' hL
  have hI : ∫ ω, (ratioMf z (ts_lam hT) (sand hT (freshU b E X ω)) ^ 3 +
      ratioMf z (ts_lam hT) (sand hT (freshU b E X ω)) ^ 9) ∂freshLaw W b ≤ σ ^ 3 + σ ^ 9 := by
    rw [integral_add i3 i9]; exact add_le_add m3 m9
  rw [← hc] at hUa hLw'
  have hpt := ratio_layer_point hz hb0 hb hW h1 h2 hX hT hUi hU2 (i3.add i9) σm hcov hUa hLw' u
  refine hpt.trans ?_
  have hτ0 : 0 ≤ layerTau b E X := by unfold layerTau hsSandwich; positivity
  have hs0 : 0 ≤ hsSandwich (passiveTransmission b E X) (passiveF b E X) := Real.sqrt_nonneg _
  have hK : 0 ≤ 4 * (lamHat z + lamLip z) + 2 * lamHat z + cq * lamHat z := by
    have := mul_nonneg hcq hΛ; linarith
  have hκL : 0 ≤ Cu * (4 * (lamHat z + lamLip z) + 2 * lamHat z + cq * lamHat z) :=
    mul_nonneg hCu hK
  have hκM : 0 ≤ Cb * (lamHat z + 1) +
      Cu * (4 * (lamHat z + lamLip z) + 2 * lamHat z + cq * lamHat z) + CD / 2 * lamHat z +
      Cu * (1 + cq) + CD / 2 := by
    have := mul_nonneg hCb (add_nonneg hΛ zero_le_one)
    have := mul_nonneg (div_nonneg hCD zero_le_two) hΛ
    have := mul_nonneg hCu (add_nonneg zero_le_one hcq)
    have := div_nonneg hCD zero_le_two
    linarith
  exact ratio_rhs_le z (mul_nonneg (by norm_num)
    (pow_nonneg (by linarith [quadK_nonneg z, cubK_nonneg hzr]) 3)) hκM (div_nonneg hCD zero_le_two) hκL
    (mul_nonneg hCε (by linarith)) (by linarith) hΛ hP1 hv0 hv1 hg0 hgP hs0 hhs hτ0 hτ (mul_nonneg ha hg0) hy
    hU0 hU hL0 hL hε hS hσ0 hσ hI

end BlockBand.Transmission.LawForced
