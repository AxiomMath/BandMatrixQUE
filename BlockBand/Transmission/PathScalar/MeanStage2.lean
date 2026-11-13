module

public import BlockBand.Transmission.PathScalar.MeanStage1

/-!
# The passive mean map, stage 2: the sharp contraction

With stage 1's localization, `w`, `u`, `ζ` and both Herglotz masses are within `O(δ₀ + ε)` of
their matched values (`stage_two_local`, `stage_two_mass`), so `κ = k₋ + O(δ)` and
`|T| ≤ d_* + O(δ)`, giving `|1 - κT| ≥ b + kGap/2` (`|k₋| d_* ≤ 1 - b - kGap`, `MeanBulk`).
* `mean_stage_two`: `|u - a| ≤ ρ δ₀ + C ε` with `ρ = rhoMean b κ < 1`;
* `passiveMean_stability`: the same with existential constants depending on `b, κ, C_v` only.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PathScalar

open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.Bridge
open scoped ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

/-!
## Stage 2 constants
-/
def C3c (b κ Cv : ℝ) : ℝ := C1c b κ Cv / etaLow b κ
def C2c (b κ Cv : ℝ) : ℝ := C3c b κ Cv + 1 / etaLow b κ
def C4c (b κ Cv : ℝ) : ℝ := C1c b κ Cv + C2c b κ Cv
def Lc (b κ Cv : ℝ) : ℝ := 2 * ((C1c b κ Cv + 1) + 2 * C4c b κ Cv) / etaLow b κ
def Mc (b κ Cv : ℝ) : ℝ := Lc b κ Cv + 2 * C3c b κ Cv + C3c b κ Cv * Lc b κ Cv
def deltaS (b κ Cv : ℝ) : ℝ :=
  min 1 (min (etaLow b κ / (2 * C4c b κ Cv)) (min (kGap b κ / (2 * Mc b κ Cv))
    (min (1 / C3c b κ Cv) (kGap b κ / (4 * b * C3c b κ Cv)))))
def rhoMean (b κ : ℝ) : ℝ := (b + kGap b κ / 4) / (b + kGap b κ / 2)
def K7c (b κ Cv : ℝ) : ℝ := 1 + 2 * (2 + Lc b κ Cv)
def Cfin (b κ Cv : ℝ) : ℝ := rhoMean b κ * K7c b κ Cv + 2

section Consts2
variable {b κ Cv : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ) (hCv : 0 ≤ Cv)
include hb0 hb hκ hCv

theorem C1c_pos : 0 < C1c b κ Cv := by
  have := etaLow_pos (by linarith : b < 1) hκ
  have hQ := Q0c_pos hb0 hb hκ hCv
  have hθ := theta1_lt_one hb0 hb hκ hCv
  have hT : 0 ≤ Tmax b κ Cv := by unfold Tmax; positivity
  unfold C1c; apply div_pos (by positivity) (by linarith)

theorem consts2_pos : 0 < C3c b κ Cv ∧ 0 < C2c b κ Cv ∧ 0 < C4c b κ Cv ∧ 0 < Lc b κ Cv ∧
    0 < Mc b κ Cv ∧ 0 < deltaS b κ Cv := by
  have hη := etaLow_pos (by linarith : b < 1) hκ
  have h1 := C1c_pos hb0 hb hκ hCv
  have hg := kGap_pos hb0 hb hκ
  have h3 : 0 < C3c b κ Cv := by unfold C3c; positivity
  have h2 : 0 < C2c b κ Cv := by unfold C2c; positivity
  have h4 : 0 < C4c b κ Cv := by unfold C4c; positivity
  have hL : 0 < Lc b κ Cv := by unfold Lc; positivity
  have hM : 0 < Mc b κ Cv := by unfold Mc; positivity
  refine ⟨h3, h2, h4, hL, hM, ?_⟩
  unfold deltaS
  exact lt_min one_pos (lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity)
    (by positivity))))

end Consts2

theorem rhoMean_lt_one {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ) :
    0 ≤ rhoMean b κ ∧ rhoMean b κ < 1 := by
  have hg := kGap_pos hb0 hb hκ
  unfold rhoMean
  exact ⟨by positivity, (div_lt_one (by positivity)).2 (by linarith)⟩

theorem A_sharp {A η d C₁ C₄ δ ηl : ℝ} (hηl : 0 < ηl) (hηle : ηl ≤ η)
    (hd2 : d ≤ 2) (hC4δ : C₄ * δ ≤ ηl / 2) (hδ0 : 0 ≤ δ) (hC₄ : 0 ≤ C₄) (hC1 : 0 ≤ C₁)
    (h : (η - C₄ * δ) * A ≤ η * d + (C₁ + 1) * δ) :
    A ≤ d + 2 * ((C₁ + 1) + 2 * C₄) / ηl * δ := by
  set L := 2 * ((C₁ + 1) + 2 * C₄) / ηl
  have hL : ηl * L = 2 * ((C₁ + 1) + 2 * C₄) := by simp only [L]; field_simp
  have hL0 : 0 ≤ L := by positivity
  have hpos : 0 < η - C₄ * δ := by linarith
  have key : η * d + (C₁ + 1) * δ ≤ (η - C₄ * δ) * (d + L * δ) := by
    have e1 : ηl * L * δ ≤ η * L * δ := by
      have := mul_le_mul_of_nonneg_right hηle (mul_nonneg hL0 hδ0); nlinarith
    have e2 : C₄ * δ * d ≤ 2 * (C₄ * δ) := by nlinarith [mul_nonneg hC₄ hδ0]
    have e3 : C₄ * δ * (L * δ) ≤ ηl / 2 * (L * δ) :=
      mul_le_mul_of_nonneg_right hC4δ (mul_nonneg hL0 hδ0)
    have e4 : ηl / 2 * (L * δ) = ((C₁ + 1) + 2 * C₄) * δ := by
      rw [show ηl / 2 * (L * δ) = (ηl * L) / 2 * δ by ring, hL]; ring
    nlinarith
  by_contra hc
  have := mul_lt_mul_of_pos_left (not_le.1 hc) hpos
  linarith

/-- The common hypotheses of the mean-step analysis. -/
structure MeanHyp {W : ℕ} (b κ E Cv ε δ₀ : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (v u : ℂ) : Prop where
  hb0 : 0 < b
  hb : b < 1 / 2
  hκ : 0 < κ
  hE : E ∈ bulkInterval κ
  hCv : 0 ≤ Cv
  hY : (passiveY X).PosSemidef
  hv0 : v.im ≤ 0
  hvC : ‖v‖ ≤ Cv
  hs : ‖u * (boundaryZ b E - (b : ℂ) * v) - 1‖ ≤ ε
  hr : ‖v - stieltjes X (zetaOf b E v u)‖ ≤ ε
  hε0 : 0 ≤ ε
  hε : ε ≤ eps1 b κ Cv
  hδ : jetDistance0 b E X ≤ δ₀
  hδ₁ : δ₀ ≤ b * etaLow b κ / 2
  hδs : δ₀ + ε ≤ deltaS b κ Cv

/-- Stage 2, local bounds: `w`, `u` and `ζ` near the matched point. -/
theorem stage_two_local {W : ℕ} {b κ E Cv ε δ₀ : ℝ} {X : Matrix (Fin W) (Fin W) ℂ} {v u : ℂ}
    (H : MeanHyp b κ E Cv ε δ₀ X v u) :
    ‖(boundaryZ b E - (b : ℂ) * v)⁻¹ - matchedA E‖ ≤ C3c b κ Cv * (δ₀ + ε) ∧
      ‖u - matchedA E‖ ≤ C2c b κ Cv * (δ₀ + ε) ∧
      etaZ b E - C4c b κ Cv * (δ₀ + ε) ≤ (zetaOf b E v u).im ∧
      ‖v - matchedA E‖ ≤ C1c b κ Cv * (δ₀ + ε) ∧ 0 < (zetaOf b E v u).im := by
  obtain ⟨hb0, hb, hκ, hE, hCv, hY, hv0, hvC, hs, hr, hε0, hε, hδ, hδ₁, hδs⟩ := H
  obtain ⟨hζQ, hv1⟩ := mean_stage_one hb0 hb hκ hE hCv hY hv0 hvC hs hr hε0 hε hδ hδ₁
  obtain ⟨hw1, hwn, -, -, -⟩ := stage_one_setup hb0 hb hκ hE hCv hv0 hvC hs hε0 hε
  have hηl := etaLow_pos (by linarith : b < 1) hκ
  have ha1 : ‖matchedA E‖ = 1 := bulk_norm_a hκ hE
  have hc : 0 < 1 - 2 * b := by linarith
  have hb1 : b ≤ 1 := by linarith
  set w := (boundaryZ b E - (b : ℂ) * v)⁻¹
  set δ := δ₀ + ε
  have hwa : w - matchedA E = (b : ℂ) * matchedA E * w * (v - matchedA E) := by
    linear_combination (-w) * bulk_a_mul (b := b) hκ hE + matchedA E * hw1
  have hwan : ‖w - matchedA E‖ ≤ C3c b κ Cv * δ := by
    rw [hwa, norm_mul, norm_mul, norm_mul, ha1, Complex.norm_real, Real.norm_of_nonneg hb0.le,
      mul_one]
    calc b * ‖w‖ * ‖v - matchedA E‖ ≤ 1 * (1 / etaLow b κ) * (C1c b κ Cv * δ) := by gcongr
      _ = C3c b κ Cv * δ := by unfold C3c; ring
  have hu2 : u - matchedA E = (w - matchedA E) + (u * (boundaryZ b E - (b : ℂ) * v) - 1) * w := by
    linear_combination (-u) * hw1
  have hun : ‖u - matchedA E‖ ≤ C2c b κ Cv * δ := by
    rw [hu2]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    have h1 : ‖u * (boundaryZ b E - (b : ℂ) * v) - 1‖ * ‖w‖ ≤ ε * (1 / etaLow b κ) :=
      mul_le_mul hs hwn (norm_nonneg _) hε0
    have h2 : ε * (1 / etaLow b κ) ≤ δ * (1 / etaLow b κ) := by
      gcongr; linarith [(norm_nonneg _).trans hδ]
    unfold C2c; linarith
  have hζz : zetaOf b E v u - boundaryZ b E =
      -((1 - 2 * b : ℝ) : ℂ) * (v - matchedA E) - (b : ℂ) * (u - matchedA E) := by
    rw [bulk_z_eq hκ hE]; simp only [zetaOf]; ring
  have hζzn : ‖zetaOf b E v u - boundaryZ b E‖ ≤ C4c b κ Cv * δ := by
    rw [hζz]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hc.le,
      Complex.norm_real, Real.norm_of_nonneg hb0.le]
    unfold C4c
    have e1 : (1 - 2 * b) * ‖v - matchedA E‖ ≤ 1 * (C1c b κ Cv * δ) :=
      mul_le_mul (by linarith) hv1 (norm_nonneg _) zero_le_one
    have e2 : b * ‖u - matchedA E‖ ≤ 1 * (C2c b κ Cv * δ) :=
      mul_le_mul hb1 hun (norm_nonneg _) zero_le_one
    linarith
  have hζim : etaZ b E - C4c b κ Cv * δ ≤ (zetaOf b E v u).im := by
    have e : (zetaOf b E v u).im = (boundaryZ b E).im + (zetaOf b E v u - boundaryZ b E).im := by
      simp
    rw [e]
    have := (neg_le_abs _).trans ((Complex.abs_im_le_norm _).trans hζzn)
    unfold etaZ; linarith
  have hζpos : 0 < (zetaOf b E v u).im :=
    lt_of_lt_of_le (by have := Q0c_pos hb0 hb hκ hCv; positivity) hζQ
  exact ⟨hwan, hun, hζim, hv1, hζpos⟩

theorem one_div_le_Lc {b κ Cv : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ) (hCv : 0 ≤ Cv) :
    1 / etaLow b κ ≤ Lc b κ Cv := by
  have hηl := etaLow_pos (by linarith : b < 1) hκ
  have h1 := C1c_pos hb0 hb hκ hCv
  have h4 := (consts2_pos hb0 hb hκ hCv).2.2.1
  unfold Lc
  apply div_le_div_of_nonneg_right _ hηl.le
  linarith

/-- Stage 2, the sharp Herglotz masses and `|T|`. -/
theorem stage_two_mass {W : ℕ} {b κ E Cv ε δ₀ : ℝ} {X : Matrix (Fin W) (Fin W) ℂ} {v u : ℂ}
    (H : MeanHyp b κ E Cv ε δ₀ X v u) :
    ‖crossTr X (zetaOf b E v u) (boundaryZ b E)‖ ≤ dStar b + Lc b κ Cv * (δ₀ + ε) := by
  obtain ⟨hwan, hun, hζim, hv1, hζpos⟩ := stage_two_local H
  obtain ⟨hb0, hb, hκ, hE, hCv, hY, hv0, hvC, hs, hr, hε0, hε, hδ, hδ₁, hδs⟩ := H
  obtain ⟨h3, h2', h4, hL, -, -⟩ := consts2_pos hb0 hb hκ hCv
  have h1c := C1c_pos hb0 hb hκ hCv
  have hηl := etaLow_pos (by linarith : b < 1) hκ
  have hηle := etaLow_le (by linarith : b < 1) hκ hE
  have hδ0 : 0 ≤ δ₀ := (norm_nonneg _).trans hδ
  set δ := δ₀ + ε with hδdef
  have hεδ : ε ≤ δ := by linarith
  have hδ4 : δ ≤ etaLow b κ / (2 * C4c b κ Cv) :=
    hδs.trans ((min_le_right _ _).trans (min_le_left _ _))
  obtain ⟨hA, hA₀⟩ := mass_bounds hb hκ hE hY hζpos hr hδ
  have hd0 : 0 ≤ dStar b := by rw [dStar]; exact div_nonneg zero_le_one (by linarith)
  have hd2 : dStar b ≤ 2 := by rw [dStar, div_le_iff₀ (by linarith)]; linarith
  have hC4δ : C4c b κ Cv * δ ≤ etaLow b κ / 2 := by
    rw [le_div_iff₀ (by positivity)] at hδ4; linarith
  have hAs : sqMass X (zetaOf b E v u) ≤ dStar b + Lc b κ Cv * δ := by
    have hvim : -v.im ≤ etaZ b E * dStar b + C1c b κ Cv * δ := by
      have e : -v.im = -(matchedA E).im - (v - matchedA E).im := by
        simp only [Complex.sub_im]; ring
      rw [e, bulk_im_a hb hκ hE]
      have := (neg_le_abs _).trans ((Complex.abs_im_le_norm (v - matchedA E)).trans hv1)
      linarith
    have hm := mul_le_mul_of_nonneg_right hζim (sqMass_nonneg X (zetaOf b E v u))
    have hA' : (etaZ b E - C4c b κ Cv * δ) * sqMass X (zetaOf b E v u) ≤
        etaZ b E * dStar b + (C1c b κ Cv + 1) * δ := by linarith
    exact A_sharp hηl hηle hd2 hC4δ (by positivity) h4.le h1c.le hA'
  have hA₀s : sqMass X (boundaryZ b E) ≤ dStar b + Lc b κ Cv * δ := by
    have hηpos : 0 < etaZ b E := hηl.trans_le hηle
    have hA₀' : sqMass X (boundaryZ b E) ≤ dStar b + δ₀ / etaZ b E := by
      have := div_le_div_of_nonneg_right hA₀ hηpos.le
      rwa [mul_div_cancel_left₀ _ hηpos.ne', add_div, mul_div_cancel_left₀ _ hηpos.ne'] at this
    have e1 : δ₀ / etaZ b E ≤ δ * (1 / etaLow b κ) := by
      have := div_le_div_of_nonneg_left hδ0 hηl hηle
      have : δ₀ / etaLow b κ ≤ δ / etaLow b κ := by gcongr; linarith
      rw [mul_one_div]; linarith
    have e2 : δ * (1 / etaLow b κ) ≤ δ * Lc b κ Cv :=
      mul_le_mul_of_nonneg_left (one_div_le_Lc hb0 hb hκ hCv) (by positivity)
    linarith
  have hsA := Real.sq_sqrt (sqMass_nonneg X (zetaOf b E v u))
  have hsA₀ := Real.sq_sqrt (sqMass_nonneg X (boundaryZ b E))
  have hT := norm_crossTr_le X (zetaOf b E v u) (boundaryZ b E)
  have hsq0 := sq_nonneg (Real.sqrt (sqMass X (zetaOf b E v u)) -
    Real.sqrt (sqMass X (boundaryZ b E)))
  have hsq : Real.sqrt (sqMass X (zetaOf b E v u)) * Real.sqrt (sqMass X (boundaryZ b E)) ≤
      (sqMass X (zetaOf b E v u) + sqMass X (boundaryZ b E)) / 2 := by
    linear_combination (1 / 2 : ℝ) * hsq0 + (1 / 2 : ℝ) * hsA + (1 / 2 : ℝ) * hsA₀
  linarith

/-- Stage 2, the final real arithmetic. -/
theorem stage_two_arith {b κ Cv kn κn Tn vn un wn den δ₀ ε : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) (hCv : 0 ≤ Cv) (hδ0 : 0 ≤ δ₀) (hε0 : 0 ≤ ε)
    (hδs : δ₀ + ε ≤ deltaS b κ Cv)
    (hκn : κn ≤ kn + C3c b κ Cv * (δ₀ + ε)) (hTn : Tn ≤ dStar b + Lc b κ Cv * (δ₀ + ε))
    (hTn0 : 0 ≤ Tn) (hvn0 : 0 ≤ vn) (hwn0 : 0 ≤ wn)
    (hkn0 : 0 ≤ kn) (hkn1 : kn ≤ 1) (hkd : kn * dStar b ≤ 1 - b - kGap b κ)
    (hwle : wn ≤ 1 + C3c b κ Cv * (δ₀ + ε)) (hden : 1 - κn * Tn ≤ den)
    (hn : vn * den ≤ δ₀ + ε + b * Tn * ε * wn) (hu : un ≤ b * wn * vn + ε * wn) :
    un ≤ rhoMean b κ * δ₀ + Cfin b κ Cv * ε := by
  obtain ⟨h3, -, -, hL, hM, -⟩ := consts2_pos hb0 hb hκ hCv
  have hg := kGap_pos hb0 hb hκ
  set δ := δ₀ + ε with hδdef
  have hδ0' : 0 ≤ δ := by linarith
  have hδ1 : δ ≤ 1 := hδs.trans (min_le_left _ _)
  have hδM : δ ≤ kGap b κ / (2 * Mc b κ Cv) :=
    hδs.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδ3 : δ ≤ 1 / C3c b κ Cv :=
    hδs.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_left _ _))))
  have hδb : δ ≤ kGap b κ / (4 * b * C3c b κ Cv) :=
    hδs.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_right _ _))))
  have hd0 : 0 ≤ dStar b := by rw [dStar]; exact div_nonneg zero_le_one (by linarith)
  have hd2 : dStar b ≤ 2 := by rw [dStar, div_le_iff₀ (by linarith)]; linarith
  set C3 := C3c b κ Cv
  set L := Lc b κ Cv
  have hC3δ : C3 * δ ≤ 1 := by rw [le_div_iff₀ h3] at hδ3; linarith
  have hC3δ0 : 0 ≤ C3 * δ := by positivity
  have hLδ0 : 0 ≤ L * δ := by positivity
  have hprod : κn * Tn ≤ 1 - b - kGap b κ / 2 := by
    have e1 : κn * Tn ≤ (kn + C3 * δ) * (dStar b + L * δ) :=
      mul_le_mul hκn hTn hTn0 (by positivity)
    have f1 : kn * (L * δ) ≤ L * δ := mul_le_of_le_one_left hLδ0 hkn1
    have f2 : C3 * δ * dStar b ≤ C3 * δ * 2 := mul_le_mul_of_nonneg_left hd2 hC3δ0
    have f3 : C3 * δ * (L * δ) ≤ C3 * δ * L := by
      have := mul_le_mul_of_nonneg_left hδ1 (mul_nonneg hC3δ0 hL.le)
      linarith [mul_comm (C3 * δ) L]
    have e2 : (kn + C3 * δ) * (dStar b + L * δ) ≤ kn * dStar b + Mc b κ Cv * δ := by
      have : Mc b κ Cv * δ = L * δ + 2 * (C3 * δ) + C3 * δ * L := by unfold Mc; ring
      rw [this]
      have ex : (kn + C3 * δ) * (dStar b + L * δ) =
          kn * dStar b + kn * (L * δ) + C3 * δ * dStar b + C3 * δ * (L * δ) := by ring
      rw [ex]; linarith
    have e3 : Mc b κ Cv * δ ≤ kGap b κ / 2 := by
      rw [le_div_iff₀ (by positivity)] at hδM; linarith
    linarith
  have hden' : b + kGap b κ / 2 ≤ den := by linarith
  have hwn2 : wn ≤ 2 := by linarith
  have hT2 : Tn ≤ 2 + L := by have := mul_le_mul_of_nonneg_left hδ1 hL.le; linarith
  have hb1 : b ≤ 1 := by linarith
  have f : b * Tn * ε * wn ≤ 2 * (2 + L) * ε := by
    have e : b * Tn ≤ 1 * (2 + L) := mul_le_mul hb1 hT2 hTn0 zero_le_one
    have e' : b * Tn * ε ≤ (2 + L) * ε := by
      have := mul_le_mul_of_nonneg_right e hε0; linarith
    have := mul_le_mul e' hwn2 hwn0 (by positivity)
    linarith
  have hrhs : vn * (b + kGap b κ / 2) ≤ δ₀ + K7c b κ Cv * ε := by
    have g : vn * (b + kGap b κ / 2) ≤ vn * den := mul_le_mul_of_nonneg_left hden' hvn0
    unfold K7c; linarith
  have hbw : b * wn ≤ b + kGap b κ / 4 := by
    have h' : b * (C3 * δ) ≤ kGap b κ / 4 := by
      rw [le_div_iff₀ (by positivity)] at hδb
      have : b * (C3 * δ) * 4 = δ * (4 * b * C3) := by ring
      linarith
    have := mul_le_mul_of_nonneg_left hwle hb0.le
    linarith
  have hpos : 0 < b + kGap b κ / 2 := by positivity
  have hv' : vn ≤ (δ₀ + K7c b κ Cv * ε) / (b + kGap b κ / 2) := by
    rw [le_div_iff₀ hpos]; exact hrhs
  have hq0 : 0 ≤ (δ₀ + K7c b κ Cv * ε) / (b + kGap b κ / 2) := hvn0.trans hv'
  calc un ≤ b * wn * vn + ε * wn := hu
    _ ≤ (b + kGap b κ / 4) * ((δ₀ + K7c b κ Cv * ε) / (b + kGap b κ / 2)) + ε * 2 := by
        have := mul_le_mul hbw hv' hvn0 (by positivity)
        have := mul_le_mul_of_nonneg_left hwn2 hε0
        linarith
    _ = rhoMean b κ * δ₀ + Cfin b κ Cv * ε := by
        unfold Cfin rhoMean; field_simp; ring

/-- **Stage 2 (sharp contraction)**: `|u - a| ≤ ρ δ₀ + C ε`, `ρ < 1`. -/
theorem mean_stage_two {W : ℕ} {b κ E Cv ε δ₀ : ℝ} {X : Matrix (Fin W) (Fin W) ℂ} {v u : ℂ}
    (H : MeanHyp b κ E Cv ε δ₀ X v u) :
    ‖u - matchedA E‖ ≤ rhoMean b κ * δ₀ + Cfin b κ Cv * ε := by
  obtain ⟨hwan, hun, hζim, hv1, hζpos⟩ := stage_two_local H
  have hTn := stage_two_mass H
  obtain ⟨hb0, hb, hκ, hE, hCv, hY, hv0, hvC, hs, hr, hε0, hε, hδ, hδ₁, hδs⟩ := H
  obtain ⟨h1, h2⟩ := bulk_bounds hκ hE
  obtain ⟨hw1, -, -, -, -⟩ := stage_one_setup hb0 hb hκ hE hCv hv0 hvC hs hε0 hε
  have ha1 : ‖matchedA E‖ = 1 := bulk_norm_a hκ hE
  have hδ0 : 0 ≤ δ₀ := (norm_nonneg _).trans hδ
  have hzpos : 0 < (boundaryZ b E).im := etaZ_pos b E (by linarith) h1 h2
  set w := (boundaryZ b E - (b : ℂ) * v)⁻¹
  set T := crossTr X (zetaOf b E v u) (boundaryZ b E)
  set κc : ℂ := ((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * matchedA E * w
  obtain ⟨hid1, hid2⟩ := mean_identity (a := matchedA E) (z := boundaryZ b E) (v := v) (u := u)
    (w := w) (fζ := stieltjes X (zetaOf b E v u)) (fz := stieltjes X (boundaryZ b E)) (T := T)
    (b := (b : ℂ)) (c := ((1 - 2 * b : ℝ) : ℂ)) (E := (E : ℂ)) hw1 (bulk_a_mul hκ hE)
    (bulk_z_eq hκ hE) (stieltjes_sub hY hζpos hzpos)
  have hwle : ‖w‖ ≤ 1 + C3c b κ Cv * (δ₀ + ε) := by
    have := norm_le_insert' w (matchedA E)
    rw [ha1] at this; linarith [norm_sub_rev w (matchedA E)]
  have hκk : κc - kMinus b E = (b : ℂ) ^ 2 * matchedA E * (w - matchedA E) := by
    simp only [κc, kMinus]; ring
  have hκn : ‖κc‖ ≤ ‖kMinus b E‖ + C3c b κ Cv * (δ₀ + ε) := by
    have hb2 : b ^ 2 ≤ 1 := by nlinarith
    have : ‖κc - kMinus b E‖ ≤ C3c b κ Cv * (δ₀ + ε) := by
      rw [hκk, norm_mul, norm_mul, ha1, norm_pow, Complex.norm_real, Real.norm_of_nonneg hb0.le,
        mul_one]
      calc b ^ 2 * ‖w - matchedA E‖ ≤ 1 * (C3c b κ Cv * (δ₀ + ε)) :=
            mul_le_mul hb2 hwan (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
    linarith [norm_le_insert' κc (kMinus b E), norm_sub_rev κc (kMinus b E)]
  have hkn1 : ‖kMinus b E‖ ≤ 1 := by
    have := norm_kMinus_lt b E hb0 hb h1 h2
    have : (1 - b) ^ 2 ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    linarith
  have hden : 1 - ‖κc‖ * ‖T‖ ≤ ‖1 - κc * T‖ := by
    have := norm_sub_norm_le (1 : ℂ) (κc * T)
    rw [norm_one, norm_mul] at this; linarith
  have hn : ‖v - matchedA E‖ * ‖1 - κc * T‖ ≤ δ₀ + ε + b * ‖T‖ * ε * ‖w‖ := by
    rw [← norm_mul, hid1]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hδ hr)) ?_)
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hb0.le]
    gcongr
  have hu : ‖u - matchedA E‖ ≤ b * ‖w‖ * ‖v - matchedA E‖ + ε * ‖w‖ := by
    rw [hid2]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_mul, norm_mul, ha1, Complex.norm_real, Real.norm_of_nonneg hb0.le]
    have := mul_le_mul_of_nonneg_right hs (norm_nonneg w)
    linarith
  exact stage_two_arith hb0 hb hκ hCv hδ0 hε0 hδs hκn hTn (norm_nonneg _)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hkn1 (bulk_kMinus hb0 hb hκ hE) hwle hden hn hu

/-- **Deterministic stability of the passive mean map** (branch selection included): any
approximate solution `(v, u)` of the one-port mean equations, with `Im v ≤ 0` and `|v| ≤ C_v`,
has `|u - a| ≤ ρ δ₀(X) + C ε` on `δ₀(X) ≤ d₀`, `ε ≤ ε₀`; `ρ < 1` and all constants depend
only on `b, κ, C_v`. -/
theorem passiveMean_stability {b κ Cv : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ)
    (hCv : 0 ≤ Cv) :
    ∃ d₀ ρ C ε₀ : ℝ, 0 < d₀ ∧ 0 ≤ ρ ∧ ρ < 1 ∧ 0 ≤ C ∧ 0 < ε₀ ∧
      ∀ (W : ℕ) (E : ℝ), E ∈ bulkInterval κ → ∀ X : Matrix (Fin W) (Fin W) ℂ,
        (passiveY X).PosSemidef → ∀ (v u : ℂ) (ε : ℝ), v.im ≤ 0 → ‖v‖ ≤ Cv →
          ‖u * (boundaryZ b E - (b : ℂ) * v) - 1‖ ≤ ε →
          ‖v - stieltjes X (zetaOf b E v u)‖ ≤ ε → 0 ≤ ε → ε ≤ ε₀ →
          jetDistance0 b E X ≤ d₀ → ‖u - matchedA E‖ ≤ ρ * jetDistance0 b E X + C * ε := by
  obtain ⟨-, -, -, -, -, hds⟩ := consts2_pos hb0 hb hκ hCv
  have hηl := etaLow_pos (by linarith : b < 1) hκ
  obtain ⟨hρ0, hρ1⟩ := rhoMean_lt_one hb0 hb hκ
  have he1 := eps1_pos hb0 hb hκ hCv
  have hCf : 0 ≤ Cfin b κ Cv := by
    obtain ⟨-, -, -, hL, -, -⟩ := consts2_pos hb0 hb hκ hCv
    unfold Cfin K7c; positivity
  refine ⟨min (b * etaLow b κ / 2) (deltaS b κ Cv / 2), rhoMean b κ, Cfin b κ Cv,
    min (eps1 b κ Cv) (deltaS b κ Cv / 2), lt_min (by positivity) (by positivity), hρ0, hρ1, hCf,
    lt_min he1 (by positivity), ?_⟩
  intro W E hE X hY v u ε hv0 hvC hs hr hε0 hε hδ
  exact mean_stage_two ⟨hb0, hb, hκ, hE, hCv, hY, hv0, hvC, hs, hr, hε0,
    hε.trans (min_le_left _ _), le_rfl, hδ.trans (min_le_left _ _),
    by linarith [hδ.trans (min_le_right _ _), hε.trans (min_le_right _ _)]⟩

end BlockBand.Transmission.PathScalar
