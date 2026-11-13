module

public import BlockBand.Transmission.PathScalar.MeanBulk

/-!
# The passive mean map, stage 1: branch identification

Unknowns: `v` (the physical mean), `u` (the port mean), `ζ = -E - cv - bu` (`zetaOf`). An
approximate solution has residuals `|u(z - bv) - 1| ≤ ε` and `|v - f(ζ)| ≤ ε`,
`f = stieltjes X`. The reference point is the matched value `(a, a)`, at which `ζ = z` and
the residual is `f(z) - a`, of size `δ₀(X)`.
* `PathScalar.mean_identity` (proved in the sibling module): `(v - a)(1 - κT) = (f(z) - a) + (v - f(ζ)) + bTsw` and
  `u - a = baw(v - a) + sw`, with `w = (z - bv)⁻¹`, `κ = c + b²aw`, `T = W⁻¹Tr M_ζ M_z`;
* `stage_one_weights`: the Herglotz masses give `|κ||T| ≤ θ₁ < 1` **globally**, from the two
  imaginary-part identities only (no a priori closeness to `a`);
* `mean_stage_one`: `|v - a| ≤ C₁(δ₀ + ε)`, and `Im ζ ≥ Q₀/2 > 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PathScalar

open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.Bridge
open scoped ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

/-- Crude-stage constants. -/
def h0c (Cv : ℝ) : ℝ := 1 / (2 + Cv) ^ 2
def Q0c (b κ Cv : ℝ) : ℝ := b * etaLow b κ * h0c Cv
def K1c (b κ : ℝ) : ℝ := (1 - 2 * b) + b ^ 2 / etaLow b κ ^ 2
def lam1 (b κ Cv : ℝ) : ℝ :=
  (K1c b κ * Cv + Q0c b κ Cv / 4) / (K1c b κ * Cv + Q0c b κ Cv / 2)
def theta1 (b κ Cv : ℝ) : ℝ := (lam1 b κ Cv + (1 - b / 2)) / 2
def Tmax (b κ Cv : ℝ) : ℝ := ((Cv + 1) / (Q0c b κ Cv / 2) + (2 + 1 / etaLow b κ)) / 2
def C1c (b κ Cv : ℝ) : ℝ := (1 + b * Tmax b κ Cv / etaLow b κ) / (1 - theta1 b κ Cv)
def eps1 (b κ Cv : ℝ) : ℝ :=
  min 1 (min (Q0c b κ Cv * etaLow b κ / (2 * b)) (Q0c b κ Cv / (4 * K1c b κ)))

section Consts
variable {b κ Cv : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ) (hCv : 0 ≤ Cv)
include hb0 hb hκ hCv

theorem Q0c_pos : 0 < Q0c b κ Cv := by
  have := etaLow_pos (by linarith : b < 1) hκ
  unfold Q0c h0c; positivity

omit hCv in
theorem K1c_pos : 0 < K1c b κ := by
  have := etaLow_pos (by linarith : b < 1) hκ
  unfold K1c; have : 0 < 1 - 2 * b := by linarith
  positivity

theorem lam1_lt_one : lam1 b κ Cv < 1 := by
  have hQ := Q0c_pos hb0 hb hκ hCv
  have hK := K1c_pos hb0 hb hκ
  unfold lam1
  rw [div_lt_one (by positivity)]; linarith

theorem theta1_lt_one : theta1 b κ Cv < 1 := by
  have := lam1_lt_one hb0 hb hκ hCv
  unfold theta1; linarith

theorem eps1_pos : 0 < eps1 b κ Cv := by
  have hQ := Q0c_pos hb0 hb hκ hCv
  have hK := K1c_pos hb0 hb hκ
  have := etaLow_pos (by linarith : b < 1) hκ
  unfold eps1
  exact lt_min one_pos (lt_min (by positivity) (by positivity))

end Consts

/-- Shorthand for `ζ = -E - cv - bu`. -/
def zetaOf (b E : ℝ) (v u : ℂ) : ℂ := -(E : ℂ) - ((1 - 2 * b : ℝ) : ℂ) * v - (b : ℂ) * u

theorem im_zetaOf (b E : ℝ) (v u : ℂ) :
    (zetaOf b E v u).im = (1 - 2 * b) * (-v.im) + b * (-u.im) := by
  simp [zetaOf]; ring

/-- Stage 1, setup: the port factor `w = (z - bv)⁻¹` and the lower bound on `Im ζ`. -/
theorem stage_one_setup {b κ E Cv ε : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ)
    (hE : E ∈ bulkInterval κ) (hCv : 0 ≤ Cv) {v u : ℂ} (hv0 : v.im ≤ 0) (hvC : ‖v‖ ≤ Cv)
    (hs : ‖u * (boundaryZ b E - (b : ℂ) * v) - 1‖ ≤ ε)
    (hε0 : 0 ≤ ε) (hε : ε ≤ eps1 b κ Cv) :
    let w := (boundaryZ b E - (b : ℂ) * v)⁻¹
    w * (boundaryZ b E - (b : ℂ) * v) = 1 ∧ ‖w‖ ≤ 1 / etaLow b κ ∧ h0c Cv ≤ ‖w‖ ^ 2 ∧
      ‖w‖ ^ 2 ≤ 1 / etaLow b κ ^ 2 ∧
      ((1 - 2 * b) + b ^ 2 * ‖w‖ ^ 2) * (-v.im) + Q0c b κ Cv / 2 ≤ (zetaOf b E v u).im := by
  obtain ⟨h1, h2⟩ := bulk_bounds hκ hE
  have hηl := etaLow_pos (by linarith : b < 1) hκ
  have hηle := etaLow_le (by linarith : b < 1) hκ hE
  have hη1 := bulk_eta_le_one hb0 hκ hE
  have hQ := Q0c_pos hb0 hb hκ hCv
  have hK := K1c_pos hb0 hb hκ
  have hθ := theta1_lt_one hb0 hb hκ hCv
  have hεl : ε ≤ 1 := hε.trans (min_le_left _ _)
  have hε2 : ε ≤ Q0c b κ Cv * etaLow b κ / (2 * b) :=
    hε.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hε3 : ε ≤ Q0c b κ Cv / (4 * K1c b κ) :=
    hε.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hc : 0 < 1 - 2 * b := by linarith
  set η := etaZ b E with hηdef
  set a := matchedA E
  set z := boundaryZ b E
  set α := -v.im
  have hα0 : 0 ≤ α := by simp only [α]; linarith
  have hαC : α ≤ Cv := (neg_le_abs _).trans ((Complex.abs_im_le_norm v).trans hvC)
  set q := z - (b : ℂ) * v
  have hqim : q.im = η + b * α := by simp [q, z, η, etaZ, α]; ring
  have hqpos : η ≤ q.im := by rw [hqim]; linarith [mul_nonneg hb0.le hα0]
  have hq0 : q ≠ 0 := fun h => by rw [h] at hqpos; simp at hqpos; linarith
  set w := q⁻¹
  have hw1 : w * q = 1 := inv_mul_cancel₀ hq0
  have hqn : η ≤ ‖q‖ := hqpos.trans (Complex.im_le_norm q)
  have hwn : ‖w‖ ≤ 1 / etaLow b κ := by
    rw [norm_inv]; rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le hηl (hηle.trans hqn)
  have hqu : ‖q‖ ≤ 2 + Cv := by
    calc ‖q‖ ≤ ‖z‖ + ‖(b : ℂ) * v‖ := norm_sub_le _ _
      _ ≤ 2 + 1 * Cv := by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hb0.le]
          gcongr
          · exact bulk_norm_z hb0 hb hκ hE
          · linarith
      _ = 2 + Cv := by ring
  set h := ‖w‖ ^ 2
  have hh0 : h0c Cv ≤ h := by
    have hwl : 1 / (2 + Cv) ≤ ‖w‖ := by
      rw [norm_inv, inv_eq_one_div]
      exact one_div_le_one_div_of_le (lt_of_lt_of_le (by linarith) hqn) hqu
    unfold h0c
    calc 1 / (2 + Cv) ^ 2 = (1 / (2 + Cv)) ^ 2 := by rw [div_pow, one_pow]
      _ ≤ ‖w‖ ^ 2 := pow_le_pow_left₀ (by positivity) hwl 2
  have hhu : h ≤ 1 / etaLow b κ ^ 2 := by
    calc h = ‖w‖ ^ 2 := rfl
      _ ≤ (1 / etaLow b κ) ^ 2 := by gcongr
      _ = 1 / etaLow b κ ^ 2 := by rw [div_pow, one_pow]
  have hwim : -w.im = q.im * h := neg_im_of_mul_eq_one hw1
  set s := u * q - 1
  have hu_eq : u = w + s * w := by
    have : u = u * (w * q) := by rw [hw1, mul_one]
    rw [this]; simp only [s]; ring
  have hsw : (s * w).im ≤ ε * ‖w‖ := by
    refine (Complex.im_le_norm _).trans ?_
    rw [norm_mul]; gcongr
  have himu : -u.im ≥ (η + b * α) * h - ε * ‖w‖ := by
    rw [hu_eq, Complex.add_im]; rw [hqim] at hwim; linarith
  set ζ := zetaOf b E v u
  have hζim : ζ.im = (1 - 2 * b) * α + b * (-u.im) := im_zetaOf b E v u
  have hbηh : Q0c b κ Cv ≤ b * η * h :=
    mul_le_mul (mul_le_mul_of_nonneg_left hηle hb0.le) hh0 (by unfold h0c; positivity)
      (mul_nonneg hb0.le (hηl.le.trans hηle))
  have hbεw : b * (ε * ‖w‖) ≤ Q0c b κ Cv / 2 := by
    have h1' : ε * ‖w‖ ≤ ε * (1 / etaLow b κ) := by gcongr
    have h2' : b * (ε * (1 / etaLow b κ)) ≤ Q0c b κ Cv / 2 := by
      have e : b * (ε * (1 / etaLow b κ)) = ε * (2 * b / etaLow b κ) / 2 := by field_simp
      rw [e]
      have : ε * (2 * b / etaLow b κ) ≤ Q0c b κ Cv * etaLow b κ / (2 * b) * (2 * b / etaLow b κ) :=
        by gcongr
      have e2 : Q0c b κ Cv * etaLow b κ / (2 * b) * (2 * b / etaLow b κ) = Q0c b κ Cv := by
        field_simp
      linarith
    exact (mul_le_mul_of_nonneg_left h1' hb0.le).trans h2'
  set P := ((1 - 2 * b) + b ^ 2 * h) * α
  have hζlow : P + Q0c b κ Cv / 2 ≤ ζ.im := by
    have key := mul_le_mul_of_nonneg_left himu hb0.le
    rw [hζim]; simp only [P]
    linear_combination key + hbηh + hbεw
  have hP0 : 0 ≤ P := mul_nonneg (by positivity) hα0
  have hζQ : Q0c b κ Cv / 2 ≤ ζ.im := le_trans (by linarith) hζlow
  have hζpos : 0 < ζ.im := lt_of_lt_of_le (by positivity) hζQ
  exact ⟨hw1, hwn, hh0, hhu, hζlow⟩

/-- Stage 1, the weighted contraction in real variables. -/
theorem stage_one_weights {b κ Cv A A₀ α ε δ₀ wn η ζim : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) (hCv : 0 ≤ Cv) (hε0 : 0 ≤ ε) (hε : ε ≤ eps1 b κ Cv) (hα0 : 0 ≤ α)
    (hαC : α ≤ Cv) (hA0 : 0 ≤ A) (hA₀0 : 0 ≤ A₀)
    (hhu : wn ^ 2 ≤ 1 / etaLow b κ ^ 2) (hηle : etaLow b κ ≤ η) (hη1 : η ≤ 1)
    (hζlow : ((1 - 2 * b) + b ^ 2 * wn ^ 2) * α + Q0c b κ Cv / 2 ≤ ζim)
    (hA : ζim * A ≤ α + ε) (hA₀ : η * A₀ ≤ η * dStar b + δ₀) (hδ0 : 0 ≤ δ₀)
    (hδ₁ : δ₀ ≤ b * etaLow b κ / 2) :
    ((1 - 2 * b) + b ^ 2 * wn) ^ 2 * (A * A₀) ≤ theta1 b κ Cv ^ 2 ∧
      (A + A₀) / 2 ≤ Tmax b κ Cv ∧ 0 ≤ theta1 b κ Cv := by
  have hηl := etaLow_pos (by linarith : b < 1) hκ
  have hQ := Q0c_pos hb0 hb hκ hCv
  have hK := K1c_pos hb0 hb hκ
  have hc : 0 < 1 - 2 * b := by linarith
  have hεl : ε ≤ 1 := hε.trans (min_le_left _ _)
  have hε3 : ε ≤ Q0c b κ Cv / (4 * K1c b κ) :=
    hε.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hηpos : 0 < η := hηl.trans_le hηle
  set h := wn ^ 2 with hh
  set P := ((1 - 2 * b) + b ^ 2 * h) * α
  have hP0 : 0 ≤ P := mul_nonneg (by positivity) hα0
  have hζQ : Q0c b κ Cv / 2 ≤ ζim := le_trans (by linarith) hζlow
  have hcbh : (1 - 2 * b) + b ^ 2 * h ≤ K1c b κ := by
    unfold K1c; have : b ^ 2 * h ≤ b ^ 2 * (1 / etaLow b κ ^ 2) := by gcongr
    rw [mul_one_div] at this; linarith
  have hcbh0 : 0 ≤ (1 - 2 * b) + b ^ 2 * h := by positivity
  have hX1 : ((1 - 2 * b) + b ^ 2 * h) * A ≤ lam1 b κ Cv := by
    have hnum : ((1 - 2 * b) + b ^ 2 * h) * A * ζim ≤ P + Q0c b κ Cv / 4 := by
      have e1 : ((1 - 2 * b) + b ^ 2 * h) * A * ζim ≤ ((1 - 2 * b) + b ^ 2 * h) * (α + ε) := by
        rw [mul_assoc, mul_comm A]; exact mul_le_mul_of_nonneg_left hA hcbh0
      have e2 : ((1 - 2 * b) + b ^ 2 * h) * ε ≤ Q0c b κ Cv / 4 := by
        have := mul_le_mul hcbh hε3 hε0 hK.le
        rw [show K1c b κ * (Q0c b κ Cv / (4 * K1c b κ)) = Q0c b κ Cv / 4 by field_simp] at this
        linarith
      simp only [P]; linear_combination e1 + e2
    have hstep1 : ((1 - 2 * b) + b ^ 2 * h) * A ≤ (P + Q0c b κ Cv / 4) / (P + Q0c b κ Cv / 2) := by
      rw [le_div_iff₀ (by positivity)]
      exact (mul_le_mul_of_nonneg_left hζlow (mul_nonneg hcbh0 hA0)).trans hnum
    have hPle : P ≤ K1c b κ * Cv := mul_le_mul hcbh hαC hα0 hK.le
    refine hstep1.trans ?_
    unfold lam1
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linear_combination (1 / 4 : ℝ) * mul_nonneg (sub_nonneg.2 hPle) hQ.le
  have hcb1 : (1 - 2 * b) + b ^ 2 ≤ 1 := by
    have : (1 - 2 * b) + b ^ 2 = (1 - b) ^ 2 := by ring
    rw [this]; exact pow_le_one₀ (by linarith) (by linarith)
  have hcb0 : 0 ≤ (1 - 2 * b) + b ^ 2 := by positivity
  have hA₀' : A₀ ≤ dStar b + δ₀ / η := by
    have := div_le_div_of_nonneg_right hA₀ hηpos.le
    rwa [mul_div_cancel_left₀ _ hηpos.ne', add_div, mul_div_cancel_left₀ _ hηpos.ne'] at this
  have h2' : δ₀ / η ≤ δ₀ / etaLow b κ := div_le_div_of_nonneg_left hδ0 hηl hηle
  have h3' : δ₀ / etaLow b κ ≤ b / 2 := by rw [div_le_iff₀ hηl]; linarith
  have hY1 : ((1 - 2 * b) + b ^ 2) * A₀ ≤ 1 - b / 2 := by
    have e : ((1 - 2 * b) + b ^ 2) * dStar b = 1 - b := by
      have h1b : (1 - b) ≠ 0 := (by linarith : (0:ℝ) < 1 - b).ne'
      rw [dStar]; field_simp; ring
    have h4' : 0 ≤ δ₀ / η := div_nonneg hδ0 hηpos.le
    have hδη : ((1 - 2 * b) + b ^ 2) * (δ₀ / η) ≤ b / 2 :=
      (mul_le_of_le_one_left h4' hcb1).trans (h2'.trans h3')
    have := mul_le_mul_of_nonneg_left hA₀' hcb0
    linear_combination this + hδη + e
  have hκsq : ((1 - 2 * b) + b ^ 2 * wn) ^ 2 ≤ ((1 - 2 * b) + b ^ 2 * h) * ((1 - 2 * b) + b ^ 2) := by
    have : ((1 - 2 * b) + b ^ 2 * h) * ((1 - 2 * b) + b ^ 2) - ((1 - 2 * b) + b ^ 2 * wn) ^ 2 =
        (1 - 2 * b) * b ^ 2 * (1 - wn) ^ 2 := by simp only [h]; ring
    have h0 : 0 ≤ (1 - 2 * b) * b ^ 2 * (1 - wn) ^ 2 := by positivity
    linarith
  have hX1n : 0 ≤ ((1 - 2 * b) + b ^ 2 * h) * A := mul_nonneg hcbh0 hA0
  have hY1n : 0 ≤ ((1 - 2 * b) + b ^ 2) * A₀ := mul_nonneg hcb0 hA₀0
  have hθ0 : 0 ≤ theta1 b κ Cv := by unfold theta1; linarith [hX1n.trans hX1]
  refine ⟨?_, ?_, hθ0⟩
  · have e2 : ((1 - 2 * b) + b ^ 2 * wn) ^ 2 * (A * A₀) ≤
        (((1 - 2 * b) + b ^ 2 * h) * A) * (((1 - 2 * b) + b ^ 2) * A₀) := by
      have := mul_le_mul_of_nonneg_right hκsq (mul_nonneg hA0 hA₀0)
      linarith [this]
    have e3 : (((1 - 2 * b) + b ^ 2 * h) * A) * (((1 - 2 * b) + b ^ 2) * A₀) ≤
        lam1 b κ Cv * (1 - b / 2) := mul_le_mul hX1 hY1 hY1n (hX1n.trans hX1)
    have e4 : lam1 b κ Cv * (1 - b / 2) ≤ theta1 b κ Cv ^ 2 := by
      unfold theta1
      have := sq_nonneg (lam1 b κ Cv - (1 - b / 2))
      linarith
    linarith
  · have hAle : A ≤ (Cv + 1) / (Q0c b κ Cv / 2) := by
      rw [le_div_iff₀ (by positivity)]
      calc A * (Q0c b κ Cv / 2) ≤ A * ζim := mul_le_mul_of_nonneg_left hζQ hA0
        _ = ζim * A := mul_comm _ _
        _ ≤ α + ε := hA
        _ ≤ Cv + 1 := by linarith
    have hd : dStar b ≤ 2 := by rw [dStar, div_le_iff₀ (by linarith)]; linarith
    have hηl1 : etaLow b κ ≤ 1 := hηle.trans hη1
    have h5 : b / 2 ≤ 1 / etaLow b κ := by
      rw [le_div_iff₀ hηl]; nlinarith
    unfold Tmax; linarith

/-- The two Herglotz mass bounds at `ζ` and at `z`. -/
theorem mass_bounds {W : ℕ} {b κ E ε δ₀ : ℝ} (hb : b < 1 / 2) (hκ : 0 < κ)
    (hE : E ∈ bulkInterval κ) {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef)
    {v ζ : ℂ} (hζpos : 0 < ζ.im) (hr : ‖v - stieltjes X ζ‖ ≤ ε)
    (hδ : jetDistance0 b E X ≤ δ₀) :
    ζ.im * sqMass X ζ ≤ -v.im + ε ∧
      etaZ b E * sqMass X (boundaryZ b E) ≤ etaZ b E * dStar b + δ₀ := by
  obtain ⟨h1, h2⟩ := bulk_bounds hκ hE
  have hzpos : 0 < (boundaryZ b E).im := etaZ_pos b E (by linarith) h1 h2
  constructor
  · have h' := im_mul_sqMass_le hY hζpos
    have hi : -(stieltjes X ζ).im = -v.im + (v - stieltjes X ζ).im := by
      simp only [Complex.sub_im]; ring
    linarith [(Complex.im_le_norm (v - stieltjes X ζ)).trans hr]
  · have h' := im_mul_sqMass_le hY hzpos
    have hj : jetDistance0 b E X = ‖stieltjes X (boundaryZ b E) - matchedA E‖ := rfl
    have hi : -(stieltjes X (boundaryZ b E)).im =
        -(matchedA E).im - (stieltjes X (boundaryZ b E) - matchedA E).im := by
      simp only [Complex.sub_im]; ring
    have := (neg_le_abs _).trans ((Complex.abs_im_le_norm
      (stieltjes X (boundaryZ b E) - matchedA E)).trans (hj ▸ hδ))
    rw [hi, bulk_im_a hb hκ hE] at h'
    exact h'.trans (by unfold etaZ at *; linarith)

/-- **Stage 1 (crude contraction, branch identification)**: the means lie within
`C₁(δ₀ + ε)` of the matched value. -/
theorem mean_stage_one {W : ℕ} {b κ E Cv ε δ₀ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ)
    (hE : E ∈ bulkInterval κ) (hCv : 0 ≤ Cv) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) {v u : ℂ} (hv0 : v.im ≤ 0) (hvC : ‖v‖ ≤ Cv)
    (hs : ‖u * (boundaryZ b E - (b : ℂ) * v) - 1‖ ≤ ε)
    (hr : ‖v - stieltjes X (zetaOf b E v u)‖ ≤ ε) (hε0 : 0 ≤ ε) (hε : ε ≤ eps1 b κ Cv)
    (hδ : jetDistance0 b E X ≤ δ₀) (hδ₁ : δ₀ ≤ b * etaLow b κ / 2) :
    Q0c b κ Cv / 2 ≤ (zetaOf b E v u).im ∧
      ‖v - matchedA E‖ ≤ C1c b κ Cv * (δ₀ + ε) := by
  obtain ⟨h1, h2⟩ := bulk_bounds hκ hE
  obtain ⟨hw1, hwn, hh0, hhu, hζlow⟩ :=
    stage_one_setup hb0 hb hκ hE hCv hv0 hvC hs hε0 hε
  have hηl := etaLow_pos (by linarith : b < 1) hκ
  have hηle := etaLow_le (by linarith : b < 1) hκ hE
  have hη1 := bulk_eta_le_one hb0 hκ hE
  have hQ := Q0c_pos hb0 hb hκ hCv
  have hθ := theta1_lt_one hb0 hb hκ hCv
  have hc : 0 < 1 - 2 * b := by linarith
  have hδ0 : 0 ≤ δ₀ := (norm_nonneg _).trans hδ
  set w := (boundaryZ b E - (b : ℂ) * v)⁻¹
  set ζ := zetaOf b E v u
  have hα0 : 0 ≤ -v.im := by linarith
  have hαC : -v.im ≤ Cv := (neg_le_abs _).trans ((Complex.abs_im_le_norm v).trans hvC)
  have hζQ : Q0c b κ Cv / 2 ≤ ζ.im :=
    le_trans (le_add_of_nonneg_left (mul_nonneg (by positivity) hα0)) hζlow
  have hζpos : 0 < ζ.im := lt_of_lt_of_le (by positivity) hζQ
  refine ⟨hζQ, ?_⟩
  obtain ⟨hA, hA₀⟩ := mass_bounds hb hκ hE hY hζpos hr hδ
  obtain ⟨hwt, hTm, hθ0⟩ := stage_one_weights hb0 hb hκ hCv hε0 hε hα0 hαC (sqMass_nonneg X ζ)
    (sqMass_nonneg X (boundaryZ b E)) hhu hηle hη1 hζlow hA hA₀ hδ0 hδ₁
  have hzpos : 0 < (boundaryZ b E).im := etaZ_pos b E (by linarith) h1 h2
  have ha1 : ‖matchedA E‖ = 1 := bulk_norm_a hκ hE
  set T := crossTr X ζ (boundaryZ b E)
  set κc : ℂ := ((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * matchedA E * w
  have hκn : ‖κc‖ ≤ (1 - 2 * b) + b ^ 2 * ‖w‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_of_nonneg hc.le, norm_mul, norm_mul, ha1, norm_pow,
      Complex.norm_real, Real.norm_of_nonneg hb0.le, mul_one]
  have hT := norm_crossTr_le X ζ (boundaryZ b E)
  have hsA := Real.sq_sqrt (sqMass_nonneg X ζ)
  have hsA₀ := Real.sq_sqrt (sqMass_nonneg X (boundaryZ b E))
  have hTsq : ‖T‖ ^ 2 ≤ sqMass X ζ * sqMass X (boundaryZ b E) := by
    have := pow_le_pow_left₀ (norm_nonneg _) hT 2
    rw [mul_pow, hsA, hsA₀] at this; exact this
  have hκT : ‖κc‖ * ‖T‖ ≤ theta1 b κ Cv := by
    have hp : (‖κc‖ * ‖T‖) ^ 2 ≤ theta1 b κ Cv ^ 2 := by
      rw [mul_pow]
      exact (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hκn 2) hTsq (by positivity)
        (by positivity)).trans hwt
    exact (pow_le_pow_iff_left₀ (by positivity) hθ0 two_ne_zero).1 hp
  have hTle : ‖T‖ ≤ Tmax b κ Cv := by
    have hsq : Real.sqrt (sqMass X ζ) * Real.sqrt (sqMass X (boundaryZ b E)) ≤
        (sqMass X ζ + sqMass X (boundaryZ b E)) / 2 := by
      have := sq_nonneg (Real.sqrt (sqMass X ζ) - Real.sqrt (sqMass X (boundaryZ b E)))
      linear_combination (1 / 2 : ℝ) * this + (1 / 2 : ℝ) * hsA + (1 / 2 : ℝ) * hsA₀
    linarith
  have hTm0 : 0 ≤ Tmax b κ Cv := (norm_nonneg T).trans hTle
  have hres := stieltjes_sub hY hζpos hzpos
  have hid := (mean_identity (a := matchedA E) (z := boundaryZ b E) (v := v) (u := u) (w := w)
    (fζ := stieltjes X ζ) (fz := stieltjes X (boundaryZ b E)) (T := T) (b := (b : ℂ))
    (c := ((1 - 2 * b : ℝ) : ℂ)) (E := (E : ℂ)) hw1 (bulk_a_mul hκ hE) (bulk_z_eq hκ hE)
    hres).1
  have hrhs : ‖(stieltjes X (boundaryZ b E) - matchedA E) + (v - stieltjes X ζ) +
      (b : ℂ) * T * (u * (boundaryZ b E - (b : ℂ) * v) - 1) * w‖ ≤
      δ₀ + ε + b * Tmax b κ Cv * ε * (1 / etaLow b κ) := by
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add hδ hr)) ?_)
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hb0.le]
    gcongr
  have hden : 1 - theta1 b κ Cv ≤ ‖1 - κc * T‖ := by
    have := norm_sub_norm_le (1 : ℂ) (κc * T)
    rw [norm_one, norm_mul] at this; linarith
  have hθpos : 0 < 1 - theta1 b κ Cv := by linarith
  have key : ‖v - matchedA E‖ * (1 - theta1 b κ Cv) ≤
      δ₀ + ε + b * Tmax b κ Cv * ε * (1 / etaLow b κ) := by
    calc ‖v - matchedA E‖ * (1 - theta1 b κ Cv) ≤ ‖v - matchedA E‖ * ‖1 - κc * T‖ :=
          mul_le_mul_of_nonneg_left hden (norm_nonneg _)
      _ = ‖(v - matchedA E) * (1 - κc * T)‖ := (norm_mul _ _).symm
      _ = _ := by rw [hid]
      _ ≤ _ := hrhs
  rw [← le_div_iff₀ hθpos] at key
  refine key.trans ?_
  unfold C1c
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ hθpos.le
  have : b * Tmax b κ Cv * ε * (1 / etaLow b κ) = (b * Tmax b κ Cv / etaLow b κ) * ε := by ring
  rw [this]
  have hx : 0 ≤ b * Tmax b κ Cv / etaLow b κ := by positivity
  linear_combination mul_nonneg hx hδ0

end BlockBand.Transmission.PathScalar
