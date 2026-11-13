module

public import BlockBand.Transmission.PassiveLayer.RPlus
public import BlockBand.Transmission.PassiveLayer.WeightedLetters
public import BlockBand.Transmission.PathScalar.MeanStepLimit
public import BlockBand.Transmission.PathScalar.Superexp
public import BlockBand.Transmission.Bridge.Recursion
public import BlockBand.Transmission.Bridge.Passive
public import BlockBand.Transmission.PassiveCovariance.WordReduction

/-!
# The exact passive update `Q₊ = L*QL`

Law `freshLaw W b`, deterministic passive `X` (`Y = -Im X ⪰ 0`), `0 < b < 1/2`, `-2 < E < 2`.

The passive matrix `Q` transforms under one fresh layer as `Q₊ = L*QL`; this file proves the
identity and its consequences for the mass and the source terms.

* `mu_core` (deterministic, `Fin W` coordinates): for `P = A - E - X` with `A` Hermitian,
  `S = P - z⁻¹BB*`, `X₊ = B*P⁻¹B`, `L = K(-z⁻¹S⁻¹B)`, `RK = 1`:
  `R₊*Y₊R₊ = L*(R*YR)L` (`Y₊ = B*P⁻*YP⁻¹B`, `-z⁻¹S⁻¹B = -P⁻¹BR₊`).
* `ae_passiveQ_freshSchur`: `Q₊ = L*QL` almost surely; consequences for
  `q₊ = Re Tr(QLL*)`, `Tr(Q₊f₊) = Tr(Q·Lf₊L*)` and `‖Q₊^{1/2}f₊Q₊^{1/2}‖_HS`.
* `passiveMass_le_width`: `q ≤ W/(4η)` for every `X` (`T = I - S*S`).
* Measurability of `q`, `Tr(Qf)`, `‖Q^{1/2}fQ^{1/2}‖_HS` and of `(X, ω) ↦ X₊`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.SourceMixing

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open scoped ComplexOrder

variable {W : ℕ}

/-!
## Width bound
-/

/-- `q ≤ W/(4η)` for every `X` (`T = 4ηQ = I - S*S ⪯ I`). -/
theorem passiveMass_le_width {b E : ℝ} (hb : b < 1) (h1 : -2 < E) (h2 : E < 2)
    (X : Matrix (Fin W) (Fin W) ℂ) : passiveMass b E X ≤ W / (4 * etaZ b E) := by
  have hη := PassiveCovariance.etaZ_pos b E hb h1 h2
  have hT := Bridge.passiveTransmission_eq_one_sub b E X
  have hpsd := (Matrix.posSemidef_conjTranspose_mul_self (Bridge.passiveS b E X)).trace_nonneg
  have htr : (passiveTransmission b E X).trace.re = 4 * etaZ b E * passiveMass b E X := by
    rw [passiveTransmission, trace_smul, passiveMass, smul_eq_mul, Complex.re_ofReal_mul]
  rw [hT, trace_sub, trace_one, Complex.sub_re] at htr
  have h0 := (Complex.nonneg_iff.mp hpsd).1
  simp only [Fintype.card_fin, Complex.natCast_re] at htr h0
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-!
## Deterministic algebra
-/

theorem mu_inv_sub_adj {P : Matrix (Fin W) (Fin W) ℂ} (hP : IsUnit P) :
    P⁻¹ - (P⁻¹)ᴴ = (P⁻¹)ᴴ * (Pᴴ - P) * P⁻¹ := by
  have hPP : P * P⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hP)
  have h1 : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, hPP, conjTranspose_one]
  rw [Matrix.mul_sub, Matrix.sub_mul, h1, Matrix.one_mul, Matrix.mul_assoc, hPP, Matrix.mul_one]

/-- `-Im(B*P⁻¹B) = B*P⁻*((i/2)(P* - P))P⁻¹B`. -/
theorem mu_passiveY_conj {P : Matrix (Fin W) (Fin W) ℂ} (hP : IsUnit P)
    (B : Matrix (Fin W) (Fin W) ℂ) :
    passiveY (Bᴴ * P⁻¹ * B) =
      Bᴴ * (P⁻¹)ᴴ * ((Complex.I / 2) • (Pᴴ - P)) * P⁻¹ * B := by
  have hadj : (Bᴴ * P⁻¹ * B)ᴴ = Bᴴ * (P⁻¹)ᴴ * B := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hd : Bᴴ * P⁻¹ * B - (Bᴴ * P⁻¹ * B)ᴴ = Bᴴ * ((P⁻¹)ᴴ * (Pᴴ - P) * P⁻¹) * B := by
    rw [hadj, ← mu_inv_sub_adj hP, Matrix.mul_sub, Matrix.sub_mul]
  rw [passiveY, matrixImaginaryPart, hd]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, ← smul_neg, neg_smul, neg_neg,
    neg_div]

/-- `(i/2)(P* - P) = Y` for `P = A - E - X`, `A` Hermitian. -/
theorem mu_half_adj_sub {A X : Matrix (Fin W) (Fin W) ℂ} (hA : A.IsHermitian) (E : ℝ) :
    (Complex.I / 2) • ((A - (E : ℂ) • 1 - X)ᴴ - (A - (E : ℂ) • 1 - X)) = passiveY X := by
  have hE : ((E : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ))ᴴ = (E : ℂ) • 1 := by
    rw [conjTranspose_smul, conjTranspose_one, Complex.star_def, Complex.conj_ofReal]
  rw [conjTranspose_sub, conjTranspose_sub, hA.eq, hE, passiveY, matrixImaginaryPart]
  have : A - (E : ℂ) • 1 - Xᴴ - (A - (E : ℂ) • 1 - X) = X - Xᴴ := by abel
  rw [this, ← neg_smul]
  congr 1
  ring

/-- `P⁻¹BR₊ = z⁻¹S⁻¹B` with `R₊ = z⁻¹ + z⁻²B*S⁻¹B`, `S = P - z⁻¹BB*`. -/
theorem mu_g12 {P B : Matrix (Fin W) (Fin W) ℂ} {z : ℂ} (hz : z ≠ 0) (hP : IsUnit P)
    (hS : IsUnit (P - z⁻¹ • (B * Bᴴ))) :
    P⁻¹ * B * (z⁻¹ • 1 + (z⁻¹ ^ 2) • (Bᴴ * (P - z⁻¹ • (B * Bᴴ))⁻¹ * B)) =
      z⁻¹ • ((P - z⁻¹ • (B * Bᴴ))⁻¹ * B) := by
  set S := P - z⁻¹ • (B * Bᴴ) with hSdef
  have hPP : P⁻¹ * P = 1 := nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hP)
  have hSS : S * S⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hS)
  have hBB : B * Bᴴ = z • (P - S) := by
    rw [hSdef, sub_sub_cancel, smul_smul, mul_inv_cancel₀ hz, one_smul]
  have key : P⁻¹ * (B * Bᴴ) * S⁻¹ * B = z • (S⁻¹ * B - P⁻¹ * B) := by
    rw [hBB]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul]
    rw [hPP, Matrix.one_mul, Matrix.mul_assoc P⁻¹ S, hSS, Matrix.mul_one]
  have e : P⁻¹ * B * (Bᴴ * S⁻¹ * B) = P⁻¹ * (B * Bᴴ) * S⁻¹ * B := by
    simp only [Matrix.mul_assoc]
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one, e, key, smul_smul]
  have hz' : z⁻¹ ^ 2 * z = z⁻¹ := by field_simp
  rw [hz', smul_sub]
  abel

/-- The deterministic core of the passive update: `R₊*Y₊R₊ = L*(R*YR)L`. -/
theorem mu_core {A B X R : Matrix (Fin W) (Fin W) ℂ} {E : ℝ} {z : ℂ} (hz : z ≠ 0)
    (hA : A.IsHermitian) (hP : IsUnit (A - (E : ℂ) • 1 - X))
    (hS : IsUnit (A - (E : ℂ) • 1 - X - z⁻¹ • (B * Bᴴ))) (hRK : R * (z • 1 - X) = 1) :
    ((z • 1 - Bᴴ * (A - (E : ℂ) • 1 - X)⁻¹ * B)⁻¹)ᴴ *
        passiveY (Bᴴ * (A - (E : ℂ) • 1 - X)⁻¹ * B) *
        (z • 1 - Bᴴ * (A - (E : ℂ) • 1 - X)⁻¹ * B)⁻¹ =
      ((z • 1 - X) * (-z⁻¹ • ((A - (E : ℂ) • 1 - X - z⁻¹ • (B * Bᴴ))⁻¹ * B)))ᴴ *
        (Rᴴ * passiveY X * R) *
        ((z • 1 - X) * (-z⁻¹ • ((A - (E : ℂ) • 1 - X - z⁻¹ • (B * Bᴴ))⁻¹ * B))) := by
  set P := A - (E : ℂ) • 1 - X with hPdef
  set K := z • (1 : Matrix (Fin W) (Fin W) ℂ) - X
  set S := P - z⁻¹ • (B * Bᴴ)
  set Rp := z⁻¹ • (1 : Matrix (Fin W) (Fin W) ℂ) + (z⁻¹ ^ 2) • (Bᴴ * S⁻¹ * B)
  have hRp : (z • 1 - Bᴴ * P⁻¹ * B)⁻¹ = Rp := inv_eq_right_inv (woodbury P B hz hP hS)
  have hL : -z⁻¹ • (S⁻¹ * B) = -(P⁻¹ * B * Rp) := by
    rw [neg_smul, mu_g12 hz hP hS]
  have hY := mu_passiveY_conj hP B
  rw [mu_half_adj_sub hA E] at hY
  rw [hRp, hY, hL, Matrix.mul_neg, conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg,
    Matrix.neg_mul, neg_neg]
  have hKR : Kᴴ * Rᴴ = 1 := by rw [← conjTranspose_mul, hRK, conjTranspose_one]
  have e1 : (K * (P⁻¹ * B * Rp))ᴴ * (Rᴴ * passiveY X * R) * (K * (P⁻¹ * B * Rp)) =
      (P⁻¹ * B * Rp)ᴴ * (Kᴴ * Rᴴ) * passiveY X * (R * K) * (P⁻¹ * B * Rp) := by
    rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
  rw [e1, hKR, hRK, Matrix.mul_one, Matrix.mul_one]
  simp only [conjTranspose_mul, Matrix.mul_assoc]

/-!
## The almost-sure update
-/

theorem mu_liftX_inv (M : Matrix (Fin W) (Fin W) ℂ) : liftX M⁻¹ = (liftX M)⁻¹ := by
  rw [liftX_eq_submatrix, liftX_eq_submatrix]
  exact (Matrix.inv_submatrix_equiv M (Equiv.uniqueProd (Fin W) (Fin 1))
    (Equiv.uniqueProd (Fin W) (Fin 1))).symm

theorem mu_isUnit_of_liftX {M : Matrix (Fin W) (Fin W) ℂ} (h : IsUnit (liftX M)) : IsUnit M := by
  rw [isUnit_iff_isUnit_det] at h ⊢
  rwa [det_liftX] at h

/-- `freshL = K(-z⁻¹S⁻¹B)` on the event `A` Hermitian, `B` invertible, in `Fin W` coordinates. -/
theorem mu_freshL_eq {b E : ℝ} (hη : 0 < (boundaryZ b E).im) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) {ω : LayerSample W .oneBlockOnePort}
    (hA : (ω.1 0).IsHermitian) (hB : IsUnit (ω.2 0 0)) :
    freshL b E X ω = (boundaryZ b E • 1 - X) * (-(boundaryZ b E)⁻¹ •
      ((ω.1 0 - (E : ℂ) • 1 - X - (boundaryZ b E)⁻¹ • (ω.2 0 0 * (ω.2 0 0)ᴴ))⁻¹ * ω.2 0 0)) ∧
      IsUnit (ω.1 0 - (E : ℂ) • 1 - X - (boundaryZ b E)⁻¹ • (ω.2 0 0 * (ω.2 0 0)ᴴ)) := by
  set z := boundaryZ b E
  have h := (layer_schur E hη hY hA hB).2.1
  have hSl : schurS E z X ω =
      liftX (ω.1 0 - (E : ℂ) • 1 - X - z⁻¹ • (ω.2 0 0 * (ω.2 0 0)ᴴ)) := by
    rw [schurS, bondL, bondMatrix_one_eq, blockDiag_one_eq, liftX_sub, liftX_sub, liftX_sub,
      liftX_smul, liftX_smul, liftX_one, liftX_mul, liftX_conjTranspose]
  have hS := isUnit_schurS E hη hY hA hB
  refine ⟨?_, mu_isUnit_of_liftX (hSl ▸ hS)⟩
  have hg : freshL b E X ω = lAt E z X ω := rfl
  rw [hg, lAt, g12_eq h, hSl, bondL, bondMatrix_one_eq, ← mu_liftX_inv, ← liftX_mul,
    ← liftX_smul]
  rfl

/-- The passive update `Q₊ = L*QL` holds almost surely. -/
theorem ae_passiveQ_freshSchur {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hW : 1 ≤ W) {E : ℝ}
    (h1 : -2 < E) (h2 : E < 2) {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef) :
    ∀ᵐ ω ∂freshLaw W b, passiveQ b E (freshSchur E X ω) =
      (freshL b E X ω)ᴴ * passiveQ b E X * freshL b E X ω := by
  have hη : 0 < (boundaryZ b E).im := PassiveCovariance.etaZ_pos b E (by linarith) h1 h2
  have hz : boundaryZ b E ≠ 0 := fun h0 => by rw [h0] at hη; simp at hη
  filter_upwards [ae_good W hb0 hW, ae_isUnit_physBlock W hb hW E X] with ω hω hPl
  obtain ⟨hL, hS⟩ := mu_freshL_eq hη hY hω.1 hω.2
  have hP : IsUnit (ω.1 0 - (E : ℂ) • 1 - X) := by
    refine mu_isUnit_of_liftX ?_
    rwa [liftX_sub, liftX_sub, liftX_smul, liftX_one, ← blockDiag_one_eq]
  have hfs : freshSchur E X ω = (ω.2 0 0)ᴴ * (ω.1 0 - (E : ℂ) • 1 - X)⁻¹ * ω.2 0 0 := by
    conv_lhs => rw [PathScalar.layerSample_eta ω]
    exact Bridge.freshSchur_eq E X _ _
  have hRK := (PassiveCovariance.nearPencil_inverse hb0 hb h1 h2 hY).2
  rw [hL, passiveQ, passiveQ, hfs, passiveResolvent, passiveResolvent]
  exact mu_core hz hω.1 hP hS hRK

/-- `q₊ = Re Tr(Q LL*)` almost surely. -/
theorem ae_passiveMass_freshSchur {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hW : 1 ≤ W) {E : ℝ}
    (h1 : -2 < E) (h2 : E < 2) {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef) :
    ∀ᵐ ω ∂freshLaw W b, passiveMass b E (freshSchur E X ω) =
      (passiveQ b E X * freshU b E X ω).trace.re := by
  filter_upwards [ae_passiveQ_freshSchur hb0 hb hW h1 h2 hY] with ω h
  rw [passiveMass, h, freshU, Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]

/-- `Tr(Q₊f₊) = Tr(Q·Lf₊L*)` almost surely. -/
theorem ae_traceQF_freshSchur {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hW : 1 ≤ W) {E : ℝ}
    (h1 : -2 < E) (h2 : E < 2) {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef) :
    ∀ᵐ ω ∂freshLaw W b,
      (passiveQ b E (freshSchur E X ω) * passiveF b E (freshSchur E X ω)).trace =
        (passiveQ b E X * freshTransportedF b E X ω).trace := by
  filter_upwards [ae_passiveQ_freshSchur hb0 hb hW h1 h2 hY] with ω h
  rw [h, freshTransportedF]
  simp only [Matrix.mul_assoc]
  rw [trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- `‖Q₊^{1/2}f₊Q₊^{1/2}‖_HS = ‖Q^{1/2}(Lf₊L*)Q^{1/2}‖_HS` almost surely. -/
theorem ae_hsSandwich_freshSchur {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hW : 1 ≤ W) {E : ℝ}
    (h1 : -2 < E) (h2 : E < 2) {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef) :
    ∀ᵐ ω ∂freshLaw W b,
      hsSandwich (passiveQ b E (freshSchur E X ω)) (passiveF b E (freshSchur E X ω)) =
        hsSandwich (passiveQ b E X) (freshTransportedF b E X ω) := by
  filter_upwards [ae_passiveQ_freshSchur hb0 hb hW h1 h2 hY] with ω h
  rw [hsSandwich, hsSandwich, h, freshTransportedF]
  generalize freshL b E X ω = L
  generalize passiveQ b E X = Q
  generalize passiveF b E (freshSchur E X ω) = F
  have e1 : Lᴴ * Q * L * F * (Lᴴ * Q * L) * Fᴴ = Lᴴ * (Q * L * F * Lᴴ * Q * L * Fᴴ) := by
    simp only [Matrix.mul_assoc]
  have e2 : Q * (L * F * Lᴴ) * Q * (L * F * Lᴴ)ᴴ = (Q * L * F * Lᴴ * Q * L * Fᴴ) * Lᴴ := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
  rw [e1, e2, trace_mul_comm]

/-!
## Measurability
-/

theorem mu_measurable_resolvent (b E : ℝ) :
    Measurable fun X : Matrix (Fin W) (Fin W) ℂ => passiveResolvent b E X :=
  Bridge.measurable_matrix_inv.comp (continuous_const.sub continuous_id).measurable

theorem mu_measurable_passiveQ (b E : ℝ) :
    Measurable fun X : Matrix (Fin W) (Fin W) ℂ => passiveQ b E X := by
  have hY : Measurable fun X : Matrix (Fin W) (Fin W) ℂ => passiveY X := by
    have : Continuous fun X : Matrix (Fin W) (Fin W) ℂ => passiveY X := by
      unfold passiveY matrixImaginaryPart; fun_prop
    exact this.measurable
  have hR := mu_measurable_resolvent (W := W) b E
  exact Bridge.measurable_matrix_mul' (Bridge.measurable_matrix_mul'
    (Bridge.measurable_matrix_conjTranspose' hR) hY) hR

theorem measurable_passiveMass (b E : ℝ) :
    Measurable fun X : Matrix (Fin W) (Fin W) ℂ => passiveMass b E X :=
  (Complex.continuous_re.comp (continuous_id.matrix_trace)).measurable.comp
    (mu_measurable_passiveQ b E)

theorem mu_measurable_passiveF (b E : ℝ) :
    Measurable fun X : Matrix (Fin W) (Fin W) ℂ => passiveF b E X :=
  (continuous_id.sub continuous_const).measurable.comp (mu_measurable_resolvent b E)

theorem measurable_traceQF (b E : ℝ) :
    Measurable fun X : Matrix (Fin W) (Fin W) ℂ => (passiveQ b E X * passiveF b E X).trace :=
  continuous_id.matrix_trace.measurable.comp
    (Bridge.measurable_matrix_mul' (mu_measurable_passiveQ b E) (mu_measurable_passiveF b E))

theorem measurable_hsQF (b E : ℝ) :
    Measurable fun X : Matrix (Fin W) (Fin W) ℂ => hsSandwich (passiveQ b E X) (passiveF b E X) := by
  have hQ := mu_measurable_passiveQ (W := W) b E
  have hF := mu_measurable_passiveF (W := W) b E
  have hm := Bridge.measurable_matrix_mul' (Bridge.measurable_matrix_mul'
    (Bridge.measurable_matrix_mul' hQ hF) hQ) (Bridge.measurable_matrix_conjTranspose' hF)
  exact (Real.continuous_sqrt.comp (Complex.continuous_re.comp continuous_id.matrix_trace)).measurable.comp hm

/-- Joint measurability of `(X, ω) ↦ X₊`. -/
theorem measurable_freshSchur_prod (E : ℝ) :
    Measurable fun q : Matrix (Fin W) (Fin W) ℂ × LayerSample W .oneBlockOnePort =>
      freshSchur E q.1 q.2 := by
  have hlift : Measurable fun q : Matrix (Fin W) (Fin W) ℂ × LayerSample W .oneBlockOnePort =>
      (Matrix.of fun (u v : Fin 1 × Fin W) => q.1 u.2 v.2 :
        Matrix (PhysSite W .oneBlockOnePort) (PhysSite W .oneBlockOnePort) ℂ) :=
    Measurable.of_eval_matrix _ fun u v => measurable_fst.eval_matrix
  exact Measurable.of_eval_matrix _ fun x y =>
    (PathScalar.measurable_layerSchur .oneBlockOnePort E hlift measurable_snd).eval_matrix

end BlockBand.Transmission.SourceMixing
