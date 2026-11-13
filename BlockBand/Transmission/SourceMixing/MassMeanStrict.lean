module

public import BlockBand.Transmission.SourceMixing.MassMeanDomain

/-!
# The `q/W`-exact mass mean for strictly passive inputs

Hypothesis `PassiveBoundsStatement`. Law `freshLaw W b`, deterministic strictly passive `X`
(`Y ≻ 0`), fixed `b ∈ (0, 1/2)`, `E ∈ (-2, 2)`; the constant depends on `b, E` only, uniformly in
`W ≥ W₀` and `X`.

The bound `Re Tr(Q E[LL*]) ≤ q/(1+αq/W) + C(δ₀ + W⁻²)q` when `Y` is positive definite.

Proof outline. With `M = (ζ - X)⁻¹`, `v = (z - bm₁)⁻¹`, `h = |v|²`, `A = ⟨MMᴴ⟩`,
`y = ⟨MᴴYM⟩`, `ι = Im ζ`, `k = c + b²h`:
* the imaginary parts of the scalar equations (Ward identity `mm_ward`, `Im v = -h Im(z - bm₁)`,
  `ζ = -E - cm₁ - bm₂`, `m₁ ≈ ⟨M⟩`, `m₂ ≈ v`) give `ι(1 - kA) = bhη + ky + O(W⁻²)`;
* with `s₁(1 - kA) = bh + O(W⁻²)` (`scalarS1`): `s₁(bhη + ky) = bhι + O(W⁻²)`;
* `M = R·KM`, so `W y = Tr(Q·KM KMᴴ)` exactly, and `E(q₊) = Re Tr(Q E[LL*]) =
  Re(s₁)·Wy + O(qW⁻²)` (`freshU_mean`);
* `mm_F_le` (proved in the sibling module) compares `Wy·bh/(bhη + ky)` with `q/(η(1+αq/W))`, using `|h - 1|, ‖KM - 1‖,
  |ζ - z| ≤ C(δ₀ + W⁻²)` (`mm_matched0`) and `q ≤ W/(4η)`.
Off the domain `δ₀ ≤ d₁` the crude bound `‖E[LL*]‖q ≤ C₁q ≤ (C₁/d₁)δ₀q` is used.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.SourceMixing

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PathScalar
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- `Re s₁` on the domain: from the imaginary parts and the `s₁` equation,
`Re s₁ ≤ (bhι + ε)/(bhη + k_h u/W)` with `ε = (I_zC₂ + 2C_fC_D)e`. -/
theorem mm_sre (hW1 : 1 ≤ W) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosDef) {C2 Cf CD Iz e : ℝ}
    (hC2 : 0 ≤ C2) (hCf : 0 ≤ Cf) (hCD : 0 ≤ CD)
    (hG : ∀ α β, Integrable (fun ω => gRes b E X ω α β) (layerLaw W b .oneBlockOnePort))
    (hB0 : ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 0 0 - mOf b E X‖ ≤
      CD / (W : ℝ) ^ 2)
    (hB1 : ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 1 1 -
      vOf b E X • 1‖ ≤ CD / (W : ℝ) ^ 2)
    (hzM : (zetaX b E X • 1 - X) * mOf b E X = 1)
    (hS : ‖sOne b E X * (1 - khOf b E X * aOf b E X) - (b : ℂ) * hOf b E X‖ ≤ C2 / (W : ℝ) ^ 2)
    (hsn : ‖sOne b E X‖ ≤ Cf) (hh : |Complex.normSq (vOf b E X) - 1| ≤ 1 / 2)
    (hιb : |(zetaX b E X).im| ≤ Iz) (hWe : 1 / (W : ℝ) ^ 2 ≤ e) :
    (sOne b E X).re ≤ (b * Complex.normSq (vOf b E X) * (zetaX b E X).im +
        (Iz * C2 + Cf * (2 * CD)) * e) /
      (b * Complex.normSq (vOf b E X) * etaZ b E + ((1 - 2 * b) + b ^ 2 * Complex.normSq (vOf b E X)) *
        (((mOf b E X)ᴴ * passiveY X * mOf b E X).trace.re / W)) := by
  have hη := etaZ_pos b E (by linarith) h1 h2
  set M := mOf b E X
  set v := vOf b E X
  set h := Complex.normSq v
  set u := (Mᴴ * passiveY X * M).trace.re
  have hhlo : 1 / 2 ≤ h := by have := neg_abs_le (h - 1); linarith
  have hhhi : h ≤ 3 / 2 := by have := le_abs_self (h - 1); linarith
  have hu0 : 0 ≤ u := (mm_trace_posSemidef (hY.posSemidef.conjTranspose_mul_mul_same M)).1
  have hAP := mm_trace_posSemidef (Matrix.posSemidef_self_mul_conjTranspose M)
  set A := (aOf b E X).re
  have hAeq : aOf b E X = (A : ℂ) := by
    refine Complex.ext (by simp [A]) ?_
    simp only [aOf, Complex.ofReal_im]
    rw [hAP.2]; simp [Complex.mul_im]
  have hheq : hOf b E X = (h : ℂ) := by simp only [hOf, h, Complex.mul_conj]; rfl
  have hward := mm_ward X M (zetaX b E X) hzM
  have hy : ((W : ℂ)⁻¹ * (Mᴴ * passiveY X * M).trace).re = u / W := by
    rw [show ((W : ℂ)⁻¹) = (((W : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul,
      div_eq_inv_mul]
  rw [hy] at hward
  obtain ⟨hm1, hm2⟩ := meanTr_eq_blk b E X hG
  have hd1 : ‖meanTr b E X 0 - (W : ℂ)⁻¹ * M.trace‖ ≤ CD / (W : ℝ) ^ 2 := by
    rw [hm1]; exact (norm_normTrace_sub_le _ _).trans hB0
  have hd2 : ‖meanTr b E X 3 - v‖ ≤ CD / (W : ℝ) ^ 2 := by
    have e1 := normTrace_smul_one hW1 v
    rw [hm2]
    calc _ = ‖(W : ℂ)⁻¹ * (blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 1 1).trace -
          (W : ℂ)⁻¹ * (v • (1 : Matrix (Fin W) (Fin W) ℂ)).trace‖ := by rw [e1]
      _ ≤ _ := (norm_normTrace_sub_le _ _).trans hB1
  have hι : (zetaX b E X).im = (1 - 2 * b) * (-(meanTr b E X 0).im) +
      b * (-(meanTr b E X 3).im) := im_zetaOf b E _ _
  have hvim : v.im = -h * (etaZ b E - b * (meanTr b E X 0).im) := by
    have := mm_inv_im (boundaryZ b E - (b : ℂ) * meanTr b E X 0)
    rw [show (boundaryZ b E - (b : ℂ) * meanTr b E X 0)⁻¹ = v from rfl] at this
    rw [this, Complex.mul_conj, Complex.ofReal_re, Complex.sub_im, Complex.im_ofReal_mul]; rfl
  have hE₁ := mm_im_algebra hb0 hb (by positivity) hhhi hward hι hvim hd1 hd2
  set ι := (zetaX b E X).im
  set k := (1 - 2 * b) + b ^ 2 * h
  set L := 1 - k * A
  set D := b * h * etaZ b E + k * (u / W)
  have hsL : ‖sOne b E X * (L : ℂ) - ((b * h : ℝ) : ℂ)‖ ≤ C2 / (W : ℝ) ^ 2 := by
    rw [hAeq, hheq] at hS
    convert hS using 2; simp only [L, k, khOf, hheq]; push_cast; ring
  have hDpos : 0 < D := by
    have : 0 ≤ k * (u / W) := by
      have : 0 ≤ k := by have : 0 ≤ 1 - 2 * b := by linarith
                         positivity
      positivity
    have : 0 < b * h * etaZ b E := by have : 0 < h := by linarith
                                      positivity
    simp only [D]; linarith
  have hres := mm_re_s hsL (show ι * L = D + (ι * L - D) by ring) hsn hDpos
  have he0 : 0 ≤ e := le_trans (by positivity) hWe
  have hε : |ι| * (C2 / (W : ℝ) ^ 2) + Cf * |ι * L - D| ≤ (Iz * C2 + Cf * (2 * CD)) * e := by
    have a1 : |ι| * (C2 / (W : ℝ) ^ 2) ≤ Iz * C2 * e := by
      rw [div_eq_mul_one_div, ← mul_assoc]
      exact mul_le_mul (mul_le_mul_of_nonneg_right hιb hC2) hWe (by positivity)
        (by have := (abs_nonneg ι).trans hιb; positivity)
    have a2 : Cf * |ι * L - D| ≤ Cf * (2 * CD) * e := by
      rw [mul_assoc]; refine mul_le_mul_of_nonneg_left (hE₁.trans ?_) hCf
      rw [mul_assoc]; refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      calc CD / (W : ℝ) ^ 2 = CD * (1 / (W : ℝ) ^ 2) := by ring
        _ ≤ CD * e := mul_le_mul_of_nonneg_left hWe hCD
    calc _ ≤ Iz * C2 * e + Cf * (2 * CD) * e := add_le_add a1 a2
      _ = _ := by ring
  refine hres.trans (div_le_div_of_nonneg_right ?_ hDpos.le)
  have : b * h * ι = (b : ℝ) * h * ι := rfl
  linarith

/-- The on-domain bound, from the matched values and `Re s₁`. -/
theorem mm_onDomain {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    (hW1 : 1 ≤ W) {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosDef) {Cm Cf e ε : ℝ}
    (hCm : 0 ≤ Cm) (hCf : 0 ≤ Cf) (he0 : 0 ≤ e) (he1 : e ≤ 1) (hWe : 1 / (W : ℝ) ^ 2 ≤ e)
    (hε : 0 ≤ ε) (hzζ : ‖boundaryZ b E - zetaX b E X‖ ≤ Cm * e)
    (hKM1 : ‖kmOf b E X - 1‖ ≤ Cm * e) (hh1 : |Complex.normSq (vOf b E X) - 1| ≤ Cm * e)
    (hCme : Cm * e ≤ 1 / 2)
    (hU : ‖matrixExpect (freshLaw W b) (freshU b E X) -
      sOne b E X • (kmOf b E X * (kmOf b E X)ᴴ)‖ ≤ Cf / (W : ℝ) ^ 2)
    (hsre : (sOne b E X).re ≤ (b * Complex.normSq (vOf b E X) * (zetaX b E X).im + ε) /
      (b * Complex.normSq (vOf b E X) * etaZ b E + ((1 - 2 * b) + b ^ 2 * Complex.normSq (vOf b E X)) *
        (((mOf b E X)ᴴ * passiveY X * mOf b E X).trace.re / W))) :
    (passiveQ b E X * matrixExpect (freshLaw W b) (freshU b E X)).trace.re ≤
      passiveMass b E X / (1 + alphaCoef b E * passiveMass b E X / W) +
        (Cm / etaZ b E + 2 * Cm + Cm ^ 2 + Cm / etaZ b E * (2 * Cm + Cm ^ 2) +
          (1 + Cm / etaZ b E) * (1 + Cm) ^ 2 * ((1 - 2 * b) / b * 2 * Cm / (4 * etaZ b E ^ 2))) *
          e * passiveMass b E X +
        (1 + Cm) ^ 2 * passiveMass b E X * ε * (2 / (b * etaZ b E)) + Cf * e * passiveMass b E X := by
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW1
  have hYs := hY.posSemidef
  set q := passiveMass b E X
  have hq : 0 ≤ q := passiveMass_nonneg b E hYs
  obtain ⟨-, hRz⟩ := nearPencil_inverse hb0 hb h1 h2 hYs
  have hKMeq : kmOf b E X = (boundaryZ b E • 1 - X) * mOf b E X :=
    (blkAt_kHat_mul_zero b E X _).1
  have hRKM : passiveResolvent b E X * kmOf b E X = mOf b E X := by
    rw [hKMeq, ← Matrix.mul_assoc, hRz, Matrix.one_mul]
  obtain ⟨hu0, -, huq, hdec⟩ := mm_trace_decomp (Q := passiveQ b E X)
    (U := matrixExpect (freshLaw W b) (freshU b E X)) (sOne b E X) hYs rfl hRKM
  set u := ((mOf b E X)ᴴ * passiveY X * mOf b E X).trace.re
  have hKMle : ‖kmOf b E X‖ ≤ 1 + Cm * e := by
    have := norm_add_le (kmOf b E X - 1) 1
    rw [sub_add_cancel] at this
    have h1' : ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ 1 := PassiveLayer.norm_one_le'
    linarith
  set Λ := max (‖kmOf b E X‖ ^ 2) 1
  have hΛ1 : 1 ≤ Λ := le_max_right _ _
  have hCe0 : 0 ≤ Cm * e := mul_nonneg hCm he0
  have hΛ' : Λ ≤ (1 + Cm * e) ^ 2 := max_le
    (pow_le_pow_left₀ (norm_nonneg _) hKMle 2) (one_le_pow₀ (by linarith))
  have hΛC : Λ ≤ (1 + Cm) ^ 2 :=
    hΛ'.trans (pow_le_pow_left₀ (by linarith)
      (by linarith [mul_le_of_le_one_right hCm he1]) 2)
  have huΛ : u ≤ Λ * q := (show u ≤ ‖kmOf b E X‖ ^ 2 * q from huq).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hq)
  have hhlo : 1 / 2 ≤ Complex.normSq (vOf b E X) := by
    have := neg_abs_le (Complex.normSq (vOf b E X) - 1); linarith
  have hιη : |(zetaX b E X).im - etaZ b E| ≤ Cm * e := by
    have : (zetaX b E X).im - etaZ b E = -(boundaryZ b E - zetaX b E X).im := by
      simp only [etaZ, Complex.sub_im]; ring
    rw [this, abs_neg]; exact (Complex.abs_im_le_norm _).trans hzζ
  have hqW := mm_passiveMass_le (b := b) (by linarith) h1 h2 X
  have hfin := mm_scalar_final hη hb0 hb hhlo hh1 hu0 huΛ hΛ1 hΛ' hq hqW hWpos hιη he0 he1 hCm
    hε hsre
  have hG0eq : q / (1 + (1 - b) ^ 2 / (b * etaZ b E) * q / W) =
      q / (1 + alphaCoef b E * q / W) := by rw [alphaCoef]
  rw [hG0eq] at hfin
  have hΔq : ‖matrixExpect (freshLaw W b) (freshU b E X) -
      sOne b E X • (kmOf b E X * (kmOf b E X)ᴴ)‖ * q ≤ Cf * e * q := by
    refine mul_le_mul_of_nonneg_right (hU.trans ?_) hq
    rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hWe hCf
  have herr : Λ * q * ε * (2 / (b * etaZ b E)) ≤ (1 + Cm) ^ 2 * q * ε * (2 / (b * etaZ b E)) := by
    have : 0 ≤ q * ε * (2 / (b * etaZ b E)) := by positivity
    calc Λ * q * ε * (2 / (b * etaZ b E)) = Λ * (q * ε * (2 / (b * etaZ b E))) := by ring
      _ ≤ (1 + Cm) ^ 2 * (q * ε * (2 / (b * etaZ b E))) := mul_le_mul_of_nonneg_right hΛC this
      _ = _ := by ring
  have hdec' : (passiveQ b E X * matrixExpect (freshLaw W b) (freshU b E X)).trace.re ≤
      (sOne b E X).re * u + ‖matrixExpect (freshLaw W b) (freshU b E X) -
        sOne b E X • (kmOf b E X * (kmOf b E X)ᴴ)‖ * q := hdec
  have huq' : u ≤ ‖kmOf b E X‖ ^ 2 * q := huq
  linarith only [hdec', hΔq, herr, hfin]

/-- The mass mean for strictly passive inputs. -/
theorem massMean_strict (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef →
        (passiveQ b E X * matrixExpect (freshLaw W b) (freshU b E X)).trace.re ≤
          passiveMass b E X / (1 + alphaCoef b E * passiveMass b E X / W) +
            C * (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2) * passiveMass b E X := by
  have hη := etaZ_pos b E (by linarith) h1 h2
  obtain ⟨Cf, Wf, hCf, hF⟩ := freshU_mean hA hb0 hb h1 h2
  obtain ⟨C2, W2, hC2, hS1⟩ := scalarS1 hA hb0 hb h1 h2
  obtain ⟨CD, WD, hCD, hD⟩ := dressedBlocks hA hb0 hb h1 h2
  obtain ⟨d₀, Cm, Wm, hd₀, hCm, hm0⟩ := mm_matched0 hA hb0 hb h1 h2
  set η := etaZ b E
  set c := 1 - 2 * b
  have hc : 0 ≤ c := by simp only [c]; linarith
  set d₁ := min d₀ (min (1 / (4 * Cm + 4)) (1 / 2))
  have hd₁ : 0 < d₁ := lt_min hd₀ (lt_min (by positivity) (by norm_num))
  have hd₁0 : d₁ ≤ d₀ := min_le_left _ _
  have hd₁m : d₁ ≤ 1 / (4 * Cm + 4) := (min_le_right _ _).trans (min_le_left _ _)
  have hd₁h : d₁ ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  set C₁ := Cf * Cf * Cf + Cf
  set Iz := ‖boundaryZ b E‖ + 1
  set Kh := c / b * 2 * Cm / (4 * η ^ 2)
  set Cmain := Cm / η + 2 * Cm + Cm ^ 2 + Cm / η * (2 * Cm + Cm ^ 2) +
    (1 + Cm / η) * (1 + Cm) ^ 2 * Kh
  set Cerr := (1 + Cm) ^ 2 * (Iz * C2 + Cf * (2 * CD)) * (2 / (b * η)) + Cf
  refine ⟨Cmain + Cerr + C₁ / d₁, max (max (max Wf W2) (max WD Wm)) ⌈d₁⁻¹⌉₊,
    by positivity, fun W hW X hX => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hWf, hW2⟩, hWD, hWm⟩, hWd⟩ := hW
  have hY := hX.posSemidef
  obtain ⟨hKMn, hsn, hU⟩ := hF W hWf X hX
  obtain ⟨hW1, -, hM, hv, -, -, hB0, hB1, hG, hzM, -⟩ := hD W hWD X hX
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW1
  have hW1r : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  set Q := passiveQ b E X
  set q := passiveMass b E X
  set U := matrixExpect (freshLaw W b) (freshU b E X)
  set δ := jetDistance0 b E X
  set e := δ + (W : ℝ)⁻¹ ^ 2
  have hQ : Q.PosSemidef := hY.conjTranspose_mul_mul_same _
  have hq : 0 ≤ q := passiveMass_nonneg b E hY
  have hδ : 0 ≤ δ := norm_nonneg _
  have hWe : (W : ℝ)⁻¹ ^ 2 ≤ e := by simp only [e]; linarith
  have hW2le : (W : ℝ)⁻¹ ^ 2 = 1 / (W : ℝ) ^ 2 := by rw [inv_pow, one_div]
  set α := alphaCoef b E
  have hα : 0 ≤ α := by simp only [α, alphaCoef]; positivity
  set G0 := q / (1 + α * q / W)
  have hG0 : 0 ≤ G0 := by positivity
  have hG0q : G0 ≤ q := div_le_self hq (by
    have : 0 ≤ α * q / W := by positivity
    linarith)
  -- crude bound
  have hUn : ‖U‖ ≤ C₁ := by
    have h := norm_add_le (U - sOne b E X • (kmOf b E X * (kmOf b E X)ᴴ))
      (sOne b E X • (kmOf b E X * (kmOf b E X)ᴴ))
    rw [sub_add_cancel] at h
    have h2' : ‖sOne b E X • (kmOf b E X * (kmOf b E X)ᴴ)‖ ≤ Cf * (Cf * Cf) := by
      refine (norm_smul_le _ _).trans (mul_le_mul hsn ?_ (norm_nonneg _) hCf)
      refine (Matrix.l2_opNorm_mul _ _).trans ?_
      rw [Matrix.l2_opNorm_conjTranspose]; exact mul_le_mul hKMn hKMn (norm_nonneg _) hCf
    have h3 : Cf / (W : ℝ) ^ 2 ≤ Cf := div_le_self hCf (by nlinarith)
    simp only [C₁]; linarith
  have hcrude : (Q * U).trace.re ≤ C₁ * q :=
    (mm_re_trace_le hQ).trans (mul_le_mul_of_nonneg_right hUn hq)
  by_cases hdom : δ ≤ d₁
  swap
  · push Not at hdom
    have : C₁ * q ≤ C₁ / d₁ * (δ * q) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hd₁]
      have : 0 ≤ C₁ := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hdom.le (mul_nonneg this hq)]
    have h4 : 0 ≤ (Cmain + Cerr) * (e * q) := by positivity
    have h5 : C₁ / d₁ * (δ * q) ≤ C₁ / d₁ * (e * q) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (by simp only [e]; linarith [sq_nonneg ((W : ℝ)⁻¹)]) hq) (by positivity)
    have e6 : G0 + (Cmain + Cerr + C₁ / d₁) * e * q =
        G0 + (Cmain + Cerr) * (e * q) + C₁ / d₁ * (e * q) := by ring
    rw [e6]
    calc (Q * U).trace.re ≤ C₁ / d₁ * (δ * q) := hcrude.trans this
      _ ≤ _ := by linarith
  -- on the domain
  have hWinv : (W : ℝ)⁻¹ ≤ d₁ := by
    rw [inv_le_comm₀ hWpos hd₁]; exact (Nat.le_ceil _).trans (by exact_mod_cast hWd)
  have hWsq : (W : ℝ)⁻¹ ^ 2 ≤ d₁ := by
    have : (W : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hW1r
    nlinarith [inv_nonneg.mpr hWpos.le]
  have he1 : e ≤ 1 := by simp only [e]; linarith
  have hCme : Cm * e ≤ 1 / 2 := by
    have : e ≤ 2 / (4 * Cm + 4) := by
      simp only [e]; have := hd₁m; rw [show (2 : ℝ) / (4 * Cm + 4) = 2 * (1 / (4 * Cm + 4)) by ring]
      linarith
    calc Cm * e ≤ Cm * (2 / (4 * Cm + 4)) := mul_le_mul_of_nonneg_left this hCm
      _ ≤ 1 / 2 := by rw [mul_div_assoc', div_le_iff₀ (by positivity)]; linarith
  obtain ⟨hzζ, hKM1, hh1⟩ := hm0 W hWm X hX (hdom.trans hd₁0)
  have he0 : 0 ≤ e := by simp only [e]; positivity
  have hheq : hOf b E X - 1 = ((Complex.normSq (vOf b E X) - 1 : ℝ) : ℂ) := by
    simp only [hOf, Complex.mul_conj]; push_cast; ring
  have hh1' : |Complex.normSq (vOf b E X) - 1| ≤ Cm * e := by
    rw [hheq, Complex.norm_real, Real.norm_eq_abs] at hh1; exact hh1
  have hW2e : 1 / (W : ℝ) ^ 2 ≤ e := by rw [← hW2le]; exact hWe
  have hιb : |(zetaX b E X).im| ≤ Iz := by
    have h' : |(zetaX b E X).im| ≤ ‖zetaX b E X‖ := Complex.abs_im_le_norm _
    have h'' : ‖zetaX b E X‖ ≤ ‖boundaryZ b E‖ + ‖boundaryZ b E - zetaX b E X‖ := by
      have := norm_sub_le (boundaryZ b E) (boundaryZ b E - zetaX b E X)
      rwa [sub_sub_cancel] at this
    simp only [Iz]; linarith
  have hsre := mm_sre hW1 hb0 hb h1 h2 hX hC2 hCf hCD hG hB0 hB1 hzM (hS1 W hW2 X hX).2.2 hsn
    (hh1'.trans hCme) hιb hW2e
  have hε : 0 ≤ (Iz * C2 + Cf * (2 * CD)) * e := by positivity
  have hon := mm_onDomain hb0 hb h1 h2 hW1 hX hCm hCf he0 he1 hW2e hε hzζ hKM1 hh1' hCme hU hsre
  have key : (Q * U).trace.re ≤ G0 + Cmain * e * q +
      (1 + Cm) ^ 2 * q * ((Iz * C2 + Cf * (2 * CD)) * e) * (2 / (b * η)) + Cf * e * q := hon
  have e7 : G0 + (Cmain + Cerr + C₁ / d₁) * e * q = G0 + Cmain * e * q +
      ((1 + Cm) ^ 2 * q * ((Iz * C2 + Cf * (2 * CD)) * e) * (2 / (b * η)) + Cf * e * q) +
      C₁ / d₁ * e * q := by simp only [Cerr]; ring
  have h8 : 0 ≤ C₁ / d₁ * e * q := by positivity
  rw [e7]
  linarith only [key, h8]

end BlockBand.Transmission.SourceMixing
