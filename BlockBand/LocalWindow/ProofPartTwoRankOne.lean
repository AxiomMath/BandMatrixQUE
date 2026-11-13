module

public import BlockBand.LocalWindow.ProofPartTwoObservable
public import BlockBand.LocalWindow.ProofCertificateRegular

/-!
# The pole certificate for the rank-one family

`ProofETH.rootRectangle_of_poleCertificate` gives the root rectangle of `F̂(e)` from
`certErrHat(e) ≤ ε_c`. Here the same holds for **every** Hermitian `F'` with `F' - F̂(e)` of rank
one (in particular `F_reg(e) + ρ ww*` for every real `ρ` off crowding, and `F(e)` itself at a
nonpole `e`), with the same constants, provided `2/(W s √κ) ≤ ε_c` (large `W`). The certificate
`χ` of the regularity certificate lemma moves by at most `1/(W s Im μ)` under a rank-one change
(`norm_certificateChi_sub_le_rankOne`), and `BlockBand.Palm.certificate_full_uniform`
applies to any Hermitian matrix.

## Main results

* `norm_certificateMatrixTrace_sub_le_rankOne`, **`norm_certificateChi_sub_le_rankOne`**.
* `norm_trace_le_card_mul_opNorm`, **`norm_certificateChi_sub_le`**: `χ` is Lipschitz in
  `(F, E, μ)`: `|χ₁ - χ₂| ≤ (‖F₁ - F₂‖ + |E₁ - E₂| + c|μ₁ - μ₂|)/(c² Im μ₁ Im μ₂) + |μ₁ - μ₂|`
  (for moving the certificate from a grid energy to a nearby energy).
* **`rootRectangle_rankOne_of_poleCertificate`**: fixed `b ∈ (0, 1/2)`, `κ > 0`; constants
  `ε_c, r, s₀, v₀ > 0`; for every Hermitian `F'` with `F' - F̂(e) = a b*`: Dyson roots of `F'`
  with `v₀ ≤ Im m ≤ v₀⁻¹` at every `x + iη`, `|x - e| ≤ r`, `0 ≤ η ≤ 1`, `s' ∈ [s - s₀, s]`.
* `isHermitian_rankOne`, `truncF_add_rankOne_sub`.
* **`pairRootRectangle_rankOne_family`**: for every real `ρ` and vector `w`,
  `PairRootRectangle (F̂(e) + ρ ww* - e) s' 0 r v₀` (the grid deformations `K_g` of the
  bounded-`ρ` range, uniformly in `ρ`).
* `PairRootRectangle.mono`: shrinking the rectangle.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofPartTwo

open Matrix Set
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs
open BlockBand.LocalWindow.ProofCount BlockBand.LocalWindow.ProofCertificate
open BlockBand.LocalWindow.ProofETH
open scoped Matrix.Norms.L2Operator ComplexConjugate

section Generic

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Rank one at fixed height, normalized trace**: for Hermitian `F₁, F₂` with
`F₁ - F₂ = a bᵀ` and `Im w ≠ 0`, `|⟨(F₁ - w)⁻¹⟩ - ⟨(F₂ - w)⁻¹⟩| ≤ 2/(N |Im w|)`. -/
theorem norm_certificateMatrixTrace_sub_le_rankOne {F₁ F₂ : Matrix ι ι ℂ}
    (hF₁ : F₁.IsHermitian) (hF₂ : F₂.IsHermitian) (a b : ι → ℂ) (hD : F₁ - F₂ = vecMulVec a b)
    {w : ℂ} (hw : w.im ≠ 0) :
    ‖BlockBand.Palm.certificateMatrixTrace F₁ w - BlockBand.Palm.certificateMatrixTrace F₂ w‖ ≤
      2 / (Fintype.card ι * |w.im|) := by
  unfold BlockBand.Palm.certificateMatrixTrace BlockBand.Palm.certificateMatrixResolvent
  have h := norm_weightedTrace_resolvent_sub_le hF₁ hF₂ hw a b hD (fun _ => 1) (fun _ => by simp)
  simp only [one_mul] at h
  rw [← sub_div, ← trace_sub, norm_div, Complex.norm_natCast]
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | hpos
  · rw [h0]; simp
  have hN : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr hpos
  have hwa : 0 < |w.im| := abs_pos.mpr hw
  rw [div_le_div_iff₀ hN (mul_pos hN hwa)]
  have e : ((F₁ - w • (1 : Matrix ι ι ℂ))⁻¹ - (F₂ - w • (1 : Matrix ι ι ℂ))⁻¹).trace =
      ∑ x, ((F₁ - w • (1 : Matrix ι ι ℂ))⁻¹ - (F₂ - w • (1 : Matrix ι ι ℂ))⁻¹) x x := rfl
  rw [e]
  have h' : ‖∑ x, ((F₁ - w • (1 : Matrix ι ι ℂ))⁻¹ - (F₂ - w • (1 : Matrix ι ι ℂ))⁻¹) x x‖ *
      |w.im| ≤ 2 := by
    have := mul_le_mul_of_nonneg_right h hwa.le
    rwa [mul_assoc, inv_mul_cancel₀ hwa.ne', mul_one] at this
  nlinarith

/-- **The certificate `χ` under a rank-one change**: for
Hermitian `F₁, F₂` with `F₁ - F₂ = a bᵀ`, `c > 0` and `Im μ > 0`,
`|χ(F₁, c, E, μ) - χ(F₂, c, E, μ)| ≤ 2/(N c Im μ)`. -/
theorem norm_certificateChi_sub_le_rankOne {F₁ F₂ : Matrix ι ι ℂ} (hF₁ : F₁.IsHermitian)
    (hF₂ : F₂.IsHermitian) (a b : ι → ℂ) (hD : F₁ - F₂ = vecMulVec a b) {c E : ℝ} (hc : 0 < c)
    {μ : ℂ} (hμ : 0 < μ.im) :
    ‖BlockBand.Palm.certificateChi F₁ c E μ - BlockBand.Palm.certificateChi F₂ c E μ‖ ≤
      2 / (Fintype.card ι * (c * μ.im)) := by
  unfold BlockBand.Palm.certificateChi
  have hwim : ((E : ℂ) + (c : ℂ) * μ).im = c * μ.im := by simp [Complex.mul_im]
  have hw : ((E : ℂ) + (c : ℂ) * μ).im ≠ 0 := by rw [hwim]; positivity
  have h := norm_certificateMatrixTrace_sub_le_rankOne hF₁ hF₂ a b hD hw
  rw [hwim, abs_of_pos (mul_pos hc hμ)] at h
  rw [sub_sub_sub_cancel_right]
  exact h

/-- `|Tr X| ≤ N ‖X‖` (`L²` operator norm). -/
theorem norm_trace_le_card_mul_opNorm (X : Matrix ι ι ℂ) :
    ‖X.trace‖ ≤ Fintype.card ι * ‖X‖ := by
  have hdiag : ∀ a, ‖X a a‖ ≤ ‖X‖ := by
    intro a
    have h := norm_quadForm_le X (Pi.single a 1)
    have h1 : star (Pi.single a (1 : ℂ)) ⬝ᵥ (X *ᵥ Pi.single a 1) = X a a := by
      rw [mulVec_single_one]
      simp [dotProduct, Pi.single_apply]
    have h2 : sqNorm (Pi.single a (1 : ℂ) : ι → ℂ) = 1 := by
      unfold sqNorm
      rw [Finset.sum_eq_single a (fun b _ hb => by simp [hb]) (by simp)]
      simp
    rwa [h1, h2, mul_one] at h
  calc ‖X.trace‖ ≤ ∑ a, ‖X a a‖ := norm_sum_le _ _
    _ ≤ ∑ _a : ι, ‖X‖ := Finset.sum_le_sum fun a _ => hdiag a
    _ = Fintype.card ι * ‖X‖ := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

/-- **The certificate `χ` is Lipschitz in `(F, E, μ)`** (moving a certificate from a grid energy
to a nearby one): for Hermitian `F₁, F₂`, `c > 0`, `Im μ_j > 0`,
`|χ(F₁,c,E₁,μ₁) - χ(F₂,c,E₂,μ₂)| ≤
  (‖F₁ - F₂‖ + |E₁ - E₂| + c|μ₁ - μ₂|)/((c Im μ₁)(c Im μ₂)) + |μ₁ - μ₂|`. -/
theorem norm_certificateChi_sub_le [Nonempty ι] {F₁ F₂ : Matrix ι ι ℂ} (hF₁ : F₁.IsHermitian)
    (hF₂ : F₂.IsHermitian) {c E₁ E₂ : ℝ} (hc : 0 < c) {μ₁ μ₂ : ℂ} (hμ₁ : 0 < μ₁.im)
    (hμ₂ : 0 < μ₂.im) :
    ‖BlockBand.Palm.certificateChi F₁ c E₁ μ₁ - BlockBand.Palm.certificateChi F₂ c E₂ μ₂‖ ≤
      (‖F₁ - F₂‖ + |E₁ - E₂| + c * ‖μ₁ - μ₂‖) / ((c * μ₁.im) * (c * μ₂.im)) + ‖μ₁ - μ₂‖ := by
  unfold BlockBand.Palm.certificateChi BlockBand.Palm.certificateMatrixTrace
    BlockBand.Palm.certificateMatrixResolvent
  set w₁ : ℂ := (E₁ : ℂ) + (c : ℂ) * μ₁ with hw₁def
  set w₂ : ℂ := (E₂ : ℂ) + (c : ℂ) * μ₂ with hw₂def
  have hw₁im : w₁.im = c * μ₁.im := by simp [w₁, Complex.mul_im]
  have hw₂im : w₂.im = c * μ₂.im := by simp [w₂, Complex.mul_im]
  have hp₁ : 0 < c * μ₁.im := mul_pos hc hμ₁
  have hp₂ : 0 < c * μ₂.im := mul_pos hc hμ₂
  have hw₁ : w₁.im ≠ 0 := by rw [hw₁im]; exact hp₁.ne'
  have hw₂ : w₂.im ≠ 0 := by rw [hw₂im]; exact hp₂.ne'
  set R₁ := (F₁ - w₁ • (1 : Matrix ι ι ℂ))⁻¹
  set R₂ := (F₂ - w₂ • (1 : Matrix ι ι ℂ))⁻¹
  have hres := ProofETH.inv_sub_inv (det_resolvent_ne_zero hF₁ hw₁) (det_resolvent_ne_zero hF₂ hw₂)
  have hR₁ : ‖R₁‖ ≤ (c * μ₁.im)⁻¹ := by
    have := opNorm_resolvent_le hF₁ hw₁; rwa [hw₁im, abs_of_pos hp₁] at this
  have hR₂ : ‖R₂‖ ≤ (c * μ₂.im)⁻¹ := by
    have := opNorm_resolvent_le hF₂ hw₂; rwa [hw₂im, abs_of_pos hp₂] at this
  have hX : F₂ - w₂ • (1 : Matrix ι ι ℂ) - (F₁ - w₁ • (1 : Matrix ι ι ℂ)) =
      -(F₁ - F₂) + (w₁ - w₂) • (1 : Matrix ι ι ℂ) := by
    rw [sub_smul]; abel
  have hwd : ‖w₁ - w₂‖ ≤ |E₁ - E₂| + c * ‖μ₁ - μ₂‖ := by
    have e : w₁ - w₂ = ((E₁ - E₂ : ℝ) : ℂ) + (c : ℂ) * (μ₁ - μ₂) := by
      rw [hw₁def, hw₂def]; push_cast; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hc]
  have hXn : ‖F₂ - w₂ • (1 : Matrix ι ι ℂ) - (F₁ - w₁ • (1 : Matrix ι ι ℂ))‖ ≤
      ‖F₁ - F₂‖ + |E₁ - E₂| + c * ‖μ₁ - μ₂‖ := by
    rw [hX]
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg]
    have := opNorm_smul_one_le (ι := ι) (w₁ - w₂)
    linarith
  have hRd : ‖R₁ - R₂‖ ≤ (‖F₁ - F₂‖ + |E₁ - E₂| + c * ‖μ₁ - μ₂‖) / ((c * μ₁.im) * (c * μ₂.im)) := by
    rw [hres]
    have hA0 : 0 ≤ ‖F₁ - F₂‖ + |E₁ - E₂| + c * ‖μ₁ - μ₂‖ := by positivity
    calc ‖R₁ * (F₂ - w₂ • (1 : Matrix ι ι ℂ) - (F₁ - w₁ • (1 : Matrix ι ι ℂ))) * R₂‖
        ≤ ‖R₁‖ * ‖F₂ - w₂ • (1 : Matrix ι ι ℂ) - (F₁ - w₁ • (1 : Matrix ι ι ℂ))‖ * ‖R₂‖ := by
          refine (norm_mul_le _ _).trans ?_
          exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ (c * μ₁.im)⁻¹ * (‖F₁ - F₂‖ + |E₁ - E₂| + c * ‖μ₁ - μ₂‖) * (c * μ₂.im)⁻¹ :=
          mul_le_mul (mul_le_mul hR₁ hXn (norm_nonneg _) (by positivity)) hR₂ (norm_nonneg _)
            (by positivity)
      _ = _ := by field_simp
  have hN : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have htr : ‖R₁.trace / (Fintype.card ι : ℂ) - R₂.trace / (Fintype.card ι : ℂ)‖ ≤ ‖R₁ - R₂‖ := by
    rw [← sub_div, ← trace_sub, norm_div, Complex.norm_natCast, div_le_iff₀ hN, mul_comm]
    exact norm_trace_le_card_mul_opNorm _
  calc ‖R₁.trace / (Fintype.card ι : ℂ) - μ₁ - (R₂.trace / (Fintype.card ι : ℂ) - μ₂)‖
      = ‖(R₁.trace / (Fintype.card ι : ℂ) - R₂.trace / (Fintype.card ι : ℂ)) - (μ₁ - μ₂)‖ := by
        congr 1; ring
    _ ≤ ‖R₁.trace / (Fintype.card ι : ℂ) - R₂.trace / (Fintype.card ι : ℂ)‖ + ‖μ₁ - μ₂‖ :=
        norm_sub_le _ _
    _ ≤ _ := add_le_add_left (htr.trans hRd) _

/-- `ρ w w*` is Hermitian for real `ρ`. -/
theorem isHermitian_rankOne (ρ : ℝ) (w : ι → ℂ) :
    (((ρ : ℂ)) • vecMulVec w (star w)).IsHermitian := by
  rw [IsHermitian, conjTranspose_smul, conjTranspose_vecMulVec, star_star, Complex.star_def,
    Complex.conj_ofReal]

end Generic

/-- A root rectangle may be shrunk: `|E' - E| + r' ≤ r` gives the rectangle at `E'` of radius
`r'`. -/
theorem PairRootRectangle.mono {p : Parameters} {i : ZMod p.n} {K : PairMatrix p i}
    {s E r v₀ E' r' : ℝ} (h : PairRootRectangle K s E r v₀) (hle : |E' - E| + r' ≤ r) :
    PairRootRectangle K s E' r' v₀ := by
  intro x hx η hη hη1
  refine h x ?_ η hη hη1
  calc |x - E| = |(x - E') + (E' - E)| := by ring_nf
    _ ≤ |x - E'| + |E' - E| := abs_add_le _ _
    _ ≤ r := by linarith

variable {p : Parameters} {i : ZMod p.n}

/-- **Root rectangle for every rank-one modification of `F̂(e)`** (the uniform
pole certificate and the regularity certificate, through
`BlockBand.Palm.certificate_full_uniform`). Fixed `b ∈ (0, 1/2)`, `κ > 0` first; then constants
`ε_c, r, s₀, v₀ > 0` (depending only on `b, κ`); for every admissible `p` with `p.b = b`, split
state with Hermitian `V`, truncation radius `ε`, `e ∈ bulkInterval κ` with
`certErrHat ε p i ω e ≤ ε_c` and `2/(W s √κ) ≤ ε_c` (`s = splitS p`), every Hermitian `F'` with
`F' - F̂(e) = a bᵀ` (rank at most one), `s' ∈ [s - s₀, s]`, `|x - e| ≤ r`, `0 ≤ η ≤ 1`: `F'` has
a Dyson root `m` at `x + iη` (variance `s'`) with `v₀ ≤ Im m ≤ v₀⁻¹`. Uniform in `F'`, in
particular in the rank-one parameter `ρ`. -/
theorem rootRectangle_rankOne_of_poleCertificate (b κ : ℝ) (hb : 0 < b) (hb' : b < 1 / 2)
    (hκ : 0 < κ) :
    ∃ εc r s₀ v₀ : ℝ, 0 < εc ∧ 0 < r ∧ 0 < s₀ ∧ 0 < v₀ ∧
      ∀ p : Parameters, p.b = b → ∀ (i : ZMod p.n) (om : SplitState p i)
        (_hV : om.2.2.IsHermitian) (ε e : ℝ), e ∈ bulkInterval κ → certErrHat ε p i om e ≤ εc →
        2 / ((p.W : ℝ) * splitS p * Real.sqrt κ) ≤ εc →
        ∀ F' : PairMatrix p i, F'.IsHermitian → ∀ a a' : PairSite p i → ℂ,
          F' - truncF ε om.1 om.2.1 om.2.2 e = vecMulVec a a' →
        ∀ s' : ℝ, splitS p - s₀ ≤ s' → s' ≤ splitS p →
          ∀ x : ℝ, |x - e| ≤ r → ∀ η : ℝ, 0 ≤ η → η ≤ 1 →
            ∃ m : ℂ, IsDysonRoot F' s' ((x : ℂ) + (η : ℂ) * Complex.I) m ∧ v₀ ≤ m.im ∧
              m.im ≤ v₀⁻¹ := by
  set c := min (1 - 2 * b) b with hcdef
  have hc : 0 < c := lt_min (by linarith) hb
  have hc1 : c < 1 := (min_le_right _ _).trans_lt (by linarith)
  have hV0 : 0 < Real.sqrt κ / 2 := by have := Real.sqrt_pos.mpr hκ; linarith
  obtain ⟨εf, r, s₀, v₀, C, hεf, hr, hs₀, -, hv₀, -, h⟩ :=
    BlockBand.Palm.certificate_full_uniform.{0} hc hc1 hV0
  refine ⟨εf / 2, r, s₀, v₀, half_pos hεf, hr, hs₀, hv₀, fun p hpb i om hV ε e he hcert hW F' hF'
    a a' hD s' hs1 hs2 x hx η hη hη1 => ?_⟩
  have hsp : splitS p = c := splitS_eq hpb
  have : Nonempty (PairSite p i) := ⟨⟨(i, ⟨0, p.W_pos⟩), Or.inl rfl⟩⟩
  have hW0 : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hsk : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  have him := sqrt_le_abs_matchedA_im hκ he
  have himle : (matchedA e).im ≤ 0 := by
    rw [matchedA_im]; have := Real.sqrt_nonneg (4 - e ^ 2); linarith
  have hVμ : Real.sqrt κ / 2 ≤ (conj (matchedA e)).im := by
    rw [Complex.conj_im]; rw [abs_of_nonpos himle] at him; exact him
  have hμpos : 0 < (conj (matchedA e)).im := hV0.trans_le hVμ
  have he2 : e ^ 2 ≤ 4 := by obtain ⟨h1, h2⟩ := he; nlinarith
  have hμ : ‖conj (matchedA e)‖ ≤ 1 := by rw [Complex.norm_conj, norm_matchedA he2]
  set F := truncF ε om.1 om.2.1 om.2.2 e
  have hF : F.IsHermitian := isHermitian_truncF ε om.1 om.2.1 hV e
  have hchi := (norm_certificateChi_le ε om hV e).trans hcert
  have hrk := norm_certificateChi_sub_le_rankOne hF' hF a a' hD (c := splitS p) (E := e)
    (BlockBand.Angular.PairCoareaBridge.splitS_pos p) hμpos
  have hcard : (Fintype.card (PairSite p i) : ℝ) = 2 * (p.W : ℝ) := by
    rw [BlockBand.Angular.FiberAngular.card_pairSite]; push_cast; ring
  rw [hcard] at hrk
  have hs : 0 < splitS p := BlockBand.Angular.PairCoareaBridge.splitS_pos p
  have hsmall : 2 / (2 * (p.W : ℝ) * (splitS p * (conj (matchedA e)).im)) ≤
      2 / ((p.W : ℝ) * splitS p * Real.sqrt κ) := by
    refine div_le_div_of_nonneg_left zero_le_two (by positivity) ?_
    have : (p.W : ℝ) * splitS p * Real.sqrt κ = 2 * (p.W : ℝ) * (splitS p * (Real.sqrt κ / 2)) := by
      ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hVμ hs.le) (by positivity)
  have hchi' : ‖BlockBand.Palm.certificateChi F' (splitS p) e (conj (matchedA e))‖ ≤ εf := by
    have h1 := norm_sub_le_norm_sub_add_norm_sub
      (BlockBand.Palm.certificateChi F' (splitS p) e (conj (matchedA e)))
      (BlockBand.Palm.certificateChi F (splitS p) e (conj (matchedA e))) 0
    simp only [sub_zero] at h1
    linarith
  rw [hsp] at hchi' hs1 hs2
  obtain ⟨heq, hlo, hhi⟩ :=
    (h (PairSite p i) F' hF' e (conj (matchedA e)) hVμ hμ hchi').1 s' hs1 hs2 x hx η hη hη1
  refine ⟨_, ?_, hlo, hhi⟩
  rw [isDysonRoot_iff, mul_comm (η : ℂ) Complex.I]
  exact ⟨hv₀.trans_le hlo, heq⟩

/-- `F̂(e) + ρ ww* - F̂(e) = (ρ w) w*`. -/
theorem truncF_add_rankOne_sub (ε : ℝ) (om : SplitState p i) (e ρ : ℝ) (w : PairSite p i → ℂ) :
    truncF ε om.1 om.2.1 om.2.2 e + ((ρ : ℂ)) • vecMulVec w (star w) -
        truncF ε om.1 om.2.1 om.2.2 e = vecMulVec ((ρ : ℂ) • w) (star w) := by
  rw [add_sub_cancel_left, smul_vecMulVec]

/-- **The pole certificate for the rank-one family, uniformly in `ρ`**: with
the constants of `rootRectangle_rankOne_of_poleCertificate`, for every real `ρ` and vector `w`,
the grid deformation `K_g = F̂(e) + ρ ww* - e` has the root rectangle
`PairRootRectangle K_g s' 0 r v₀` (centre `0`, radius `r`) for every `s' ∈ [s - s₀, s]`. -/
theorem pairRootRectangle_rankOne_family (b κ : ℝ) (hb : 0 < b) (hb' : b < 1 / 2)
    (hκ : 0 < κ) :
    ∃ εc r s₀ v₀ : ℝ, 0 < εc ∧ 0 < r ∧ 0 < s₀ ∧ 0 < v₀ ∧
      ∀ p : Parameters, p.b = b → ∀ (i : ZMod p.n) (om : SplitState p i)
        (_hV : om.2.2.IsHermitian) (ε e : ℝ), e ∈ bulkInterval κ → certErrHat ε p i om e ≤ εc →
        2 / ((p.W : ℝ) * splitS p * Real.sqrt κ) ≤ εc →
        ∀ (ρ : ℝ) (w : PairSite p i → ℂ) (s' : ℝ), splitS p - s₀ ≤ s' → s' ≤ splitS p →
          PairRootRectangle (truncF ε om.1 om.2.1 om.2.2 e + ((ρ : ℂ)) • vecMulVec w (star w) -
            (e : ℂ) • (1 : PairMatrix p i)) s' 0 r v₀ := by
  obtain ⟨εc, r, s₀, v₀, hεc, hr, hs₀, hv₀, h⟩ :=
    rootRectangle_rankOne_of_poleCertificate b κ hb hb' hκ
  refine ⟨εc, r, s₀, v₀, hεc, hr, hs₀, hv₀, fun p hpb i om hV ε e he hcert hW ρ w s' hs1 hs2 => ?_⟩
  intro x hx η hη hη1
  have hF' : (truncF ε om.1 om.2.1 om.2.2 e + ((ρ : ℂ)) • vecMulVec w (star w)).IsHermitian :=
    (isHermitian_truncF ε om.1 om.2.1 hV e).add (isHermitian_rankOne ρ w)
  have hx' : |(x + e) - e| ≤ r := by rw [add_sub_cancel_right]; simpa using hx
  obtain ⟨m, hm, hlo, -⟩ := h p hpb i om hV ε e he hcert hW _ hF' _ _
    (truncF_add_rankOne_sub ε om e ρ w) s' hs1 hs2 (x + e) hx' η hη hη1
  refine ⟨m, ?_, hlo⟩
  rw [isDysonRoot_sub_smul]
  have e1 : (x : ℂ) + (η : ℂ) * Complex.I + (e : ℂ) = ((x + e : ℝ) : ℂ) + (η : ℂ) * Complex.I := by
    push_cast; ring
  rw [e1]
  exact hm

end BlockBand.LocalWindow.ProofPartTwo
