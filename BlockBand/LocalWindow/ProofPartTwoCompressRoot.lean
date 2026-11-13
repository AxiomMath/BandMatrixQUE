module

public import BlockBand.LocalWindow.ProofPartTwoRankOne
public import BlockBand.LocalWindow.ProofPartTwoCompressETH

/-!
# The root rectangle of the compressed deformation

The compressed window estimate (`LocalWindow.ProofPartTwo.gue_not_compressWindowGood_le`) needs a
root rectangle of the compressed deformation `B₀ = U*F'U` at the compressed variance `s'`. It is
derived here directly from the regularity certificate
(`BlockBand.Palm.certificate_full_uniform`, for any Hermitian matrix of any dimension) applied
to `B₀` on `Fin (2W - 1)`: compressing to a codimension-one subspace moves the normalized trace of
the resolvent by `O(1/(N Im ω))`, so the certificate `χ` of `B₀` is within `O(1/(W s √κ))` of the
certificate of `F̂(e)`.

## Main results

* **`compress_certificateMatrixTrace_sub_le`** (generic): for Hermitian `F`, an isometry `U`
  with `1 - UU* = ww*`, `|κ| + 1 = |ι|`, `Im ω > 0`:
  `|⟨(U*FU - ω)⁻¹⟩ - ⟨(F - ω)⁻¹⟩| ≤ 4/(|κ| Im ω)` (Schur complement at `ρ = ∞` through
  `compress_resolvent_sub_le` at one finite `ρ`, plus the rank-one bound).
* `compress_certificateChi_sub_le`: the same for `χ`.
* **`rootRectangle_compress_of_poleCertificate`**: fixed `b ∈ (0, 1/2)`, `κ > 0`; constants
  `ε_c, r, s₀, v₀ > 0`; for every Hermitian `F'` with `F' - F̂(e)` of rank one, every isometry
  `U : ℂ^{2W-1} → ℂ^{pair}` with `1 - UU* = ww*`, `s' ∈ [s - s₀, s]`: Dyson roots of `U*F'U` with
  `v₀ ≤ Im m ≤ v₀⁻¹` at every `x + iη`, `|x - e| ≤ r`, `0 ≤ η ≤ 1`, provided `8/(W s √κ) ≤ ε_c`.
* `compressVar_mem_of_le`: `s(1 - 1/2W) ∈ [s - s₀, s]` once `s ≤ 2W s₀`.
* **`compressRootRectangle_family`**: the compressed grid deformation
  `U*(F' - e)U` has `RootRectangle · s' 0 r v₀` (the hypothesis of
  `gue_not_compressWindowGood_le`).
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

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- **Compression to a codimension-one subspace moves the normalized resolvent trace by
`O(1/(N Im ω))`** (the Schur complement at `ρ = ∞`): for Hermitian `F`, an
isometry `U` (`U*U = 1`) with `1 - UU* = ww*`, `|κ| + 1 = |ι|` and `Im ω > 0`,
`|⟨(U*FU - ω)⁻¹⟩_κ - ⟨(F - ω)⁻¹⟩_ι| ≤ 4/(|κ| Im ω)`. -/
theorem compress_certificateMatrixTrace_sub_le [Nonempty ι] [Nonempty κ]
    (hcard : Fintype.card κ + 1 = Fintype.card ι) {F : Matrix ι ι ℂ} (hF : F.IsHermitian)
    {U : Matrix ι κ ℂ} (hU : Uᴴ * U = 1) {w : ι → ℂ}
    (hPw : 1 - U * Uᴴ = vecMulVec w (star w)) {ω : ℂ} (hω : 0 < ω.im) :
    ‖BlockBand.Palm.certificateMatrixTrace (Uᴴ * F * U) ω -
        BlockBand.Palm.certificateMatrixTrace F ω‖ ≤ 4 / (Fintype.card κ * ω.im) := by
  set Nι : ℝ := (Fintype.card ι : ℝ) with hNι
  set Nκ : ℝ := (Fintype.card κ : ℝ) with hNκ
  have hNκ0 : 0 < Nκ := Nat.cast_pos.mpr Fintype.card_pos
  have hNι0 : 0 < Nι := Nat.cast_pos.mpr Fintype.card_pos
  have hNικ : Nι = Nκ + 1 := by rw [hNι, hNκ, ← hcard]; push_cast; ring
  set c := (1 + ‖F‖ / ω.im) ^ 3 with hc
  have hc0 : 0 ≤ c := by positivity
  set ρ : ℝ := ‖ω‖ + Nι * ω.im * c + 1 with hρdef
  have hρpos : 0 < ρ := by positivity
  have hρ : ‖ω‖ < |ρ| := by
    rw [abs_of_pos hρpos, hρdef]; have : 0 ≤ Nι * ω.im * c := by positivity
    linarith
  set Rρ := (F + (ρ : ℂ) • (1 - U * Uᴴ) - ω • (1 : Matrix ι ι ℂ))⁻¹ with hRρ
  set RB := (Uᴴ * F * U - ω • (1 : Matrix κ κ ℂ))⁻¹ with hRB
  set RF := (F - ω • (1 : Matrix ι ι ℂ))⁻¹ with hRF
  -- the Schur complement at one large `ρ`
  have h1 : ‖Rρ.trace - RB.trace‖ ≤ 1 / ω.im := by
    have htr : (U * RB * Uᴴ).trace = RB.trace := by
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]
    have hs := compress_resolvent_sub_le hF hU hω hρ
    rw [← htr, ← trace_sub]
    have hden : |ρ| - ‖ω‖ = Nι * ω.im * c + 1 := by rw [abs_of_pos hρpos, hρdef]; ring
    calc ‖(Rρ - U * RB * Uᴴ).trace‖ ≤ Nι * ‖Rρ - U * RB * Uᴴ‖ := compress_norm_trace_le _
      _ ≤ Nι * (c / (|ρ| - ‖ω‖)) := mul_le_mul_of_nonneg_left hs hNι0.le
      _ ≤ 1 / ω.im := by
          rw [hden, mul_div_assoc', div_le_div_iff₀ (by positivity) hω]
          nlinarith
  -- the rank-one bound
  have h2 : ‖Rρ.trace - RF.trace‖ ≤ 2 / ω.im := by
    have hD : F + (ρ : ℂ) • (1 - U * Uᴴ) - F = vecMulVec ((ρ : ℂ) • w) (star w) := by
      rw [add_sub_cancel_left, hPw, smul_vecMulVec]
    have h := norm_certificateMatrixTrace_sub_le_rankOne (isHermitian_compressFull hF U ρ) hF
      _ _ hD hω.ne'
    unfold BlockBand.Palm.certificateMatrixTrace BlockBand.Palm.certificateMatrixResolvent at h
    rw [← sub_div, norm_div, Complex.norm_natCast, abs_of_pos hω, ← trace_sub,
      div_le_div_iff₀ hNι0 (mul_pos hNι0 hω)] at h
    rw [trace_sub] at h
    rw [le_div_iff₀ hω]
    have h' : Nι * (‖Rρ.trace - RF.trace‖ * ω.im) ≤ Nι * 2 := by linarith
    exact le_of_mul_le_mul_left h' hNι0
  have h3 : ‖RF.trace‖ ≤ Nι / ω.im := by
    have h := compress_norm_trace_le RF
    have hR := opNorm_resolvent_le hF hω.ne'
    rw [abs_of_pos hω] at hR
    calc ‖RF.trace‖ ≤ Nι * ‖RF‖ := h
      _ ≤ Nι * ω.im⁻¹ := mul_le_mul_of_nonneg_left hR hNι0.le
      _ = Nι / ω.im := by rw [div_eq_mul_inv]
  have h4 : ‖RB.trace - RF.trace‖ ≤ 3 / ω.im := by
    have := norm_sub_le_norm_sub_add_norm_sub RB.trace Rρ.trace RF.trace
    have h1' : ‖RB.trace - Rρ.trace‖ ≤ 1 / ω.im := by rw [norm_sub_rev]; exact h1
    have e : 3 / ω.im = 1 / ω.im + 2 / ω.im := by ring
    linarith
  -- the normalizations
  unfold BlockBand.Palm.certificateMatrixTrace BlockBand.Palm.certificateMatrixResolvent
  rw [← hRB, ← hRF]
  have hnκ : (Fintype.card κ : ℂ) = ((Nκ : ℝ) : ℂ) := by rw [hNκ]; push_cast; rfl
  have hnι : (Fintype.card ι : ℂ) = ((Nκ : ℝ) : ℂ) + 1 := by
    rw [← hcard]; push_cast; rfl
  have hnκ0 : ((Nκ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hNκ0.ne'
  have hnι0 : ((Nκ : ℝ) : ℂ) + 1 ≠ 0 := by
    have : ((Nκ + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (0 : ℝ) < Nκ + 1).ne'
    exact_mod_cast this
  have e : RB.trace / (Fintype.card κ : ℂ) - RF.trace / (Fintype.card ι : ℂ) =
      (RB.trace - RF.trace) / ((Nκ : ℝ) : ℂ) +
        RF.trace / (((Nκ : ℝ) : ℂ) * (((Nκ : ℝ) : ℂ) + 1)) := by
    rw [hnκ, hnι]; field_simp; ring
  rw [e]
  have hn1 : ‖(((Nκ : ℝ) : ℂ))‖ = Nκ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hNκ0]
  have hn2 : ‖((Nκ : ℝ) : ℂ) * (((Nκ : ℝ) : ℂ) + 1)‖ = Nκ * Nι := by
    have : ((Nκ : ℝ) : ℂ) * (((Nκ : ℝ) : ℂ) + 1) = (((Nκ * (Nκ + 1)) : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), hNικ]
  refine (norm_add_le _ _).trans ?_
  rw [norm_div, norm_div, hn1, hn2]
  calc ‖RB.trace - RF.trace‖ / Nκ + ‖RF.trace‖ / (Nκ * Nι)
      ≤ (3 / ω.im) / Nκ + (Nι / ω.im) / (Nκ * Nι) :=
        add_le_add (div_le_div_of_nonneg_right h4 hNκ0.le)
          (div_le_div_of_nonneg_right h3 (by positivity))
    _ = 4 / (Nκ * ω.im) := by field_simp; ring

/-- **The certificate `χ` under compression**: under the
hypotheses of `compress_certificateMatrixTrace_sub_le`, `c > 0`, `Im μ > 0`:
`|χ(U*FU, c, E, μ) - χ(F, c, E, μ)| ≤ 4/(|κ| c Im μ)`. -/
theorem compress_certificateChi_sub_le [Nonempty ι] [Nonempty κ]
    (hcard : Fintype.card κ + 1 = Fintype.card ι) {F : Matrix ι ι ℂ} (hF : F.IsHermitian)
    {U : Matrix ι κ ℂ} (hU : Uᴴ * U = 1) {w : ι → ℂ}
    (hPw : 1 - U * Uᴴ = vecMulVec w (star w)) {c E : ℝ} (hc : 0 < c) {μ : ℂ} (hμ : 0 < μ.im) :
    ‖BlockBand.Palm.certificateChi (Uᴴ * F * U) c E μ - BlockBand.Palm.certificateChi F c E μ‖ ≤
      4 / (Fintype.card κ * (c * μ.im)) := by
  unfold BlockBand.Palm.certificateChi
  have hwim : ((E : ℂ) + (c : ℂ) * μ).im = c * μ.im := by simp [Complex.mul_im]
  have h := compress_certificateMatrixTrace_sub_le hcard hF hU hPw
    (ω := (E : ℂ) + (c : ℂ) * μ) (by rw [hwim]; positivity)
  rw [hwim] at h
  rw [sub_sub_sub_cancel_right]
  exact h

end Generic

variable {p : Parameters} {i : ZMod p.n}

/-- **Root rectangle of the compressed deformation from the pole certificate** (the uniform
pole certificate and the regularity certificate, through `BlockBand.Palm.certificate_full_uniform`
on `Fin (2W - 1)`). Fixed `b ∈ (0, 1/2)`, `κ > 0` first; then constants
`ε_c, r, s₀, v₀ > 0` (depending only on `b, κ`); for every admissible `p` with `p.b = b`, split
state with Hermitian `V`, truncation radius `ε`, `e ∈ bulkInterval κ` with
`certErrHat ε p i ω e ≤ ε_c` and `8/(W s √κ) ≤ ε_c` (`s = splitS p`), every Hermitian pair `F'`
with `F' - F̂(e) = a bᵀ` (rank at most one), every isometry `U : ℂ^{2W-1} → ℂ^{pair}` with
`1 - UU* = ww*`, `s' ∈ [s - s₀, s]`, `|x - e| ≤ r`, `0 ≤ η ≤ 1`: the compressed deformation
`U*F'U` has a Dyson root `m` at `x + iη` (variance `s'`, dimension `2W - 1`) with
`v₀ ≤ Im m ≤ v₀⁻¹`. Uniform in `F'` (in particular in the rank-one parameter `ρ`) and in `U`. -/
theorem rootRectangle_compress_of_poleCertificate (b κ : ℝ) (hb : 0 < b) (hb' : b < 1 / 2)
    (hκ : 0 < κ) :
    ∃ εc r s₀ v₀ : ℝ, 0 < εc ∧ 0 < r ∧ 0 < s₀ ∧ 0 < v₀ ∧
      ∀ p : Parameters, p.b = b → ∀ (i : ZMod p.n) (om : SplitState p i)
        (_hV : om.2.2.IsHermitian) (ε e : ℝ), e ∈ bulkInterval κ → certErrHat ε p i om e ≤ εc →
        8 / ((p.W : ℝ) * splitS p * Real.sqrt κ) ≤ εc →
        ∀ F' : PairMatrix p i, F'.IsHermitian → ∀ a a' : PairSite p i → ℂ,
          F' - truncF ε om.1 om.2.1 om.2.2 e = vecMulVec a a' →
        ∀ (U : Matrix (PairSite p i) (Fin (2 * p.W - 1)) ℂ) (w : PairSite p i → ℂ),
          Uᴴ * U = 1 → 1 - U * Uᴴ = vecMulVec w (star w) →
        ∀ s' : ℝ, splitS p - s₀ ≤ s' → s' ≤ splitS p →
          ∀ x : ℝ, |x - e| ≤ r → ∀ η : ℝ, 0 ≤ η → η ≤ 1 →
            ∃ m : ℂ, IsDysonRoot (Uᴴ * F' * U) s' ((x : ℂ) + (η : ℂ) * Complex.I) m ∧
              v₀ ≤ m.im ∧ m.im ≤ v₀⁻¹ := by
  set c := min (1 - 2 * b) b with hcdef
  have hc : 0 < c := lt_min (by linarith) hb
  have hc1 : c < 1 := (min_le_right _ _).trans_lt (by linarith)
  have hV0 : 0 < Real.sqrt κ / 2 := by have := Real.sqrt_pos.mpr hκ; linarith
  obtain ⟨εf, r, s₀, v₀, C, hεf, hr, hs₀, -, hv₀, -, h⟩ :=
    BlockBand.Palm.certificate_full_uniform.{0} hc hc1 hV0
  refine ⟨εf / 3, r, s₀, v₀, by positivity, hr, hs₀, hv₀, fun p hpb i om hV ε e he hcert hW F'
    hF' a a' hD U w hU hPw s' hs1 hs2 x hx η hη hη1 => ?_⟩
  have hsp : splitS p = c := splitS_eq hpb
  have : Nonempty (PairSite p i) := ⟨⟨(i, ⟨0, p.W_pos⟩), Or.inl rfl⟩⟩
  have : Nonempty (Fin (2 * p.W - 1)) := ⟨⟨0, by have := p.W_pos; omega⟩⟩
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
  have hs : 0 < splitS p := BlockBand.Angular.PairCoareaBridge.splitS_pos p
  have hchi := (norm_certificateChi_le ε om hV e).trans hcert
  -- the rank-one step
  have hrk := norm_certificateChi_sub_le_rankOne hF' hF a a' hD (c := splitS p) (E := e)
    hs hμpos
  have hcard : (Fintype.card (PairSite p i) : ℝ) = 2 * (p.W : ℝ) := by
    rw [BlockBand.Angular.FiberAngular.card_pairSite]; push_cast; ring
  rw [hcard] at hrk
  have hsmall1 : 2 / (2 * (p.W : ℝ) * (splitS p * (conj (matchedA e)).im)) ≤
      8 / ((p.W : ℝ) * splitS p * Real.sqrt κ) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : (p.W : ℝ) * splitS p * Real.sqrt κ ≤
        2 * ((p.W : ℝ) * splitS p * (conj (matchedA e)).im) := by
      have := mul_le_mul_of_nonneg_left hVμ (by positivity : (0 : ℝ) ≤ (p.W : ℝ) * splitS p)
      nlinarith
    nlinarith [mul_pos (mul_pos hW0 hs) hμpos]
  -- the compression step
  have hcardc : Fintype.card (Fin (2 * p.W - 1)) + 1 = Fintype.card (PairSite p i) := by
    rw [Fintype.card_fin, card_pairSite_cc]; have := p.W_pos; omega
  have hcomp := compress_certificateChi_sub_le hcardc hF' hU hPw (c := splitS p) (E := e)
    hs hμpos
  have hWc : (p.W : ℝ) ≤ (Fintype.card (Fin (2 * p.W - 1)) : ℝ) := by
    rw [Fintype.card_fin]; have := p.W_pos; exact_mod_cast (by omega : p.W ≤ 2 * p.W - 1)
  have hsmall2 : 4 / ((Fintype.card (Fin (2 * p.W - 1)) : ℝ) * (splitS p * (conj (matchedA e)).im))
      ≤ 8 / ((p.W : ℝ) * splitS p * Real.sqrt κ) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : (p.W : ℝ) * splitS p * Real.sqrt κ ≤
        2 * ((Fintype.card (Fin (2 * p.W - 1)) : ℝ) * (splitS p * (conj (matchedA e)).im)) := by
      have ha := mul_le_mul_of_nonneg_left hVμ (by positivity : (0 : ℝ) ≤ splitS p)
      have hb2 : (p.W : ℝ) * (splitS p * Real.sqrt κ) ≤
          (Fintype.card (Fin (2 * p.W - 1)) : ℝ) * (2 * (splitS p * (conj (matchedA e)).im)) :=
        mul_le_mul hWc (by linarith) (by positivity) (by positivity)
      nlinarith
    nlinarith [mul_pos (mul_pos hW0 hs) hμpos]
  have hchi' : ‖BlockBand.Palm.certificateChi (Uᴴ * F' * U) (splitS p) e (conj (matchedA e))‖ ≤
      εf := by
    have h1 := norm_sub_le_norm_sub_add_norm_sub
      (BlockBand.Palm.certificateChi (Uᴴ * F' * U) (splitS p) e (conj (matchedA e)))
      (BlockBand.Palm.certificateChi F' (splitS p) e (conj (matchedA e))) 0
    have h2 := norm_sub_le_norm_sub_add_norm_sub
      (BlockBand.Palm.certificateChi F' (splitS p) e (conj (matchedA e)))
      (BlockBand.Palm.certificateChi F (splitS p) e (conj (matchedA e))) 0
    simp only [sub_zero] at h1 h2
    linarith
  have hB : (Uᴴ * F' * U).IsHermitian := isHermitian_compress hF' U
  rw [hsp] at hchi' hs1 hs2
  obtain ⟨heq, hlo, hhi⟩ :=
    (h (Fin (2 * p.W - 1)) (Uᴴ * F' * U) hB e (conj (matchedA e)) hVμ hμ hchi').1 s' hs1 hs2
      x hx η hη hη1
  refine ⟨_, ?_, hlo, hhi⟩
  rw [isDysonRoot_iff, mul_comm (η : ℂ) Complex.I]
  exact ⟨hv₀.trans_le hlo, heq⟩

/-- The compressed variance lies in the certificate range: `s - s₀ ≤ s(1 - 1/2W) ≤ s` once
`0 ≤ s ≤ 2W s₀`. -/
theorem compressVar_mem_of_le {s s₀ : ℝ} (hs : 0 ≤ s) (hle : s ≤ 2 * (p.W : ℝ) * s₀) :
    s - s₀ ≤ compressVar p s ∧ compressVar p s ≤ s := by
  have hW0 : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  unfold compressVar
  have e : s * (1 - 1 / (2 * (p.W : ℝ))) = s - s / (2 * (p.W : ℝ)) := by field_simp
  rw [e]
  have h1 : s / (2 * (p.W : ℝ)) ≤ s₀ := by rw [div_le_iff₀ (by positivity)]; linarith
  have h2 : 0 ≤ s / (2 * (p.W : ℝ)) := by positivity
  constructor <;> linarith

/-- `U*(F' - e)U = U*F'U - e` for an isometry. -/
theorem compress_sub_smul_one (U : Matrix (PairSite p i) (Fin (2 * p.W - 1)) ℂ)
    (hU : Uᴴ * U = 1) (F' : PairMatrix p i) (e : ℂ) :
    Uᴴ * (F' - e • (1 : PairMatrix p i)) * U =
      Uᴴ * F' * U - e • (1 : Matrix (Fin (2 * p.W - 1)) (Fin (2 * p.W - 1)) ℂ) := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hU]

/-- **The compressed root rectangle for the grid deformations** (the
hypothesis `RootRectangle` of `gue_not_compressWindowGood_le`): with the constants of
`rootRectangle_compress_of_poleCertificate`, for every Hermitian `F'` with `F' - F̂(e)` of rank
one (e.g. `F' = F̂(e) + ρww*` for every real `ρ`), every isometry `U` with `1 - UU* = ww*` and
`s' ∈ [s - s₀, s]`, the compressed grid deformation `U*(F' - e)U` on `Fin (2W - 1)` satisfies
`RootRectangle (U*(F' - e)U) s' 0 r v₀`. -/
theorem compressRootRectangle_family (b κ : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (hκ : 0 < κ) :
    ∃ εc r s₀ v₀ : ℝ, 0 < εc ∧ 0 < r ∧ 0 < s₀ ∧ 0 < v₀ ∧
      ∀ p : Parameters, p.b = b → ∀ (i : ZMod p.n) (om : SplitState p i)
        (_hV : om.2.2.IsHermitian) (ε e : ℝ), e ∈ bulkInterval κ → certErrHat ε p i om e ≤ εc →
        8 / ((p.W : ℝ) * splitS p * Real.sqrt κ) ≤ εc →
        ∀ F' : PairMatrix p i, F'.IsHermitian → ∀ a a' : PairSite p i → ℂ,
          F' - truncF ε om.1 om.2.1 om.2.2 e = vecMulVec a a' →
        ∀ (U : Matrix (PairSite p i) (Fin (2 * p.W - 1)) ℂ) (w : PairSite p i → ℂ),
          Uᴴ * U = 1 → 1 - U * Uᴴ = vecMulVec w (star w) →
        ∀ s' : ℝ, splitS p - s₀ ≤ s' → s' ≤ splitS p →
          RootRectangle (Uᴴ * (F' - (e : ℂ) • (1 : PairMatrix p i)) * U) s' 0 r v₀ := by
  obtain ⟨εc, r, s₀, v₀, hεc, hr, hs₀, hv₀, h⟩ :=
    rootRectangle_compress_of_poleCertificate b κ hb hb' hκ
  refine ⟨εc, r, s₀, v₀, hεc, hr, hs₀, hv₀, fun p hpb i om hV ε e he hcert hW F' hF' a a' hD
    U w hU hPw s' hs1 hs2 => ?_⟩
  intro x hx η hη hη1
  have hx' : |(x + e) - e| ≤ r := by rw [add_sub_cancel_right]; simpa using hx
  obtain ⟨m, hm, hlo, -⟩ := h p hpb i om hV ε e he hcert hW F' hF' a a' hD U w hU hPw s' hs1 hs2
    (x + e) hx' η hη hη1
  refine ⟨m, ?_, hlo⟩
  rw [compress_sub_smul_one U hU, isDysonRoot_sub_smul]
  have e1 : (x : ℂ) + (η : ℂ) * Complex.I + (e : ℂ) = ((x + e : ℝ) : ℂ) + (η : ℂ) * Complex.I := by
    push_cast; ring
  rw [e1]
  exact hm

end BlockBand.LocalWindow.ProofPartTwo
