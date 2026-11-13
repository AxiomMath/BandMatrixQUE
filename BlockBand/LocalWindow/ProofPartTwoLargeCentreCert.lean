module

public import BlockBand.LocalWindow.ProofPartTwoLargeCentre
public import BlockBand.DeterminantScore.SelectedResolventTransfer
public import BlockBand.LocalWindow.ProofNormEvent

/-!
# The truncated certificate off the energy grid

The exterior event of part (ii) (`ExteriorGood`, `partTwoExterior_le`) controls the truncated
certificate `certErrHat ε₀ ω e` only at the grid energies `e ∈ Es`. The certificate is
Lipschitz in the energy with a polynomial constant, so it is controlled at every bulk energy
within `W^{-big}` of the grid.

## Main results

* `opNorm_truncF_sub_le`: `‖F̂(E) - F̂(e)‖ ≤ ‖C‖²|E - e|/ε²` (operator-norm form of
  `norm_truncF_sub_le`).
* `opNorm_resolvent_sub_le_two`: `‖(K₁ - z₁)⁻¹ - (K₂ - z₂)⁻¹‖ ≤ c⁻²(‖K₁ - K₂‖ + |z₁ - z₂|)` for
  Hermitian `K_j` and `|Im z_j| ≥ c > 0`.
* **`certErrHat_le_add`**: on `bulkInterval κ`, `certErrHat ε ω E ≤ certErrHat ε ω e +
  certLip ε κ s ‖C‖ |E - e|`, `certLip = 2(2/(s√κ))²(‖C‖²/ε² + 1 + s(1/2 + 2/√κ)) + 1/2 + 2/√κ`
  (`s = splitS p`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofPartTwo

open Matrix Set
open BlockBand.Coarea BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.Layers
open BlockBand.LocalWindow.ProofETH BlockBand.LocalWindow.ProofCount
open BlockBand.LocalWindow.ProofCertificate
open scoped Matrix.Norms.L2Operator

local notation "T" => Matrix.toEuclideanLin (𝕜 := ℂ)

section Generic

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- **`F̂` is `ε⁻²`-Lipschitz in operator norm**: `‖F̂(E) - F̂(e)‖ ≤ ‖C‖² |E - e|/ε²`. -/
theorem opNorm_truncF_sub_le {H_R : Matrix α α ℂ} (hH : H_R.IsHermitian) (C : Matrix α β ℂ)
    (V : Matrix β β ℂ) {ε : ℝ} (hε : 0 < ε) (E e : ℝ) :
    ‖truncF ε H_R C V E - truncF ε H_R C V e‖ ≤ ‖C‖ ^ 2 * (|E - e| / ε ^ 2) := by
  refine opNorm_le_of_toE _ (by positivity) fun x => ?_
  refine norm_truncF_sub_le hH C V hε (norm_nonneg C) (fun v => ?_) (fun w => ?_) E e x
  · exact BlockBand.LocalWindow.ProofNormEvent.toE_le_opNorm C v
  · have := BlockBand.LocalWindow.ProofNormEvent.toE_le_opNorm Cᴴ w
    rwa [Matrix.l2_opNorm_conjTranspose] at this

/-- **Two-sided resolvent difference**: for Hermitian `K₁, K₂` and `|Im z_j| ≥ c > 0`,
`‖(K₁ - z₁)⁻¹ - (K₂ - z₂)⁻¹‖ ≤ c⁻²(‖K₁ - K₂‖ + ‖z₁ - z₂‖)`. -/
theorem opNorm_resolvent_sub_le_two {K₁ K₂ : Matrix β β ℂ} (hK₁ : K₁.IsHermitian)
    (hK₂ : K₂.IsHermitian) {z₁ z₂ : ℂ} {c : ℝ} (hc : 0 < c) (h₁ : c ≤ |z₁.im|)
    (h₂ : c ≤ |z₂.im|) :
    ‖(K₁ - z₁ • (1 : Matrix β β ℂ))⁻¹ - (K₂ - z₂ • (1 : Matrix β β ℂ))⁻¹‖ ≤
      (c⁻¹) ^ 2 * (‖K₁ - K₂‖ + ‖z₁ - z₂‖) := by
  have hz₁ : z₁.im ≠ 0 := fun h => by rw [h, abs_zero] at h₁; linarith
  have hz₂ : z₂.im ≠ 0 := fun h => by rw [h, abs_zero] at h₂; linarith
  rw [ProofETH.inv_sub_inv (det_resolvent_ne_zero hK₁ hz₁) (det_resolvent_ne_zero hK₂ hz₂)]
  have hn₁ : ‖(K₁ - z₁ • (1 : Matrix β β ℂ))⁻¹‖ ≤ c⁻¹ :=
    (opNorm_resolvent_le hK₁ hz₁).trans (inv_anti₀ hc h₁)
  have hn₂ : ‖(K₂ - z₂ • (1 : Matrix β β ℂ))⁻¹‖ ≤ c⁻¹ :=
    (opNorm_resolvent_le hK₂ hz₂).trans (inv_anti₀ hc h₂)
  have hD : ‖K₂ - z₂ • (1 : Matrix β β ℂ) - (K₁ - z₁ • (1 : Matrix β β ℂ))‖ ≤
      ‖K₁ - K₂‖ + ‖z₁ - z₂‖ := by
    rw [show K₂ - z₂ • (1 : Matrix β β ℂ) - (K₁ - z₁ • (1 : Matrix β β ℂ)) =
        -(K₁ - K₂) + (z₁ - z₂) • (1 : Matrix β β ℂ) by rw [sub_smul]; abel]
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg]
    exact add_le_add le_rfl (opNorm_smul_one_le _)
  calc ‖(K₁ - z₁ • (1 : Matrix β β ℂ))⁻¹ *
        (K₂ - z₂ • (1 : Matrix β β ℂ) - (K₁ - z₁ • (1 : Matrix β β ℂ))) *
        (K₂ - z₂ • (1 : Matrix β β ℂ))⁻¹‖
      ≤ ‖(K₁ - z₁ • (1 : Matrix β β ℂ))⁻¹‖ *
          ‖K₂ - z₂ • (1 : Matrix β β ℂ) - (K₁ - z₁ • (1 : Matrix β β ℂ))‖ *
          ‖(K₂ - z₂ • (1 : Matrix β β ℂ))⁻¹‖ := by
        refine (Matrix.l2_opNorm_mul _ _).trans ?_
        exact mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ ≤ c⁻¹ * (‖K₁ - K₂‖ + ‖z₁ - z₂‖) * c⁻¹ := by
        gcongr
    _ = (c⁻¹) ^ 2 * (‖K₁ - K₂‖ + ‖z₁ - z₂‖) := by ring

end Generic

variable {p : Parameters} {i : ZMod p.n}

/-- The Lipschitz constant of the truncated certificate on `bulkInterval κ`. -/
def certLip (ε κ s c : ℝ) : ℝ :=
  2 * (2 / (s * Real.sqrt κ)) ^ 2 * (c ^ 2 / ε ^ 2 + 1 + s * (1 / 2 + 2 / Real.sqrt κ)) +
    (1 / 2 + 2 / Real.sqrt κ)

/-- **The truncated certificate is Lipschitz on the bulk**: for Hermitian
`H_R, V`, `ε > 0`, `κ > 0` and `E, e ∈ bulkInterval κ`,
`certErrHat ε ω E ≤ certErrHat ε ω e + certLip ε κ s ‖C‖ |E - e|` (`s = splitS p`). -/
theorem certErrHat_le_add {om : SplitState p i} (hH : om.1.IsHermitian) (hV : om.2.2.IsHermitian)
    {ε κ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) {E e : ℝ} (hE : E ∈ bulkInterval κ)
    (he : e ∈ bulkInterval κ) :
    certErrHat ε p i om E ≤ certErrHat ε p i om e +
      certLip ε κ (splitS p) ‖om.2.1‖ * |E - e| := by
  have hs : 0 < splitS p := lt_min p.c_pos p.b_pos
  set s := splitS p with hsdef
  have hsk : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  set c := s * Real.sqrt κ / 2 with hcdef
  have hc : 0 < c := by positivity
  set zE : ℂ := (E : ℂ) + (s : ℂ) * matchedA E with hzE
  set ze : ℂ := (e : ℂ) + (s : ℂ) * matchedA e with hze
  have hzim : ∀ x : ℝ, x ∈ bulkInterval κ →
      c ≤ |((x : ℂ) + (s : ℂ) * matchedA x).im| := by
    intro x hx
    have h := sqrt_le_abs_matchedA_im hκ hx
    have e1 : ((x : ℂ) + (s : ℂ) * matchedA x).im = s * (matchedA x).im := by
      simp [Complex.add_im, Complex.mul_im]
    rw [e1, abs_mul, abs_of_pos hs, hcdef]
    nlinarith
  have hXE : truncF ε om.1 om.2.1 om.2.2 E - (E : ℂ) • (1 : PairMatrix p i) -
      ((s : ℂ) * matchedA E) • (1 : PairMatrix p i) =
      truncF ε om.1 om.2.1 om.2.2 E - zE • (1 : PairMatrix p i) := by
    rw [hzE, add_smul]; abel
  have hXe : truncF ε om.1 om.2.1 om.2.2 e - (e : ℂ) • (1 : PairMatrix p i) -
      ((s : ℂ) * matchedA e) • (1 : PairMatrix p i) =
      truncF ε om.1 om.2.1 om.2.2 e - ze • (1 : PairMatrix p i) := by
    rw [hze, add_smul]; abel
  have hTh : ∀ x : ℝ, (truncF ε om.1 om.2.1 om.2.2 x).IsHermitian := fun x =>
    isHermitian_truncF ε om.1 om.2.1 hV x
  have hA := BlockBand.DeterminantScore.SelectedResolvent.norm_matchedA_sub_le hκ hE he
  have hR : ‖(truncF ε om.1 om.2.1 om.2.2 E - zE • (1 : PairMatrix p i))⁻¹ -
      (truncF ε om.1 om.2.1 om.2.2 e - ze • (1 : PairMatrix p i))⁻¹‖ ≤
      (2 / (s * Real.sqrt κ)) ^ 2 * (‖om.2.1‖ ^ 2 / ε ^ 2 + 1 + s * (1 / 2 + 2 / Real.sqrt κ)) *
        |E - e| := by
    refine (opNorm_resolvent_sub_le_two (hTh E) (hTh e) hc (hzim E hE) (hzim e he)).trans ?_
    have hF := opNorm_truncF_sub_le hH om.2.1 om.2.2 hε E e
    have hz : ‖zE - ze‖ ≤ (1 + s * (1 / 2 + 2 / Real.sqrt κ)) * |E - e| := by
      rw [show zE - ze = ((E - e : ℝ) : ℂ) + (s : ℂ) * (matchedA E - matchedA e) by
        rw [hzE, hze]; push_cast; ring]
      refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hs]
      nlinarith [mul_le_mul_of_nonneg_left hA hs.le]
    have hci : c⁻¹ = 2 / (s * Real.sqrt κ) := by rw [hcdef]; field_simp
    rw [hci]
    have hpos : 0 ≤ (2 / (s * Real.sqrt κ)) ^ 2 := sq_nonneg _
    have : ‖truncF ε om.1 om.2.1 om.2.2 E - truncF ε om.1 om.2.1 om.2.2 e‖ + ‖zE - ze‖ ≤
        (‖om.2.1‖ ^ 2 / ε ^ 2 + 1 + s * (1 / 2 + 2 / Real.sqrt κ)) * |E - e| := by
      have e2 : ‖om.2.1‖ ^ 2 * (|E - e| / ε ^ 2) = ‖om.2.1‖ ^ 2 / ε ^ 2 * |E - e| := by ring
      rw [e2] at hF
      nlinarith
    calc (2 / (s * Real.sqrt κ)) ^ 2 *
          (‖truncF ε om.1 om.2.1 om.2.2 E - truncF ε om.1 om.2.1 om.2.2 e‖ + ‖zE - ze‖)
        ≤ (2 / (s * Real.sqrt κ)) ^ 2 *
          ((‖om.2.1‖ ^ 2 / ε ^ 2 + 1 + s * (1 / 2 + 2 / Real.sqrt κ)) * |E - e|) :=
          mul_le_mul_of_nonneg_left this hpos
      _ = _ := by ring
  set L₀ := (2 / (s * Real.sqrt κ)) ^ 2 *
    (‖om.2.1‖ ^ 2 / ε ^ 2 + 1 + s * (1 / 2 + 2 / Real.sqrt κ)) with hL₀
  have hL₀0 : 0 ≤ L₀ * |E - e| := (norm_nonneg _).trans hR
  have hblk : ∀ k : ZMod p.n,
      ‖pairBlockTrace p i (truncF ε om.1 om.2.1 om.2.2 E - zE • (1 : PairMatrix p i))⁻¹ k -
          matchedA E‖ ≤
        ‖pairBlockTrace p i (truncF ε om.1 om.2.1 om.2.2 e - ze • (1 : PairMatrix p i))⁻¹ k -
          matchedA e‖ + certLip ε κ s ‖om.2.1‖ * |E - e| := by
    intro k
    have hb := BlockBand.DeterminantScore.SelectedResolvent.norm_pairBlockTrace_le
      (M := (truncF ε om.1 om.2.1 om.2.2 E - zE • (1 : PairMatrix p i))⁻¹ -
        (truncF ε om.1 om.2.1 om.2.2 e - ze • (1 : PairMatrix p i))⁻¹) hL₀0
      (fun v => (BlockBand.LocalWindow.ProofNormEvent.toE_le_opNorm _ v).trans
        (mul_le_mul_of_nonneg_right hR (norm_nonneg _))) k
    rw [← BlockBand.DeterminantScore.SelectedResolvent.pairBlockTrace_sub] at hb
    have t := norm_sub_le_norm_sub_add_norm_sub
      (pairBlockTrace p i (truncF ε om.1 om.2.1 om.2.2 E - zE • (1 : PairMatrix p i))⁻¹ k)
      (pairBlockTrace p i (truncF ε om.1 om.2.1 om.2.2 e - ze • (1 : PairMatrix p i))⁻¹ k)
      (matchedA E)
    have t2 := norm_sub_le_norm_sub_add_norm_sub
      (pairBlockTrace p i (truncF ε om.1 om.2.1 om.2.2 e - ze • (1 : PairMatrix p i))⁻¹ k)
      (matchedA e) (matchedA E)
    rw [norm_sub_rev (matchedA e) (matchedA E)] at t2
    have hcl : certLip ε κ s ‖om.2.1‖ * |E - e| =
        2 * (L₀ * |E - e|) + (1 / 2 + 2 / Real.sqrt κ) * |E - e| := by
      rw [hL₀]; unfold certLip; ring
    rw [hcl]
    linarith
  unfold certErrHat
  rw [← hsdef, hXE, hXe]
  refine max_le ?_ ?_
  · exact (hblk i).trans (add_le_add_left (le_max_left _ _) _) |>.trans_eq (by ring)
  · exact (hblk (i + 1)).trans (add_le_add_left (le_max_right _ _) _) |>.trans_eq (by ring)

end BlockBand.LocalWindow.ProofPartTwo
