module

public import BlockBand.LocalWindow.ProofPartTwoLargeCentre

/-!
# The deterministic bound at one exact eigenvector, large `ρ`

The deterministic overlap bound of the large-`ρ` branch of part (ii) of the physical local-window
lemma at one exact eigenvector.

## Main results

* **`largeRho_point_le`**: `largeRho_actual_transfer` applied to the embedded compressed
  observable `U J_c U*` (`embed_compress`), with the centre comparison `largeRho_hcen` and the
  observable change `norm_quad_sub_le_compress` (`‖U*JU - J_c‖ ≤ δ_J`, the `w`-component
  `|w*u| ≤ 2K/|ρ|`). The conclusion is the real overlap error of part (ii) at the exact energy
  `E` and eigenvalue `λ`, centred at `windowCenter J K₀(E) s λ`, for a pair contraction `J`
  (class (a): `J_c = U*B₀U`, `δ_J = 0`; class (b): `J_c = f(compRegM e)`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofPartTwo

open Matrix Set
open BlockBand.Coarea BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.External BlockBand.LocalWindow.ProofETH BlockBand.LocalWindow.ProofCount
open scoped Matrix.Norms.L2Operator

variable {p : Parameters} {i : ZMod p.n}

attribute [local instance] pairSite_nonempty

/-- Hypotheses of `largeRho_actual_transfer` (exterior point, simple label `j₀` separated at
`ε` from `E` and `e`, `‖F_reg(E) - E + G‖ ≤ K`, `4K ≤ |ρ(E)|`, unit eigenvector `u` of
`A(E)` with eigenvalue `|λ| ≤ K`, `|λ - μ| ≤ h/2`, compressed count `≤ n_S`) with the compressed
window bound for a compressed contraction `J_c`, `‖J_c - U*JU‖ ≤ δ_J`, and the root rectangles
of `largeRho_hcen` (`|λ| ≤ r`, `|μ| + h ≤ r`).
With `s' = compressVar p s`,
`r_g = (‖C‖²/ε² + 1)|E - e|`, `q = 2K/|ρ|`, `τ = (r_g + 4K²/|ρ|)/(h/2)`, `c̄ = 1/(sv₀²)` and
`η` the bound of `largeRho_hcen`:
`|Re u*Ju - windowCenter J K₀(E) s λ| ≤ n_S · 2N^{ε'}N^{-1/2} + η + 2τ + (1 + c̄)τ² + q(2 + q) +
2qc̄ + δ_J + 4q`.
-/
theorem largeRho_point_le (sel : CEH.EigenpairSelection (2 * p.W))
    (sel' : CEH.EigenpairSelection (2 * p.W - 1)) {ε : ℝ} (hε : 0 < ε) {om : SplitState p i}
    (hH : om.1.IsHermitian) (hV : om.2.2.IsHermitian) {j₀ : ExteriorSite p i}
    (hs : PoleSimple hH j₀) {E e : ℝ} (hsepE : PoleSeparated ε hH j₀ E)
    (hsepe : PoleSeparated ε hH j₀ e) (hdet : (om.1 - (E : ℂ) • 1).det ≠ 0)
    {G : PairMatrix p i} {K : ℝ} (hK : 0 < K)
    (hMG : ‖regF hH j₀ om.2.1 om.2.2 E - (E : ℂ) • 1 + G‖ ≤ K)
    (hρ4 : 4 * K ≤ |poleRho hH j₀ om.2.1 E|) {lam : ℝ} (hlam : |lam| ≤ K)
    {u : PairSite p i → ℂ} (hu : sqNorm u = 1)
    (heig : schurA p i om G E *ᵥ u = (lam : ℂ) • u) {J : PairMatrix p i} (hJ : ‖J‖ ≤ 1)
    {Jc : Matrix (Fin (2 * p.W - 1)) (Fin (2 * p.W - 1)) ℂ} (hJc : ‖Jc‖ ≤ 1) {δJ : ℝ}
    (hδJ : ‖Jc - (poleIsometry sel j₀ om)ᴴ * J * poleIsometry sel j₀ om‖ ≤ δJ)
    {s v₀ r μ β ε' nS : ℝ} (hs0 : 0 < s) (hv₀ : 0 < v₀)
    (hwin : NatWindowGood (compRegF sel ε j₀ e om) sel' (compressVar p s) μ β ε' Jc
      ((poleIsometry sel j₀ om)ᴴ * G * poleIsometry sel j₀ om))
    (hcount : ∀ hX : ((poleIsometry sel j₀ om)ᴴ * G * poleIsometry sel j₀ om).IsHermitian,
      ((Finset.univ.filter fun k => sel'.eigenvalue (natDeformed (compRegF sel ε j₀ e om)
        ((poleIsometry sel j₀ om)ᴴ * G * poleIsometry sel j₀ om) hX) k ∈
          Icc (μ - compressRadius p β) (μ + compressRadius p β)).card : ℝ) ≤ nS)
    (hlamμ : |lam - μ| ≤ compressRadius p β / 2)
    (hRK : PairRootRectangle (schurK0 p i om E) s 0 r v₀)
    (hRc : RootRectangle ((poleIsometry sel j₀ om)ᴴ *
      (regF hH j₀ om.2.1 om.2.2 E - (E : ℂ) • 1) * poleIsometry sel j₀ om) (compressVar p s) 0 r v₀)
    (hRe : RootRectangle (compRegM sel ε j₀ e om) (compressVar p s) 0 r v₀)
    (hlamr : |lam| ≤ r) (hμ : |μ| + compressRadius p β ≤ r)
    (hρ : |lam| + 1 / v₀ < |poleRho hH j₀ om.2.1 E|)
    (hδ₁ : 4 * ((1 + ‖regF hH j₀ om.2.1 om.2.2 E - (E : ℂ) • 1‖ / (compressVar p s * v₀)) ^ 3 /
      (|poleRho hH j₀ om.2.1 E| - (|lam| + 1 / v₀))) ≤ v₀)
    (hδ₂ : 2 * ((1 + ‖regF hH j₀ om.2.1 om.2.2 E - (E : ℂ) • 1‖ / (compressVar p s * v₀)) ^ 3 /
      (|poleRho hH j₀ om.2.1 E| - (|lam| + 1 / v₀))) ≤ compressVar p s * v₀ ^ 3) :
    |(star u ⬝ᵥ (J *ᵥ u)).re - BlockBand.LocalWindow.windowCenter p i J (schurK0 p i om E) s lam| ≤
      nS * compressTol p ε' +
        (2 * resLip (compressVar p s) v₀ / v₀ *
            (3 * compressRadius p β / 2 + (‖om.2.1‖ ^ 2 / ε ^ 2 + 1) * |E - e|) +
          δJ / (compressVar p s * v₀ ^ 2) +
          compressCentreErr p s v₀ ‖regF hH j₀ om.2.1 om.2.2 E - (E : ℂ) • 1‖
            (poleRho hH j₀ om.2.1 E) lam) +
        2 * (((‖om.2.1‖ ^ 2 / ε ^ 2 + 1) * |E - e| + 4 * K ^ 2 / |poleRho hH j₀ om.2.1 E|) /
          (compressRadius p β / 2)) +
        (1 + 1 / (s * v₀ ^ 2)) * (((‖om.2.1‖ ^ 2 / ε ^ 2 + 1) * |E - e| +
          4 * K ^ 2 / |poleRho hH j₀ om.2.1 E|) / (compressRadius p β / 2)) ^ 2 +
        2 * K / |poleRho hH j₀ om.2.1 E| * (2 + 2 * K / |poleRho hH j₀ om.2.1 E|) +
        2 * (2 * K / |poleRho hH j₀ om.2.1 E|) * (1 / (s * v₀ ^ 2)) +
        (δJ + 4 * (2 * K / |poleRho hH j₀ om.2.1 E|)) := by
  set U := poleIsometry sel j₀ om with hUdef
  set w := poleDir hH j₀ om.2.1 with hwdef
  set ρ := poleRho hH j₀ om.2.1 E with hρdef
  obtain ⟨hUU, hUw, hcompl⟩ := poleIsometry_spec sel hH hs
  have hw : sqNorm w = 1 := sqNorm_poleDir hH j₀ om.2.1
  have hρ0 : 0 < |ρ| := by linarith
  -- the embedded compressed observable
  obtain ⟨hJ'1, hUJ'⟩ := embed_compress hUU hJc
  set J' := U * Jc * Uᴴ with hJ'def
  have hwin' : NatWindowGood (compRegF sel ε j₀ e om) sel' (compressVar p s) μ β ε'
      (Uᴴ * J' * U) (Uᴴ * G * U) := by rw [hUJ']; exact hwin
  set c₀ := pairCentre J (schurK0 p i om E) s lam with hc₀
  have hcen := largeRho_hcen sel hε hH hV hs hsepE hsepe hdet hs0 hv₀ hRK hRc hRe hlamr hμ hlamμ
    hρ hδ₁ hδ₂ hJ hJc hδJ
  have hcen' : ∀ lam' ∈ Icc (μ - compressRadius p β) (μ + compressRadius p β),
      ‖nativeCentre (Uᴴ * J' * U) (compRegM sel ε j₀ e om) (compressVar p s) lam' - c₀‖ ≤
        2 * resLip (compressVar p s) v₀ / v₀ *
            (3 * compressRadius p β / 2 + (‖om.2.1‖ ^ 2 / ε ^ 2 + 1) * |E - e|) +
          δJ / (compressVar p s * v₀ ^ 2) +
          compressCentreErr p s v₀ ‖regF hH j₀ om.2.1 om.2.2 E - (E : ℂ) • 1‖ ρ lam := by
    rw [hUJ']; exact hcen
  have hT := largeRho_actual_transfer sel sel' hε hH hV hs hsepE hsepe hdet hK hMG hρ4 hlam hu
    heig hJ'1 hwin' hcount hlamμ hcen'
  -- the observable change
  set M := regF hH j₀ om.2.1 om.2.2 E - (E : ℂ) • 1 + G with hMdef
  have heig' : (M + (ρ : ℂ) • vecMulVec w (star w)) *ᵥ u = (lam : ℂ) • u := by
    have h := heig
    unfold schurA at h
    rw [schurK0_pole_decomp om hH j₀ hdet] at h
    rw [show M + (ρ : ℂ) • vecMulVec w (star w) = regF hH j₀ om.2.1 om.2.2 E - (E : ℂ) • 1 +
        ((poleRho hH j₀ om.2.1 E : ℝ) : ℂ) •
          vecMulVec (poleDir hH j₀ om.2.1) (star (poleDir hH j₀ om.2.1)) + G by
      rw [hMdef]; abel]
    exact h
  have hdec := decomp_of_compl hcompl u
  have hy : vnorm (Uᴴ *ᵥ u) ≤ 1 := by
    refine (vnorm_mulVec_le _ _).trans ?_
    rw [vnorm_of_sqNorm_one hu, mul_one]
    exact opNorm_conjTranspose_le_one_of_isometry hUU
  have hJJ : ‖J - J'‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith)
  have hq := norm_quad_sub_le_compress hUU hJJ hw hu hy hdec
  rw [hUJ'] at hq
  have hx : ‖star w ⬝ᵥ u‖ ≤ 2 * K / |ρ| :=
    largeRho_component_le hMG hw hu (abs_pos.mp hρ0) hlam heig'
  -- the size of the centre
  have hMEh := isHermitian_regK om hH hV j₀ E
  have hww : vecMulVec w (star w) = 1 - U * Uᴴ := eq_sub_of_add_eq' hcompl
  have hKh : (schurK0 p i om E).IsHermitian := by
    rw [schurK0_pole_decomp om hH j₀ hdet, hww]
    exact isHermitian_compressFull hMEh U ρ
  have hc₀n : ‖c₀‖ ≤ 1 / (s * v₀ ^ 2) :=
    norm_pairCentre_le_rect hKh hJ hs0 hv₀ hRK (by rwa [sub_zero])
  set τ := ((‖om.2.1‖ ^ 2 / ε ^ 2 + 1) * |E - e| + 4 * K ^ 2 / |ρ|) / (compressRadius p β / 2)
  set qq := 2 * K / |ρ| with hqq
  have hq0 : 0 ≤ qq := by positivity
  have hb1 : (1 + ‖c₀‖) * τ ^ 2 ≤ (1 + 1 / (s * v₀ ^ 2)) * τ ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  have hb2 : 2 * qq * ‖c₀‖ ≤ 2 * qq * (1 / (s * v₀ ^ 2)) :=
    mul_le_mul_of_nonneg_left hc₀n (by positivity)
  have hre : |(star u ⬝ᵥ (J *ᵥ u)).re -
      BlockBand.LocalWindow.windowCenter p i J (schurK0 p i om E) s lam| ≤
      ‖star u ⬝ᵥ (J *ᵥ u) - c₀‖ := by
    rw [hc₀, ← re_pairCentre, ← Complex.sub_re]
    exact Complex.abs_re_le_norm _
  have hq' : ‖star u ⬝ᵥ (J *ᵥ u) - star u ⬝ᵥ (J' *ᵥ u)‖ ≤ δJ + 4 * qq := by
    refine hq.trans ?_
    rw [norm_sub_rev]
    linarith
  have htri := norm_sub_le_norm_sub_add_norm_sub (star u ⬝ᵥ (J *ᵥ u)) (star u ⬝ᵥ (J' *ᵥ u)) c₀
  refine hre.trans (htri.trans ?_)
  linarith

end BlockBand.LocalWindow.ProofPartTwo
