module

public import BlockBand.DeterminantScore.SelectedResolventDyson

/-!
# Selected-energy regularity and centre from the one-trace certificate (deterministic)

* `selected_regular`: fixed `b, κ` first; then `ε₁, δ, L > 0`; for every admissible `p`
  (`p.b = b`), pair, Hermitian deformation `K` and `E ∈ bulkInterval κ` with
  `‖χ‖ ≤ ε₁`, `χ = ⟨(K - s ā)⁻¹⟩ - ā` (`s = splitS p`): the shift `λ + s m(λ)` lies in
  `{Im ≥ 1/L, |·| ≤ L}` for `|λ| ≤ δ`; the centre `g = windowCenter K K s` is `L`-Lipschitz on
  `[-δ, δ]`; `‖m(iη) - m(0)‖ ≤ L η` for `0 ≤ η ≤ δ`; `|g(0) + sE| ≤ L ‖χ‖` and
  `‖m(0) - ā‖ ≤ L ‖χ‖` (`m = pairDyson K s`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.SelectedResolvent

open Matrix Set BlockBand.Palm
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Model.Construction BlockBand.LocalWindow
open scoped ComplexConjugate

/-- `V ≤ Im ā(E)` and `‖ā(E)‖ ≤ 1` on the bulk interval, `V = √κ/2`. -/
theorem conj_matchedA_bounds {κ E : ℝ} (hκ : 0 < κ) (hE : E ∈ bulkInterval κ) :
    Real.sqrt κ / 2 ≤ (conj (matchedA E)).im ∧ ‖conj (matchedA E)‖ ≤ 1 := by
  have him := ProofCertificate.sqrt_le_abs_matchedA_im hκ hE
  have himle : (matchedA E).im ≤ 0 := by
    rw [ProofCertificate.matchedA_im]; have := Real.sqrt_nonneg (4 - E ^ 2); linarith
  rw [abs_of_nonpos himle] at him
  have he2 : E ^ 2 ≤ 4 := by obtain ⟨h1, h2⟩ := hE; nlinarith
  refine ⟨by rw [Complex.conj_im]; exact him, ?_⟩
  rw [Complex.norm_conj, ProofCertificate.norm_matchedA he2]

/-- `Re ā(E) = -E/2`. -/
theorem conj_matchedA_re (E : ℝ) : (conj (matchedA E)).re = -E / 2 := by
  rw [Complex.conj_re]; rfl

/-- **The regularity and centre items of `SelectedResolventStatement` from the certificate**. Fixed `0 < b < 1/2`, `κ > 0` first; then
`ε₁, δ, L > 0`; uniformly in `p` with `p.b = b`, pairs, Hermitian `K` and `E ∈ bulkInterval κ`
with `‖χ(K, s, 0, ā(E))‖ ≤ ε₁`, `s = splitS p`, `m = pairDyson K s`, `g = windowCenter K K s`:
the shift bounds, `L`-Lipschitz `g` on `[-δ, δ]`, `‖m(iη) - m(0)‖ ≤ Lη` for `0 ≤ η ≤ δ`,
`|g(0) + sE| ≤ L‖χ‖`, `‖m(0) - ā(E)‖ ≤ L‖χ‖`. -/
theorem selected_regular (b κ : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (hκ : 0 < κ) :
    ∃ ε₁ δ L : ℝ, 0 < ε₁ ∧ 0 < δ ∧ 0 < L ∧
      ∀ (p : Parameters), p.b = b → ∀ (i : ZMod p.n) (K : PairMatrix p i), K.IsHermitian →
        ∀ E : ℝ, E ∈ bulkInterval κ →
          ‖certificateChi K (splitS p) 0 (conj (matchedA E))‖ ≤ ε₁ →
          (∀ lam : ℝ, |lam| ≤ δ →
            L⁻¹ ≤ ((lam : ℂ) + (splitS p : ℂ) * pairDyson p i K (splitS p) lam).im ∧
              ‖(lam : ℂ) + (splitS p : ℂ) * pairDyson p i K (splitS p) lam‖ ≤ L) ∧
          (∀ x ∈ Icc (-δ) δ, ∀ y ∈ Icc (-δ) δ,
            |windowCenter p i K K (splitS p) x - windowCenter p i K K (splitS p) y| ≤
              L * |x - y|) ∧
          (∀ η : ℝ, 0 ≤ η → η ≤ δ →
            ‖pairDyson p i K (splitS p) ((η : ℂ) * Complex.I) - pairDyson p i K (splitS p) 0‖ ≤
              L * η) ∧
          |windowCenter p i K K (splitS p) 0 + splitS p * E| ≤
            L * ‖certificateChi K (splitS p) 0 (conj (matchedA E))‖ ∧
          ‖pairDyson p i K (splitS p) 0 - conj (matchedA E)‖ ≤
            L * ‖certificateChi K (splitS p) 0 (conj (matchedA E))‖ := by
  set c := min (1 - 2 * b) b with hcdef
  have hc : 0 < c := lt_min (by linarith) hb
  have hc1 : c < 1 := (min_le_right _ _).trans_lt (by linarith)
  set V := Real.sqrt κ / 2 with hVdef
  have hV : 0 < V := by have := Real.sqrt_pos.mpr hκ; positivity
  obtain ⟨ε₁, δ, L, hε₁, hδ, hL, hreg⟩ := pair_regular hc hc1 hV
  set L' := max (max (1 + 2 * c * L + L) (4 / (3 * c * V))) (δ + 2 * c) with hL'def
  have hL'1 : 1 + 2 * c * L + L ≤ L' := (le_max_left _ _).trans (le_max_left _ _)
  have hL'2 : 4 / (3 * c * V) ≤ L' := (le_max_right _ _).trans (le_max_left _ _)
  have hL'3 : δ + 2 * c ≤ L' := le_max_right _ _
  have hcL : 0 ≤ 2 * c * L := by positivity
  have hL'pos : 0 < L' := lt_of_lt_of_le (by positivity) hL'1
  have hLL' : L ≤ L' := by linarith
  refine ⟨ε₁, δ, L', hε₁, hδ, hL'pos, fun p hpb i K hK E hE hchi => ?_⟩
  have hsp : splitS p = c := ProofCertificate.splitS_eq hpb
  rw [hsp] at hchi ⊢
  obtain ⟨hVμ, hμ1⟩ := conj_matchedA_bounds hκ hE
  obtain ⟨hpt, hlip, hm0⟩ := hreg p i K hK (conj (matchedA E)) hVμ hμ1 hchi
  have hreal : ∀ lam : ℝ, |lam| ≤ δ → ‖(lam : ℂ)‖ ≤ δ ∧ 0 ≤ (lam : ℂ).im := fun lam h =>
    ⟨by rw [Complex.norm_real, Real.norm_eq_abs]; exact h, by simp⟩
  have hcenter : ∀ lam : ℝ, |lam| ≤ δ →
      windowCenter p i K K c lam = lam + 2 * c * (pairDyson p i K c lam).re := by
    intro lam hlam
    obtain ⟨hn, him⟩ := hreal lam hlam
    obtain ⟨hIm, -, heq⟩ := hpt lam him hn
    exact windowCenter_eq hK hc (lt_of_lt_of_le (by positivity) hIm) heq
  have hre_le : ∀ u v : ℂ, |u.re - v.re| ≤ ‖u - v‖ := fun u v => by
    rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
  refine ⟨fun lam hlam => ?_, fun x hx y hy => ?_, fun η hη hηδ => ?_, ?_, ?_⟩
  · obtain ⟨hn, him⟩ := hreal lam hlam
    obtain ⟨hIm, hnorm, -⟩ := hpt lam him hn
    constructor
    · have him' : ((lam : ℂ) + (c : ℂ) * pairDyson p i K c lam).im =
          c * (pairDyson p i K c lam).im := by simp [Complex.mul_im]
      rw [him']
      have h1 : L'⁻¹ ≤ 3 * c * V / 4 := by
        rw [inv_le_comm₀ hL'pos (by positivity)]
        calc (3 * c * V / 4)⁻¹ = 4 / (3 * c * V) := by field_simp
          _ ≤ L' := hL'2
      nlinarith
    · calc ‖(lam : ℂ) + (c : ℂ) * pairDyson p i K c lam‖
          ≤ ‖(lam : ℂ)‖ + ‖(c : ℂ) * pairDyson p i K c lam‖ := norm_add_le _ _
        _ ≤ δ + c * 2 := by
            simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
            gcongr
        _ ≤ L' := by linarith
  · have hxa : |x| ≤ δ := abs_le.mpr ⟨hx.1, hx.2⟩
    have hya : |y| ≤ δ := abs_le.mpr ⟨hy.1, hy.2⟩
    rw [hcenter x hxa, hcenter y hya]
    obtain ⟨hxn, hxi⟩ := hreal x hxa
    obtain ⟨hyn, hyi⟩ := hreal y hya
    have hm := hlip x y hxi hyi hxn hyn
    have hxy : ‖(x : ℂ) - (y : ℂ)‖ = |x - y| := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [hxy] at hm
    have h1 := hre_le (pairDyson p i K c x) (pairDyson p i K c y)
    calc |x + 2 * c * (pairDyson p i K c x).re - (y + 2 * c * (pairDyson p i K c y).re)|
        = |(x - y) + 2 * c * ((pairDyson p i K c x).re - (pairDyson p i K c y).re)| := by
          ring_nf
      _ ≤ |x - y| + 2 * c * |(pairDyson p i K c x).re - (pairDyson p i K c y).re| := by
          refine (abs_add_le _ _).trans (le_of_eq ?_)
          rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * c)]
      _ ≤ |x - y| + 2 * c * (L * |x - y|) := by gcongr; exact h1.trans hm
      _ = (1 + 2 * c * L) * |x - y| := by ring
      _ ≤ L' * |x - y| := by gcongr; linarith
  · have hz1 : 0 ≤ ((η : ℂ) * Complex.I).im := by simp [hη]
    have hz1n : ‖(η : ℂ) * Complex.I‖ ≤ δ := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hη]
      exact hηδ
    have h := hlip ((η : ℂ) * Complex.I) 0 hz1 (by simp) hz1n (by simp; exact hδ.le)
    rw [sub_zero, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hη] at h
    exact h.trans (by gcongr)
  · have h0 := hcenter 0 (by simp; exact hδ.le)
    simp only [Complex.ofReal_zero] at h0
    rw [h0]
    have hre := hre_le (pairDyson p i K c 0) (conj (matchedA E))
    rw [conj_matchedA_re] at hre
    calc |(0 : ℝ) + 2 * c * (pairDyson p i K c 0).re + c * E|
        = 2 * c * |(pairDyson p i K c 0).re - -E / 2| := by
          rw [show (0 : ℝ) + 2 * c * (pairDyson p i K c 0).re + c * E =
              2 * c * ((pairDyson p i K c 0).re - -E / 2) by ring, abs_mul,
            abs_of_pos (by positivity : (0 : ℝ) < 2 * c)]
      _ ≤ 2 * c * (L * ‖certificateChi K c 0 (conj (matchedA E))‖) := by
          gcongr; exact hre.trans hm0
      _ = (2 * c * L) * ‖certificateChi K c 0 (conj (matchedA E))‖ := by ring
      _ ≤ L' * ‖certificateChi K c 0 (conj (matchedA E))‖ := by
          gcongr; linarith
  · exact hm0.trans (by gcongr)

end BlockBand.DeterminantScore.SelectedResolvent
