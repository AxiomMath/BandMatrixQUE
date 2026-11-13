module

public import BlockBand.LocalWindow.ProofETHPair
public import BlockBand.LocalWindow.ProofETHRegular

/-!
# The ETH centre and the window centre `j_B`

Comparison of the centre of the external ETH theorem with the window centre `j_B`, and the size
of the typical spacing on a root rectangle, for part (ii) of the physical local-window lemma.

## Main results

* `windowCenter_eq_re`: `windowCenter = Re (d⁻¹ Tr (B Γ))`.
* `ethCentre_close`: the ETH centre at `z` is close to the window centre at a real `x₀`.
* `spacing_le_of_rootRectangle`: on a root rectangle (`Im m ≥ v₀` up to height `1`), every value
  `η_f(x) ≤ 1` of a typical spacing satisfies `η_f(x) ≤ π/(N v₀)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofETH

open MeasureTheory Matrix Set
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.External BlockBand.LocalWindow.LawBridge
open scoped ENNReal NNReal Matrix.Norms.L2Operator

section Reindex

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem trace_reindex_ETH (e : ι ≃ κ) (A : Matrix ι ι ℂ) : (reindex e e A).trace = A.trace := by
  unfold trace
  simp only [reindex_apply, submatrix_apply, diag_apply]
  exact e.symm.sum_comp (fun a => A a a)

theorem reindex_mul_ETH (e : ι ≃ κ) (A B : Matrix ι ι ℂ) :
    reindex e e (A * B) = reindex e e A * reindex e e B := by
  simp only [reindex_apply]
  exact (submatrix_mul_equiv A B _ e.symm _).symm

theorem reindex_resolvent (e : ι ≃ κ) (A : Matrix ι ι ℂ) (w : ℂ) :
    (reindex e e A - w • (1 : Matrix κ κ ℂ))⁻¹ = reindex e e (A - w • (1 : Matrix ι ι ℂ))⁻¹ := by
  have h : reindex e e A - w • (1 : Matrix κ κ ℂ) = reindex e e (A - w • 1) := by
    ext a b
    simp [reindex_apply, Matrix.sub_apply, Matrix.one_apply, e.symm.injective.eq_iff]
  rw [h, inv_reindex]

end Reindex

variable {p : Parameters} {i : ZMod p.n}

/-- `windowCenter` is the real part of the complex window centre `d⁻¹ Tr(B Γ)`. -/
theorem windowCenter_eq_re (B K : PairMatrix p i) (s lam : ℝ) :
    BlockBand.LocalWindow.windowCenter p i B K s lam =
      ((((2 * (p.W : ℝ))⁻¹ : ℝ) : ℂ) * (B * BlockBand.LocalWindow.windowGamma p i K s lam).trace).re := by
  unfold BlockBand.LocalWindow.windowCenter
  rw [Complex.re_ofReal_mul]

theorem inflatedSpectralPoint_im {s : ℝ} {F : CEH.SourceHermitian (2 * p.W)}
    {M : CEH.MDEBranch (Real.sqrt s) F} (spacing : CEH.TypicalSpacing M) (ξ x : ℝ) :
    (CEH.inflatedSpectralPoint spacing ξ x).im = ((2 * p.W : ℕ) : ℝ) ^ ξ * spacing.eta x := by
  unfold CEH.inflatedSpectralPoint
  simp

theorem inflatedSpectralPoint_im_pos {s : ℝ} {F : CEH.SourceHermitian (2 * p.W)}
    {M : CEH.MDEBranch (Real.sqrt s) F} (spacing : CEH.TypicalSpacing M) (ξ x : ℝ) :
    0 < (CEH.inflatedSpectralPoint spacing ξ x).im := by
  rw [inflatedSpectralPoint_im]
  have hN : (0 : ℝ) < ((2 * p.W : ℕ) : ℝ) := by
    have := p.W_pos; exact_mod_cast Nat.mul_pos two_pos this
  exact mul_pos (Real.rpow_pos_of_pos hN _) (spacing.positive x)

/-- **ETH centre versus window centre** (the centre of the external ETH theorem and
`j_B`). Under `MDEBranchIdentification`, for `s > 0`, a Hermitian pair deformation `K`,
any branch `M` of `K` (reindexed) at `λ = √s`, a typical spacing, a pair contraction `J`
(`‖J‖ ≤ 1`), a Dyson root `m` of `K` at `z = x + i N^ξ η_f(x)` and a root `m₀` of `K` at the real
`x₀`: `|⟨Γ(z) J⟩ - d⁻¹ Tr(J Γ_K(x₀))| ≤ Im z/(s Im m) + 2|w - w₀|/(s Im m₀)`, `w = z + s m`,
`w₀ = x₀ + s m₀`. -/
theorem ethCentre_close (hMDE : MDEBranchIdentification) {s : ℝ} (hs : 0 < s)
    {K : PairMatrix p i} (hK : K.IsHermitian)
    (M : CEH.MDEBranch (Real.sqrt s) (toSourceHermitian K hK)) (spacing : CEH.TypicalSpacing M)
    (ξ : ℝ) {J : PairMatrix p i} (hJ : ‖J‖ ≤ 1) {x x₀ : ℝ} {m m₀ : ℂ}
    (hroot : IsDysonRoot K s (CEH.inflatedSpectralPoint spacing ξ x) m)
    (hroot₀ : IsDysonRoot K s (x₀ : ℂ) m₀) :
    ‖ethCentre M spacing ξ J x -
        ((((2 * (p.W : ℝ))⁻¹ : ℝ) : ℂ) * (J * BlockBand.LocalWindow.windowGamma p i K s x₀).trace)‖ ≤
      (CEH.inflatedSpectralPoint spacing ξ x).im / (s * m.im) +
        2 * ‖(CEH.inflatedSpectralPoint spacing ξ x + (s : ℂ) * m) - ((x₀ : ℂ) + (s : ℂ) * m₀)‖ /
          (s * m₀.im) := by
  set e := pairEquiv p i
  set z := CEH.inflatedSpectralPoint spacing ξ x with hzdef
  have hNpos : 0 < 2 * p.W := Nat.mul_pos two_pos p.W_pos
  have hz : 0 < z.im := inflatedSpectralPoint_im_pos spacing ξ x
  have : Nonempty (PairSite p i) := ⟨⟨(i, ⟨0, p.W_pos⟩), Or.inl rfl⟩⟩
  -- the branch at `z`
  have hrootF : IsDysonRoot (toSourceHermitian K hK).1 s z m := (isDysonRoot_reindex e K s z m).mpr hroot
  obtain ⟨hm, heq⟩ := (isDysonRoot_iff _ s z m).mp hrootF
  obtain ⟨hMz, htr⟩ := BlockBand.LocalWindow.ProofCertificate.branch_eq_of_root hMDE hNpos hs
    (toSourceHermitian K hK) M hz hm heq
  set w := z + (s : ℂ) * m with hw
  have hwim : 0 < w.im := dysonRoot_w_im_pos hs hz.le hm
  have htr' : CEH.normalizedTrace ((toSourceHermitian K hK).1 - w • (1 : Matrix (Fin (2 * p.W)) (Fin (2 * p.W)) ℂ))⁻¹ =
      m := by rw [← hMz]; exact htr
  have hΓ := gammaMatrix_eq (toSourceHermitian K hK).2 hwim.ne' htr'
  -- the ETH centre as a pair trace
  set R := (K - w • (1 : PairMatrix p i))⁻¹
  have hR : ((toSourceHermitian K hK).1 - w • (1 : Matrix (Fin (2 * p.W)) (Fin (2 * p.W)) ℂ))⁻¹ = reindex e e R :=
    reindex_resolvent e K w
  have hcentre : ethCentre M spacing ξ J x =
      (((2 * (p.W : ℝ))⁻¹ : ℝ) : ℂ) * (((w.im / m.im : ℝ) : ℂ) * (R * Rᴴ * J).trace) := by
    unfold ethCentre
    rw [hMz, hΓ, hR, conjTranspose_reindex, ← reindex_mul_ETH, smul_mul_assoc, ← reindex_mul_ETH]
    unfold CEH.normalizedTrace
    rw [trace_smul, trace_reindex_ETH, smul_eq_mul]
    push_cast; ring
  -- the window centre
  have hpd : BlockBand.LocalWindow.pairDyson p i K s x₀ = m₀ :=
    pairDyson_eq_of_isDysonRoot p i hK hs (by simp) hroot₀
  set R₀ := (K - ((x₀ : ℂ) + (s : ℂ) * m₀) • (1 : PairMatrix p i))⁻¹
  have hwin : (J * BlockBand.LocalWindow.windowGamma p i K s x₀).trace =
      (s : ℂ) * (R₀ * R₀ᴴ * J).trace := by
    rw [windowGamma_eq, hpd, mul_smul_comm, trace_smul, smul_eq_mul, trace_mul_comm]
  -- `centre_close` on the pair
  have hJ' : ∀ v : PairSite p i → ℂ, sqNorm (Jᴴ *ᵥ v) ≤ 1 ^ 2 * sqNorm v := fun v =>
    sqNorm_mulVec_le_of_opNorm_le (by rw [Matrix.l2_opNorm_conjTranspose]; exact hJ) v
  have hcc := centre_close hK hs (x₀ := x₀) hz.le hroot hroot₀ hJ'
  rw [BlockBand.Angular.FiberAngular.card_pairSite] at hcc
  rw [hcentre, hwin, ← mul_sub, norm_mul]
  have hW2 : (0 : ℝ) < 2 * (p.W : ℝ) := by have := p.W_pos; positivity
  have hnorm : ‖((((2 * (p.W : ℝ))⁻¹ : ℝ) : ℂ))‖ = (2 * (p.W : ℝ))⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hW2)]
  rw [hnorm]
  have hcast : ((2 * p.W : ℕ) : ℝ) = 2 * (p.W : ℝ) := by push_cast; ring
  rw [hcast] at hcc
  calc (2 * (p.W : ℝ))⁻¹ * ‖((w.im / m.im : ℝ) : ℂ) * (R * Rᴴ * J).trace -
        (s : ℂ) * (R₀ * R₀ᴴ * J).trace‖
      ≤ (2 * (p.W : ℝ))⁻¹ * (2 * (p.W : ℝ) * (z.im / (s * m.im) +
          2 * ‖w - ((x₀ : ℂ) + (s : ℂ) * m₀)‖ / (s * m₀.im))) :=
        mul_le_mul_of_nonneg_left hcc (inv_nonneg.mpr hW2.le)
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hW2.ne', one_mul]

/-- **Size of the typical spacing on a root rectangle** (the external ETH theorem,
`N η_f ρ(x + iη_f) = 1`, `ρ = |Im ⟨M⟩|/π`). Under `MDEBranchIdentification`, if every point
`x + iη`, `|x - E₀| ≤ r`, `0 < η ≤ 1`, carries a Dyson root of `K` with `Im m ≥ v₀ > 0`, then
`η_f(x) ≤ 1` forces `η_f(x) ≤ π/(N v₀)`, `N = 2W`. -/
theorem spacing_le_of_rootRectangle (hMDE : MDEBranchIdentification) {s : ℝ} (hs : 0 < s)
    {K : PairMatrix p i} (hK : K.IsHermitian)
    (M : CEH.MDEBranch (Real.sqrt s) (toSourceHermitian K hK)) (spacing : CEH.TypicalSpacing M)
    {E₀ r v₀ : ℝ} (hv₀ : 0 < v₀)
    (hrect : ∀ x : ℝ, |x - E₀| ≤ r → ∀ η : ℝ, 0 < η → η ≤ 1 →
      ∃ m : ℂ, IsDysonRoot K s ((x : ℂ) + (η : ℂ) * Complex.I) m ∧ v₀ ≤ m.im)
    {x : ℝ} (hx : |x - E₀| ≤ r) (hη1 : spacing.eta x ≤ 1) :
    spacing.eta x ≤ Real.pi / (((2 * p.W : ℕ) : ℝ) * v₀) := by
  have hNpos : 0 < 2 * p.W := Nat.mul_pos two_pos p.W_pos
  have hNr : (0 : ℝ) < ((2 * p.W : ℕ) : ℝ) := by exact_mod_cast hNpos
  set η := spacing.eta x
  have hη : 0 < η := spacing.positive x
  obtain ⟨m, hroot, hv⟩ := hrect x hx η hη hη1
  set z : ℂ := (x : ℂ) + (η : ℂ) * Complex.I
  have hz : 0 < z.im := by simp [z, hη]
  have hrootF : IsDysonRoot (toSourceHermitian K hK).1 s z m :=
    (isDysonRoot_reindex (pairEquiv p i) K s z m).mpr hroot
  obtain ⟨hm, heq⟩ := (isDysonRoot_iff _ s z m).mp hrootF
  obtain ⟨-, htr⟩ := BlockBand.LocalWindow.ProofCertificate.branch_eq_of_root hMDE hNpos hs
    (toSourceHermitian K hK) M hz hm heq
  have hspec := spacing.equation x
  unfold CEH.sourceDensity at hspec
  rw [htr, abs_of_pos hm] at hspec
  -- `1 = N η Im m/π ≥ N η v₀/π`
  have hpi := Real.pi_pos
  have h1 : (((2 * p.W : ℕ) : ℝ) * η) * v₀ ≤ Real.pi := by
    have : ((2 * p.W : ℕ) : ℝ) * η * (m.im / Real.pi) = 1 := hspec
    have h2 : ((2 * p.W : ℕ) : ℝ) * η * m.im = Real.pi := by
      field_simp at this; linarith
    have h3 : 0 ≤ ((2 * p.W : ℕ) : ℝ) * η := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hv h3]
  rw [le_div_iff₀ (mul_pos hNr hv₀)]
  nlinarith

end BlockBand.LocalWindow.ProofETH
