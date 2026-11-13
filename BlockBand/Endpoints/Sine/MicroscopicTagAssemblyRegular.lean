module

public import BlockBand.Endpoints.Sine.MicroscopicTagAssemblyGauss
public import BlockBand.Endpoints.Poisson.SequentialCollarsCertificateAlgebra

/-!
# The microscopic tag comparison on one regular exterior

`mts_palm_gauss_regular`: on one regular exterior, the Palm tag test is close to the Gaussian tag
test of covariance `Γ₀`. The proof passes from the Palm law to the Gaussian field of covariance
`Γ` (through `UniformClockTagsPalmContract`) and from `Γ` to `Γ₀`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Clocks BlockBand.Internal.Contracts.ClocksCommonPort
open BlockBand.Internal.Contracts.ClocksLeadProfile
open scoped ENNReal NNReal ComplexOrder ComplexConjugate BoundedContinuousFunction

theorem mts_isUnit_det_sub {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Matrix ι ι ℂ}
    (hF : F.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) : IsUnit (F - z • 1).det := by
  rcases lt_or_gt_of_ne hz with h | h
  · have h' : 0 < (conj z).im := by simp; linarith
    have hu := isUnit_det_sub_hermitian hF h'
    have : (F - z • 1) = -((conj z • 1 - F)ᴴ) := by
      rw [conjTranspose_sub, conjTranspose_smul, hF.eq, conjTranspose_one]
      simp
    rw [this, det_neg, det_conjTranspose]
    exact ((isUnit_one.neg).pow _).mul hu.star
  · have hu := isUnit_det_sub_hermitian hF h
    have : (F - z • 1) = -(z • 1 - F) := by abel
    rw [this, det_neg]
    exact ((isUnit_one.neg).pow _).mul hu

theorem mts_reindex_gram {ι κ : Type*} [Fintype ι] [Fintype κ] (σ : ι ≃ κ)
    (M : Matrix ι ι ℂ) :
    Matrix.reindex σ σ M * (Matrix.reindex σ σ M)ᴴ = Matrix.reindex σ σ (M * Mᴴ) := by
  simp only [Matrix.reindex_apply, conjTranspose_submatrix]
  rw [submatrix_mul_equiv]

/-- Palm law → Gaussian field of covariance `Γ₀` on one regular exterior. -/
theorem mts_palm_gauss_regular (hUCT : UniformClockTagsPalmContract)
    (hCS : ClockCovarianceStabilityContract) {b : ℝ} (hb : 0 < b) (hb' : b < 1 / 2) {κ : ℝ}
    (hκ : 0 < κ) {A r₀ s₀ v₀ : ℝ} (hFC : FreshConstants (1 - 2 * b) r₀ s₀ v₀)
    (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ) {ε K : ℝ} (hε : 0 < ε) (hK : 0 < K) :
    ∃ η : ℝ, 0 < η ∧ ∃ W₀ : ℕ, ∀ (p : Parameters), p.b = b → W₀ ≤ p.W →
    ∀ (k : ZMod p.n) (σ : BlockSite p k ≃ Fin (Fintype.card (BlockSite p k)))
      (ω : BlockState p k), ∀ e ∈ bulkInterval κ, IsBlockRegular p k σ A r₀ s₀ v₀ η e ω →
    ∀ (q : ℕ), 0 < q →
    ∀ Dt : Fin q → Matrix (Fin (Fintype.card (BlockSite p k)))
      (Fin (Fintype.card (BlockSite p k))) ℂ, (∀ j, (Dt j).PosSemidef) →
      ((∑ j, Dt j) - 1).PosSemidef →
      |(q : ℝ)⁻¹ * ∑ j, palmExpect (blockDeformation p k σ ω e) p.c e
            (fun v => Φ (ratioHalfLine ((q : ℂ) • Dt j) (∑ j, Dt j) (fun _ => 0) v)) -
          (q : ℝ)⁻¹ * ∑ j, ∫ g, Φ (ratioHalfLine ((q : ℂ) • Dt j) (∑ j, Dt j) (fun _ => 0)
            (Matrix.reindex σ σ (blockFieldFactor p k ω e) *ᵥ g))
            ∂circularVectorLaw (Fin (Fintype.card (BlockSite p k)))| ≤
        2 * ε + 2 * ‖Φ‖ / K := by
  obtain ⟨N₀, hN₀⟩ := hUCT A (1 - 2 * b) r₀ s₀ v₀ hFC Φ ε hε
  obtain ⟨ω₀, hω₀, hMT⟩ := mts_multiTag_covariance hCS hK Φ hε
  set h0 := Real.sqrt (3 * min κ 1) / 2 with hh0
  have hh0p : 0 < h0 := by
    rw [hh0]; exact div_pos (Real.sqrt_pos.2 (by positivity)) (by norm_num)
  set δ := min (ω₀ / 4) (1 / 4)
  have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
  refine ⟨h0 * δ, mul_pos hh0p hδ, max N₀ 1, ?_⟩
  intro p hpb hW k σ ω e he hreg q hq Dt hDt hD1
  have hc : p.c = 1 - 2 * b := by rw [Parameters.c, hpb]
  have hcard : Fintype.card (BlockSite p k) = p.W := mts_card_blockSite p k
  have hN : N₀ ≤ Fintype.card (BlockSite p k) := by rw [hcard]; exact (le_max_left _ _).trans hW
  have hN0 : 0 < Fintype.card (BlockSite p k) := by rw [hcard]; exact p.W_pos
  obtain ⟨hFcl, hm⟩ := hreg
  have hF : (blockDeformation p k σ ω e).IsHermitian := hFcl.1
  set F := blockDeformation p k σ ω e
  set m := freshDyson F p.c e
  set a := matchedA e
  -- the height
  have hah : h0 ≤ -a.im := by
    rw [mts_matchedA_im, neg_neg, hh0]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply Real.sqrt_le_sqrt
    have hk1 : min κ 1 ≤ 1 := min_le_right _ _
    have hkk : min κ 1 ≤ κ := min_le_left _ _
    have hm0 : 0 ≤ min κ 1 := le_min hκ.le zero_le_one
    have h1 := he.1; have h2 := he.2
    nlinarith
  have ha : a.im < 0 := by linarith
  have hm' : ‖m - conj a‖ ≤ δ * (-a.im) := by
    calc ‖m - conj a‖ ≤ h0 * δ := hm
      _ ≤ δ * (-a.im) := by rw [mul_comm]; exact mul_le_mul_of_nonneg_left hah hδ.le
  have hmim : 0 < m.im := by
    have h1 : |(m - conj a).im| ≤ ‖m - conj a‖ := Complex.abs_im_le_norm _
    have h2 : (m - conj a).im = m.im + a.im := by simp
    rw [h2] at h1
    have h3 := (abs_le.1 (h1.trans hm')).1
    have h4 : δ * (-a.im) ≤ (1 / 4) * (-a.im) :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) (by linarith)
    nlinarith
  -- the Palm → Γ comparison
  have hX : IsUnit (F - ((e : ℂ) + (p.c : ℂ) * m) • 1).det := by
    refine mts_isUnit_det_sub hF ?_
    rw [show ((e : ℂ) + (p.c : ℂ) * m).im = p.c * m.im by simp]
    exact (mul_pos p.c_pos hmim).ne'
  have hTΓ : 0 < traceAgainst (freshGamma F p.c e) (∑ j, Dt j) := by
    unfold freshGamma
    exact mts_traceAgainst_pos hN0 p.c_pos _ _ hX hD1
  have hFcl' : FreshClass F A (1 - 2 * b) e r₀ s₀ v₀ := by rw [← hc]; exact hFcl
  have hstep1 := hN₀ _ hN hN0 F e hFcl' q hq Dt hDt (by rw [← hc]; exact hTΓ)
    (mts_freshFactor F (1 - 2 * b) e) (by rw [← hc]; exact mts_freshFactor_gram F p.c_pos.le e)
    (fun _ => 0) measurable_const
  rw [← hc] at hstep1
  -- the Γ → Γ₀ comparison
  set Γ₀ := Matrix.reindex σ σ (blockMatchedGamma p k ω e)
  set M₀ := Matrix.reindex σ σ (blockFieldFactor p k ω e)
  have hM₀ : M₀ * M₀ᴴ = Γ₀ := by
    simp only [M₀, Γ₀]; rw [mts_reindex_gram, mts_blockFieldFactor_gram]
  have he2 : |e| ≤ 2 := by
    have := he.1; have := he.2; rw [abs_le]; constructor <;> linarith
  have hΓ₀eq : Γ₀ = (p.c : ℂ) • ((F - ((e : ℂ) + (p.c : ℂ) * a) • 1)ᴴ *
      (F - ((e : ℂ) + (p.c : ℂ) * a) • 1))⁻¹ := mts_reindex_blockGamma0 p k σ ω he2
  have hY : IsUnit (F - ((e : ℂ) + (p.c : ℂ) * a) • 1).det := by
    refine mts_isUnit_det_sub hF ?_
    rw [show ((e : ℂ) + (p.c : ℂ) * a).im = p.c * a.im by simp]
    exact (mul_neg_of_pos_of_neg p.c_pos ha).ne
  have hTΓ₀ : 0 < traceAgainst Γ₀ (∑ j, Dt j) := by
    rw [hΓ₀eq]; exact mts_traceAgainst_pos hN0 p.c_pos _ _ hY hD1
  have hΓ₀psd : Γ₀.PosSemidef := by rw [← hM₀]; exact posSemidef_self_mul_conjTranspose M₀
  obtain ⟨hL1, hL2⟩ := mts_relLoewner (e := e) hF p.c_pos ha hδ.le (min_le_left _ _)
    (min_le_right _ _) hm'
  have hstep2 := hMT _ Γ₀ (freshGamma F p.c e) ω₀ hω₀.le le_rfl hΓ₀psd
    (by rw [hΓ₀eq]; exact hL1) (by rw [hΓ₀eq]; exact hL2) q hq Dt hDt hTΓ₀
    (mts_freshFactor F p.c e) M₀ (mts_freshFactor_gram F p.c_pos.le e) hM₀ (fun _ => 0)
    measurable_const
  calc _ ≤ |(q : ℝ)⁻¹ * ∑ j, palmExpect F p.c e
            (fun v => Φ (ratioHalfLine ((q : ℂ) • Dt j) (∑ j, Dt j) (fun _ => 0) v)) -
          (q : ℝ)⁻¹ * ∑ j, ∫ g, Φ (ratioHalfLine ((q : ℂ) • Dt j) (∑ j, Dt j) (fun _ => 0)
            (mts_freshFactor F p.c e *ᵥ g)) ∂circularVectorLaw _| +
        |(q : ℝ)⁻¹ * ∑ j, (∫ g, Φ (ratioHalfLine ((q : ℂ) • Dt j) (∑ j, Dt j) (fun _ => 0)
            (mts_freshFactor F p.c e *ᵥ g)) ∂circularVectorLaw _) -
          (q : ℝ)⁻¹ * ∑ j, ∫ g, Φ (ratioHalfLine ((q : ℂ) • Dt j) (∑ j, Dt j) (fun _ => 0)
            (M₀ *ᵥ g)) ∂circularVectorLaw _| := abs_sub_le _ _ _
    _ ≤ ε + (ε + 2 * ‖Φ‖ / K) := add_le_add hstep1 hstep2
    _ = 2 * ε + 2 * ‖Φ‖ / K := by ring

end BlockBand.Endpoints
