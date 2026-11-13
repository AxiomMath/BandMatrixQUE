module

public import BlockBand.LocalWindow.ProofPartTwoLargeAssembly
public import BlockBand.QUE.GUEInputs.Fields
public import BlockBand.QUE.GUEInputs.PartTwoLargeRhoSection

/-!
# The large-`ρ` branch of the physical local window, part (ii) (GUE inputs)

`partTwoLargeRho_holds`: the large-`ρ` branch of part (ii) of the physical local window lemma.

The statements are those of `BlockBand.LocalWindow.ProofPartTwoLargeAssembly`, with `NativeInputs`
replaced by the hypotheses `EigenpairsExist` and `SpacingExists` (fields of
`External.CEH.SourceContract`) as needed, and without `GUEWignerFamilyAdapter`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofPartTwo.GUEInputs

open MeasureTheory Matrix Set Filter
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs BlockBand.External BlockBand.LocalWindow.LawBridge
open BlockBand.LocalWindow.ProofETH BlockBand.LocalWindow.ProofCount
open BlockBand.LocalWindow.ProofCertificate
open scoped ENNReal NNReal Matrix.Norms.L2Operator

section

attribute [local instance] pairSite_nonempty

set_option maxHeartbeats 4000000 in
/-- **The large-`ρ` branch of part (ii) of the physical local window lemma.** -/
theorem partTwoLargeRho_holds (hEig : BlockBand.QUE.GUEInputs.EigenpairsExist) (hSp : BlockBand.QUE.GUEInputs.SpacingExists)
    (hMDE : MDEBranchIdentification) (hETH : ExternalETH) (hELG : ExternalLocalGUE)
    (hPBC : PhysicalBlockConditionalCount) (hMT : MatchedTracesContract)
    (hRL : RankLocationContract) (hCo : CoareaContract) (hBridge : PairGUELawBridgeStatement)
    (hComp : CompressedGUELawBridgeStatement) :
    PartTwoLargeRhoStatement := by
  intro b T ϑ hϑ
  by_cases hb : 0 < b ∧ b < 1 / 2
  swap
  · refine ⟨1 / 2, 1, by norm_num, by norm_num,
      fun ε _ D _ K₀ A₀ _ => ⟨0, 0, 0, fun p hpb => ?_⟩⟩
    exact absurd ⟨hpb ▸ p.b_pos, hpb ▸ p.b_lt_half⟩ hb
  obtain ⟨hb0, hb1⟩ := hb
  set ϑ' := min ϑ (1 / 4) with hϑ'
  have hϑ'0 : 0 < ϑ' := lt_min hϑ (by norm_num)
  have hϑ'1 : ϑ' < 1 / 2 := (min_le_right _ _).trans_lt (by norm_num)
  have hϑ'4 : ϑ' ≤ 1 / 4 := min_le_right _ _
  set κ := Real.pi * ϑ' / 4 with hκ
  have hκ0 : 0 < κ := by positivity
  have hκ2 : κ ≤ 2 := by
    have := mul_le_mul Real.pi_lt_four.le hϑ'4 hϑ'0.le (by norm_num)
    rw [hκ]; linarith
  obtain ⟨εc₁, r₁, s₀₁, v₀₁, hεc₁, hr₁, hs₀₁, hv₀₁, hrect⟩ :=
    largeRho_rectangles b κ hb0 hb1 hκ0
  obtain ⟨εc₂, r₂, s₀₂, v₀₂, hεc₂, hr₂, hs₀₂, hv₀₂, hfam⟩ :=
    pairRootRectangle_regF_family b κ hb0 hb1 hκ0
  set εc := min εc₁ εc₂ with hεcdef
  set r := min r₁ r₂ with hrdef
  set s₀ := min s₀₁ s₀₂ with hs₀def
  set v₀ := min v₀₁ v₀₂ with hv₀def
  have hεc : 0 < εc := lt_min hεc₁ hεc₂
  have hr : 0 < r := lt_min hr₁ hr₂
  have hs₀ : 0 < s₀ := lt_min hs₀₁ hs₀₂
  have hv₀ : 0 < v₀ := lt_min hv₀₁ hv₀₂
  set δ := min (r / 4) (1 / 2) with hδ
  have hδ0 : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδr : δ ≤ r / 4 := min_le_left _ _
  have hδ1 : δ ≤ 1 / 2 := min_le_right _ _
  refine ⟨δ, 1, hδ0, hδ1.trans_lt (by norm_num), fun ε hε D hD K₀ A₀ hA₀ => ?_⟩
  have hA₀0 : 0 ≤ A₀ := by linarith
  set s := min (1 - 2 * b) b with hsdef
  have hs : 0 < s := lt_min (by linarith) hb0
  -- the exterior events
  set M := 2 * (A₀ + 1) + 7 with hM
  have hM0 : 0 ≤ M := by positivity
  obtain ⟨CG₁, C₁, -, hC₁, hext₁⟩ := partTwoExterior_le hPBC hMT hRL hCo b T ϑ' κ κ (1 / 2) D M
    A₀ hb0 hb1 hϑ'0 hϑ'1 hκ0 hκ0 (by norm_num) hD.le hA₀
  obtain ⟨CG, C₂, hCG, hC₂, hext₂⟩ := partTwoExterior_le hPBC hMT hRL hCo b T ϑ' κ κ (1 / 2) D M
    (A₀ + 1) hb0 hb1 hϑ'0 hϑ'1 hκ0 hκ0 (by norm_num) hD.le (by linarith)
  obtain ⟨CGG, cG, hCGG, hcG, hgueE⟩ := gue_gueEvent_section_le
  obtain ⟨Cn, hCn, hnb⟩ := ProofNormEvent.normBound_le_rpow T D cG hcG
  -- the scales
  set a := A₀ + 5 with ha
  have ha1 : 1 ≤ a := by linarith
  set κ₀ := |T| + CG + T ^ 2 + 2 with hκ₀
  have hκ₀0 : 0 ≤ κ₀ := by positivity
  set κ₁ := κ₀ + CGG + 1 with hκ₁
  have hκ₁1 : 1 ≤ κ₁ := by linarith
  set Ceth := (Real.sqrt (s / 2))⁻¹ * κ₀ with hCeth
  set Ccnt := (Real.sqrt s)⁻¹ * κ₀ with hCcnt
  -- the compressed ETH and the compressed count
  obtain ⟨β₀, hβ₀, hβ₀2, hethW⟩ := BlockBand.LocalWindow.ProofPartTwo.GUEInputs.gue_largeRhoCompBad_section_le hSp hMDE hETH hComp a
    Ceth (s / 2) s (r / 2) v₀ (half_pos hs) (by linarith) (half_pos hr) hv₀
  set εm := min ε (1 / 2) with hεm
  have hεm0 : 0 < εm := lt_min hε (by norm_num)
  set ε' := εm / 3 with hε'
  have hε'0 : 0 < ε' := by positivity
  have hε'1 : ε' ≤ 1 := by have : εm ≤ 1 / 2 := min_le_right _ _; linarith
  set β := min (β₀ / 2) (εm / 3) with hβdef
  have hβ0 : 0 < β := lt_min (half_pos hβ₀) (by positivity)
  have hββ₀ : β < β₀ := (min_le_left _ _).trans_lt (half_lt_self hβ₀)
  have hβh : β ≤ 1 / 2 := by have : β ≤ β₀ / 2 := min_le_left _ _; linarith
  have hβ1 : β < 1 := by linarith
  have hβε : β + ε' ≤ ε := by
    have h1 : β ≤ εm / 3 := min_le_right _ _
    have h2 : εm ≤ ε := min_le_left _ _
    linarith
  set D' := D + M + 3 with hD'
  have hD'0 : 0 < D' := by linarith
  obtain ⟨N₁, hN₁⟩ := hethW β hβ0 hββ₀ ε' D' hε'0 hD'0
  obtain ⟨N₂, Cc, hCc, hN₂⟩ := gue_largeRhoCountBad_section_le hBridge hELG hMDE a Ccnt s r
    (r / 2) v₀ hs (half_pos hr) hv₀ β hβ0 hβ1 D' hD'0
  -- the constants
  set Kq := max K₀ 0 with hKq
  have hKq0 : 0 ≤ Kq := le_max_right _ _
  set Z := largeRhoZ s v₀ Kq with hZ
  have hZ0 : 0 ≤ Z := by rw [hZ]; unfold largeRhoZ; positivity
  set Lb := 2 * resLip (s / 2) v₀ / v₀ with hLb
  set cbar := 1 / (s * v₀ ^ 2) with hcbar
  have hcbar0 : 0 ≤ cbar := by positivity
  set Cpt := 4 * (2 * Cc + 1) + 2 * Lb + 14 + 5 * cbar with hCpt
  set Cprob := C₁ + C₂ + 30 * |T| + Cn with hCprob
  set Cfin := max Cpt Cprob with hCfin
  -- certificate threshold constants
  set q := (s * (Real.sqrt κ / 2))⁻¹ with hq
  set La := 1 / 2 + 2 / Real.sqrt κ with hLa
  set G₀ := 2 * q * q + 2 * q * q * (s * La) + La with hG₀
  set Q := 8 / (s * Real.sqrt κ) + G₀ with hQ
  have hsk : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ0
  have hQ0 : 0 ≤ Q := by positivity
  -- the large-`W` conditions
  have ev1 : ∀ᶠ n : ℕ in atTop, 4 * T ^ 2 + 5 + 2 ≤ ((n : ℕ) : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop _
  have ev2 : ∀ᶠ n : ℕ in atTop,
      s / (2 * s₀) + Z * κ₁ ^ 4 + T ^ 2 + 4 * Kq ≤ ((n : ℕ) : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop _
  have ev3 := eventually_const_mul_rpow_le ((1 + Q) / εc) (-(1 / 2)) (by norm_num)
  have ev4 := eventually_const_mul_rpow_le (4 / r + 8) (-(1 / 2)) (by norm_num)
  obtain ⟨W₀, hW₀⟩ := eventually_atTop.mp ((eventually_ge_atTop (N₁ + N₂ + 1)).and
    (ev1.and (ev2.and (ev3.and ev4))))
  refine ⟨4 * (A₀ + 5) + 1, Cfin, W₀, fun p hpb hn hWW model i Pω hPω B hB => ?_⟩
  obtain ⟨hNN, hW7, hW2, hWc, hWr⟩ := hW₀ p.W hWW
  -- scale facts
  set W : ℝ := (p.W : ℝ) with hWdef
  have hW1 : (1 : ℝ) ≤ W := by rw [hWdef]; exact_mod_cast p.W_pos
  have hW0 : (0 : ℝ) < W := by linarith
  have hspl : splitS p = s := splitS_eq hpb
  have hsp0 : 0 < splitS p := BlockBand.Angular.PairCoareaBridge.splitS_pos p
  have hn0 : (0 : ℝ) < p.n := by exact_mod_cast p.n_pos
  have hT0 : 0 ≤ T := by
    by_contra h; push Not at h
    have := mul_neg_of_neg_of_pos h hW0
    linarith only [this, hn, hn0]
  have hTabs : |T| = T := abs_of_nonneg hT0
  have hZk0 : 0 ≤ Z * κ₁ ^ 4 := by positivity
  have hsk0 : 0 ≤ s / (2 * s₀) := by positivity
  have hss0 : s / (2 * s₀) ≤ W := by linarith only [hW2, hZk0, sq_nonneg T, hKq0]
  have hWZ : Z * κ₁ ^ 4 + T ^ 2 ≤ W := by linarith only [hW2, hsk0, hKq0]
  have h4K : 4 * Kq ≤ W := by linarith only [hW2, hsk0, hZk0, sq_nonneg T]
  have hss : splitS p ≤ 2 * W * s₀₁ := by
    rw [div_le_iff₀ (by positivity)] at hss0
    have h1 : s₀ ≤ s₀₁ := min_le_left _ _
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * W)
    rw [hspl]; linarith only [hss0, h2]
  set X := W ^ (-(1 / 2) : ℝ) with hXdef
  have hX0 : 0 < X := Real.rpow_pos_of_pos hW0 _
  have hXW : X ^ 2 * W = 1 := rpow_neg_half_sq_mul hW0
  have hX1 : X ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW1 (by norm_num)
  have h8X : 8 * X ≤ 1 := by
    have : 0 ≤ 4 / r * X := by positivity
    linarith only [hWr, this]
  have hrX : X ≤ r / 4 := by
    have h1 : 4 / r * X ≤ 1 := by
      have : 0 ≤ 8 * X := by positivity
      linarith only [hWr, this]
    rw [div_mul_eq_mul_div, div_le_one hr] at h1; linarith only [h1]
  set c := (p.n : ℝ) * W with hcdef
  have hc0 : 0 ≤ c := by positivity
  have hc1 : 1 ≤ c := by
    have : (1 : ℝ) ≤ p.n := by exact_mod_cast p.n_pos
    exact one_le_mul_of_one_le_of_one_le this hW1
  have hcT : c ≤ T * W ^ 2 := by
    calc c = (p.n : ℝ) * W := rfl
      _ ≤ T * W * W := mul_le_mul_of_nonneg_right hn hW0.le
      _ = T * W ^ 2 := by ring
  set ε₀ := W ^ (-A₀) with hε₀
  set ε₁ := W ^ (-(A₀ + 1)) with hε₁
  have hε₁0 : 0 < ε₁ := Real.rpow_pos_of_pos hW0 _
  have hε₁1 : ε₁ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith)
  have hε₁₀ : 2 * ε₁ ≤ ε₀ := by
    have e : ε₁ = ε₀ * W ^ (-1 : ℝ) := by
      rw [hε₁, hε₀, ← Real.rpow_add hW0]; ring_nf
    have h2 : W ^ (-1 : ℝ) ≤ 1 / 2 := by
      rw [Real.rpow_neg_one, one_div]
      exact inv_anti₀ (by norm_num) (by have := sq_nonneg T; linarith only [hW7, this])
    have h0 : 0 ≤ ε₀ := Real.rpow_nonneg hW0.le _
    have h3 := mul_le_mul_of_nonneg_left h2 h0
    rw [e]; linarith only [h3]
  set hE := W ^ (-2 : ℝ) / (c ^ 2 / ε₁ ^ 2 + 1) with hhE
  have hWm2 : 0 < W ^ (-2 : ℝ) := Real.rpow_pos_of_pos hW0 _
  have hhE0 : 0 < hE := div_pos hWm2 (by positivity)
  have hrE : (c ^ 2 / ε₁ ^ 2 + 1) * hE = W ^ (-2 : ℝ) := by
    rw [hhE]; exact mul_div_cancel₀ _ (ne_of_gt (by positivity))
  have hη : ε₁ + hE ≤ ε₀ := by
    have hW2' : W ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW1 (by norm_num)
    have e : (c ^ 2 / ε₁ ^ 2 + 1) * hE = hE * (c ^ 2 / ε₁ ^ 2) + hE := by ring
    have hq1 : hE * (c ^ 2 / ε₁ ^ 2) ≤ 1 := by linarith only [hrE, e, hhE0, hW2']
    have hq2 : hE * c ^ 2 ≤ ε₁ ^ 2 := by
      have e2 : hE * (c ^ 2 / ε₁ ^ 2) * ε₁ ^ 2 = hE * c ^ 2 := by field_simp
      have := mul_le_mul_of_nonneg_right hq1 (sq_nonneg ε₁)
      linarith only [this, e2]
    have hq3 : hE ≤ hE * c ^ 2 := le_mul_of_one_le_right hhE0.le (one_le_pow₀ hc1)
    have hq4 : ε₁ ^ 2 ≤ ε₁ := by rw [sq]; exact mul_le_of_le_one_left hε₁0.le hε₁1
    linarith only [hq2, hq3, hq4, hε₁₀]
  -- the energy grid
  obtain ⟨Es, hEs, hEsc, hEsg⟩ := ProofPartOne.exists_bulk_grid hκ0.le hκ2 hhE0
  have hcard : (Es.card : ℝ) ≤ W ^ M := by
    refine hEsc.trans ((le_of_eq ?_).trans (ProofPartOne.grid_card_bound hW1 hn0.le hn
      (by linarith only [hA₀0] : 0 ≤ A₀ + 1) (by linarith only [hW7])))
    rfl
  have hEs2 : ∀ e ∈ Es, |e| ≤ 2 := by
    intro e he
    obtain ⟨a1, a2⟩ := hEs e he
    rw [abs_le]; constructor <;> linarith only [a1, a2, hκ0]
  obtain ⟨Ω₁, S₁, hcs₁, hgood₁, hjoint₁⟩ := hext₁ p hpb hn model i Pω hPω Es hEs hcard
  obtain ⟨Ω₂, S₂, hcs₂, hgood₂, -⟩ := hext₂ p hpb hn model i Pω hPω Es hEs hcard
  obtain ⟨sel⟩ := hEig (2 * p.W) (Nat.mul_pos two_pos p.W_pos)
  obtain ⟨sel'⟩ := hEig (2 * p.W - 1)
    (by have := p.W_pos; omega)
  obtain ⟨Jc, hJm, hJs, hBn, hJclose⟩ := exists_largeGridJ sel hε₁0 hB
  -- the window-centre grid
  set h := compressRadius p β with hhdef
  obtain ⟨hhlo, hhup⟩ := compressRadius_bounds (p := p) hβ0.le hβ1.le
  have hh0 : 0 < h := lt_of_lt_of_le (by positivity) hhlo
  have hhX : h ≤ X := hhup.trans (Real.rpow_le_rpow_of_exponent_le hW1 (by linarith))
  set Ms := intervalGrid δ (h / 2) with hMsdef
  have hMs : (Ms.card : ℝ) ≤ 6 * W := centreGrid_card_le hW1 hδ0.le hδ1 hhlo
  have hmemM : ∀ μ ∈ Ms, |μ| ≤ δ := fun μ hμ => intervalGrid_mem hδ0.le (by positivity) hμ
  -- the compressed variance
  obtain ⟨hcv1, hcv2⟩ := compressVar_bounds (p := p) hs.le
  have hcvm : compressVar p (splitS p) ∈ Icc (s / 2) s := by rw [hspl]; exact ⟨hcv1, hcv2⟩
  -- the certificate threshold
  have hthr : W ^ (-1 + 1 / 2 : ℝ) + 4 / (W * (splitS p * Real.sqrt κ)) + G₀ * W ^ (-2 : ℝ) ≤ εc
      ∧ 8 / (W * splitS p * Real.sqrt κ) ≤ εc := by
    have hm : W ^ (-1 + 1 / 2 : ℝ) = W ^ (-(1 / 2) : ℝ) := by norm_num
    have hWh0 : 0 ≤ W ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg hW0.le _
    have hW1' : W⁻¹ ≤ W ^ (-(1 / 2) : ℝ) := by
      rw [← Real.rpow_neg_one]; exact Real.rpow_le_rpow_of_exponent_le hW1 (by norm_num)
    have hW2' : W ^ (-2 : ℝ) ≤ W ^ (-(1 / 2) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hW1 (by norm_num)
    have hc' : (1 + Q) * W ^ (-(1 / 2) : ℝ) ≤ εc := by
      have := hWc; rw [div_mul_eq_mul_div, div_le_one hεc] at this; exact this
    have e8 : 8 / (W * splitS p * Real.sqrt κ) = 8 / (s * Real.sqrt κ) * W⁻¹ := by
      rw [hspl]; field_simp
    have e4 : 4 / (W * (splitS p * Real.sqrt κ)) ≤ 8 / (s * Real.sqrt κ) * W⁻¹ := by
      rw [hspl, show 8 / (s * Real.sqrt κ) * W⁻¹ = 8 / (W * (s * Real.sqrt κ)) by field_simp]
      exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
    have hG0 : 0 ≤ G₀ := by positivity
    have a1 : 8 / (s * Real.sqrt κ) * W⁻¹ ≤ 8 / (s * Real.sqrt κ) * W ^ (-(1 / 2) : ℝ) :=
      mul_le_mul_of_nonneg_left hW1' (by positivity)
    have a2 : G₀ * W ^ (-2 : ℝ) ≤ G₀ * W ^ (-(1 / 2) : ℝ) := mul_le_mul_of_nonneg_left hW2' hG0
    rw [hm, e8]
    rw [hQ] at hc'
    constructor
    · linarith only [hc', a1, a2, e4]
    · linarith only [a1, hc', mul_nonneg hG0 hWh0, hWh0]
  have h8 : 8 / (W * splitS p * Real.sqrt κ) ≤ εc₁ := hthr.2.trans (min_le_left _ _)
  have h2f : 2 / (W * splitS p * Real.sqrt κ) ≤ εc₂ := by
    refine le_trans ?_ (hthr.2.trans (min_le_right _ _))
    exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
  have hgl : ∀ e : ℝ, |e| ≤ hE → BlockBand.DeterminantScore.SelectedResolvent.gridLip (splitS p) κ c
      ε₁ * |e| ≤ G₀ * W ^ (-2 : ℝ) := by
    intro e he
    have hhEW : hE ≤ W ^ (-2 : ℝ) := by
      have h0 : 0 ≤ c ^ 2 / ε₁ ^ 2 := by positivity
      rw [hhE]; exact div_le_self hWm2.le (by linarith only [h0])
    unfold BlockBand.DeterminantScore.SelectedResolvent.gridLip
    rw [hspl]
    have h0 : 0 ≤ 2 * (s * (Real.sqrt κ / 2))⁻¹ * (s * (Real.sqrt κ / 2))⁻¹ *
        (c ^ 2 / ε₁ ^ 2 + 1 + s * (1 / 2 + 2 / Real.sqrt κ)) + (1 / 2 + 2 / Real.sqrt κ) := by
      positivity
    have e : (2 * (s * (Real.sqrt κ / 2))⁻¹ * (s * (Real.sqrt κ / 2))⁻¹ *
        (c ^ 2 / ε₁ ^ 2 + 1 + s * (1 / 2 + 2 / Real.sqrt κ)) + (1 / 2 + 2 / Real.sqrt κ)) * hE =
        2 * q * q * ((c ^ 2 / ε₁ ^ 2 + 1) * hE) + (2 * q * q * (s * La) + La) * hE := by
      rw [hq, hLa]; ring
    have h1 : (2 * q * q * (s * La) + La) * hE ≤ (2 * q * q * (s * La) + La) * W ^ (-2 : ℝ) :=
      mul_le_mul_of_nonneg_left hhEW (by positivity)
    calc _ ≤ _ * hE := mul_le_mul_of_nonneg_left he h0
      _ = _ := e
      _ ≤ G₀ * W ^ (-2 : ℝ) := by rw [hrE, hG₀]; linarith only [h1]
  have hcertG : ∀ om : SplitState p i, ExteriorGood p i CG ε₁ (1 / 2) κ Es om →
      ∀ e ∈ Es, certErrHat ε₁ p i om e ≤ εc := by
    intro om hom e he
    refine (hom.2.2.2 e he).trans ?_
    unfold certThreshold
    have : 0 ≤ G₀ * W ^ (-2 : ℝ) := by positivity
    linarith only [hthr.1, this]
  -- the regular part
  have hreg : ∀ om : SplitState p i, ∀ hH : om.1.IsHermitian, ExtNormBounds p i CG om →
      ∀ j₀ : ExteriorSite p i, ∀ x : ℝ, |x| ≤ 2 → PoleSeparated ε₁ hH j₀ x →
        ‖regF hH j₀ om.2.1 om.2.2 x - (x : ℂ) • (1 : PairMatrix p i)‖ ≤ κ₀ * W ^ a := by
    intro om hH hext j₀ x hx hsep
    have hC : ‖om.2.1‖ ≤ c := opNorm_le_of_toE _ hc0 hext.1
    have hV : ‖om.2.2‖ ≤ c + CG := opNorm_le_of_toE _ (by positivity) hext.2.2
    have h1 := opNorm_regK_le hε₁0 om hH j₀ hsep
    have h2 := regScale_le hW1 hT0 hcT hCG.le hA₀0 hV (norm_nonneg _) hC hx
    rw [hκ₀, hTabs]
    exact h1.trans h2
  have hWa1 : 1 ≤ W ^ a := Real.one_le_rpow hW1 (by linarith only [ha1])
  have hWN : W ^ a ≤ ((2 * p.W - 1 : ℕ) : ℝ) ^ a := by
    rw [natCast_two_mul_sub_one]
    exact Real.rpow_le_rpow hW0.le (by linarith only [hW1]) (by linarith only [ha1])
  have hWN2 : W ^ a ≤ ((2 * p.W : ℕ) : ℝ) ^ a := by
    have : ((2 * p.W : ℕ) : ℝ) = 2 * W := by rw [hWdef]; push_cast; ring
    rw [this]
    exact Real.rpow_le_rpow hW0.le (by linarith only [hW1]) (by linarith only [ha1])
  -- the hypotheses of the compressed ETH at an exterior point
  have hethHyp : ∀ om : SplitState p i, ExteriorGood p i CG ε₁ (1 / 2) κ Es om →
      ∀ j₀ : ExteriorSite p i, ∀ e ∈ Es, ∀ μ ∈ Ms, om ∈ poleLabelSet ε₁ j₀ e →
        (Real.sqrt (compressVar p (splitS p)))⁻¹ * ‖compRegM sel ε₁ j₀ e om‖ ≤
            Ceth * ((2 * p.W - 1 : ℕ) : ℝ) ^ a ∧
          RootRectangle (compRegM sel ε₁ j₀ e om) (compressVar p (splitS p)) μ (r / 2) v₀ ∧
          (Jc j₀ e om).IsHermitian ∧ ‖Jc j₀ e om‖ ≤ 1 := by
    intro om hom j₀ e he μ hμ hl
    have hcert := hcertG om hom e he
    have hJ := hJs j₀ e om hl
    obtain ⟨hH, hsimp, hsep⟩ := hl
    obtain ⟨⟨-, hV⟩, -, hext, -⟩ := hom
    have hnorm : ‖compRegM sel ε₁ j₀ e om‖ ≤ κ₀ * W ^ a := by
      rw [compRegM_eq sel ε₁ hH hV hsimp hsep]
      exact (opNorm_compress_le (poleIsometry_spec sel hH hsimp).1 _).trans
        (hreg om hH hext j₀ e (hEs2 e he) hsep)
    refine ⟨?_, ?_, hJ⟩
    · have hsq : Real.sqrt (s / 2) ≤ Real.sqrt (compressVar p (splitS p)) :=
        Real.sqrt_le_sqrt hcvm.1
      have hinv : (Real.sqrt (compressVar p (splitS p)))⁻¹ ≤ (Real.sqrt (s / 2))⁻¹ :=
        inv_anti₀ (Real.sqrt_pos.mpr (half_pos hs)) hsq
      calc (Real.sqrt (compressVar p (splitS p)))⁻¹ * ‖compRegM sel ε₁ j₀ e om‖
          ≤ (Real.sqrt (s / 2))⁻¹ * (κ₀ * W ^ a) :=
            mul_le_mul hinv hnorm (norm_nonneg _) (inv_nonneg.mpr (Real.sqrt_nonneg _))
        _ ≤ (Real.sqrt (s / 2))⁻¹ * (κ₀ * ((2 * p.W - 1 : ℕ) : ℝ) ^ a) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hWN hκ₀0)
              (inv_nonneg.mpr (Real.sqrt_nonneg _))
        _ = Ceth * ((2 * p.W - 1 : ℕ) : ℝ) ^ a := by rw [hCeth]; ring
    · have hR := (hrect p hpb i om hV ε₁ e (hEs e he) (hcert.trans (min_le_left _ _)) h8 hss sel
        hH j₀ hsimp hsep).2.1
      have hμr : |μ| + r / 2 ≤ r := by have := hmemM μ hμ; linarith only [this, hδr, hr]
      exact rootRectangle_shift (rootRectangle_mono hR (min_le_left _ _) (min_le_left _ _)) hμr
  -- the hypotheses of the compressed count at an exterior point
  have hcntHyp : ∀ om : SplitState p i, ExteriorGood p i CG ε₁ (1 / 2) κ Es om →
      ∀ j₀ : ExteriorSite p i, ∀ e ∈ Es, om ∈ poleLabelSet ε₁ j₀ e →
        ∃ K : PairMatrix p i, K.IsHermitian ∧
          (poleIsometry sel j₀ om)ᴴ * K * poleIsometry sel j₀ om = compRegM sel ε₁ j₀ e om ∧
          (Real.sqrt (splitS p))⁻¹ * ‖K‖ ≤ Ccnt * ((2 * p.W : ℕ) : ℝ) ^ a ∧
          ∀ μ ∈ Ms, |μ| ≤ r ∧ PairRootRectangle K (splitS p) μ (r / 2) v₀ := by
    intro om hom j₀ e he hl
    have hcert := hcertG om hom e he
    obtain ⟨hH, hsimp, hsep⟩ := hl
    obtain ⟨⟨-, hV⟩, -, hext, -⟩ := hom
    have hKeq : regF hH j₀ om.2.1 om.2.2 e +
        ((0 : ℝ) : ℂ) • vecMulVec (poleDir hH j₀ om.2.1) (star (poleDir hH j₀ om.2.1)) -
          (e : ℂ) • (1 : PairMatrix p i) =
        regF hH j₀ om.2.1 om.2.2 e - (e : ℂ) • (1 : PairMatrix p i) := by simp
    refine ⟨_, ?_, poleCompress_regK_rankOne_eq sel ε₁ hH hV hsimp hsep 0, ?_, ?_⟩
    · rw [hKeq]; exact isHermitian_regK om hH hV j₀ e
    · rw [hKeq, hspl]
      have hn := hreg om hH hext j₀ e (hEs2 e he) hsep
      calc (Real.sqrt s)⁻¹ * ‖regF hH j₀ om.2.1 om.2.2 e - (e : ℂ) • (1 : PairMatrix p i)‖
          ≤ (Real.sqrt s)⁻¹ * (κ₀ * W ^ a) :=
            mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr (Real.sqrt_nonneg _))
        _ ≤ (Real.sqrt s)⁻¹ * (κ₀ * ((2 * p.W : ℕ) : ℝ) ^ a) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hWN2 hκ₀0)
              (inv_nonneg.mpr (Real.sqrt_nonneg _))
        _ = Ccnt * ((2 * p.W : ℕ) : ℝ) ^ a := by rw [hCcnt]; ring
    · intro μ hμ
      have hμδ := hmemM μ hμ
      refine ⟨by linarith only [hμδ, hδr, hr], ?_⟩
      have hR := hfam p hpb i om hV ε₁ e (hEs e he) (hcert.trans (min_le_right _ _)) h2f hH j₀
        hsep 0 (splitS p) (by linarith only [hs₀₂]) le_rfl
      exact pairRootRectangle_shift (pairRootRectangle_mono hR (show r ≤ r₂ from min_le_right _ _)
        (show v₀ ≤ v₀₂ from min_le_right _ _)) (by rw [sub_zero]; linarith only [hμδ, hδr, hr])
  -- the bad set
  set nS := Cc * ((2 * p.W : ℕ) : ℝ) ^ β + 1 with hnS
  set Sc := largeRhoCompBad sel sel' ε₁ Es Ms (compressVar p (splitS p)) β ε' Jc with hSc
  set Sn := largeRhoCountBad sel sel' ε₁ Es Ms β nS with hSn
  set Sg := ProofNormEvent.gueEvent p i CGG with hSg
  set ν := gueMeasure (PairSite p i) (pairTime p (splitS p)) with hν
  set w := W ^ (-D) with hw
  have hw0 : 0 ≤ w := Real.rpow_nonneg hW0.le _
  have hN₁W : N₁ ≤ 2 * p.W - 1 := by omega
  have hN₂W : N₂ ≤ 2 * p.W := by omega
  refine ⟨Ω₁ ∪ Ω₂, S₁ ∪ S₂ ∪ Sc ∪ Sn ∪ Sg, ?_, ?_, ?_, ?_⟩
  · exact (((hcs₁.1.union hcs₂.1).union (measurableSet_largeRhoCompBad sel sel' hε₁0 Es Ms
      (compressVar_pos (p := p) hsp0) β ε' hJm)).union
      (measurableSet_largeRhoCountBad sel sel' hε₁0 Es Ms β nS)).union (measurableSet_gueEvent CGG)
  · -- the exterior probability
    refine (measure_union_le _ _).trans ((add_le_add hcs₁.2.1 hcs₂.2.1).trans ?_)
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : C₁ + C₂ ≤ Cfin := by
      have : 0 ≤ 30 * |T| := by positivity
      exact le_trans (by rw [hCprob]; linarith only [this, hCn]) (le_max_right _ _)
    have := mul_le_mul_of_nonneg_right h1 hw0
    linarith only [this]
  · -- the sections
    intro om hom
    simp only [Set.mem_union, not_or] at hom
    have hg := hgood₂ om hom.2
    have hsc := hN₁ p i hN₁W (splitS p) hsp0 hcvm sel sel' ε₁ Es Ms Jc om (hethHyp om hg)
    have hsn := hN₂ p i hN₂W (splitS p) hspl.ge sel sel' ε₁ Es Ms om (hcntHyp om hg)
    have hsg := hgueE p i om
    have hidx := largeRho_index_le (i := i) hT0 hD.le hM0 hn hcard hMs
    have hexp : Real.exp (-(cG * (2 * W))) ≤ Cn * w := by
      have := hnb p hn
      have h0 : 0 ≤ 4 * ((p.n : ℝ) * p.W) ^ 2 * Real.exp (-(p.W : ℝ) / 8) := by positivity
      linarith only [this, h0]
    rw [Set.preimage_union, Set.preimage_union, Set.preimage_union, Set.preimage_union]
    refine (measure_union5_le ν _ _ _ _ _).trans ?_
    have e : ν (Prod.mk om ⁻¹' S₁) + ν (Prod.mk om ⁻¹' S₂) + ν (Prod.mk om ⁻¹' Sc) +
        ν (Prod.mk om ⁻¹' Sn) + ν (Prod.mk om ⁻¹' Sg) =
        (ν (Prod.mk om ⁻¹' S₁) + ν (Prod.mk om ⁻¹' S₂)) +
          (ν (Prod.mk om ⁻¹' Sc) + ν (Prod.mk om ⁻¹' Sn)) + ν (Prod.mk om ⁻¹' Sg) := by ring
    rw [e]
    refine (add_le_add (add_le_add (add_le_add (hcs₁.2.2 om hom.1) (hcs₂.2.2 om hom.2))
      ((add_le_add hsc hsn).trans hidx)) (hsg.trans (ENNReal.ofReal_le_ofReal hexp))).trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : Cprob ≤ Cfin := le_max_right _ _
    have e2 : C₁ * w + C₂ * w + 30 * T * w + Cn * w = Cprob * w := by
      rw [hCprob, hTabs]; ring
    have := mul_le_mul_of_nonneg_right h1 hw0
    linarith only [this, e2]
  · -- the conclusion off the bad set
    intro x hx1 hx2 α hα hlg
    simp only [Set.mem_union, not_or] at hx1 hx2
    obtain ⟨⟨⟨⟨hxS₁, -⟩, hxSc⟩, hxSn⟩, hxSg⟩ := hx2
    obtain ⟨-, hdetall, hrank⟩ := hjoint₁ x hx1.1 hxS₁
    obtain ⟨⟨hH, hV⟩, hcrowd, -, -⟩ := hgood₁ x.1 hx1.1
    have hg := hgood₂ x.1 hx1.2
    have hext : ExtNormBounds p i CG x.1 := hg.2.2.1
    set E := physicalOrderedEigenvalue p (assemble p i x.1 x.2) α with hEdef
    have hαϑ' : IsBulkRank p ϑ' α := ProofPartOne.isBulkRank_antitone (min_le_left _ _) hα
    have hcl := BlockBand.Window.Count.classicalLocation_mem_bulk p hϑ'0 hαϑ'
    have hEκ : E ∈ bulkInterval κ := by
      have hEl := hrank α hαϑ'
      obtain ⟨c1, c2⟩ := hcl
      rw [abs_lt] at hEl
      have : Real.pi * ϑ' / 2 = 2 * κ := by rw [hκ]; ring
      refine ⟨?_, ?_⟩ <;> linarith only [c1, c2, hEl.1, hEl.2, this]
    have hE2 : |E| ≤ 2 := by
      obtain ⟨c1, c2⟩ := hEκ; rw [abs_le]; constructor <;> linarith only [c1, c2, hκ0]
    obtain ⟨e, he, hEe⟩ := hEsg E hEκ
    have hEe' : ε₁ + |E - e| ≤ W ^ (-A₀) := by linarith only [hη, hEe]
    obtain ⟨j₀, hsimp, -, hsepE, hsepe, hρgt⟩ :=
      largeRho_label hH (hdetall α) (hcrowd E hE2) hlg hEe'
    have hC : ‖x.1.2.1‖ ≤ c := opNorm_le_of_toE _ hc0 hext.1
    have hsq : sqNorm (poleCoupling hH j₀ x.1.2.1) ≤ c ^ 2 :=
      sqNorm_poleCoupling_le_of_toE hH j₀ hext.2.1
    set ρ := poleRho hH j₀ x.1.2.1 E with hρdef
    set Kb := κ₁ * W ^ a with hKb
    have hWa : W ≤ W ^ a := by
      calc W = W ^ (1 : ℝ) := (Real.rpow_one W).symm
        _ ≤ W ^ a := Real.rpow_le_rpow_of_exponent_le hW1 ha1
    have hKbW : W ≤ Kb := hWa.trans (le_mul_of_one_le_left (by linarith only [hWa1]) hκ₁1)
    have hKb0 : 0 < Kb := by linarith only [hKbW, hW1]
    have hρZ : Z * Kb ^ 4 ≤ |ρ| := rho_lower hW1 hc0 hcT hA₀0 hsq hWZ hρgt
    have hnM : ‖regF hH j₀ x.1.2.1 x.1.2.2 E - (E : ℂ) • (1 : PairMatrix p i)‖ ≤ κ₀ * W ^ a :=
      hreg x.1 hH hext j₀ E hE2 hsepE
    have hnMK : ‖regF hH j₀ x.1.2.1 x.1.2.2 E - (E : ℂ) • (1 : PairMatrix p i)‖ ≤ Kb := by
      refine hnM.trans (mul_le_mul_of_nonneg_right (by rw [hκ₁]; linarith only [hCGG])
        (by linarith only [hWa1]))
    have hGn : ‖x.2‖ ≤ CGG := not_lt.mp hxSg
    have hMG : ‖regF hH j₀ x.1.2.1 x.1.2.2 E - (E : ℂ) • 1 + x.2‖ ≤ Kb := by
      refine (norm_add_le _ _).trans ?_
      have h1 : CGG ≤ CGG * W ^ a := le_mul_of_one_le_right hCGG.le hWa1
      have e : Kb = κ₀ * W ^ a + CGG * W ^ a + W ^ a := by rw [hKb, hκ₁]; ring
      linarith only [hnM, hGn, h1, e, hWa1]
    -- certificates and root rectangles
    have hcerte : certErrHat ε₁ p i x.1 e ≤ εc := hcertG x.1 hg e he
    have hcertE : certErrHat ε₁ p i x.1 E ≤ εc := by
      have h1 := BlockBand.DeterminantScore.SelectedResolvent.certErrHat_le_grid x.1 hH hV hε₁0
        hc0 hκ0 hext.1 hext.2.1 hsp0 hEκ (hEs e he)
      have h2 := hgl (E - e) hEe
      have h3 := hg.2.2.2 e he
      unfold certThreshold at h3
      linarith only [h1, h2, h3, hthr.1]
    have hR₁ := hrect p hpb i x.1 hV ε₁ E hEκ (hcertE.trans (min_le_left _ _)) h8 hss sel hH j₀
      hsimp hsepE
    have hR₂ := hrect p hpb i x.1 hV ε₁ e (hEs e he) (hcerte.trans (min_le_left _ _)) h8 hss sel
      hH j₀ hsimp hsepe
    have hRc := rootRectangle_mono hR₁.1 (min_le_left r₁ r₂) (min_le_left v₀₁ v₀₂)
    have hRK := pairRootRectangle_mono (hR₁.2.2 (hdetall α)) (min_le_left r₁ r₂)
      (min_le_left v₀₁ v₀₂)
    have hRe := rootRectangle_mono hR₂.2.1 (min_le_left r₁ r₂) (min_le_left v₀₁ v₀₂)
    have hl : x.1 ∈ poleLabelSet ε₁ j₀ e := ⟨hH, hsimp, hsepe⟩
    intro lam hlam u hu hAu
    obtain ⟨μ, hμM, hlamμ⟩ := exists_intervalGrid_near (half_pos hh0) hlam
    have hμδ := hmemM μ hμM
    have hwin : NatWindowGood (compRegF sel ε₁ j₀ e x.1) sel' (compressVar p (splitS p)) μ β ε'
        (Jc j₀ e x.1) ((poleIsometry sel j₀ x.1)ᴴ * x.2 * poleIsometry sel j₀ x.1) := by
      by_contra hbad
      apply hxSc
      rw [hSc]
      unfold largeRhoCompBad
      exact mem_iUnion.2 ⟨j₀, mem_iUnion₂.2 ⟨e, he, mem_iUnion₂.2 ⟨μ, hμM, ⟨hl, hbad⟩⟩⟩⟩
    have hcount := hcount_of_not_mem_largeRhoCountBad (om := x.1) (G := x.2) sel sel'
      (show (x.1, x.2) ∉ Sn by rw [Prod.mk.eta]; exact hxSn) he hμM hl
    -- the conditions on `ρ`
    have hlam1 : |lam| ≤ 1 := hlam.trans (hδ1.trans (by norm_num))
    obtain ⟨hρ4, hρ6, hρlam, hδ₁, hδ₂, hcceX, hqX, hKKX, hδJ2⟩ :=
      largeRho_rho_conds (s' := compressVar p s) (K₀ := Kq) hW1 hKbW hX0 hXW hs hcv1 hv₀
        (norm_nonneg _) hnMK hlam1 hKq0 hρZ
    have hρpos : 0 < |ρ| := by linarith only [hρ4, hKb0]
    -- the observable change
    have hδJ := hJclose x.1 hH hV j₀ hsimp E e hsepE hsepe (hdetall α) Kb hKb0 hnMK hρ6
    -- the operator error from the grid
    set rg := (‖x.1.2.1‖ ^ 2 / ε₁ ^ 2 + 1) * |E - e| with hrg
    have hrg0 : 0 ≤ rg := by positivity
    have hrgW : rg ≤ W ^ (-2 : ℝ) := by
      have h1 : ‖x.1.2.1‖ ^ 2 / ε₁ ^ 2 + 1 ≤ c ^ 2 / ε₁ ^ 2 + 1 := by
        have := pow_le_pow_left₀ (norm_nonneg _) hC 2
        have := div_le_div_of_nonneg_right this (sq_nonneg ε₁)
        linarith only [this]
      rw [hrg, ← hrE]
      exact mul_le_mul h1 hEe (abs_nonneg _) (by positivity)
    have hXh : X * (1 / (2 * W)) / 4 ≤ X * h / 4 := by
      have := mul_le_mul_of_nonneg_left hhlo hX0.le
      linarith only [this]
    have hrgX : rg ≤ X * h / 4 := (hrgW.trans (rpow_neg_two_le hW1 h8X)).trans hXh
    have hKK : 4 * Kb ^ 2 / |ρ| ≤ X * h / 4 := hKKX.trans hXh
    set δJ := Real.sqrt ((2 * p.W - 1 : ℕ) : ℝ) * Kq * rg +
      Real.sqrt (2 * W) * ((3 * Kq * Kb ^ 2 + 4 * Kb) / |ρ|) with hδJdef
    have hδJ0 : 0 ≤ δJ := by
      have : 0 ≤ (3 * Kq * Kb ^ 2 + 4 * Kb) / |ρ| := div_nonneg (by positivity) hρpos.le
      positivity
    have hK4W : 4 * Kq * W ^ (-1 : ℝ) ≤ 1 := by
      rw [Real.rpow_neg_one, ← div_eq_mul_inv, div_le_one hW0]; exact h4K
    have hδJX : δJ ≤ X := by
      have h1 := sqrt_mul_rg_le (N := ((2 * p.W - 1 : ℕ) : ℝ)) hW1
        (by rw [natCast_two_mul_sub_one]; linarith only []) hKq0 hrg0 hrgW hK4W
      linarith only [h1, hδJ2, hδJdef]
    -- the deterministic bound at the eigenvector
    have hmain := largeRho_point_le sel sel' hε₁0 hH hV hsimp hsepE hsepe (hdetall α) hKb0 hMG
      hρ4 (by linarith only [hlam1, hKbW, hW1]) (sqNorm_eq_one_of_l2Norm hu) hAu (hBn x.1 E) (hJs j₀ e x.1 hl).2 hδJ
      hsp0 hv₀ hwin hcount hlamμ hRK hRc hRe (by linarith only [hlam, hδr, hr, hrdef])
      (by linarith only [hμδ, hδr, hhX, hrX, hrdef, hhdef, hr]) hρlam
      (by rw [hspl]; exact hδ₁) (by rw [hspl]; exact hδ₂)
    refine hmain.trans ?_
    rw [hspl]
    -- the error budget
    have hL0 : 0 ≤ 2 * resLip (compressVar p s) v₀ / v₀ := by
      have h1 : 0 ≤ resLip (compressVar p s) v₀ := by
        unfold resLip
        have := rootLip_nonneg (compressVar p s) v₀
        have := compressVar_pos (p := p) hs
        positivity
      positivity
    have hL : 2 * resLip (compressVar p s) v₀ / v₀ ≤ Lb := by
      rw [hLb]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (resLip_anti (half_pos hs) hcv1 hv₀) (by norm_num)) hv₀.le
    have hcce : compressCentreErr p s v₀
        ‖regF hH j₀ x.1.2.1 x.1.2.2 E - (E : ℂ) • (1 : PairMatrix p i)‖ ρ lam ≤ X := hcceX
    refine (largeRho_budget_le (X := X) hX0.le hX1 hh0 hL0 hrg0 hrgX hKb0.le hρpos hKK hqX hδJ0
      hδJX hcce hs hv₀ hcv1).trans ?_
    have e5 : (5 : ℝ) / (s * v₀ ^ 2) = 5 * cbar := by rw [hcbar]; ring
    rw [e5]
    have hnStol := nS_mul_compressTol_le (p := p) hCc.le hβ0.le hβ1.le hε'0.le hε'1
    refine (largeRho_final_le hW1 hh0.le hhup hβh hnStol hβε hε.le hL0 hL hcbar0 hCc.le).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hW0.le _)

end

end BlockBand.LocalWindow.ProofPartTwo.GUEInputs
