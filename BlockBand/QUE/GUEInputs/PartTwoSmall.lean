module

public import BlockBand.LocalWindow.ProofPartTwoSmall
public import BlockBand.QUE.GUEInputs.Fields
public import BlockBand.QUE.GUEInputs.PartTwoMeasurable

/-!
# The small-`ρ` branch of the physical local window, part (ii) (GUE inputs)

`partTwoSmallRho_holds`: the small-`ρ` branch of part (ii) of the physical local window lemma.

The statements are those of `BlockBand.LocalWindow.ProofPartTwoSmall`, with `NativeInputs` replaced
by the hypotheses `EigenpairsExist` and `SpacingExists` (fields of `External.CEH.SourceContract`) as
needed, and without `GUEWignerFamilyAdapter`.
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

set_option maxHeartbeats 2000000 in
/-- **The small-`ρ` branch of part (ii) of the physical local window lemma.** -/
theorem partTwoSmallRho_holds (hEig : BlockBand.QUE.GUEInputs.EigenpairsExist) (hSp : BlockBand.QUE.GUEInputs.SpacingExists)
    (hMDE : MDEBranchIdentification) (hETH : ExternalETH) (hELG : ExternalLocalGUE)
    (hPBC : PhysicalBlockConditionalCount) (hMT : MatchedTracesContract)
    (hRL : RankLocationContract) (hCo : CoareaContract) (hBridge : PairGUELawBridgeStatement) :
    PartTwoSmallRhoStatement := by
  intro b T ϑ hϑ
  by_cases hb : 0 < b ∧ b < 1 / 2
  swap
  · refine ⟨1 / 2, 1, by norm_num, by norm_num, fun ε _ D _ K₀ A₀ H _ => ⟨0, 0, fun p hpb => ?_⟩⟩
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
  obtain ⟨εc, r, s₀, v₀, hεc, hr, hs₀, hv₀, hrect⟩ := smallRho_rectangles b κ hb0 hb1 hκ0
  set δ := min (r / 2) (1 / 2) with hδ
  have hδ0 : 0 < δ := lt_min (half_pos hr) (by norm_num)
  refine ⟨δ, 1, hδ0, (min_le_right _ _).trans_lt (by norm_num),
    fun ε hε D hD K₀ A₀ H hA₀ => ?_⟩
  have hA₀0 : 0 ≤ A₀ := by linarith
  set s := min (1 - 2 * b) b with hsdef
  have hs : 0 < s := lt_min (by linarith) hb0
  -- the exterior events
  set M := 2 * (A₀ + 1) + 7 with hM
  obtain ⟨CG₁, C₁, -, hC₁, hext₁⟩ := partTwoExterior_le hPBC hMT hRL hCo b T ϑ' κ κ (1 / 2) D M
    A₀ hb0 hb1 hϑ'0 hϑ'1 hκ0 hκ0 (by norm_num) hD.le hA₀
  obtain ⟨CG, C₂, hCG, hC₂, hext₂⟩ := partTwoExterior_le hPBC hMT hRL hCo b T ϑ' κ κ (1 / 2) D M
    (A₀ + 1) hb0 hb1 hϑ'0 hϑ'1 hκ0 hκ0 (by norm_num) hD.le (by linarith)
  -- the window ETH and count at the norm scale of the grid deformations
  set Aeth := A₀ + 5 + |H| with hAeth
  set Ceth := (Real.sqrt s)⁻¹ * (|T| + CG + 2 * T ^ 2 + 3) with hCeth
  obtain ⟨β₀, hβ₀, hβ₀2, hethW⟩ := BlockBand.LocalWindow.ProofPartTwo.GUEInputs.gridWindowBad hSp hMDE hETH hBridge Aeth Ceth s s (r / 2)
    v₀ hs le_rfl (half_pos hr) hv₀
  set εm := min ε (1 / 2) with hεm
  have hεm0 : 0 < εm := lt_min hε (by norm_num)
  set εw := εm / 3 with hεw
  have hεw0 : 0 < εw := by positivity
  set β := min (β₀ / 2) (εm / 3) with hβdef
  have hβ0 : 0 < β := lt_min (half_pos hβ₀) (by positivity)
  have hββ₀ : β < β₀ := (min_le_left _ _).trans_lt (half_lt_self hβ₀)
  have hβ1 : β ≤ 1 := (min_le_left _ _).trans (by linarith)
  have hβε : β + εw ≤ ε := by
    have h1 : β ≤ εm / 3 := min_le_right _ _
    have h2 : εm ≤ ε := min_le_left _ _
    linarith
  have hβh : β + εw ≤ 1 / 2 := by
    have h1 : β ≤ εm / 3 := min_le_right _ _
    have h2 : εm ≤ 1 / 2 := min_le_right _ _
    linarith
  set MI := 3 * A₀ + 18 + |H| with hMI
  have hMI0 : 0 ≤ MI := by positivity
  set D' := D + MI with hD'
  have hD'0 : 0 < D' := by linarith
  obtain ⟨N₁, hN₁⟩ := hethW β hβ0 hββ₀ εw D' hεw0 hD'0
  obtain ⟨N₂, Cc, hCc, hN₂⟩ := gue_windowCount_le hBridge hELG hMDE Aeth Ceth s 1 (r / 2) v₀ hs
    (half_pos hr) hv₀ β hβ0 hβ1 D' hD'0
  -- the constants
  set Kq := max K₀ 0 with hKq
  have hKq0 : 0 ≤ Kq := le_max_right _ _
  set Cpt := 2 * Cc + 4 * (2 * resLip s v₀ / v₀) + 144 + 8 * Kq with hCpt
  set KI := 6 * (|T| + 1) * (2 * T ^ 2 + 4) with hKI
  have hKI0 : 0 ≤ KI := by positivity
  set Cfin := max Cpt (C₁ + C₂ + 3 * KI) with hCfin
  set q := (s * (Real.sqrt κ / 2))⁻¹ with hq
  set La := 1 / 2 + 2 / Real.sqrt κ with hLa
  set G₀ := 2 * q * q + 2 * q * q * (s * La) + La with hG₀
  set Q := 4 / (s * Real.sqrt κ) + G₀ with hQ
  have hsk : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ0
  have hQ0 : 0 ≤ Q := by positivity
  -- the large-`W` conditions
  have ev1 : ∀ᶠ n : ℕ in atTop, 4 * T ^ 2 + 5 + 2 ≤ ((n : ℕ) : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop _
  have ev2 := eventually_const_mul_rpow_le (2 / r) (-1 + β) (by linarith)
  have ev3 := eventually_const_mul_rpow_le ((1 + Q) / εc) (-(1 / 2)) (by norm_num)
  obtain ⟨W₀, hW₀⟩ := eventually_atTop.mp ((eventually_ge_atTop (N₁ + N₂)).and
    (ev1.and (ev2.and ev3)))
  refine ⟨Cfin, W₀, fun p hpb hn hWW model i Pω hPω B hB => ?_⟩
  obtain ⟨hNN, hW7, hWr, hWc⟩ := hW₀ p.W hWW
  -- scale facts
  set W : ℝ := (p.W : ℝ) with hWdef
  have hW1 : (1 : ℝ) ≤ W := by rw [hWdef]; exact_mod_cast p.W_pos
  have hW0 : (0 : ℝ) < W := by linarith
  have hspl : splitS p = s := splitS_eq hpb
  have hn0 : (0 : ℝ) < p.n := by exact_mod_cast p.n_pos
  have hT0 : 0 ≤ T := by
    by_contra h; push Not at h
    have := mul_neg_of_neg_of_pos h hW0
    linarith only [this, hn, hn0]
  have hTabs : |T| = T := abs_of_nonneg hT0
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
  have hhEW : hE ≤ W ^ (-2 : ℝ) := by
    have h0 : 0 ≤ c ^ 2 / ε₁ ^ 2 := by positivity
    rw [hhE]; exact div_le_self hWm2.le (by linarith)
  have hη : ε₁ + hE ≤ ε₀ := by
    have hW2 : W ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW1 (by norm_num)
    have e : (c ^ 2 / ε₁ ^ 2 + 1) * hE = hE * (c ^ 2 / ε₁ ^ 2) + hE := by ring
    have hq1 : hE * (c ^ 2 / ε₁ ^ 2) ≤ 1 := by linarith only [hrE, e, hhE0, hW2]
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
  obtain ⟨Ω₁, S₁, hcs₁, hgood₁, hjoint₁⟩ := hext₁ p hpb hn model i Pω hPω Es hEs hcard
  obtain ⟨Ω₂, S₂, hcs₂, hgood₂, -⟩ := hext₂ p hpb hn model i Pω hPω Es hEs hcard
  obtain ⟨sel⟩ := hEig (2 * p.W) (Nat.mul_pos two_pos p.W_pos)
  obtain ⟨Jg, hJm, hJH, hJn, hJ⟩ := exists_smallGridJ (K₀ := K₀) hε₁0 hB
  -- the grids
  set Lρ := W ^ H + c ^ 2 / W ^ (-A₀) with hLρ
  set d : ℝ := ((2 * p.W : ℕ) : ℝ) with hd
  have hdW : d = 2 * W := by rw [hd, Nat.cast_mul, Nat.cast_two]
  set I := smallIndex (p := p) (i := i) Es Lρ (W ^ (-2 : ℝ)) δ (d ^ (-1 + β)) with hI
  set Sg := smallBadSet sel ε₁ (splitS p) β εw Cc Jg I with hSg
  set ν := gueMeasure (PairSite p i) (pairTime p (splitS p)) with hν
  set w := W ^ (-D) with hw
  have hw0 : 0 ≤ w := Real.rpow_nonneg hW0.le _
  -- certificate threshold
  have hthr : W ^ (-1 + 1 / 2 : ℝ) + 4 / (W * (splitS p * Real.sqrt κ)) + G₀ * W ^ (-2 : ℝ) ≤ εc
      ∧ 2 / (W * splitS p * Real.sqrt κ) ≤ εc := by
    have hm : W ^ (-1 + 1 / 2 : ℝ) = W ^ (-(1 / 2) : ℝ) := by norm_num
    have hWh : W ^ (-(1 / 2) : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW1 (by norm_num)
    have hWh0 : 0 ≤ W ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg hW0.le _
    have hW1' : W⁻¹ ≤ W ^ (-(1 / 2) : ℝ) := by
      rw [← Real.rpow_neg_one]; exact Real.rpow_le_rpow_of_exponent_le hW1 (by norm_num)
    have hW2' : W ^ (-2 : ℝ) ≤ W ^ (-(1 / 2) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hW1 (by norm_num)
    have hc' : (1 + Q) * W ^ (-(1 / 2) : ℝ) ≤ εc := by
      have := hWc; rw [div_mul_eq_mul_div, div_le_one hεc] at this; exact this
    have e4 : 4 / (W * (splitS p * Real.sqrt κ)) = 4 / (s * Real.sqrt κ) * W⁻¹ := by
      rw [hspl]; field_simp
    have e2 : 2 / (W * splitS p * Real.sqrt κ) ≤ 4 / (s * Real.sqrt κ) * W⁻¹ := by
      rw [hspl, show 4 / (s * Real.sqrt κ) * W⁻¹ = 4 / (W * s * Real.sqrt κ) by field_simp]
      exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
    have hG0 : 0 ≤ G₀ := by positivity
    have a1 : 4 / (s * Real.sqrt κ) * W⁻¹ ≤ 4 / (s * Real.sqrt κ) * W ^ (-(1 / 2) : ℝ) :=
      mul_le_mul_of_nonneg_left hW1' (by positivity)
    have a2 : G₀ * W ^ (-2 : ℝ) ≤ G₀ * W ^ (-(1 / 2) : ℝ) := mul_le_mul_of_nonneg_left hW2' hG0
    rw [hm, e4]
    rw [hQ] at hc'
    constructor
    · linarith only [hc', a1, a2]
    · linarith only [e2, a1, hc', mul_nonneg hG0 hWh0, hWh0]
  have hgl : ∀ e : ℝ, |e| ≤ hE → BlockBand.DeterminantScore.SelectedResolvent.gridLip (splitS p) κ c
      ε₁ * |e| ≤ G₀ * W ^ (-2 : ℝ) := by
    intro e he
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
  -- the bad set
  have hsp0 : 0 < splitS p := BlockBand.Angular.PairCoareaBridge.splitS_pos p
  have hSgm : MeasurableSet Sg := measurableSet_smallBadSet hε₁0 hsp0 hJm I
  have hN₁W : N₁ ≤ 2 * p.W := by omega
  have hN₂W : N₂ ≤ 2 * p.W := by omega
  have hWd : W ≤ d := by rw [hdW]; linarith only [hW1]
  have hd0 : 0 < d := by linarith only [hWd, hW0]
  have hs' : splitS p - s₀ ≤ splitS p := by linarith only [hs₀]
  have hδr : δ ≤ r / 2 := min_le_left _ _
  have hδ1 : δ ≤ 1 / 2 := min_le_right _ _
  -- the index set
  have hmemI : ∀ q ∈ I, q.2.1 ∈ Es ∧ |q.2.2.1| ≤ Lρ ∧ |q.2.2.2| ≤ δ := by
    intro q hq
    rw [hI] at hq
    unfold smallIndex at hq
    simp only [Finset.mem_product, Finset.mem_univ, true_and] at hq
    have hL0 : 0 ≤ Lρ := by positivity
    have hh0 : 0 < d ^ (-1 + β) := Real.rpow_pos_of_pos hd0 _
    exact ⟨hq.1, intervalGrid_mem hL0 hWm2.le hq.2.1, intervalGrid_mem hδ0.le (by positivity) hq.2.2⟩
  have hcertG : ∀ om : SplitState p i, ExteriorGood p i CG ε₁ (1 / 2) κ Es om →
      ∀ e ∈ Es, certErrHat ε₁ p i om e ≤ εc := by
    intro om hom e he
    refine (hom.2.2.2 e he).trans ?_
    unfold certThreshold
    have : 0 ≤ G₀ * W ^ (-2 : ℝ) := by positivity
    linarith only [hthr.1, this]
  -- norm bound and root rectangle of the grid deformations
  have hnormK : ∀ om : SplitState p i, ExteriorGood p i CG ε₁ (1 / 2) κ Es om →
      ∀ q ∈ I, om ∈ smallLabel ε₁ q.1 q.2.1 →
        (Real.sqrt (splitS p))⁻¹ * ‖smallGridK ε₁ q.1 q.2.1 q.2.2.1 om‖ ≤
          Ceth * ((2 * p.W : ℕ) : ℝ) ^ Aeth := by
    intro om hom q hq hl
    obtain ⟨he, hρq, -⟩ := hmemI q hq
    obtain ⟨⟨-, hV⟩, -, ⟨hC, hC', hVn⟩, -⟩ := hom
    have h1 := opNorm_smallGridK_le hV hc0 hC hC' (by positivity) hVn hε₁0 q.1 q.2.1 q.2.2.1 hl
    have he2 : |q.2.1| ≤ 2 := by
      obtain ⟨a1, a2⟩ := hEs _ he; rw [abs_le]; constructor <;> linarith only [a1, a2, hκ0]
    have h2 := smallGridK_scale (H := H) hW1 hc0 hcT hCG.le hA₀0
    have h3 : W ^ Aeth ≤ d ^ Aeth := Real.rpow_le_rpow hW0.le hWd (by positivity)
    have h4 : ‖smallGridK ε₁ q.1 q.2.1 q.2.2.1 om‖ ≤ (T + CG + 2 * T ^ 2 + 3) * d ^ Aeth := by
      have h5 : (T + CG + 2 * T ^ 2 + 3) * W ^ Aeth ≤ (T + CG + 2 * T ^ 2 + 3) * d ^ Aeth :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      linarith only [h1, he2, hρq, h2, h5]
    rw [hspl, hCeth, hTabs, mul_assoc]
    exact mul_le_mul_of_nonneg_left h4 (inv_nonneg.mpr (Real.sqrt_nonneg _))
  have hrectK : ∀ om : SplitState p i, ExteriorGood p i CG ε₁ (1 / 2) κ Es om →
      ∀ q ∈ I, om ∈ smallLabel ε₁ q.1 q.2.1 →
        PairRootRectangle (smallGridK ε₁ q.1 q.2.1 q.2.2.1 om) (splitS p) q.2.2.2 (r / 2) v₀ := by
    intro om hom q hq hl
    obtain ⟨he, -, hμ⟩ := hmemI q hq
    have h := (hrect p hpb i om hom.1.2 ε₁ hthr.2 (splitS p) hs' le_rfl).1 q.2.1 (hEs _ he)
      (hcertG om hom _ he) q.1 q.2.2.1 hl
    exact h.mono (by rw [sub_zero]; linarith only [hμ, hδr])
  refine ⟨Ω₁ ∪ Ω₂, S₁ ∪ S₂ ∪ Sg, (hcs₁.1.union hcs₂.1).union hSgm, ?_, ?_, ?_⟩
  · -- the exterior probability
    refine (measure_union_le _ _).trans ((add_le_add hcs₁.2.1 hcs₂.2.1).trans ?_)
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have : C₁ * w + C₂ * w ≤ (C₁ + C₂ + 3 * KI) * w := by nlinarith only [hw0, hKI0]
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hw0)
  · -- the sections
    intro om hom
    simp only [Set.mem_union, not_or] at hom
    have hg := hgood₂ om hom.2
    have hsec := smallBadSet_section_le (sel := sel) (ε₁ := ε₁) (s := splitS p) (β := β) (εw := εw)
      (Cc := Cc) (Jg := Jg) ν I om (a := ENNReal.ofReal (d ^ (-D')))
      (c := 2 * ENNReal.ofReal (d ^ (-D')))
      (fun q hq hl => (hN₁ p i hN₁W (splitS p) ⟨hspl.ge, hspl.le⟩ (SplitState p i)
        (smallGridK ε₁ q.1 q.2.1 q.2.2.1) (Jg q.1 q.2.1 q.2.2.1)
        (measurable_smallGridK hε₁0 _ _ _) (isHermitian_smallGridK ε₁ _ _ _) (hJm _ _ _)
        (hJH _ _ _) (hJn _ _ _) q.2.2.2 sel).2 om (hnormK om hg q hq hl) (hrectK om hg q hq hl))
      (fun q hq hl => hN₂ p i hN₂W (splitS p) hspl.ge (smallGridK ε₁ q.1 q.2.1 q.2.2.1 om)
        (isHermitian_smallGridK ε₁ _ _ _ om) (hnormK om hg q hq hl) q.2.2.2
        ((hmemI q hq).2.2.trans (by linarith only [hδ1])) (hrectK om hg q hq hl) sel)
    have hIc := smallIndex_card_le (p := p) (i := i) (H := H) hT0 hn hA₀0 hδ0.le hδ1 hβ0.le hcard
    have hgrid : (I.card : ℝ≥0∞) * (ENNReal.ofReal (d ^ (-D')) + 2 * ENNReal.ofReal (d ^ (-D'))) ≤
        ENNReal.ofReal (3 * KI * w) := by
      have hx0 : 0 ≤ d ^ (-D') := Real.rpow_nonneg hd0.le _
      rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_add hx0 (by positivity), ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : d ^ (-D') ≤ W ^ (-D') := Real.rpow_le_rpow_of_nonpos hW0 hWd (by linarith only [hD'0])
      have h2 : W ^ MI * W ^ (-D') = w := by
        rw [hw, ← Real.rpow_add hW0, hD']; ring_nf
      have hIc' : (I.card : ℝ) ≤ KI * W ^ MI := by
        rw [hKI, hTabs, hMI]; exact hIc
      have h3 : (I.card : ℝ) * (d ^ (-D') + 2 * d ^ (-D')) ≤ KI * W ^ MI * (3 * W ^ (-D')) :=
        mul_le_mul hIc' (by linarith only [h1]) (by positivity) (by positivity)
      calc (I.card : ℝ) * (d ^ (-D') + 2 * d ^ (-D')) ≤ KI * W ^ MI * (3 * W ^ (-D')) := h3
        _ = 3 * KI * (W ^ MI * W ^ (-D')) := by ring
        _ = 3 * KI * w := by rw [h2]
    rw [Set.preimage_union, Set.preimage_union]
    refine (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
      (add_le_add (hcs₁.2.2 om hom.1) (hcs₂.2.2 om hom.2))) (hsec.trans hgrid)) |>.trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have : C₁ * w + C₂ * w + 3 * KI * w = (C₁ + C₂ + 3 * KI) * w := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) hw0
  · -- the conclusion off the bad set
    intro x hx1 hx2 α hα hsm
    simp only [Set.mem_union, not_or] at hx1 hx2
    obtain ⟨hGh, hdetall, hrank⟩ := hjoint₁ x hx1.1 hx2.1.1
    obtain ⟨⟨hH, hV⟩, hcrowd, ⟨hC, hC', -⟩, -⟩ := hgood₁ x.1 hx1.1
    have hg := hgood₂ x.1 hx1.2
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
    have hR := hrect p hpb i x.1 hV ε₁ hthr.2 (splitS p) hs' le_rfl
    have hcertE : certErrHat ε₁ p i x.1 E ≤ εc := by
      obtain ⟨e, he, hEe⟩ := hEsg E hEκ
      have h1 := BlockBand.DeterminantScore.SelectedResolvent.certErrHat_le_grid x.1 hH hV hε₁0 hc0
        hκ0 hC hC' hsp0 hEκ (hEs e he)
      have h2 := hgl (E - e) hEe
      have h3 := hg.2.2.2 e he
      unfold certThreshold at h3
      linarith only [h1, h2, h3, hthr.1]
    have hhr : d ^ (-1 + β) ≤ r / 2 := by
      have h1 : d ^ (-1 + β) ≤ W ^ (-1 + β) :=
        Real.rpow_le_rpow_of_nonpos hW0 hWd (by linarith only [hβ1, hββ₀, hβ₀2])
      have h2 : W ^ (-1 + β) ≤ r / 2 := by
        have := hWr; rw [div_mul_eq_mul_div, div_le_one hr] at this; linarith only [this]
      exact h1.trans h2
    have hnot : (x.1, x.2) ∉ Sg := by rw [Prod.mk.eta]; exact hx2.2
    intro lam hlam u hu hAu
    have hmain := smallRho_good_of_not_mem hH hV hGh hc0 hC hC' sel (hdetall α) (hcrowd E hE2) hsm
      hε₁0 hη (hEsg E hEκ) hrE.le le_rfl
      (fun e he l ρg hl => hR.1 e (hEs e he) (hcertG x.1 hg e he) l ρg hl)
      (fun j₀ hsep => hR.2 E hEκ hcertE (hdetall α) hH j₀ hsep) hδr hhr hnot
      (hJ x.1 E hH hV) (fun l e ρg => hJn l e ρg x.1) hv₀ hKq0 hβ0 hεw0 hβε hβh hCc.le
      lam hlam u hu hAu
    refine hmain.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hW0.le _))
    rw [hspl]
    exact le_max_left _ _

end BlockBand.LocalWindow.ProofPartTwo.GUEInputs
