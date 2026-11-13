module

public import BlockBand.DeterminantScore.PhysicalColumnMass

/-!
# The physical column: whole-row inverse moments under the pair law

`physicalColumn_holds (hC : CoareaContract) : PhysicalColumnStatement`: for fixed `b` and
`2 ≤ q < 3` there is `C` with `E♯‖Rw‖^q ≤ C W^{q/2}` for every outer-measurable unit `w ⊥ v` and
`E♯‖R‖_HS^q ≤ C W^q`, at every `n ≥ 4`, `W`, model, rank, pair, splitting law and frame (every
energy: no energy restriction appears). The constant is
`C = 3 · 2^{q/2} (2/s_b)^{q/2} C_{2,q}`, `s_b = min(1 - 2b, b)`,
`C_{2,q} = gaussianGradientConstant 2 q` (the Gaussian polynomial gradient lemma). The only
hypothesis is `CoareaContract` (fields `pairLaw_measure` and `pairLaw_probability`).

Proof, in order, from results proved in the sibling modules:
* `rowPoly`, `gradient_lower_bound`: `det M` is a real polynomial of degree `≤ 2` in the whole
  row, and `‖∇P‖² ≥ t P²‖Re₀‖²` in whitened coordinates;
* `sector_neighbour`: a whole Hermitian row variation moves `N_-` by at most one, so the restored
  row lies in at most three neighbouring sectors;
* `gue_core`: rotation `w ↦ e₀`, whitening, row split, the Gaussian lemma, inertia dropped in the
  numerator;
* `inner_col`, `inner_hs`: fixed-`θ` column and Hilbert–Schmidt bounds (`‖U_v*w‖ ≤ 1`,
  `‖R‖_HS^q ≤ (d-1)^{q/2-1}Σ_a‖Re_a‖^q`);
* `outerInt_sector_le_one`: integrating the unchanged base restores three pair laws of mass `≤ 1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.PhysicalColumn

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Angular.FiberAngular BlockBand.DeterminantScore.GaussianGradient
open scoped ENNReal NNReal

theorem pairTime_splitS_pos (p : Parameters) : 0 < pairTime p (splitS p) := by
  have hs := BlockBand.Angular.PairCoareaBridge.splitS_pos p
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  unfold pairTime
  exact Real.toNNReal_pos.mpr (by positivity)

theorem inv_pairTime_rpow (p : Parameters) (q : ℝ) :
    ((pairTime p (splitS p) : ℝ)⁻¹) ^ (q / 2) =
      (2 / splitS p) ^ (q / 2) * (p.W : ℝ) ^ (q / 2) := by
  have hs := BlockBand.Angular.PairCoareaBridge.splitS_pos p
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  unfold pairTime
  rw [Real.coe_toNNReal _ (by positivity),
    show (splitS p / (2 * (p.W : ℝ)))⁻¹ = (2 / splitS p) * p.W by field_simp]
  exact Real.mul_rpow (by positivity) hW.le

theorem three_mul_ofReal (x : ℝ) : 3 * ENNReal.ofReal x = ENNReal.ofReal (3 * x) := by
  rw [ENNReal.ofReal_mul (by norm_num)]
  simp

/-- **The physical column lemma** (`PhysicalColumnStatement`), under `CoareaContract`. -/
theorem physicalColumn_holds (hC : CoareaContract) : PhysicalColumnStatement := by
  intro b q hq2 hq3
  set C₀ := gaussianGradientConstant 2 q
  have hC0 : 0 ≤ C₀ := gaussianGradientConstant_nonneg 2 q hq2 hq3
  set sb := min (1 - 2 * b) b
  set A := (2 / sb) ^ (q / 2) * C₀
  refine ⟨3 * 2 ^ (q / 2) * A, ?_⟩
  intro p hb model α i Pω hPω U hU
  have hs : splitS p = sb := by
    unfold splitS Parameters.c; rw [hb]
  have hsp := BlockBand.Angular.PairCoareaBridge.splitS_pos p
  have ht := pairTime_splitS_pos p
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hsb : 0 < sb := hs ▸ hsp
  have hA : 0 ≤ A := mul_nonneg (Real.rpow_nonneg (by positivity) _) hC0
  have hrate : ((pairTime p (splitS p) : ℝ)⁻¹) ^ (q / 2) =
      (2 / sb) ^ (q / 2) * (p.W : ℝ) ^ (q / 2) := by
    rw [inv_pairTime_rpow, hs]
  have h2 : (1 : ℝ) ≤ 2 ^ (q / 2) := Real.one_le_rpow (by norm_num) (by linarith)
  have hWq : 0 ≤ (p.W : ℝ) ^ (q / 2) := Real.rpow_nonneg hW.le _
  refine ⟨fun w hw hwu => ?_, ?_⟩
  · have hB := pairExpect_le hC hPω hU α
      (fun θ G' => ENNReal.ofReal (l2Norm ((outerM U θ G')⁻¹ *ᵥ ((U θ.2.2)ᴴ *ᵥ w θ)) ^ q))
      (ENNReal.ofReal (((pairTime p (splitS p) : ℝ)⁻¹) ^ (q / 2) * C₀))
      (fun θ hR hV hv => inner_col (splitS p) U hR hV ht hq2 hq3
        ((l2Norm_conjTranspose_mulVec_le (hU.2 θ.2.2 hv).1 (w θ)).trans
          (le_of_eq (hwu θ hv).1)) α)
    refine hB.trans ?_
    rw [three_mul_ofReal]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hrate]
    have hAW : 0 ≤ A * (p.W : ℝ) ^ (q / 2) := mul_nonneg hA hWq
    calc 3 * ((2 / sb) ^ (q / 2) * (p.W : ℝ) ^ (q / 2) * C₀) = 3 * (A * (p.W : ℝ) ^ (q / 2)) := by
          simp only [A]; ring
      _ ≤ 3 * (2 ^ (q / 2) * (A * (p.W : ℝ) ^ (q / 2))) := by
          exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hAW h2) (by norm_num)
      _ = 3 * 2 ^ (q / 2) * A * (p.W : ℝ) ^ (q / 2) := by ring
  · have hB := pairExpect_le hC hPω hU α
      (fun θ G' => ENNReal.ofReal (invHS U θ G' ^ q))
      (ENNReal.ofReal (((2 * p.W - 1 : ℕ) : ℝ) ^ (q / 2) *
        ((((pairTime p (splitS p) : ℝ))⁻¹) ^ (q / 2) * C₀)))
      (fun θ hR hV _ => inner_hs (splitS p) U hR hV ht hq2 hq3 α)
    refine hB.trans ?_
    rw [three_mul_ofReal]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hrate]
    set m : ℝ := ((2 * p.W - 1 : ℕ) : ℝ)
    have hm0 : 0 ≤ m := Nat.cast_nonneg _
    have hm : m ≤ 2 * p.W := by
      simp only [m]
      have : 2 * p.W - 1 ≤ 2 * p.W := Nat.sub_le _ _
      exact_mod_cast this
    have hmq : m ^ (q / 2) ≤ 2 ^ (q / 2) * (p.W : ℝ) ^ (q / 2) := by
      rw [← Real.mul_rpow (by norm_num) hW.le]
      exact Real.rpow_le_rpow hm0 hm (by linarith)
    have hWW : (p.W : ℝ) ^ q = (p.W : ℝ) ^ (q / 2) * (p.W : ℝ) ^ (q / 2) := by
      rw [← Real.rpow_add hW]; ring_nf
    have hAW : 0 ≤ A * (p.W : ℝ) ^ (q / 2) := mul_nonneg hA hWq
    rw [hWW]
    calc 3 * (m ^ (q / 2) * ((2 / sb) ^ (q / 2) * (p.W : ℝ) ^ (q / 2) * C₀))
        = 3 * (m ^ (q / 2) * (A * (p.W : ℝ) ^ (q / 2))) := by simp only [A]; ring
      _ ≤ 3 * ((2 ^ (q / 2) * (p.W : ℝ) ^ (q / 2)) * (A * (p.W : ℝ) ^ (q / 2))) := by
          gcongr
      _ = 3 * 2 ^ (q / 2) * A * ((p.W : ℝ) ^ (q / 2) * (p.W : ℝ) ^ (q / 2)) := by ring

end BlockBand.DeterminantScore.PhysicalColumn
