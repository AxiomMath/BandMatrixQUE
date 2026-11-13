module

public import BlockBand.SourceProcess.FullSourceStops.WordValue
public import BlockBand.SourceProcess.FullSourceStops.TagSup
public import BlockBand.Transmission.LengthUniform.ConductanceUniform

/-!
# Moments of the load `L_j = 1 + 2g_j + Σ_a Tr Q_{a,j}`

`lintegral_wordLoad_pow_le`: every moment of the load is bounded uniformly on `bulkInterval κI`,
in the tag births and in `εW ≤ j ≤ TW`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceStops

open MeasureTheory
open BlockBand.Internal.Contracts.Inputs BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.SourceMixing BlockBand.Transmission.LengthUniform
open scoped ENNReal

variable {W : ℕ}

/-- The summands of the load: `1`, `2‖g‖`, `‖Tr Q_a‖`. -/
def loadTerm (b E : ℝ) {nT nI : ℕ} (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (W j : ℕ)
    (ω : GrowthPath W) : Option (Option (Fin nT ⊕ Fin nI)) → ℝ≥0∞
  | none => 1
  | some none => 2 * ‖pathConductance b E W j ω‖ₑ
  | some (some a) => ‖sourceTrace b E k q W j ω a‖ₑ

theorem ofReal_wordLoad_le (b E : ℝ) {nT nI : ℕ} (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ)
    (hq : IsIntervalTests q) (j : ℕ) (ω : GrowthPath W) :
    ENNReal.ofReal (wordLoad b E k q W j ω) ≤ ∑ o, loadTerm b E k q W j ω o := by
  rw [Fintype.sum_option, Fintype.sum_option]
  simp only [loadTerm, wordLoad]
  refine ENNReal.ofReal_add_le.trans ?_
  rw [← add_assoc]
  refine add_le_add (ENNReal.ofReal_add_le.trans (add_le_add (by simp) ?_)) ?_
  · rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    exact mul_le_mul_right (Real.ofReal_le_enorm _) 2
  · rw [ENNReal.ofReal_sum_of_nonneg fun a _ => sourceTrace_nonneg b E k q hq j ω a]
    exact Finset.sum_le_sum fun a _ => Real.ofReal_le_enorm _

theorem measurable_loadTerm (b E : ℝ) {nT nI : ℕ} (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ)
    (j : ℕ) (o : Option (Option (Fin nT ⊕ Fin nI))) :
    Measurable fun ω : GrowthPath W => loadTerm b E k q W j ω o := by
  rcases o with _ | _ | a
  · exact measurable_const
  · exact (measurable_pathConductance b E j).enorm.const_mul _
  · exact (measurable_sourceTrace b E k q j a).enorm

/-- **Load moments**, uniformly on `bulkInterval κI`, in `k` and in `εW ≤ j ≤ TW`. -/
theorem lintegral_wordLoad_pow_le (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI →
    ∀ (nT nI : ℕ) (q : Fin nI → ℝ → ℝ), IsIntervalTests q → ∀ ε T : ℝ, 0 < ε → ε < T →
    ∀ n : ℕ, 1 ≤ n → ∃ (C : ℝ≥0∞) (W₀ : ℕ), C ≠ ⊤ ∧ ∀ W : ℕ, W₀ ≤ W →
      ∀ E ∈ bulkInterval κI, ∀ (k : Fin nT → ℕ) (j : ℕ), ε * W ≤ j → (j : ℝ) ≤ T * W →
        ∫⁻ ω, ENNReal.ofReal (wordLoad b E k q W j ω) ^ n ∂growthPathLaw W b ≤ C := by
  intro b hb0 hb κI hκ nT nI q hq ε T hε hεT n hn
  obtain ⟨Cg, hCg⟩ := lengthUniform_conductance_holds hMT hGA hLp b hb0 hb κI ε n hκ hε
    (by exact_mod_cast hn)
  obtain ⟨Wg, hWg⟩ := hCg T
  obtain ⟨Cs, Ws, hCs⟩ := supMoments_of (tagSupBulk_holds hGA hLp hSR) b hb0 hb κI hκ nT nI q hq
    ε T n hε hεT (by exact_mod_cast hn)
  set c₀ : ℝ≥0∞ :=
    ((Finset.univ : Finset (Option (Option (Fin nT ⊕ Fin nI)))).card : ℝ≥0∞) ^ ((n : ℝ) - 1)
  have hc₀ : c₀ ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith) (ENNReal.natCast_ne_top _)
  set B : Option (Option (Fin nT ⊕ Fin nI)) → ℝ≥0∞ := fun o => match o with
    | none => 1
    | some none => 2 ^ n * ENNReal.ofReal Cg
    | some (some _) => ENNReal.ofReal Cs
  have hB : ∀ o, B o ≠ ⊤ := by
    intro o; rcases o with _ | _ | a
    · exact ENNReal.one_ne_top
    · exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) ENNReal.ofReal_ne_top
    · exact ENNReal.ofReal_ne_top
  refine ⟨c₀ * ∑ o, B o, max Wg Ws, ENNReal.mul_ne_top hc₀
    (ENNReal.sum_ne_top.mpr fun o _ => hB o), fun W hW E hE k j hj1 hj2 => ?_⟩
  have hpt : ∀ ω, ENNReal.ofReal (wordLoad b E k q W j ω) ^ n ≤
      c₀ * ∑ o, loadTerm b E k q W j ω o ^ n := fun ω => by
    have h := ENNReal.rpow_sum_le_const_mul_sum_rpow (s := Finset.univ)
      (f := loadTerm b E k q W j ω) (p := n) (by exact_mod_cast hn)
    simp only [ENNReal.rpow_natCast] at h
    exact (pow_le_pow_left₀ zero_le (ofReal_wordLoad_le b E k q hq j ω) n).trans h
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_const_mul' _ _ hc₀, lintegral_finsetSum _ fun o _ =>
    (measurable_loadTerm b E k q j o).pow_const n]
  refine mul_le_mul_right (Finset.sum_le_sum fun o _ => ?_) c₀
  rcases o with _ | _ | a
  · simp [loadTerm, B]
  · simp only [loadTerm, B, mul_pow]
    rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)]
    refine mul_le_mul_right ?_ _
    have h := hWg W (le_of_max_le_left hW) E hE j hj1 hj2
    simpa only [ENNReal.rpow_natCast] using h
  · simp only [loadTerm, B]
    have h := hCs W (le_of_max_le_right hW) E hE k a
    simp only [ENNReal.rpow_natCast] at h
    refine le_trans (lintegral_mono fun ω => pow_le_pow_left₀ zero_le ?_ n) h
    exact le_iSup₂_of_le (f := fun (j' : ℕ) (_ : ε * W ≤ j' ∧ (j' : ℝ) ≤ T * W) =>
      ‖sourceTrace b E k q W j' ω a‖ₑ) j ⟨hj1, hj2⟩ le_rfl

end BlockBand.SourceProcess.FullSourceStops
