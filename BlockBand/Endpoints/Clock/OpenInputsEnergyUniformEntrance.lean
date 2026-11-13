module

public import BlockBand.Endpoints.Clock.OpenInputsEnergyUniformStep

/-!
# The open-inputs lemma, energy-uniform: the entrance

The zero-entrance lemma (`ZeroEntranceStatement`, proved by `zeroEntrance_of_contracts`) is stated
with constants uniform on the compact parameter set `zeParam κ' b e` (`κ' ≤ b`, `κ' ≤ 1 - 2b`,
`κ' ≤ 4 - e²`): its seed clause gives `C, c_*` and its fixed-`J` clause gives `a, C, W₀` after
`κ'` and `J`, uniformly in `(b, e)`. `OpenInputsProof.entrance_bound` uses `κ' = kappaOf b E`;
here we use `κ' = min (min b (1-2b)) (4-(2-κ)²)`, which satisfies `zeParam κ' b E` for every
`E ∈ bulkInterval κ` (`zeParam_bulk`). The proof is the fixed-energy one with `E` introduced after
the constants (`entrance_bound_unif`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
  BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal NNReal Matrix.Norms.L2Operator

namespace MovingEnergy

open OpenInputsProof CavityMeanProb ZeroEntranceProb

variable {b κ : ℝ}

/-- The compact the zero-entrance lemma parameter `κ' = min(b, 1-2b, 4-(2-κ)²)` covering
`bulkInterval κ`. -/
def kappaBulk (b κ : ℝ) : ℝ := min (min b (1 - 2 * b)) (4 - (2 - κ) ^ 2)

theorem zeParam_bulk (hb0 : 0 < b) (hb1 : b < 1 / 2) (hκ : 0 < κ) (hκ4 : κ < 4) :
    0 < kappaBulk b κ ∧ ∀ E ∈ bulkInterval κ, zeParam (kappaBulk b κ) b E := by
  have h4 := BlockBand.Layers.four_sub_sq_pos hκ hκ4
  refine ⟨lt_min (lt_min hb0 (by linarith)) h4, fun E hE => ⟨?_, ?_, ?_⟩⟩
  · exact (min_le_left _ _).trans (min_le_left _ _)
  · exact (min_le_left _ _).trans (min_le_right _ _)
  · have := BlockBand.Layers.sq_le_of_mem_bulkInterval hE
    exact (min_le_right _ _).trans (by linarith)

/-- **The entrance, uniformly on `bulkInterval κ`** (`OpenInputsProof.entrance_bound`
with `J, ε, a, K, W₀` depending only on `(b, κ, r)`). -/
theorem entrance_bound_unif (hZ : ZeroEntranceStatement) (hb0 : 0 < b) (hb1 : b < 1 / 2)
    (hκ : 0 < κ) (hκ4 : κ < 4) {r : ℝ} (hr : 0 < r) :
    ∃ (J : ℕ) (ε a K : ℝ) (W₀ : ℕ), 0 < ε ∧ 0 < a ∧ 0 ≤ K ∧
      ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
        ∀ D : Matrix (Fin W) (Fin W) ℂ, D.IsHermitian → ‖D‖ ≤ ε →
        ∀ P : ℝ, 2 ≤ P → P ≤ a * W →
          oneEndedLaw W b J {ω | r < chainD0 b E D J ω} ≤
            ENNReal.ofReal ((K * Real.sqrt P / W) ^ P) := by
  obtain ⟨μ, -, hseed, hfix⟩ := hZ
  obtain ⟨hκ', hpar⟩ := zeParam_bulk hb0 hb1 hκ hκ4
  obtain ⟨Cs, cs, hCs, hcs, hseed'⟩ := hseed (kappaBulk b κ) hκ'
  have hlim : Tendsto (fun J : ℕ => Cs * Real.exp (-cs * J)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun J : ℕ => -cs * (J : ℝ)) atTop atBot :=
      tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (neg_lt_zero.mpr hcs)
    have h2 := (Real.tendsto_exp_atBot.comp h1).const_mul Cs
    simpa [Function.comp_def] using h2
  obtain ⟨J, hJ⟩ := (hlim.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < r / 4))).exists
  obtain ⟨a, C, W₀, ha, hC, hfixJ⟩ := hfix (kappaBulk b κ) hκ' J
  refine ⟨J, r / (4 * C), a, 4 * C / r, max W₀ (⌈4 * C / r⌉₊ + 1), by positivity, ha,
    by positivity, ?_⟩
  intro W hW E hEκ D hD hDε P hP2 hPa
  have hW0 : W₀ ≤ W := (le_max_left _ _).trans hW
  have hW1 : ⌈4 * C / r⌉₊ + 1 ≤ W := (le_max_right _ _).trans hW
  have hWr : (0 : ℝ) < W := by
    have : (1 : ℝ) ≤ W := by exact_mod_cast (Nat.succ_le_of_lt (Nat.lt_of_lt_of_le
      (Nat.succ_pos _) hW1))
    linarith
  have hCW : C / W ≤ r / 4 := by
    have h1 : 4 * C / r < W := by
      have := Nat.le_ceil (4 * C / r)
      have h2 : ((⌈4 * C / r⌉₊ + 1 : ℕ) : ℝ) ≤ W := by exact_mod_cast hW1
      push_cast at h2; linarith
    rw [div_lt_iff₀ hr] at h1
    rw [div_le_iff₀ hWr]; linarith
  obtain ⟨hmean, -, hconc, hpert⟩ := hfixJ W hW0 b E (hpar E hEκ)
  obtain ⟨h1, -⟩ := hconc D hD P hP2 hPa
  obtain ⟨h2, -⟩ := hpert (r / (4 * C)) D hD hDε
  have h3 := hseed' b E J (hpar E hEκ)
  have hCε : C * (r / (4 * C)) = r / 4 := by field_simp
  set Z := ∫ ω', zeTrace E D J (boundaryZ b E) ω' ∂oneEndedLaw W b J with hZdef
  have hsub : {ω | r < chainD0 b E D J ω} ⊆
      {ω | r / 4 ≤ ‖zeTrace E D J (boundaryZ b E) ω - Z‖} := by
    intro ω hω
    have hω' : r < chainD0 b E D J ω := hω
    show r / 4 ≤ ‖zeTrace E D J (boundaryZ b E) ω - Z‖
    have e : chainD0 b E D J ω = ‖zeTrace E D J (boundaryZ b E) ω - matchedA E‖ := rfl
    rw [e] at hω'
    set h := zeTrace E D J (boundaryZ b E) ω
    set Z0 := ∫ ω', zeTrace E (0 : Matrix (Fin W) (Fin W) ℂ) J (boundaryZ b E) ω'
      ∂oneEndedLaw W b J
    set G := stieltjesG (μ b E J) (boundaryZ b E)
    have t1 := norm_sub_le_norm_sub_add_norm_sub h Z (matchedA E)
    have t2 := norm_sub_le_norm_sub_add_norm_sub Z Z0 (matchedA E)
    have t3 := norm_sub_le_norm_sub_add_norm_sub Z0 G (matchedA E)
    have hs : Cs * Real.exp (-cs * J) < r / 4 := hJ
    linarith
  refine (measure_mono hsub).trans ?_
  have hB0 : 0 ≤ C * Real.sqrt P / W := by positivity
  have hm : AEStronglyMeasurable (fun ω => zeTrace E D J (boundaryZ b E) ω - Z)
      (oneEndedLaw W b J) :=
    ((measurable_zeTrace E D J (boundaryZ b E)).sub measurable_const).aestronglyMeasurable
  have hN : eLpNorm (fun ω => ‖zeTrace E D J (boundaryZ b E) ω - Z‖) (ENNReal.ofReal P)
      (oneEndedLaw W b J) ≤ ENNReal.ofReal (C * Real.sqrt P / W) := by
    rw [eLpNorm_norm _ hm]; exact h1
  refine (measure_ge_le_of_eLpNorm (by positivity) (by linarith) hB0 hN).trans
    (le_of_eq (congrArg ENNReal.ofReal ?_))
  congr 1
  field_simp

end MovingEnergy

end BlockBand.Endpoints.Clock
