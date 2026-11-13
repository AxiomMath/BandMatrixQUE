module

public import BlockBand.SourceProcess.PhysApprox.B3LayerMeanSep
public import BlockBand.SourceProcess.PhysApprox.B3LayerMeanGram
public import BlockBand.SourceProcess.PhysApprox.B3DecayInStep
public import BlockBand.SourceProcess.PhysApprox.B3ClosedForm
public import BlockBand.SourceProcess.ContractingWords.SepAll
public import BlockBand.SourceProcess.ContractingWords.LayerWord
public import BlockBand.SourceProcess.ClosedSummedProof.ClosedInt
public import BlockBand.SourceProcess.ClosedSummedProof.LayerLetters
public import BlockBand.SourceProcess.FullSourceStops.CurrentCarrier

/-!
# `B3ClosedContrLayerForm` from the padded Cayley chain

**`b3ClosedContrLayerForm_of_cayley : GaussianAbsorptionContract → B3CayleyChain → B3CayleySep →
B3DecayIn.B3ClosedContrLayerForm`**. `B3CayleyChain` and `B3CayleySep` are hypotheses on the
padded Cayley chain and its separators.

The witnesses, at a no-birth step `j`, for `σ, k, l` (measure `closedLaw b W np`):
* the two-port `𝕏 = hermPart(b3ChainXX j)` (Hermitian everywhere; equal to `b3ChainXX j` on the
  alive set, where the chain estimate makes it Hermitian);
* polarization letters patched off the Borel alive set `A^M_j`: with `a = V_je_l`, `w = V_je_k`,
  `L = aw* = L₊ + iL₋`, `L₊ = ¼(u₀u₀* - u₂u₂*)`, `L₋ = ¼(u₁u₁* - u₃u₃*)`, `u_p = a + iᵖw`
  (`polHalf`, `polHalf_add`); `tag 0 ↦ 1_{A^M}L₊`, `tag 1 ↦ 1_{A^M}L₋`, `current ↦ 0`;
  `Tr|L_±| ≤ ‖a‖² + ‖w‖² ≤ 2 Re Tr M_j < 2R` (Loewner, `nuclearNorm_polHalf_le`);
* no injection (`c = 0`, `c₀ = 0`), words `Zs t = [[(tag t, Σ_σ)]]` (degree 1, one contracting
  separator), weights `wt = (1, i)`;
* `Q_j = Tr(LΣ_σ(𝕏_j)) = Σ_t wt_t coreProd` (the separator identity at `j`);
  `Q_{j+1} = Tr(L NΣ_σ(Φ_F𝕏_j)N*) = Σ_t wt_t newProd` (frame transport `V_{j+1} = N*V_j`, the
  growth `𝕏_{j+1} = Φ_F𝕏_j` and the separator identity at `j + 1`; `newWord_zero`);
* integrability of `1_{A_j}Q_{j+1}`: on `A_j`, `|Q_{j+1}| ≤ R‖N‖² ≤ R(1 + ‖N‖⁴)`
  (`‖Σ_σ(Φ_F𝕏)‖ ≤ 1` for Hermitian `𝕏`), and `∫‖N(𝕏, F)‖⁴ dF ≤ C₄` uniformly in Hermitian `𝕏`
  (`fresh_pow_bound`), Tonelli (`integrable_b3_of_fresh`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory ProbabilityTheory Filter Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.SourceProcess.FullSourceStops
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.CompleteSourceGap BlockBand.SourceProcess.ContractingWords
open BlockBand.SourceProcess.ClosedLimit
open BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open scoped ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W np K : ℕ}

/-!
## Polarization letters
-/

section Letters

variable {ι : Type}

/-- `¼(u_pu_p* - u_qu_q*)`, `u_r = a + iʳw`. -/
def polHalf (a w : ι → ℂ) (p q : Fin 4) : Matrix ι ι ℂ :=
  ((1 / 4 : ℝ) : ℂ) • (ClosedSummedProof.rk1 (ClosedSummedProof.polVec a w p) -
    ClosedSummedProof.rk1 (ClosedSummedProof.polVec a w q))

theorem polHalf_add [Fintype ι] (a w : ι → ℂ) :
    polHalf a w 0 2 + Complex.I • polHalf a w 1 3 = vecMulVec a (star w) := by
  have h := ClosedSummedProof.pol_sum a w
  rw [Fin.sum_univ_four] at h
  rw [← h]
  ext x y
  simp only [polHalf, ClosedSummedProof.polCoef, Matrix.add_apply, Matrix.smul_apply,
    Matrix.sub_apply, smul_eq_mul, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
  rw [show ((3 : Fin 4) : ℕ) = 3 from rfl]
  push_cast
  ring_nf
  simp only [Complex.I_sq, Complex.I_pow_three]
  ring

theorem polHalf_isHermitian [Fintype ι] (a w : ι → ℂ) (p q : Fin 4) :
    (polHalf a w p q).IsHermitian :=
  ((ClosedSummedProof.isHermitian_rk1 _).sub (ClosedSummedProof.isHermitian_rk1 _)).smul
    (by simp [IsSelfAdjoint])

theorem trace_rk1_re [Fintype ι] [DecidableEq ι] (u : ι → ℂ) :
    (ClosedSummedProof.rk1 u).trace.re = ∑ x, ‖u x‖ ^ 2 :=
  (nuclearNorm_of_posSemidef (ClosedSummedProof.posSemidef_rk1 u)).symm.trans
    (ClosedSummedProof.nuclearNorm_rk1 u)

/-- **`Tr|¼(u_pu_p* - u_qu_q*)| ≤ ‖a‖² + ‖w‖²`** (Loewner comparison). -/
theorem nuclearNorm_polHalf_le [Fintype ι] [DecidableEq ι] (a w : ι → ℂ) (p q : Fin 4) :
    nuclearNorm (polHalf a w p q) ≤ ∑ x, ‖a x‖ ^ 2 + ∑ x, ‖w x‖ ^ 2 := by
  set up := ClosedSummedProof.polVec a w p
  set uq := ClosedSummedProof.polVec a w q
  set H : Matrix ι ι ℂ :=
    ((1 / 4 : ℝ) : ℂ) • (ClosedSummedProof.rk1 up + ClosedSummedProof.rk1 uq)
  have hh : (0 : ℂ) ≤ ((1 / 2 : ℝ) : ℂ) := Complex.zero_le_real.mpr (by norm_num)
  have h1 : (H - polHalf a w p q).PosSemidef := by
    have e : H - polHalf a w p q = ((1 / 2 : ℝ) : ℂ) • ClosedSummedProof.rk1 uq := by
      ext x y
      simp only [H, polHalf, Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
        up, uq]
      push_cast
      ring
    rw [e]
    exact (ClosedSummedProof.posSemidef_rk1 _).smul hh
  have h2 : (H + polHalf a w p q).PosSemidef := by
    have e : H + polHalf a w p q = ((1 / 2 : ℝ) : ℂ) • ClosedSummedProof.rk1 up := by
      ext x y
      simp only [H, polHalf, Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
        up, uq]
      push_cast
      ring
    rw [e]
    exact (ClosedSummedProof.posSemidef_rk1 _).smul hh
  refine (FullSourceStops.nuclearNorm_le_of_loewner (polHalf_isHermitian a w p q) h1 h2).trans ?_
  rw [Matrix.trace_smul, Matrix.trace_add, smul_eq_mul, Complex.re_ofReal_mul, Complex.add_re,
    trace_rk1_re, trace_rk1_re]
  have hp : ∑ x, ‖up x‖ ^ 2 ≤ 2 * (∑ x, ‖a x‖ ^ 2 + ∑ x, ‖w x‖ ^ 2) :=
    (Finset.sum_le_sum fun x _ => ClosedSummedProof.norm_polVec_sq_le a w p x).trans
      (le_of_eq (by rw [← Finset.mul_sum, Finset.sum_add_distrib]))
  have hq : ∑ x, ‖uq x‖ ^ 2 ≤ 2 * (∑ x, ‖a x‖ ^ 2 + ∑ x, ‖w x‖ ^ 2) :=
    (Finset.sum_le_sum fun x _ => ClosedSummedProof.norm_polVec_sq_le a w q x).trans
      (le_of_eq (by rw [← Finset.mul_sum, Finset.sum_add_distrib]))
  linarith

/-- The polarization letters of `aw*`: `tag 0 ↦ L₊`, `tag 1 ↦ L₋`, `current ↦ 0`. -/
def kLetters (a w : ι → ℂ) : TraceLetter 2 0 → Matrix ι ι ℂ
  | .current => 0
  | .tag t => if t = 0 then polHalf a w 0 2 else polHalf a w 1 3
  | .interval i => i.elim0

theorem kLetters_tag0 (a w : ι → ℂ) : kLetters a w (.tag 0) = polHalf a w 0 2 := by
  simp [kLetters]

theorem kLetters_tag1 (a w : ι → ℂ) : kLetters a w (.tag 1) = polHalf a w 1 3 := by
  simp [kLetters]

theorem kLetters_isHermitian [Fintype ι] (a w : ι → ℂ) (ℓ : TraceLetter 2 0) :
    (kLetters a w ℓ).IsHermitian := by
  cases ℓ with
  | current => exact isHermitian_zero
  | tag t =>
    by_cases ht : t = 0
    · simp only [kLetters, ht, ↓reduceIte]; exact polHalf_isHermitian a w 0 2
    · simp only [kLetters, ht, ↓reduceIte]; exact polHalf_isHermitian a w 1 3
  | interval i => exact i.elim0

theorem kLetters_nuc [Fintype ι] [DecidableEq ι] (a w : ι → ℂ) (ℓ : TraceLetter 2 0) :
    nuclearNorm (kLetters a w ℓ) ≤ ∑ x, ‖a x‖ ^ 2 + ∑ x, ‖w x‖ ^ 2 := by
  cases ℓ with
  | current =>
    simp only [kLetters]
    rw [nuclearNorm_of_posSemidef PosSemidef.zero, trace_zero, Complex.zero_re]
    positivity
  | tag t =>
    by_cases ht : t = 0
    · simp only [kLetters, ht, ↓reduceIte]; exact nuclearNorm_polHalf_le a w 0 2
    · simp only [kLetters, ht, ↓reduceIte]; exact nuclearNorm_polHalf_le a w 1 3
  | interval i => exact i.elim0

theorem measurable_polHalf {α : Type*} [MeasurableSpace α] {a w : α → ι → ℂ}
    (ha : Measurable a) (hw : Measurable w) (p q : Fin 4) :
    Measurable fun y => polHalf (a y) (w y) p q := by
  refine Measurable.of_eval_matrix _ fun x x' => ?_
  have h1 : ∀ z, Measurable fun y => a y z := fun z => (measurable_pi_apply z).comp ha
  have h2 : ∀ z, Measurable fun y => w y z := fun z => (measurable_pi_apply z).comp hw
  simp only [polHalf, ClosedSummedProof.rk1, ClosedSummedProof.polVec, Matrix.smul_apply,
    Matrix.sub_apply, vecMulVec_apply, Pi.add_apply, Pi.smul_apply, Pi.star_apply, smul_eq_mul]
  fun_prop

theorem measurable_kLetters {α : Type*} [MeasurableSpace α] {a w : α → ι → ℂ}
    (ha : Measurable a) (hw : Measurable w) (ℓ : TraceLetter 2 0) :
    Measurable fun y => kLetters (a y) (w y) ℓ := by
  cases ℓ with
  | current => exact measurable_const
  | tag t =>
    by_cases ht : t = 0
    · simp only [kLetters, ht, ↓reduceIte]; exact measurable_polHalf ha hw 0 2
    · simp only [kLetters, ht, ↓reduceIte]; exact measurable_polHalf ha hw 1 3
  | interval i => exact i.elim0

/-- `Σ_t wt_t Tr(L_t T) = Tr(aw*T)` with `wt = (1, i)`. -/
theorem sum_wt_kLetters [Fintype ι] (a w : ι → ℂ) (T : Matrix ι ι ℂ) :
    ∑ t : Fin 2, (![1, Complex.I] : Fin 2 → ℂ) t * (kLetters a w (.tag t) * T).trace =
      (vecMulVec a (star w) * T).trace := by
  rw [Fin.sum_univ_two, kLetters_tag0, kLetters_tag1, ← polHalf_add, Matrix.add_mul,
    Matrix.trace_add, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  simp

end Letters

/-!
## One-letter products
-/

theorem coreProd_single {nT nI : ℕ}
    (A : TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (T : Separator → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (x : TraceLetter nT nI × Separator) :
    coreProd A T [[x]] = (A x.1 * T x.2).trace := by
  simp [coreProd, matWord, letWord]

theorem b3LayerVal_single {nT nI : ℕ} (b E : ℝ)
    (A : TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (F : LayerSample W .oneBlockOnePort)
    (x : TraceLetter nT nI × Separator) :
    B3DecayIn.b3LayerVal b E A (fun _ => 0) XX F [[x]] =
      (A x.1 * transportedSep b E XX x.2 F).trace := by
  simp only [B3DecayIn.b3LayerVal, newProd, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one]
  rw [newWord_zero]
  simp [matWord, letWord, transportedSep]

/-!
## The closed coordinates through the padded state
-/

theorem b3ContrCoord_eq_sep (b E s h : ℝ) (τ m : Fin np → ℝ) (i : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (σ : Fin 4)
    (k l : SrcCol K (Fin np)) (y : ProbedPath W np × ℝ)
    (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (hs : B3SepAt b E s h τ m W i Vs XX y) :
    b3ContrCoord b E s h τ m W i Vs σ k l y =
      (vecMulVec (fun x => b3ClosedFrameAt b E s h τ m W i Vs y x l)
        (star fun x => b3ClosedFrameAt b E s h τ m W i Vs y x k) *
        sepOf b E XX (contrSepOf σ)).trace := by
  rw [ClosedSummedProof.trace_col, b3ContrCoord, hs σ]

theorem b3ContrCoord_succ_eq (b E s h : ℝ) (τ m : Fin np → ℝ) (j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (σ : Fin 4)
    (k l : SrcCol K (Fin np)) (y : ProbedPath W np × ℝ)
    (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (hs : B3SepAt b E s h τ m W (j + 1) Vs (freshTwoPortSchur E XX (freshSample W j y.1.1)) y)
    (hT : b3ClosedFrameAt b E s h τ m W (j + 1) Vs y =
      (freshTransport b E XX (freshSample W j y.1.1))ᴴ * b3ClosedFrameAt b E s h τ m W j Vs y) :
    b3ContrCoord b E s h τ m W (j + 1) Vs σ k l y =
      (vecMulVec (fun x => b3ClosedFrameAt b E s h τ m W j Vs y x l)
        (star fun x => b3ClosedFrameAt b E s h τ m W j Vs y x k) *
        transportedSep b E XX (contrSepOf σ) (freshSample W j y.1.1)).trace := by
  rw [ClosedSummedProof.trace_col, b3ContrCoord, hs σ, hT]
  simp only [transportedSep, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]

/-!
## The layer form
-/

/-- **`B3ClosedContrLayerForm` from the padded Cayley chain and its separators.** -/
theorem b3ClosedContrLayerForm_of_cayley (hGA : GaussianAbsorptionContract) (hC : B3CayleyChain)
    (hS : B3CayleySep) : B3DecayIn.B3ClosedContrLayerForm := by
  intro b E np τ m T s h K Vs hF R
  obtain ⟨hb0, hb, hE1, hE2, -⟩ := hF.1
  set κ := min (2 + E) (2 - E)
  have hκ : 0 < κ := lt_min (by linarith) (by linarith)
  have hEκ : E ∈ bulkInterval κ :=
    ⟨by linarith [min_le_left (2 + E) (2 - E)], by linarith [min_le_right (2 + E) (2 - E)]⟩
  have hη : 0 < etaZ b E :=
    BlockBand.Transmission.PassiveCovariance.etaZ_pos b E (by linarith) hE1 hE2
  obtain ⟨C₄, W₀, hC₄, hfp⟩ := ClosedSummedProof.fresh_pow_bound hGA hb0 hb hκ
  refine ⟨2 * max R 0, 0, by positivity, le_rfl, ?_⟩
  filter_upwards [hC b E np τ m T s h K Vs hF R, hS b E np τ m T s h K Vs hF R,
    hF.2.2.2.2.2, eventually_ge_atTop (max W₀ 1)] with W hCW hSW hVW hWW j hj σ k l
  obtain ⟨hW0, hW⟩ := max_le_iff.1 hWW
  have hsj : closeLen s W ≤ j := (Finset.mem_Ico.1 (Finset.mem_filter.1 hj).1).1
  have hVs : Measurable[growthSigma W (closeLen s W)] (Vs W) := hVW.1
  have hmV : Measurable (Vs W) :=
    hVs.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  have hVinv : ∀ ω, Vs W (extPast W j (pastCoords W j ω)) = Vs W ω :=
    fun ω => growth_fun_extPast hsj hVs ω
  obtain ⟨hXm, hXinv, hXae⟩ := hCW j hj
  have hAlm : MeasurableSet (b3AliveM (np := np) b E s h τ m R W j (Vs W)) :=
    measurableSet_b3AliveM b E s h τ m R W j hmV
  have hAlinv : ∀ y, b3Ext W j y ∈ b3AliveM (np := np) b E s h τ m R W j (Vs W) ↔
      y ∈ b3AliveM (np := np) b E s h τ m R W j (Vs W) :=
    mem_b3AliveM_b3Ext b E s h τ m R hsj le_rfl hVinv
  have hVmeas := measurable_b3ClosedFrameAt b E s h τ m W j hmV (np := np)
  have hVinv' : ∀ y, b3ClosedFrameAt b E s h τ m W j (Vs W) (b3Ext W j y) =
      b3ClosedFrameAt b E s h τ m W j (Vs W) y :=
    fun y => b3ClosedFrameAt_b3Ext b E s h τ m hsj le_rfl hVinv y
  have hcol : ∀ c : SrcCol K (Fin np), Measurable fun y : ProbedPath W np × ℝ =>
      fun x => b3ClosedFrameAt b E s h τ m W j (Vs W) y x c :=
    fun c => Measurable.of_eval fun x => hVmeas.eval_matrix
  have hXXm : Measurable fun y : ProbedPath W np × ℝ => hermPart (b3ChainXX b E s h W j y) := by
    have : Measurable fun y : ProbedPath W np × ℝ =>
        b3ChainXX b E s h W j y + (b3ChainXX b E s h W j y)ᴴ :=
      ClosingAux.measurable_matrix_add hXm (measurable_matrix_conjTranspose' hXm)
    exact ClosingAux.measurable_matrix_cmul measurable_const this
  refine ⟨2, 0, fun y : ProbedPath W np × ℝ => hermPart (b3ChainXX b E s h W j y),
    (b3AliveM (np := np) b E s h τ m R W j (Vs W)).indicator (fun y =>
      kLetters (fun x => b3ClosedFrameAt b E s h τ m W j (Vs W) y x l)
        (fun x => b3ClosedFrameAt b E s h τ m W j (Vs W) y x k)),
    fun _ => 0, fun t => [[(TraceLetter.tag t, contrSepOf σ)]], ![1, Complex.I],
    hXXm, ?_, ?_, ?_, fun y => hermPart_isHermitian _, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_,
    ?_, ?_⟩
  · -- measurability of the letters
    intro ℓ
    have e : (fun y => (b3AliveM (np := np) b E s h τ m R W j (Vs W)).indicator (fun y =>
        kLetters (fun x => b3ClosedFrameAt b E s h τ m W j (Vs W) y x l)
          (fun x => b3ClosedFrameAt b E s h τ m W j (Vs W) y x k)) y ℓ) =
        (b3AliveM (np := np) b E s h τ m R W j (Vs W)).indicator (fun y =>
          kLetters (fun x => b3ClosedFrameAt b E s h τ m W j (Vs W) y x l)
            (fun x => b3ClosedFrameAt b E s h τ m W j (Vs W) y x k) ℓ) := by
      funext y
      by_cases hy : y ∈ b3AliveM (np := np) b E s h τ m R W j (Vs W) <;> simp [hy]
    rw [e]
    exact (measurable_kLetters (hcol l) (hcol k) ℓ).indicator hAlm
  · intro y
    simp only [hXinv]
  · intro y
    by_cases hy : y ∈ b3AliveM (np := np) b E s h τ m R W j (Vs W)
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem ((hAlinv y).2 hy), hVinv']
    · rw [Set.indicator_of_notMem hy,
        Set.indicator_of_notMem (fun h' => hy ((hAlinv y).1 h'))]
  · intro y ℓ
    by_cases hy : y ∈ b3AliveM (np := np) b E s h τ m R W j (Vs W)
    · rw [Set.indicator_of_mem hy]; exact kLetters_isHermitian _ _ ℓ
    · rw [Set.indicator_of_notMem hy]; exact isHermitian_zero
  · intro y ℓ
    by_cases hy : y ∈ b3AliveM (np := np) b E s h τ m R W j (Vs W)
    · rw [Set.indicator_of_mem hy]
      have htr : ((b3ClosedFrameAt b E s h τ m W j (Vs W) y)ᴴ *
          b3ClosedFrameAt b E s h τ m W j (Vs W) y).trace.re < R := hy.2 j hsj le_rfl
      have h1 := ClosedSummedProof.sum_col_sq_le (b3ClosedFrameAt b E s h τ m W j (Vs W) y) l
      have h2 := ClosedSummedProof.sum_col_sq_le (b3ClosedFrameAt b E s h τ m W j (Vs W) y) k
      refine (kLetters_nuc _ _ ℓ).trans ?_
      have : R ≤ max R 0 := le_max_left _ _
      linarith
    · rw [Set.indicator_of_notMem hy, Pi.zero_apply, nuclearNorm_of_posSemidef PosSemidef.zero,
        trace_zero, Complex.zero_re]
      positivity
  · intro ℓ; simp
  · intro t; simp [IsAdmittedProduct]
  · intro t; simp [productDegree]
  · fin_cases σ <;> decide
  · intro t; fin_cases t <;> simp
  · -- integrability of `1_{A_j}Q_{j+1}`
    set μ := closedLaw b W np
    have hfm := aestronglyMeasurable_contr (b := b) (by linarith) hE1 hE2 s h τ m R W j hmV
      (j + 1) σ k l
    set g : ProbedPath W np × ℝ → ℝ := fun y => Real.sqrt R ^ 2 *
      (1 + ‖freshTransport b E (hermPart (b3ChainXX b E s h W j y)) (freshSample W j y.1.1)‖ ^ 4)
      with hg
    have hgi : Integrable (fun y => ‖((g y : ℝ) : ℂ)‖) μ := by
      set Ψ : (PastSample W j × ((Fin np → Fin W → ℂ) × ℝ)) × LayerSample W .oneBlockOnePort →
          ℂ := fun z => ((Real.sqrt R ^ 2 * (1 + ‖freshTransport b E
            (hermPart (b3ChainXX b E s h W j (b3Rebuild W j z.1))) z.2‖ ^ 4) : ℝ) : ℂ)
      have hR' : Measurable fun z : (PastSample W j × ((Fin np → Fin W → ℂ) × ℝ)) ×
          LayerSample W .oneBlockOnePort => b3Rebuild W j z.1 :=
        (measurable_b3Rebuild W j).comp measurable_fst
      have hΨm : Measurable Ψ :=
        Complex.measurable_ofReal.comp (measurable_const.mul (measurable_const.add
          ((FullSource.measurable_freshTransport_comp b E (hXXm.comp hR')
            measurable_snd).norm.pow_const 4)))
      have hcomp : (fun y => Ψ (b3Past W j y, freshSample W j y.1.1)) =
          fun y => ((g y : ℝ) : ℂ) := by
        funext y
        simp only [Ψ, g, b3Rebuild_b3Past, hXinv]
      have hB : ∀ x, ∫⁻ f, ‖Ψ (x, f)‖ₑ ∂freshLaw W b ≤
          ENNReal.ofReal (Real.sqrt R ^ 2 * (1 + C₄)) := by
        intro x
        set X0 := hermPart (b3ChainXX b E s h W j (b3Rebuild W j x))
        obtain ⟨hN1, hN2⟩ := hfp W hW0 E hEκ X0 (hermPart_isHermitian _)
        have hpt : ∀ f, ‖Ψ (x, f)‖ₑ =
            ENNReal.ofReal (Real.sqrt R ^ 2 * (1 + ‖freshTransport b E X0 f‖ ^ 4)) := by
          intro f
          rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        have hInt : Integrable (fun f => Real.sqrt R ^ 2 * (1 + ‖freshTransport b E X0 f‖ ^ 4))
            (freshLaw W b) := ((integrable_const (1 : ℝ)).add hN2).const_mul _
        rw [lintegral_congr hpt, ← ofReal_integral_eq_lintegral_ofReal hInt
          (Eventually.of_forall fun f => by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [integral_const_mul, integral_add (integrable_const _) hN2, integral_const,
          probReal_univ, one_smul]
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have := integrable_b3_of_fresh b j hΨm _ hB
      rw [hcomp] at this
      exact this.norm
    refine hgi.mono' hfm ?_
    filter_upwards [hXae, hSW j hj, ae_closedPath_good (np := np) hb0 hb hE1 hE2 hW] with y hch
      hsep hgood
    by_cases hA : y ∈ b3Alive b E s h τ m R W j (Vs W)
    swap
    · rw [Set.indicator_of_notMem hA, norm_zero]; exact norm_nonneg _
    rw [Set.indicator_of_mem hA]
    obtain ⟨hH, -, hTr, -, -⟩ := hch hA
    obtain ⟨-, hgrow, hs1⟩ := hsep hA
    rw [hgrow] at hs1
    set V := b3ClosedFrameAt b E s h τ m W j (Vs W) y
    set N := freshTransport b E (b3ChainXX b E s h W j y) (freshSample W j y.1.1)
    set M := transportedSep b E (b3ChainXX b E s h W j y) (contrSepOf σ) (freshSample W j y.1.1)
    have hQ : b3ContrCoord b E s h τ m W (j + 1) (Vs W) σ k l y =
        bilinear (fun x => V x k) M (fun x => V x l) := by
      rw [b3ContrCoord_succ_eq b E s h τ m j (Vs W) σ k l y _ hs1 hTr,
        ClosedSummedProof.trace_col, entry_eq_dot]
      rfl
    have hSep : ‖sepOf b E (freshTwoPortSchur E (b3ChainXX b E s h W j y)
        (freshSample W j y.1.1)) (contrSepOf σ)‖ ≤ 1 :=
      norm_sepOf_le b E (freshTwoPortSchur_isHermitian E hH (hgood.1 j)) hη _
    have hM : ‖M‖ ≤ ‖N‖ ^ 2 := norm_transportedSep_le hSep
    have htr : (Vᴴ * V).trace.re < R := hA.2 j hsj le_rfl
    have hvk : vecNorm (fun x => V x k) ≤ Real.sqrt R :=
      Real.sqrt_le_sqrt ((col_sq_le_trace V k).trans htr.le)
    have hvl : vecNorm (fun x => V x l) ≤ Real.sqrt R :=
      Real.sqrt_le_sqrt ((col_sq_le_trace V l).trans htr.le)
    have hgy : ‖((g y : ℝ) : ℂ)‖ = Real.sqrt R ^ 2 * (1 + ‖N‖ ^ 4) := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), hg]
      simp only [hermPart_of_isHermitian hH, N]
    rw [hQ, hgy]
    have hX : ‖N‖ ^ 2 ≤ 1 + ‖N‖ ^ 4 := by nlinarith [sq_nonneg (‖N‖ ^ 2 - 1)]
    have h0 := Transmission.PassiveCovariance.vecNorm_nonneg (fun x => V x k)
    have h0' := Transmission.PassiveCovariance.vecNorm_nonneg (fun x => V x l)
    calc ‖bilinear (fun x => V x k) M (fun x => V x l)‖ ≤
          vecNorm (fun x => V x k) * ‖M‖ * vecNorm (fun x => V x l) :=
          Transmission.PassiveCovariance.norm_bilinear_le _ _ _
      _ ≤ Real.sqrt R * ‖N‖ ^ 2 * Real.sqrt R :=
          mul_le_mul (mul_le_mul hvk hM (norm_nonneg _) (Real.sqrt_nonneg _)) hvl h0'
            (by positivity)
      _ = Real.sqrt R ^ 2 * ‖N‖ ^ 2 := by ring
      _ ≤ Real.sqrt R ^ 2 * (1 + ‖N‖ ^ 4) := mul_le_mul_of_nonneg_left hX (by positivity)
  · -- the a.e. layer form
    filter_upwards [hXae, hSW j hj, b3Alive_ae_eq (by linarith) hE1 hE2 s h τ m R W j (Vs W)]
      with y hch hsep hyA hA
    have hyAl : y ∈ b3AliveM (np := np) b E s h τ m R W j (Vs W) := (Iff.of_eq hyA).mp hA
    obtain ⟨hH, hNS, hTr, -, -⟩ := hch hA
    obtain ⟨hs0, hgrow, hs1⟩ := hsep hA
    rw [hgrow] at hs1
    have hXX := hermPart_of_isHermitian hH
    refine ⟨by rw [hXX]; exact hNS, ?_, ?_⟩
    · rw [b3ContrCoord_succ_eq b E s h τ m j (Vs W) σ k l y _ hs1 hTr]
      simp only [b3LayerVal_single, Set.indicator_of_mem hyAl, hXX]
      rw [sum_wt_kLetters]
    · rw [b3ContrCoord_eq_sep b E s h τ m j (Vs W) σ k l y _ hs0]
      simp only [coreProd_single, Set.indicator_of_mem hyAl, hXX]
      rw [sum_wt_kLetters]

end BlockBand.SourceProcess.PhysApprox.B3
