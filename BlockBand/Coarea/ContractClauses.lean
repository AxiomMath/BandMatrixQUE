module

public import BlockBand.Internal.Contracts.CoareaPalm
public import BlockBand.Coarea.ProjectiveFrameDerivative
public import BlockBand.Coarea.GUELaw

/-!
# Clauses of the coarea and fresh eigenpair density statements

The probability, frame and splitting clauses of `CoareaContract`, and the frame clause of
`FreshEigenpairDensityContract`.

* `coarea_pairLaw_probability` = `CoareaContract.pairLaw_probability` (from
  `physicalPairMeasure_isProbability`).
* `coarea_frame_exists` = `CoareaContract.frame_exists` and `freshDensity_frame_exists` =
  `FreshEigenpairDensityContract.frame_exists`: for every finite index type of cardinality
  `m + 1` (`exists_measurable_frame`) the map `v ↦ U_v` takes the first nonvanishing
  coordinate `k` of `v` (measurable `Nat.find` selection), rotates the phase so that `v_k > 0`,
  applies the phase-fixed Householder unitary `phaseFixedHouseholderFrame` and keeps the
  columns other than `k`. It is Borel measurable on all of `ℂ^d` and, for every vector with
  `l2Norm v = 1`, `U_vᴴ U_v = 1` and `U_vᴴ v = 0`. For the pair, `card S = 2W` uses `n ≥ 4`
  (`i ≠ i + 1`).
* `coarea_splitting_exists` = `CoareaContract.splitting_exists`: for `0 < s ≤ min(c,b)`,
  `t = s/(2W)`, the explicit law `Pω = (H ↦ (H_R, C, V)).law` with
  `V_ab = √(1 - t/σ²_ab) H_ab` on the pair block (`σ²_ab = entryVariance`, so
  `σ²_ab ≥ min(c,b)/W > t`). The reassembled law `(Pω ⊗ GUE_S(t)).map assemble` is
  Hermitian-supported and has the physical joint characteristic function (the residual
  variance `σ² - t` plus the GUE variance `t` on every pair coordinate, computed through
  `integral_exp_gueTestPairing`), hence equals `model.law` by
  `physicalGaussianRingLaw_unique`. Measure: the exact physical law; every admissible
  `Parameters` and every exact model; exact finite-dimensional identity, no norm or limit.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Coarea.ContractClauses

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Model.Construction BlockBand.QUE.Fourier
  BlockBand.Coarea BlockBand.Coarea.GUELaw BlockBand.SourceProcess
open scoped ENNReal NNReal ComplexConjugate

section Frame

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Phase-rotated vector `conj(v_k/|v_k|) v`, whose `k`-th coordinate is `|v_k|`. -/
def framePhaseVec (k : ι) (v : ι → ℂ) : ι → ℂ :=
  star (v k / ((‖v k‖ : ℝ) : ℂ)) • v

/-- Householder unitary sending `e_k` to the phase-rotated vector. -/
def frameHouseholder (k : ι) (v : ι → ℂ) : Matrix ι ι ℂ :=
  phaseFixedHouseholderFrame k (framePhaseVec k v)

theorem measurable_frameHouseholder (k : ι) : Measurable (frameHouseholder k) := by
  change Measurable (fun v : ι → ℂ => fun a b => frameHouseholder k v a b)
  rw [measurable_pi_iff]
  intro a
  rw [measurable_pi_iff]
  intro b
  have : (fun v : ι → ℂ => frameHouseholder k v a b) = fun v =>
      -(if a = b then 1 else 0) +
        (((1 + (framePhaseVec k v k).re)⁻¹ : ℝ) : ℂ) *
          phaseFixedHouseholderShift k (framePhaseVec k v) a *
          star (phaseFixedHouseholderShift k (framePhaseVec k v) b) := by
    funext v
    exact phaseFixedHouseholderFrame_apply k a b _
  rw [this]
  simp only [framePhaseVec, phaseFixedHouseholderShift, phaseFixedCoordinateVector,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  fun_prop

omit [Fintype ι] [DecidableEq ι] in
theorem framePhaseVec_apply_self (k : ι) (v : ι → ℂ) (hk : v k ≠ 0) :
    framePhaseVec k v k = ((‖v k‖ : ℝ) : ℂ) := by
  have hn : (‖v k‖ : ℝ) ≠ 0 := norm_ne_zero_iff.2 hk
  have hnC : ((‖v k‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn
  simp only [framePhaseVec, Pi.smul_apply, smul_eq_mul, star_div₀, Complex.star_def,
    Complex.conj_ofReal]
  rw [div_mul_eq_mul_div, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  field_simp
  push_cast
  ring

omit [Fintype ι] [DecidableEq ι] in
theorem norm_framePhaseVec_apply (k : ι) (v : ι → ℂ) (hk : v k ≠ 0) (j : ι) :
    ‖framePhaseVec k v j‖ = ‖v j‖ := by
  have hn : (‖v k‖ : ℝ) ≠ 0 := norm_ne_zero_iff.2 hk
  simp only [framePhaseVec, Pi.smul_apply, smul_eq_mul, norm_mul, norm_star, norm_div,
    Complex.norm_real, norm_norm, div_self hn, one_mul]

omit [DecidableEq ι] in
theorem l2Norm_framePhaseVec (k : ι) (v : ι → ℂ) (hk : v k ≠ 0) :
    l2Norm (framePhaseVec k v) = l2Norm v := by
  simp only [l2Norm, norm_framePhaseVec_apply k v hk]

theorem frameHouseholder_unitary (k : ι) (v : ι → ℂ) (hk : v k ≠ 0) (hv : l2Norm v = 1) :
    (frameHouseholder k v)ᴴ * frameHouseholder k v = 1 := by
  have hw := framePhaseVec_apply_self k v hk
  have hpos : 0 < ‖v k‖ := norm_pos_iff.2 hk
  have := phaseFixedHouseholderFrame_unitary k (WithLp.toLp 2 (framePhaseVec k v))
    (by rw [EuclideanSpace.norm_eq]; simpa [l2Norm, norm_framePhaseVec_apply k v hk] using hv)
    (by simp [hw]) (by simp [hw, hpos])
  exact this

theorem frameHouseholder_mulVec (k : ι) (v : ι → ℂ) (hk : v k ≠ 0) :
    frameHouseholder k v *ᵥ phaseFixedCoordinateVector k = framePhaseVec k v := by
  have hw := framePhaseVec_apply_self k v hk
  have hpos : 0 < ‖v k‖ := norm_pos_iff.2 hk
  apply phaseFixedHouseholderFrame_mulVec_coordinate
  · simp [hw]
  · simp [hw]; linarith

variable {m : ℕ}

/-- The columns other than `k`, indexed by `Fin m` through `succAbove`. -/
def frameColumn (e : ι ≃ Fin (m + 1)) (k : ι) (j : Fin m) : ι :=
  e.symm ((e k).succAbove j)

omit [Fintype ι] [DecidableEq ι] in
theorem frameColumn_injective (e : ι ≃ Fin (m + 1)) (k : ι) :
    Function.Injective (frameColumn e k) := by
  intro a b h
  exact Fin.succAbove_right_injective (e.symm.injective h)

omit [Fintype ι] [DecidableEq ι] in
theorem frameColumn_ne (e : ι ≃ Fin (m + 1)) (k : ι) (j : Fin m) : frameColumn e k j ≠ k := by
  intro h
  have h2 : e (frameColumn e k j) = (e k).succAbove j := by
    simp [frameColumn]
  rw [h] at h2
  exact Fin.succAbove_ne _ _ h2.symm

/-- The frame of `v^⊥` attached to the coordinate `k`. -/
def frameAt (e : ι ≃ Fin (m + 1)) (k : ι) (v : ι → ℂ) : Matrix ι (Fin m) ℂ :=
  (frameHouseholder k v).submatrix id (frameColumn e k)

theorem measurable_frameAt (e : ι ≃ Fin (m + 1)) (k : ι) : Measurable (frameAt e k) := by
  have h := measurable_frameHouseholder (ι := ι) k
  change Measurable (fun v : ι → ℂ => fun a b => frameAt e k v a b)
  rw [measurable_pi_iff]
  intro a
  rw [measurable_pi_iff]
  intro b
  have ha : Measurable (fun v : ι → ℂ => frameHouseholder k v a) := measurable_pi_apply a |>.comp h
  exact measurable_pi_apply (frameColumn e k b) |>.comp ha

theorem frameAt_orthonormal (e : ι ≃ Fin (m + 1)) (k : ι) (v : ι → ℂ) (hk : v k ≠ 0)
    (hv : l2Norm v = 1) : (frameAt e k v)ᴴ * frameAt e k v = 1 := by
  rw [frameAt, conjTranspose_submatrix, ← submatrix_mul _ _ _ _ _ Function.bijective_id,
    frameHouseholder_unitary k v hk hv, submatrix_one _ (frameColumn_injective e k)]

theorem frameAt_orthogonal (e : ι ≃ Fin (m + 1)) (k : ι) (v : ι → ℂ) (hk : v k ≠ 0)
    (hv : l2Norm v = 1) : (frameAt e k v)ᴴ *ᵥ v = 0 := by
  have hU := frameHouseholder_unitary k v hk hv
  have hH := frameHouseholder_mulVec k v hk
  set c : ℂ := star (v k / ((‖v k‖ : ℝ) : ℂ)) with hc
  have hn : (‖v k‖ : ℝ) ≠ 0 := norm_ne_zero_iff.2 hk
  have hc0 : c ≠ 0 := by
    rw [hc]
    simp [hk, hn]
  have hw : framePhaseVec k v = c • v := rfl
  have hvw : v = c⁻¹ • framePhaseVec k v := by
    rw [hw, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hstar : (frameHouseholder k v)ᴴ *ᵥ v = c⁻¹ • phaseFixedCoordinateVector k := by
    have h1 : (frameHouseholder k v)ᴴ *ᵥ framePhaseVec k v = phaseFixedCoordinateVector k := by
      rw [← hH, Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]
    calc (frameHouseholder k v)ᴴ *ᵥ v
        = (frameHouseholder k v)ᴴ *ᵥ (c⁻¹ • framePhaseVec k v) := congrArg _ hvw
      _ = c⁻¹ • phaseFixedCoordinateVector k := by rw [Matrix.mulVec_smul, h1]
  funext j
  have hj := congrFun hstar (frameColumn e k j)
  simp only [Pi.smul_apply, smul_eq_mul, phaseFixedCoordinateVector,
    Pi.single_eq_of_ne (frameColumn_ne e k j), mul_zero] at hj
  rw [frameAt, conjTranspose_submatrix]
  simpa [Matrix.mulVec, dotProduct, Matrix.submatrix] using hj

/-- Selection predicate: `n` is a coordinate index at which `v` does not vanish
(or the fallback `n = m + 1`). -/
def frameSelect (e : ι ≃ Fin (m + 1)) (n : ℕ) (v : ι → ℂ) : Prop :=
  if h : n < m + 1 then v (e.symm ⟨n, h⟩) ≠ 0 else True

omit [Fintype ι] [DecidableEq ι] in
theorem frameSelect_exists (e : ι ≃ Fin (m + 1)) (v : ι → ℂ) : ∃ n, frameSelect e n v :=
  ⟨m + 1, by simp [frameSelect]⟩

/-- The frame candidate attached to the selection index `n`. -/
def frameCandidate (e : ι ≃ Fin (m + 1)) (n : ℕ) (v : ι → ℂ) : Matrix ι (Fin m) ℂ :=
  if h : n < m + 1 then frameAt e (e.symm ⟨n, h⟩) v else 0

open Classical in
/-- A measurable orthonormal frame of `v^⊥`: Householder frame at the first
nonvanishing coordinate of `v`. -/
def measurableFrame (e : ι ≃ Fin (m + 1)) (v : ι → ℂ) : Matrix ι (Fin m) ℂ :=
  frameCandidate e (Nat.find (frameSelect_exists e v)) v

open Classical in
theorem measurable_measurableFrame (e : ι ≃ Fin (m + 1)) : Measurable (measurableFrame e) := by
  refine Measurable.find (p := fun n v => frameSelect e n v) (f := frameCandidate e) ?_ ?_
    (frameSelect_exists e)
  · intro n
    unfold frameCandidate
    split_ifs with h
    · exact measurable_frameAt e _
    · exact measurable_const
  · intro n
    unfold frameSelect
    split_ifs with h
    · exact (measurableSet_singleton (0 : ℂ)).compl.preimage (measurable_pi_apply _)
    · exact MeasurableSet.univ

omit [DecidableEq ι] in
theorem exists_ne_zero_of_l2Norm (v : ι → ℂ) (hv : l2Norm v = 1) : ∃ k, v k ≠ 0 := by
  by_contra h
  push Not at h
  simp [l2Norm, h] at hv

open Classical in
theorem measurableFrame_spec (e : ι ≃ Fin (m + 1)) (v : ι → ℂ) (hv : l2Norm v = 1) :
    (measurableFrame e v)ᴴ * measurableFrame e v = 1 ∧ (measurableFrame e v)ᴴ *ᵥ v = 0 := by
  obtain ⟨k, hk⟩ := exists_ne_zero_of_l2Norm v hv
  have hle : Nat.find (frameSelect_exists e v) ≤ (e k : ℕ) :=
    Nat.find_min' _ (by simp [frameSelect, hk])
  have hlt : Nat.find (frameSelect_exists e v) < m + 1 := lt_of_le_of_lt hle (e k).isLt
  have hspec := Nat.find_spec (frameSelect_exists e v)
  have hk' : v (e.symm ⟨Nat.find (frameSelect_exists e v), hlt⟩) ≠ 0 := by
    unfold frameSelect at hspec
    split_ifs at hspec with hc
    · exact hspec
    · exact absurd hlt hc
  have hF : measurableFrame e v =
      frameAt e (e.symm ⟨Nat.find (frameSelect_exists e v), hlt⟩) v := by
    simp only [measurableFrame, frameCandidate, hlt, ↓reduceDIte]
  rw [hF]
  exact ⟨frameAt_orthonormal e _ v hk' hv, frameAt_orthogonal e _ v hk' hv⟩

/-- Generic frame existence: any finite index type of cardinality `m + 1`. -/
theorem exists_measurable_frame (h : Fintype.card ι = m + 1) :
    ∃ U : (ι → ℂ) → Matrix ι (Fin m) ℂ, Measurable U ∧ ∀ v : ι → ℂ, l2Norm v = 1 →
      (U v)ᴴ * U v = 1 ∧ (U v)ᴴ *ᵥ v = 0 :=
  let e := Fintype.equivFinOfCardEq h
  ⟨measurableFrame e, measurable_measurableFrame e, measurableFrame_spec e⟩

end Frame

/-!
## Frames of the exposed pair and of the fresh block
-/

theorem pair_ne_succ (p : Parameters) (i : ZMod p.n) : i ≠ i + 1 := by
  intro h
  have h1 : ((1 : ℕ) : ZMod p.n) = 0 := by
    have : (1 : ZMod p.n) = 0 := by
      have := congrArg (fun x => x - i) h
      simpa using this.symm
    exact_mod_cast this
  rw [ZMod.natCast_eq_zero_iff] at h1
  have := Nat.le_of_dvd one_pos h1
  have := p.n_ge_four
  omega

theorem card_pairSite (p : Parameters) (i : ZMod p.n) :
    Fintype.card (PairSite p i) = 2 * p.W := by
  classical
  rw [Fintype.card_subtype]
  have hfilter : (Finset.univ.filter fun x : p.Site => x.1 = i ∨ x.1 = i + 1) =
      ({i, i + 1} : Finset (ZMod p.n)) ×ˢ (Finset.univ : Finset (Fin p.W)) := by
    ext x
    simp
  rw [hfilter, Finset.card_product, Finset.card_pair (pair_ne_succ p i), Finset.card_univ,
    Fintype.card_fin]

/-- `CoareaContract.frame_exists`. -/
theorem coarea_frame_exists : ∀ (p : Parameters) (i : ZMod p.n),
    ∃ U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ, IsPairFrame p i U := by
  intro p i
  have h : Fintype.card (PairSite p i) = (2 * p.W - 1) + 1 := by
    rw [card_pairSite]
    have := p.W_pos
    omega
  exact exists_measurable_frame h

/-- `FreshEigenpairDensityContract.frame_exists`. -/
theorem freshDensity_frame_exists : ∀ (N : ℕ), 0 < N →
    ∃ U : (Fin N → ℂ) → Matrix (Fin N) (Fin (N - 1)) ℂ, IsFreshFrame U := by
  intro N hN
  have h : Fintype.card (Fin N) = (N - 1) + 1 := by
    rw [Fintype.card_fin]
    omega
  exact exists_measurable_frame h

/-- `CoareaContract.pairLaw_probability`. -/
theorem coarea_pairLaw_probability : ∀ (p : Parameters) (model : p.GaussianRingModel)
    (α : Fin p.N) (i : ZMod p.n), IsProbabilityMeasure (physicalPairMeasure p model α i) :=
  fun p model α i => physicalPairMeasure_isProbability p model α i

section GUEChar

variable {ι : Type*} [Fintype ι]

/-- Diagonal/upper/lower splitting of a double sum along an injective key. -/
theorem sum_sum_split_key [DecidableEq ι] (κ : ι → ℕ) (hκ : Function.Injective κ)
    (F : ι → ι → ℝ) :
    ∑ a, ∑ b, F a b = ∑ a, F a a + ∑ a, ∑ b, if κ a < κ b then F a b + F b a else 0 := by
  have hpt : ∀ a b, F a b = (if a = b then F a b else 0) + (if κ a < κ b then F a b else 0) +
      (if κ b < κ a then F a b else 0) := by
    intro a b
    by_cases hab : a = b
    · subst hab; simp
    · have hne : κ a ≠ κ b := fun h => hab (hκ h)
      rcases lt_or_gt_of_ne hne with h | h
      · simp [hab, h, not_lt.2 h.le]
      · simp [hab, h, not_lt.2 h.le]
  calc ∑ a, ∑ b, F a b
      = ∑ a, ∑ b, ((if a = b then F a b else 0) + (if κ a < κ b then F a b else 0) +
          (if κ b < κ a then F a b else 0)) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hpt a b
    _ = ∑ a, F a a + (∑ a, ∑ b, (if κ a < κ b then F a b else 0) +
          ∑ a, ∑ b, (if κ b < κ a then F a b else 0)) := by
        simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
        ring
    _ = ∑ a, F a a + (∑ a, ∑ b, (if κ a < κ b then F a b else 0) +
          ∑ a, ∑ b, (if κ a < κ b then F b a else 0)) := by
        congr 2
        exact Finset.sum_comm
    _ = ∑ a, F a a + ∑ a, ∑ b, if κ a < κ b then F a b + F b a else 0 := by
        rw [← Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun b _ => ?_
        split_ifs <;> ring

theorem gueScale_sq (t : ℝ≥0) : gueScale t ^ 2 = (t : ℝ) / 4 := by
  rw [gueScale, div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by norm_num)]
  ring

omit [Fintype ι] in
theorem gueSample_circ_re (t : ℝ≥0) (r : RealIndex ι → ℝ) (a b : ι) :
    (gueSample t (circularBrownianCoordinates r) a b).re =
      gueScale t * (r ((a, b), 0) + r ((b, a), 0)) := by
  simp [gueSample, circularBrownianCoordinates, gueScale, Complex.div_ofReal_re,
    Complex.div_ofReal_im]
  ring

omit [Fintype ι] in
theorem gueSample_circ_im (t : ℝ≥0) (r : RealIndex ι → ℝ) (a b : ι) :
    (gueSample t (circularBrownianCoordinates r) a b).im =
      gueScale t * (r ((a, b), 1) - r ((b, a), 1)) := by
  simp [gueSample, circularBrownianCoordinates, gueScale, Complex.div_ofReal_re,
    Complex.div_ofReal_im]
  ring

/-- The real linear functional of the GUE matrix tested in the characteristic function. -/
def gueTestPairing (κ : ι → ℕ) (D : ι → ℝ) (U V : ι → ι → ℝ) (G : Matrix ι ι ℂ) : ℝ :=
  ∑ a, D a * (G a a).re +
    ∑ a, ∑ b, if κ a < κ b then U a b * (G a b).re + V a b * (G a b).im else 0

/-- The variance of `gueTestPairing` under `GUE_ι(t)`. -/
def gueTestVariance (κ : ι → ℕ) (t : ℝ≥0) (D : ι → ℝ) (U V : ι → ι → ℝ) : ℝ :=
  (t : ℝ) * ∑ a, D a ^ 2 +
    ∑ a, ∑ b, if κ a < κ b then (t : ℝ) / 2 * (U a b ^ 2 + V a b ^ 2) else 0

/-- Coefficients of `gueTestPairing ∘ gueSample t ∘ circ` on the real circular inputs. -/
def gueTestCoef [DecidableEq ι] (κ : ι → ℕ) (t : ℝ≥0) (D : ι → ℝ) (U V : ι → ι → ℝ)
    (k : RealIndex ι) : ℝ :=
  if k.2 = 0 then
    (if k.1.1 = k.1.2 then 2 * gueScale t * D k.1.1
      else if κ k.1.1 < κ k.1.2 then gueScale t * U k.1.1 k.1.2
      else gueScale t * U k.1.2 k.1.1)
  else
    (if k.1.1 = k.1.2 then 0
      else if κ k.1.1 < κ k.1.2 then gueScale t * V k.1.1 k.1.2
      else -(gueScale t * V k.1.2 k.1.1))

theorem sum_realIndex (f : RealIndex ι → ℝ) :
    ∑ k, f k = ∑ a, ∑ b, (f ((a, b), 0) + f ((a, b), 1)) := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp [Fin.sum_univ_two]

theorem gueTestPairing_gueSample [DecidableEq ι] (κ : ι → ℕ) (hκ : Function.Injective κ)
    (t : ℝ≥0) (D : ι → ℝ) (U V : ι → ι → ℝ) (r : RealIndex ι → ℝ) :
    gueTestPairing κ D U V (gueSample t (circularBrownianCoordinates r)) =
      ∑ k, gueTestCoef κ t D U V k * r k := by
  rw [sum_realIndex, sum_sum_split_key κ hκ]
  unfold gueTestPairing
  simp only [gueSample_circ_re, gueSample_circ_im]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    simp [gueTestCoef]
    ring
  · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases h : κ a < κ b
    · have hab : a ≠ b := fun e => by subst e; exact lt_irrefl _ h
      have hba : b ≠ a := Ne.symm hab
      have h' : ¬ κ b < κ a := not_lt.2 h.le
      simp [gueTestCoef, h, h', hab, hba]
      ring
    · simp [h]

theorem gueTestCoef_sq [DecidableEq ι] (κ : ι → ℕ) (hκ : Function.Injective κ)
    (t : ℝ≥0) (D : ι → ℝ) (U V : ι → ι → ℝ) :
    ∑ k, ((1 : ℝ≥0) : ℝ) * gueTestCoef κ t D U V k ^ 2 = gueTestVariance κ t D U V := by
  rw [sum_realIndex, sum_sum_split_key κ hκ]
  unfold gueTestVariance
  have hs := gueScale_sq t
  congr 1
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [gueTestCoef]
    simp
    nlinarith [hs]
  · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases h : κ a < κ b
    · have hab : a ≠ b := fun e => by subst e; exact lt_irrefl _ h
      have hba : b ≠ a := Ne.symm hab
      have h' : ¬ κ b < κ a := not_lt.2 h.le
      simp [gueTestCoef, h, h', hab, hba]
      nlinarith [hs]
    · simp [h]

/-- Characteristic function of `GUE_ι(t)` against the coordinate pairing. -/
theorem integral_exp_gueTestPairing (κ : ι → ℕ) (hκ : Function.Injective κ)
    (t : ℝ≥0) (D : ι → ℝ) (U V : ι → ι → ℝ) :
    ∫ G, Complex.exp (Complex.I * (gueTestPairing κ D U V G : ℂ)) ∂gueMeasure ι t =
      Complex.exp (-(gueTestVariance κ t D U V : ℂ) / 2) := by
  classical
  unfold gueMeasure commonCircularIncrementLaw
  rw [Measure.map_map (measurable_gueSample t) measurable_circularBrownianCoordinates]
  rw [integral_map ((measurable_gueSample t).comp
    measurable_circularBrownianCoordinates).aemeasurable (by
      unfold gueTestPairing
      fun_prop)]
  simp only [Function.comp_apply, gueTestPairing_gueSample κ hκ]
  rw [BlockBand.Parameters.gaussianProduct_characteristic, gueTestCoef_sq κ hκ]

end GUEChar

section Split

variable (p : Parameters) (i : ZMod p.n)

/-- Residual scaling factor `√(1 - t/σ²_ab)` on the exposed pair block, `t = s/(2W)`. -/
def pairResidualFactor (s : ℝ) (a b : PairSite p i) : ℝ :=
  Real.sqrt (1 - (pairTime p s : ℝ) / p.entryVariance a.1 b.1)

/-- `H ↦ (H_R, C, V)` with `V_ab = √(1 - t/σ²_ab) H_ab` on the pair block. -/
def residualSplitMap (s : ℝ) (H : p.SiteMatrix) : SplitState p i :=
  (exteriorBlock p i H, couplingBlock p i H,
    fun a b => (pairResidualFactor p i s a b : ℂ) * pairBlock p i H a b)

/-- The explicit splitting law `Pω`: image of the physical law under `residualSplitMap`. -/
def residualSplitLaw (model : p.GaussianRingModel) (s : ℝ) : Measure (SplitState p i) :=
  (model.law : Measure p.SiteMatrix).map (residualSplitMap p i s)

/-- The residual factor extended by `1` off the pair block. -/
def siteResidualFactor (s : ℝ) (x y : p.Site) : ℝ :=
  if h : (x.1 = i ∨ x.1 = i + 1) ∧ (y.1 = i ∨ y.1 = i + 1) then
    pairResidualFactor p i s ⟨x, h.1⟩ ⟨y, h.2⟩ else 1

theorem assemble_residualSplitMap (s : ℝ) (H : p.SiteMatrix) (hH : H.IsHermitian) :
    assemble p i (residualSplitMap p i s H) 0 =
      Matrix.of fun x y => (siteResidualFactor p i s x y : ℂ) * H x y := by
  ext x y
  unfold assemble residualSplitMap siteResidualFactor
  by_cases hx : x.1 = i ∨ x.1 = i + 1 <;> by_cases hy : y.1 = i ∨ y.1 = i + 1
  · simp [hx, hy, pairBlock]
  · simp only [hx, hy, dite_true, dite_false, couplingBlock, and_false, Matrix.of_apply,
      Complex.ofReal_one, one_mul]
    exact hH.apply x y
  · simp [hx, hy, couplingBlock]
  · simp [hx, hy, exteriorBlock]

theorem assemble_eq_add (ω : SplitState p i) (G : PairMatrix p i) :
    assemble p i ω G = assemble p i ω 0 + assemble p i 0 G := by
  ext x y
  rw [Matrix.add_apply]
  unfold assemble
  by_cases hx : x.1 = i ∨ x.1 = i + 1 <;> by_cases hy : y.1 = i ∨ y.1 = i + 1 <;>
    simp [hx, hy]

theorem coordinatePairing_add (d : p.Site → ℝ) (u v : p.Site → p.Site → ℝ)
    (H K : p.SiteMatrix) :
    p.coordinatePairing d u v (H + K) =
      p.coordinatePairing d u v H + p.coordinatePairing d u v K := by
  unfold Parameters.coordinatePairing
  have h1 : ∀ x, d x * ((H + K) x x).re = d x * (H x x).re + d x * (K x x).re := by
    intro x; simp; ring
  have h2 : ∀ x y, u x y * ((H + K) x y).re + v x y * ((H + K) x y).im =
      (u x y * (H x y).re + v x y * (H x y).im) + (u x y * (K x y).re + v x y * (K x y).im) := by
    intro x y; simp; ring
  simp only [h1, h2, Finset.sum_add_distrib]
  ring

theorem coordinatePairing_scale (d : p.Site → ℝ) (u v : p.Site → p.Site → ℝ)
    (m : p.Site → p.Site → ℝ) (H : p.SiteMatrix) :
    p.coordinatePairing d u v (Matrix.of fun x y => (m x y : ℂ) * H x y) =
      p.coordinatePairing (fun x => d x * m x x) (fun x y => u x y * m x y)
        (fun x y => v x y * m x y) H := by
  unfold Parameters.coordinatePairing
  simp only [Matrix.of_apply, Complex.re_ofReal_mul, Complex.im_ofReal_mul]
  congr 1
  · exact Finset.sum_congr rfl fun x _ => by ring
  · exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

theorem sum_eq_sum_pairSite (f : p.Site → ℝ) (hf : ∀ x, ¬ (x.1 = i ∨ x.1 = i + 1) → f x = 0) :
    ∑ x, f x = ∑ a : PairSite p i, f a.1 := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun x : p.Site => x.1 = i ∨ x.1 = i + 1) f]
  have h0 : ∑ a : {x : p.Site // ¬ (x.1 = i ∨ x.1 = i + 1)}, f a.1 = 0 :=
    Finset.sum_eq_zero fun a _ => hf a.1 a.2
  rw [h0, add_zero]

theorem assemble_zero_apply (G : PairMatrix p i) (x y : p.Site) :
    assemble p i 0 G x y =
      if hx : x.1 = i ∨ x.1 = i + 1 then
        if hy : y.1 = i ∨ y.1 = i + 1 then G ⟨x, hx⟩ ⟨y, hy⟩ else 0
      else 0 := by
  unfold assemble
  by_cases hx : x.1 = i ∨ x.1 = i + 1 <;> by_cases hy : y.1 = i ∨ y.1 = i + 1 <;>
    simp [hx, hy]

/-- The physical pairing of the embedded pair matrix is the GUE test pairing. -/
theorem coordinatePairing_assemble_zero (d : p.Site → ℝ) (u v : p.Site → p.Site → ℝ)
    (G : PairMatrix p i) :
    p.coordinatePairing d u v (assemble p i 0 G) =
      gueTestPairing (fun a : PairSite p i => p.siteIndex a.1) (fun a => d a.1)
        (fun a b => u a.1 b.1) (fun a b => v a.1 b.1) G := by
  unfold Parameters.coordinatePairing gueTestPairing
  congr 1
  · rw [sum_eq_sum_pairSite p i]
    · refine Finset.sum_congr rfl fun a _ => ?_
      simp [assemble_zero_apply, a.2]
    · intro x hx
      simp [assemble_zero_apply, hx]
  · simp only [Finset.sum_filter]
    rw [sum_eq_sum_pairSite p i]
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [sum_eq_sum_pairSite p i]
      · refine Finset.sum_congr rfl fun b _ => ?_
        simp [assemble_zero_apply, a.2, b.2]
      · intro y hy
        simp [assemble_zero_apply, hy]
    · intro x hx
      refine Finset.sum_eq_zero fun y _ => ?_
      simp [assemble_zero_apply, hx]

theorem entryVariance_pair_ge (x y : p.Site) (hx : x.1 = i ∨ x.1 = i + 1)
    (hy : y.1 = i ∨ y.1 = i + 1) : min p.c p.b / p.W ≤ p.entryVariance x y := by
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  unfold Parameters.entryVariance
  split_ifs with h1 h2
  · exact div_le_div_of_nonneg_right (min_le_left _ _) hW.le
  · exact div_le_div_of_nonneg_right (min_le_right _ _) hW.le
  · exfalso
    apply h2
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact absurd (hy.trans hx.symm) h1
    · left; rw [hx, hy]
    · right; rw [hx, hy]; ring
    · exact absurd (hy.trans hx.symm) h1

theorem pairTime_lt (s : ℝ) (hs : 0 < s) (hsc : s ≤ min p.c p.b) :
    (pairTime p s : ℝ) < min p.c p.b / p.W := by
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hmin : 0 < min p.c p.b := lt_min p.c_pos p.b_pos
  unfold pairTime
  rw [Real.coe_toNNReal _ (by positivity)]
  rw [div_lt_div_iff₀ (by positivity) hW]
  nlinarith

theorem siteResidualFactor_sq (s : ℝ) (hs : 0 < s) (hsc : s ≤ min p.c p.b) (x y : p.Site) :
    p.entryVariance x y * siteResidualFactor p i s x y ^ 2 +
      (if (x.1 = i ∨ x.1 = i + 1) ∧ (y.1 = i ∨ y.1 = i + 1) then (pairTime p s : ℝ) else 0) =
      p.entryVariance x y := by
  unfold siteResidualFactor
  split_ifs with h
  · have hσ := entryVariance_pair_ge p i x y h.1 h.2
    have ht := pairTime_lt p s hs hsc
    have hmin : 0 < min p.c p.b / p.W := by
      have := lt_min p.c_pos p.b_pos
      have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
      positivity
    have hσpos : 0 < p.entryVariance x y := lt_of_lt_of_le hmin hσ
    have hle : (pairTime p s : ℝ) / p.entryVariance x y ≤ 1 := by
      rw [div_le_one hσpos]; linarith
    unfold pairResidualFactor
    rw [Real.sq_sqrt (by linarith)]
    field_simp
    ring
  · ring

/-- The physical variance splits into the residual variance and the GUE variance. -/
theorem coordinateVariance_split (s : ℝ) (hs : 0 < s) (hsc : s ≤ min p.c p.b)
    (d : p.Site → ℝ) (u v : p.Site → p.Site → ℝ) :
    p.coordinateVariance d u v =
      p.coordinateVariance (fun x => d x * siteResidualFactor p i s x x)
          (fun x y => u x y * siteResidualFactor p i s x y)
          (fun x y => v x y * siteResidualFactor p i s x y) +
        gueTestVariance (fun a : PairSite p i => p.siteIndex a.1) (pairTime p s)
          (fun a => d a.1) (fun a b => u a.1 b.1) (fun a b => v a.1 b.1) := by
  set t : ℝ := (pairTime p s : ℝ)
  set m := siteResidualFactor p i s
  have hkey := siteResidualFactor_sq p i s hs hsc
  have hg1 : (t * ∑ a : PairSite p i, d a.1 ^ 2) =
      ∑ x : p.Site, (if (x.1 = i ∨ x.1 = i + 1) ∧ (x.1 = i ∨ x.1 = i + 1) then t else 0) *
        d x ^ 2 := by
    rw [Finset.mul_sum, sum_eq_sum_pairSite p i]
    · refine Finset.sum_congr rfl fun a _ => ?_
      simp [a.2]
    · intro x hx
      simp [hx]
  have hg2 : (∑ a : PairSite p i, ∑ b : PairSite p i,
      if p.siteIndex a.1 < p.siteIndex b.1 then t / 2 * (u a.1 b.1 ^ 2 + v a.1 b.1 ^ 2) else 0) =
      ∑ x : p.Site, ∑ y ∈ Finset.univ.filter (fun y => p.siteIndex x < p.siteIndex y),
        (if (x.1 = i ∨ x.1 = i + 1) ∧ (y.1 = i ∨ y.1 = i + 1) then t else 0) / 2 *
          (u x y ^ 2 + v x y ^ 2) := by
    simp only [Finset.sum_filter]
    symm
    rw [sum_eq_sum_pairSite p i]
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [sum_eq_sum_pairSite p i]
      · refine Finset.sum_congr rfl fun b _ => ?_
        simp [a.2, b.2]
      · intro y hy
        simp [hy]
    · intro x hx
      refine Finset.sum_eq_zero fun y _ => ?_
      simp [hx]
  unfold Parameters.coordinateVariance gueTestVariance
  rw [hg1, hg2]
  have e1 : ∑ x, p.entryVariance x x * d x ^ 2 =
      ∑ x, p.entryVariance x x * (d x * m x x) ^ 2 +
        ∑ x : p.Site, (if (x.1 = i ∨ x.1 = i + 1) ∧ (x.1 = i ∨ x.1 = i + 1) then t else 0) *
          d x ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    have := hkey x x
    calc p.entryVariance x x * d x ^ 2
        = (p.entryVariance x x * m x x ^ 2 +
            (if (x.1 = i ∨ x.1 = i + 1) ∧ (x.1 = i ∨ x.1 = i + 1) then t else 0)) * d x ^ 2 := by
          rw [this]
      _ = _ := by ring
  have e2 : (∑ x, ∑ y ∈ Finset.univ.filter (fun y => p.siteIndex x < p.siteIndex y),
      p.entryVariance x y / 2 * (u x y ^ 2 + v x y ^ 2)) =
      (∑ x, ∑ y ∈ Finset.univ.filter (fun y => p.siteIndex x < p.siteIndex y),
        p.entryVariance x y / 2 * ((u x y * m x y) ^ 2 + (v x y * m x y) ^ 2)) +
      ∑ x : p.Site, ∑ y ∈ Finset.univ.filter (fun y => p.siteIndex x < p.siteIndex y),
        (if (x.1 = i ∨ x.1 = i + 1) ∧ (y.1 = i ∨ y.1 = i + 1) then t else 0) / 2 *
          (u x y ^ 2 + v x y ^ 2) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    have := hkey x y
    calc p.entryVariance x y / 2 * (u x y ^ 2 + v x y ^ 2)
        = (p.entryVariance x y * m x y ^ 2 +
            (if (x.1 = i ∨ x.1 = i + 1) ∧ (y.1 = i ∨ y.1 = i + 1) then t else 0)) / 2 *
              (u x y ^ 2 + v x y ^ 2) := by
          rw [this]
      _ = _ := by ring
  rw [e1, e2]
  ring

theorem measurable_residualSplitMap (s : ℝ) : Measurable (residualSplitMap p i s) := by
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
  · exact Measurable.of_eval_matrix _ fun a b => Matrix.measurable_apply
  · exact Measurable.of_eval_matrix _ fun a b => Matrix.measurable_apply
  · refine Measurable.of_eval_matrix _ fun a b => ?_
    exact measurable_const.mul Matrix.measurable_apply

theorem measurable_assemble :
    Measurable (fun x : SplitState p i × PairMatrix p i => assemble p i x.1 x.2) := by
  refine Measurable.of_eval_matrix _ fun x y => ?_
  unfold assemble
  have h1 : Measurable (fun z : SplitState p i × PairMatrix p i => z.1.1) :=
    measurable_fst.comp measurable_fst
  have h2 : Measurable (fun z : SplitState p i × PairMatrix p i => z.1.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_fst)
  have h3 : Measurable (fun z : SplitState p i × PairMatrix p i => z.1.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_fst)
  have h4 : Measurable (fun z : SplitState p i × PairMatrix p i => z.2) := measurable_snd
  split_ifs
  · exact (Matrix.measurable_apply.comp h3).add (Matrix.measurable_apply.comp h4)
  · exact continuous_star.measurable.comp (Matrix.measurable_apply.comp h2)
  · exact Matrix.measurable_apply.comp h2
  · exact Matrix.measurable_apply.comp h1

theorem assemble_isHermitian (ω : SplitState p i) (G : PairMatrix p i)
    (h1 : ω.1.IsHermitian) (h3 : ω.2.2.IsHermitian) (hG : G.IsHermitian) :
    (assemble p i ω G).IsHermitian := by
  ext x y
  rw [Matrix.conjTranspose_apply]
  unfold assemble
  by_cases hx : x.1 = i ∨ x.1 = i + 1 <;> by_cases hy : y.1 = i ∨ y.1 = i + 1
  · simp only [hx, hy, dite_true, star_add]
    rw [h3.apply, hG.apply]
  · simp [hx, hy]
  · simp [hx, hy]
  · simp only [hx, hy, dite_false]
    exact h1.apply _ _

theorem ae_residualSplitLaw (model : p.GaussianRingModel) (s : ℝ) :
    ∀ᵐ ω ∂residualSplitLaw p i model s, ω.1.IsHermitian ∧ ω.2.2.IsHermitian := by
  unfold residualSplitLaw
  have hms : MeasurableSet {ω : SplitState p i | ω.1.IsHermitian ∧ ω.2.2.IsHermitian} :=
    (BlockBand.Model.Construction.measurableSet_isHermitian.preimage measurable_fst).inter
      (BlockBand.Model.Construction.measurableSet_isHermitian.preimage (measurable_snd.comp measurable_snd))
  rw [ae_map_iff (measurable_residualSplitMap p i s).aemeasurable hms]
  filter_upwards [model.isPhysical.1] with H hH
  refine ⟨?_, ?_⟩
  · ext a b
    simp only [residualSplitMap, exteriorBlock, Matrix.conjTranspose_apply]
    exact hH.apply _ _
  · ext a b
    rw [Matrix.conjTranspose_apply]
    simp only [residualSplitMap, pairBlock, star_mul']
    rw [hH.apply]
    congr 1
    simp only [pairResidualFactor, (p.entryVariance_symm b.1 a.1).symm, Complex.star_def,
      Complex.conj_ofReal]

instance isProbabilityMeasure_residualSplitLaw (model : p.GaussianRingModel) (s : ℝ) :
    IsProbabilityMeasure (residualSplitLaw p i model s) := by
  unfold residualSplitLaw
  exact (Measure.isProbabilityMeasure_map_iff (measurable_residualSplitMap p i s).aemeasurable).2
    inferInstance

/-- The candidate reassembled law. -/
def splitAssembledLaw (model : p.GaussianRingModel) (s : ℝ) : Measure p.SiteMatrix :=
  ((residualSplitLaw p i model s).prod (gueMeasure (PairSite p i) (pairTime p s))).map
    (fun x => assemble p i x.1 x.2)

instance isProbabilityMeasure_splitAssembledLaw (model : p.GaussianRingModel) (s : ℝ) :
    IsProbabilityMeasure (splitAssembledLaw p i model s) := by
  unfold splitAssembledLaw
  exact (Measure.isProbabilityMeasure_map_iff (measurable_assemble p i).aemeasurable).2
    inferInstance

theorem ae_isHermitian_splitAssembledLaw (model : p.GaussianRingModel) (s : ℝ) :
    ∀ᵐ H ∂splitAssembledLaw p i model s, H.IsHermitian := by
  unfold splitAssembledLaw
  rw [ae_map_iff (measurable_assemble p i).aemeasurable BlockBand.Model.Construction.measurableSet_isHermitian]
  have hω := (Measure.quasiMeasurePreserving_fst
    (μ := residualSplitLaw p i model s)
    (ν := gueMeasure (PairSite p i) (pairTime p s))).ae (ae_residualSplitLaw p i model s)
  have hG := (Measure.quasiMeasurePreserving_snd
    (μ := residualSplitLaw p i model s)
    (ν := gueMeasure (PairSite p i) (pairTime p s))).ae
      (ae_isHermitian_gueMeasure (ι := PairSite p i) (pairTime p s))
  filter_upwards [hω, hG] with x hx hx'
  exact assemble_isHermitian p i x.1 x.2 hx.1 hx.2 hx'

theorem measurable_exp_pairing (d : p.Site → ℝ) (u v : p.Site → p.Site → ℝ) :
    Measurable (fun H : p.SiteMatrix =>
      Complex.exp (Complex.I * (p.coordinatePairing d u v H : ℂ))) := by
  unfold Parameters.coordinatePairing
  have : ∀ x y, Measurable (fun H : p.SiteMatrix => H x y) := fun x y => Matrix.measurable_apply
  fun_prop

theorem charFun_splitAssembledLaw (model : p.GaussianRingModel) (s : ℝ) (hs : 0 < s)
    (hsc : s ≤ min p.c p.b) (d : p.Site → ℝ) (u v : p.Site → p.Site → ℝ) :
    ∫ H, Complex.exp (Complex.I * (p.coordinatePairing d u v H : ℂ))
        ∂splitAssembledLaw p i model s =
      Complex.exp (-(p.coordinateVariance d u v : ℂ) / 2) := by
  set κ : PairSite p i → ℕ := fun a => p.siteIndex a.1
  have hκ : Function.Injective κ := p.siteIndex_injective.comp Subtype.val_injective
  unfold splitAssembledLaw
  rw [integral_map (measurable_assemble p i).aemeasurable
    (measurable_exp_pairing p d u v).aestronglyMeasurable]
  have hpt : ∀ x : SplitState p i × PairMatrix p i,
      Complex.exp (Complex.I * (p.coordinatePairing d u v (assemble p i x.1 x.2) : ℂ)) =
        Complex.exp (Complex.I * (p.coordinatePairing d u v (assemble p i x.1 0) : ℂ)) *
          Complex.exp (Complex.I * (gueTestPairing κ (fun a => d a.1) (fun a b => u a.1 b.1)
            (fun a b => v a.1 b.1) x.2 : ℂ)) := by
    intro x
    rw [assemble_eq_add, coordinatePairing_add, coordinatePairing_assemble_zero, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [hpt]
  rw [integral_prod_mul (fun ω : SplitState p i =>
      Complex.exp (Complex.I * (p.coordinatePairing d u v (assemble p i ω 0) : ℂ)))
    (fun G : PairMatrix p i => Complex.exp (Complex.I * (gueTestPairing κ (fun a => d a.1)
      (fun a b => u a.1 b.1) (fun a b => v a.1 b.1) G : ℂ)))]
  rw [integral_exp_gueTestPairing κ hκ]
  have hmeas : Measurable (fun ω : SplitState p i =>
      Complex.exp (Complex.I * (p.coordinatePairing d u v (assemble p i ω 0) : ℂ))) := by
    have hA : Measurable (fun ω : SplitState p i => assemble p i ω 0) :=
      (measurable_assemble p i).comp (measurable_id.prodMk measurable_const)
    exact (measurable_exp_pairing p d u v).comp hA
  unfold residualSplitLaw
  rw [integral_map (measurable_residualSplitMap p i s).aemeasurable hmeas.aestronglyMeasurable]
  have hae : (fun H : p.SiteMatrix =>
      Complex.exp (Complex.I *
        (p.coordinatePairing d u v (assemble p i (residualSplitMap p i s H) 0) : ℂ))) =ᵐ[
      (model.law : Measure p.SiteMatrix)]
      fun H => Complex.exp (Complex.I * (p.coordinatePairing
        (fun x => d x * siteResidualFactor p i s x x)
        (fun x y => u x y * siteResidualFactor p i s x y)
        (fun x y => v x y * siteResidualFactor p i s x y) H : ℂ)) := by
    filter_upwards [model.isPhysical.1] with H hH
    rw [assemble_residualSplitMap p i s H hH, coordinatePairing_scale]
  rw [integral_congr_ae hae, model.isPhysical.2, ← Complex.exp_add,
    coordinateVariance_split p i s hs hsc d u v]
  congr 1
  push_cast
  ring

/-- `CoareaContract.splitting_exists`. -/
theorem coarea_splitting_exists : ∀ (p : Parameters) (model : p.GaussianRingModel) (i : ZMod p.n)
    (s : ℝ), 0 < s → s ≤ min p.c p.b →
      ∃ Pω : Measure (SplitState p i), IsPairSplitting p i model s Pω := by
  intro p model i s hs hsc
  refine ⟨residualSplitLaw p i model s, ?_⟩
  let model' : p.GaussianRingModel :=
    ⟨⟨splitAssembledLaw p i model s, inferInstance⟩,
      ⟨ae_isHermitian_splitAssembledLaw p i model s,
        charFun_splitAssembledLaw p i model s hs hsc⟩⟩
  have h := BlockBand.Parameters.physicalGaussianRingLaw_unique model' model
  exact congrArg (fun P : ProbabilityMeasure p.SiteMatrix => (P : Measure p.SiteMatrix)) h

end Split

end BlockBand.Coarea.ContractClauses
