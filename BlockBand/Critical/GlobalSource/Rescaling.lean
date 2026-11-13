module

public import BlockBand.Critical.GlobalSource.BlockLaws

/-!
# Global Gaussian source: mass rescaling and block-law convergence

* `rescaleFactor`, `rescaledProfile`: profile `c q`, `c = m/m_W`, with discrete mass exactly `m`.
* `tendsto_profileMass_div`, `tendsto_rescaleFactor`: `m_W → m`, `c → 1`.
* `tendsto_tv_contBlockLaw_discreteBlockLaw`: total variation of the block laws `→ 0`.
* `tendsto_charFun_rescale`: the Gaussian mass rescaling changes the characteristic functions by
  `o(1)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.GlobalSource

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open BlockBand.Internal.Contracts.CriticalEntire
open BlockBand.Internal.Contracts.TransmissionPath

/-- Mass-rescaling factor `c = m/m_W` (`m = τ∫q`, `m_W = profileMass` of the path profile); `1` if `m_W = 0`. -/
def rescaleFactor (τ : ℝ) (Q : C(BlockBand.Torus, ℝ)) (W n : ℕ) : ℝ :=
  if profileMass W (probePathLength n) (pathProfileValue n Q) = 0 then 1
  else probeMass τ Q / profileMass W (probePathLength n) (pathProfileValue n Q)

/-- The rescaled path profile `c q`, whose discrete mass is exactly `m` (`profileMass_rescaledProfile`). -/
def rescaledProfile (τ : ℝ) (Q : C(BlockBand.Torus, ℝ)) (W n : ℕ) :
    Fin (probePathLength n) → ℝ :=
  fun i => rescaleFactor τ Q W n * pathProfileValue n Q i

/-- The continuum block law is a probability measure. -/
theorem isProbabilityMeasure_contBlockLaw {τ : ℝ} (hτ : 0 < τ) {Q : C(BlockBand.Torus, ℝ)}
    (hQ : ∀ x, 0 ≤ Q x) (W L : ℕ) : IsProbabilityMeasure (contBlockLaw τ Q W L) := by
  have := isProbabilityMeasure_probeBirthLaw hτ hQ
  unfold contBlockLaw
  split_ifs
  · infer_instance
  · infer_instance

/-- `Σ_o v(o) = m_W / m`. -/
theorem sum_contRefWeight (τ : ℝ) (Q : C(BlockBand.Torus, ℝ)) (W n : ℕ) :
    ∑ o, contRefWeight τ Q W n o =
      profileMass W (probePathLength n) (pathProfileValue n Q) / probeMass τ Q := by
  rw [Fin.sum_univ_castSucc]
  simp only [contRefWeight, Fin.val_castSucc, Fin.is_lt, ↓reduceDIte, Fin.val_last, lt_self_iff_false,
    add_zero, profileMass]
  rw [Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp

/-- `|Σ v - Σ p| ≤ Σ |p - v|`. -/
theorem abs_sum_sub_le {ι : Type*} [Fintype ι] (p v : ι → ℝ) :
    |∑ o, v o - ∑ o, p o| ≤ ∑ o, |p o - v o| := by
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  exact Finset.sum_congr rfl fun o _ => abs_sub_comm _ _

/-- (i) The discrete mass `m_W = W⁻¹ Σ_i q(i)` of the remaining path converges to `m = τ∫q` (positive mass), along every critical sequence. -/
theorem tendsto_profileMass_div {τ : ℝ} (hτ : 0 < τ) {Q : C(BlockBand.Torus, ℝ)}
    (hQ : ∀ x, 0 ≤ Q x) (hm : 0 < probeMass τ Q) (s : BlockBand.CriticalSequence τ) :
    Tendsto (fun j => profileMass (s.W j) (probePathLength (s.n j))
      (pathProfileValue (s.n j) Q) / probeMass τ Q) atTop (𝓝 1) := by
  have h := tendsto_sum_abs_contBlockLaw_sub hτ hQ hm s
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun j => norm_nonneg _) (fun j => ?_) h
  have := isProbabilityMeasure_contBlockLaw hτ hQ (s.W j) (probePathLength (s.n j))
  have h1 : ∑ o, (contBlockLaw τ Q (s.W j) (probePathLength (s.n j)) {o}).toReal = 1 := by
    have := sum_measureReal_singleton (μ := contBlockLaw τ Q (s.W j) (probePathLength (s.n j)))
      Finset.univ
    rw [Finset.coe_univ, probReal_univ] at this
    exact this
  rw [← sum_contRefWeight, Real.norm_eq_abs, ← h1]
  exact abs_sum_sub_le _ _

/-- Atoms of the discrete block law. -/
theorem discreteBlockLaw_real_castSucc {W L : ℕ} {r : Fin L → ℝ} (hr : ∀ k, 0 ≤ r k)
    (hpm : 0 < profileMass W L r) (i : Fin L) :
    (discreteBlockLaw W L r).real {i.castSucc} = r i / ((W : ℝ) * profileMass W L r) := by
  classical
  simp only [discreteBlockLaw, hpm, ↓reduceIte, Measure.real]
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · rw [Measure.dirac_apply' _ (measurableSet_singleton _),
      Set.indicator_of_mem (Set.mem_singleton _),
      Pi.one_apply, mul_one, ENNReal.toReal_ofReal (div_nonneg (hr i) (by
        have : (0 : ℝ) ≤ W := Nat.cast_nonneg W
        positivity))]
  · intro k _ hk
    rw [Measure.dirac_apply' _ (measurableSet_singleton _), Set.indicator_of_notMem, mul_zero]
    simp only [Set.mem_singleton_iff]
    exact fun h => hk (Fin.castSucc_injective _ h)
  · simp

/-- The discrete block law has no mass on the no-tag index (positive mass). -/
theorem discreteBlockLaw_real_last {W L : ℕ} {r : Fin L → ℝ} (hpm : 0 < profileMass W L r) :
    (discreteBlockLaw W L r).real {Fin.last L} = 0 := by
  classical
  simp only [discreteBlockLaw, hpm, ↓reduceIte, Measure.real]
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  rw [Finset.sum_eq_zero fun k _ => by
    rw [Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_singleton _),
      Set.indicator_of_notMem (by simp [Fin.castSucc_ne_last]), smul_zero]]
  rfl

/-- The rescaled profile has discrete mass `m`. -/
theorem profileMass_rescaledProfile {τ : ℝ} {Q : C(BlockBand.Torus, ℝ)} {W n : ℕ}
    (h : profileMass W (probePathLength n) (pathProfileValue n Q) ≠ 0) :
    profileMass W (probePathLength n) (rescaledProfile τ Q W n) = probeMass τ Q := by
  unfold rescaledProfile rescaleFactor
  simp only [h, ↓reduceIte]
  have : profileMass W (probePathLength n) (fun i => probeMass τ Q /
      profileMass W (probePathLength n) (pathProfileValue n Q) * pathProfileValue n Q i) =
      probeMass τ Q / profileMass W (probePathLength n) (pathProfileValue n Q) *
        profileMass W (probePathLength n) (pathProfileValue n Q) := by
    simp only [profileMass, ← Finset.mul_sum]; ring
  rw [this, div_mul_cancel₀ _ h]

/-- (ii) **Block-law comparison**: along every critical sequence the continuum block law (`k = ⌊W t⌋`, `t` of
density `q(t/τ)/m`) and the discrete block law of the rescaled profile (`P(K = i) = q_i/(W m_W)`)
are close in total variation (positive mass). -/
theorem tendsto_tv_contBlockLaw_discreteBlockLaw {τ : ℝ} (hτ : 0 < τ) {Q : C(BlockBand.Torus, ℝ)}
    (hQ : ∀ x, 0 ≤ Q x) (hm : 0 < probeMass τ Q) (s : BlockBand.CriticalSequence τ) :
    Tendsto (fun j => ∑ o, |(contBlockLaw τ Q (s.W j) (probePathLength (s.n j))).real {o} -
      (discreteBlockLaw (s.W j) (probePathLength (s.n j))
        (rescaledProfile τ Q (s.W j) (s.n j))).real {o}|) atTop (𝓝 0) := by
  set m := probeMass τ Q
  have h1 := tendsto_sum_abs_contBlockLaw_sub hτ hQ hm s
  have h2 := tendsto_profileMass_div hτ hQ hm s
  have h3 : Tendsto (fun j => |profileMass (s.W j) (probePathLength (s.n j))
      (pathProfileValue (s.n j) Q) / m - 1|) atTop (𝓝 0) := by
    have := (h2.sub (tendsto_const_nhds (x := (1 : ℝ)))).abs
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun j => Finset.sum_nonneg fun o _ => abs_nonneg _)
    ?_ (by simpa using h1.add h3)
  filter_upwards [h2.eventually (lt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with j hj
  set W := s.W j
  set n := s.n j
  set L := probePathLength n
  set q := pathProfileValue n Q
  set pm := profileMass W L q
  have hpm : 0 < pm := by
    have := (div_pos_iff_of_pos_right hm).1 hj; exact this
  have hpm' : profileMass W (probePathLength n) (pathProfileValue n Q) ≠ 0 := hpm.ne'
  have hpmr : profileMass W L (rescaledProfile τ Q W n) = m :=
    profileMass_rescaledProfile hpm.ne'
  have hr : ∀ k, 0 ≤ rescaledProfile τ Q W n k := fun k => by
    unfold rescaledProfile rescaleFactor
    simp only [hpm', ↓reduceIte]
    exact mul_nonneg (div_nonneg hm.le hpm.le) (hQ _)
  have hWpos : (0 : ℝ) < W := by exact_mod_cast s.W_pos j
  -- the discrete law as rescaled reference weights
  have hd : ∀ o, (discreteBlockLaw W L (rescaledProfile τ Q W n)).real {o} =
      (m / pm) * contRefWeight τ Q W n o := by
    intro o
    induction o using Fin.lastCases with
    | last => rw [discreteBlockLaw_real_last (hpmr ▸ hm), contRefWeight]; simp [L]
    | cast i =>
      rw [discreteBlockLaw_real_castSucc hr (hpmr ▸ hm), hpmr, contRefWeight]
      have hi : (i.castSucc : Fin (L + 1)).val < probePathLength n := by simp [L]
      simp only [hi, ↓reduceDIte, rescaledProfile, rescaleFactor, hpm', ↓reduceIte]
      have he : (⟨(i.castSucc : Fin (L + 1)).val, hi⟩ : Fin (probePathLength n)) = i := Fin.ext rfl
      rw [he]
      ring
  have hsum : ∑ o, contRefWeight τ Q W n o = pm / m := sum_contRefWeight τ Q W n
  calc ∑ o, |(contBlockLaw τ Q W L).real {o} - (discreteBlockLaw W L
        (rescaledProfile τ Q W n)).real {o}|
      ≤ ∑ o, (|(contBlockLaw τ Q W L {o}).toReal - contRefWeight τ Q W n o| +
          |contRefWeight τ Q W n o - (m / pm) * contRefWeight τ Q W n o|) := by
        refine Finset.sum_le_sum fun o _ => ?_
        rw [hd]
        exact abs_sub_le _ _ _
    _ = ∑ o, |(contBlockLaw τ Q W L {o}).toReal - contRefWeight τ Q W n o| +
          |pm / m - 1| := by
        rw [Finset.sum_add_distrib]
        congr 1
        have hv : ∀ o, 0 ≤ contRefWeight τ Q W n o := fun o => by
          unfold contRefWeight; split_ifs
          · exact div_nonneg (hQ _) (by positivity)
          · exact le_rfl
        have : ∀ o, |contRefWeight τ Q W n o - (m / pm) * contRefWeight τ Q W n o| =
            |1 - m / pm| * contRefWeight τ Q W n o := fun o => by
          rw [← one_sub_mul, abs_mul, abs_of_nonneg (hv o)]
        simp_rw [this]
        rw [← Finset.mul_sum, hsum]
        rw [← abs_of_pos (div_pos hpm hm), ← abs_mul, sub_mul, one_mul, div_mul_div_comm,
          mul_comm m pm, div_self (mul_pos hpm hm).ne', abs_of_pos (div_pos hpm hm)]

/-- A zero-mass profile vanishes on the path. -/
theorem pathProfileValue_eq_zero_of_probeMass {τ : ℝ} (hτ : 0 < τ) {Q : C(BlockBand.Torus, ℝ)}
    (hQ : ∀ x, 0 ≤ Q x) (hm : ¬ 0 < probeMass τ Q) (n : ℕ) (i : Fin (probePathLength n)) :
    pathProfileValue n Q i = 0 :=
  eq_zero_of_probeMass_eq_zero hτ hQ (le_antisymm (not_lt.1 hm) (probeMass_nonneg hτ.le hQ)) _

/-- A zero-mass profile has zero discrete mass. -/
theorem profileMass_eq_zero_of_probeMass {τ : ℝ} (hτ : 0 < τ) {Q : C(BlockBand.Torus, ℝ)}
    (hQ : ∀ x, 0 ≤ Q x) (hm : ¬ 0 < probeMass τ Q) (W n : ℕ) :
    profileMass W (probePathLength n) (pathProfileValue n Q) = 0 := by
  simp [profileMass, pathProfileValue_eq_zero_of_probeMass hτ hQ hm]

/-- (iii) The rescaling factors tend to `1` along every critical sequence. -/
theorem tendsto_rescaleFactor {τ : ℝ} (hτ : 0 < τ) {Q : C(BlockBand.Torus, ℝ)}
    (hQ : ∀ x, 0 ≤ Q x) (s : BlockBand.CriticalSequence τ) :
    Tendsto (fun j => rescaleFactor τ Q (s.W j) (s.n j)) atTop (𝓝 1) := by
  by_cases hm : 0 < probeMass τ Q
  · have h2 := tendsto_profileMass_div hτ hQ hm s
    have h := h2.inv₀ one_ne_zero
    rw [inv_one] at h
    refine h.congr' ?_
    filter_upwards [h2.eventually (lt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with j hj
    have hpm : profileMass (s.W j) (probePathLength (s.n j)) (pathProfileValue (s.n j) Q) ≠ 0 :=
      ((div_pos_iff_of_pos_right hm).1 hj).ne'
    simp only [rescaleFactor, hpm, ↓reduceIte, inv_div]
  · refine tendsto_const_nhds.congr fun j => ?_
    simp [rescaleFactor, profileMass_eq_zero_of_probeMass hτ hQ hm]

/-- Eventually the rescaled discrete mass equals the continuum mass `m`. -/
theorem eventually_profileMass_rescaledProfile {τ : ℝ} (hτ : 0 < τ) {Q : C(BlockBand.Torus, ℝ)}
    (hQ : ∀ x, 0 ≤ Q x) (s : BlockBand.CriticalSequence τ) :
    ∀ᶠ j in atTop, profileMass (s.W j) (probePathLength (s.n j))
      (rescaledProfile τ Q (s.W j) (s.n j)) = probeMass τ Q := by
  by_cases hm : 0 < probeMass τ Q
  · have h2 := tendsto_profileMass_div hτ hQ hm s
    filter_upwards [h2.eventually (lt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with j hj
    exact profileMass_rescaledProfile ((div_pos_iff_of_pos_right hm).1 hj).ne'
  · refine Eventually.of_forall fun j => ?_
    have h0 := le_antisymm (not_lt.1 hm) (probeMass_nonneg hτ.le hQ)
    rw [h0]
    simp [profileMass, rescaledProfile, pathProfileValue_eq_zero_of_probeMass hτ hQ hm]

/-- For a zero-mass group both block laws are the no-tag point mass. -/
theorem contBlockLaw_eq_discreteBlockLaw_of_zero {τ : ℝ} (hτ : 0 < τ) {Q : C(BlockBand.Torus, ℝ)}
    (hQ : ∀ x, 0 ≤ Q x) (hm : ¬ 0 < probeMass τ Q) (W n : ℕ) :
    contBlockLaw τ Q W (probePathLength n) =
      discreteBlockLaw W (probePathLength n) (rescaledProfile τ Q W n) := by
  have h0 : profileMass W (probePathLength n) (rescaledProfile τ Q W n) = 0 := by
    simp [profileMass, rescaledProfile, pathProfileValue_eq_zero_of_probeMass hτ hQ hm]
  simp [contBlockLaw, discreteBlockLaw, hm, h0]

/-- Rescaling profiles by `c_a ≥ 0` multiplies `𝒦_{aa'}` by `√(c_a c_{a'})` (same probes). -/
theorem profileProbeMatrix_rescale (b E : ℝ) (W L : ℕ) {J : ℕ} (q : Fin J → Fin L → ℝ)
    {c : Fin J → ℝ} (hc : ∀ a, 0 ≤ c a) (x : GrowthPath W × (Fin J → Fin L × Fin W → ℂ)) :
    profileProbeMatrix b E W L (fun a i => c a * q a i) x =
      Matrix.of fun a a' => ((Real.sqrt (c a) * Real.sqrt (c a') : ℝ) : ℂ) *
        profileProbeMatrix b E W L q x a a' := by
  funext a a'
  rw [Matrix.of_apply]
  simp only [profileProbeMatrix, profileWeight, Real.sqrt_mul (hc _)]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [Pi.star_apply, star_mul', Complex.star_def, Complex.conj_ofReal]
  push_cast
  ring

/-- `matrixCoord` is additive. -/
theorem matrixCoord_sub {J : ℕ} (K K' : Matrix (Fin J) (Fin J) ℂ) :
    matrixCoord J K - matrixCoord J K' = matrixCoord J (K - K') := by
  ext p
  simp only [PiLp.sub_apply, matrixCoord_apply, Matrix.sub_apply]
  split_ifs <;> simp

/-- Entrywise rescaling by factors within `δ` of `1` moves `matrixCoord` by at most `δ‖·‖`. -/
theorem norm_matrixCoord_scale_sub_le {J : ℕ} (K : Matrix (Fin J) (Fin J) ℂ)
    (d : Fin J → Fin J → ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (hd : ∀ a a', |1 - d a a'| ≤ δ) :
    ‖matrixCoord J K - matrixCoord J (Matrix.of fun a a' => ((d a a' : ℝ) : ℂ) * K a a')‖ ≤
      δ * ‖matrixCoord J K‖ := by
  rw [matrixCoord_sub]
  refine le_of_sq_le_sq ?_ (by positivity)
  rw [mul_pow, norm_sq_matrixCoord, norm_sq_matrixCoord, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun a' _ => ?_
  rw [Matrix.sub_apply, Matrix.of_apply, ← one_sub_mul, norm_mul, mul_pow]
  · gcongr
    rw [show (1 : ℂ) - ((d a a' : ℝ) : ℂ) = ((1 - d a a' : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
    exact hd a a'

/-- **Gaussian mass rescaling.** Domain: `0 < b < 1/2`, `-2 < E < 2`, `τ > 0`, nonnegative
continuous profiles, any critical sequence, any `u`. The characteristic functions (real coordinates)
of `𝒦_W` (law `globalProbeMatrixLaw`) and of the Gaussian probe matrix with the rescaled profiles
`c_a q_a` (law `profileProbeLaw`) differ by `o(1)` as `j → ∞`. Proof: same probes,
`𝒦^c_{aa'} = √(c_a c_{a'}) 𝒦_{aa'}`, `c → 1`, and the uniform second moment of `𝒦_W`
(`exists_eventually_lintegral_norm_sq_le`). Uses only the field `extendedSourceMoments`. -/
theorem tendsto_charFun_rescale
    (hCS : BlockBand.Internal.Contracts.TransmissionLaws.ComplexSourceLawContract)
    {b E τ : ℝ} (hb : 0 < b) (hb' : b < 1 / 2) (hE : -2 < E) (hE' : E < 2) (hτ : 0 < τ) {J : ℕ}
    {Q : Fin J → C(BlockBand.Torus, ℝ)} (hQ : ∀ a x, 0 ≤ Q a x)
    (s : BlockBand.CriticalSequence τ) (u : EuclideanSpace ℝ (Fin J × Fin J × Fin 2)) :
    Tendsto (fun j => ‖charFun (((globalProbeMatrixLaw b E (s.W j) (s.n j) Q :
        ProbabilityMeasure (Matrix (Fin J) (Fin J) ℂ)) : Measure _).map (matrixCoord J)) u -
      charFun ((profileProbeLaw (s.W j) (probePathLength (s.n j)) J b).map (fun x =>
        matrixCoord J (profileProbeMatrix b E (s.W j) (probePathLength (s.n j))
          (fun a => rescaledProfile τ (Q a) (s.W j) (s.n j)) x))) u‖) atTop (𝓝 0) := by
  set e := matrixCoord J
  obtain ⟨B, hBtop, hB⟩ := exists_eventually_lintegral_norm_sq_le hCS hb hb' hE hE' hQ s
  set c : ℕ → Fin J → ℝ := fun j a => rescaleFactor τ (Q a) (s.W j) (s.n j)
  have hc0 : ∀ j a, 0 ≤ c j a := by
    intro j a
    simp only [c, rescaleFactor]
    split_ifs with h
    · exact zero_le_one
    · exact div_nonneg (probeMass_nonneg hτ.le (hQ a)) (by
        unfold profileMass
        exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => hQ _ _))
  set δ : ℕ → ℝ := fun j => ∑ a, ∑ a', |1 - Real.sqrt (c j a) * Real.sqrt (c j a')|
  have hδ0 : ∀ j, 0 ≤ δ j := fun j => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    have : ∀ a a', Tendsto (fun j => |1 - Real.sqrt (c j a) * Real.sqrt (c j a')|) atTop
        (𝓝 0) := by
      intro a a'
      have h1 := ((tendsto_rescaleFactor hτ (hQ a) s).sqrt).mul
        ((tendsto_rescaleFactor hτ (hQ a') s).sqrt)
      simpa using (tendsto_const_nhds (x := (1 : ℝ)) |>.sub h1).abs
    simpa using tendsto_finsetSum _ fun a _ => tendsto_finsetSum _ fun a' _ => this a a'
  have hlim : Tendsto (fun j => ‖u‖ * δ j * (1 + B.toReal)) atTop (𝓝 0) := by
    simpa using (hδlim.const_mul ‖u‖).mul_const (1 + B.toReal)
  refine squeeze_zero' (Eventually.of_forall fun j => norm_nonneg _) ?_ hlim
  filter_upwards [hB] with j hj
  set W := s.W j
  set n := s.n j
  set L := probePathLength n
  have hK := measurable_globalProbeMatrix b E W n Q
  set X : GlobalProbeSample W n J → EuclideanSpace ℝ (Fin J × Fin J × Fin 2) :=
    fun x => e (globalProbeMatrix b E W n Q x)
  have hX : Measurable X := e.continuous.measurable.comp hK
  set d : Fin J → Fin J → ℝ := fun a a' => Real.sqrt (c j a) * Real.sqrt (c j a')
  have hYeq : (fun x => e (profileProbeMatrix b E W L
      (fun a => rescaledProfile τ (Q a) W n) x)) =
      fun x => e (Matrix.of fun a a' => ((d a a' : ℝ) : ℂ) * globalProbeMatrix b E W n Q x a a') := by
    funext x
    have := profileProbeMatrix_rescale b E W L (fun a => pathProfileValue n (Q a)) (hc0 j) x
    exact congrArg e this
  have hcontS : Continuous fun K : Matrix (Fin J) (Fin J) ℂ =>
      e (Matrix.of fun a a' => ((d a a' : ℝ) : ℂ) * K a a') :=
    e.continuous.comp (continuous_pi fun a => continuous_pi fun a' =>
      continuous_const.mul ((continuous_apply a').comp (continuous_apply a)))
  have hY : Measurable fun x : GlobalProbeSample W n J =>
      e (Matrix.of fun a a' => ((d a a' : ℝ) : ℂ) * globalProbeMatrix b E W n Q x a a') :=
    hcontS.measurable.comp hK
  have hlaw : (((globalProbeMatrixLaw b E W n Q : ProbabilityMeasure _) : Measure _).map e) =
      (globalProbeLaw W n J b).map X := by
    change ((globalProbeLaw W n J b).map (globalProbeMatrix b E W n Q)).map e = _
    rw [Measure.map_map e.continuous.measurable hK]
    rfl
  rw [hlaw, hYeq]
  change ‖charFun ((globalProbeLaw W n J b).map X) u - charFun ((globalProbeLaw W n J b).map
    _) u‖ ≤ _
  refine (norm_charFun_map_sub_le _ hX hY u).trans ?_
  -- pointwise domination
  have hpt : ∀ x, min 2 (‖u‖ * ‖X x - e (Matrix.of fun a a' => ((d a a' : ℝ) : ℂ) *
      globalProbeMatrix b E W n Q x a a')‖) ≤ ‖u‖ * δ j * (1 + ‖X x‖ ^ 2) := by
    intro x
    refine (min_le_right _ _).trans ?_
    have h1 := norm_matrixCoord_scale_sub_le (globalProbeMatrix b E W n Q x) d (hδ0 j)
      (fun a a' => Finset.single_le_sum (f := fun a' => |1 - d a a'|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ a') |>.trans
        (Finset.single_le_sum (f := fun a => ∑ a', |1 - d a a'|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ a)))
    have h2 : ‖X x‖ ≤ 1 + ‖X x‖ ^ 2 := by nlinarith [norm_nonneg (X x)]
    calc ‖u‖ * ‖X x - e (Matrix.of fun a a' => ((d a a' : ℝ) : ℂ) *
          globalProbeMatrix b E W n Q x a a')‖ ≤ ‖u‖ * (δ j * ‖X x‖) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ ≤ ‖u‖ * (δ j * (1 + ‖X x‖ ^ 2)) := by gcongr
      _ = _ := by ring
  have hsq : Integrable (fun x => ‖X x‖ ^ 2) (globalProbeLaw W n J b) := by
    refine ⟨(hX.norm.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun x => ?_)) (hj.trans_lt hBtop.lt_top)
    rw [Real.enorm_eq_ofReal (by positivity)]
  have hint2 : Integrable (fun x => ‖u‖ * δ j * (1 + ‖X x‖ ^ 2)) (globalProbeLaw W n J b) :=
    ((integrable_const 1).add hsq).const_mul _
  refine (integral_mono_of_nonneg (Eventually.of_forall fun x =>
    le_min (by norm_num) (by positivity)) hint2 (Eventually.of_forall hpt)).trans ?_
  rw [integral_const_mul, integral_add (integrable_const 1) hsq, integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (by positivity)
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => by positivity)
    (hX.norm.pow_const 2).aestronglyMeasurable]
  exact ENNReal.toReal_mono hBtop hj

end BlockBand.Critical.GlobalSource
