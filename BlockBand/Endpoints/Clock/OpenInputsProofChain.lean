module

public import BlockBand.Endpoints.Clock.OpenInputsProofStep

/-!
# The open-inputs lemma: the scalar and first-jet recursion along the chain

For one fresh layer at a deterministic Hermitian old matrix `X` (conditioning on the past `𝓕_j`),
`X₊ = freshSchur E X y`, the fresh fluctuations `freshNoise0 = |h₊(z) - E h₊(z)|`,
`freshNoise1 = |h₊'(z) - E h₊'(z)|` have conditional `L^p` norms `≤ C√p/W` for `2 ≤ p ≤ a₀W` (the
cavity-mean lemma (iii)–(iv)), and on the scalar domain `δ₀(X) ≤ r₀` (`one_step`):
* `δ₀(X₊) ≤ q δ₀(X) + C/W² + freshNoise0` (the cavity-mean lemma (ii) and the deterministic
  contraction `step_bound`);
* `δ₁(X₊) ≤ q δ₁(X) + C δ₀(X) + C/W² + freshNoise1`.

Along the chain we define `δ₀, δ₁` of `X_j` (`chainD0`, `chainD1`), the scalar-domain events
`goodSet` (`δ₀(X_i) ≤ r₀` for all `J ≤ i ≤ j`, i.e. no exit), and prove their measurability (the
first jet through difference quotients, `aesm_deriv_nrt`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
  BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal NNReal Matrix.Norms.L2Operator

namespace OpenInputsProof

open CavityMeanProb ZeroEntranceProb

variable {W : ℕ}

/-!
## Measurability
-/

section Meas

theorem measurable_nrt_comp {Ω : Type*} [MeasurableSpace Ω] {F : Ω → Matrix (Fin W) (Fin W) ℂ}
    (hF : Measurable F) (ζ : ℂ) : Measurable (fun ω => normalizedResolventTrace (F ω) ζ) := by
  have h := (measurable_nrt_joint (W := W)).comp (hF.prodMk (measurable_const (a := ζ)))
  exact h

/-- The step sequence `i/(n+1) → 0`, `≠ 0`. -/
theorem tendsto_stepSeq :
    Tendsto (fun n : ℕ => Complex.I * (((1 / ((n : ℝ) + 1)) : ℝ) : ℂ)) atTop (𝓝[≠] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
  · have h1 := (Complex.continuous_ofReal.tendsto 0).comp
      (tendsto_one_div_add_atTop_nhds_zero_nat)
    have h2 := (tendsto_const_nhds (x := Complex.I)).mul h1
    simpa [Function.comp_def] using h2
  · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    refine mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr ?_)
    positivity

/-- The first jet `ω ↦ f_ω'(z)` of an almost surely Hermitian random matrix is
a.e.-strongly measurable (limit of difference quotients). -/
theorem aesm_deriv_nrt {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {F : Ω → Matrix (Fin W) (Fin W) ℂ} (hF : Measurable F) (hH : ∀ᵐ ω ∂μ, (F ω).IsHermitian)
    {z : ℂ} (hz : 0 < z.im) :
    AEStronglyMeasurable (fun ω => deriv (normalizedResolventTrace (F ω)) z) μ := by
  refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
    (f := fun (n : ℕ) ω => (Complex.I * (((1 / ((n : ℝ) + 1)) : ℝ) : ℂ))⁻¹ •
      (normalizedResolventTrace (F ω) (z + Complex.I * (((1 / ((n : ℝ) + 1)) : ℝ) : ℂ)) -
        normalizedResolventTrace (F ω) z)) (fun n => ?_) ?_
  · simp only [smul_eq_mul]
    exact (((measurable_nrt_comp hF _).sub (measurable_nrt_comp hF z)).const_mul
      _).aestronglyMeasurable
  · filter_upwards [hH] with ω hω
    rw [(hasDerivAt_normalizedResolventTrace hω hz).deriv]
    have := ((hasDerivAt_normalizedResolventTrace hω hz).tendsto_slope_zero).comp tendsto_stepSeq
    simpa only [Function.comp_def] using this

end Meas

/-!
## One fresh layer
-/

/-- The fresh scalar fluctuation `|h₊(z) - E(h₊(z) | X)|`. -/
def freshNoise0 (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (y : OneEndedLayer W) : ℝ :=
  ‖cavityHplus E X (boundaryZ b E) y - ∫ y', cavityHplus E X (boundaryZ b E) y' ∂freshLaw W b‖

/-- The fresh first-jet fluctuation `|h₊'(z) - E(h₊'(z) | X)|`. -/
def freshNoise1 (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (y : OneEndedLayer W) : ℝ :=
  ‖deriv (fun ζ => cavityHplus E X ζ y) (boundaryZ b E) -
    ∫ y', deriv (fun ζ => cavityHplus E X ζ y') (boundaryZ b E) ∂freshLaw W b‖

theorem jetDistance0_freshSchur (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (y : OneEndedLayer W) :
    jetDistance0 b E (freshSchur E X y) = ‖cavityHplus E X (boundaryZ b E) y - matchedA E‖ :=
  rfl

theorem jetDistance1_freshSchur (b E : ℝ) (s : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (y : OneEndedLayer W) :
    jetDistance1 b E s (freshSchur E X y) =
      ‖deriv (fun ζ => cavityHplus E X ζ y) (boundaryZ b E) - s‖ :=
  rfl

theorem measurable_freshSchur_right (E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    Measurable (fun y : OneEndedLayer W => freshSchur E X y) := by
  have h := (measurable_freshSchur_joint (W := W) E).comp
    ((measurable_const (a := X)).prodMk (measurable_id (α := OneEndedLayer W)))
  exact h

theorem measurable_cavityHplus_right (E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ζ : ℂ) :
    Measurable (fun y : OneEndedLayer W => cavityHplus E X ζ y) := by
  have h := (measurable_nrt_joint (W := W)).comp
    ((measurable_freshSchur_right E X).prodMk (measurable_const (a := ζ)))
  exact h

theorem measurable_freshNoise0 (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    Measurable (freshNoise0 b E X) :=
  ((measurable_cavityHplus_right E X _).sub measurable_const).norm

theorem aesm_freshNoise1 (b E : ℝ) {X : Matrix (Fin W) (Fin W) ℂ} (hX : X.IsHermitian)
    (hz : 0 < (boundaryZ b E).im) : AEStronglyMeasurable (freshNoise1 b E X) (freshLaw W b) := by
  have h := aesm_deriv_nrt (μ := freshLaw W b) (measurable_freshSchur_right E X)
    (ae_freshSchur_isHermitian W b E hX) hz
  exact (h.sub aestronglyMeasurable_const).norm

/-- **One step** at a deterministic Hermitian past. -/
theorem one_step (hQ : CavityMeanStatement) {b E : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2)
    (hE0 : -2 < E) (hE1 : E < 2) :
    ∃ r₀ q Cst C₀ a₀ : ℝ, 0 < r₀ ∧ 0 ≤ q ∧ q < 1 ∧ 0 ≤ Cst ∧ 0 ≤ C₀ ∧ 0 < a₀ ∧
      ∀ W : ℕ, 0 < W → ∀ X : Matrix (Fin W) (Fin W) ℂ, X.IsHermitian →
        (∀ p : ℝ, 2 ≤ p → p ≤ a₀ * W →
          eLpNorm (freshNoise0 b E X) (ENNReal.ofReal p) (freshLaw W b) ≤
              ENNReal.ofReal (C₀ * Real.sqrt p / W) ∧
            eLpNorm (freshNoise1 b E X) (ENNReal.ofReal p) (freshLaw W b) ≤
              ENNReal.ofReal (C₀ * Real.sqrt p / W)) ∧
        (jetDistance0 b E X ≤ r₀ → ∀ y : OneEndedLayer W,
          jetDistance0 b E (freshSchur E X y) ≤
              q * jetDistance0 b E X + C₀ / (W : ℝ) ^ 2 + freshNoise0 b E X y ∧
            ∀ s : ℂ, IsStationaryJet b E s →
              jetDistance1 b E s (freshSchur E X y) ≤
                q * jetDistance1 b E s X + Cst * jetDistance0 b E X + C₀ / (W : ℝ) ^ 2 +
                  freshNoise1 b E X y) := by
  have hE : |E| ≤ 2 := abs_le.mpr ⟨hE0.le, hE1.le⟩
  have hzpos : 0 < (boundaryZ b E).im := by
    rw [BlockBand.Layers.boundaryZ_im hE]
    have := BlockBand.Layers.matchedA_im_neg (abs_lt.mpr ⟨hE0, hE1⟩)
    have : 0 < 1 - b := by linarith
    nlinarith
  obtain ⟨r₀, q, Cst, hr₀, hq0, hq1, hCst, hstep⟩ := step_bound hb0 hb1 hE0 hE1
  obtain ⟨⟨a₀, C₀, ha₀, hC₀, h0⟩, h1⟩ := hQ b hb0 hb1 (boundaryZ b E).im ‖boundaryZ b E‖ hzpos
  obtain ⟨a₁, C₁, ha₁, h1⟩ := h1 1
  set Cm := max C₀ (max C₁ 0) with hCm
  have hCm0 : 0 ≤ Cm := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨r₀, q, Cst, Cm, min a₀ a₁, hr₀, hq0, hq1, hCst, hCm0, lt_min ha₀ ha₁, ?_⟩
  intro W hW X hX
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  obtain ⟨-, -, hmean0, hfl0⟩ := h0 W hW X hX E (boundaryZ b E) le_rfl le_rfl
  obtain ⟨hmean1, hfl1⟩ := h1 W hW X hX E (boundaryZ b E) le_rfl le_rfl
  simp only [iteratedDeriv_one] at hmean1 hfl1
  have hmono : ∀ c : ℝ, c ≤ Cm → ∀ p : ℝ, 0 ≤ p →
      ENNReal.ofReal (c * Real.sqrt p / W) ≤ ENNReal.ofReal (Cm * Real.sqrt p / W) := by
    intro c hc p _
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right hc (by positivity)
  refine ⟨fun p hp2 hpa => ⟨?_, ?_⟩, fun hδ y => ⟨?_, fun s hs => ?_⟩⟩
  · have hpa0 : p ≤ a₀ * W := hpa.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hWr.le)
    refine (eLpNorm_mono (measurable_freshNoise0 b E X).aestronglyMeasurable
      fun y => (norm_norm _).le).trans ?_
    exact (hfl0 p hp2 hpa0).trans (hmono C₀ (le_max_left _ _) p (by linarith))
  · have hpa1 : p ≤ a₁ * W := hpa.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hWr.le)
    refine (eLpNorm_mono (aesm_freshNoise1 b E hX hzpos) fun y => (norm_norm _).le).trans ?_
    exact (hfl1 p hp2 hpa1).trans
      (hmono C₁ ((le_max_left _ _).trans (le_max_right _ _)) p (by linarith))
  · obtain ⟨hsc, -⟩ := hstep hW X hX hδ
    rw [jetDistance0_freshSchur]
    set h := cavityHplus E X (boundaryZ b E) y
    set m := ∫ y', cavityHplus E X (boundaryZ b E) y' ∂freshLaw W b
    have htri : ‖h - matchedA E‖ ≤ ‖h - m‖ + ‖m - cavityU X b E (boundaryZ b E)‖ +
        ‖cavityU X b E (boundaryZ b E) - matchedA E‖ := by
      have := norm_sub_le_norm_sub_add_norm_sub h m (matchedA E)
      have := norm_sub_le_norm_sub_add_norm_sub m (cavityU X b E (boundaryZ b E)) (matchedA E)
      linarith
    have hm : ‖m - cavityU X b E (boundaryZ b E)‖ ≤ Cm / (W : ℝ) ^ 2 :=
      hmean0.trans (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))
    have : freshNoise0 b E X y = ‖h - m‖ := rfl
    linarith
  · obtain ⟨-, hj⟩ := hstep hW X hX hδ
    rw [jetDistance1_freshSchur]
    set d := deriv (fun ζ => cavityHplus E X ζ y) (boundaryZ b E)
    set m := ∫ y', deriv (fun ζ => cavityHplus E X ζ y') (boundaryZ b E) ∂freshLaw W b
    have htri : ‖d - s‖ ≤ ‖d - m‖ + ‖m - deriv (cavityU X b E) (boundaryZ b E)‖ +
        ‖deriv (cavityU X b E) (boundaryZ b E) - s‖ := by
      have := norm_sub_le_norm_sub_add_norm_sub d m s
      have := norm_sub_le_norm_sub_add_norm_sub m (deriv (cavityU X b E) (boundaryZ b E)) s
      linarith
    have hm : ‖m - deriv (cavityU X b E) (boundaryZ b E)‖ ≤ Cm / (W : ℝ) ^ 2 :=
      hmean1.trans (div_le_div_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _))
        (by positivity))
    have : freshNoise1 b E X y = ‖d - m‖ := rfl
    have := hj s hs
    linarith

/-!
## The chain
-/

section Chain

variable (b E : ℝ) (s : ℂ) (D : Matrix (Fin W) (Fin W) ℂ)

/-- `δ₀(X_j)`. -/
def chainD0 (j : ℕ) (ω : Fin j → OneEndedLayer W) : ℝ := jetDistance0 b E (oneEndedX E D j ω)

/-- `δ₁(X_j)` at the jet `s`. -/
def chainD1 (j : ℕ) (ω : Fin j → OneEndedLayer W) : ℝ := jetDistance1 b E s (oneEndedX E D j ω)

/-- `Φ_j = δ₀(X_j) + λ δ₁(X_j)`. -/
def chainPhi (lam : ℝ) (j : ℕ) (ω : Fin j → OneEndedLayer W) : ℝ :=
  chainD0 b E D j ω + lam * chainD1 b E s D j ω

/-- The scalar-domain events ("no exit"): `δ₀(X_i) ≤ r₀` for every `J ≤ i ≤ j`. -/
def goodSet (r₀ : ℝ) (J : ℕ) : (j : ℕ) → Set (Fin j → OneEndedLayer W)
  | 0 => {ω | J = 0 → chainD0 b E D 0 ω ≤ r₀}
  | j + 1 => {ω | Fin.init ω ∈ goodSet r₀ J j ∧ (J ≤ j + 1 → chainD0 b E D (j + 1) ω ≤ r₀)}

/-- The combined fresh noise `N₀ + λ N₁` of step `j + 1`. -/
def chainNoise (lam : ℝ) (j : ℕ) (q : (Fin j → OneEndedLayer W) × OneEndedLayer W) : ℝ :=
  freshNoise0 b E (oneEndedX E D j q.1) q.2 + lam * freshNoise1 b E (oneEndedX E D j q.1) q.2

/-- The scalar fresh noise of step `j + 1`. -/
def chainNoise0 (j : ℕ) (q : (Fin j → OneEndedLayer W) × OneEndedLayer W) : ℝ :=
  freshNoise0 b E (oneEndedX E D j q.1) q.2

variable {b E s D}

theorem measurable_chainD0 (j : ℕ) : Measurable (chainD0 b E D j) :=
  ((measurable_zeTrace E D j (boundaryZ b E)).sub measurable_const).norm

theorem aesm_chainD1 (hD : D.IsHermitian) (hz : 0 < (boundaryZ b E).im) (j : ℕ) :
    AEStronglyMeasurable (chainD1 b E s D j) (oneEndedLaw W b j) :=
  ((aesm_deriv_nrt (measurable_X E D j) (ae_X_isHermitian b E hD j) hz).sub
    aestronglyMeasurable_const).norm

theorem aesm_chainPhi (hD : D.IsHermitian) (hz : 0 < (boundaryZ b E).im) (lam : ℝ) (j : ℕ) :
    AEStronglyMeasurable (chainPhi b E s D lam j) (oneEndedLaw W b j) :=
  (measurable_chainD0 j).aestronglyMeasurable.add
    (aestronglyMeasurable_const.mul (aesm_chainD1 hD hz j))

theorem measurableSet_goodSet (r₀ : ℝ) (J : ℕ) :
    ∀ j : ℕ, MeasurableSet (goodSet b E D r₀ J j)
  | 0 => by
    by_cases hJ : J = 0
    · have : goodSet b E D r₀ J 0 = {ω | chainD0 b E D 0 ω ≤ r₀} := by
        ext ω; simp [goodSet, hJ]
      rw [this]; exact measurableSet_le (measurable_chainD0 0) measurable_const
    · have : goodSet b E D r₀ J 0 = Set.univ := by
        ext ω; simp [goodSet, hJ]
      rw [this]; exact MeasurableSet.univ
  | j + 1 => by
    have h1 : MeasurableSet {ω : Fin (j + 1) → OneEndedLayer W | Fin.init ω ∈ goodSet b E D r₀ J j} :=
      (measurable_init j) (measurableSet_goodSet r₀ J j)
    by_cases hJ : J ≤ j + 1
    · have : goodSet b E D r₀ J (j + 1) =
          {ω : Fin (j + 1) → OneEndedLayer W | Fin.init ω ∈ goodSet b E D r₀ J j} ∩
          {ω | chainD0 b E D (j + 1) ω ≤ r₀} := by
        ext ω; simp [goodSet, hJ]
      rw [this]
      exact h1.inter (measurableSet_le (measurable_chainD0 (j + 1)) measurable_const)
    · have : goodSet b E D r₀ J (j + 1) =
          {ω : Fin (j + 1) → OneEndedLayer W | Fin.init ω ∈ goodSet b E D r₀ J j} := by
        ext ω; simp [goodSet, hJ]
      rw [this]; exact h1

theorem goodSet_eq_univ {r₀ : ℝ} {J : ℕ} (j : ℕ) (hj : j < J) :
    goodSet b E D r₀ J j = Set.univ := by
  induction j with
  | zero => ext ω; simp [goodSet, Nat.pos_iff_ne_zero.mp hj]
  | succ j ih =>
    have ih' := ih (by omega)
    ext ω
    simp only [goodSet, ih', Set.mem_univ, true_and, iff_true]
    intro h; omega

theorem chainD0_le_of_mem_goodSet {r₀ : ℝ} {J : ℕ} :
    ∀ {j : ℕ} {ω : Fin j → OneEndedLayer W}, ω ∈ goodSet b E D r₀ J j → J ≤ j →
      chainD0 b E D j ω ≤ r₀
  | 0, _, hω, hj => hω (by omega)
  | _ + 1, _, hω, hj => hω.2 hj

theorem init_mem_goodSet {r₀ : ℝ} {J j : ℕ} {ω : Fin (j + 1) → OneEndedLayer W}
    (hω : ω ∈ goodSet b E D r₀ J (j + 1)) : Fin.init ω ∈ goodSet b E D r₀ J j := hω.1

theorem goodSet_compl_subset {r₀ : ℝ} {J : ℕ} :
    (goodSet b E D r₀ J J)ᶜ ⊆ {ω | r₀ < chainD0 b E D J ω} := by
  intro ω hω
  show r₀ < chainD0 b E D J ω
  by_contra h'
  have h := not_lt.mp h'
  apply hω
  cases J with
  | zero => exact fun _ => h
  | succ J =>
    refine ⟨?_, fun _ => h⟩
    rw [goodSet_eq_univ J (by omega)]; exact Set.mem_univ _

theorem measurable_chainNoise0 (j : ℕ) : Measurable (chainNoise0 b E D j) := by
  have hX : Measurable (fun q : (Fin j → OneEndedLayer W) × OneEndedLayer W =>
      (oneEndedX E D j q.1, q.2)) :=
    ((measurable_X E D j).comp measurable_fst).prodMk measurable_snd
  have h1 : Measurable (fun q : (Fin j → OneEndedLayer W) × OneEndedLayer W =>
      cavityHplus E (oneEndedX E D j q.1) (boundaryZ b E) q.2) :=
    measurable_nextG E D j (boundaryZ b E)
  have h2 : Measurable (fun q : (Fin j → OneEndedLayer W) × OneEndedLayer W =>
      ∫ y, cavityHplus E (oneEndedX E D j q.1) (boundaryZ b E) y ∂freshLaw W b) :=
    ((stronglyMeasurable_condMean b E D j (boundaryZ b E)).measurable).comp measurable_fst
  exact (h1.sub h2).norm

theorem aesm_chainNoise (hD : D.IsHermitian) (hz : 0 < (boundaryZ b E).im) (lam : ℝ) (j : ℕ) :
    AEStronglyMeasurable (chainNoise b E D lam j) ((oneEndedLaw W b j).prod (freshLaw W b)) := by
  have hF : Measurable (fun q : (Fin j → OneEndedLayer W) × OneEndedLayer W =>
      freshSchur E (oneEndedX E D j q.1) q.2) := by
    have h := (measurable_freshSchur_joint (W := W) E).comp
      (((measurable_X E D j).comp measurable_fst).prodMk measurable_snd)
    exact h
  have hH : ∀ᵐ q ∂((oneEndedLaw W b j).prod (freshLaw W b)),
      (freshSchur E (oneEndedX E D j q.1) q.2).IsHermitian := by
    filter_upwards [ae_prod_herm b E hD j] with q hq using hq.2
  have hG := aesm_deriv_nrt hF hH hz
  have hGm : AEStronglyMeasurable (fun q : (Fin j → OneEndedLayer W) × OneEndedLayer W =>
      ∫ y, deriv (fun ζ => cavityHplus E (oneEndedX E D j q.1) ζ y) (boundaryZ b E)
        ∂freshLaw W b) ((oneEndedLaw W b j).prod (freshLaw W b)) := by
    have h := hG.integral_prod_right'
    exact h.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have h1 : AEStronglyMeasurable (fun q : (Fin j → OneEndedLayer W) × OneEndedLayer W =>
      freshNoise1 b E (oneEndedX E D j q.1) q.2) ((oneEndedLaw W b j).prod (freshLaw W b)) :=
    (hG.sub hGm).norm
  exact (measurable_chainNoise0 j).aestronglyMeasurable.add (aestronglyMeasurable_const.mul h1)

end Chain

/-!
## Conditioning along the chain
-/

section Generic

variable {S : Type*} [MeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν]

theorem eLpNorm_real_mul {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ} (c : ℝ)
    (p : ℝ≥0∞) : eLpNorm (fun x => c * f x) p μ = ENNReal.ofReal |c| * eLpNorm f p μ := by
  have h := eLpNorm_const_smul c f p μ
  rw [Real.enorm_eq_ofReal_abs] at h
  exact h

/-- **Conditional Minkowski step**: a pathwise bound by the past and a fresh noise with
conditional `L^p` norm `≤ B` gives the `L^p` recursion. -/
theorem eLpNorm_step_le {j : ℕ} {f : (Fin (j + 1) → S) → ℝ} {g : (Fin j → S) → ℝ}
    {n : (Fin j → S) × S → ℝ} (hf : AEStronglyMeasurable f (Measure.pi fun _ => ν))
    (hg : AEStronglyMeasurable g (Measure.pi fun _ => ν))
    (hn : AEStronglyMeasurable n ((Measure.pi fun _ : Fin j => ν).prod ν))
    {θ c B p : ℝ} (hθ : 0 ≤ θ) (hc : 0 ≤ c) (hB : 0 ≤ B) (hp : 1 ≤ p)
    (hpt : ∀ᵐ ω ∂(Measure.pi fun _ : Fin (j + 1) => ν),
      ‖f ω‖ ≤ θ * ‖g (Fin.init ω)‖ + c + n (Fin.init ω, ω (Fin.last j)))
    (hnb : ∀ᵐ x ∂(Measure.pi fun _ : Fin j => ν),
      eLpNorm (fun y => n (x, y)) (ENNReal.ofReal p) ν ≤ ENNReal.ofReal B) :
    eLpNorm f (ENNReal.ofReal p) (Measure.pi fun _ => ν) ≤
      ENNReal.ofReal θ * eLpNorm g (ENNReal.ofReal p) (Measure.pi fun _ => ν) +
        ENNReal.ofReal c + ENNReal.ofReal B := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hp
  have h1 : eLpNorm f (ENNReal.ofReal p) (Measure.pi fun _ => ν) ≤
      eLpNorm ((fun ω : Fin (j + 1) → S => θ * ‖g (Fin.init ω)‖) + (fun _ => c) +
        (fun ω => n (Fin.init ω, ω (Fin.last j)))) (ENNReal.ofReal p)
        (Measure.pi fun _ => ν) := by
    refine eLpNorm_mono_ae hf (hpt.mono fun ω h => ?_)
    simp only [Pi.add_apply, Real.norm_eq_abs] at h ⊢
    rw [← Real.norm_eq_abs] at h
    exact h.trans (le_abs_self _)
  refine h1.trans ((eLpNorm_add_le hp1).trans (add_le_add ((eLpNorm_add_le hp1).trans
    (add_le_add ?_ ?_)) ?_))
  · rw [eLpNorm_real_mul, abs_of_nonneg hθ]
    gcongr
    have hgi : AEStronglyMeasurable (fun ω : Fin (j + 1) → S => g (Fin.init ω))
        (Measure.pi fun _ => ν) := hg.comp_measurePreserving (measurePreserving_init ν j)
    rw [eLpNorm_norm _ hgi]
    exact (eLpNorm_init_eq ν j hg _).le
  · rw [ZeroEntranceProb.eLpNorm_const_prob _ (by linarith), abs_of_nonneg hc]
  · refine (eLpNorm_initLast_le ν j hn (by linarith) hnb).trans ?_
    rw [ZeroEntranceProb.eLpNorm_const_prob _ (by linarith), abs_of_nonneg hB]

/-- **Exit recursion**: if outside `A'` (past) or a large fresh noise, the event `A` occurs
only on the stated union, then `P(A) ≤ P(A') + P(noise ≥ ρ)`. -/
theorem measure_step_le {j : ℕ} {A : Set (Fin (j + 1) → S)} {A' : Set (Fin j → S)}
    (hA' : MeasurableSet A') {n : (Fin j → S) × S → ℝ} {ρ : ℝ}
    (hsub : ∀ᵐ ω ∂(Measure.pi fun _ : Fin (j + 1) => ν),
      ω ∈ A → Fin.init ω ∈ A' ∨ ρ ≤ n (Fin.init ω, ω (Fin.last j))) :
    (Measure.pi fun _ : Fin (j + 1) => ν) A ≤ (Measure.pi fun _ : Fin j => ν) A' +
      (Measure.pi fun _ : Fin (j + 1) => ν) {ω | ρ ≤ n (Fin.init ω, ω (Fin.last j))} := by
  have h1 : (Measure.pi fun _ : Fin (j + 1) => ν) A ≤ (Measure.pi fun _ : Fin (j + 1) => ν)
      ((fun ω => Fin.init ω) ⁻¹' A' ∪ {ω | ρ ≤ n (Fin.init ω, ω (Fin.last j))}) := by
    refine measure_mono_ae (hsub.mono fun ω h hω => ?_)
    rcases h hω with h' | h'
    · exact Or.inl h'
    · exact Or.inr h'
  refine h1.trans ((measure_union_le _ _).trans (add_le_add ?_ le_rfl))
  rw [(measurePreserving_init ν j).measure_preimage hA'.nullMeasurableSet]

end Generic

/-- **Markov at order `P`**: `P(ρ ≤ f) ≤ (B/ρ)^P` when `‖f‖_P ≤ B`. -/
theorem measure_ge_le_of_eLpNorm {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    {ρ P B : ℝ} (hρ : 0 < ρ) (hP : 0 < P) (hB0 : 0 ≤ B)
    (hB : eLpNorm f (ENNReal.ofReal P) μ ≤ ENNReal.ofReal B) :
    μ {x | ρ ≤ f x} ≤ ENNReal.ofReal ((B / ρ) ^ P) := by
  have hP0 : ENNReal.ofReal P ≠ 0 := by simpa using hP
  have hsub : {x | ρ ≤ f x} ⊆ {x | ENNReal.ofReal ρ ≤ ‖f x‖ₑ} := by
    intro x hx
    show ENNReal.ofReal ρ ≤ ‖f x‖ₑ
    have hx' : ρ ≤ f x := hx
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (hx'.trans (le_abs_self _))
  refine (measure_mono hsub).trans ?_
  refine (meas_ge_le_mul_pow_eLpNorm_enorm μ hP0 ENNReal.ofReal_ne_top
    (ENNReal.ofReal_pos.mpr hρ).ne' (fun h => absurd h ENNReal.ofReal_ne_top)).trans ?_
  rw [ENNReal.toReal_ofReal hP.le]
  calc (ENNReal.ofReal ρ)⁻¹ ^ P * eLpNorm f (ENNReal.ofReal P) μ ^ P
      ≤ (ENNReal.ofReal ρ)⁻¹ ^ P * ENNReal.ofReal B ^ P := by gcongr
    _ = ENNReal.ofReal ((B / ρ) ^ P) := by
      rw [← ENNReal.mul_rpow_of_nonneg _ _ hP.le, ← ENNReal.ofReal_inv_of_pos hρ,
        ← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_rpow_of_nonneg (by positivity) hP.le,
        div_eq_inv_mul]

end OpenInputsProof

end BlockBand.Endpoints.Clock
