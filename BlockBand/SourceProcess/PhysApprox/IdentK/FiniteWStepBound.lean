module

public import BlockBand.SourceProcess.PhysApprox.IdentK.FiniteWStep

/-!
# The tested bound of one step without a birth

* `xvec`, `phiZ`, `zeta_eq_phiZ`: the discrete state is a continuous function of the
  coordinate vectors at `j` and at `n_s`; hence continuous functions of `zeta j` are
  `b3Sigma W j`-measurable (`measurable_comp_zeta`), and continuous functions of the Gram state
  are measurable (`measurable_comp_gram`).
* `exists_bound_coef`: drift and bracket coefficients are bounded on Gram states with entries
  at most `R`; on `A'_j` the closed Gram state is such a state.
* `dStep`: the step `F(ζ_{j+1}) − F(ζ_j) − W⁻¹ Λ(J_j, ζ_j)` of a test; `dStep_eq` (the
  generator identity `gen_jF`).
* **`enorm_step_le`**: the tested bound of one step without a birth.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram.IdentK.FW

open MeasureTheory Finset Filter Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.CapLimit
open scoped ComplexConjugate ENNReal

variable {W np K : ℕ}

/-!
## The state as a continuous function of coordinate vectors
-/

/-- The Gram state of a coordinate vector. -/
def gOfV (x : CIdx K np → ℂ) : GSt K np := gramOfEntries fun e => x (Sum.inl e)

/-- The `𝒦` matrix of a coordinate vector. -/
def kOfV (x : CIdx K np → ℂ) : KSt np := Matrix.of fun i j => x (Sum.inr (i, j))

theorem continuous_gOfV : Continuous (gOfV (K := K) (np := np)) :=
  continuous_gramOfEntries.comp (continuous_pi fun _ => continuous_apply _)

theorem continuous_kOfV : Continuous (kOfV (K := K) (np := np)) :=
  continuous_pi fun _ => continuous_pi fun _ => continuous_apply _

/-- The state from jumps and two coordinate vectors. -/
def phiZ (J : GSt K np × KSt np) (x x0 : CIdx K np → ℂ) : ZK K np :=
  ((gOfV x - J.1, 0, gOfV x0), kOfV x - J.2,
    fun a => (kOfV x - J.2) a.1 a.2 - kOfV x0 a.1 a.2, kOfV x0)

theorem continuous_phiZ (J : GSt K np × KSt np) :
    Continuous fun q : (CIdx K np → ℂ) × (CIdx K np → ℂ) => phiZ J q.1 q.2 := by
  have hg := continuous_gOfV (K := K) (np := np)
  have hk := continuous_kOfV (K := K) (np := np)
  unfold phiZ
  refine Continuous.prodMk (Continuous.prodMk ((hg.comp continuous_fst).sub continuous_const)
    (continuous_const.prodMk (hg.comp continuous_snd))) (Continuous.prodMk
    ((hk.comp continuous_fst).sub continuous_const) (Continuous.prodMk
      (continuous_pi fun a => ?_) (hk.comp continuous_snd)))
  exact (((hk.comp continuous_fst).sub continuous_const).matrix_elem a.1 a.2).sub
    ((hk.comp continuous_snd).matrix_elem a.1 a.2)

section Path

variable (b E s h : ℝ) (τ m : Fin np → ℝ) (W : ℕ)
  (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)

/-- The coordinate vector at length `j`. -/
def xvec (j : ℕ) (y : ProbedPath W np × ℝ) : CIdx K np → ℂ :=
  fun c => b3X b E s h τ m W j Vs c y

theorem gOfV_xvec (j : ℕ) (y : ProbedPath W np × ℝ) :
    gOfV (xvec b E s h τ m W Vs j y) = b3ClosedGramAt b E s h τ m W j Vs y :=
  gramOfEntries_gramEntry _

theorem kOfV_xvec (j : ℕ) (y : ProbedPath W np × ℝ) :
    kOfV (xvec b E s h τ m W Vs j y) = b3ClosedKAt b E s h τ m W j y := by
  ext i k; rfl

theorem zeta_eq_phiZ (j : ℕ) (y : ProbedPath W np × ℝ) :
    zeta b E s h τ m W Vs j y = phiZ (b3JumpAt b s τ m W j, b3KJumpAt E s τ m W j)
      (xvec b E s h τ m W Vs j y) (xvec b E s h τ m W Vs (closeLen s W) y) := by
  simp only [zeta, phiZ, gOfV_xvec, kOfV_xvec]

variable {b E s h τ m W Vs}

theorem measurable_xvec_past {i j : ℕ} (hs : closeLen s W ≤ i) (hij : i ≤ j)
    (hV : Measurable[growthSigma W (closeLen s W)] Vs) :
    Measurable[b3Sigma W j np] (xvec b E s h τ m W Vs i) :=
  measurable_pi_of fun c => Modul.measurable_b3X_past s h τ m hs hij hV c

theorem measurable_xvec {i : ℕ} (hV : Measurable Vs) :
    Measurable (xvec b E s h τ m W Vs i) :=
  measurable_pi_iff.2 fun c => Modul.measurable_b3X s h τ m hV c

/-- **Continuous functions of the discrete state are adapted.** -/
theorem measurable_comp_zeta {j : ℕ} (hs : closeLen s W ≤ j)
    (hV : Measurable[growthSigma W (closeLen s W)] Vs) {f : ZK K np → ℂ} (hf : Continuous f) :
    Measurable[b3Sigma W j np] fun y => f (zeta b E s h τ m W Vs j y) := by
  have h1 : Measurable[b3Sigma W j np] fun y =>
      (xvec b E s h τ m W Vs j y, xvec b E s h τ m W Vs (closeLen s W) y) :=
    (measurable_xvec_past hs le_rfl hV).prodMk (measurable_xvec_past le_rfl hs hV)
  have h2 := (hf.comp (continuous_phiZ (b3JumpAt (K := K) b s τ m W j,
    b3KJumpAt E s τ m W j))).measurable.comp h1
  simp only [zeta_eq_phiZ]
  exact h2

/-- Continuous functions of the closed Gram state are measurable. -/
theorem measurable_comp_gram {j : ℕ} (hV : Measurable Vs) {f : GSt K np → ℂ}
    (hf : Continuous f) : Measurable fun y => f (b3ClosedGramAt b E s h τ m W j Vs y) := by
  have h2 := (hf.comp continuous_gOfV).measurable.comp (measurable_xvec (i := j) (b := b)
    (E := E) (s := s) (h := h) (τ := τ) (m := m) hV)
  simpa only [Function.comp_def, gOfV_xvec] using h2

theorem measurable_betaS {j : ℕ} (hV : Measurable Vs) (i : BI K np) :
    Measurable fun y => betaS b E s h τ m W Vs j y i := by
  have hX := fun c => Modul.measurable_b3X (b := b) (E := E) (W := W) (np := np) s h τ m
    (i := j) hV c
  have hX1 := fun c => Modul.measurable_b3X (b := b) (E := E) (W := W) (np := np) s h τ m
    (i := j + 1) hV c
  rcases i with e | a | a
  · have : (fun y => betaS b E s h τ m W Vs j y (Sum.inl e)) = fun y =>
        b3X b E s h τ m W (j + 1) Vs (Sum.inl e) y - b3X b E s h τ m W j Vs (Sum.inl e) y -
          gramEntry e (b3BirthAt b τ m W j) := by
      funext y; simp [betaS, bvec, dYs, b3X, cEntry, gramEntry_sub']
    rw [this]; exact ((hX1 _).sub (hX _)).sub measurable_const
  · have : (fun y => betaS b E s h τ m W Vs j y (Sum.inr (Sum.inl a))) = fun y =>
        b3X b E s h τ m W (j + 1) Vs (Sum.inr a) y - b3X b E s h τ m W j Vs (Sum.inr a) y -
          b3KBirthAt E τ m W j a.1 a.2 := by
      funext y; simp [betaS, bvec, dKs, b3X, cEntry]
    rw [this]; exact ((hX1 _).sub (hX _)).sub measurable_const
  · have : (fun y => betaS b E s h τ m W Vs j y (Sum.inr (Sum.inr a))) = fun y =>
        conj (b3X b E s h τ m W (j + 1) Vs (Sum.inr a) y - b3X b E s h τ m W j Vs (Sum.inr a) y -
          b3KBirthAt E τ m W j a.1 a.2) := by
      funext y; simp [betaS, bvec, dKs, b3X, cEntry]
    rw [this]; exact Complex.continuous_conj.measurable.comp (((hX1 _).sub (hX _)).sub
      measurable_const)

end Path

/-!
## Bounded coefficients
-/

theorem continuous_dvec (b E : ℝ) (i : BI K np) : Continuous fun H : GSt K np => dvec b E H i := by
  rcases i with e | a | a
  · exact continuous_drE b E e
  · exact continuous_const
  · exact continuous_const

theorem continuous_Bmat (b E : ℝ) (i i' : BI K np) :
    Continuous fun H : GSt K np => Bmat b E H i i' := by
  rcases i with e | a | a <;> rcases i' with e' | a' | a' <;> simp only [Bmat] <;> fun_prop

theorem exists_bound_coef (b E R : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ H : GSt K np,
    (∀ e, ‖gramEntry e H‖ ≤ R) → (∀ i, ‖dvec b E H i‖ ≤ C) ∧ ∀ i i', ‖Bmat b E H i i'‖ ≤ C := by
  have hbox := isCompact_box (K := K) (np := np) R
  have hd : ∀ i : BI K np, ∃ C, ∀ H ∈ {y : GSt K np | ∀ e, ‖gramEntry e y‖ ≤ R},
      ‖dvec b E H i‖ ≤ C := fun i => hbox.exists_bound_of_continuousOn
    (continuous_dvec b E i).continuousOn
  have hB : ∀ i i' : BI K np, ∃ C, ∀ H ∈ {y : GSt K np | ∀ e, ‖gramEntry e y‖ ≤ R},
      ‖Bmat b E H i i'‖ ≤ C := fun i i' => hbox.exists_bound_of_continuousOn
    (continuous_Bmat b E i i').continuousOn
  choose Cd hCd using hd
  choose CB hCB using hB
  refine ⟨∑ i, |Cd i| + ∑ i, ∑ i', |CB i i'|, by positivity, fun H hH => ⟨fun i => ?_,
    fun i i' => ?_⟩⟩
  · have h1 : |Cd i| ≤ ∑ i, |Cd i| := single_le_sum (f := fun i => |Cd i|)
      (fun _ _ => abs_nonneg _) (mem_univ i)
    have h2 : 0 ≤ ∑ i, ∑ i', |CB i i'| := by positivity
    linarith [hCd i H hH, le_abs_self (Cd i)]
  · have h1 : |CB i i'| ≤ ∑ i', |CB i i'| := single_le_sum (f := fun i' => |CB i i'|)
      (fun _ _ => abs_nonneg _) (mem_univ i')
    have h2 : ∑ i', |CB i i'| ≤ ∑ i, ∑ i', |CB i i'| :=
      single_le_sum (f := fun i => ∑ i', |CB i i'|) (fun _ _ => by positivity) (mem_univ i)
    have h3 : 0 ≤ ∑ i, |Cd i| := by positivity
    linarith [hCB i i' H hH, le_abs_self (CB i i')]

theorem gram_bound_of_alive {b E s h : ℝ} {τ m : Fin np → ℝ} {R : ℝ} {W j : ℕ}
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} (hs : closeLen s W ≤ j)
    {y : ProbedPath W np × ℝ} (hy : y ∈ b3AliveM b E s h τ m R W j Vs) (e : GIdx K np) :
    ‖gramEntry e (b3ClosedGramAt b E s h τ m W j Vs y)‖ ≤ R :=
  ((norm_gramEntry_b3ClosedGramAt_le b E s h τ m W j Vs y e).trans (hy.2 j hs le_rfl).le)

/-!
## The step of a test
-/

/-- The uniform Taylor bound of `exists_taylor_bound`, as a predicate on the constant. -/
def TayB (χ ξ : ℝ → ℝ) (κ : KTest K np) (D C : ℝ) : Prop :=
  0 ≤ C ∧
    (∀ z : ZK K np, Adm D z → ‖κ.fn χ ξ z‖ ≤ C ∧ (∀ i, ‖(jF χ ξ κ z).l i‖ ≤ C) ∧
      ∀ i i', ‖(jF χ ξ κ z).q i i'‖ ≤ C) ∧
    ∀ (z : ZK K np) (dY : GSt K np) (dK : KSt np), Adm D z → Adm D (zstep z dY dK) →
      DiagReal dY →
      ‖κ.fn χ ξ (zstep z dY dK) - κ.fn χ ξ z - lin (jF χ ξ κ z).l (bvec dY dK) -
        quad (jF χ ξ κ z).q (bvec dY dK)‖ ≤ C * nrm (bvec dY dK) ^ 3

theorem exists_tayB {χ ξ : ℝ → ℝ} (hχ : ContDiff ℝ 3 χ) (hχs : HasCompactSupport χ)
    (hξ : ContDiff ℝ 3 ξ) (hξs : HasCompactSupport ξ) (κ : KTest K np) {D : ℝ} (hD : 0 ≤ D) :
    ∃ C, TayB χ ξ κ D C := exists_taylor_bound hχ hχs hξ hξs κ hD

section StepDef

variable (b E s h : ℝ) (τ m : Fin np → ℝ) (W : ℕ)
  (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (χ ξ : ℝ → ℝ) (κ : KTest K np)

/-- **The step of a test**: `F(ζ_{j+1}) − F(ζ_j) − W⁻¹ Λ(J_j, ζ_j)`. -/
def dStep (j : ℕ) (y : ProbedPath W np × ℝ) : ℂ :=
  κ.fn χ ξ (zeta b E s h τ m W Vs (j + 1) y) - κ.fn χ ξ (zeta b E s h τ m W Vs j y) -
    (W : ℂ)⁻¹ * κ.lam χ ξ b E (b3JumpAt b s τ m W j, zeta b E s h τ m W Vs j y)

/-- The Taylor remainder of a step. -/
def remS (j : ℕ) (y : ProbedPath W np × ℝ) : ℂ :=
  κ.fn χ ξ (zeta b E s h τ m W Vs (j + 1) y) - κ.fn χ ξ (zeta b E s h τ m W Vs j y) -
    lin (jF χ ξ κ (zeta b E s h τ m W Vs j y)).l (betaS b E s h τ m W Vs j y) -
    quad (jF χ ξ κ (zeta b E s h τ m W Vs j y)).q (betaS b E s h τ m W Vs j y)

theorem dStep_eq (j : ℕ) (y : ProbedPath W np × ℝ) :
    dStep b E s h τ m W Vs χ ξ κ j y =
      lin (jF χ ξ κ (zeta b E s h τ m W Vs j y)).l (betaS b E s h τ m W Vs j y) +
        quad (jF χ ξ κ (zeta b E s h τ m W Vs j y)).q (betaS b E s h τ m W Vs j y) +
        remS b E s h τ m W Vs χ ξ κ j y -
        (W : ℂ)⁻¹ * (lin (jF χ ξ κ (zeta b E s h τ m W Vs j y)).l
            (dvec b E (b3ClosedGramAt b E s h τ m W j Vs y)) +
          ∑ i, ∑ i', (jF χ ξ κ (zeta b E s h τ m W Vs j y)).q i i' *
            Bmat b E (b3ClosedGramAt b E s h τ m W j Vs y) i i') := by
  have hH : (zeta b E s h τ m W Vs j y).1.1 + b3JumpAt b s τ m W j =
      b3ClosedGramAt b E s h τ m W j Vs y := by simp [zeta]
  have hg := gen_jF χ ξ b E κ (b3JumpAt b s τ m W j) (zeta b E s h τ m W Vs j y)
  rw [hH] at hg
  rw [dStep, ← hg, remS, gen]
  ring

end StepDef

theorem indicator_mul' {α : Type*} (A : Set α) (f g : α → ℂ) :
    A.indicator (fun y => f y * g y) = fun y => A.indicator f y * A.indicator g y := by
  funext y; by_cases hy : y ∈ A <;> simp [hy]

/-- **The tested bound of one step without a birth.** -/
theorem enorm_step_le {b E s h : ℝ} {τ m : Fin np → ℝ} {R : ℝ} {W : ℕ}
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} (hb : b < 1) (hE1 : -2 < E)
    (hE2 : E < 2) (hV : Measurable[growthSigma W (closeLen s W)] Vs) {χ ξ : ℝ → ℝ}
    (hχ : ContDiff ℝ 3 χ) (hξ : ContDiff ℝ 3 ξ) (κ : KTest K np) {C : ℝ}
    (hC : TayB χ ξ κ (((Fintype.card (SrcCol K (Fin np)) : ℝ) + 1) * cJump b m) C) {j : ℕ}
    (hjs : closeLen s W ≤ j) (hj : ¬ IsBirthStep τ W j)
    (hL2 : ∀ c, MemLp ((b3Alive b E s h τ m R W j Vs).indicator (b3dX b E s h τ m W j Vs c)) 2
      (closedLaw b W np))
    {g : ProbedPath W np × ℝ → ℂ} (hg : StronglyMeasurable[b3Sigma W j np] g) {Cg : ℝ}
    (hCg : 0 ≤ Cg) (hgb : ∀ y, ‖g y‖ ≤ Cg) :
    ‖∫ y, g y * (b3AliveM b E s h τ m R W j Vs).indicator
        (dStep b E s h τ m W Vs χ ξ κ j) y ∂closedLaw b W np‖ₑ ≤
      ENNReal.ofReal (Cg * C) * (∑ i, pinE1 b E s h τ m R W Vs j i +
        ∑ i, ∑ i', pinE2 b E s h τ m R W Vs j i i') +
      ENNReal.ofReal Cg * (ENNReal.ofReal C * ∫⁻ y, (b3AliveM b E s h τ m R W j Vs).indicator
        (fun y => ENNReal.ofReal (nrm (betaS b E s h τ m W Vs j y) ^ 3)) y ∂closedLaw b W np) := by
  set μ := closedLaw b W np
  set A' := b3AliveM b E s h τ m R W j Vs
  have hV' : Measurable Vs := hV.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  have hm := gen_sigma_le W j np
  have hA : MeasurableSet[b3Sigma W j np] A' :=
    Modul.measurableSet_b3AliveM_past s h τ m R hjs le_rfl hV
  have hAm : MeasurableSet A' := hm _ hA
  have hAA := b3Alive_ae_eq hb hE1 hE2 s h τ m R W j Vs (np := np)
  obtain ⟨hχc, hχd, hχdd⟩ := cut_continuity hχ
  obtain ⟨hξc, hξd, hξdd⟩ := cut_continuity hξ
  obtain ⟨hC0, hCb, hCr⟩ := hC
  set D := ((Fintype.card (SrcCol K (Fin np)) : ℝ) + 1) * cJump b m
  obtain ⟨CR, hCR0, hCR⟩ := exists_bound_coef (K := K) (np := np) b E R
  -- measurability
  have hl : ∀ i, StronglyMeasurable[b3Sigma W j np] fun y =>
      (jF χ ξ κ (zeta b E s h τ m W Vs j y)).l i := fun i =>
    (measurable_comp_zeta hjs hV (continuous_jF_l hχc hχd hξc hξd κ i)).stronglyMeasurable
  have hq : ∀ i i', StronglyMeasurable[b3Sigma W j np] fun y =>
      (jF χ ξ κ (zeta b E s h τ m W Vs j y)).q i i' := fun i i' =>
    (measurable_comp_zeta hjs hV
      (continuous_jF_q hχc hχd hχdd hξc hξd hξdd κ i i')).stronglyMeasurable
  have hlb : ∀ y i, ‖(jF χ ξ κ (zeta b E s h τ m W Vs j y)).l i‖ ≤ C := fun y i =>
    (hCb _ (adm_zeta b E s h τ m W Vs j y)).2.1 i
  have hqb : ∀ y i i', ‖(jF χ ξ κ (zeta b E s h τ m W Vs j y)).q i i'‖ ≤ C := fun y i i' =>
    (hCb _ (adm_zeta b E s h τ m W Vs j y)).2.2 i i'
  -- the basic increments
  have hβ2 : ∀ i, MemLp (A'.indicator fun y => betaS b E s h τ m W Vs j y i) 2 μ := by
    intro i
    rcases i with e | a | a
    · have h1 := (hL2 (Sum.inl e)).ae_eq (indicator_ae_eq_of_ae_eq_set hAA)
      refine h1.congr_norm ?_ ?_ |>.mono_measure le_rfl
      · exact ((measurable_betaS hV' _).indicator hAm).aestronglyMeasurable
      · exact Eventually.of_forall fun y => by
          by_cases hy : y ∈ A' <;> simp [A', hy, betaS_inl b E s h τ m W Vs hj]
    · have h1 := (hL2 (Sum.inr a)).ae_eq (indicator_ae_eq_of_ae_eq_set hAA)
      refine h1.congr_norm ?_ ?_ |>.mono_measure le_rfl
      · exact ((measurable_betaS hV' _).indicator hAm).aestronglyMeasurable
      · exact Eventually.of_forall fun y => by
          by_cases hy : y ∈ A' <;> simp [A', hy, betaS_K b E s h τ m W Vs hj]
    · have h1 := (hL2 (Sum.inr a)).ae_eq (indicator_ae_eq_of_ae_eq_set hAA)
      refine h1.congr_norm ?_ ?_ |>.mono_measure le_rfl
      · exact ((measurable_betaS hV' _).indicator hAm).aestronglyMeasurable
      · refine Eventually.of_forall fun y => ?_
        by_cases hy : y ∈ A' <;> simp [A', hy, betaS_Kc b E s h τ m W Vs hj]
  have hβ : ∀ i, Integrable (A'.indicator fun y => betaS b E s h τ m W Vs j y i) μ :=
    fun i => (hβ2 i).integrable one_le_two
  have hββ : ∀ i i', Integrable (A'.indicator fun y =>
      betaS b E s h τ m W Vs j y i * betaS b E s h τ m W Vs j y i') μ := fun i i' => by
    rw [indicator_mul']; exact (hβ2 i).integrable_mul (hβ2 i')
  -- the coefficients on the alive set
  have hcoef : ∀ y ∈ A', (∀ i, ‖dvec b E (b3ClosedGramAt b E s h τ m W j Vs y) i‖ ≤ CR) ∧
      ∀ i i', ‖Bmat b E (b3ClosedGramAt b E s h τ m W j Vs y) i i'‖ ≤ CR := fun y hy =>
    hCR _ (gram_bound_of_alive hjs hy)
  have hwn : ‖(W : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_natCast]
    rcases Nat.eq_zero_or_pos W with h0 | h0
    · simp [h0]
    · exact inv_le_one_of_one_le₀ (by exact_mod_cast h0)
  have hd : ∀ i, Integrable (A'.indicator fun y =>
      (W : ℂ)⁻¹ * dvec b E (b3ClosedGramAt b E s h τ m W j Vs y) i) μ := fun i => by
    refine Integrable.of_bound ((((measurable_comp_gram hV' (continuous_dvec b E i)).const_mul
      _).indicator hAm).aestronglyMeasurable) CR (Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ A'
    · rw [Set.indicator_of_mem hy, norm_mul]
      exact (mul_le_mul hwn ((hcoef y hy).1 i) (norm_nonneg _) zero_le_one).trans (by simp)
    · rw [Set.indicator_of_notMem hy, norm_zero]; exact hCR0
  have hB : ∀ i i', Integrable (A'.indicator fun y =>
      (W : ℂ)⁻¹ * Bmat b E (b3ClosedGramAt b E s h τ m W j Vs y) i i') μ := fun i i' => by
    refine Integrable.of_bound ((((measurable_comp_gram hV' (continuous_Bmat b E i i')).const_mul
      _).indicator hAm).aestronglyMeasurable) CR (Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ A'
    · rw [Set.indicator_of_mem hy, norm_mul]
      exact (mul_le_mul hwn ((hcoef y hy).2 i i') (norm_nonneg _) zero_le_one).trans (by simp)
    · rw [Set.indicator_of_notMem hy, norm_zero]; exact hCR0
  -- the remainder
  have hF : ∀ k, closeLen s W ≤ k → Measurable fun y => κ.fn χ ξ (zeta b E s h τ m W Vs k y) :=
    fun k hk => (measurable_comp_zeta hk hV (κ.continuous_fn hχc hξc)).mono (gen_sigma_le W k np)
      le_rfl
  have hFb : ∀ k y, ‖κ.fn χ ξ (zeta b E s h τ m W Vs k y)‖ ≤ C := fun k y =>
    (hCb _ (adm_zeta b E s h τ m W Vs k y)).1
  have hrem : Integrable (A'.indicator (remS b E s h τ m W Vs χ ξ κ j)) μ := by
    have e : A'.indicator (remS b E s h τ m W Vs χ ξ κ j) = fun y =>
        A'.indicator (fun y => κ.fn χ ξ (zeta b E s h τ m W Vs (j + 1) y) -
          κ.fn χ ξ (zeta b E s h τ m W Vs j y)) y -
        ∑ i, (jF χ ξ κ (zeta b E s h τ m W Vs j y)).l i *
          A'.indicator (fun y => betaS b E s h τ m W Vs j y i) y -
        ∑ i, ∑ i', (jF χ ξ κ (zeta b E s h τ m W Vs j y)).q i i' *
          A'.indicator (fun y => betaS b E s h τ m W Vs j y i *
            betaS b E s h τ m W Vs j y i') y := by
      funext y
      by_cases hy : y ∈ A'
      · simp [Set.indicator_of_mem hy, remS, lin, quad]
      · simp [Set.indicator_of_notMem hy]
    rw [e]
    refine ((Integrable.of_bound ((((hF _ (by omega)).sub (hF _ hjs)).indicator
      hAm).aestronglyMeasurable) (C + C) (Eventually.of_forall fun y => ?_)).sub
      (integrable_finsetSum _ fun i _ => (hβ i).bdd_mul ((hl i).mono hm).aestronglyMeasurable
        (Eventually.of_forall fun y => hlb y i))).sub
      (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun i' _ =>
        (hββ i i').bdd_mul ((hq i i').mono hm).aestronglyMeasurable
          (Eventually.of_forall fun y => hqb y i i'))
    by_cases hy : y ∈ A'
    · rw [Set.indicator_of_mem hy]
      exact (norm_sub_le _ _).trans (add_le_add (hFb _ _) (hFb _ _))
    · rw [Set.indicator_of_notMem hy, norm_zero]; linarith
  have hremb : ∫⁻ y, ‖A'.indicator (remS b E s h τ m W Vs χ ξ κ j) y‖ₑ ∂μ ≤
      ENNReal.ofReal C * ∫⁻ y, A'.indicator
        (fun y => ENNReal.ofReal (nrm (betaS b E s h τ m W Vs j y) ^ 3)) y ∂μ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun y => ?_
    by_cases hy : y ∈ A'
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, ← ENNReal.ofReal_mul hC0,
        ← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 := hCr _ _ _ (adm_zeta b E s h τ m W Vs j y)
        (by rw [← zeta_succ b E s h τ m W Vs hjs]; exact adm_zeta b E s h τ m W Vs (j + 1) y)
        (diagReal_dYs b E s h τ m W Vs j y)
      rw [← zeta_succ b E s h τ m W Vs hjs] at h1
      exact h1
    · simp [Set.indicator_of_notMem hy]
  -- assemble
  have e : A'.indicator (dStep b E s h τ m W Vs χ ξ κ j) = A'.indicator (fun y =>
      lin (jF χ ξ κ (zeta b E s h τ m W Vs j y)).l (betaS b E s h τ m W Vs j y) +
        quad (jF χ ξ κ (zeta b E s h τ m W Vs j y)).q (betaS b E s h τ m W Vs j y) +
        remS b E s h τ m W Vs χ ξ κ j y -
        (W : ℂ)⁻¹ * (lin (jF χ ξ κ (zeta b E s h τ m W Vs j y)).l
            (dvec b E (b3ClosedGramAt b E s h τ m W j Vs y)) +
          ∑ i, ∑ i', (jF χ ξ κ (zeta b E s h τ m W Vs j y)).q i i' *
            Bmat b E (b3ClosedGramAt b E s h τ m W j Vs y) i i')) := by
    congr 1; funext y; exact dStep_eq b E s h τ m W Vs χ ξ κ j y
  rw [e]
  have habs := enorm_integral_step_le hm hA (fun y => betaS b E s h τ m W Vs j y)
    (fun y => (jF χ ξ κ (zeta b E s h τ m W Vs j y)).l)
    (fun y => dvec b E (b3ClosedGramAt b E s h τ m W j Vs y))
    (fun y => (jF χ ξ κ (zeta b E s h τ m W Vs j y)).q)
    (fun y => Bmat b E (b3ClosedGramAt b E s h τ m W j Vs y))
    (remS b E s h τ m W Vs χ ξ κ j) g (W : ℂ)⁻¹ hC0 hCg hl hq hg hlb hqb hgb hβ hββ hd hB hrem
  refine habs.trans (add_le_add (le_of_eq ?_) (mul_le_mul' le_rfl hremb))
  congr 2
  · exact sum_congr rfl fun i _ => e1S_eq s h τ m R W Vs hb hE1 hE2 hj i
  · exact sum_congr rfl fun i _ => sum_congr rfl fun i' _ =>
      e2S_eq s h τ m R W Vs hb hE1 hE2 hj i i'

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram.IdentK.FW
