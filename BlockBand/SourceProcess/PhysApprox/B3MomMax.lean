module

public import BlockBand.SourceProcess.PhysApprox.B3MomTight
public import BlockBand.SourceProcess.PhysApprox.B3Bridge
public import BlockBand.SourceProcess.PhysApprox.B3Pins2

/-!
# The maximal stopped `𝒦` moment: reduction to three parts

Fix an entry `ij`. With `X_j = (𝒦_cl)_{j,ij}`, the stopped step `Z_j = 1_{A_j}(X_{j+1} − X_j)`
(`kStopStep`), its conditional mean `e_j = E[Z_j | b3Sigma j]` (`kStopMean`) and its centred
part `d_j = Z_j − e_j`:

* **`kStop_telescope`**: `X_{n_s} = 0` (`b3ClosedKAt_start`) and `A_j ⊆ A_i` for `i ≤ j` give
  `X_{j+1} = Σ_{n_s ≤ i ≤ j} Z_i` on `A_j`;
* **`complexKStoppedMomentMax_of_parts`**: `ComplexKStoppedMomentMax` follows from three
  estimates, by splitting the steps into births and non-births and
  `(a + b + c)⁴ ≤ 27(a⁴ + b⁴ + c⁴)`:
  - `KStopMartMax`: the maximal fourth moment of the centred sum `Σ_{non-birth} d_i`
    (Doob and Burkholder; `TargetMartMax` below);
  - `KStopMeanSum`: the fourth moment of the summed conditional means (Minkowski; mean
    size `C(δ₀ + W⁻²) Tr M_pr`);
  - `KStopBirthSum`: the fourth moment of the summed births (finitely many).

No step uses the per-length stopped fourth moment, and nothing here uses the final-time resolvent
`(1 − zN_j)⁻¹`: the steps `Z_j` are those of the closed process, to be estimated in the time-`s`
representation.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ClosedPath
open scoped NNReal ENNReal

variable {W np K : ℕ}

/-!
## The stopped steps, their means and their centred parts
-/

/-- The stopped step `Z_i = 1_{A_i}(X_{i+1} − X_i)` of the entry `ij` of the closed `𝒦`. -/
def kStopStep (b E s h : ℝ) (τ m : Fin np → ℝ) (R : ℝ) (W i : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (ij : Fin np × Fin np)
    (y : ProbedPath W np × ℝ) : ℂ :=
  (b3Alive b E s h τ m R W i Vs).indicator (fun y =>
    b3ClosedKAt b E s h τ m W (i + 1) y ij.1 ij.2 - b3ClosedKAt b E s h τ m W i y ij.1 ij.2) y

/-- The conditional mean `e_i = E[Z_i | b3Sigma i]` under `closedLaw`. -/
def kStopMean (b E s h : ℝ) (τ m : Fin np → ℝ) (R : ℝ) (W i : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (ij : Fin np × Fin np) :
    ProbedPath W np × ℝ → ℂ :=
  (closedLaw b W np)[kStopStep b E s h τ m R W i Vs ij | b3Sigma W i np]

/-- The centred part `d_i = Z_i − e_i`. -/
def kStopMart (b E s h : ℝ) (τ m : Fin np → ℝ) (R : ℝ) (W i : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (ij : Fin np × Fin np)
    (y : ProbedPath W np × ℝ) : ℂ :=
  kStopStep b E s h τ m R W i Vs ij y - kStopMean b E s h τ m R W i Vs ij y

/-!
## Telescoping on the alive set
-/

theorem b3Alive_anti {b E s h : ℝ} {τ m : Fin np → ℝ} {R : ℝ} {W : ℕ}
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} {i j : ℕ} (hij : i ≤ j)
    {y : ProbedPath W np × ℝ} (hy : y ∈ b3Alive b E s h τ m R W j Vs) :
    y ∈ b3Alive b E s h τ m R W i Vs :=
  ⟨hy.1, fun k hk1 hk2 => hy.2 k hk1 (hk2.trans hij)⟩

/-- **Telescoping**: on `A_j`, `X_{j+1} = Σ_{n_s ≤ i ≤ j} Z_i` (`X_{n_s} = 0`,
`b3ClosedKAt_start`). -/
theorem kStop_telescope {b E s h : ℝ} {τ m : Fin np → ℝ} (hτ : ∀ i, s < τ i) (R : ℝ) (W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (ij : Fin np × Fin np)
    {j : ℕ} (hj : closeLen s W ≤ j) {y : ProbedPath W np × ℝ}
    (hy : y ∈ b3Alive b E s h τ m R W j Vs) :
    b3ClosedKAt b E s h τ m W (j + 1) y ij.1 ij.2 =
      ∑ i ∈ Finset.Ico (closeLen s W) (j + 1), kStopStep b E s h τ m R W i Vs ij y := by
  induction j, hj using Nat.le_induction with
  | base =>
      rw [Nat.Ico_succ_singleton, Finset.sum_singleton, kStopStep,
        Set.indicator_of_mem hy, b3ClosedKAt_start hτ, Matrix.zero_apply, sub_zero]
  | succ j hj ih =>
      rw [Finset.sum_Ico_succ_top (by omega), ← ih (b3Alive_anti (Nat.le_succ j) hy),
        kStopStep, Set.indicator_of_mem hy]
      ring

/-!
## The pointwise bound
-/

theorem add_pow_four_le_three (a c d : ℝ≥0∞) :
    (a + c + d) ^ 4 ≤ 27 * (a ^ 4 + c ^ 4 + d ^ 4) := by
  have h := ENNReal.rpow_sum_le_const_mul_sum_rpow (s := Finset.univ) (f := ![a, c, d])
    (p := 4) (by norm_num)
  have e : ∀ x : ℝ≥0∞, x ^ (4 : ℝ) = x ^ (4 : ℕ) := fun x => by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  simp only [Fin.sum_univ_three, Finset.card_univ, Fintype.card_fin, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h
  rw [e, e, e, e, show (4 : ℝ) - 1 = ((3 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast] at h
  calc (a + c + d) ^ 4 ≤ ((3 : ℕ) : ℝ≥0∞) ^ 3 * (a ^ 4 + c ^ 4 + d ^ 4) := h
    _ = 27 * (a ^ 4 + c ^ 4 + d ^ 4) := by norm_num

/-- The stopped sum up to `n` is split into the centred non-birth sum, the non-birth means and
the births; the last two are bounded by their totals up to `N ≥ n`. -/
theorem enorm_kStopSum_le (b E s h : ℝ) (τ m : Fin np → ℝ) (R : ℝ) (W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (ij : Fin np × Fin np)
    {n N : ℕ} (hn : n ≤ N) (y : ProbedPath W np × ℝ) :
    ‖∑ i ∈ Finset.Ico (closeLen s W) n, kStopStep b E s h τ m R W i Vs ij y‖ₑ ≤
      ‖∑ i ∈ (Finset.Ico (closeLen s W) n).filter (fun i => ¬ IsBirthStep τ W i),
          kStopMart b E s h τ m R W i Vs ij y‖ₑ +
        ∑ i ∈ (Finset.Ico (closeLen s W) N).filter (fun i => ¬ IsBirthStep τ W i),
          ‖kStopMean b E s h τ m R W i Vs ij y‖ₑ +
        ∑ i ∈ (Finset.Ico (closeLen s W) N).filter (fun i => IsBirthStep τ W i),
          ‖kStopStep b E s h τ m R W i Vs ij y‖ₑ := by
  set Z := fun i => kStopStep b E s h τ m R W i Vs ij y
  set e := fun i => kStopMean b E s h τ m R W i Vs ij y
  have hsub : Finset.Ico (closeLen s W) n ⊆ Finset.Ico (closeLen s W) N :=
    Finset.Ico_subset_Ico_right hn
  have hsplit : ∑ i ∈ Finset.Ico (closeLen s W) n, Z i =
      ∑ i ∈ (Finset.Ico (closeLen s W) n).filter (fun i => ¬ IsBirthStep τ W i),
          kStopMart b E s h τ m R W i Vs ij y +
        ∑ i ∈ (Finset.Ico (closeLen s W) n).filter (fun i => ¬ IsBirthStep τ W i), e i +
        ∑ i ∈ (Finset.Ico (closeLen s W) n).filter (fun i => IsBirthStep τ W i), Z i := by
    rw [← Finset.sum_add_distrib, add_comm, ← Finset.sum_filter_add_sum_filter_not _
      (fun i => IsBirthStep τ W i)]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [kStopMart, Z, e]
    ring
  rw [hsplit]
  refine (enorm_add_le _ _).trans (add_le_add ((enorm_add_le _ _).trans
    (add_le_add le_rfl ?_)) ?_)
  · exact (enorm_sum_le _ _).trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset_filter _ hsub) fun _ _ _ => zero_le)
  · exact (enorm_sum_le _ _).trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset_filter _ hsub) fun _ _ _ => zero_le)

/-!
## The three parts
-/

/-- **`KStopMartMax`** (Burkholder for the centred increments):
the maximal fourth moment of the centred non-birth stopped sum of every `𝒦` entry is bounded,
uniformly in `W`. `TargetMartMax` reduces it to per-step fourth moments. -/
def KStopMartMax : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ C : ℝ, ∀ᶠ W in atTop, ∀ ij : Fin np × Fin np,
      ∫⁻ y, ⨆ n ∈ Finset.Icc (closeLen s W) ⌊(W : ℝ) * T⌋₊,
          ‖∑ i ∈ (Finset.Ico (closeLen s W) n).filter (fun i => ¬ IsBirthStep τ W i),
            kStopMart b E s h τ m R W i (Vs W) ij y‖ₑ ^ 4 ∂closedLaw b W np ≤ ENNReal.ofReal C

/-- **`KStopMeanSum`** (mean size `C(δ₀ + W⁻²) Tr M_pr`, Minkowski for the
summed means): the fourth moment of the summed conditional means over the
non-birth steps is bounded, uniformly in `W`. -/
def KStopMeanSum : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ C : ℝ, ∀ᶠ W in atTop, ∀ ij : Fin np × Fin np,
      ∫⁻ y, (∑ i ∈ (Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊).filter
          (fun i => ¬ IsBirthStep τ W i), ‖kStopMean b E s h τ m R W i (Vs W) ij y‖ₑ) ^ 4
        ∂closedLaw b W np ≤ ENNReal.ofReal C

/-- **`KStopBirthSum`** (at birth the fresh diagonal is `≈ am`, old/new
cross entries are small; at most `np` birth steps): the fourth moment of the summed stopped birth
steps is bounded, uniformly in `W`. -/
def KStopBirthSum : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ C : ℝ, ∀ᶠ W in atTop, ∀ ij : Fin np × Fin np,
      ∫⁻ y, (∑ i ∈ (Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊).filter
          (fun i => IsBirthStep τ W i), ‖kStopStep b E s h τ m R W i (Vs W) ij y‖ₑ) ^ 4
        ∂closedLaw b W np ≤ ENNReal.ofReal C

/-- **`KStopStepFour`** (the centred increment has `L^p`
size `C_p Tr M_pr/√W`, at `p = 4`): `W` times the summed stopped fourth moments of the non-birth
steps is bounded. Rate form of the `𝒦` rows of `ComplexClosedFourth`. -/
def KStopStepFour : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ C : ℝ, ∀ᶠ W in atTop, ∀ ij : Fin np × Fin np,
      ((W : ℕ) : ℝ≥0∞) * ∑ i ∈ (Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊).filter
          (fun i => ¬ IsBirthStep τ W i),
        ∫⁻ y, ‖kStopStep b E s h τ m R W i (Vs W) ij y‖ₑ ^ 4 ∂closedLaw b W np ≤
          ENNReal.ofReal C

/-- **`TargetMartMax`**: Doob's `L⁴` maximal inequality
(`Stochastic.SDE.DoobLp.martingale_eLpNorm_runMax_norm_le`) and the crude Burkholder bound
`E|Σ_{i<N} d_i|⁴ ≤ C N Σ E|d_i|⁴` (`E|d_i|⁴ ≤ 16 E|Z_i|⁴`; cf.
`Generator.integral_modSum_pow_four_le` for bounded real steps) give `KStopMartMax` from the
per-step estimate, since `N ≤ TW`. Needs the adaptedness of `Z_i` to `b3Sigma (i + 1)` (closed
objects at length `i + 1`, time-`s` frame) and `b3Sigma` monotone. -/
def TargetMartMax : Prop := KStopStepFour → KStopMartMax

/-!
## A.e. measurability
-/

theorem measurable_b3Sigma_map (W i np : ℕ) :
    Measurable fun y : ProbedPath W np × ℝ =>
      (Transmission.Bridge.pastCoords W i y.1.1, y.1.2, y.2) :=
  ((Transmission.Bridge.measurable_pastCoords W i).comp (measurable_fst.comp measurable_fst)).prodMk
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd)

theorem measurable_kStopMean (b E s h : ℝ) (τ m : Fin np → ℝ) (R : ℝ) (W i : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (ij : Fin np × Fin np) :
    Measurable (kStopMean b E s h τ m R W i Vs ij) :=
  (stronglyMeasurable_condExp.mono (measurable_b3Sigma_map W i np).comap_le).measurable

/-- The stopped step is a.e. measurable (alive set a.e. Borel, `b3Alive_ae_eq`). -/
theorem aemeasurable_kStopStep {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) (s h : ℝ)
    (τ m : Fin np → ℝ) (R : ℝ) (W i : ℕ)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} (hV : Measurable Vs)
    (ij : Fin np × Fin np) :
    AEMeasurable (kStopStep b E s h τ m R W i Vs ij) (closedLaw b W np) := by
  have hf : Measurable fun y : ProbedPath W np × ℝ =>
      b3ClosedKAt b E s h τ m W (i + 1) y ij.1 ij.2 - b3ClosedKAt b E s h τ m W i y ij.1 ij.2 :=
    (measurable_b3ClosedKAt b E s h τ m W (i + 1)).eval_matrix.sub
      (measurable_b3ClosedKAt b E s h τ m W i).eval_matrix
  exact (hf.indicator (measurableSet_b3AliveM b E s h τ m R W i hV)).aemeasurable.congr
    (indicator_ae_eq_of_ae_eq_set (b3Alive_ae_eq hb hE1 hE2 s h τ m R W i Vs)).symm

/-!
## The reduction
-/

/-- **The maximal stopped `𝒦` moment from the three parts** `KStopMartMax`, `KStopMeanSum`,
`KStopBirthSum`; the conclusion is the body of `ComplexKStoppedMomentMax`. -/
theorem kStoppedMax_of_parts (hM : KStopMartMax) (hE : KStopMeanSum) (hB : KStopBirthSum) :
    ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
      (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
      FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ C : ℝ, ∀ᶠ W in atTop, ∀ ij : Fin np × Fin np,
        ∫⁻ y, ⨆ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊,
            (b3Alive b E s h τ m R W j (Vs W)).indicator
              (fun y => ‖b3ClosedKAt b E s h τ m W (j + 1) y ij.1 ij.2‖ₑ ^ 4) y
          ∂closedLaw b W np ≤ ENNReal.ofReal C := by
  intro b E np τ m T s h K Vs hF R
  have hτ := hF.2.2.1
  obtain ⟨C₁, h₁⟩ := hM b E np τ m T s h K Vs hF R
  obtain ⟨C₂, h₂⟩ := hE b E np τ m T s h K Vs hF R
  obtain ⟨C₃, h₃⟩ := hB b E np τ m T s h K Vs hF R
  refine ⟨27 * (max C₁ 0 + max C₂ 0 + max C₃ 0), ?_⟩
  have hb1 : b < 1 := by linarith [hF.1.2.1]
  filter_upwards [h₁, h₂, h₃, hF.2.2.2.2.2] with W hW1 hW2 hW3 hVW ij
  have hmV : Measurable (Vs W) :=
    hVW.1.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  set N := ⌊(W : ℝ) * T⌋₊
  set fM : ProbedPath W np × ℝ → ℝ≥0∞ := fun y => ⨆ n ∈ Finset.Icc (closeLen s W) N,
    ‖∑ i ∈ (Finset.Ico (closeLen s W) n).filter (fun i => ¬ IsBirthStep τ W i),
      kStopMart b E s h τ m R W i (Vs W) ij y‖ₑ
  set fE : ProbedPath W np × ℝ → ℝ≥0∞ := fun y =>
    ∑ i ∈ (Finset.Ico (closeLen s W) N).filter (fun i => ¬ IsBirthStep τ W i),
      ‖kStopMean b E s h τ m R W i (Vs W) ij y‖ₑ
  set fB : ProbedPath W np × ℝ → ℝ≥0∞ := fun y =>
    ∑ i ∈ (Finset.Ico (closeLen s W) N).filter (fun i => IsBirthStep τ W i),
      ‖kStopStep b E s h τ m R W i (Vs W) ij y‖ₑ
  have hpt : ∀ y, (⨆ j ∈ Finset.Ico (closeLen s W) N,
      (b3Alive b E s h τ m R W j (Vs W)).indicator
        (fun y => ‖b3ClosedKAt b E s h τ m W (j + 1) y ij.1 ij.2‖ₑ ^ 4) y) ≤
      27 * ((⨆ n ∈ Finset.Icc (closeLen s W) N,
        ‖∑ i ∈ (Finset.Ico (closeLen s W) n).filter (fun i => ¬ IsBirthStep τ W i),
          kStopMart b E s h τ m R W i (Vs W) ij y‖ₑ ^ 4) + fE y ^ 4 + fB y ^ 4) := by
    intro y
    refine iSup₂_le fun j hj => ?_
    obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.1 hj
    by_cases hy : y ∈ b3Alive b E s h τ m R W j (Vs W)
    · rw [Set.indicator_of_mem hy, kStop_telescope hτ R W (Vs W) ij hj1 hy]
      have hb := enorm_kStopSum_le b E s h τ m R W (Vs W) ij (n := j + 1) (N := N) hj2 y
      have hmem : j + 1 ∈ Finset.Icc (closeLen s W) N :=
        Finset.mem_Icc.2 ⟨by omega, hj2⟩
      have hM' : ‖∑ i ∈ (Finset.Ico (closeLen s W) (j + 1)).filter
            (fun i => ¬ IsBirthStep τ W i), kStopMart b E s h τ m R W i (Vs W) ij y‖ₑ ^ 4 ≤
          ⨆ n ∈ Finset.Icc (closeLen s W) N,
            ‖∑ i ∈ (Finset.Ico (closeLen s W) n).filter (fun i => ¬ IsBirthStep τ W i),
              kStopMart b E s h τ m R W i (Vs W) ij y‖ₑ ^ 4 :=
        le_iSup₂ (f := fun n (_ : n ∈ Finset.Icc (closeLen s W) N) =>
          ‖∑ i ∈ (Finset.Ico (closeLen s W) n).filter (fun i => ¬ IsBirthStep τ W i),
            kStopMart b E s h τ m R W i (Vs W) ij y‖ₑ ^ 4) (j + 1) hmem
      calc _ ≤ (‖∑ i ∈ (Finset.Ico (closeLen s W) (j + 1)).filter
              (fun i => ¬ IsBirthStep τ W i), kStopMart b E s h τ m R W i (Vs W) ij y‖ₑ +
            fE y + fB y) ^ 4 := pow_le_pow_left₀ zero_le hb 4
        _ ≤ 27 * (‖∑ i ∈ (Finset.Ico (closeLen s W) (j + 1)).filter
              (fun i => ¬ IsBirthStep τ W i), kStopMart b E s h τ m R W i (Vs W) ij y‖ₑ ^ 4 +
            fE y ^ 4 + fB y ^ 4) := add_pow_four_le_three _ _ _
        _ ≤ _ := by gcongr
    · rw [Set.indicator_of_notMem hy]
      exact zero_le
  have hfE : Measurable fun y => fE y ^ 4 :=
    (Finset.measurable_sum _ fun i _ =>
      (measurable_kStopMean b E s h τ m R W i (Vs W) ij).enorm).pow_const 4
  have hfB : AEMeasurable (fun y => fB y ^ 4) (closedLaw b W np) :=
    (Finset.aemeasurable_fun_sum _ fun i _ => (aemeasurable_kStopStep hb1 hF.1.2.2.1
      hF.1.2.2.2.1 s h τ m R W i hmV ij).enorm).pow_const 4
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_right' _ hfB,
    lintegral_add_right _ hfE]
  calc 27 * (∫⁻ y, (⨆ n ∈ Finset.Icc (closeLen s W) N,
            ‖∑ i ∈ (Finset.Ico (closeLen s W) n).filter (fun i => ¬ IsBirthStep τ W i),
              kStopMart b E s h τ m R W i (Vs W) ij y‖ₑ ^ 4) ∂closedLaw b W np +
          ∫⁻ y, fE y ^ 4 ∂closedLaw b W np + ∫⁻ y, fB y ^ 4 ∂closedLaw b W np)
        ≤ 27 * (ENNReal.ofReal (max C₁ 0) + ENNReal.ofReal (max C₂ 0) +
            ENNReal.ofReal (max C₃ 0)) := by
          gcongr
          · exact (hW1 ij).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
          · exact (hW2 ij).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
          · exact (hW3 ij).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
      _ = ENNReal.ofReal (27 * (max C₁ 0 + max C₂ 0 + max C₃ 0)) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add (by positivity)
            (by positivity), ENNReal.ofReal_add (by positivity) (by positivity)]
          norm_num

/-- **`ComplexKStoppedMomentMax` from the three parts** (`KStopMartMax`, `KStopMeanSum`,
`KStopBirthSum`). -/
theorem complexKStoppedMomentMax_of_parts (hM : KStopMartMax) (hE : KStopMeanSum)
    (hB : KStopBirthSum) : ComplexKStoppedMomentMax :=
  kStoppedMax_of_parts hM hE hB

end BlockBand.SourceProcess.PhysApprox.B3
