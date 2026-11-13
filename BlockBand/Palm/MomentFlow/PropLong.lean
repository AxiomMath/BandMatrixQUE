module

public import BlockBand.Palm.MomentFlow.Tail6
public import BlockBand.Palm.MomentFlow.Steps2LongUnif
public import BlockBand.Palm.GoodEventHolds
public import BlockBand.Palm.MomentFlow.PropBulk

/-!
# Long-jump bounds `e` and `K` for the long-versus-short comparison

* `longFlowRate`, `full_sub_short_eq_long`: `𝓑F - 𝓢F = 𝓑_{long}F` along every sample path.
* **`longGen_single_le`** (`r = 1`): `|𝓑_{mask}f(δ_i)| ≤ Σ_{P i j} c_ij f(δ_j) + (Σ_{P i j} c_ij) f(δ_i)`.
* **`longGen_local_le`** (every `r`): `|𝓑_{mask}f(ζ)| ≤ Σ_i ζ_i Σ_{j≠i, P i j} c_ij(1+ζ_j)f(ζ^{ij})
  + (r+1) f(ζ) Σ_i ζ_i Σ_{P i j} c_ij` (`f ≥ 0`), the interface for the removal identity.
* **`longGen_global_le`** (the bound `K`): `|𝓑_{mask}f(ζ)| ≤ 2B(r+1)rL` from `|f| ≤ B` on the
  sector and masked row sums `≤ L`.
* **`longCoupling_good`** (from `GaussianLpGradient`, `MultivariateGaussianIBP` via
  `spectralGoodEvent_s8`): one **𝓛-measurable** bad set `≤ N^{-D}` off which, at all times of
  `[a,c]`, long pairs are separated (`c₁|i-j|/N`) and `longCoupling ≤ CN/ℓ` for every label. The
  𝓛-measurability goes through the continuous truncated rates `truncRate N (c₁ℓ/N)`, equal to the
  exact rates on the separation event.
* **`long_coupling_all_labels`**: `long_coupling_uniform` with one bad set for all
  labels (union at level `D + 1`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open MeasureTheory ProbabilityTheory Set Filter Finset
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Internal.Contracts.Inputs BlockBand.Palm BlockBand.Palm.RelativeLocalization

variable {N : ℕ}

/-- Long rates `c_ij 1{|i-j| ≥ ℓ}`. -/
def longFlowRate (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N) (ℓ : ℕ) (σ : ℝ) :
    Fin N → Fin N → ℝ :=
  maskRate (fun i j => ¬ labelDist i j < ℓ) (flowRate F a ω σ)

theorem full_sub_short_eq_long (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N) (ℓ : ℕ)
    (σ : ℝ) (f : Occ N → ℝ) (ζ : Occ N) :
    momentGenerator (flowRate F a ω σ) f ζ - momentGenerator (shortFlowRate F a ω ℓ σ) f ζ =
      momentGenerator (longFlowRate F a ω ℓ σ) f ζ := by
  have h := flowMomentGenerator_eq_short_add_long F a ω ℓ σ f ζ
  unfold flowMomentGenerator shortFlowMomentGenerator at h
  rw [h, longFlowRate]; ring

theorem sum_erase_maskRate_le {P : Fin N → Fin N → Prop} [DecidableRel P] {c : Fin N → Fin N → ℝ}
    (hc : ∀ i j, 0 ≤ c i j) (i : Fin N) :
    ∑ j ∈ univ.erase i, maskRate P c i j ≤ ∑ j ∈ univ.filter (P i), c i j := by
  rw [Finset.sum_filter]
  refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun j _ _ => ?_).trans
    (le_of_eq (Finset.sum_congr rfl fun j _ => by simp [maskRate]))
  unfold maskRate; split_ifs <;> simp [hc]

/-- **Global long-jump bound**: on the `r`-sector, with `|f| ≤ B` on the sector and masked row
sums `≤ L`, `|𝓑_{mask} f(ζ)| ≤ 2B(r+1) r L`. -/
theorem longGen_global_le {P : Fin N → Fin N → Prop} [DecidableRel P] {c : Fin N → Fin N → ℝ}
    (hc : ∀ i j, 0 ≤ c i j) {r : ℕ} {ζ : Occ N} (hζ : ζ ∈ sector N r) {f : Occ N → ℝ} {B L : ℝ}
    (hB : ∀ η ∈ sector N r, |f η| ≤ B) (hL : ∀ i, ∑ j ∈ univ.filter (P i), c i j ≤ L) :
    |momentGenerator (maskRate P c) f ζ| ≤ 2 * B * (r + 1) * r * L := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB ζ hζ)
  have hζsum := mem_sector.1 hζ
  have hζle : ∀ j, (ζ j : ℝ) ≤ r := fun j => by
    have : ζ j ≤ r := hζsum ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    exact_mod_cast this
  have hm0 : ∀ i j, 0 ≤ maskRate P c i j := fun i j => by unfold maskRate; split_ifs <;> simp [hc]
  unfold momentGenerator
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ i, |∑ j ∈ univ.erase i, maskRate P c i j * jumpCoeff ζ i j *
      (f (move ζ i j) - f ζ)| ≤ (ζ i : ℝ) * (2 * B * (r + 1) * L) := by
    intro i
    rcases Nat.eq_zero_or_pos (ζ i) with hi | hi
    · rw [Finset.sum_eq_zero fun j _ => by rw [jumpCoeff_eq_zero_of_eq_zero ζ j hi]; ring]
      simp [hi]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j ∈ univ.erase i, |maskRate P c i j * jumpCoeff ζ i j * (f (move ζ i j) - f ζ)|
        ≤ ∑ j ∈ univ.erase i, maskRate P c i j * ((ζ i : ℝ) * (1 + r) * (2 * B)) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hij : i ≠ j := Ne.symm (Finset.mem_erase.1 hj).1
          rw [abs_mul, abs_mul, abs_of_nonneg (hm0 i j), abs_of_nonneg (jumpCoeff_nonneg ζ i j),
            mul_assoc]
          refine mul_le_mul_of_nonneg_left (mul_le_mul ?_ ?_ (abs_nonneg _) (by positivity)) (hm0 i j)
          · unfold jumpCoeff
            exact mul_le_mul_of_nonneg_left (by linarith [hζle j]) (Nat.cast_nonneg _)
          · refine (abs_sub _ _).trans ?_
            linarith [hB _ (move_mem_sector hζ hij hi), hB ζ hζ]
      _ = (∑ j ∈ univ.erase i, maskRate P c i j) * ((ζ i : ℝ) * (1 + r) * (2 * B)) :=
          (Finset.sum_mul _ _ _).symm
      _ ≤ L * ((ζ i : ℝ) * (1 + r) * (2 * B)) :=
          mul_le_mul_of_nonneg_right ((sum_erase_maskRate_le hc i).trans (hL i)) (by positivity)
      _ = (ζ i : ℝ) * (2 * B * (r + 1) * L) := by ring
  calc ∑ i, |∑ j ∈ univ.erase i, maskRate P c i j * jumpCoeff ζ i j * (f (move ζ i j) - f ζ)|
      ≤ ∑ i, (ζ i : ℝ) * (2 * B * (r + 1) * L) := Finset.sum_le_sum fun i _ => hterm i
    _ = 2 * B * (r + 1) * r * L := by
        rw [← Finset.sum_mul]
        have : ∑ i, (ζ i : ℝ) = r := by exact_mod_cast hζsum
        rw [this]; ring

/-- **Local long-jump bound at one particle**: with `f ≥ 0` on the one-particle sector,
`|𝓑_{mask} f(δ_i)| ≤ Σ_{j: P i j} c_ij f(δ_j) + (Σ_{j: P i j} c_ij) f(δ_i)`. -/
theorem longGen_single_le {P : Fin N → Fin N → Prop} [DecidableRel P] {c : Fin N → Fin N → ℝ}
    (hc : ∀ i j, 0 ≤ c i j) {f : Occ N → ℝ} (hf : ∀ j : Fin N, 0 ≤ f (Pi.single j 1)) (i : Fin N) :
    |momentGenerator (maskRate P c) f (Pi.single i 1)| ≤
      ∑ j ∈ univ.filter (P i), c i j * f (Pi.single j 1) +
        (∑ j ∈ univ.filter (P i), c i j) * f (Pi.single i 1) := by
  classical
  have hm0 : ∀ i j, 0 ≤ maskRate P c i j := fun i j => by unfold maskRate; split_ifs <;> simp [hc]
  unfold momentGenerator
  rw [Finset.sum_eq_single i]
  · have e : ∀ j ∈ univ.erase i, maskRate P c i j * jumpCoeff (Pi.single i 1) i j *
        (f (move (Pi.single i 1) i j) - f (Pi.single i 1)) =
        maskRate P c i j * (f (Pi.single j 1) - f (Pi.single i 1)) := by
      intro j hj
      have hij : i ≠ j := Ne.symm (Finset.mem_erase.1 hj).1
      rw [move_single i j hij]
      simp [jumpCoeff, Ne.symm hij]
    rw [Finset.sum_congr rfl e]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j ∈ univ.erase i, |maskRate P c i j * (f (Pi.single j 1) - f (Pi.single i 1))|
        ≤ ∑ j ∈ univ.erase i, (maskRate P c i j * f (Pi.single j 1) +
            maskRate P c i j * f (Pi.single i 1)) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul, abs_of_nonneg (hm0 i j), ← mul_add]
          refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans ?_) (hm0 i j)
          rw [abs_of_nonneg (hf j), abs_of_nonneg (hf i)]
      _ ≤ ∑ j ∈ univ.filter (P i), c i j * f (Pi.single j 1) +
            (∑ j ∈ univ.filter (P i), c i j) * f (Pi.single i 1) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul]
          refine add_le_add ?_ (mul_le_mul_of_nonneg_right (sum_erase_maskRate_le hc i) (hf i))
          rw [Finset.sum_filter]
          refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            fun j _ _ => mul_nonneg (hm0 i j) (hf j)).trans (le_of_eq ?_)
          exact Finset.sum_congr rfl fun j _ => by unfold maskRate; split_ifs <;> simp
  · intro i' _ hi'
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [jumpCoeff_eq_zero_of_eq_zero _ j (by simp [hi'])]; ring
  · simp

/-- Long-row sums as the filter form used by `longCoupling`. -/
theorem longCoupling_eq_filter (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N) (ℓ : ℕ)
    (σ : ℝ) (i : Fin N) :
    longCoupling F a ω ℓ σ i = ∑ j ∈ univ.filter (fun j => ¬ labelDist i j < ℓ), flowRate F a ω σ i j := by
  unfold longCoupling
  exact Finset.sum_congr (Finset.filter_congr fun j _ => not_lt.symm) fun _ _ => rfl

/-- **𝓛-measurable long-coupling good event** (from `GaussianLpGradient`,
`MultivariateGaussianIBP` via `spectralGoodEvent_s8`): one `pathSigma`-measurable `B`,
`P(B) ≤ N^{-D}`, off which for all `s ∈ [a,c]` and labels: long pairs are separated,
`c₁|i-j|/N ≤ |λ_i(s) - λ_j(s)|`, and `longCoupling(s,i) ≤ C N/ℓ`. -/
theorem longCoupling_good (hLp : GaussianLpGradient) (hIBP : MultivariateGaussianIBP)
    {A c r₀ s₀ v₀ : ℝ} (hK : FreshConstants c r₀ s₀ v₀) :
    ∃ c₁ C : ℝ, 0 < c₁ ∧ 0 < C ∧ ∀ D : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c E r₀ s₀ v₀ →
        let a : ℝ := c - (N : ℝ) ^ (-(1 / 100 : ℝ))
        let ℓ : ℕ := ⌊(N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)⌋₊
        ∃ B : Set (FlowSample N), MeasurableSet[pathSigma F a a c] B ∧
          flowLaw N a B ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) ∧
          ∀ ω ∉ B, ∀ s ∈ Icc a c, (∀ i j : Fin N, ℓ ≤ labelDist i j →
              c₁ * (labelDist i j : ℝ) / N ≤ |flowEigenvalue F a ω s i - flowEigenvalue F a ω s j|) ∧
            ∀ i : Fin N, longCoupling F a ω ℓ s i ≤ C * N / ℓ := by
  classical
  obtain ⟨c₁, C₁, C, b₀, hc₁, -, hC, -, hS8⟩ :=
    BlockBand.Palm.GoodEvent.spectralGoodEvent_s8 hLp hIBP A c r₀ s₀ v₀ hK
  refine ⟨c₁, C, hc₁, hC, fun D => ?_⟩
  obtain ⟨N₁, hN₁⟩ := hS8 D
  refine ⟨max N₁ 1, fun N hN F E hFC => ?_⟩
  intro a ℓ
  have hS := hN₁ N (le_of_max_le_left hN) F E hFC
  dsimp only at hS
  have hNpos : 0 < N := le_of_max_le_right hN
  have hF := hFC.1
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  have hℓ1 : 1 ≤ ℓ := Nat.le_floor (by
    rw [Nat.cast_one]; exact Real.one_le_rpow hNr (by norm_num))
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ1
  set g : ℝ := c₁ * ℓ / N with hg
  have hg0 : 0 < g := by positivity
  have ha : a ≤ c := by
    simp only [a]; linarith [Real.rpow_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N) (-(1 / 100 : ℝ))]
  set T : ℝ → FlowSample N → Fin N → ℝ := fun s ω i =>
    ∑ j ∈ univ.filter (fun j => ¬ labelDist i j < ℓ),
      truncRate N g (flowEigenvalue F a ω s i - flowEigenvalue F a ω s j) with hT
  set G1 : Set (FlowSample N) := ⋂ i : Fin N, ⋂ j : Fin N, {ω | ℓ ≤ labelDist i j → ∀ s ∈ Icc a c,
    c₁ * (labelDist i j : ℝ) / N - |flowEigenvalue F a ω s i - flowEigenvalue F a ω s j| ≤ 0}
  set G2 : Set (FlowSample N) := ⋂ i : Fin N, {ω | ∀ s ∈ Icc a c, T s ω i ≤ C * N / ℓ}
  have hmeas : ∀ s ∈ Icc a c, ∀ k, Measurable[pathSigma F a a c] fun ω => flowEigenvalue F a ω s k :=
    fun s hs k => measurable_flowEigenvalue_pathSigma F a a c hs k
  have hG1 : MeasurableSet[pathSigma F a a c] G1 := by
    refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
    by_cases hij : ℓ ≤ labelDist i j
    · convert measurableSet_forall_Icc_le (m := pathSigma F a a c)
        (f := fun s ω => c₁ * (labelDist i j : ℝ) / N -
          |flowEigenvalue F a ω s i - flowEigenvalue F a ω s j|)
        (fun s hs => ?_) (fun ω => ?_) 0 using 1
      · ext ω; exact ⟨fun h => h hij, fun h _ => h⟩
      · exact (continuous_abs.measurable.comp ((hmeas s hs i).sub (hmeas s hs j))).const_sub _
      · exact (continuous_const.sub ((continuous_flowEigenvalue hF a ω i).sub
          (continuous_flowEigenvalue hF a ω j)).abs).continuousOn
    · simp only [hij, false_implies, ofPred_true, MeasurableSet.univ]
  have hG2 : MeasurableSet[pathSigma F a a c] G2 := by
    refine MeasurableSet.iInter fun i => measurableSet_forall_Icc_le (fun s hs => ?_)
      (fun ω => ?_) _
    · exact Finset.measurable_sum _ fun j _ =>
        (continuous_truncRate hNpos hg0).measurable.comp ((hmeas s hs i).sub (hmeas s hs j))
    · exact (continuous_finsetSum _ fun j _ => (continuous_truncRate hNpos hg0).comp
        ((continuous_flowEigenvalue hF a ω i).sub (continuous_flowEigenvalue hF a ω j))).continuousOn
  have hTeq : ∀ ω s i, (∀ j : Fin N, ℓ ≤ labelDist i j →
      c₁ * (labelDist i j : ℝ) / N ≤ |flowEigenvalue F a ω s i - flowEigenvalue F a ω s j|) →
      T s ω i = longCoupling F a ω ℓ s i := by
    intro ω s i h
    rw [longCoupling_eq_filter]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hl : ℓ ≤ labelDist i j := not_lt.1 (Finset.mem_filter.1 hj).2
    have hgx : g ≤ |flowEigenvalue F a ω s i - flowEigenvalue F a ω s j| := by
      refine le_trans ?_ (h j hl)
      simp only [hg]
      gcongr
    rw [truncRate_eq hgx hg0.le]; rfl
  refine ⟨(G1 ∩ G2)ᶜ, (hG1.inter hG2).compl, ?_, ?_⟩
  · refine (measure_mono fun ω hω => ?_).trans hS
    simp only [mem_ofPred_eq]
    intro hgood
    apply hω
    refine ⟨mem_iInter.2 fun i => mem_iInter.2 fun j => fun hij s hs => ?_,
      mem_iInter.2 fun i => fun s hs => ?_⟩
    · linarith [(hgood s hs).1 i j hij]
    · rw [hTeq ω s i ((hgood s hs).1 i)]
      exact ((hgood s hs).2.2.2.2.1 i).1
  · intro ω hω s hs
    obtain ⟨h1, h2⟩ := not_not.1 hω
    have hsep : ∀ i j : Fin N, ℓ ≤ labelDist i j →
        c₁ * (labelDist i j : ℝ) / N ≤ |flowEigenvalue F a ω s i - flowEigenvalue F a ω s j| :=
      fun i j hij => by linarith [mem_iInter.1 (mem_iInter.1 h1 i) j hij s hs]
    refine ⟨hsep, fun i => ?_⟩
    rw [← hTeq ω s i (hsep i)]
    exact mem_iInter.1 h2 i s hs

/-- **`long_coupling_uniform` for all labels at once** (union over the `N` labels at level
`D + 1`). Same hypotheses and conclusion as `long_coupling_uniform`, with one bad
set for every label `i`. -/
theorem long_coupling_all_labels (hELG : ExternalLocalGUE) (hMDE : MDEBranchIdentification)
    (hLp : GaussianLpGradient) (hIBP : MultivariateGaussianIBP)
    (hDBM : ∀ N : ℕ, DysonBrownianMotion N) {A c r₀ s₀ v₀ : ℝ}
    (hK : FreshConstants c r₀ s₀ v₀) {ε : ℝ} (hε : 0 < ε) (hε5 : ε < 1 / 5) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ Cst : ℝ, 0 ≤ Cst ∧ ∀ D : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c E r₀ s₀ v₀ →
        ∀ q : Fin N → ℂ, ∀ Φ : ℝ → Occ N → FlowSample N → ℝ,
          (∀ σ ∈ Icc (c - (N : ℝ) ^ (-(1 / 100 : ℝ))) c, ∀ j : Fin N,
            Φ σ (Pi.single j 1) =ᵐ[flowLaw N (c - (N : ℝ) ^ (-(1 / 100 : ℝ)))]
              condMoment F (c - (N : ℝ) ^ (-(1 / 100 : ℝ))) c q σ (Pi.single j 1)) →
          (∀ᵐ ω ∂flowLaw N (c - (N : ℝ) ^ (-(1 / 100 : ℝ))), ∀ j : Fin N,
            ContinuousOn (fun σ => Φ σ (Pi.single j 1) ω)
              (Icc (c - (N : ℝ) ^ (-(1 / 100 : ℝ))) c)) →
          ∃ B : Set (FlowSample N),
            MeasurableSet[pathSigma F (c - (N : ℝ) ^ (-(1 / 100 : ℝ)))
              (c - (N : ℝ) ^ (-(1 / 100 : ℝ))) c] B ∧
            flowLaw N (c - (N : ℝ) ^ (-(1 / 100 : ℝ))) B ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) ∧
            (∀ ω ∉ B, ∀ s ∈ Icc (c - (N : ℝ) ^ (-(1 / 100 : ℝ))) c, ∀ i j : Fin N,
              ⌊(N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)⌋₊ ≤ labelDist i j →
              flowRate F (c - (N : ℝ) ^ (-(1 / 100 : ℝ))) ω s i j ≤ 1) ∧
            ∀ᵐ ω ∂flowLaw N (c - (N : ℝ) ^ (-(1 / 100 : ℝ))), ω ∉ B → ∀ i : Fin N,
              ∀ s ∈ Icc (c - (N : ℝ) ^ (-(1 / 100 : ℝ))) c,
              |flowEigenvalue F (c - (N : ℝ) ^ (-(1 / 100 : ℝ))) ω s i - E| < r₀ / 2 →
              ∑ j ∈ Finset.univ.filter
                  (fun j => ⌊(N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)⌋₊ ≤ labelDist i j),
                flowRate F (c - (N : ℝ) ^ (-(1 / 100 : ℝ))) ω s i j *
                  Φ s (Pi.single j 1) ω ≤
              2 / (c₁ * ⌊(N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)⌋₊ / N) * Cst *
                  quadForm (freshGamma F c E) q +
                (N : ℝ) ^ (2 - (D + 1)) * ∑ k, ‖q k‖ ^ 2 := by
  obtain ⟨c₁, hc₁, Cst, hCst, hW⟩ :=
    long_coupling_uniform hELG hMDE hLp hIBP hDBM (A := A) hK hε hε5
  refine ⟨c₁, hc₁, Cst, hCst, fun D => ?_⟩
  obtain ⟨N₀, hN₀⟩ := hW (D + 1)
  refine ⟨max N₀ 1, fun N hN F E hFC q Φ hver hcont => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (le_of_max_le_right hN)
  choose B hBm hBμ hBrate hBae using fun i : Fin N =>
    hN₀ N (le_of_max_le_left hN) F E hFC q i Φ hver hcont
  refine ⟨⋃ i, B i, MeasurableSet.iUnion hBm, ?_, ?_, ?_⟩
  · refine (measure_iUnion_le _).trans ?_
    rw [tsum_fintype]
    calc ∑ i, flowLaw N (c - (N : ℝ) ^ (-(1 / 100 : ℝ))) (B i)
        ≤ ∑ _i : Fin N, ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) := Finset.sum_le_sum fun i _ => hBμ i
      _ = ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          congr 1
          rw [neg_add, Real.rpow_add hNpos, Real.rpow_neg_one]; field_simp
  · intro ω hω s hs i j hij
    exact hBrate i ω (fun h => hω (mem_iUnion.2 ⟨i, h⟩)) s hs j hij
  · filter_upwards [ae_all_iff.2 hBae] with ω hω hωB i
    exact hω i (fun h => hωB (mem_iUnion.2 ⟨i, h⟩))

/-- **Local long-jump bound, every `r`** (interface for the removal identity): for `f ≥ 0` on
the `r`-sector,
`|𝓑_{mask} f(ζ)| ≤ Σ_i ζ_i Σ_{j ≠ i, P i j} c_ij (1+ζ_j) f(ζ^{ij}) + (r+1) f(ζ) Σ_i ζ_i Σ_{j: P i j} c_ij`.
By the removal identity (`condExp_remove_mul_ne`), `(1+ζ_j) F_r(ζ^{ij}) = E[P_i X_j | 𝓛]` for the
conditional moments, so the first sum is `Σ_i ζ_i Σ_j c_ij E[P_i X_j | 𝓛]`. -/
theorem longGen_local_le {P : Fin N → Fin N → Prop} [DecidableRel P] {c : Fin N → Fin N → ℝ}
    (hc : ∀ i j, 0 ≤ c i j) {r : ℕ} {ζ : Occ N} (hζ : ζ ∈ sector N r) {f : Occ N → ℝ}
    (hf : ∀ η ∈ sector N r, 0 ≤ f η) :
    |momentGenerator (maskRate P c) f ζ| ≤
      ∑ i, (ζ i : ℝ) * ∑ j ∈ (univ.erase i).filter (P i), c i j * (1 + ζ j) * f (move ζ i j) +
        (r + 1) * f ζ * ∑ i, (ζ i : ℝ) * ∑ j ∈ univ.filter (P i), c i j := by
  classical
  have hζsum := mem_sector.1 hζ
  have hζle : ∀ j, (ζ j : ℝ) ≤ r := fun j => by
    have : ζ j ≤ r := hζsum ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    exact_mod_cast this
  have hm0 : ∀ i j, 0 ≤ maskRate P c i j := fun i j => by unfold maskRate; split_ifs <;> simp [hc]
  have hf0 := hf ζ hζ
  unfold momentGenerator
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rcases Nat.eq_zero_or_pos (ζ i) with hi | hi
  · rw [Finset.sum_eq_zero fun j _ => by rw [jumpCoeff_eq_zero_of_eq_zero ζ j hi]; ring]
    simp [hi]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hsplit : ∀ j ∈ univ.erase i,
      |maskRate P c i j * jumpCoeff ζ i j * (f (move ζ i j) - f ζ)| ≤
        (ζ i : ℝ) * (if P i j then c i j * (1 + ζ j) * f (move ζ i j) else 0) +
          (r + 1) * f ζ * ((ζ i : ℝ) * maskRate P c i j) := by
    intro j hj
    have hij : i ≠ j := Ne.symm (Finset.mem_erase.1 hj).1
    have hmv := hf _ (move_mem_sector hζ hij hi)
    rw [abs_mul, abs_of_nonneg (mul_nonneg (hm0 i j) (jumpCoeff_nonneg ζ i j))]
    have hab : |f (move ζ i j) - f ζ| ≤ f (move ζ i j) + f ζ :=
      (abs_sub _ _).trans (by rw [abs_of_nonneg hmv, abs_of_nonneg hf0])
    refine (mul_le_mul_of_nonneg_left hab (mul_nonneg (hm0 i j) (jumpCoeff_nonneg ζ i j))).trans ?_
    unfold maskRate jumpCoeff
    split_ifs with hP
    · have : (ζ i : ℝ) * (1 + ζ j) * f ζ ≤ (ζ i : ℝ) * (r + 1) * f ζ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith [hζle j])
          (Nat.cast_nonneg _)) hf0
      nlinarith [hc i j]
    · simp
  refine (Finset.sum_le_sum hsplit).trans ?_
  rw [Finset.sum_add_distrib]
  refine add_le_add (le_of_eq ?_) ?_
  · rw [← Finset.mul_sum, Finset.sum_filter]
  · rw [← Finset.mul_sum, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (sum_erase_maskRate_le hc i)
      (Nat.cast_nonneg _)) (mul_nonneg (by positivity) hf0)

end BlockBand.Palm.MomentFlow
