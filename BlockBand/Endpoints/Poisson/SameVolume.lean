module

public import BlockBand.Endpoints.Poisson.SameVolumeBoxes

/-!
# The same-volume log-error bound from the single-collar log error

We reduce the same-volume log-error bound to a single-collar log-error bound, taken as a
hypothesis.

* `SvSingleCollarLogError` (a hypothesis, see its docstring): the single-collar log-error bound
  integrated against `f`, for one collar removal of the stage matrices of
  the sequential-collars lemma, in the geometry of the same-volume log-error bound.
* `sv_coupling`: the coupling `γ` of the ring law and the product of the box laws: the law of
  `(H^ring, (H_i)_i)` with all of them read off the same Gaussian coordinates (the rewiring of
  the collars), with the exact marginals.
* `sv_pointwise_le`: for every configuration, `|𝓡_δ^C(H^ring) - 𝓡_δ^C(H^boxes)|` is at most the
  sum of the `2m` stage differences (exact identification of `H^ring`, `H^boxes`, `P_C` with the
  empty-stage matrices; telescope; common fully matched model).
* `peSameVolumeLogError_of_singleCollar`: `SvSingleCollarLogError → PeSameVolumeLogError`
  (add the `≤ 2m` stage errors).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.InputsRing (ringParameters toBlockCoords directSumBlockCoords)
open BlockBand.Internal.Contracts.Inputs (blockProjector)
open scoped ENNReal ContDiff

/-!
## 1. The single-collar log error
-/

/-- **The single-collar log error.** Setting: exactly that of `PeSameVolumeLogError`:
`0 < b < 1/2`, bulk `E`, `f ≥ 0` `C^∞` with compact support; `c > 0` before `δ`; `C = C_{f,δ}` before the partition `(m, a, R, τ)` with
`R ≥ 2`, `τ ≥ 1`, `Σ a_i = 1`, `4R + 1 ≤ a_i τ`; a critical sequence `(n_j, W_j)` and box block
numbers `n_i(j) ≥ 4` with `n_i/W → a_i τ` and eventually `Σ_i n_i = n`. The collar layout is
`svLayout` (unit `i` has `n_i` blocks), the base block `0`, the buffer `⌊R W⌋` blocks, the source
set `C = InSource` and the physical source `κ = δW²/Λ`, `Λ = nWρ(E)`.

Statement: for either pairing `π`, every stage `S` and every collar `k ∉ S` (any removal order),
for every `ε > 0`, eventually in `j`, under the original prior in Gaussian coordinates,
`E |svStageStat π S - svStageStat π (S ∪ {k})| ≤ C m² e^{-cR} + ε`, where
`svStageStat π S = (πδ)⁻¹ ∫ f(x) B_κ^{π,S}(E + x/Λ) dx` and `B_κ^{π,S}(e)` is the source-centred
log-determinant (the positive log increment) of the stage matrix with matched leads
`z = z_b(e)`. This is the paper's bound
`limsup_W E|B^closed_κ(e) - B^matched_κ(e)| ≤ C_κ m² e^{-c'R}` (uniform in the bounded unfolded
window `e = E + x/Λ`, `x ∈ supp f`), integrated against `f`.

Why it is a hypothesis. Its proof in the paper is the analytic core of the derivation, and none
of it is formalized:
* the absorbed scattering matrix of the old network and the Ward bounds on the remote scattering
  source;
* the unitary dilation of the source;
* the Cauchy-integral removal of the exceptional sets (`PassiveLog`, `SingularLogMoments`), and
  the cancellation of the `κ`-independent prefactor of the stage factorization (this
  cancellation is proved, in the first clause of `sequentialCollars_full`);
* Tonelli in `(x, v)` for the integration against `f` (it needs the integrability of
  `x ↦ f(x) B_κ(E + x/Λ)`, which uses the log-moment bounds).

It is strictly weaker than `PeSameVolumeLogError`: it concerns a single collar removal in one
pairing. `PeSameVolumeLogError` needs in addition the coupling of the ring law and the product of
the box laws, the identification of `H^ring`, `H^boxes` and the absorber projectors with the
empty-stage matrices, the core sizes, the telescope of both pairings to the common fully matched
model and the summation of the `2m` stage errors; these are proved (`sv_telescope`,
`sv_directSum_eq`, `sv_pointwise_le`, `peSameVolumeLogError_of_singleCollar`). -/
def SvSingleCollarLogError : Prop :=
  ∀ (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (E : ℝ), -2 < E → E < 2 →
  ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → (∀ x, 0 ≤ f x) →
  ∃ c : ℝ, 0 < c ∧ ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧
  ∀ (m : ℕ) (a : Fin m → ℝ) (R τ : ℝ), 2 ≤ R → 1 ≤ τ → ∑ i, a i = 1 →
    (∀ i, 4 * R + 1 ≤ a i * τ) →
  ∀ (s : CriticalSequence τ) (nb : ℕ → Fin m → ℕ), (∀ j i, 4 ≤ nb j i) →
    (∀ i, Tendsto (fun j => (nb j i : ℝ) / (s.W j : ℝ)) atTop (𝓝 (a i * τ))) →
    (∀ᶠ j in atTop, ∑ i, nb j i = s.n j) →
  ∀ (π : Pairing) (S : Finset (Fin m)) (k : Fin m), k ∉ S → ∀ ε : ℝ, 0 < ε →
  ∀ᶠ j in atTop,
    ∫⁻ v, ENNReal.ofReal
        |svStageStat (svLayout (nb j)) π S b E
            (((s.parameters b hb hb' j).N : ℝ) * Parameters.semicircleDensity E) δ
            ⌊R * (s.W j : ℝ)⌋₊ f v -
          svStageStat (svLayout (nb j)) π (insert k S) b E
            (((s.parameters b hb hb' j).N : ℝ) * Parameters.semicircleDensity E) δ
            ⌊R * (s.W j : ℝ)⌋₊ f v|
      ∂ringCoordLaw (s.parameters b hb hb' j).n (s.parameters b hb hb' j).W b ≤
      ENNReal.ofReal (C * (m : ℝ) ^ 2 * Real.exp (-(c * R)) + ε)

/-!
## 2. The coupling
-/

variable {m : ℕ}

theorem sv_measurable_boxCoords {n W : ℕ} (nb : Fin m → ℕ) (i : Fin m) :
    Measurable (svBoxCoords (n := n) (W := W) nb i) := by
  unfold svBoxCoords
  exact (measurable_pi_iff.mpr fun q => (measurable_pi_apply _).comp measurable_fst).prodMk
    (measurable_pi_iff.mpr fun q => (measurable_pi_apply _).comp measurable_snd)

/-- **The coupling** of the ring law and the product of the box laws: the law, under the original
prior, of `(H^ring, (H_i)_i)` read off the same Gaussian coordinates. Its marginals are exactly
`model.law` and `⊗ᵢ boxes_i.law`; lower integrals against it are bounded by the prior integral. -/
theorem sv_coupling (p : Parameters) (model : p.GaussianRingModel) (nb : Fin m → ℕ)
    (hnb : ∀ i, 4 ≤ nb i) (hsum : ∑ i, nb i = p.n)
    (boxes : ∀ i, (ringParameters (nb i) p.W p.b (hnb i) p.W_pos p.b_pos
      p.b_lt_half).GaussianRingModel)
    (G : p.SiteMatrix × (∀ i, (ringParameters (nb i) p.W p.b (hnb i) p.W_pos p.b_pos
      p.b_lt_half).SiteMatrix) → ℝ≥0∞) :
    ∃ γ : Measure (p.SiteMatrix × ∀ i, (ringParameters (nb i) p.W p.b (hnb i) p.W_pos p.b_pos
        p.b_lt_half).SiteMatrix),
      IsProbabilityMeasure γ ∧
      γ.map Prod.fst = (model.law : Measure p.SiteMatrix) ∧
      γ.map Prod.snd = Measure.pi (fun i => ((boxes i).law : Measure (ringParameters (nb i) p.W
        p.b (hnb i) p.W_pos p.b_pos p.b_lt_half).SiteMatrix)) ∧
      ∫⁻ w, G w ∂γ ≤ ∫⁻ v, G (ringMatrix v, fun i => ringMatrix (svBoxCoords nb i v))
        ∂ringCoordLaw p.n p.W p.b := by
  have : ∀ i, NeZero (nb i) := fun i => ⟨by have := hnb i; omega⟩
  let F : RingCoords p.n p.W → p.SiteMatrix × (∀ i, (ringParameters (nb i) p.W p.b (hnb i)
      p.W_pos p.b_pos p.b_lt_half).SiteMatrix) :=
    fun v => (ringMatrix v, fun i => ringMatrix (svBoxCoords nb i v))
  have hF2 : Measurable fun v : RingCoords p.n p.W =>
      (fun i => ringMatrix (svBoxCoords nb i v) : ∀ i, (ringParameters (nb i) p.W p.b (hnb i)
        p.W_pos p.b_pos p.b_lt_half).SiteMatrix) :=
    measurable_pi_iff.mpr fun i => measurable_ringMatrix.comp (sv_measurable_boxCoords nb i)
  have hF : Measurable F := measurable_ringMatrix.prodMk hF2
  refine ⟨(ringCoordLaw p.n p.W p.b).map F, (Measure.isProbabilityMeasure_map_iff hF.aemeasurable).mpr inferInstance,
    ?_, ?_, lintegral_map_le _ hF.aemeasurable⟩
  · rw [Measure.map_map measurable_fst hF]
    exact ringCoordLaw_map_eq_model coordinatePriorIsPhysical p model
  · rw [Measure.map_map measurable_snd hF]
    have hlaw := sv_hasLaw_boxCoords (n := p.n) (W := p.W) hnb hsum p.b
    have : ∀ i, SigmaFinite ((boxes i).law : Measure (ringParameters (nb i) p.W p.b (hnb i)
        p.W_pos p.b_pos p.b_lt_half).SiteMatrix) := fun i => inferInstance
    have hmp : MeasurePreserving
        (fun (c : ∀ i, RingCoords (nb i) p.W) i => ringMatrix (c i))
        (Measure.pi fun i => ringCoordLaw (nb i) p.W p.b)
        (Measure.pi fun i => ((boxes i).law : Measure (ringParameters (nb i) p.W p.b (hnb i)
          p.W_pos p.b_pos p.b_lt_half).SiteMatrix)) :=
      measurePreserving_pi (fun i => ringCoordLaw (nb i) p.W p.b)
        (fun i => ((boxes i).law : Measure (ringParameters (nb i) p.W p.b (hnb i)
          p.W_pos p.b_pos p.b_lt_half).SiteMatrix)) (hν := this) fun i =>
        ⟨measurable_ringMatrix, ringCoordLaw_map_eq_model coordinatePriorIsPhysical _ (boxes i)⟩
    have := (hmp.comp_hasLaw hlaw).map_eq
    exact this

/-!
## 3. The pointwise telescope
-/

/-- **Pointwise reduction to the stage differences.** For every configuration of the Gaussian
coordinates, `|𝓡_δ^C(H^ring) - 𝓡_δ^C(H^boxes)|` (cores `svRingCore`, `svBoxCore`, global
unfolding `Λ = nWρ`) is at most the sum of the `2m` stage differences of the two pairings. -/
theorem sv_pointwise_le (p : Parameters) (nb : Fin m → ℕ) (hnb : ∀ i, 4 ≤ nb i)
    (hsum : ∑ i, nb i = p.n) (E δ : ℝ) (buf : ℕ) (f : ℝ → ℝ) (v : RingCoords p.n p.W) :
    |positiveLogStatistic (ringMatrix v) E ((p.N : ℝ) * Parameters.semicircleDensity E) δ
        (physicalBlockProjector p (svRingCore (nb := nb) (n := p.n) buf)) f -
      positiveLogStatistic (directSumBlockCoords nb
          (fun i => toBlockCoords (ringParameters (nb i) p.W p.b (hnb i) p.W_pos p.b_pos
            p.b_lt_half) (ringMatrix (svBoxCoords nb i v))))
        E ((((∑ i, nb i) * p.W : ℕ) : ℝ) * Parameters.semicircleDensity E) δ
        (blockProjector (svBoxCore (nb := nb) (n := p.n) buf)) f| ≤
      ∑ k : Fin m, |svStageStat (svLayout nb) .cyclic (svStages m k.val) p.b E
          ((p.N : ℝ) * Parameters.semicircleDensity E) δ buf f v -
        svStageStat (svLayout nb) .cyclic (insert k (svStages m k.val)) p.b E
          ((p.N : ℝ) * Parameters.semicircleDensity E) δ buf f v| +
      ∑ k : Fin m, |svStageStat (svLayout nb) .box (svStages m k.val) p.b E
          ((p.N : ℝ) * Parameters.semicircleDensity E) δ buf f v -
        svStageStat (svLayout nb) .box (insert k (svStages m k.val)) p.b E
          ((p.N : ℝ) * Parameters.semicircleDensity E) δ buf f v| := by
  have hW : p.W ≠ 0 := p.W_pos.ne'
  have hL := sv_isCollarLayout hnb hsum
  have hΛ : ((((∑ i, nb i) * p.W : ℕ) : ℝ)) = (p.N : ℝ) := by
    rw [hsum]; rfl
  rw [hΛ, sv_directSum_eq (n := p.n) hnb hsum p.b p.W_pos p.b_pos p.b_lt_half v,
    sv_blockProjector_eq (W := p.W) hnb hsum buf, positiveLogStatistic_submatrix,
    sv_physicalBlockProjector_eq, ← sv_stageHerm_cyclic_empty (svLayout nb)
      (by have := p.n_ge_four; omega) (0 : ZMod p.n) v,
    ← sv_stageStat_empty _ _ _ _ _ _ _ _ _ hW, ← sv_stageStat_empty _ _ _ _ _ _ _ _ _ hW,
    sv_stageStat_empty_sub _ hL]
  refine (abs_sub _ _).trans (add_le_add ?_ ?_)
  · exact Finset.abs_sum_le_sum_abs _ _
  · exact Finset.abs_sum_le_sum_abs _ _

/-!
## 4. The reduction
-/

/-- **The same-volume log-error bound from the single-collar log error**: telescope each pairing
to the common fully matched model, add the at most `2m` stage errors, and integrate against
`f`. The constant is `2C`, with `C` that of `SvSingleCollarLogError`, and the same `c`.

Proved here: the coupling (`sv_coupling`, exact marginals), the identification of `H^ring`,
`H^boxes` and the absorber projectors of the cores with the empty-stage matrices of both pairings
(`sv_pointwise_le`), the core sizes `|Cᶜ| ≤ m(3 + 2⌊RW⌋) ≤ m(3 + 2RW)`, the telescope to the
common fully matched model and the summation of the `2m` stage errors. -/
theorem peSameVolumeLogError_of_singleCollar (h : SvSingleCollarLogError) :
    PeSameVolumeLogError := by
  intro b hb hb' E hE1 hE2 f hf hfs hf0
  obtain ⟨c, hc, hδ⟩ := h b hb hb' E hE1 hE2 f hf hfs hf0
  refine ⟨c, hc, fun δ hδpos => ?_⟩
  obtain ⟨C, hC, hmain⟩ := hδ δ hδpos
  refine ⟨2 * C, by positivity, ?_⟩
  intro m a R τ hR hτ ha hgap s model nb hnb hlim hsum boxes ε hε
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp at ha
    · exact hm
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  set ε' : ℝ := ε / (2 * m) with hε'
  have hε'pos : 0 < ε' := by positivity
  have hstage : ∀ (π : Pairing) (k : Fin m), ∀ᶠ j in atTop,
      ∫⁻ v, ENNReal.ofReal
          |svStageStat (svLayout (nb j)) π (svStages m k.val) b E
              (((s.parameters b hb hb' j).N : ℝ) * Parameters.semicircleDensity E) δ
              ⌊R * (s.W j : ℝ)⌋₊ f v -
            svStageStat (svLayout (nb j)) π (insert k (svStages m k.val)) b E
              (((s.parameters b hb hb' j).N : ℝ) * Parameters.semicircleDensity E) δ
              ⌊R * (s.W j : ℝ)⌋₊ f v|
        ∂ringCoordLaw (s.parameters b hb hb' j).n (s.parameters b hb hb' j).W b ≤
        ENNReal.ofReal (C * (m : ℝ) ^ 2 * Real.exp (-(c * R)) + ε') :=
    fun π k => hmain m a R τ hR hτ ha hgap s nb hnb hlim hsum π (svStages m k.val) k
      (sv_not_mem_stages k) ε' hε'pos
  filter_upwards [hsum, Filter.eventually_all.2 (hstage .cyclic),
    Filter.eventually_all.2 (hstage .box)] with j hsj hcj hbj
  set p := s.parameters b hb hb' j with hp
  have hsj' : ∑ i, nb j i = p.n := hsj
  set buf := ⌊R * (s.W j : ℝ)⌋₊ with hbuf
  have hbufle : (buf : ℝ) ≤ R * (s.W j : ℝ) :=
    Nat.floor_le (mul_nonneg (by linarith) (Nat.cast_nonneg _))
  have hcard : ∀ k : ℕ, k ≤ m * (3 + 2 * buf) → (k : ℝ) ≤ m * (3 + 2 * R * s.W j) := by
    intro k hk
    have : (k : ℝ) ≤ (m : ℝ) * (3 + 2 * (buf : ℝ)) := by exact_mod_cast hk
    nlinarith
  obtain ⟨γ, hγ, hγ1, hγ2, hγle⟩ := sv_coupling p (model j) (nb j) (hnb j) hsj' (boxes j)
    (fun w => ENNReal.ofReal
      |positiveLogStatistic w.1 E (((s.parameters b hb hb' j).N : ℝ) *
          Parameters.semicircleDensity E) δ
          (physicalBlockProjector (s.parameters b hb hb' j)
            (svRingCore (nb := nb j) (n := p.n) buf)) f -
        positiveLogStatistic (directSumBlockCoords (nb j)
            (fun i => toBlockCoords
              (ringParameters (nb j i) (s.W j) b (hnb j i) (s.W_pos j) hb hb') (w.2 i)))
          E ((((∑ i, nb j i) * s.W j : ℕ) : ℝ) * Parameters.semicircleDensity E) δ
          (blockProjector (svBoxCore (nb := nb j) (n := p.n) buf)) f|)
  refine ⟨svRingCore (nb := nb j) (n := p.n) buf, svBoxCore (nb := nb j) (n := p.n) buf,
    hcard _ (sv_card_compl_ringCore_le (n := p.n) (hnb j) hsj' buf),
    hcard _ (sv_card_compl_boxCore_le (n := p.n) (hnb j) hsj' buf), γ, hγ, hγ1, hγ2,
    hγle.trans ?_⟩
  have hfc : Continuous f := hf.continuous
  have hmeas : ∀ (π : Pairing) (k : Fin m), Measurable fun v : RingCoords p.n p.W =>
      ENNReal.ofReal |svStageStat (svLayout (nb j)) π (svStages m k.val) b E
          ((p.N : ℝ) * Parameters.semicircleDensity E) δ buf f v -
        svStageStat (svLayout (nb j)) π (insert k (svStages m k.val)) b E
          ((p.N : ℝ) * Parameters.semicircleDensity E) δ buf f v| := fun π k =>
    ENNReal.measurable_ofReal.comp
      (((sv_measurable_stageStat _ _ _ _ _ _ _ _ hfc).sub
        (sv_measurable_stageStat _ _ _ _ _ _ _ _ hfc)).abs)
  calc ∫⁻ v, _ ∂ringCoordLaw p.n p.W p.b
      ≤ ∫⁻ v, ((∑ k : Fin m, ENNReal.ofReal |svStageStat (svLayout (nb j)) .cyclic
            (svStages m k.val) b E ((p.N : ℝ) * Parameters.semicircleDensity E) δ buf f v -
          svStageStat (svLayout (nb j)) .cyclic (insert k (svStages m k.val)) b E
            ((p.N : ℝ) * Parameters.semicircleDensity E) δ buf f v|) +
        ∑ k : Fin m, ENNReal.ofReal |svStageStat (svLayout (nb j)) .box
            (svStages m k.val) b E ((p.N : ℝ) * Parameters.semicircleDensity E) δ buf f v -
          svStageStat (svLayout (nb j)) .box (insert k (svStages m k.val)) b E
            ((p.N : ℝ) * Parameters.semicircleDensity E) δ buf f v|)
          ∂ringCoordLaw p.n p.W p.b := by
        refine lintegral_mono fun v => ?_
        rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => abs_nonneg _),
          ← ENNReal.ofReal_sum_of_nonneg (fun _ _ => abs_nonneg _),
          ← ENNReal.ofReal_add (Finset.sum_nonneg fun _ _ => abs_nonneg _)
            (Finset.sum_nonneg fun _ _ => abs_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (sv_pointwise_le p (nb j) (hnb j) hsj' E δ buf f v)
    _ = (∑ k : Fin m, ∫⁻ v, ENNReal.ofReal |svStageStat (svLayout (nb j)) .cyclic
            (svStages m k.val) b E ((p.N : ℝ) * Parameters.semicircleDensity E) δ buf f v -
          svStageStat (svLayout (nb j)) .cyclic (insert k (svStages m k.val)) b E
            ((p.N : ℝ) * Parameters.semicircleDensity E) δ buf f v| ∂ringCoordLaw p.n p.W p.b) +
        ∑ k : Fin m, ∫⁻ v, ENNReal.ofReal |svStageStat (svLayout (nb j)) .box
            (svStages m k.val) b E ((p.N : ℝ) * Parameters.semicircleDensity E) δ buf f v -
          svStageStat (svLayout (nb j)) .box (insert k (svStages m k.val)) b E
            ((p.N : ℝ) * Parameters.semicircleDensity E) δ buf f v| ∂ringCoordLaw p.n p.W p.b := by
        rw [lintegral_add_left (Finset.measurable_sum _ fun k _ => hmeas .cyclic k),
          lintegral_finsetSum _ fun k _ => hmeas .cyclic k,
          lintegral_finsetSum _ fun k _ => hmeas .box k]
    _ ≤ (∑ _k : Fin m, ENNReal.ofReal (C * (m : ℝ) ^ 2 * Real.exp (-(c * R)) + ε')) +
        ∑ _k : Fin m, ENNReal.ofReal (C * (m : ℝ) ^ 2 * Real.exp (-(c * R)) + ε') :=
        add_le_add (Finset.sum_le_sum fun k _ => hcj k) (Finset.sum_le_sum fun k _ => hbj k)
    _ = ENNReal.ofReal (2 * C * (m : ℝ) ^ 3 * Real.exp (-(c * R)) + ε) := by
        have h0 : 0 ≤ C * (m : ℝ) ^ 2 * Real.exp (-(c * R)) + ε' := by positivity
        rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => h0), ← ENNReal.ofReal_add
          (Finset.sum_nonneg fun _ _ => h0) (Finset.sum_nonneg fun _ _ => h0)]
        congr 1
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [hε']
        field_simp
        ring

end BlockBand.Endpoints
