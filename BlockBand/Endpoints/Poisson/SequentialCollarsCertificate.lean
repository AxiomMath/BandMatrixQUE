module

public import BlockBand.Endpoints.Poisson.SequentialCollarsCertificateLaw

/-!
# The sequential-collars lemma, item (ii)

Item (ii) states: the compressed zero-source response `r₀` satisfies the collar scalar
certificate except on probability `O_{m,D}(W^{-D})` for every fixed `D`, at each deterministic
compact-bulk energy, and its defect `g₀ = Tr(I - r₀*r₀)` has `E g₀² ≤ C`, uniformly in the total
length (`sequentialCollars_certificate`, `sequentialCollars_conductance`). Law: the original
prior `ringCoordLaw` (transported to every `model.law` in `sequentialCollars_full`). Zero source,
matched value `z = z_b(e)`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers (PathSample pathLaw pathMatrix pathSchur boundaryZ
  matchedDistance MatchedTracesContract bulkInterval)
open BlockBand.Internal.Contracts.Critical (conductance oldScattering)
open BlockBand.Internal.Contracts.TransmissionUniform (TransmissionLengthUniformContract)
open BlockBand.Internal.Contracts.TransmissionPath (growthPathLaw pathAt)
open scoped ENNReal

section Lengths

variable {m n : ℕ} {L : Fin m → ℕ} {s : ZMod n}

theorem le_rightLen (hL : IsCollarLayout n L) (S : Finset (Fin m)) (k : Fin m) :
    L k ≤ rightLen L s hL S k := by
  by_contra hlt
  push Not at hlt
  obtain ⟨j, -, hj⟩ := rightLen_spec (s := s) hL S k
  rw [unitPos_add] at hj
  have := hL.2 j
  have := ((unitPos_inj hL s (by omega) (by omega)).mp hj).2
  omega

theorem le_leftLen (hL : IsCollarLayout n L) (S : Finset (Fin m)) (k : Fin m) :
    L ((finRotate m).symm k) ≤ leftLen L s hL S k := by
  set k' := (finRotate m).symm k
  by_contra hlt
  push Not at hlt
  obtain ⟨j, -, hj⟩ := leftLen_spec (s := s) hL S k
  have he := pathEnd_succ (s := s) hL k'
  rw [Equiv.apply_symm_apply] at he
  have h1 : unitPos n L s k 0 - 1 = unitPos n L s k' (L k' + 2) := by
    rw [← he]; unfold pathEnd; ring
  rw [h1] at hj
  have h2 : unitPos n L s k' (L k' + 2) - (leftLen L s hL S k : ZMod n) =
      unitPos n L s k' (L k' + 2 - leftLen L s hL S k) := by
    rw [unitPos_eq_add (o := L k' + 2), unitPos_eq_add (o := L k' + 2 - leftLen L s hL S k),
      Nat.cast_sub (by omega)]
    ring
  rw [h2] at hj
  have := hL.2 j; have := hL.2 k'
  have := ((unitPos_inj hL s (by omega) (by omega)).mp hj).2
  omega

/-- The two incident runs have length between `min_j L j` and `n`. -/
theorem compRun_lengths (hL : IsCollarLayout n L) (π : Pairing) (S : Finset (Fin m)) (k : Fin m)
    {ℓ : ℕ} (hℓ : ∀ j, ℓ ≤ L j) :
    (ℓ ≤ (compRunR (s := s) hL π S k).2 ∧ (compRunR (s := s) hL π S k).2 ≤ n) ∧
      (ℓ ≤ (compRunL (s := s) hL π S k).2 ∧ (compRunL (s := s) hL π S k).2 ≤ n) := by
  have hn := layout_le hL k
  cases π
  · exact ⟨⟨(hℓ k).trans (le_rightLen hL S k), (rightLen_le hL S k).trans (by omega)⟩,
      ⟨(hℓ _).trans (le_leftLen hL S k), (leftLen_le hL S k).trans (by omega)⟩⟩
  · exact ⟨⟨hℓ k, by simp only [compRunR]; omega⟩, ⟨hℓ k, by simp only [compRunL]; omega⟩⟩

end Lengths

section Event

variable (p : Parameters) {m : ℕ} (L : Fin m → ℕ) (s : ZMod p.n)

/-- Almost surely (original prior), the deterministic bounds of `certificate_on_event` hold. -/
theorem ae_certificate_bounds (hL : IsCollarLayout p.n L) (π : Pairing) {S : Finset (Fin m)}
    {k : Fin m} (hk : k ∉ S) {e : ℝ} (he1 : -2 < e) (he2 : e < 2) (buf : ℕ) :
    ∀ᵐ ω ∂(ringCoordLaw p.n p.W p.b),
      matchedDistance p.b e (oldX0 L s π S k p.b e buf ω) ≤
          max (matchedDistance p.b e (pathSchur e (runSample (compRunR (s := s) hL π S k).1
              (compRunR (s := s) hL π S k).2 ω)))
            (matchedDistance p.b e (pathSchur e (runSample (compRunL (s := s) hL π S k).1
              (compRunL (s := s) hL π S k).2 ω))) ∧
        ‖conductance (oldResponse (boundaryZ p.b e) (oldX0 L s π S k p.b e buf ω))‖ ≤
          ‖nearConductance p.b e (pathSchur e (runSample (compRunR (s := s) hL π S k).1
              (compRunR (s := s) hL π S k).2 ω))‖ +
            ‖nearConductance p.b e (pathSchur e (runSample (compRunL (s := s) hL π S k).1
              (compRunL (s := s) hL π S k).2 ω))‖ := by
  have hz := boundaryZ_im_pos (b := p.b) (by linarith [p.b_lt_half]) he1 he2
  filter_upwards [ringCoordLaw_ae_isHermitian (n := p.n) (W := p.W) p.b,
    ae_isUnit_det_oldInterior p L s π S k e hz buf 0,
    ae_isUnit_det_runPath p (compRunR (s := s) hL π S k).1 (compRunR (s := s) hL π S k).2 e,
    ae_isUnit_det_runPath p (compRunL (s := s) hL π S k).1 (compRunL (s := s) hL π S k).2 e]
    with ω hA hM hPR hPL
  exact certificate_on_event hL π hk hz buf ω hA hM hPR hPL

end Event

section Markov

/-- Markov's inequality for the matched-traces theorem quantity of a run, transported to the
original prior. -/
theorem run_tail_le (p : Parameters) (p₀ : ZMod p.n) {r : ℕ} (hr1 : 1 ≤ r) (hrn : r < p.n)
    (e δ q : ℝ) (hδ : 0 < δ) (hq : 0 < q) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : eLpNorm (fun ps : PathSample p.W r => matchedDistance p.b e (pathSchur e ps))
      (ENNReal.ofReal q) (pathLaw p.W r p.b) ≤ ENNReal.ofReal B) :
    ringCoordLaw p.n p.W p.b
        {ω | δ < matchedDistance p.b e (pathSchur e (runSample p₀ r ω))} ≤
      ENNReal.ofReal ((δ⁻¹ * B) ^ q) := by
  have hX := hasLaw_runSample (W := p.W) p₀ hr1 hrn p.b
  have hdm : Measurable fun ps : PathSample p.W r => matchedDistance p.b e (pathSchur e ps) :=
    (measurable_matchedDistance p.b e).comp (measurable_pathSchur e)
  have hsub : {ω | δ < matchedDistance p.b e (pathSchur e (runSample p₀ r ω))} ⊆
      {ω | ENNReal.ofReal δ ≤ ‖(fun ps : PathSample p.W r => matchedDistance p.b e
        (pathSchur e ps)) (runSample p₀ r ω)‖ₑ} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (hω.le.trans (le_abs_self _))
  refine (measure_mono hsub).trans ?_
  have hq0 : ENNReal.ofReal q ≠ 0 := by simpa using hq
  have hM := meas_ge_le_mul_pow_eLpNorm_enorm (ringCoordLaw p.n p.W p.b) hq0 ENNReal.ofReal_ne_top
    (f := (fun ps : PathSample p.W r => matchedDistance p.b e (pathSchur e ps)) ∘
      runSample p₀ r) (ε := ENNReal.ofReal δ) (by simpa using hδ) (by simp)
  refine hM.trans ?_
  have heq : eLpNorm ((fun ps : PathSample p.W r => matchedDistance p.b e (pathSchur e ps)) ∘
      runSample p₀ r) (ENNReal.ofReal q) (ringCoordLaw p.n p.W p.b) =
      eLpNorm (fun ps : PathSample p.W r => matchedDistance p.b e (pathSchur e ps))
        (ENNReal.ofReal q) (pathLaw p.W r p.b) := by
    rw [← eLpNorm_map_measure hdm.aestronglyMeasurable hX.aemeasurable, hX.map_eq]
  rw [heq, ENNReal.toReal_ofReal hq.le]
  calc (ENNReal.ofReal δ)⁻¹ ^ q * eLpNorm (fun ps : PathSample p.W r =>
        matchedDistance p.b e (pathSchur e ps)) (ENNReal.ofReal q) (pathLaw p.W r p.b) ^ q
      ≤ (ENNReal.ofReal δ)⁻¹ ^ q * (ENNReal.ofReal B) ^ q := by
        gcongr
    _ = ENNReal.ofReal ((δ⁻¹ * B) ^ q) := by
        rw [← ENNReal.ofReal_inv_of_pos hδ, ENNReal.ofReal_rpow_of_nonneg (by positivity) hq.le,
          ENNReal.ofReal_rpow_of_nonneg hB0 hq.le, ← ENNReal.ofReal_mul (by positivity),
          Real.mul_rpow (by positivity) hB0]

theorem real_tail_arith {W K q D : ℝ} (hW : 1 ≤ W) (hq : q = D + 2)
    (hWK : 2 * K + 1 ≤ W) : 2 * (K * W ^ (-q)) ≤ W ^ (-D) := by
  have hW0 : 0 < W := by linarith
  have h1 : W ^ (-D) = W ^ (-q) * W ^ (2 : ℝ) := by
    rw [← Real.rpow_add hW0]; congr 1; rw [hq]; ring
  have h2 : 2 * K ≤ W ^ (2 : ℝ) := by
    rw [Real.rpow_two]; nlinarith
  rw [h1]
  have h3 : 0 < W ^ (-q) := Real.rpow_pos_of_pos hW0 _
  nlinarith

end Markov

section Certificate

/-- **Sequential-collars lemma, item (ii): scalar certificate.** Hypothesis: `MatchedTracesContract`. Fix
`b ∈ (0,1/2)`, a bulk margin `κI > 0`, a certificate threshold `δ > 0` (e.g. `d_*/2` of the collar kernel
theorem), a power `D` and a total-length ratio `T`. Then there is `W₀` such that for every admissible `p` with
`p.b = b`, `p.W ≥ W₀` and `n ≤ T W`, every collar layout of its ring, either pairing, every stage (`S`, `k ∉ S`),
every buffer and every deterministic bulk energy `e ∈ [-2+κI, 2-κI]`, under the original prior the compressed
zero-source response violates the certificate `d(X₀) ≤ δ` with probability at most `W^{-D}`. -/
theorem sequentialCollars_certificate (hMT : MatchedTracesContract) {b : ℝ} (hb0 : 0 < b)
    (hb1 : b < 1 / 2) {κI : ℝ} (hκI : 0 < κI) {δ : ℝ} (hδ : 0 < δ) (D : ℕ) (T : ℝ) :
    ∃ W₀ : ℕ, ∀ p : Parameters, p.b = b → W₀ ≤ p.W → (p.n : ℝ) ≤ T * p.W →
      ∀ {m : ℕ} (L : Fin m → ℕ) (s : ZMod p.n) (_hL : IsCollarLayout p.n L) (π : Pairing)
        (S : Finset (Fin m)) (k : Fin m), k ∉ S → ∀ (buf : ℕ) (e : ℝ), e ∈ bulkInterval κI →
        ringCoordLaw p.n p.W p.b
            {ω | δ < matchedDistance b e (oldX0 L s π S k b e buf ω)} ≤
          ENNReal.ofReal ((p.W : ℝ) ^ (-(D : ℝ))) := by
  obtain ⟨ε₀, C, hε₀, hMTb⟩ := hMT.path b hb0 hb1 κI T hκI
  set q : ℝ := (D : ℝ) + 2 with hq
  set C' := max C 0
  set K : ℝ := (δ⁻¹ * (C' * Real.sqrt q)) ^ q
  have hK : 0 ≤ K := Real.rpow_nonneg (by positivity) _
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hqe0 : 0 ≤ q / ε₀ := div_nonneg hq0 hε₀.le
  refine ⟨⌈2 * K + 1 + q / ε₀⌉₊ + 1, ?_⟩
  intro p hpb hW hn m L s hL π S k hk buf e he
  subst hpb
  have he1 : -2 < e := by have := he.1; linarith
  have he2 : e < 2 := by have := he.2; linarith
  have hWr : 2 * K + 1 + q / ε₀ ≤ (p.W : ℝ) := by
    have := Nat.le_ceil (2 * K + 1 + q / ε₀)
    have h2 : ((⌈2 * K + 1 + q / ε₀⌉₊ + 1 : ℕ) : ℝ) ≤ p.W := by exact_mod_cast hW
    push_cast at h2; linarith
  have hqε : q ≤ ε₀ * p.W := by
    have : q / ε₀ ≤ p.W := by linarith
    rwa [div_le_iff₀ hε₀, mul_comm] at this
  have hW1 : (1 : ℝ) ≤ p.W := by linarith
  have hq2 : (2 : ℝ) ≤ q := by rw [hq]; have : (0 : ℝ) ≤ D := Nat.cast_nonneg D; linarith
  have hWpos : 0 < (p.W : ℝ) := by linarith
  -- the matched-traces tail of each run
  have htail : ∀ (p₀ : ZMod p.n) (r : ℕ), IsOldRun L s π S k p₀ r →
      ringCoordLaw p.n p.W p.b {ω | δ < matchedDistance p.b e (pathSchur e (runSample p₀ r ω))} ≤
        ENNReal.ofReal (K * (p.W : ℝ) ^ (-q)) := by
    intro p₀ r hr
    have hrn : r < p.n := by have := hr.lt; omega
    have hrT : (r : ℝ) ≤ T * p.W := by
      have : (r : ℝ) ≤ p.n := by exact_mod_cast hrn.le
      linarith
    have hB := hMTb p.W p.W_pos q hq2 hqε r hr.one_le hrT e he
    have hB' : eLpNorm (fun ps : PathSample p.W r => matchedDistance p.b e (pathSchur e ps))
        (ENNReal.ofReal q) (pathLaw p.W r p.b) ≤ ENNReal.ofReal (C' * Real.sqrt q / p.W) :=
      hB.trans (ENNReal.ofReal_le_ofReal (by gcongr; exact le_max_left _ _))
    refine (run_tail_le p p₀ hr.one_le hrn e δ q hδ (by linarith)
      (by have : 0 ≤ C' := le_max_right _ _; positivity) hB').trans ?_
    apply le_of_eq
    congr 1
    rw [show δ⁻¹ * (C' * Real.sqrt q / p.W) = (δ⁻¹ * (C' * Real.sqrt q)) * (p.W : ℝ)⁻¹ by ring,
      Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow hWpos.le,
      ← Real.rpow_neg hWpos.le]
  -- the ae inclusion of events
  have hae := ae_certificate_bounds p L s hL π hk he1 he2 buf
  set dR := fun ω : RingCoords p.n p.W => matchedDistance p.b e (pathSchur e
    (runSample (compRunR (s := s) hL π S k).1
    (compRunR (s := s) hL π S k).2 ω))
  set dL := fun ω : RingCoords p.n p.W => matchedDistance p.b e (pathSchur e
    (runSample (compRunL (s := s) hL π S k).1
    (compRunL (s := s) hL π S k).2 ω))
  have hsub : {ω | δ < matchedDistance p.b e (oldX0 L s π S k p.b e buf ω)}
      ≤ᵐ[ringCoordLaw p.n p.W p.b]
      ({ω | δ < dR ω} ∪ {ω | δ < dL ω} : Set (RingCoords p.n p.W)) := by
    filter_upwards [hae] with ω hω hmem
    have h := lt_of_lt_of_le hmem hω.1
    rcases lt_max_iff.mp h with h | h
    · exact Or.inl h
    · exact Or.inr h
  calc ringCoordLaw p.n p.W p.b {ω | δ < matchedDistance p.b e (oldX0 L s π S k p.b e buf ω)}
      ≤ ringCoordLaw p.n p.W p.b ({ω | δ < dR ω} ∪ {ω | δ < dL ω}) := measure_mono_ae hsub
    _ ≤ ringCoordLaw p.n p.W p.b {ω | δ < dR ω} + ringCoordLaw p.n p.W p.b {ω | δ < dL ω} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (K * (p.W : ℝ) ^ (-q)) + ENNReal.ofReal (K * (p.W : ℝ) ^ (-q)) :=
        add_le_add (htail _ _ (compRunR_isOldRun hL π S k)) (htail _ _ (compRunL_isOldRun hL π S k))
    _ = ENNReal.ofReal (2 * (K * (p.W : ℝ) ^ (-q))) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
    _ ≤ ENNReal.ofReal ((p.W : ℝ) ^ (-(D : ℝ))) :=
        ENNReal.ofReal_le_ofReal (real_tail_arith hW1 hq (by linarith))

/-- **Sequential-collars lemma, item (ii): defect moment.** The conductance bound follows from the conductance
moments, applied at lengths at least `εW`. Hypothesis: `TransmissionLengthUniformContract`. Fix `b ∈ (0,1/2)`, a
bulk margin `κI > 0` and `ε > 0` (complementary paths of at least `εW` blocks; in the paper `ε = 4R`). There is
`C`, **chosen before the total-length ratio `T`**, and then `W₀ = W₀(T)`, such that for every admissible `p` with
`p.b = b`, `p.W ≥ W₀`, `n ≤ TW`, every collar layout with all complementary paths of length `≥ εW`, either
pairing, every stage and every bulk energy: `E g₀² ≤ C` for the defect `g₀ = Tr(I - r₀*r₀)` of the compressed
zero-source response (`conductance`), under the original prior. -/
theorem sequentialCollars_conductance (hTU : TransmissionLengthUniformContract) {b : ℝ}
    (hb0 : 0 < b) (hb1 : b < 1 / 2) {κI : ℝ} (hκI : 0 < κI) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ T : ℝ, ∃ W₀ : ℕ, ∀ p : Parameters, p.b = b → W₀ ≤ p.W →
      (p.n : ℝ) ≤ T * p.W →
      ∀ {m : ℕ} (L : Fin m → ℕ) (s : ZMod p.n) (_hL : IsCollarLayout p.n L),
        (∀ j, ε * p.W ≤ L j) → ∀ (π : Pairing) (S : Finset (Fin m)) (k : Fin m), k ∉ S →
        ∀ (buf : ℕ) (e : ℝ), e ∈ bulkInterval κI →
        ∫⁻ ω, ‖conductance (oldResponse (boundaryZ b e) (oldX0 L s π S k b e buf ω))‖ₑ ^ (2 : ℝ)
            ∂(ringCoordLaw p.n p.W p.b) ≤ ENNReal.ofReal C := by
  obtain ⟨C₀, hC₀⟩ := hTU.conductance b hb0 hb1 κI ε 2 hκI hε (by norm_num)
  refine ⟨4 * max C₀ 0, fun T => ?_⟩
  obtain ⟨W₀, hW₀⟩ := hC₀ T
  refine ⟨W₀, ?_⟩
  intro p hpb hW hn m L s hL hεL π S k hk buf e he
  subst hpb
  have he1 : -2 < e := by have := he.1; linarith
  have he2 : e < 2 := by have := he.2; linarith
  set P := ringCoordLaw p.n p.W p.b
  have hmom : ∀ (p₀ : ZMod p.n) (r : ℕ), IsOldRun L s π S k p₀ r → ε * p.W ≤ r →
      ∫⁻ ω, ‖nearConductance p.b e (pathSchur e (runSample p₀ r ω))‖ₑ ^ (2 : ℝ) ∂P ≤
        ENNReal.ofReal C₀ := by
    intro p₀ r hr hεr
    have hrn : r < p.n := by have := hr.lt; omega
    have hrT : (r : ℝ) ≤ T * p.W := by
      have : (r : ℝ) ≤ p.n := by exact_mod_cast hrn.le
      linarith
    have hf : Measurable fun ps : PathSample p.W r =>
        ‖nearConductance p.b e (pathSchur e ps)‖ₑ ^ (2 : ℝ) :=
      (((measurable_nearConductance p.b e).comp (measurable_pathSchur e)).enorm).pow_const _
    rw [(hasLaw_runSample (W := p.W) p₀ hr.one_le hrn p.b).lintegral_comp
      (f := fun ps : PathSample p.W r => ‖nearConductance p.b e (pathSchur e ps)‖ₑ ^ (2 : ℝ))
      hf.aemeasurable,
      ← (hasLaw_pathAt p.W r p.b hr.one_le).lintegral_comp hf.aemeasurable]
    simp_rw [← pathConductance_eq]
    exact hW₀ p.W hW e he r hεr hrT
  have hlen := compRun_lengths (s := s) hL π S k (ℓ := ⌈ε * p.W⌉₊)
    (fun j => Nat.ceil_le.mpr (hεL j))
  have hR := hmom _ _ (compRunR_isOldRun hL π S k)
    ((Nat.le_ceil _).trans (by exact_mod_cast hlen.1.1))
  have hL' := hmom _ _ (compRunL_isOldRun hL π S k)
    ((Nat.le_ceil _).trans (by exact_mod_cast hlen.2.1))
  have hae := ae_certificate_bounds p L s hL π hk he1 he2 buf
  set gR := fun ω : RingCoords p.n p.W => nearConductance p.b e (pathSchur e
    (runSample (compRunR (s := s) hL π S k).1
    (compRunR (s := s) hL π S k).2 ω))
  set gL := fun ω : RingCoords p.n p.W => nearConductance p.b e (pathSchur e
    (runSample (compRunL (s := s) hL π S k).1
    (compRunL (s := s) hL π S k).2 ω))
  have hgRm : Measurable fun ω : RingCoords p.n p.W => ‖gR ω‖ₑ ^ (2 : ℝ) :=
    ((((measurable_nearConductance p.b e).comp (measurable_pathSchur e)).comp
      (measurable_runSample _ _)).enorm).pow_const _
  calc ∫⁻ ω, ‖conductance (oldResponse (boundaryZ p.b e) (oldX0 L s π S k p.b e buf ω))‖ₑ ^
          (2 : ℝ) ∂P
      ≤ ∫⁻ ω, (2 : ℝ≥0∞) ^ ((2 : ℝ) - 1) * (‖gR ω‖ₑ ^ (2 : ℝ) + ‖gL ω‖ₑ ^ (2 : ℝ)) ∂P := by
        refine lintegral_mono_ae ?_
        filter_upwards [hae] with ω hω
        refine le_trans (ENNReal.rpow_le_rpow ?_ (by norm_num))
          (ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ (by norm_num))
        rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
          ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
        exact ENNReal.ofReal_le_ofReal hω.2
    _ = 2 * (∫⁻ ω, ‖gR ω‖ₑ ^ (2 : ℝ) ∂P + ∫⁻ ω, ‖gL ω‖ₑ ^ (2 : ℝ) ∂P) := by
        rw [lintegral_const_mul' _ _ (by simp), lintegral_add_left hgRm]
        norm_num
    _ ≤ 2 * (ENNReal.ofReal C₀ + ENNReal.ofReal C₀) := by gcongr
    _ ≤ ENNReal.ofReal (4 * max C₀ 0) := by
        rw [show (4 : ℝ) * max C₀ 0 = 2 * (max C₀ 0 + max C₀ 0) by ring,
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add (le_max_right _ _)
            (le_max_right _ _)]
        gcongr <;> norm_num

end Certificate

end BlockBand.Endpoints
