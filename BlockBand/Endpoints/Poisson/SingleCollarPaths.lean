module

public import BlockBand.Endpoints.Poisson.SingleCollarPathsNetwork
public import BlockBand.Endpoints.Poisson.SingleCollarWardAssembly

/-!
# The source Gram matrix on the components of the old network

We bound `Tr Q_C^q` by the fractional traces of the interval sources of the at most `m` path
components of the old network, and prove `ScwComponentPaths`.

* `scp_intervalSource_eq`: `Q(q) = 𝒰*diag(q((n-i)/W)/W²)𝒰` on the path positions `i`.
* `scp_sourceGram_le` (deterministic, every sample): for every source profile `qs ≥ 0` equal to
  `1` on the source windows,
  `Tr Q_C^q ≤ Σ_{i ∈ S ∪ {k}} Tr Q(qs i)^q` (`0 < q ≤ 1`), where `Q(qs i)` is the interval source
  of the run sample of component `i` (the run right of collar `i`) read as a grown path. Proof:
  the old network is the stage matrix of `S ∪ {k}` (`stageMatrix_after_reindex`), whose
  components are two-port Gaussian paths; `scp_gram_le`; profile monotonicity.
* **`scwComponentPaths : ScwComponentPaths`**: lengths `len i = scpLen` on `S ∪ {k}` and `0` on
  unused slots; the law clause is `scp_map_intervalSource_lift` with the run-sample law
  `hasLaw_runSample` and the length marginal `scp_growthPathLaw_map_pathAt`.
* `scsWardScattering : ScsWardScattering` and `peSameVolumeLogError_of_remoteHigher` (the
  analogue of `peSameVolumeLogError_of_componentPaths` without the hypothesis
  `ScwComponentPaths`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Matrix Set Function
open BlockBand.Internal.Contracts.TransmissionPath (fracTrace intervalSource growthPathLaw
  GrowthPath FullSite fullPathMatrix boundaryToInterior tagResponse tagProjection)
open BlockBand.Internal.Contracts.Layers (boundaryZ MatchedTracesContract)
open BlockBand.Internal.Contracts.Critical (CollarKernelContract)
open BlockBand.Internal.Contracts.TransmissionUniform (TransmissionLengthUniformContract)
open BlockBand.Internal.Contracts.Inputs (PassiveLog)
open scoped ComplexOrder

/-!
## The interval source as a diagonal sandwich
-/

section Interval

/-- `Q(q) = 𝒰*diag(v)𝒰` with `v` the profile weight of the path position. -/
theorem scp_intervalSource_eq (b E : ℝ) (W n : ℕ) (q : ℝ → ℝ) (ω : GrowthPath W) :
    intervalSource b E W n q ω = (boundaryToInterior b E W n ω)ᴴ *
      diagonal (fun a : Fin n × Fin W =>
        ((q (((n - 1 - a.1.val + 1 : ℕ) : ℝ) / W) / (W : ℝ) ^ 2 : ℝ) : ℂ)) *
      boundaryToInterior b E W n ω := by
  ext p p'
  rw [scp_conj_diag_apply]
  unfold intervalSource
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul]
  unfold tagResponse tagProjection
  simp only [scp_conj_diag_apply]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  have ha := a.1.isLt
  rw [Finset.sum_eq_single (n - 1 - a.1.val)]
  · have h1 : n - 1 - a.1.val < n := by omega
    have h2 : n - 1 - (n - 1 - a.1.val) = a.1.val := by omega
    simp only [h1, h2, and_self, ite_true, mul_one]
    ring
  · intro k _ hk
    have h : ¬ (k < n ∧ a.1.val = n - 1 - k) := by omega
    simp only [h, ite_false, mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

/-- **Profile monotonicity.** If `w ∈ {0,1}` and the profile is `1` wherever `w = 1`, then
`W⁻²𝒰*diag(w)𝒰 ⪯ Q(q)`. -/
theorem scp_intervalSource_sub_posSemidef (b E : ℝ) (W n : ℕ) (q : ℝ → ℝ) (hq : ∀ x, 0 ≤ q x)
    (ω : GrowthPath W) (w : Fin n × Fin W → ℝ)
    (hw : ∀ a, w a = 0 ∨ (w a = 1 ∧ q (((n - 1 - a.1.val + 1 : ℕ) : ℝ) / W) = 1)) :
    (intervalSource b E W n q ω - (((1 / (W : ℝ) ^ 2 : ℝ)) : ℂ) •
      ((boundaryToInterior b E W n ω)ᴴ * diagonal (fun a => (w a : ℂ)) *
        boundaryToInterior b E W n ω)).PosSemidef := by
  set B := boundaryToInterior b E W n ω
  have heq : intervalSource b E W n q ω - (((1 / (W : ℝ) ^ 2 : ℝ)) : ℂ) •
      (Bᴴ * diagonal (fun a => (w a : ℂ)) * B) =
      Bᴴ * diagonal (fun a : Fin n × Fin W =>
        ((q (((n - 1 - a.1.val + 1 : ℕ) : ℝ) / W) / (W : ℝ) ^ 2 - 1 / (W : ℝ) ^ 2 * w a : ℝ) : ℂ)) *
        B := by
    rw [scp_intervalSource_eq]
    ext p p'
    rw [Matrix.sub_apply, Matrix.smul_apply, scp_conj_diag_apply, scp_conj_diag_apply,
      scp_conj_diag_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    push_cast; ring
  rw [heq]
  refine scp_posSemidef_conj_diag B fun a => ?_
  rcases hw a with h | ⟨h1, h2⟩
  · rw [h, mul_zero, sub_zero]
    exact div_nonneg (hq _) (sq_nonneg _)
  · rw [h1, h2]; simp

end Interval

/-!
## The old network as a stage matrix
-/

section Network

variable {m n W : ℕ} {L : Fin m → ℕ} {s : ZMod n}

variable (L s) in
/-- The port/interior order of the old network as the surviving sites of stage `S ∪ {k}`. -/
def scpSigma (hL : IsCollarLayout n L) {S : Finset (Fin m)} {k : Fin m} (hk : k ∉ S) :
    ScwPorts (W := W) L s S k ⊕ ScwInner (W := W) L s S k ≃ StageSite L s (insert k S) W :=
  (scwEquiv L s S k).trans (afterEquiv hL hk).symm

theorem scp_full_eq_stage (hL : IsCollarLayout n L) (π : Pairing) {S : Finset (Fin m)} {k : Fin m}
    (hk : k ∉ S) (b e : ℝ) (buf : ℕ) (t : ℝ) (ω : RingCoords n W) :
    scwFull L s π S k b e buf t ω =
      (stageMatrix L s π (insert k S) e (boundaryZ b e) buf t ω).submatrix
        (scpSigma L s hL hk) (scpSigma L s hL hk) := by
  unfold scwFull
  rw [← stageMatrix_after_reindex hL hk π e (boundaryZ b e) buf t ω, submatrix_submatrix]
  rfl

theorem scp_sigma_inr (hL : IsCollarLayout n L) {S : Finset (Fin m)} {k : Fin m} (hk : k ∉ S)
    (u : ScwInner (W := W) L s S k) : (scpSigma L s hL hk (Sum.inr u)).1 = u.1.1 := rfl

theorem scp_sigma_inl_inl (hL : IsCollarLayout n L) {S : Finset (Fin m)} {k : Fin m} (hk : k ∉ S)
    (c : Fin 2 × Fin W) : (scpSigma L s hL hk (Sum.inl (Sum.inl c))).1 = outerSite L s k c := rfl

theorem scp_sigma_inl_inr (hL : IsCollarLayout n L) {S : Finset (Fin m)} {k : Fin m} (hk : k ∉ S)
    (x : ScwMatched (W := W) L s S k) : (scpSigma L s hL hk (Sum.inl (Sum.inr x))).1 = x.1.1 := rfl

theorem scp_isDeleted_mono {S : Finset (Fin m)} {k : Fin m} {p : ZMod n}
    (h : IsDeleted L s S p) : IsDeleted L s (insert k S) p := by
  obtain ⟨j, hj, he⟩ := h
  exact ⟨j, Finset.mem_insert_of_mem hj, he⟩

theorem scp_isMatched_mono {S : Finset (Fin m)} {k : Fin m} {p : ZMod n}
    (h : IsMatched L s S p) : IsMatched L s (insert k S) p := by
  obtain ⟨j, hj, he⟩ := h
  exact ⟨j, Finset.mem_insert_of_mem hj, he⟩

/-- Every outer site of a collar of `S ∪ {k}` is a port of the old network. -/
theorem scp_port_exists (hL : IsCollarLayout n L) {S : Finset (Fin m)} {k : Fin m} (hk : k ∉ S)
    {j : Fin m} (hj : j ∈ insert k S) (c : Fin 2 × Fin W) :
    ∃ p, (scpSigma L s hL hk (Sum.inl p)).1 = outerSite L s j c := by
  by_cases hjk : j = k
  · subst hjk
    exact ⟨Sum.inl c, rfl⟩
  · have hjS : j ∈ S := by
      rcases Finset.mem_insert.mp hj with h | h
      · exact absurd h hjk
      · exact h
    have hLj := hL.2 j
    have hLk := hL.2 k
    have hc := c.1.isLt
    have hnd : ¬ IsDeleted L s S (outerSite L s j c).1 :=
      scp_collar_not_deleted hL S j (o := 2 * c.1.val) (by omega) (by omega)
    have hnc : ¬ InCollar L s k (outerSite L s j c).1 := by
      rintro (he | he | he) <;>
      · exact hjk ((unitPos_inj hL s (by omega) (by omega)).mp he).1
    have hm : IsMatched L s S (outerSite L s j c).1 := by
      refine ⟨j, hjS, ?_⟩
      rcases c with ⟨c, w⟩
      fin_cases c
      · exact Or.inl rfl
      · exact Or.inr rfl
    exact ⟨Sum.inr ⟨⟨outerSite L s j c, hnd, hnc⟩, hm⟩, rfl⟩

end Network

/-!
## The components of the old network
-/

section Components

variable {m n W : ℕ} {L : Fin m → ℕ} {s : ZMod n}

theorem scp_site_not_deleted' (hL : IsCollarLayout n L) (π : Pairing) (T : Finset (Fin m))
    (i : Fin m) (x : FullSite W (scpLen L s hL π T i)) :
    ¬ IsDeleted L s T (scpSite L s π (unitPos n L s i 3) (scpLen L s hL π T i) x).1 := by
  obtain ⟨j, -, hR⟩ := scp_comp_right (s := s) hL π T i
  exact scp_site_not_deleted hL (scp_comp_run hL π T i) hR x

variable (L s) in
/-- The sites of component `i` as surviving sites of stage `T`. -/
def scpPhi (hL : IsCollarLayout n L) (π : Pairing) (T : Finset (Fin m)) (i : Fin m) :
    FullSite W (scpLen L s hL π T i) → StageSite L s T W :=
  fun x => ⟨scpSite L s π (unitPos n L s i 3) (scpLen L s hL π T i) x,
    scp_site_not_deleted' hL π T i x⟩

theorem scp_comp_right_mem (hL : IsCollarLayout n L) (π : Pairing) {T : Finset (Fin m)}
    {i : Fin m} (hi : i ∈ T) :
    ∃ j ∈ T, runRight L s π (unitPos n L s i 3) (scpLen L s hL π T i) = unitPos n L s j 0 := by
  obtain ⟨j, hj, hR⟩ := scp_comp_right (s := s) hL π T i
  rw [Finset.insert_eq_of_mem hi] at hj
  exact ⟨j, hj, hR⟩

variable [NeZero n] in
/-- **`Tr Q_C^q ≤ Σ_{components} Tr (W⁻²𝒰_i*P_{C_i}𝒰_i)^q`** on the explicit old network. -/
theorem scp_gram_le_components (hL : IsCollarLayout n L) (π : Pairing) {S : Finset (Fin m)}
    {k : Fin m} (hk : k ∉ S) (b e : ℝ) (buf : ℕ) (ω : RingCoords n W) {q : ℝ} (hq0 : 0 < q)
    (hq1 : q ≤ 1) :
    fracTrace q (scwGram (scwSrc (W := W) L s S k buf) (scwFull L s π S k b e buf 0 ω)⁻¹) ≤
      ∑ i ∈ insert k S, fracTrace q (scpCompGram (scpSigma L s hL hk)
        (fun u => InSource L s buf u.1.1.1) (scpPhi L s hL π (insert k S) i)
        (fullPathMatrix b e W (scpLen L s hL π (insert k S) i)
          (scpLift _ (runSample (unitPos n L s i 3) (scpLen L s hL π (insert k S) i) ω)))) := by
  classical
  set T := insert k S with hT
  set σ := scpSigma (W := W) L s hL hk
  have hkT : k ∈ T := Finset.mem_insert_self _ _
  rw [scp_full_eq_stage hL π hk b e buf 0 ω]
  refine scp_gram_le σ (stageMatrix L s π T e (boundaryZ b e) buf 0 ω)
    (fun u => InSource L s buf u.1.1.1) T (fun i => scpLen L s hL π T i)
    (fun i => scpPhi L s hL π T i) _ ?_ ?_ ?_ ?_ ?_ ?_ hq0 hq1
  · -- injectivity
    intro i hi x y hxy
    obtain ⟨j, -, hR⟩ := scp_comp_right_mem (s := s) hL π hi
    exact scp_site_injective hL (scp_comp_run hL π T i) hR (congrArg Subtype.val hxy)
  · -- the block
    intro i hi x y
    obtain ⟨j, hj, hR⟩ := scp_comp_right_mem (s := s) hL π hi
    exact scp_block hL hi hj (scp_comp_run hL π T i) hR b e buf ω x y
  · -- decoupling
    intro i hi x y hy
    obtain ⟨j, hj, hR⟩ := scp_comp_right_mem (s := s) hL π hi
    have hy' : y.1 ∉ Set.range (scpSite L s π (unitPos n L s i 3) (scpLen L s hL π T i)) := by
      rintro ⟨x', hx'⟩
      exact hy ⟨x', Subtype.ext hx'⟩
    exact scp_dec hL hi hj (scp_comp_run hL π T i) hR e (boundaryZ b e) buf 0 ω x y.1 y.2 hy'
  · -- path sites are interior
    intro i hi a
    have h := scp_comp_run (s := s) hL π T i
    have hp : (scpSite L s π (unitPos n L s i 3) (scpLen L s hL π T i) (Sum.inl a) : RingSite n W) =
        (unitPos n L s i 3 + (a.1.val : ℕ), a.2) := rfl
    have hnd : ¬ IsDeleted L s S (unitPos n L s i 3 + (a.1.val : ℕ)) := fun hd =>
      h.not_deleted a.1.isLt (scp_isDeleted_mono hd)
    have hnc : ¬ InCollar L s k (unitPos n L s i 3 + (a.1.val : ℕ)) := fun hc =>
      h.avoid a.1.val a.1.isLt ⟨k, Finset.mem_insert_of_mem hkT, hc⟩
    have hnm : ¬ IsMatched L s S (unitPos n L s i 3 + (a.1.val : ℕ)) := fun hm =>
      h.not_matched a.1.isLt (scp_isMatched_mono hm)
    exact ⟨⟨⟨(unitPos n L s i 3 + (a.1.val : ℕ), a.2), hnd, hnc⟩, hnm⟩, Subtype.ext hp.symm⟩
  · -- port sites are network ports
    intro i hi c
    obtain ⟨j, hj, hR⟩ := scp_comp_right_mem (s := s) hL π hi
    rcases c with ⟨c, w⟩
    fin_cases c
    · obtain ⟨p, hp⟩ := scp_port_exists (s := s) hL hk hi ((1 : Fin 2), w)
      refine ⟨p, Subtype.ext ?_⟩
      rw [hp]
      simp only [scpPhi, scpSite, Sum.elim_inr, runPortSite, Fin.zero_eta, ite_true,
        scp_unitPos_three_sub_one]
      rfl
    · obtain ⟨p, hp⟩ := scp_port_exists (s := s) hL hk hj ((0 : Fin 2), w)
      refine ⟨p, Subtype.ext ?_⟩
      rw [hp]
      simp only [scpPhi, scpSite, Sum.elim_inr, runPortSite, Fin.mk_one,
        show ((1 : Fin 2) = 0) = False from by simp, ite_false, hR]
      rfl
  · -- every network port belongs to a component
    have hcov : ∀ j ∈ T, ∀ w : Fin W, ∀ c : Fin 2, ∃ i ∈ T, ∃ c',
        (scpPhi (W := W) L s hL π T i (Sum.inr c')).1 = outerSite L s j (c, w) := by
      intro j hj w c
      fin_cases c
      · obtain ⟨i, hi, hR⟩ := scp_right_cover (s := s) hL π hj
        refine ⟨i, hi, ((1 : Fin 2), w), ?_⟩
        simp only [scpPhi, scpSite, Sum.elim_inr, runPortSite,
          show ((1 : Fin 2) = 0) = False from by simp, ite_false, hR]
        rfl
      · refine ⟨j, hj, ((0 : Fin 2), w), ?_⟩
        simp only [scpPhi, scpSite, Sum.elim_inr, runPortSite, ite_true,
          scp_unitPos_three_sub_one]
        rfl
    rintro (c | x)
    · obtain ⟨i, hi, c', hc'⟩ := hcov k hkT c.2 c.1
      exact ⟨i, hi, c', Subtype.ext (by rw [scp_sigma_inl_inl, hc'])⟩
    · obtain ⟨j, hjS, hjx⟩ := x.2
      have hj : j ∈ T := Finset.mem_insert_of_mem hjS
      rcases hjx with he | he
      · obtain ⟨i, hi, c', hc'⟩ := hcov j hj x.1.1.2 0
        refine ⟨i, hi, c', Subtype.ext ?_⟩
        rw [scp_sigma_inl_inr, hc']
        exact Prod.ext he rfl
      · obtain ⟨i, hi, c', hc'⟩ := hcov j hj x.1.1.2 1
        refine ⟨i, hi, c', Subtype.ext ?_⟩
        rw [scp_sigma_inl_inr, hc']
        exact Prod.ext he rfl

end Components

/-!
## `Tr Q_C^q` against the interval sources of the components
-/

section Bound

/-- **The deterministic component bound** (every sample): for source profiles `qs ≥ 0` equal to
`1` on the source windows of the components `i ∈ S ∪ {k}`,
`Tr Q_C^q ≤ Σ_{i ∈ S ∪ {k}} Tr Q(qs i)^q`, `0 < q ≤ 1`, with `Q(qs i)` the interval source of the
run sample of component `i` read as a grown path. -/
theorem scp_sourceGram_le (P : Parameters) {m : ℕ} (L : Fin m → ℕ) (hL : IsCollarLayout P.n L)
    (π : Pairing) {S : Finset (Fin m)} {k : Fin m} (hk : k ∉ S) (buf : ℕ) (e : ℝ)
    (qs : Fin m → ℝ → ℝ) (hqs : ∀ i x, 0 ≤ qs i x)
    (hwin : ∀ i ∈ insert k S, ∀ x ∈ Icc (((buf : ℝ) - 2) / P.W)
      (((scpLen L (0 : ZMod P.n) hL π (insert k S) i : ℝ) - buf + 2) / P.W), qs i x = 1)
    (ω : RingCoords P.n P.W) {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) :
    fracTrace q (scwSourceGram P L π S k e buf ω) ≤
      ∑ i ∈ insert k S, fracTrace q (intervalSource P.b e P.W
        (scpLen L (0 : ZMod P.n) hL π (insert k S) i) (qs i)
        (scpLift _ (runSample (unitPos P.n L 0 i 3) (scpLen L (0 : ZMod P.n) hL π (insert k S) i)
          ω))) := by
  classical
  set T := insert k S with hT
  set c : ℝ := 1 / (P.W : ℝ) ^ 2 with hcdef
  have hc : 0 ≤ c := by positivity
  have hG := scp_gram_le_components (s := (0 : ZMod P.n)) (W := P.W) hL π hk P.b e buf ω hq0 hq1
  set σ := scpSigma (W := P.W) L (0 : ZMod P.n) hL hk
  set src : ScwInner (W := P.W) L (0 : ZMod P.n) S k → Prop :=
    fun u => InSource L (0 : ZMod P.n) buf u.1.1.1
  unfold scwSourceGram
  rw [fracTrace_smul (scw_posSemidef_gram _ _).isHermitian hc]
  have hKpsd : ∀ i, (scpCompGram σ src (scpPhi L (0 : ZMod P.n) hL π T i)
      (fullPathMatrix P.b e P.W (scpLen L (0 : ZMod P.n) hL π T i)
        (scpLift _ (runSample (unitPos P.n L 0 i 3) (scpLen L (0 : ZMod P.n) hL π T i) ω)))).PosSemidef :=
    fun i => scp_posSemidef_conj_diag _ fun a => scp_ind_nonneg _
  refine (mul_le_mul_of_nonneg_left hG (Real.rpow_nonneg hc q)).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [← fracTrace_smul (hKpsd i).isHermitian hc]
  set r := scpLen L (0 : ZMod P.n) hL π T i with hr
  obtain ⟨j, hj, hR⟩ := scp_comp_right_mem (s := (0 : ZMod P.n)) hL π hi
  refine fracTrace_mono ((hKpsd i).smul (Complex.zero_le_real.mpr hc)).isHermitian
    (intervalSource_posSemidef _ _ _ _ _ (hqs i) _).isHermitian
    (scp_intervalSource_sub_posSemidef P.b e P.W r (qs i) (hqs i) _ _ fun a => ?_) hq0.le
  -- the weight of a path site: `1` only on source sites, where the profile is `1`
  by_cases hex : ∃ u, src u ∧ σ (Sum.inr u) = scpPhi L (0 : ZMod P.n) hL π T i (Sum.inl a)
  · right
    refine ⟨by simp only [scpWeight, scpInd]; exact ite_eq_left hex, ?_⟩
    obtain ⟨u, hsrc, hu⟩ := hex
    have hu1 : u.1.1 = (unitPos P.n L 0 i 3 + (a.1.val : ℕ), a.2) := congrArg Subtype.val hu
    have hs : InSource L (0 : ZMod P.n) buf (unitPos P.n L 0 i 3 + (a.1.val : ℕ)) := by
      have := hsrc; simp only [src, hu1] at this; exact this
    have hwd := scp_window hL hR a.1.isLt hs
    have ha := a.1.isLt
    have hx : ((r - 1 - a.1.val + 1 : ℕ) : ℝ) = (r : ℝ) - a.1.val := by
      rw [show r - 1 - a.1.val + 1 = r - a.1.val by omega, Nat.cast_sub (by omega)]
    have hcast1 : ((a.1.val : ℕ) : ℝ) + buf < r := by exact_mod_cast hwd.2
    have hcast2 : (buf : ℝ) ≤ a.1.val := by exact_mod_cast hwd.1
    refine hwin i hi _ ⟨?_, ?_⟩ <;> rw [hx] <;>
      exact div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  · left
    simp only [scpWeight, scpInd]
    exact ite_eq_right hex

end Bound

/-!
## `ScwComponentPaths`
-/

section Paths

/-- **`ScwComponentPaths` holds.** Lengths: `scpLen` on the components `i ∈ S ∪ {k}`, `0` on the
unused slots; `Qc i` is the interval source of the run sample of component `i` (`0` on unused
slots). -/
theorem scwComponentPaths : ScwComponentPaths := by
  intro P m L hL π S k hk buf e _ _
  classical
  set T := insert k S with hT
  set len : Fin m → ℕ := fun i => if i ∈ T then scpLen L (0 : ZMod P.n) hL π T i else 0 with hlen
  have hrun := fun i => scp_comp_run (s := (0 : ZMod P.n)) hL π T i
  refine ⟨len, fun i => ?_, fun qs hqs hwin => ?_⟩
  · simp only [len]
    split_ifs
    · have := (hrun i).lt; omega
    · exact Nat.zero_le _
  set Qc : Fin m → RingCoords P.n P.W → Matrix (Fin 2 × Fin P.W) (Fin 2 × Fin P.W) ℂ :=
    fun i ω => if i ∈ T then intervalSource P.b e P.W (scpLen L (0 : ZMod P.n) hL π T i) (qs i)
      (scpLift _ (runSample (unitPos P.n L 0 i 3) (scpLen L (0 : ZMod P.n) hL π T i) ω)) else 0
    with hQc
  have hQin : ∀ i ∈ T, Qc i = fun ω => intervalSource P.b e P.W
      (scpLen L (0 : ZMod P.n) hL π T i) (qs i)
      (scpLift _ (runSample (unitPos P.n L 0 i 3) (scpLen L (0 : ZMod P.n) hL π T i) ω)) :=
    fun i hi => funext fun ω => ite_eq_left hi
  have hQout : ∀ i ∉ T, Qc i = fun _ => 0 := fun i hi => funext fun ω => ite_eq_right hi
  refine ⟨Qc, fun i => ?_, fun i => ?_, ?_⟩
  · by_cases hi : i ∈ T
    · rw [hQin i hi]
      exact (sca2_measurable_intervalSource _ _ _ _ _).comp
        ((scp_measurable_lift _).comp (measurable_runSample _ _))
    · rw [hQout i hi]
      exact measurable_const
  · by_cases hi : i ∈ T
    · have hl : len i = scpLen L (0 : ZMod P.n) hL π T i := ite_eq_left hi
      rw [hQin i hi, hl]
      have h := hrun i
      exact scp_map_intervalSource_lift P.b e h.one_le (qs i)
        (hasLaw_runSample _ h.one_le (by have := h.lt; omega) P.b)
    · have hl : len i = 0 := ite_eq_right hi
      have h0 : intervalSource P.b e P.W 0 (qs i) = fun _ => 0 := by
        funext ω; simp [intervalSource]
      have := isProbabilityMeasure_growthPathLaw P.W P.b
      rw [hQout i hi, hl, h0, Measure.map_const, Measure.map_const, measure_univ, measure_univ]
  · refine Filter.Eventually.of_forall fun ω q hq0 hq1 => ?_
    have hwin' : ∀ i ∈ T, ∀ x ∈ Icc (((buf : ℝ) - 2) / P.W)
        (((scpLen L (0 : ZMod P.n) hL π T i : ℝ) - buf + 2) / P.W), qs i x = 1 := by
      intro i hi x hx
      have hl : len i = scpLen L (0 : ZMod P.n) hL π T i := ite_eq_left hi
      have := hwin i x
      rw [hl] at this
      exact this hx
    calc fracTrace q (scwSourceGram P L π S k e buf ω)
        ≤ ∑ i ∈ T, fracTrace q (intervalSource P.b e P.W (scpLen L (0 : ZMod P.n) hL π T i) (qs i)
            (scpLift _ (runSample (unitPos P.n L 0 i 3) (scpLen L (0 : ZMod P.n) hL π T i) ω))) :=
          scp_sourceGram_le P L hL π hk buf e qs (fun i x => (hqs i x).1) hwin' ω hq0 hq1.le
      _ = ∑ i ∈ T, fracTrace q (Qc i ω) :=
          Finset.sum_congr rfl fun i hi => by rw [hQin i hi]
      _ ≤ ∑ i, fracTrace q (Qc i ω) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun i _ _ => fracTrace_nonneg _ _

/-- **`ScsWardScattering` holds** (`scsWardScattering_of_componentPaths` and `scwComponentPaths`). -/
theorem scsWardScattering : ScsWardScattering :=
  scsWardScattering_of_componentPaths scwComponentPaths

/-- **`PeSameVolumeLogError` from `CollarKernelContract`, `MatchedTracesContract`,
`TransmissionLengthUniformContract`, `PassiveLog` and `RemoteHigherUniformStatement`**
(`peSameVolumeLogError_of_componentPaths` with `scwComponentPaths`). -/
theorem peSameVolumeLogError_of_remoteHigher (hK : CollarKernelContract)
    (hMT : MatchedTracesContract) (hTU : TransmissionLengthUniformContract) (hPL : PassiveLog)
    (hRHU : RemoteHigherUniformStatement) : PeSameVolumeLogError :=
  peSameVolumeLogError_of_componentPaths hK hMT hTU hPL hRHU scwComponentPaths

end Paths

end BlockBand.Endpoints
