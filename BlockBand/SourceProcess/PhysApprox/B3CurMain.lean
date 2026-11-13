module

public import BlockBand.SourceProcess.PhysApprox.B3CurTimeS
public import BlockBand.SourceProcess.PhysApprox.B3Pins
public import BlockBand.SourceProcess.ClosedReduce.Entrance

/-!
# The closed current `ComplexClosedCurrent`

At the final length `n = ⌊WT⌋ ≥ n_s`, with `N_{n_s}⋯N_{n-1}` the physical transport, `C_n(z)`
the closing map with the time-`s` data and `|z| = 1`:

* **`closed_current_frame`** (deterministic): if `𝕊_j` is unitary at every length, the transport
  keeps the far output at every `j ≥ 1`, the closed transport identity and the invertibility of
  `1 - zN_j` hold, `1 ≤ n_s`, the cap holds (`t_k ≤ h²` for `k ≥ K`), retained `t_k < 1`,
  `h² < 1`, and `V_s` satisfies the two almost-sure clauses of `IsTimeSFrame`, then
  `C_nᴴ(𝕊_nᴴP𝕊_n - P)C_n = X 𝖣 Xᴴ`, `X = C_nᴴ(N_{n_s}⋯N_{n-1})ᴴV_s` (the closed current
  columns). The proof: current conservation along the path, the iterated closed transport,
  and at time `s` the closed current equals `V_s𝖣V_sᴴ` (`retCurrent_eq_frame`).
* `closedSourceData_three_eq` (deterministic): under the same hypotheses coordinate `3` of
  `closedSourceData` equals `(M𝖣M)_pr` of `b3ClosedGramAt` at `⌊WT⌋`, exactly.
* **`complexClosedCurrent_holds : ComplexClosedCurrent`**: the difference vanishes
  almost surely on the cap event, so the probability in `ComplexClosedCurrent` is `0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3Cur

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedSum
open BlockBand.SourceProcess.ClosedReduce BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess BlockBand.Transmission.Bridge
open BlockBand.SourceProcess.PhysApprox.B3

variable {W : ℕ} {b E s h : ℝ} {K : ℕ} {ω : GrowthPath W}

/-!
## The closed current at the final length
-/

/-- **The closed current is the closed current-column current** (deterministic). -/
theorem closed_current_frame (Vs : Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) {n : ℕ}
    (hn : closeLen s W ≤ n) (hs : 1 ≤ closeLen s W)
    (hU : ∀ j, scatteringMatrix b E W j ω * (scatteringMatrix b E W j ω)ᴴ = 1)
    (hfar : ∀ j, 1 ≤ j → (1 - nearPortProj W) * scatteringMatrix b E W j ω *
      transportN b E W j ω = (1 - nearPortProj W) * scatteringMatrix b E W (j + 1) ω)
    (hT : ∀ j, 1 ≤ j → ∀ z : ℂ, ‖z‖ ≤ 1 →
      (physClosingMapAt b E s h W (j + 1) ω z)ᴴ * (transportN b E W j ω)ᴴ =
        ((1 - farEmbed (omittedProj b E h W (closeLen s W) ω)) *
          (transportN b E W j ω * physClosingMapAt b E s h W (j + 1) ω z))ᴴ *
          (physClosingMapAt b E s h W j ω z)ᴴ)
    (hR : ∀ j, 1 ≤ j → ∀ z : ℂ, ‖z‖ ≤ 1 →
      IsUnit (1 - z • closingN (scatteringMatrix b E W j ω)
        (farEmbed (omittedProj b E h W (closeLen s W) ω))
        (farEmbed (closingPairing b E h W (closeLen s W) ω))).det)
    (hcap : ∀ k, K ≤ k → physTseq b E s W ω k ≤ h ^ 2)
    (hlt : ∀ k : Fin K, h ^ 2 < physTseq b E s W ω k.val → physTseq b E s W ω k.val < 1)
    (hh : h ^ 2 < 1)
    (hG : gramPair (nearPortProj W) Vs =
      curGramOf (initialGram K (Fin 0) (physTseq b E s W ω) h))
    (hE : ∀ x k, ((physOutProj b E s W ω - nearPortProj W) * Vs) x k =
      modeEig (physTseq b E s W ω k.1.val) k.2 * Vs x k)
    {z : ℂ} (hz : ‖z‖ = 1) :
    (physClosingMapAt b E s h W n ω z)ᴴ *
        ((scatteringMatrix b E W n ω)ᴴ * nearPortProj W * scatteringMatrix b E W n ω -
          nearPortProj W) * physClosingMapAt b E s h W n ω z =
      ((physClosingMapAt b E s h W n ω z)ᴴ *
          (stepProd (fun j => transportN b E W j ω) (closeLen s W) (n - closeLen s W))ᴴ * Vs) *
        sig2 K *
        ((physClosingMapAt b E s h W n ω z)ᴴ *
          (stepProd (fun j => transportN b E W j ω) (closeLen s W) (n - closeLen s W))ᴴ * Vs)ᴴ := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_sub_cancel_left]
  set n₀ := closeLen s W
  set P := nearPortProj W
  set Np := stepProd (fun j => transportN b E W j ω) n₀ m
  set Mp := stepProd (closedTransport b E s h W ω z) n₀ m
  have hPH : Pᴴ = P := nearPortProj_conjTranspose
  have hPP : P * P = P := nearPortProj_mul_self
  have hJ : Npᴴ * ((scatteringMatrix b E W n₀ ω)ᴴ * P * scatteringMatrix b E W n₀ ω - P) * Np =
      (scatteringMatrix b E W (n₀ + m) ω)ᴴ * P * scatteringMatrix b E W (n₀ + m) ω - P := by
    refine current_iterate (fun j => (scatteringMatrix b E W j ω)ᴴ * P *
      scatteringMatrix b E W j ω - P) (fun j => transportN b E W j ω) n₀ m fun i _ => ?_
    exact current_step hPH hPP (mul_eq_one_comm.mp (hU _)) (mul_eq_one_comm.mp (hU _))
      (one_sub_nearPortProj_mul_transportN _ ω) (hfar _ (by omega))
  have hIt := conj_stepProd_iterate (fun j => physClosingMapAt b E s h W j ω z)
    (fun j => transportN b E W j ω) (closedTransport b E s h W ω z) n₀ m
    (fun i _ => hT _ (by omega) z hz.le)
  change (physClosingMapAt b E s h W (n₀ + m) ω z)ᴴ * Npᴴ =
    Mpᴴ * (physClosingMapAt b E s h W n₀ ω z)ᴴ at hIt
  have hIt' : Np * physClosingMapAt b E s h W (n₀ + m) ω z =
      physClosingMapAt b E s h W n₀ ω z * Mp := by
    have := congrArg conjTranspose hIt
    simpa only [conjTranspose_mul, conjTranspose_conjTranspose] using this
  have hfix : (physClosingMapAt b E s h W n₀ ω z)ᴴ * Vs = Vs :=
    closedFix z (omitted_mul_timeSFrame Vs (hU n₀) hG hE)
  have hX : (physClosingMapAt b E s h W (n₀ + m) ω z)ᴴ * Npᴴ * Vs = Mpᴴ * Vs := by
    rw [hIt, Matrix.mul_assoc, hfix]
  have hs0 := closed_timeS_current (K := K) (hU n₀) hcap hlt hh hz (hR n₀ hs z hz.le)
  rw [retCurrent_eq_frame Vs (hU n₀) hcap hlt hh hG hE] at hs0
  rw [hX, ← hJ]
  calc (physClosingMapAt b E s h W (n₀ + m) ω z)ᴴ *
        (Npᴴ * ((scatteringMatrix b E W n₀ ω)ᴴ * P * scatteringMatrix b E W n₀ ω - P) * Np) *
        physClosingMapAt b E s h W (n₀ + m) ω z =
      ((physClosingMapAt b E s h W (n₀ + m) ω z)ᴴ * Npᴴ) *
        ((scatteringMatrix b E W n₀ ω)ᴴ * P * scatteringMatrix b E W n₀ ω - P) *
        (Np * physClosingMapAt b E s h W (n₀ + m) ω z) := by simp only [Matrix.mul_assoc]
    _ = Mpᴴ * ((physClosingMapAt b E s h W n₀ ω z)ᴴ *
        ((scatteringMatrix b E W n₀ ω)ᴴ * P * scatteringMatrix b E W n₀ ω - P) *
        physClosingMapAt b E s h W n₀ ω z) * Mp := by
          rw [hIt, hIt']; simp only [Matrix.mul_assoc]
    _ = Mpᴴ * Vs * sig2 K * (Mpᴴ * Vs)ᴴ := by
          change Mpᴴ * ((physClosingMapAt b E s h W n₀ ω z)ᴴ * (physOutProj b E s W ω - P) *
            physClosingMapAt b E s h W n₀ ω z) * Mp = _
          rw [hs0]
          simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]

/-!
## The probe block of `M𝖣M`
-/

theorem nearPortProj_mul_farEmbed (X : Matrix (Fin W) (Fin W) ℂ) :
    nearPortProj W * farEmbed X = 0 := by
  rw [← conjTranspose_conjTranspose (nearPortProj W * farEmbed X), conjTranspose_mul,
    nearPortProj_conjTranspose, farEmbed_conjTranspose, farEmbed_mul_nearPortProj,
    conjTranspose_zero]

/-- The probe columns of a frame. -/
def prBlock {ι π : Type*} (V : Matrix ι (SrcCol K π) ℂ) : Matrix ι π ℂ :=
  Matrix.of fun z i => V z (Sum.inr i)

/-- The current-column selector. -/
def curSel (K : ℕ) (π : Type*) [DecidableEq π] : Matrix (SrcCol K π) (Fin K × Fin 2) ℂ :=
  Matrix.of fun c c' => if c = Sum.inl c' then 1 else 0

/-- The probe-column selector. -/
def prSel (K : ℕ) (π : Type*) [DecidableEq π] : Matrix (SrcCol K π) π ℂ :=
  Matrix.of fun c i => if c = Sum.inr i then 1 else 0

theorem mul_curSel {ι π : Type*} [Fintype π] [DecidableEq π] (V : Matrix ι (SrcCol K π) ℂ) :
    V * curSel K π = curBlock V := by
  ext z c
  simp [mul_apply, curSel, curBlock]

theorem mul_prSel {ι π : Type*} [Fintype π] [DecidableEq π] (V : Matrix ι (SrcCol K π) ℂ) :
    V * prSel K π = prBlock V := by
  ext z i
  simp [mul_apply, prSel, prBlock]

theorem curBlock_mul {ι ι' π : Type*} [Fintype ι'] (A : Matrix ι ι' ℂ)
    (V : Matrix ι' (SrcCol K π) ℂ) : curBlock (A * V) = A * curBlock V := by
  ext z c
  simp [curBlock, mul_apply]

theorem prBlock_mul {ι ι' π : Type*} [Fintype ι'] (A : Matrix ι ι' ℂ)
    (V : Matrix ι' (SrcCol K π) ℂ) : prBlock (A * V) = A * prBlock V := by
  ext z c
  simp [prBlock, mul_apply]

theorem srcSignature_eq_sel (π : Type*) [Fintype π] [DecidableEq π] :
    srcSignature K π = curSel K π * sig2 K * (curSel K π)ᴴ := by
  have h1 : curSel K π * sig2 K = Matrix.of fun c c' =>
      if c = Sum.inl c' then (if c'.2 = 0 then (1 : ℂ) else -1) else 0 := by
    ext c c'
    simp only [sig2, mul_diagonal, curSel, of_apply]
    split_ifs <;> simp
  rw [h1]
  ext c c'
  simp only [srcSignature, diagonal_apply, mul_apply, of_apply, conjTranspose_apply, curSel]
  rcases c with ⟨k, σ⟩ | i <;> rcases c' with ⟨k', σ'⟩ | i'
  · by_cases hc : (k, σ) = (k', σ')
    · obtain ⟨rfl, rfl⟩ := Prod.ext_iff.1 hc
      rw [Finset.sum_eq_single (k, σ) (fun c _ hc' => by
        have : ¬ (Sum.inl (k, σ) : SrcCol K π) = Sum.inl c := fun e =>
          hc' (Sum.inl_injective e).symm
        simp [this]) (by simp)]
      simp
    · have hc' : ¬ (Sum.inl (k, σ) : SrcCol K π) = Sum.inl (k', σ') := fun e =>
        hc (Sum.inl_injective e)
      simp only [hc', ↓reduceIte]
      refine (Finset.sum_eq_zero fun c _ => ?_).symm
      by_cases h1 : (k, σ) = c
      · subst h1
        have : ¬ (Sum.inl (k', σ') : SrcCol K π) = Sum.inl (k, σ) := fun e =>
          hc (Sum.inl_injective e).symm
        simp [this]
      · have : ¬ (Sum.inl (k, σ) : SrcCol K π) = Sum.inl c := fun e => h1 (Sum.inl_injective e)
        simp [this]
  · simp
  · simp
  · simp

theorem probeBlock_eq_sel {π : Type*} [Fintype π] [DecidableEq π]
    (A : Matrix (SrcCol K π) (SrcCol K π) ℂ) : probeBlock A = (prSel K π)ᴴ * A * prSel K π := by
  ext i k
  simp [probeBlock, mul_apply, prSel]

/-- `(M𝖣M)_pr = V_prᴴ V_cur 𝖣 V_curᴴ V_pr` for `M = VᴴV`. -/
theorem probeBlock_gram_sig {ι π : Type*} [Fintype ι] [Fintype π] [DecidableEq π]
    (V : Matrix ι (SrcCol K π) ℂ) :
    probeBlock ((Vᴴ * V) * srcSignature K π * (Vᴴ * V)) =
      (prBlock V)ᴴ * (curBlock V * sig2 K * (curBlock V)ᴴ) * prBlock V := by
  rw [probeBlock_eq_sel, srcSignature_eq_sel, ← mul_prSel, ← mul_curSel]
  simp only [conjTranspose_mul, Matrix.mul_assoc]

/-!
## Coordinate `3` of the closed source data
-/

/-- **Coordinate `3` of `closedSourceData` is `(M𝖣M)_pr` of the closed Gram process**,
deterministically, under the hypotheses of `closed_current_frame` at `⌊WT⌋`. -/
theorem closedSourceData_three_eq {np : ℕ} (τ m : Fin np → ℝ) (T : ℝ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (x : ProbedPath W np)
    (hn : closeLen s W ≤ ⌊(W : ℝ) * T⌋₊) (hs : 1 ≤ closeLen s W)
    (hU : ∀ j, scatteringMatrix b E W j x.1 * (scatteringMatrix b E W j x.1)ᴴ = 1)
    (hfar : ∀ j, 1 ≤ j → (1 - nearPortProj W) * scatteringMatrix b E W j x.1 *
      transportN b E W j x.1 = (1 - nearPortProj W) * scatteringMatrix b E W (j + 1) x.1)
    (hT : ∀ j, 1 ≤ j → ∀ z : ℂ, ‖z‖ ≤ 1 →
      (physClosingMapAt b E s h W (j + 1) x.1 z)ᴴ * (transportN b E W j x.1)ᴴ =
        ((1 - farEmbed (omittedProj b E h W (closeLen s W) x.1)) *
          (transportN b E W j x.1 * physClosingMapAt b E s h W (j + 1) x.1 z))ᴴ *
          (physClosingMapAt b E s h W j x.1 z)ᴴ)
    (hR : ∀ j, 1 ≤ j → ∀ z : ℂ, ‖z‖ ≤ 1 →
      IsUnit (1 - z • closingN (scatteringMatrix b E W j x.1)
        (farEmbed (omittedProj b E h W (closeLen s W) x.1))
        (farEmbed (closingPairing b E h W (closeLen s W) x.1))).det)
    (hcap : ∀ k, K ≤ k → physTseq b E s W x.1 k ≤ h ^ 2)
    (hlt : ∀ k : Fin K, h ^ 2 < physTseq b E s W x.1 k.val → physTseq b E s W x.1 k.val < 1)
    (hh : h ^ 2 < 1)
    (hG : gramPair (nearPortProj W) (Vs x.1) =
      curGramOf (initialGram K (Fin 0) (physTseq b E s W x.1) h))
    (hE : ∀ y k, ((physOutProj b E s W x.1 - nearPortProj W) * Vs x.1) y k =
      modeEig (physTseq b E s W x.1 k.1.val) k.2 * Vs x.1 y k)
    (θ : ℝ) :
    closedSourceData b E s T h τ m W (phase θ) x 3 =
      probeBlock ((b3ClosedGramAt b E s h τ m W ⌊(W : ℝ) * T⌋₊ Vs (x, θ)).1 *
        srcSignature K (Fin np) * (b3ClosedGramAt b E s h τ m W ⌊(W : ℝ) * T⌋₊ Vs (x, θ)).1) := by
  have hz : ‖phase θ‖ = 1 := by
    rw [phase]; exact Complex.norm_exp_ofReal_mul_I θ
  set n := ⌊(W : ℝ) * T⌋₊
  set C := physClosingMapAt b E s h W n x.1 (phase θ)
  set X := b3ClosedFrameAt b E s h τ m W n Vs (x, θ)
  have hcur : curBlock X = Cᴴ * (stepProd (fun j => transportN b E W j x.1) (closeLen s W)
      (n - closeLen s W))ᴴ * Vs x.1 := by
    rw [Matrix.mul_assoc]
    change curBlock (Cᴴ * b3OpenFrameAt b E s τ m W n Vs x) = _
    rw [curBlock_mul]
    congr 1
  have hpr : prBlock X = closedFrame b E s T h τ m W (phase θ) x := by
    change prBlock (Cᴴ * b3OpenFrameAt b E s τ m W n Vs x) = _
    rw [prBlock_mul]
    congr 1
  have hPC : Cᴴ * nearProjection W * C = nearProjection W := by
    exact closingMap_conj_near nearPortProj_conjTranspose nearPortProj_mul_self
      (nearPortProj_mul_farEmbed _) (nearPortProj_mul_farEmbed _)
  have key := closed_current_frame (Vs x.1) hn hs hU hfar hT hR hcap hlt hh hG hE hz
  have e3 : closedSourceData b E s T h τ m W (phase θ) x 3 =
      (closedFrame b E s T h τ m W (phase θ) x)ᴴ *
        (Cᴴ * ((scatteringMatrix b E W n x.1)ᴴ * nearProjection W * scatteringMatrix b E W n x.1 -
          nearProjection W) * C) * closedFrame b E s T h τ m W (phase θ) x := by
    have : Cᴴ * ((scatteringMatrix b E W n x.1)ᴴ * nearProjection W *
        scatteringMatrix b E W n x.1 - nearProjection W) * C =
        Cᴴ * (scatteringMatrix b E W n x.1)ᴴ * nearProjection W * scatteringMatrix b E W n x.1 *
          C - nearProjection W := by
      rw [Matrix.mul_sub, Matrix.sub_mul, hPC]; simp only [Matrix.mul_assoc]
    rw [this]
    rfl
  rw [e3, b3ClosedGramAt, gramPair]
  change _ = probeBlock (sourceGram X * srcSignature K (Fin np) * sourceGram X)
  rw [sourceGram, probeBlock_gram_sig, hcur, hpr]
  rw [← key]
  rfl

/-!
## `ComplexClosedCurrent`
-/

/-- **On the cap, `t_k ≤ h²` for every `k ≥ K`**, almost surely. -/
theorem ae_cap_tseq (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) (hW : 1 ≤ W) (s h : ℝ)
    (K : ℕ) :
    ∀ᵐ ω ∂growthPathLaw W b, ω ∈ physCapEventC b E s h K W →
      ∀ k, K ≤ k → physTseq b E s W ω k ≤ h ^ 2 := by
  filter_upwards [ae_physCapEvent_iff hb hE1 hE2 hW s h K,
    FullSourceStops.ae_scattering_unitary hb hE1 hE2 hW] with ω hiff hU hcap k hk
  have hseq := isTransmissionSequence_physTseq (b := b) (E := E) (s := s) (hU (closeLen s W)).1
  have h1 := hiff.1 hcap
  change SourceProcessLaw.seqExtract (seqTraceMeasure (physTseq b E s W ω)) K ≤ h ^ 2 at h1
  rw [SourceProcessLaw.seqExtract_seqTraceMeasure hseq] at h1
  exact (hseq.1 hk).trans h1

theorem eventually_one_le_closeLen {s : ℝ} (hs : 0 < s) : ∀ᶠ W : ℕ in atTop, 1 ≤ closeLen s W := by
  obtain ⟨N, hN⟩ := exists_nat_ge (1 / s)
  filter_upwards [eventually_ge_atTop N] with W hW
  apply Nat.le_floor
  have hW' : (N : ℝ) ≤ W := by exact_mod_cast hW
  have : (1 : ℝ) ≤ W * s := by
    calc (1 : ℝ) = 1 / s * s := by field_simp
      _ ≤ W * s := mul_le_mul_of_nonneg_right (hN.trans hW') hs.le
  simpa using this

/-- **`ComplexClosedCurrent` holds**: the closed current coordinate equals `(M𝖣M)_pr`
of the closed Gram process almost surely on the cap event, for every admissible frame. -/
theorem complexClosedCurrent_holds : ComplexClosedCurrent := by
  intro b E np τ m T s h K Vs hD θ hθ
  obtain ⟨⟨hb0, hb, hE1, hE2, -, -, -, hτT⟩, hs, hsτ, hh0, hh1, hVs⟩ := hD
  have hh : h ^ 2 < 1 := by nlinarith
  filter_upwards [eventually_ge_atTop 1, eventually_one_le_closeLen hs, hVs] with W hW hsW hV
  rcases Nat.eq_zero_or_pos np with hnp | hnp
  · subst hnp
    have : {y : ProbedPath W 0 × ℝ | y.1.1 ∈ physCapEventC b E s h K W ∧ ∃ i k : Fin 0,
        θ < ‖(closedSourceData b E s T h τ m W (phase y.2) y.1 3 -
          probeBlock ((b3ClosedGramAt b E s h τ m W ⌊(W : ℝ) * T⌋₊ (Vs W) y).1 *
            srcSignature K (Fin 0) * (b3ClosedGramAt b E s h τ m W ⌊(W : ℝ) * T⌋₊ (Vs W) y).1))
            i k‖} = ∅ := by
      ext y; simp
    rw [this, measure_empty]
    exact zero_le
  have hsT : s < T := (hsτ ⟨0, hnp⟩).trans (hτT ⟨0, hnp⟩)
  have hn : closeLen s W ≤ ⌊(W : ℝ) * T⌋₊ :=
    Nat.floor_le_floor (mul_le_mul_of_nonneg_left hsT.le (Nat.cast_nonneg W))
  have hgood : ∀ᵐ ω ∂growthPathLaw W b,
      (∀ j, scatteringMatrix b E W j ω * (scatteringMatrix b E W j ω)ᴴ = 1) ∧
      (∀ j, 1 ≤ j → (1 - nearPortProj W) * scatteringMatrix b E W j ω *
        transportN b E W j ω = (1 - nearPortProj W) * scatteringMatrix b E W (j + 1) ω) ∧
      (∀ j, 1 ≤ j → ∀ z : ℂ, ‖z‖ ≤ 1 →
        (physClosingMapAt b E s h W (j + 1) ω z)ᴴ * (transportN b E W j ω)ᴴ =
          ((1 - farEmbed (omittedProj b E h W (closeLen s W) ω)) *
            (transportN b E W j ω * physClosingMapAt b E s h W (j + 1) ω z))ᴴ *
            (physClosingMapAt b E s h W j ω z)ᴴ) ∧
      (∀ j, 1 ≤ j → ∀ z : ℂ, ‖z‖ ≤ 1 →
        IsUnit (1 - z • closingN (scatteringMatrix b E W j ω)
          (farEmbed (omittedProj b E h W (closeLen s W) ω))
          (farEmbed (closingPairing b E h W (closeLen s W) ω))).det) ∧
      (∀ k : Fin K, h ^ 2 < physTseq b E s W ω k.val → physTseq b E s W ω k.val < 1) ∧
      (ω ∈ physCapEventC b E s h K W → ∀ k, K ≤ k → physTseq b E s W ω k ≤ h ^ 2) ∧
      (gramPair (nearPortProj W) (Vs W ω) =
          curGramOf (initialGram K (Fin 0) (physTseq b E s W ω) h) ∧
        ∀ x k, ((physOutProj b E s W ω - nearPortProj W) * Vs W ω) x k =
          modeEig (physTseq b E s W ω k.1.val) k.2 * Vs W ω x k) := by
    filter_upwards [FullSourceStops.ae_scattering_unitary hb hE1 hE2 hW,
      ae_farOut_succ hb0 hb hE1 hE2 hW,
      ae_closedCol_transport_disc (s := s) (h := h) hb0 hb hE1 hE2 hW hh,
      ae_isUnit_closingResolvent (h := h) hb0 hb hE1 hE2 hW hh (closeLen s W),
      ae_hlt (s := s) hb hE1 hE2 hW, ae_cap_tseq hb hE1 hE2 hW s h K, hV.2]
      with ω hU hF hT hR hL hC hVω
    exact ⟨fun j => (hU j).1, hF, hT, hR, hL K h, hC, hVω⟩
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := growthPathLaw W b)
    (ν := Measure.pi fun _ : Fin np =>
      BlockBand.Internal.Contracts.CoareaPalm.circularVectorLaw (Fin W))).ae hgood
  have h2 := (Measure.quasiMeasurePreserving_fst (μ := probedPathLaw W np b)
    (ν := phaseLaw)).ae h1
  refine (measure_mono_null (fun y hy hg => ?_) (ae_iff.1 h2)).le.trans zero_le
  obtain ⟨hcap, i, k, hik⟩ := hy
  obtain ⟨hU, hF, hT, hR, hL, hC, hG, hE⟩ := hg
  have e := closedSourceData_three_eq τ m T (Vs W) y.1 hn hsW hU hF hT hR (hC hcap) hL hh
    hG hE y.2
  rw [e, sub_self, Matrix.zero_apply, norm_zero] at hik
  exact absurd hik (not_lt.2 hθ.le)

end BlockBand.SourceProcess.PhysApprox.B3Cur
